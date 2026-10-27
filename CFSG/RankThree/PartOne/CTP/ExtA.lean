module

public import CFSG.RankThree.PartOne.CTP.LinearEdge
public import CFSG.RankThree.PartOne.S12.InputsCT
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL
  specialLinearGroupEquivStatedSL projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCT_recognition_of_pairs)
open scoped MatrixGroups

section Bridges

theorem charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (h : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem exists_ringEquiv_of_card_eq {K K' : Type} [Field K] [Field K'] [Finite K] [Finite K']
    (h : Nat.card K = Nat.card K') : Nonempty (K ≃+* K') := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K' := Fintype.ofFinite K'
  exact ⟨FiniteField.ringEquivOfCardEq (by simpa [Nat.card_eq_fintype_card] using h)⟩

@[expose] noncomputable def projectiveSLEquivStated (n : ℕ) (K : Type) [Field K] :
    projectiveSL n K ≃* CFSG.Assembly.LowTwoRank.StatedProj (StatedSL n K) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K)

theorem exists_sl2_equiv_of_model {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (_ : CharP L 2), Nat.card L = 2 ^ f ∧
      Nonempty (SL(2, L) ≃* X) := by
  obtain ⟨-, L, _, _, hL, ⟨e⟩⟩ := h
  have := charP_two_of_card_eq_two_pow hL
  exact ⟨L, inferInstance, inferInstance, this, hL,
    ⟨((LinearCover.projectiveSLTwoEquivSL L).symm.trans (projectiveSLEquivStated 2 L)).trans
      e.symm⟩⟩

theorem exists_sl3_surj_of_centrallyL3 {X : Type} [Group X] {f : ℕ} (h : CentrallyLThree f X) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L), Nat.card L = 2 ^ f ∧
      ∃ θ₀ : SL(3, L) →* X, Function.Surjective θ₀ ∧ θ₀.ker ≤ Subgroup.center SL(3, L) := by
  rcases h with ⟨L, _, _, hL, ⟨e⟩⟩ | ⟨-, L, _, _, hL, ⟨e⟩⟩
  · refine ⟨L, inferInstance, inferInstance, hL,
      e.symm.toMonoidHom.comp (specialLinearGroupEquivStatedSL 3 L).toMonoidHom,
      e.symm.surjective.comp (specialLinearGroupEquivStatedSL 3 L).surjective, ?_⟩
    intro x hx
    change e.symm ((specialLinearGroupEquivStatedSL 3 L) x) = 1 at hx
    have h1 := (MulEquiv.map_eq_one_iff e.symm).mp hx
    have h2 := (MulEquiv.map_eq_one_iff (specialLinearGroupEquivStatedSL 3 L)).mp h1
    rw [h2]
    exact one_mem _
  · refine ⟨L, inferInstance, inferInstance, hL,
      (e.symm.toMonoidHom.comp (projectiveSLEquivStated 3 L).toMonoidHom).comp (proj 3 L),
      e.symm.surjective.comp ((projectiveSLEquivStated 3 L).surjective.comp
        (proj_surjective 3 L)), ?_⟩
    intro x hx
    have h1 : proj 3 L x = 1 := by
      apply (projectiveSLEquivStated 3 L).injective
      apply e.symm.injective
      simpa using hx
    have h2 : x ∈ (proj 3 L).ker := h1
    rwa [ker_proj, scalars_eq_center] at h2

end Bridges

theorem extCurtisTitsA : ExtCurtisTitsA := by
  intro G _ _ n f p K E hn hf hp hpq hE hgen hK2 hcomm hadj htor
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpair : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (K i) (K j) := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst h
      omega
    obtain ⟨L, _, _, hL, θ₀, hsurj, hker₀⟩ :=
      exists_sl3_surj_of_centrallyL3 (hadj i j (Or.inl hij.symm))
    obtain ⟨Li, _, _, _, hLi, ⟨ρi⟩⟩ := exists_sl2_equiv_of_model (hK2 i)
    obtain ⟨Lj, _, _, _, hLj, ⟨ρj⟩⟩ := exists_sl2_equiv_of_model (hK2 j)
    have : CharP L 2 := charP_two_of_card_eq_two_pow hL
    let θ : SL(3, L) →* G := (K i ⊔ K j).subtype.comp θ₀
    have hrange : θ.range = K i ⊔ K j := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
        Subgroup.range_subtype]
    have hker : θ.ker ≤ Subgroup.center SL(3, L) := by
      intro x hx
      exact hker₀ (Subtype.ext hx)
    have hE' : EdgeTorus p E (K i) (K j) :=
      ⟨(htor.1 i).1, (htor.1 i).2, (htor.1 j).1, (htor.1 j).2, htor.2 i j hne⟩
    obtain ⟨c, hc1, hc2⟩ := linear_edge_standardPair θ hker (by rw [hL]; exact hq4) hp hp2
      (by rw [hL]; exact hpq) hE' hrange.symm (by rw [hLi, hL]) (by rw [hLj, hL]) ρi ρj
    have hLB : LinearBlockStandardPair L (K i ⊔ K j) (K i) (K j) :=
      ⟨θ, c, hrange, hker, Or.inl ⟨hc1, hc2⟩⟩
    obtain ⟨e⟩ := exists_ringEquiv_of_card_eq (K := L) (K' := GaloisField 2 f) (by rw [hL, hF])
    exact ⟨K i ⊔ K j, hLB.of_ringEquiv e⟩
  have hcomm' : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x := by
    intro i j hij x hx y hy
    have hne : i ≠ j := by
      intro h
      subst h
      omega
    have hna : ¬ chainAdj i j := by
      rintro (h | h) <;> omega
    exact (Subgroup.mem_centralizer_iff.mp ((hcomm i j hne hna).1 hx) y hy).symm
  obtain ⟨ψ, hsurj, hker, -, hmodel⟩ := weakCT_recognition_of_pairs (GaloisField 2 f) 2 f
    Nat.prime_two hF hq4 hn hcomm' hpair hgen
  have h1 : StatedClassicalModel (G ⧸ Subgroup.center G) .PSL (n + 1) 2 f :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hmodel
  refine ⟨h1, fun hcop => ?_⟩
  have hZ : Subgroup.center SL(n + 1, GaloisField 2 f) = ⊥ := by
    have h3 := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := n + 1) (by omega)
      (GaloisField 2 f)
    rw [hF, Nat.Coprime.gcd_eq_one hcop] at h3
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h3)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hinjP : Function.Injective (proj (n + 1) (GaloisField 2 f)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_center, hZ]
  exact ⟨h1.1, GaloisField 2 f, inferInstance, inferInstance, hF,
    ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm.trans
      ((MulEquiv.ofBijective (proj (n + 1) (GaloisField 2 f))
        ⟨hinjP, proj_surjective _ _⟩).trans (projectiveSLEquivStated (n + 1) _))⟩⟩

end CFSG.RankThree.PartOne.CTP
