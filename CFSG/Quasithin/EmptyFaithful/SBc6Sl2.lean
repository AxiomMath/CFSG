module

public import CFSG.Quasithin.EmptyFaithful.SBc5SL2
import CFSG.Quasithin.Background.B6Defs
import CFSG.Quasithin.EmptyFaithful.SBd3Transport
import CFSG.Quasithin.H13.NQRigidWMGroups
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup

public section

namespace CFSG.Quasithin.SBc6

open CFSG.Quasithin.SBc5SL2 CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj
  specialLinearGroupEquivStatedSL)

section Model

private theorem center_SL2_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (SL2 F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

private theorem charP_two_of_natCard_eq_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem exists_sl2_equiv_of_psl {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧ 1 ≤ n ∧
      Nonempty (SL2 F ≃* X) := by
  obtain ⟨⟨-, hf, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hchar : CharP K 2 := charP_two_of_natCard_eq_two_pow hK
  exact ⟨K, hKf, hKfin, hchar, hK, hf, ⟨(((QuotientGroup.quotientMulEquivOfEq
    center_SL2_eq_bot).trans QuotientGroup.quotientBot).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K)).trans e.symm⟩⟩

theorem exists_statedSL_equiv_of_psl {n : ℕ} {X : Type} [Group X] (hX : IsPSL 2 2 n X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) := by
  obtain ⟨F, hFf, hFfin, -, hFcard, -, ⟨φ⟩⟩ := exists_sl2_equiv_of_psl hX
  exact ⟨F, hFf, hFfin, hFcard, ⟨φ.symm.trans (specialLinearGroupEquivStatedSL 2 F)⟩⟩

theorem isSimpleGroup_of_psl {n : ℕ} (hn : 1 < n) {X : Type} [Group X] (hX : IsPSL 2 2 n X) :
    IsSimpleGroup X := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, -, ⟨φ⟩⟩ := exists_sl2_equiv_of_psl hX
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  exact (φ.symm.trans (specialLinearGroupEquivStatedSL 2 F)).isSimpleGroup

end Model

section Overgroups

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem unitriangular_le_Uplus {F : Type} [Field F] : unitriangular 2 F ≤ Uplus F := by
  intro A hA
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hA
  refine mem_Uplus_iff.2 ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xm, hlow 1 0 (by decide), hdiag 0, hdiag 1]

private theorem entry_one_zero_of_mem_stabilizer {F : Type} [Field F] {g : SL2 F}
    (hg : g ∈ stabilizer (flagSpace 2 F 1)) : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hmem : (Pi.single 0 1 : Fin 2 → F) ∈ flagSpace 2 F 1 := by
    rw [mem_flagSpace]
    intro j hj
    have hj0 : j ≠ 0 := fun h => by simp [h] at hj
    exact Pi.single_eq_of_ne hj0 _
  have h1 := Submodule.mem_map_of_mem (f := Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) F)) hmem
  rw [mem_stabilizer.1 hg] at h1
  have h2 := mem_flagSpace.1 h1 1 le_rfl
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h2

theorem sl2_overgroup {F : Type} [Field F] {M : Subgroup (SL2 F)} (hU : Uplus F ≤ M) :
    M = ⊤ ∨ M ≤ Tplus F := by
  have hU' : unitriangular 2 F ≤ M := unitriangular_le_Uplus.trans hU
  by_cases hcuts : borelOvergroupCuts M = ∅
  · exact Or.inl (X7a.eq_top_of_borelOvergroupCuts_eq_empty M hU' hcuts)
  · refine Or.inr fun g hg => ?_
    obtain ⟨i, hi1, hin, hrnot⟩ := Set.nonempty_iff_ne_empty.2 hcuts
    have hi : i = 1 := by omega
    subst hi
    exact entry_one_zero_of_mem_stabilizer
      (mem_flagStabilizer.1 (X7a.le_flagStabilizer_borelOvergroupCuts M hU' hg) 1
        ⟨hi1, hin, hrnot⟩)

end Overgroups

section Sylow

private theorem exists_conj_Uplus {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ m) {Q : Subgroup (SL2 F)} (hQ : IsSylowTwoOf Q ⊤) :
    ∃ g : SL2 F, ∀ x : SL2 F, x ∈ Q ↔ g⁻¹ * x * g ∈ Uplus F := by
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_Uplus hm hF) hQ
  exact ⟨g, fun x => by rw [hg, B6.mem_conjSub]⟩

private theorem mem_normalizer_iff_of_conj {G : Type} [Group G] {Q U : Subgroup G} {g : G}
    (hg : ∀ x : G, x ∈ Q ↔ g⁻¹ * x * g ∈ U) (d : G) :
    d ∈ Subgroup.normalizer (Q : Set G) ↔ g⁻¹ * d * g ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (g * y * g⁻¹)
    simp only [hg] at h1
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (d * (g * y * g⁻¹) * d⁻¹) * g = (g⁻¹ * d * g) * y * (g⁻¹ * d * g)⁻¹ := by
      group
    rwa [e1, e2] at h1
  · intro h x
    simp only [hg]
    have h1 := h (g⁻¹ * x * g)
    have e2 : g⁻¹ * (d * x * d⁻¹) * g =
        (g⁻¹ * d * g) * (g⁻¹ * x * g) * (g⁻¹ * d * g)⁻¹ := by group
    rwa [e2]

theorem sl2_overgroup_sylow {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ m) {Q D : Subgroup (SL2 F)} (hQ : IsSylowTwoOf Q ⊤) (hQD : Q ≤ D) :
    D = ⊤ ∨ D ≤ Subgroup.normalizer (Q : Set (SL2 F)) := by
  obtain ⟨g, hg⟩ := exists_conj_Uplus hm hF hQ
  have hD' : ∀ y : SL2 F, y ∈ B6.conjSub g⁻¹ D ↔ g * y * g⁻¹ ∈ D := fun y => by
    rw [B6.mem_conjSub, inv_inv]
  have hUD' : Uplus F ≤ B6.conjSub g⁻¹ D := by
    intro u hu
    rw [hD']
    refine hQD ((hg _).2 ?_)
    have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
    rwa [e]
  rcases sl2_overgroup hUD' with h | h
  · left
    refine eq_top_iff.2 fun x _ => ?_
    have h1 : g⁻¹ * x * g ∈ B6.conjSub g⁻¹ D := by
      rw [h]
      exact Subgroup.mem_top _
    rw [hD'] at h1
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h1
  · right
    intro d hd
    rw [mem_normalizer_iff_of_conj hg d, normalizer_Uplus]
    refine h ?_
    rw [hD']
    have e : g * (g⁻¹ * d * g) * g⁻¹ = d := by group
    rwa [e]

theorem not_normal_sylow_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ m) {Q : Subgroup (SL2 F)} (hQ : IsSylowTwoOf Q ⊤) :
    ¬ (⊤ : Subgroup (SL2 F)) ≤ Subgroup.normalizer (Q : Set (SL2 F)) := by
  intro htop
  obtain ⟨g, hg⟩ := exists_conj_Uplus hm hF hQ
  have hall : ∀ y : SL2 F, y ∈ Tplus F := by
    intro y
    have h1 := (mem_normalizer_iff_of_conj hg (g * y * g⁻¹)).1 (htop (Subgroup.mem_top _))
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e, normalizer_Uplus] at h1
  have h10 : ((wm : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hall wm
  have hw : ((wm : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = -1 := by simp [wm]
  rw [hw] at h10
  exact one_ne_zero (neg_eq_zero.1 h10)

end Sylow

section Transport

private theorem isSylowTwoOf_top_comap {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    {Q : Subgroup B} (hQ : IsSylowTwoOf Q ⊤) : IsSylowTwoOf (Q.comap (φ : A →* B)) ⊤ := by
  have h := (SBd3T.isSylowTwoOf_map_iff (φ : A →* B) φ.injective (Q.comap (φ : A →* B)) ⊤).1
  rw [Subgroup.map_comap_eq_self_of_surjective φ.surjective,
    Subgroup.map_top_of_surjective _ φ.surjective] at h
  exact h hQ

theorem overgroup_of_psl {n : ℕ} {X : Type} [Group X] (hX : IsPSL 2 2 n X) {Q D : Subgroup X}
    (hQ : IsSylowTwoOf Q ⊤) (hQD : Q ≤ D) : D = ⊤ ∨ D ≤ Subgroup.normalizer (Q : Set X) := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, hn, ⟨φ⟩⟩ := exists_sl2_equiv_of_psl hX
  rcases sl2_overgroup_sylow hn hFcard (isSylowTwoOf_top_comap φ hQ)
      (Subgroup.comap_mono hQD : Q.comap (φ : SL2 F →* X) ≤ D.comap (φ : SL2 F →* X)) with h | h
  · left
    refine eq_top_iff.2 fun x _ => ?_
    have h1 : φ.symm x ∈ D.comap (φ : SL2 F →* X) := by
      rw [h]
      exact Subgroup.mem_top _
    simpa using h1
  · right
    intro x hx
    have h1 : φ.symm x ∈ (Subgroup.normalizer (Q : Set X)).comap (φ : SL2 F →* X) := by
      rw [Subgroup.comap_normalizer_eq_of_surjective Q φ.surjective]
      exact h (by simpa using hx)
    simpa using h1

theorem not_normal_sylow_of_psl {n : ℕ} {X : Type} [Group X] (hX : IsPSL 2 2 n X)
    {Q : Subgroup X} (hQ : IsSylowTwoOf Q ⊤) :
    ¬ (⊤ : Subgroup X) ≤ Subgroup.normalizer (Q : Set X) := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, hn, ⟨φ⟩⟩ := exists_sl2_equiv_of_psl hX
  intro htop
  refine not_normal_sylow_sl2 hn hFcard (isSylowTwoOf_top_comap φ hQ) fun a _ => ?_
  have h1 : a ∈ (Subgroup.normalizer (Q : Set X)).comap (φ : SL2 F →* X) :=
    htop (Subgroup.mem_top (φ a))
  rwa [Subgroup.comap_normalizer_eq_of_surjective Q φ.surjective] at h1

end Transport

section Sylow2

private theorem le_of_isSylowTwoOf_of_le_normalizer {Y : Type} [Group Y] [Finite Y]
    {K P R : Subgroup Y} (hP : IsSylowTwoOf P K) (hR : IsPGroup 2 R) (hRK : R ≤ K)
    (hPR : P ≤ Subgroup.normalizer (R : Set Y)) : R ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 (P ⊔ R : Subgroup Y) := hP.2.1.to_sup_of_normal_right' hR hPR
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hsup
  have hdvd : P.relIndex (P ⊔ R) ∣ P.relIndex K :=
    ⟨_, (Subgroup.relIndex_mul_relIndex P (P ⊔ R) K le_sup_left (sup_le hP.1 hRK)).symm⟩
  have hdvd2 : P.relIndex (P ⊔ R) ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card P (P ⊔ R)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hi0 : i = 0 := by
    by_contra hne
    exact hP.2.2 ((hi ▸ dvd_pow_self 2 hne).trans hdvd)
  rw [hi0, pow_zero, Subgroup.relIndex_eq_one] at hi
  exact le_sup_right.trans hi

theorem eq_of_le_normalizer_of_isSylowTwoOf {Y : Type} [Group Y] [Finite Y] {R Q Q' : Subgroup Y}
    (hQ : IsSylowTwoOf Q R) (hQ' : IsSylowTwoOf Q' R) (h : Q ≤ Subgroup.normalizer (Q' : Set Y)) :
    Q = Q' := by
  have h1 : Q' ≤ Q := le_of_isSylowTwoOf_of_le_normalizer hQ hQ'.2.1 hQ'.1 h
  exact le_antisymm
    (le_of_isSylowTwoOf_of_le_normalizer hQ' hQ.2.1 hQ.1 (h1.trans Subgroup.le_normalizer)) h1

end Sylow2

end CFSG.Quasithin.SBc6
