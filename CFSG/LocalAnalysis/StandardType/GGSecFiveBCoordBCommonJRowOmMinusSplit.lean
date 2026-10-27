module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusSplitAux1
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusSplitAux2
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Multiplicative

theorem ggSecFiveBNativeRow_omMinusSplit {K : Type} [Field K] [Finite K] {f p m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1) (hm : 3 ≤ m)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGSecFiveBNativeRow (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) p m
      (fun lab => lab = ⟨.A, m - 1, f⟩) (fun lab => lab = ⟨.twD, m, f⟩) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  haveI : CharP K 2 := hchar
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = p :=
    exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units, hK]; exact hpq)
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hf1 : 1 ≤ f := by
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hK, hf0, pow_zero] at h2
    omega
  let H₀ : Type := StatedOmega (StatedQuadMinus (m + 1) K b c)
  letI : Group H₀ := inferInstance
  let τ : (Fin m → Multiplicative (ZMod p)) →* H₀ := omMinusTorus (p := p) b c hζ
  have hτ : Function.Injective τ := by
    simpa only [τ] using
      ggCommonJOmMinusSplit_torus_injective (p := p) (m := m) (b := b) (c := c) hζ hζo
  have hsign : ∀ g : H₀, (∀ s ∈ τ.range, g * s * g⁻¹ ∈ τ.range) →
      ∃ u : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p)),
        SpCoord.IsSignedPerm u ∧ ∀ t, g * τ t * g⁻¹ = τ (u t) := by
    intro g hg
    exact ggCommonJOmMinusSplit_signed (p := p) (m := m) (b := b) (c := c) hp hζ hζo g
      (by simpa only [τ] using hg)
  have hcomp : ∀ (t : Fin m → Multiplicative (ZMod p)) (J : Subgroup H₀),
      CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({τ t} : Set H₀)) →
      Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set H₀)) = p →
        (GGCoordDense t ∧ ∃ lab, lab = (⟨.A, m - 1, f⟩ : LargeEvenLabel) ∧
            LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
            (lab = ⟨.twA, 3, 1⟩ → Subgroup.center ↥J = ⊥)) ∨
          (GGCoordSparse t ∧ ∃ lab, lab = (⟨.twD, m, f⟩ : LargeEvenLabel) ∧
            LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) := by
    intro t J hJ hcount
    obtain ⟨a, P, hP, _hcent, hf1P, hcard⟩ :=
      ggCommonJOmMinusSplit_component_count (p := p) (m := m) (b := b) (c := c)
        hp hp2 hm hirr hζ hζo t J (by simpa only [τ] using hJ)
    have htne : t ≠ 1 := by
      intro ht
      obtain ⟨hPuniv, ha0⟩ := hf1P ht
      rw [hPuniv, ha0] at hcard
      have hc1 : Nat.card ↥((omMinusTorus (p := p) b c hζ).range ⊓
          Subgroup.centralizer (J : Set (StatedOmega (StatedQuadMinus (m + 1) K b c)))) = 1 := by
        simpa only [Finset.card_univ, Fintype.card_fin, Nat.sub_self, Nat.add_zero,
          if_pos trivial, pow_zero] using hcard
      have hcount' : Nat.card ↥((omMinusTorus (p := p) b c hζ).range ⊓
          Subgroup.centralizer (J : Set (StatedOmega (StatedQuadMinus (m + 1) K b c)))) = p := by
        simpa only [τ] using hcount
      rw [hc1] at hcount'
      exact hp.ne_one hcount'.symm
    by_cases ha : a = 0
    · have hcard0 : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set H₀)) =
          p ^ (m - P.card) := by
        simpa only [τ, if_pos ha, Nat.add_zero] using hcard
      have hexp : m - P.card = 1 := by
        refine Nat.pow_right_injective hp.two_le ?_
        simpa using hcard0.symm.trans hcount
      have hPcard : P.card = m - 1 := by
        have hPle : P.card ≤ m := by simpa using P.card_le_univ
        omega
      have hcompl : (Finset.univ \ P).card = 1 := by
        rw [Finset.card_sdiff]
        simp only [Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
        omega
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hcompl
      have hsparse : GGCoordSparse t := by
        refine ⟨i₀, fun j hj => ?_⟩
        have hjP : j ∈ P := by
          by_contra hji
          have hmem : j ∈ Finset.univ \ P := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hji⟩
          rw [hi₀] at hmem
          exact hj (by simpa using (Finset.mem_singleton.mp hmem))
        have hval := hP j hjP
        apply toAdd_eq_zero.mp
        rw [ha] at hval
        rcases hval with hval | hval
        · exact hval
        · exact hval.trans (neg_zero)
      have hlab := ggCommonJOmMinusSplit_sparse_label (p := p) (m := m) (b := b) (c := c)
        hp hp2 hK hm hirr hζ hζo hsparse htne (by simpa only [τ] using hJ)
      have hlam : LargeEvenInLambda2 (⟨.twD, m, f⟩ : LargeEvenLabel) := by
        have hm2 : 2 ≤ m := by omega
        simp [LargeEvenInLambda2, hf1, hm2]
      exact Or.inr ⟨hsparse, ⟨.twD, m, f⟩, rfl, hlam, hlab⟩
    · have hcard1 : Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set H₀)) =
          p ^ (m - P.card + 1) := by
        simpa only [τ, if_neg ha] using hcard
      have hexp : m - P.card + 1 = 1 := by
        refine Nat.pow_right_injective hp.two_le ?_
        simpa using hcard1.symm.trans hcount
      have hPcard : P.card = m := by
        have hPle : P.card ≤ m := by simpa using P.card_le_univ
        omega
      have hPuniv : P = Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa using hPcard
      have hdense : GGCoordDense t := by
        intro i
        have hiP : i ∈ P := by rw [hPuniv]; exact Finset.mem_univ i
        have hi := hP i hiP
        refine ⟨?_, fun j => ?_⟩
        · intro h1
          rw [h1, toAdd_one] at hi
          rcases hi with hi | hi
          · exact ha hi.symm
          · exact ha (neg_eq_zero.mp hi.symm)
        · have hjP : j ∈ P := by rw [hPuniv]; exact Finset.mem_univ j
          have hj := hP j hjP
          rcases hi with hi | hi <;> rcases hj with hj | hj
          · left; exact toAdd.injective (hj.trans hi.symm)
          · right
            apply toAdd.injective
            simpa [toAdd_inv, hi] using hj
          · right
            apply toAdd.injective
            simpa [toAdd_inv, hi] using hj
          · left; exact toAdd.injective (hj.trans hi.symm)
      have hlab := ggCommonJOmMinusSplit_dense_label (p := p) (m := m) (b := b) (c := c)
        hp hp2 hK hm hirr hζ hζo hdense (by simpa only [τ] using hJ)
      have hlam : LargeEvenInLambda2 (⟨.A, m - 1, f⟩ : LargeEvenLabel) := by
        have hm1 : m - 1 ≠ 1 := by omega
        have hmle : 1 ≤ m - 1 := by omega
        simp [LargeEvenInLambda2, hf1, hmle, hm1]
      exact Or.inl ⟨hdense, ⟨.A, m - 1, f⟩, rfl, hlam, hlab,
        fun hlab => by cases hlab⟩
  have hconj : ∀ T : Subgroup H₀, IsElemAbelian p T → Nat.card T = p ^ m →
      ∃ α : H₀ ≃* H₀, T = τ.range.map α.toMonoidHom := by
    intro T hT hTcard
    exact ggCommonJOmMinusSplit_conj (p := p) (m := m) (b := b) (c := c)
      hp2 hirr hζ hζo hT hTcard
  have hAt : GGSecFiveBNativeAt H₀ p m
      (fun lab => lab = (⟨.A, m - 1, f⟩ : LargeEvenLabel))
      (fun lab => lab = (⟨.twD, m, f⟩ : LargeEvenLabel)) τ.range :=
    GGSecFiveBNativeAt.of_torus τ hτ hsign hcomp
  have hrow : GGSecFiveBNativeRow H₀ p m
      (fun lab => lab = (⟨.A, m - 1, f⟩ : LargeEvenLabel))
      (fun lab => lab = (⟨.twD, m, f⟩ : LargeEvenLabel)) :=
    GGSecFiveBNativeRow.of_std hAt hconj
  exact GGSecFiveBNativeRow.of_mulEquiv (rMinusEquivStatedOmega K m b c).symm hrow

end CFSG.StandardType

end
