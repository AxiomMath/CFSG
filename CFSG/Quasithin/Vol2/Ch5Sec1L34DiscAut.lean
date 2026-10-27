module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs517
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.RankThree.PartTwo.KFacts.AutSz

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)

theorem mem_inner_of_card_outer_odd {X : Type} [Group X] {n m : ℕ} (hn : Odd n)
    (hcard : Nat.card (Outer X) = n) (α : MulAut X) (hα : α ^ 2 ^ m = 1) : α ∈ inner X := by
  have hfin : Finite (Outer X) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hn.pos.ne')
  let π : MulAut X →* Outer X := QuotientGroup.mk' _
  have h2 : π α ^ 2 ^ m = 1 := by rw [← map_pow, hα, map_one]
  have h3 : π α ^ n = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hcop : Nat.gcd (2 ^ m) n = 1 := Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hn)
  have h4 : π α ^ Nat.gcd (2 ^ m) n = 1 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rw [hcop, pow_one] at h4
  exact (QuotientGroup.eq_one_iff _).mp h4

theorem card_outer_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Outer X) = Nat.card (Outer Y) := by
  have hmap : (inner X).map (MulAut.congr e).toMonoidHom = inner Y := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e x).symm⟩
    · rintro _ ⟨y, rfl⟩
      refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]
  exact Nat.card_congr (QuotientGroup.congr (inner X) (inner Y) (MulAut.congr e) hmap).toEquiv

theorem l2OddInnerFact : L2OddInnerFact := by
  intro X _ _ n hX hn φ ⟨m, hm⟩
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have hn1 : 1 ≤ n := hn.pos
  have : CharP k 2 := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card hk
  have e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) k :=
    e.trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL k)
  have hcard : Nat.card (Outer X) = n := by
    rw [card_outer_congr e']
    exact (even_SL2_full_automorphism_semilinear_model hn1 hk).2.2.2.1
  obtain ⟨x, hx⟩ := mem_inner_of_card_outer_odd hn hcard φ hm
  exact ⟨x, hx.symm⟩

theorem szTwoAutInnerFact : SzTwoAutInnerFact := by
  intro X _ f hX α ⟨m, hm⟩
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hX
  rw [hf] at hK
  set α' := MulAut.congr e α with hα'
  have hm' : α' ^ 2 ^ m = 1 := by rw [hα', ← map_pow, hm, map_one]
  obtain ⟨g, σ, hgσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK α'
  have hcard : Nat.card (RingAut K) = 2 * a + 1 :=
    (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.ringAut_card_and_cyclic hK).1
  have hσ : σ ^ (2 * a + 1) = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hτ : CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ ^ (2 * a + 1) = 1 :=
    by rw [← map_pow, hσ, map_one]
  let π : MulAut (suzukiGroup a K) →* Outer (suzukiGroup a K) := QuotientGroup.mk' _
  have h1 : π α' = π (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ) := by
    rw [hgσ, map_mul]
    have : π (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rw [this, one_mul]
  have h2 : π α' ^ 2 ^ m = 1 := by rw [← map_pow, hm', map_one]
  have h3 : π α' ^ (2 * a + 1) = 1 := by rw [h1, ← map_pow, hτ, map_one]
  have hcop : Nat.gcd (2 ^ m) (2 * a + 1) = 1 :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr ⟨a, rfl⟩)
  have h4 : π α' ^ Nat.gcd (2 ^ m) (2 * a + 1) = 1 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rw [hcop, pow_one] at h4
  obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff _).mp h4
  refine ⟨e.symm q, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hα', ← hq, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]

end CFSG.Quasithin.H13
