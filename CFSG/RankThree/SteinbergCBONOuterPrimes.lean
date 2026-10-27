module

public import CFSG.Sporadic.Schreier.ONSchreier
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder
public import CFSG.RankThree.GroupTheory.SteinbergBKConjugacyInvariantOuterPrime

public section

namespace CFSG.Quasithin.SteinbergCB

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierCharacteristic

theorem not_dvd_card_outer_of_characteristic {H : Type*} [Group H] [Finite H] (D : Subgroup H)
    [D.Characteristic] (hcent : centralizer (D : Set H) ≤ D) {p : ℕ} (hp : p.Prime)
    (hpZ : ¬ p ∣ Nat.card (center D)) (hpO : ¬ p ∣ Nat.card (Outer D)) :
    ¬ p ∣ Nat.card (Outer H) := by
  have : Finite (MulAut H) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut H))
  set K := (innerQuotientRestriction D).ker with hK
  have h1 : Nat.card (Outer H) ∣ Nat.card (innerQuotient D) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (innerQuotientOuterHom_surjective D)).toEquiv]
    exact Dvd.intro _ (card_eq_card_quotient_mul_card_subgroup _).symm
  have h2 := card_eq_card_quotient_mul_card_subgroup K
  have h3 : Nat.card (innerQuotient D ⧸ K) ∣ Nat.card (Outer D) :=
    Subgroup.card_dvd_of_injective _ (innerQuotientKernelEmbedding_injective D)
  have h4 : Nat.card K ∣ Nat.card (pointwiseKernel D) := by
    rw [hK, innerQuotientRestriction_ker_eq_image, ← index_ker]
    exact Dvd.intro_left _ (card_mul_index _)
  have h5 : Nat.card (pointwiseKernel D) ∣ Nat.card (H → center D) :=
    Subgroup.card_dvd_of_injective _ (displacementHom_injective D hcent)
  rw [Nat.card_fun] at h5
  intro hpH
  have hpI := hpH.trans h1
  rw [h2] at hpI
  rcases (Nat.Prime.dvd_mul hp).1 hpI with h | h
  · exact hpO (h.trans h3)
  · exact hpZ (hp.dvd_of_dvd_pow ((h.trans h4).trans h5))

open CFSG.ONSchreier in
theorem card_outer_onL_dvd_twelve : Nat.card (Outer onL) ∣ 12 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := lQuot_classicalModel
  have hX : Nat.card (Outer (onL ⧸ center onL)) ∣ 12 := by
    obtain ⟨⟨E, -⟩, -⟩ := CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism ((e.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          3 K))
    rw [Nat.card_congr E.toEquiv]
    have h := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
      (K := K) (ℓ := 2) (f := 2) (n := 3) Nat.prime_two (by norm_num) le_rfl hK
    simpa using h
  exact (Subgroup.card_dvd_of_injective _
    (CFSG.LocalAnalysis.ComponentInitial.outerCenterQuotientHom_injective onL)).trans hX

open CFSG.ONSchreier in
theorem not_dvd_card_outer_onM {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card (Outer onM) := by
  have hsmall : ∀ n : ℕ, 0 < n → n ∣ 12 → ¬ p ∣ n := fun n _ hdvd hpn => by
    have h2 : p ∣ 12 := hpn.trans hdvd
    have h3 := Nat.le_of_dvd (by norm_num) h2
    interval_cases p <;> revert hp hp2 hp3 h2 <;> decide
  set D := onL.subgroupOf onM with hD
  have hDL : Nat.card (Outer D) = Nat.card (Outer onL) := by
    obtain ⟨⟨E, -⟩, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (subgroupOfEquivOfLe onL_le_M)
    exact Nat.card_congr E.toEquiv
  have hZ : Nat.card (center D) = 4 := by
    rw [Nat.card_congr (Subgroup.centerCongr (subgroupOfEquivOfLe onL_le_M)).toEquiv,
      ← card_map_of_injective onL.subtype_injective, ← CFSG.centerIn_eq_map_center,
      onL_centerIn, card_onQ]
  refine not_dvd_card_outer_of_characteristic D centralizer_L_le hp ?_ ?_
  · rw [hZ]
    exact hsmall 4 (by norm_num) (by norm_num)
  · rw [hDL]
    exact hsmall _ Nat.card_pos card_outer_onL_dvd_twelve

open CFSG.ONSchreier CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers in
theorem card_on_centralizer_inter_le :
    Nat.card ↥(centralizer ({tP} : Set Pv) ⊓
      centralizer ((intrinsicCentralizer (onTSylow : Subgroup Pv) ⊓
        centralizer ({tP} : Set Pv) : Subgroup Pv) : Set Pv)) ≤ 4 := by
  set M := intrinsicCentralizer (onTSylow : Subgroup Pv) with hM
  have heq : (intersectionCentralizer M tP).map (secondCentralizer tP).subtype =
      centralizer ({tP} : Set Pv) ⊓ centralizer ((M ⊓ centralizer ({tP} : Set Pv) :
        Subgroup Pv) : Set Pv) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine mem_inf.2 ⟨y.2, mem_centralizer_iff.2 fun m hm => ?_⟩
      obtain ⟨hmM, hmC⟩ := mem_inf.1 hm
      have h := mem_centralizer_iff.1 hy ⟨m, hmC⟩ (by
        change (⟨m, hmC⟩ : secondCentralizer tP) ∈ M.subgroupOf (secondCentralizer tP)
        rw [mem_subgroupOf]
        exact hmM)
      exact congrArg Subtype.val h
    · intro hx
      obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
      refine ⟨⟨x, hx1⟩, mem_centralizer_iff.2 fun z hz => ?_, rfl⟩
      have hz' : (z : Pv) ∈ M := by
        change z ∈ M.subgroupOf (secondCentralizer tP) at hz
        rwa [mem_subgroupOf] at hz
      exact Subtype.ext (mem_centralizer_iff.1 hx2 z (mem_inf.2 ⟨hz', z.2⟩))
  rw [← heq, card_map_of_injective (secondCentralizer tP).subtype_injective]
  exact card_on_intersectionCentralizer_le

open CFSG.ONSchreier CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers in
theorem ON_large_prime_outer_automorphisms_absent (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ Nat.card (Outer CFSG.Blueprint.NativeSporadic.ON)) : p = 2 ∨ p = 3 := by
  by_contra h
  push Not at h
  obtain ⟨hp2, hp3⟩ := h
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p <;> revert hp hp2 hp3 <;> decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOM : ¬ p ∣ Nat.card (Outer (intrinsicCentralizer (onTSylow : Subgroup Pv))) := by
    obtain ⟨⟨E, -⟩, -⟩ := CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism onIntrinsicEquiv
    rw [Nat.card_congr E.toEquiv]
    exact not_dvd_card_outer_onM hp hp2 hp3
  have hOM1 : ¬ p ∣ Nat.card (Outer (centralizer ({tP} : Set Pv) : Subgroup Pv)) := by
    obtain ⟨⟨E, -⟩, -⟩ := CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (onSecondEquiv.trans mToM1.symm)
    change ¬ p ∣ Nat.card (Outer (secondCentralizer tP))
    rw [Nat.card_congr E.toEquiv]
    exact not_dvd_card_outer_onM hp hp2 hp3
  have hD : ¬ p ∣ Nat.card ↥(centralizer ({tP} : Set Pv) ⊓
      centralizer ((intrinsicCentralizer (onTSylow : Subgroup Pv) ⊓
        centralizer ({tP} : Set Pv) : Subgroup Pv) : Set Pv)) := by
    intro hpd
    have := Nat.le_of_dvd Nat.card_pos hpd
    have := card_on_centralizer_inter_le
    omega
  have hPv :=
    CFSG.RankThree.GroupTheory.SteinbergBK.conjugacy_invariant_two_centralizer_outer_prime_support
      hp (intrinsicCentralizer (onTSylow : Subgroup Pv))
      (intrinsicCentralizer_conjugacyInvariant 2 onTSylow) tP_mem on_generate hOM hOM1 hD
  obtain ⟨⟨E, -⟩, -⟩ := CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
    (G := CFSG.Blueprint.NativeSporadic.ON) (H := Pv) (by exact onEquivPv)
  rw [Nat.card_congr E.toEquiv] at hdvd
  exact hPv hdvd

end CFSG.Quasithin.SteinbergCB
