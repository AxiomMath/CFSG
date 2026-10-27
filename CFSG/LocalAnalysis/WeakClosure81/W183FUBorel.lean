module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.Holt.PointHullTwoGroupBasic
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
import CFSG.LocalAnalysis.GL83PartI.I713.UnitaryDiag
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)

section Certified


theorem w183fu_five_borel {G : Type} [Group G] [Finite G] {Q S : Subgroup G} (hQ : IsU3 ↥Q 2)
    (hS : IsSylowIn 2 S Q) : ∃ z ∈ Q ⊓ Subgroup.normalizer (S : Set G), orderOf z = 5 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup ↥Q :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hQ
  haveI := hsimple
  have hnonab : ∃ a b : ↥Q, a * b ≠ b * a :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 hQ
  have hZ : Subgroup.center ↥Q = ⊥ :=
    CFSG.Holt.PointHull.center_eq_bot_of_isSimpleGroup hnonab
  have hq : CFSG.Open.IsQuasisimple ↥Q :=
    CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup hnonab
  have hL : CFSG.Blueprint.LieModel (↥Q ⧸ Subgroup.center ↥Q) .PSU (2 * 1 + 1) 2 2 := by
    have h3 : CFSG.Blueprint.LieModel (↥Q ⧸ Subgroup.center ↥Q) .PSU 3 2 2 :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hQ
    rwa [show 2 * 1 + 1 = 3 by norm_num]
  have hWit := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_of_lieModel
    (X := ↥Q) hq (r := 1) (ε := 1) (n := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hL (ℓ := 5) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨F, hFle, hFabel, hFcard⟩ := hWit hS.toSylow
  have hFcard5 : Nat.card F = 5 := by simpa using hFcard
  have hcardgt : 1 < Nat.card F := by rw [hFcard5]; norm_num
  have hne : F ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot F).mp hcardgt
  haveI : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).mpr hne
  obtain ⟨z', hz'F, hz'ne⟩ := Subgroup.exists_ne_one_of_nontrivial F
  have hord' : orderOf z' = 5 := orderOf_eq_prime (hFabel.2 z' hz'F) hz'ne
  have hN : z' ∈ Subgroup.normalizer ((S.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) := by
    rw [← IsSylowIn.coe_toSylow (h := hS)]
    exact hFle hz'F
  have hmemG : (z' : G) ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxQ : x ∈ Q := hS.le hx
      have h1 : (⟨x, hxQ⟩ : ↥Q) ∈ S.subgroupOf Q :=
        Subgroup.mem_subgroupOf.mpr hx
      have h2 := (Subgroup.mem_normalizer_iff.mp hN ⟨x, hxQ⟩).mp h1
      simpa using Subgroup.mem_subgroupOf.mp h2
    · intro hx
      have hxQ : x ∈ Q := by
        have e : x = (z' : G)⁻¹ * ((z' : G) * x * (z' : G)⁻¹) * (z' : G) := by group
        rw [e]
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem z'.2) (hS.le hx)) z'.2
      have h2 : ((z' : ↥Q) * ⟨x, hxQ⟩ * (z' : ↥Q)⁻¹ : ↥Q) ∈ S.subgroupOf Q :=
        Subgroup.mem_subgroupOf.mpr (by simpa using hx)
      have h1 := (Subgroup.mem_normalizer_iff.mp hN ⟨x, hxQ⟩).mpr h2
      simpa using Subgroup.mem_subgroupOf.mp h1
  refine ⟨(z' : G), Subgroup.mem_inf.mpr ⟨z'.2, hmemG⟩, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hord'

end Certified

theorem w183fu_le_pRank_statedPSU_torus {K : Type} [Field K] [Finite K] {q n ℓ : ℕ}
    (hK : Nat.card K = q ^ 2) (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q + 1) (hn : 2 ≤ n)
    (hnℓ : ¬ ℓ ∣ n) :
    n - 1 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
  classical
  have hq2 : 2 ≤ q := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = ℓ := by
    refine exists_prime_orderOf_dvd_card' ℓ ?_
    rw [Nat.card_units, hK, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)]
    exact Dvd.dvd.mul_left hℓq _
  let μ : Subgroup Kˣ := Subgroup.zpowers ω
  have hμcard : Nat.card μ = ℓ := by
    dsimp only [μ]
    rw [Nat.card_zpowers, hω]
  have hμpow : ∀ x : μ, x ^ ℓ = 1 := by
    intro x
    have h1 : orderOf x ∣ Nat.card μ := orderOf_dvd_natCard x
    rw [hμcard] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hμq : ∀ x : μ, (x : Kˣ) ^ (q + 1) = 1 := by
    intro x
    obtain ⟨t, ht⟩ := hℓq
    have h2 : (x : Kˣ) ^ ℓ = 1 := by
      simpa using congrArg (fun y : μ => (y : Kˣ)) (hμpow x)
    rw [ht, pow_mul, h2, one_pow]
  let A := (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_prodHom μ n).ker
  have hAcard : Nat.card A = ℓ ^ (n - 1) := by
    have h :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_card_ker_prod_mul μ
        (by omega : 1 ≤ n)
    rw [hμcard] at h
    have hpow : ℓ ^ n = ℓ ^ (n - 1) * ℓ := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [pow_succ]
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right hℓ.pos h
  let toUnits : A →* (Fin n → Kˣ) :=
    (MonoidHom.compLeft μ.subtype (Fin n)).comp A.subtype
  let toMat : A →* (Fin n → Kˣ) := toUnits
  let F : A →* StatedSU n q K :=
    { toFun := fun g => ⟨GL83.I713.UnitaryDiag.diagHomGL (Fin n) K (toMat g), by
        refine GL83.I713.UnitaryDiag.diagHomGL_mem_statedSU (by omega : q ≠ 0) ?_ ?_
        · simpa [toMat, toUnits,
            CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_prodHom] using
            congrArg (fun y : μ => (y : Kˣ)) g.2
        · intro i
          simpa [toMat, toUnits] using hμq (g.1 i)⟩
      map_one' := by
        apply Subtype.ext
        change GL83.I713.UnitaryDiag.diagHomGL (Fin n) K (toMat 1) = 1
        rw [map_one, map_one]
      map_mul' := by
        intro g h
        apply Subtype.ext
        change GL83.I713.UnitaryDiag.diagHomGL (Fin n) K (toMat (g * h)) =
          GL83.I713.UnitaryDiag.diagHomGL (Fin n) K (toMat g) *
            GL83.I713.UnitaryDiag.diagHomGL (Fin n) K (toMat h)
        rw [map_mul, map_mul] }
  let f : A →* StatedProj (StatedSU n q K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
      (StatedSU n q K))).comp F
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hqg : (QuotientGroup.mk (F g) : StatedProj (StatedSU n q K)) =
        QuotientGroup.mk (1 : StatedSU n q K) := by
      simpa [f, QuotientGroup.mk'_apply] using hg
    obtain ⟨u, hu⟩ := GL83.I713.UnitaryDiag.exists_unit_of_mk_eq_diagonal (g := F g)
      (g' := (1 : StatedSU n q K)) (d := fun i => (toMat g i : K))
      (d' := fun _ => (1 : K)) (by exact GL83.I713.UnitaryDiag.coe_diagHomGL (toMat g)) (by
        rw [Subgroup.coe_one, Units.val_one, Matrix.diagonal_one]) hqg
    have hconst : ∀ i : Fin n, toMat g i = u⁻¹ := by
      intro i
      apply Units.ext
      have h1 : (toMat g i : K) * (u : K) = 1 := (hu i).symm
      simpa using eq_inv_of_mul_eq_one_left h1
    have hmem : u⁻¹ ∈ μ := by
      have hi := hconst ⟨0, by omega⟩
      rw [← hi]
      simpa [toMat, toUnits] using (g.1 ⟨0, by omega⟩).2
    have hpowmu : (u⁻¹) ^ ℓ = 1 := by
      simpa using hμpow ⟨u⁻¹, hmem⟩
    have hprod : ∏ i : Fin n, toMat g i = 1 := by
      simpa [toMat, toUnits,
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_prodHom] using
        congrArg (fun y : μ => (y : Kˣ)) g.2
    have hupown : (u⁻¹) ^ n = 1 := by
      have h2 : ∏ i : Fin n, toMat g i = (u⁻¹) ^ n := by
        rw [Finset.prod_congr rfl (fun i _ => hconst i), Finset.prod_const]
        simp
      rw [← h2]
      exact hprod
    have hdvd : orderOf (u⁻¹) ∣ Nat.gcd ℓ n :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpowmu) (orderOf_dvd_of_pow_eq_one hupown)
    have hgcd : Nat.gcd ℓ n = 1 := (hℓ.coprime_iff_not_dvd.mpr hnℓ).gcd_eq_one
    have hu1 : u⁻¹ = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hgcd ▸ hdvd))
    have hgj : ∀ j : Fin n, g.1 j = 1 := by
      intro j
      apply Subtype.ext
      have hj := hconst j
      rw [hu1] at hj
      simpa [toMat, toUnits] using hj
    exact Subtype.ext (funext hgj)
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => mul_comm a b
  have hpowA : ∀ a : A, a ^ ℓ = 1 := fun a =>
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_ker_pow (m := n) hμpow a
  exact CFSG.SectionRank.le_pRank_of_injective (p := ℓ)
    (G := StatedProj (StatedSU n q K)) (H := ⊤) hℓ.one_lt hcomm hpowA
    (k := n - 1) hAcard f hf le_top

theorem w183fu_two_le_pRank_five {X : Type} [Group X] [Finite X] (h : IsU3 X 2) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) := by
  have hst : StatedClassicalModel X .PSU 3 2 2 := h.statedClassicalModel (by decide)
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hst
  have hEq : CFSG.Open.pRank 5 (⊤ : Subgroup X) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (StatedProj (StatedSU 3 (2 ^ 2) K))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e
  rw [hEq]
  have hrank := w183fu_le_pRank_statedPSU_torus (K := K) (q := 2 ^ 2) (n := 3)
    (ℓ := 5) hKcard (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using hrank

end CFSG.LocalAnalysis.WeakClosure81

end
