module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLSetup
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeisCore
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec4.Item4442Proof
import CFSG.RankThree.PartTwo.Sec18.Item184a

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial
open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_perfectResidual_of_commutator_eq {Y : Type*} [Group Y] {K : Subgroup Y}
    (hK : ⁅K, K⁆ = K) : K ≤ CFSG.perfectResidual Y := by
  refine le_iInf fun n => ?_
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ, ← hK]
    exact commutator_mono ih ih

section Ctx


theorem Ctx4443.commutator_zpowers_eq {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s)
    (hIq : CFSG.IsQuasisimple (inSubgroup perfectResidual H ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual H))) :
    ⁅inSubgroup perfectResidual H, zpowers s⁆ = inSubgroup perfectResidual H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := inSubgroup perfectResidual H with hI
  have hIp : Group.IsPerfect I := isPerfect_iff.mpr (Sec18.commutator_inSubgroup_perfectResidual H)
  obtain ⟨hsN, hnot⟩ := h.concl4442.2.2.1.inducesOuterTheta I (by decide)
  by_contra hne
  have hcen := forall_mem_pCoreOf_of_commutator_ne hIp hIq (zpowers_le.mpr hsN) hne s
    (mem_zpowers s)
  have hθ : CFSG.pCore 2 I ≤ aschbacherSolvableCore 3 I :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.1 _ CFSG.pCore_normal
      (isSolvable_of_isPGroup CFSG.pCore_isPGroup)
      (not_three_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup)
  apply hnot
  refine ⟨1, ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [map_one, MulAut.one_apply, thetaQuotMulAut_mk, QuotientGroup.eq]
    have hc : ((compAction I ⟨s, hsN⟩ y : I) : G) = s * y * s⁻¹ := rfl
    have h1 : compAction I ⟨s, hsN⟩ y * y⁻¹ ∈ CFSG.pCore 2 I := by
      rw [Sec18.mem_pCore_iff_mem_pCoreOf, Subgroup.coe_mul, hc, Subgroup.coe_inv]
      exact hcen y y.2
    have h2 := (CFSG.pCore_normal (p := 2) (G := I)).conj_mem _ h1 y⁻¹
    rw [show y⁻¹ * (compAction I ⟨s, hsN⟩ y * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * compAction I ⟨s, hsN⟩ y by
      group] at h2
    exact hθ h2

theorem Ctx4443.exists_inner {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s) :
    ∀ a ∈ A, ∃ i ∈ inSubgroup perfectResidual H, ∀ x ∈ inSubgroup perfectResidual H,
      (a * x * a⁻¹)⁻¹ * (i * x * i⁻¹) ∈ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro a ha
  obtain ⟨hsP, -, -, hsH, X, hXn, hXZ, hXtop, -⟩ := h.concl4442
  have hAH : A ≤ H := Sec18.le_of_mem_scriptH₀ h.mem_scriptH₀
  set I := inSubgroup perfectResidual H with hI
  set P := CFSG.pCore 2 H with hP
  set φ := QuotientGroup.mk' P with hφ
  set sb := φ ⟨s, hsH⟩ with hsb
  set q := QuotientGroup.mk' X with hq
  have hpow : ∀ z : H ⧸ P, q z ∈ zpowers (q sb) := by
    intro z
    have hz : z ∈ X ⊔ zpowers sb := hXtop ▸ mem_top z
    have hz' := mem_map_of_mem q hz
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers,
      (map_eq_bot_iff X).mpr (by rw [hq, QuotientGroup.ker_mk']), bot_sup_eq] at hz'
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)) ⟨s, hsP⟩
  have hj' : (⟨s, hsH⟩ : H) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
  have hsb2 : (q sb) ^ (2 ^ j) = 1 := by rw [hsb, ← map_pow, ← map_pow, hj', map_one, map_one]
  have hq2 : ∀ z : H ⧸ P, (q z) ^ (2 ^ j) = 1 := by
    intro z
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hpow z)
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsb2, one_zpow]
  have haX : φ ⟨a, hAH ha⟩ ∈ X := by
    obtain ⟨e, he⟩ := h.ctx444.isE27.isPGroup ⟨a, ha⟩
    have he' : (⟨a, hAH ha⟩ : H) ^ (3 ^ e) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val he)
    have h3 : (q (φ ⟨a, hAH ha⟩)) ^ (3 ^ e) = 1 := by
      rw [← map_pow, ← map_pow, he', map_one, map_one]
    have h1 := KFacts.KS18.eq_one_of_pow_two_of_pow_three (hq2 _) h3
    rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  set R := CFSG.perfectResidual H with hR
  have hRc := CFSG.perfect_residual_characterization (G := H)
  have hRp : ⁅R, R⁆ = R := isPerfect_iff.mp hRc.2.2.1
  set Ib := R.map φ with hIb
  have hIbp : ⁅Ib, Ib⁆ = Ib := by rw [hIb, ← map_commutator, hRp]
  have hIbX : Ib ≤ X := by
    rw [← hIbp, commutator_le]
    intro u _ v _
    rw [← QuotientGroup.ker_mk' X, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm, ← hq]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hpow u)
    obtain ⟨l, hl⟩ := mem_zpowers_iff.mp (hpow v)
    rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
  have hNc := CFSG.perfect_residual_characterization (G := X)
  have : (CFSG.perfectResidual X).Characteristic := hNc.2.1
  have : Group.IsPerfect (CFSG.perfectResidual X) := hNc.2.2.1
  have hIbN : Ib ≤ (CFSG.perfectResidual X).map X.subtype :=
    Sec18.le_inSubgroup_perfectResidual hIbp hIbX
  have hNIb : (CFSG.perfectResidual X).map X.subtype ≤ Ib := by
    have hNp : ⁅(CFSG.perfectResidual X).map X.subtype, (CFSG.perfectResidual X).map X.subtype⁆ =
        (CFSG.perfectResidual X).map X.subtype := by
      rw [← map_commutator, isPerfect_iff.mp hNc.2.2.1]
    rw [hIb, Sec18.map_perfectResidual_eq (QuotientGroup.mk'_surjective P)]
    exact le_perfectResidual_of_commutator_eq hNp
  obtain ⟨n, hn, hconj⟩ := Item4442.exists_mem_conj_eq_of_isZ3L34OrHeisSL34 hXZ hNc.2.2.2.1
    (⟨φ ⟨a, hAH ha⟩, haX⟩ : X)
  obtain ⟨r, hr, hrn⟩ := hNIb ⟨n, hn, rfl⟩
  refine ⟨(r : G), ⟨r, hr, rfl⟩, fun x hx => ?_⟩
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨xX, hxX, hxXe⟩ := hIbN ⟨x', hx', rfl⟩
  have h1 := congrArg Subtype.val (hconj xX hxX)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have h2 : φ (⟨a, hAH ha⟩ * x' * (⟨a, hAH ha⟩ : H)⁻¹) = φ (r * x' * r⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hrn]
    simp only [Subgroup.coe_subtype] at hxXe
    rw [← hxXe]
    exact h1
  rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Sec18.mem_pCore_iff_mem_pCoreOf] at h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have hIH : I ≤ H := map_subtype_le _
  have hAI : A ≤ normalizer (I : Set G) :=
    hAH.trans (Sec18.le_normalizer_inSubgroup_perfectResidual H)
  have hmemI : (a * (x' : G) * a⁻¹)⁻¹ * ((r : G) * x' * (r : G)⁻¹) ∈ I := by
    refine I.mul_mem (I.inv_mem ((mem_normalizer_iff.mp (hAI ha) _).mp ⟨x', hx', rfl⟩))
      (I.mul_mem (I.mul_mem ⟨r, hr, rfl⟩ ⟨x', hx', rfl⟩) (I.inv_mem ⟨r, hr, rfl⟩))
  have hle : CFSG.Open.pCoreOf 2 H ⊓ I ≤ CFSG.Open.pCoreOf 2 I := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
    exact fun y hy => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf H (hIH hy), le_normalizer hy⟩
  exact hle ⟨h2, hmemI⟩

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
