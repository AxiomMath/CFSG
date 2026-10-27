module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsGen
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.LocalAnalysis.EvenBN.TwoF4.CoprimeProduct
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def KS152J2InvolNine : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup Γ, Nat.card E = 9 → ∀ σ : MulAut Γ, σ ^ 2 = 1 →
      (∀ e ∈ E, σ e = e) → σ = 1

namespace Proof152Gen

theorem pow_apply_eq_of_forall {Γ : Type*} [Group Γ] {E : Subgroup Γ} {σ : MulAut Γ}
    (hfix : ∀ e ∈ E, σ e = e) (k : ℕ) : ∀ e ∈ E, (σ ^ k) e = e := by
  induction k with
  | zero => intro e _; rfl
  | succ k ih =>
    intro e he
    rw [pow_succ, MulAut.mul_apply, hfix e he, ih e he]

theorem eq_one_of_pow_two_pow (hK : KS152J2InvolNine) {Γ : Type} [Group Γ] [Finite Γ]
    (hΓ : Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup Γ}
    (hE : Nat.card E = 9) {σ : MulAut Γ} (hfix : ∀ e ∈ E, σ e = e) :
    ∀ n : ℕ, σ ^ (2 ^ n) = 1 → σ = 1
  | 0, h => by simpa using h
  | n + 1, h => by
    have hτ : (σ ^ (2 ^ n)) ^ 2 = 1 := by rw [← pow_mul, ← pow_succ]; exact h
    exact eq_one_of_pow_two_pow hK hΓ hE hfix n
      (hK Γ hΓ E hE _ hτ (pow_apply_eq_of_forall hfix _))

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaQuotCentralizer_of_fix (hK : KS152J2InvolNine) {L E : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hE9 : Nat.card ((E.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9)
    {y : G} (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (hyE : y ∈ Subgroup.centralizer (E : Set G)) {n : ℕ} (hyn : y ^ (2 ^ n) = 1) :
    y ∈ Sec4.thetaQuotCentralizer L := by
  set σ := Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨y, hyN⟩) with hσ
  have hfix : ∀ e ∈ (E.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      σ e = e := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hσ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    have hay : (a : G) * y = y * a :=
      Subgroup.mem_centralizer_iff.mp hyE a (Subgroup.mem_subgroupOf.mp ha)
    rw [← hay, mul_inv_cancel_right]
  have hpow : σ ^ (2 ^ n) = 1 := by
    have h1 : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ (2 ^ n) = 1 :=
      Subtype.ext (by simpa using hyn)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσ1 : σ = 1 := eq_one_of_pow_two_pow hK hJ hE9 hfix n hpow
  exact ⟨⟨y, hyN⟩, MonoidHom.mem_ker.mpr hσ1, rfl⟩

theorem card_map_inf_eq_nine
    {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9 := by
  obtain ⟨-, h9, -⟩ := j2_point_facts hD hJ
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hTcard : Nat.card (A.subgroupOf L) = 9 := by
    rw [← Subgroup.inf_subgroupOf_right, ← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv
  rw [← hTcard]
  refine Nat.card_congr (Equiv.ofBijective (π.subgroupMap (A.subgroupOf L))
    ⟨fun x y hxy => ?_, π.subgroupMap_surjective _⟩).symm
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hdisj : Disjoint (A.subgroupOf L) π.ker := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hTcard, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3)
  have hmem : (x : ↥L)⁻¹ * (y : ↥L) ∈ A.subgroupOf L ⊓ π.ker := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem x.2) y.2, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact congrArg Subtype.val hxy
  rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
  exact Subtype.ext (eq_of_inv_mul_eq_one hmem)

omit [Finite G] in
theorem commutator_le_of_eq_zpowers_sup' {A L U : Subgroup G} {c : G}
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hAab : IsMulCommutative A) (hcA : c ∈ A)
    (hUc : U ≤ Subgroup.centralizer ({c} : Set G))
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) : ⁅U, A⁆ ≤ L := by
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx.1⟩ ⟨c, hcA⟩)
  rw [Subgroup.commutator_le]
  intro u hu a ha
  have ha' : a ∈ ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) := by
    rw [← hAc]
    exact ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at ha'
  obtain ⟨z, hz, l, hl, rfl⟩ := Set.mem_mul.mp ha'
  have hzc : z ∈ Subgroup.zpowers c := hz
  have huz : u * z = z * u := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzc
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hUc hu)) k)
  have hzN : z ∈ Subgroup.normalizer (L : Set G) :=
    hAL ((Subgroup.zpowers_le.mpr hcA) hzc)
  have hul : u * l * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hUL hu) l).mp hl.2
  have hm : u * l * u⁻¹ * l⁻¹ ∈ L := mul_mem hul (inv_mem hl.2)
  have he : ⁅u, z * l⁆ = z * (u * l * u⁻¹ * l⁻¹) * z⁻¹ := by
    rw [commutatorElement_def]
    calc u * (z * l) * u⁻¹ * (z * l)⁻¹ = (u * z) * l * u⁻¹ * l⁻¹ * z⁻¹ := by group
      _ = (z * u) * l * u⁻¹ * l⁻¹ * z⁻¹ := by rw [huz]
      _ = z * (u * l * u⁻¹ * l⁻¹) * z⁻¹ := by group
  rw [he]
  exact (Subgroup.mem_normalizer_iff.mp hzN _).mp hm

theorem inf_mem_maxInvariantPiSubgroups
    (hK : KS152J2InvolNine) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {U : Subgroup G}
    (hU : U ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2)) :
    U ⊓ L ∈ maxInvariantPiSubgroups L A (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθdef
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  obtain ⟨-, -, hAc⟩ := j2_point_facts hD hJ
  have hUmem := hU.prop
  have hU2 : IsPGroup 2 U := isPGroup_of_mem_scriptQPi Nat.prime_two hUmem
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := hUmem.1.1.1.2.2
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD.le_normalizer
  have hUinv : U ∈ invariantPiSubgroups H A (piCompl 3) :=
    ⟨hUmem.1.2, isPiSubgroup_piCompl_three_of_piOf_two hUmem.2, hAU⟩
  have hUc : U ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_invariantPiSubgroups hD.mem_A hD.orderOf_eq hUinv
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_j2 h hJ
  have hUL : U ≤ Subgroup.normalizer (L : Set G) := hUc.trans hCL
  have hLH : L ≤ H := hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hθU : θ ≤ U := theta_le_of_mem_scriptQPiStar h hJ hU
  have hθ2 : IsPGroup 2 θ := (isPGroup_theta_of_j2 h hJ).map L.subtype
  have hE9 := card_map_inf_eq_nine hD hJ
  have hVmem : U ⊓ L ∈ invariantPiSubgroups L A (piOf 2) :=
    ⟨inf_le_right, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hU2.to_le inf_le_left),
      Late.le_normalizer_inf hAU hAL⟩
  have hUA : ⁅U, A⁆ ≤ U ⊓ L := le_inf
    (Subgroup.commutator_le.mpr fun u hu a ha => by
      rw [commutatorElement_def]
      have h1 : a * u⁻¹ * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hAU ha) _).mp (inv_mem hu)
      have h2 := mul_mem hu h1
      rwa [← mul_assoc, ← mul_assoc] at h2)
    (commutator_le_of_eq_zpowers_sup' hAc hAL hA.1.1 hD.mem_A hUc hUL)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card U) :=
    CFSG.LocalAnalysis.EvenBN.TwoF4.coprime_card_of_isPGroup Nat.prime_two hU2
      (by rw [hA.2]; norm_num)
  have hUsol : Group.IsSolvable U :=
    CFSG.LocalAnalysis.EvenBN.TwoF4.isSolvable_of_isPGroup Nat.prime_two hU2
  refine ⟨hVmem, fun R hR hVR => ?_⟩
  obtain ⟨R', hR', hRR'⟩ := exists_le_mem_maxInvariantPiSubgroups hR
  have hR'2 : IsPGroup 2 R' := (isPiSubgroup_piOf_iff Nat.prime_two _).mp hR'.prop.2.1
  have hR'L : R' ≤ L := hR'.prop.1
  have hθR' : θ ≤ R' := by
    have hR'θ : R' ≤ Subgroup.normalizer (θ : Set G) := hR'L.trans (Sec6.le_normalizer_theta L)
    have hmem : R' ⊔ θ ∈ invariantPiSubgroups L A (piOf 2) :=
      ⟨sup_le hR'L (Sec6.theta_le L),
        (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hR'2.to_sup_of_normal_right' hθ2 hR'θ),
        le_normalizer_sup hR'.prop.2.2 (hAL.trans (Sec6.normalizer_le_normalizer_theta L))⟩
    exact le_sup_right.trans (hR'.2 hmem le_sup_left)
  have hUR' : U ≤ Subgroup.normalizer (R' : Set G) := by
    refine Sec6.le_normalizer_of_forall_conj_mem fun u hu r hr => ?_
    obtain ⟨y, hy, w, hw, rfl⟩ :=
      CFSG.LocalAnalysis.EvenBN.TwoF4.exists_mul_inf_centralizer_commutator hAU hUsol hcop hu
    have hwR : w ∈ R' := hRR' (hVR (hUA hw))
    have hwr : w * r * w⁻¹ ∈ R' := mul_mem (mul_mem hwR hr) (inv_mem hwR)
    obtain ⟨n, hn⟩ := hU2 ⟨y, hy.1⟩
    have hyn : y ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hyC := mem_thetaQuotCentralizer_of_fix hK hJ hE9 (hUL hy.1) hy.2 hyn
    obtain ⟨-, hyl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hyC
    have hθm := hθR' (hyl _ (hR'L hwr))
    have he : y * w * r * (y * w)⁻¹ =
        (w * r * w⁻¹) * ((w * r * w⁻¹)⁻¹ * (y * (w * r * w⁻¹) * y⁻¹)) := by group
    rw [he]
    exact mul_mem hwr hθm
  have hUR'2 : IsPGroup 2 (U ⊔ R' : Subgroup G) := hU2.to_sup_of_normal_right' hR'2 hUR'
  have hinv : U ⊔ R' ∈ invariantPiSubgroups H A (piCompl 3) :=
    ⟨sup_le hUmem.1.2 (hR'L.trans hLH),
      isPiSubgroup_piCompl_three_of_piOf_two ((isPiSubgroup_piOf_iff Nat.prime_two _).mpr hUR'2),
      le_normalizer_sup hAU hR'.prop.2.2⟩
  have hmem : U ⊔ R' ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨(mem_scriptQ_of_hj_point h hJ hinv).1, hinv.1⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hUR'2⟩
  have hR'U : R' ≤ U := le_sup_right.trans (hU.2 hmem le_sup_left)
  exact hRR'.trans (le_inf hR'U hR'L)

theorem sixtyFour_dvd_card_map_inf
    (hK : KS152J2InvolNine) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {U : Subgroup G}
    (hU : U ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2)) :
    IsPGroup 2 (((U ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) ∧
      64 ∣ Nat.card (((U ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  obtain ⟨-, -, hAc⟩ := j2_point_facts hD hJ
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact isPGroup_theta_of_j2 h hJ
  have hAinv : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G) := by
    intro V hVL hV
    rw [hAc]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (V : Set G) ?_)) hV
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (hVL hv))
  have hVmax := inf_mem_maxInvariantPiSubgroups hK h hJ hU
  obtain ⟨hf, -⟩ := maxInvariant_two_transport π hπs hker hAinv
  have hVbar := (hf _ hVmax).1
  have hV2 : IsPGroup 2 (((U ⊓ L).subgroupOf L).map π) :=
    (isPiSubgroup_piOf_iff Nat.prime_two _).mp hVbar.prop.2.1
  refine ⟨hV2, ?_⟩
  have hT3 : IsPGroup 3 (A.subgroupOf L) :=
    hA.isPGroup.comap_of_ker_isPGroup L.subtype
      (IsPGroup.ker_isPGroup_of_injective L.subtype_injective)
  obtain ⟨P, hBP⟩ := (hT3.map π).exists_le_sylow
  have hB9 := card_map_inf_eq_nine hD hJ
  obtain ⟨-, -, -, -, h5⟩ := h415 _ hJ P _ rfl _ rfl
  obtain ⟨S₀, -, hS₀P, -, ⟨T, ⟨eT⟩⟩, -⟩ := h5 _ ⟨hBP, hB9⟩
  have h64 : 64 ≤ Nat.card S₀ := KFacts.KS14.le_card_of_mulEquiv_sylow_two_projSL T eT
  have hVbar' := hVbar
  rw [hS₀P] at hVbar'
  obtain ⟨x, -, hx⟩ := hVbar'
  have hcard : Nat.card (((U ⊓ L).subgroupOf L).map π) = Nat.card S₀ := by
    rw [← hx, conjugate, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
  rw [hcard] at hk
  rw [hcard, hk]
  have hk6 : 6 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (show (64 : ℕ) = 2 ^ 6 by norm_num) ▸ Nat.pow_dvd_pow 2 hk6

end Proof152Gen

open Proof152Gen

theorem step152GenS_of
    (hK : KS152J2InvolNine) : Step152GenS := by
  intro G _ _ A c L h Y M X _ d p P T K S hD hSH
  obtain ⟨h2, h64⟩ := sixtyFour_dvd_card_map_inf hK h hD.hj hSH
  have hle : S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ L ≤
      (S ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔ X :=
    inf_le_left.trans le_sup_left
  refine ⟨_, Subgroup.map_mono fun x hx => ?_, h2, h64⟩
  exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))

end CFSG.RankThree.PartTwo.Sec15
