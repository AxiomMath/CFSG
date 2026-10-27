module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofPa
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofFrattini
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofCent
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofUnitary
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
public import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open Item812Res3 (IsMaxPSub)
open Item812Res5 (actY actY_apply_mk actY_of_mem commutator_mem_of_actY_eq_one)
open scoped commutatorElement

namespace Item812Res6

theorem eq_bot_of_isPerfect_of_isSolvable {H : Type*} [Group H] {P : Subgroup H}
    (hp : Group.IsPerfect P) (hs : Group.IsSolvable P) : P = ⊥ := by
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  exact Group.IsPerfect.not_isSolvable P hs

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_theta_of_pow {Y : Subgroup G} {x : G}
    (hx : x ∈ (aschbacherSolvableCore 3 Y).map Y.subtype) {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    x = 1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  have hk' : t ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
  have := KFacts.eq_one_of_pow_three_pow_eq_one (Item812Res4.not_dvd_card_core Y) ht hk'
  simp [this]

theorem actY_eq_one_of_commutator_mem {Y : Subgroup G} {w : Subgroup.normalizer (Y : Set G)}
    (h : ∀ z ∈ Y, (w : G) * z * (w : G)⁻¹ * z⁻¹ ∈ (aschbacherSolvableCore 3 Y).map Y.subtype) :
    actY Y w = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H z =>
    rw [actY_apply_mk, MulAut.one_apply, QuotientGroup.eq]
    obtain ⟨t, ht, hte⟩ := h z z.2
    set c : Y := compAction Y w z with hc
    have hc' : (c : G) = (w : G) * z * (w : G)⁻¹ := rfl
    have htc : t = c * z⁻¹ := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hc']
      exact hte)
    have e : c⁻¹ * z = (z⁻¹ * t * z)⁻¹ := by rw [htc]; group
    rw [e]
    exact (aschbacherSolvableCore 3 Y).inv_mem
      ((inferInstance : (aschbacherSolvableCore 3 Y).Normal).conj_mem' t ht z)

theorem commute_of_actY_eq_one {Y Pa : Subgroup G} (hPa : IsPGroup 3 Pa)
    {w : Subgroup.normalizer (Y : Set G)} (hwPa : (w : G) ∈ Pa) (hw : actY Y w = 1) {y : G}
    (hyPa : y ∈ Pa) (hyY : y ∈ Y) : (w : G) * y = y * w := by
  have h1 := commutator_mem_of_actY_eq_one hw y hyY
  have hmem : (w : G) * y * (w : G)⁻¹ * y⁻¹ ∈ Pa :=
    Pa.mul_mem (Pa.mul_mem (Pa.mul_mem hwPa hyPa) (Pa.inv_mem hwPa)) (Pa.inv_mem hyPa)
  obtain ⟨k, hk⟩ := hPa ⟨_, hmem⟩
  have hk' : ((w : G) * y * (w : G)⁻¹ * y⁻¹) ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h2 := eq_one_of_mem_theta_of_pow h1 hk'
  calc (w : G) * y = (w : G) * y * (w : G)⁻¹ * y⁻¹ * (y * w) := by group
    _ = y * w := by rw [h2, one_mul]

theorem isInnerAut_pow_three_of_projSp_eight {M : Type*} [Group M]
    (e : M ≃* projSp 2 (GaloisField 2 3)) {μ : MulAut M} (hμ : μ ^ 9 = 1) :
    IsInnerAut (μ ^ 3) := by
  set K := GaloisField 2 3
  set e' := e.trans (Sec4.projSpEquivStatedProj 2 K)
  suffices h : IsInnerAut (MulAut.congr e' μ ^ 3) by
    rwa [← map_pow, isInnerAut_congr] at h
  have hK : Nat.card K = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num) hK
  obtain ⟨-, -, -, -, -, hcard, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (by norm_num) hFr hord hzp
  set π := QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K))) with hπ
  set ν := MulAut.congr e' μ with hν
  have hν9 : ν ^ 9 = 1 := by rw [hν, ← map_pow, hμ, map_one]
  have h9 : (π ν) ^ 9 = 1 := by rw [← map_pow, hν9, map_one]
  have h6 : orderOf (π ν) ∣ 6 := by
    have := orderOf_dvd_natCard (π ν)
    rwa [hcard] at this
  have h9' : orderOf (π ν) ∣ 9 := orderOf_dvd_of_pow_eq_one h9
  have h3 : orderOf (π ν) ∣ 3 := by
    have := Nat.dvd_gcd h6 h9'
    norm_num at this
    exact this
  have h3' : π (ν ^ 3) = 1 := by
    rw [map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3'

theorem sec8J_ne_bot_of_projSp {X : Subgroup G} {a : G} (hout : InducesOuterTheta a X)
    (ha3 : a ^ 3 = 1)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3))) :
    sec8J X a ≠ ⊥ := by
  have hX' : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * 1))) := by
    simpa using hX
  obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp one_ne_zero ha3 hout hX'
  have hq := Item87Res2Proof.isQuasisimple_inSubgroup_perfectResidual_of_projSp le_rfl ι
  have hnt : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp (LocalCores.isQuasisimple_nontrivial hq)
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq hout.1 ⟨1, by rwa [pow_one]⟩
  intro h0
  apply hnt
  rw [← himg]
  change imageModTheta X (sec8J X a) = ⊥
  rw [h0, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]

end Item812Res6

namespace Item812Res6

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_trivial_mod_theta {X Y J : Subgroup G} {b u : G}
    (hX : X ∈ thetaComponentsAt 3 b) (hub : u ∈ Subgroup.centralizer ({b} : Set G))
    (huY : u ∈ Subgroup.normalizer (Y : Set G))
    (hutriv : ∀ z ∈ Y, u * z * u⁻¹ * z⁻¹ ∈ (aschbacherSolvableCore 3 Y).map Y.subtype)
    (hJX : J ≤ X) (hJY : J ≤ Y) (hJp : Group.IsPerfect J) (hJ : J ≠ ⊥) :
    u ∈ Subgroup.normalizer (X : Set G) := by
  by_contra hu
  have hne := Sec6.ne_map_conj_of_not_mem_normalizer hu
  have hXu := Sec6.map_conj_mem_thetaComponentsAt hub hX
  have hcomm := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hX hXu hne
  set θC := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) with hθC
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  set Ĵ := (J.subgroupOf Y).map π with hĴ
  set Ŝ := ((θC ⊓ Y).subgroupOf Y).map π with hŜ
  have hJYp : Group.IsPerfect (J.subgroupOf Y) :=
    hJp.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJY).symm.surjective
  have hĴp : Group.IsPerfect Ĵ := Group.IsPerfect.map π
  have hθCs : Group.IsSolvable θC := by
    have hθ : Group.IsSolvable
        (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({b} : Set G))) :=
      (solvable_prime_complement_core_characterization Nat.prime_three).1
    exact Group.isSolvable_of_surjective
      ((Subgroup.centralizer ({b} : Set G)).subtype.subgroupMap_surjective _)
  have hθCYs : Group.IsSolvable ((θC ⊓ Y).subgroupOf Y) := by
    have h1 : Group.IsSolvable (θC ⊓ Y : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : θC ⊓ Y ≤ Y)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : θC ⊓ Y ≤ Y)).symm.surjective
  have hŜs : Group.IsSolvable Ŝ := Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
  have hle : ⁅Ĵ, Ĵ⁆ ≤ Ŝ := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    have hpJ : (p : G) ∈ J := Subgroup.mem_subgroupOf.mp hp
    have hqJ : (q : G) ∈ J := Subgroup.mem_subgroupOf.mp hq
    obtain ⟨s, hs, hse⟩ := hutriv q q.2
    have hqu : u * (q : G) * u⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp huY q).mp q.2
    set q' : Y := ⟨u * (q : G) * u⁻¹, hqu⟩ with hq'
    have hse' : (s : G) = u * (q : G) * u⁻¹ * (q : G)⁻¹ := hse
    have hq's : q' = s * q := Subtype.ext (by
      rw [Subgroup.coe_mul, hse', hq']
      group)
    have hs1 : π s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
    have hπq : π q' = π q := by
      rw [hq's, map_mul, hs1, one_mul]
    have hmem : ((p * q' * p⁻¹ * q'⁻¹ : Y) : G) ∈ θC ⊓ Y := by
      refine ⟨?_, (p * q' * p⁻¹ * q'⁻¹).2⟩
      apply hcomm
      have hq'X : (q' : G) ∈ X.map (MulAut.conj u).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨q, hJX hqJ, rfl⟩
      have hc := Subgroup.commutator_mem_commutator (hJX hpJ) hq'X
      rw [commutatorElement_def] at hc
      simpa using hc
    refine ⟨p * q' * p⁻¹ * q'⁻¹, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hπq]
  have hĴs : Group.IsSolvable Ĵ := by
    have h1 : Ĵ ≤ Ŝ := by
      calc Ĵ = ⁅Ĵ, Ĵ⁆ := (Subgroup.isPerfect_iff.mp hĴp).symm
        _ ≤ Ŝ := hle
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)
  have hĴ1 : Ĵ = ⊥ := eq_bot_of_isPerfect_of_isSolvable hĴp hĴs
  have hJθ : ∀ y : G, ∀ hy : y ∈ J, (⟨y, hJY hy⟩ : Y) ∈ aschbacherSolvableCore 3 Y := by
    intro y hy
    have h1 : π ⟨y, hJY hy⟩ ∈ Ĵ := ⟨⟨y, hJY hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hĴ1, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hθ : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  let f : J →* aschbacherSolvableCore 3 Y :=
    { toFun := fun y => ⟨⟨y, hJY y.2⟩, hJθ y y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hfinj : Function.Injective f := by
    intro y z h
    exact Subtype.ext (congrArg (fun w : aschbacherSolvableCore 3 Y => ((w : Y) : G)) h)
  exact hJ (eq_bot_of_isPerfect_of_isSolvable hJp
    (Group.isSolvable_of_isSolvable_injective hfinj))

theorem false_of_mem_normalizer_of_pow {X : Subgroup G} {a u : G}
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)))
    (hout : InducesOuterTheta a X) (huN : u ∈ Subgroup.normalizer (X : Set G))
    (hu9 : u ^ 9 = 1) (hau : a ∈ Subgroup.zpowers (u ^ 3)) : False := by
  obtain ⟨haN, hout⟩ := hout
  obtain ⟨e⟩ := hX
  set φ := (thetaQuotMulAut X).comp (compAction X) with hφ
  have hμ9 : φ ⟨u, huN⟩ ^ 9 = 1 := by
    rw [← map_pow]
    have : (⟨u, huN⟩ : Subgroup.normalizer (X : Set G)) ^ 9 = 1 :=
      Subtype.ext (by simpa using hu9)
    rw [this, map_one]
  have hinner := isInnerAut_pow_three_of_projSp_eight e hμ9
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hau
  have hak : (⟨a, haN⟩ : Subgroup.normalizer (X : Set G)) = (⟨u, huN⟩ ^ 3) ^ k :=
    Subtype.ext (by simp [← hk])
  apply hout
  change φ ⟨a, haN⟩ ∈ _
  rw [hak, map_zpow, map_pow]
  exact Subgroup.zpow_mem _ hinner k


theorem exists_mem_inf_of_pow_three {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) {Pa : Subgroup G}
    (hPa : IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G))) {x : G} (hxPa : x ∈ Pa)
    (hx3 : x ^ 3 = 1) :
    ∃ y ∈ Pa ⊓ Y, x * y⁻¹ ∈ Subgroup.zpowers a ∧ x * y⁻¹ * y = y * (x * y⁻¹) := by
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a haA
  have h3 := h.toTheoremFourHyp.localRank_three.le
  have hY := h.mem_thetaComponentsAt_Y
  have hPaH : Pa ≤ Subgroup.centralizer ({a} : Set G) := hPa.1
  have hPap : IsPGroup 3 Pa := hPa.2.1
  obtain ⟨y, hyPY, hvN, hvact⟩ := Item812Res5.exists_mem_inf_of_mem_pa h hPa hxPa
  have hvPa : x * y⁻¹ ∈ Pa := Pa.mul_mem hxPa (Pa.inv_mem hyPY.1)
  have hvy : x * y⁻¹ * y = y * (x * y⁻¹) :=
    commute_of_actY_eq_one hPap (w := ⟨x * y⁻¹, hvN⟩) hvPa hvact hyPY.1 hyPY.2
  have hv3 : (x * y⁻¹) ^ 3 = 1 := by
    have hcy : Commute (x * y⁻¹) y := hvy
    have hx' : x = x * y⁻¹ * y := by group
    have h1 : (x * y⁻¹) ^ 3 * y ^ 3 = 1 := by
      rw [← hcy.mul_pow, ← hx', hx3]
    have hv3Y : (x * y⁻¹) ^ 3 ∈ Y := by
      have : (x * y⁻¹) ^ 3 = (y ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Y.inv_mem (Y.pow_mem hyPY.2 3)
    have hv3N : (x * y⁻¹) ^ 3 ∈ Subgroup.normalizer (Y : Set G) := Subgroup.pow_mem _ hvN 3
    have hv3act : actY Y ⟨(x * y⁻¹) ^ 3, hv3N⟩ = 1 := by
      have e : (⟨(x * y⁻¹) ^ 3, hv3N⟩ : Subgroup.normalizer (Y : Set G)) =
          ⟨x * y⁻¹, hvN⟩ ^ 3 := Subtype.ext (by simp)
      rw [e, map_pow, hvact, one_pow]
    rw [actY_of_mem hv3Y] at hv3act
    have hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
      rcases h.item89_Y with h9 | h6
      · obtain ⟨e⟩ := h9
        rw [← Subgroup.map_center_eq e.symm, Item812Res3.isYModel_alternatingGroup_nine.1,
          Subgroup.map_bot]
      · obtain ⟨e⟩ := h6
        rw [← Subgroup.map_center_eq e.symm, Item812Res3.isYModel_projSp_three_two.1,
          Subgroup.map_bot]
    set g : Y ⧸ aschbacherSolvableCore 3 Y :=
      ((⟨(x * y⁻¹) ^ 3, hv3Y⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) with hg
    have hgc : g ∈ Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h2 := congrArg (fun φ => φ z) hv3act
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc z * g = g * z * g⁻¹ * g := by rw [h2]
        _ = g * z := by group
    rw [hZ, Subgroup.mem_bot, hg, QuotientGroup.eq_one_iff] at hgc
    obtain ⟨k', hk'⟩ := hPap ⟨_, Pa.pow_mem hvPa 3⟩
    have hk'' : ((x * y⁻¹) ^ 3) ^ 3 ^ k' = 1 := by simpa using congrArg Subtype.val hk'
    exact eq_one_of_mem_theta_of_pow ⟨_, hgc, rfl⟩ hk''
  have hva : x * y⁻¹ ∈ Subgroup.zpowers a := by
    have hcomm : x * y⁻¹ * a = a * (x * y⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPaH hvPa)
    rcases h.item89_Y with h9 | h6
    · obtain ⟨e⟩ := h9
      exact Item812Res3.mem_zpowers_of_thetaQuotMulAut_eq_one h3 ha3 ha1 hY
        Item812Res3.isYModel_alternatingGroup_nine e hcomm hv3 hvN hvact
    · obtain ⟨e⟩ := h6
      exact Item812Res3.mem_zpowers_of_thetaQuotMulAut_eq_one h3 ha3 ha1 hY
        Item812Res3.isYModel_projSp_three_two e hcomm hv3 hvN hvact
  exact ⟨y, hyPY, hva, hvy⟩

theorem zpowers_sup_inf_eq {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X Y : Subgroup G} {n : ℕ} (h : Sec8Final G A c L a b X Y n) :
    Subgroup.zpowers a ⊔ (A ⊓ Y) = A := by
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx a haA)
  obtain ⟨Pa, hPa, hAPa⟩ :=
    Item812Res4.exists_isMaxPSub_le (Item812Res4.isPGroup_of_isElemAbelian hAab) hAC
  refine le_antisymm (sup_le ((Subgroup.zpowers_le).mpr haA) inf_le_left) fun x hx => ?_
  obtain ⟨y, hyPY, hva, -⟩ := exists_mem_inf_of_pow_three h hPa (hAPa hx) (hAab.2 x hx)
  have hyA : y ∈ A := by
    have e : y = (x * y⁻¹)⁻¹ * x := by group
    rw [e]
    exact A.mul_mem (A.inv_mem ((Subgroup.zpowers_le).mpr haA hva)) hx
  have e : x = x * y⁻¹ * y := by group
  rw [e]
  exact Subgroup.mul_mem_sup hva ⟨hyA, hyPY.2⟩

end Item812Res6

open Item812Res6


theorem fin812PaExp_of_84 (h84 : Pair84A) : Fin812PaExp := by
  intro G _ _ A c L a b X Y n h Pa hPa hAPa w hwPa hwtriv
  by_contra hw3
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb3 : b ^ 3 = 1 := h.mem_partTwoF.1.2 b hbA
  have h3 := h.toTheoremFourHyp.localRank_three.le
  have hY := h.mem_thetaComponentsAt_Y
  set H := Subgroup.centralizer ({a} : Set G) with hH
  have hNY := h.normalizer_zpowers_le_normalizer_Y
  have hHN : H ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
    hNY (Item812Res2.mem_normalizer_zpowers_of_commute
      (Subgroup.mem_centralizer_singleton_iff.mp hx))
  have hPaH : Pa ≤ H := hPa.1
  have hPap : IsPGroup 3 Pa := hPa.2.1
  have hout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h.toSec8Pair with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  have hJ : sec8J X a ≠ ⊥ := sec8J_ne_bot_of_projSp hout ha3 h.item89_X
  have hJp : Group.IsPerfect (sec8J X a) :=
    Item86ResProof.isPerfect_inSubgroup_perfectResidual' _
  have hJX : sec8J X a ≤ X := (Subgroup.map_subtype_le _).trans inf_le_left
  have hJY : sec8J X a ≤ Y := le_sup_right.trans h.le_Y
  obtain ⟨k, hk⟩ := hPap ⟨w, hwPa⟩
  have hwk : w ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hwk)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    apply hw3
    have hdvd : orderOf w ∣ 3 := by
      rw [hj]
      simpa using pow_dvd_pow 3 (show j ≤ 1 by omega)
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  set u := w ^ 3 ^ (j - 2) with hu
  have hu9 : u ^ 9 = 1 := by
    rw [hu, ← pow_mul, show 3 ^ (j - 2) * 9 = 3 ^ j by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega, ← hj, pow_orderOf_eq_one]
  have hu3 : u ^ 3 ≠ 1 := by
    intro h1
    rw [hu, ← pow_mul, ← pow_succ] at h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at this
    have := Nat.le_of_dvd (by positivity) this
    have h' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp this
    omega
  have huPa : u ∈ Pa := Pa.pow_mem hwPa _
  have huH : u ∈ H := hPaH huPa
  have huN : u ∈ Subgroup.normalizer (Y : Set G) := hHN huH
  have hwN : w ∈ Subgroup.normalizer (Y : Set G) := hHN (hPaH hwPa)
  have hwact : actY Y ⟨w, hwN⟩ = 1 := actY_eq_one_of_commutator_mem hwtriv
  have huact : actY Y ⟨u, huN⟩ = 1 := by
    have e : (⟨u, huN⟩ : Subgroup.normalizer (Y : Set G)) = ⟨w, hwN⟩ ^ 3 ^ (j - 2) :=
      Subtype.ext (by simp [hu])
    rw [e, map_pow, hwact, one_pow]
  have hutriv := commutator_mem_of_actY_eq_one huact
  have hua : u * a = a * u := Subgroup.mem_centralizer_singleton_iff.mp huH
  have hu3N : u ^ 3 ∈ Subgroup.normalizer (Y : Set G) := Subgroup.pow_mem _ huN 3
  have hu3act : actY Y ⟨u ^ 3, hu3N⟩ = 1 := by
    have e : (⟨u ^ 3, hu3N⟩ : Subgroup.normalizer (Y : Set G)) = ⟨u, huN⟩ ^ 3 :=
      Subtype.ext (by simp)
    rw [e, map_pow, huact, one_pow]
  have hu3a : u ^ 3 ∈ Subgroup.zpowers a := by
    have hcomm : u ^ 3 * a = a * u ^ 3 := (Commute.pow_left hua 3).eq
    have hcube : (u ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact hu9
    rcases h.item89_Y with h9 | h6
    · obtain ⟨e⟩ := h9
      exact Item812Res3.mem_zpowers_of_thetaQuotMulAut_eq_one h3 ha3 ha1 hY
        Item812Res3.isYModel_alternatingGroup_nine e hcomm hcube hu3N hu3act
    · obtain ⟨e⟩ := h6
      exact Item812Res3.mem_zpowers_of_thetaQuotMulAut_eq_one h3 ha3 ha1 hY
        Item812Res3.isYModel_projSp_three_two e hcomm hcube hu3N hu3act
  have hau : a ∈ Subgroup.zpowers (u ^ 3) := by
    have hle : Subgroup.zpowers (u ^ 3) ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hu3a
    have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have hou : orderOf (u ^ 3) = 3 := orderOf_eq_prime (by rw [← pow_mul]; exact hu9) hu3
    have heq : Subgroup.zpowers (u ^ 3) = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hou])
    rw [heq]
    exact Subgroup.mem_zpowers a
  obtain ⟨y, hyPY, hva, -⟩ := exists_mem_inf_of_pow_three h hPa (hAPa hbA) hb3
  have huv : u * (b * y⁻¹) = (b * y⁻¹) * u := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hva
    rw [← hi]
    exact (Commute.zpow_right hua i).eq
  have huy : u * y = y * u :=
    commute_of_actY_eq_one hPap (w := ⟨u, huN⟩) huPa huact hyPY.1 hyPY.2
  have hub : u ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * b = u * (b * y⁻¹) * y := by group
      _ = b * y⁻¹ * u * y := by rw [huv]
      _ = b * y⁻¹ * (u * y) := by group
      _ = b * y⁻¹ * (y * u) := by rw [huy]
      _ = b * u := by group
  have huX : u ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_of_trivial_mod_theta h.pairRel.2.2.1 hub huN hutriv hJX hJY hJp hJ
  exact false_of_mem_normalizer_of_pow h.item89_X hout huX hu9 hau

theorem fin812PaSplit_of_84 (h84 : Pair84A) : Fin812PaSplit :=
  fin812PaSplit_of_exp (fin812PaExp_of_84 h84)

end CFSG.RankThree.PartTwo.Sec8
