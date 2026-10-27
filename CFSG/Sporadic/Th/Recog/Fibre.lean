module

public import CFSG.Sporadic.Th.Recog.Swap
public import CFSG.Sporadic.Th.Recog.EightDim
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GriessLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CompatC
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseExtraspecial
public import CFSG.RankThree.Literature.FSmithInvolution

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Max3.InvRep
open CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G]

local instance (priority := high) instAddCommGroupZMod2Fibre : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

noncomputable def eQM : ↥(Max3.Q.subgroupOf Max3.M) ≃* ↥Max3.Q :=
  Subgroup.subgroupOfEquivOfLe Max3.Q_le_M

theorem eQM_val (x : ↥(Max3.Q.subgroupOf Max3.M)) :
    ((eQM x : ↥Max3.Q) : J) = ((x : ↥(Max3.Q.subgroupOf Max3.M)) : J) :=
  Subgroup.subgroupOfEquivOfLe_apply_coe Max3.Q_le_M x

private theorem isExtraspecial_Q_M :
    IsExtraspecialPGroup 2 ↥(Max3.Q.subgroupOf Max3.M) :=
  CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
    (P := ↥Max3.Q) (R := ↥(Max3.Q.subgroupOf Max3.M)) eQM.symm Max3.isExtraspecialPGroup_Q

theorem mem_toSetting_Q_iff (S : ThSetting G) (x : S.toSetting.M) :
    x ∈ S.toSetting.Q ↔ (x : G) ∈ S.Q := by
  constructor
  · intro h
    rw [S.toSetting_Q_eq] at h
    exact Subgroup.mem_subgroupOf.mp h
  · intro h
    rw [S.toSetting_Q_eq]
    exact Subgroup.mem_subgroupOf.mpr h

structure FibreData (S : ThSetting G) where
  θ : S.toSetting.M →* alternatingGroup (Fin 9)
  θ_surj : Function.Surjective θ
  θ_ker : θ.ker = S.toSetting.Q
  φQ : ↥S.toSetting.Q ≃* ↥(Max3.Q.subgroupOf Max3.M)
  fwd : ∀ h : S.toSetting.M, ∃ m : Max3.M, kap m = θ h ∧ ∀ x : S.toSetting.Q,
    φQ (conjAut S.toSetting.normal h x) = conjAut instNormalQSubgroupOfM m (φQ x)
  bwd : ∀ m : Max3.M, ∃ h : S.toSetting.M, kap m = θ h ∧ ∀ x : S.toSetting.Q,
    φQ (conjAut S.toSetting.normal h x) = conjAut instNormalQSubgroupOfM m (φQ x)

namespace FibreData

variable {S : ThSetting G}

private theorem conjAut_mul {H : Type*} [Group H] {Q : Subgroup H} [hQn : Q.Normal]
    (g g' : H) (x : Q) : conjAut hQn (g * g') x = conjAut hQn g (conjAut hQn g' x) := by
  simp only [conjAut, map_mul, MulAut.mul_apply]

private theorem conjAut_one {H : Type*} [Group H] {Q : Subgroup H} [hQn : Q.Normal]
    (x : Q) : conjAut hQn 1 x = x := by
  simp only [conjAut, map_one, MulAut.one_apply]

private theorem conjAut_eq_one_of_mem_center {H : Type*} [Group H] {Q : Subgroup H}
    [hQn : Q.Normal] {c : Q} (hc : c ∈ Subgroup.center Q) : conjAut hQn (c : H) = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [conjAut_apply, MulAut.one_apply]
  have h : (c : H) * (x : H) = (x : H) * (c : H) := by
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hc x).symm
  calc (c : H) * (x : H) * (c : H)⁻¹ = ((x : H) * (c : H)) * (c : H)⁻¹ := by rw [h]
    _ = (x : H) := by rw [mul_assoc, mul_inv_cancel, mul_one]

@[expose] def Fpair (Fd : FibreData S) (h : S.toSetting.M) (m : Max3.M) : Prop :=
  kap m = Fd.θ h ∧ ∀ x : S.toSetting.Q,
    Fd.φQ (conjAut S.toSetting.normal h x) = conjAut instNormalQSubgroupOfM m (Fd.φQ x)

@[expose] def F (Fd : FibreData S) : Subgroup (S.toSetting.M × Max3.M) where
  carrier := {p | Fd.Fpair p.1 p.2}
  one_mem' := by
    change Fd.Fpair (1 : S.toSetting.M) (1 : Max3.M)
    exact ⟨by rw [map_one, map_one], fun x => by rw [conjAut_one, conjAut_one]⟩
  mul_mem' := by
    rintro ⟨h₁, m₁⟩ ⟨h₂, m₂⟩ h₁m₁ h₂m₂
    change Fd.Fpair (h₁ * h₂) (m₁ * m₂)
    obtain ⟨hk₁, ha₁⟩ := h₁m₁
    obtain ⟨hk₂, ha₂⟩ := h₂m₂
    refine ⟨?_, fun x => ?_⟩
    · show kap (m₁ * m₂) = Fd.θ (h₁ * h₂)
      rw [map_mul, map_mul, hk₁, hk₂]
    · show Fd.φQ (conjAut S.toSetting.normal (h₁ * h₂) x) =
        conjAut instNormalQSubgroupOfM (m₁ * m₂) (Fd.φQ x)
      rw [conjAut_mul, ha₁, ha₂, conjAut_mul]
  inv_mem' := by
    rintro ⟨h, m⟩ hmem
    change Fd.Fpair h⁻¹ m⁻¹
    obtain ⟨hk, ha⟩ := hmem
    have ha' : ∀ x : S.toSetting.Q, Fd.φQ (conjAut S.toSetting.normal h x) =
        conjAut instNormalQSubgroupOfM m (Fd.φQ x) := ha
    refine ⟨?_, fun x => ?_⟩
    · show kap m⁻¹ = Fd.θ h⁻¹
      rw [map_inv, map_inv, hk]
    · show Fd.φQ (conjAut S.toSetting.normal h⁻¹ x) = conjAut instNormalQSubgroupOfM m⁻¹ (Fd.φQ x)
      have hx' : conjAut instNormalQSubgroupOfM m
          (Fd.φQ (conjAut S.toSetting.normal h⁻¹ x)) =
          conjAut instNormalQSubgroupOfM m (conjAut instNormalQSubgroupOfM m⁻¹ (Fd.φQ x)) := by
        rw [← ha' (conjAut S.toSetting.normal h⁻¹ x)]
        rw [← conjAut_mul, mul_inv_cancel, conjAut_one]
        rw [← conjAut_mul, mul_inv_cancel, conjAut_one]
      exact (conjAut instNormalQSubgroupOfM m).injective hx'

theorem mem_F_iff (Fd : FibreData S) (h : S.toSetting.M) (m : Max3.M) :
    (h, m) ∈ Fd.F ↔ kap m = Fd.θ h ∧ ∀ x : S.toSetting.Q,
      Fd.φQ (conjAut S.toSetting.normal h x) = conjAut instNormalQSubgroupOfM m (Fd.φQ x) :=
  Iff.rfl

theorem exists_snd (Fd : FibreData S) (h : S.toSetting.M) : ∃ m, (h, m) ∈ Fd.F := by
  obtain ⟨m, hm⟩ := Fd.fwd h
  exact ⟨m, (Fd.mem_F_iff h m).mpr hm⟩

theorem exists_fst (Fd : FibreData S) (m : Max3.M) : ∃ h, (h, m) ∈ Fd.F := by
  obtain ⟨h, hm⟩ := Fd.bwd m
  exact ⟨h, (Fd.mem_F_iff h m).mpr hm⟩

theorem mk_one_mem_F_iff (Fd : FibreData S) (h : S.toSetting.M) :
    (h, 1) ∈ Fd.F ↔ h = 1 ∨ (h : G) = S.z := by
  rw [FibreData.mem_F_iff]
  constructor
  · rintro ⟨hkap, hact⟩
    have hθ : Fd.θ h = 1 := by rw [← hkap, map_one]
    have hQ : h ∈ S.toSetting.Q := by
      have hmem : h ∈ Fd.θ.ker := MonoidHom.mem_ker.mpr hθ
      rwa [Fd.θ_ker] at hmem
    have htriv : ∀ x : S.toSetting.Q, conjAut S.toSetting.normal h x = x := by
      intro x
      refine Fd.φQ.injective ?_
      rw [hact x, conjAut_one]
    have hcenter : (⟨h, hQ⟩ : ↥S.toSetting.Q) ∈ Subgroup.center S.toSetting.Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hy' : (h : S.toSetting.M) * (y : S.toSetting.M) * (h : S.toSetting.M)⁻¹ =
          (y : S.toSetting.M) := by
        rw [← conjAut_apply S.toSetting.normal h y]
        exact congrArg Subtype.val (htriv y)
      have h2 : (h : S.toSetting.M) * (y : S.toSetting.M) =
          (y : S.toSetting.M) * (h : S.toSetting.M) := by
        calc (h : S.toSetting.M) * (y : S.toSetting.M)
            = ((h : S.toSetting.M) * (y : S.toSetting.M) * (h : S.toSetting.M)⁻¹) *
                (h : S.toSetting.M) := by group
          _ = (y : S.toSetting.M) * (h : S.toSetting.M) := by rw [hy']
      exact h2.symm
    have hc := (S.toSetting.mem_center_Q_iff (x := ⟨h, hQ⟩)).mp hcenter
    rcases hc with hc | hc
    · left
      exact congrArg Subtype.val hc
    · right
      have h1 : (h : S.toSetting.M) = S.toSetting.zM := congrArg Subtype.val hc
      rw [h1, S.toSetting.coe_zM]
      rfl
  · rintro (rfl | hz)
    · refine (Fd.mem_F_iff (1 : S.toSetting.M) (1 : Max3.M)).mpr
        ⟨by rw [map_one, map_one], fun x => by rw [conjAut_one, conjAut_one]⟩
    · have hh : h = S.toSetting.zM :=
        Subtype.ext (hz.trans S.toSetting.coe_zM.symm)
      rw [hh]
      refine (Fd.mem_F_iff S.toSetting.zM (1 : Max3.M)).mpr ⟨?_, fun x => ?_⟩
      · rw [map_one]
        symm
        rw [← MonoidHom.mem_ker, Fd.θ_ker]
        exact S.toSetting.zM_mem_Q
      · rw [conjAut_one]
        have hzq : (S.toSetting.zQ : S.toSetting.M) = S.toSetting.zM := rfl
        rw [← hzq, conjAut_eq_one_of_mem_center S.toSetting.zQ_mem_center, MulAut.one_apply]

theorem one_mk_mem_F_iff (Fd : FibreData S) (m : Max3.M) :
    (1, m) ∈ Fd.F ↔ m = 1 ∨ (m : J) = Max3.z := by
  rw [FibreData.mem_F_iff]
  constructor
  · rintro ⟨hkap, hact⟩
    have hkm : kap m = 1 := by rw [hkap, map_one]
    have hmQ : (m : J) ∈ Max3.Q := kap_eq_one_iff.mp hkm
    have hmQ' : m ∈ Max3.Q.subgroupOf Max3.M := Subgroup.mem_subgroupOf.mpr hmQ
    have hfix : ∀ y : ↥(Max3.Q.subgroupOf Max3.M),
        conjAut instNormalQSubgroupOfM m y = y := by
      intro y
      have hy := hact (Fd.φQ.symm y)
      rw [conjAut_one, MulEquiv.apply_symm_apply] at hy
      exact hy.symm
    have hcenterQM : (⟨m, hmQ'⟩ : ↥(Max3.Q.subgroupOf Max3.M)) ∈
        Subgroup.center ↥(Max3.Q.subgroupOf Max3.M) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hy' : (m : Max3.M) * (y : Max3.M) * (m : Max3.M)⁻¹ = (y : Max3.M) := by
        rw [← conjAut_apply instNormalQSubgroupOfM m y]
        exact congrArg Subtype.val (hfix y)
      have h2 : (m : Max3.M) * (y : Max3.M) = (y : Max3.M) * (m : Max3.M) := by
        calc (m : Max3.M) * (y : Max3.M)
            = ((m : Max3.M) * (y : Max3.M) * (m : Max3.M)⁻¹) * (m : Max3.M) := by group
          _ = (y : Max3.M) * (m : Max3.M) := by rw [hy']
      exact h2.symm
    have hcenterQ : eQM ⟨m, hmQ'⟩ ∈ Subgroup.center Max3.Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y₀, rfl⟩ := eQM.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcenterQM y₀]
    have hzp : ((eQM ⟨m, hmQ'⟩ : ↥Max3.Q) : J) ∈ Subgroup.zpowers Max3.z := by
      rw [Max3.center_Q] at hcenterQ
      exact Subgroup.mem_subgroupOf.mp hcenterQ
    have hval : ((eQM ⟨m, hmQ'⟩ : ↥Max3.Q) : J) = (m : J) := eQM_val ⟨m, hmQ'⟩
    rw [hval] at hzp
    have hord2 : orderOf Max3.z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact Max3.z_mul_self) Max3.z_ne_one
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
    rw [← zpow_mod_orderOf, hord2] at hk
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      apply Subtype.ext
      have h1 : (m : J) = 1 := by
        rw [← hk, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
      simpa using h1
    · right
      rw [← hk, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  · rintro (rfl | hz)
    · refine (Fd.mem_F_iff (1 : S.toSetting.M) (1 : Max3.M)).mpr
        ⟨by rw [map_one, map_one], fun x => by rw [conjAut_one, conjAut_one]⟩
    · have hm : m = (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) := Subtype.ext hz
      rw [hm]
      refine (Fd.mem_F_iff (1 : S.toSetting.M) ⟨Max3.z, Max3.z_mem_M⟩).mpr
        ⟨?_, fun x => ?_⟩
      · rw [map_one]
        exact kap_eq_one_iff.mpr Max3.z_mem_Q
      · rw [conjAut_one]
        have hconj : conjAut instNormalQSubgroupOfM (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) = 1 := by
          apply MulEquiv.ext
          intro y
          apply Subtype.ext
          rw [conjAut_apply instNormalQSubgroupOfM (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) y,
            MulAut.one_apply]
          have hcomm := Subgroup.mem_center_iff.mp Max3.z_mem_center_M (y : Max3.M)
          calc (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) * (y : Max3.M) *
                (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)⁻¹
              = ((y : Max3.M) * (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)) *
                (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)⁻¹ := by rw [← hcomm]
            _ = (y : Max3.M) := by rw [mul_assoc, mul_inv_cancel, mul_one]
        rw [hconj, MulAut.one_apply]

end FibreData

private noncomputable instance instModuleQM :
    Module (ZMod 2) (Additive (Abelianization ↥(Max3.Q.subgroupOf Max3.M))) :=
  CFSG.GroupTheory.extraspecialQuotientModule (Q := ↥(Max3.Q.subgroupOf Max3.M)) isExtraspecial_Q_M

private noncomputable def fibrePsi : ↥(Max3.Q.subgroupOf Max3.M) →* Multiplicative V8 :=
  { toFun := fun x => theta.symm (QuotientGroup.mk (eQM x))
    map_one' := by simp
    map_mul' := fun x y => by
      have hq : eQM (x * y) = eQM x * eQM y := eQM.map_mul x y
      have h : (QuotientGroup.mk (eQM (x * y)) :
            ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q) =
          (QuotientGroup.mk (eQM x) : ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q) *
            (QuotientGroup.mk (eQM y) : ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q) := by
        rw [hq]
        rfl
      rw [h]
      exact map_mul theta.symm _ _ }

private theorem fibrePsi_surj : Function.Surjective fibrePsi := by
  intro w
  obtain ⟨c, hc⟩ := Quotient.exists_rep (theta w)
  refine ⟨eQM.symm c, ?_⟩
  show theta.symm (QuotientGroup.mk (eQM (eQM.symm c))) = w
  rw [MulEquiv.apply_symm_apply, show QuotientGroup.mk c = theta w from hc,
    MulEquiv.symm_apply_apply]

private theorem fibrePsi_ker_center : ∀ x : ↥(Max3.Q.subgroupOf Max3.M),
    x ∈ fibrePsi.ker ↔ x ∈ Subgroup.center ↥(Max3.Q.subgroupOf Max3.M) := by
  intro x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have h2 : (QuotientGroup.mk (eQM x) : ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q) = 1 := by
      have := congrArg theta hx
      simpa [fibrePsi] using this
    rw [QuotientGroup.eq_one_iff] at h2
    rw [Subgroup.mem_center_iff]
    intro y
    apply eQM.injective
    have hyx : eQM (y * x) = eQM y * eQM x := eQM.map_mul y x
    have hxy : eQM (x * y) = eQM x * eQM y := eQM.map_mul x y
    have hc : eQM y * eQM x = eQM x * eQM y := Subgroup.mem_center_iff.mp h2 (eQM y)
    calc eQM (y * x) = eQM y * eQM x := hyx
      _ = eQM x * eQM y := hc
      _ = eQM (x * y) := hxy.symm
  · intro hx
    rw [MonoidHom.mem_ker]
    have h2 : (QuotientGroup.mk (eQM x) : ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro y
      obtain ⟨y₀, rfl⟩ := eQM.surjective y
      exact (eQM.map_mul y₀ x).symm.trans
        ((congrArg eQM (Subgroup.mem_center_iff.mp hx y₀)).trans (eQM.map_mul x y₀))
    show theta.symm (QuotientGroup.mk (eQM x)) = 1
    rw [h2, map_one]

private theorem fibrePsi_ker : fibrePsi.ker = commutator ↥(Max3.Q.subgroupOf Max3.M) := by
  have hcomm : commutator ↥(Max3.Q.subgroupOf Max3.M) ≤ fibrePsi.ker := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr (fun a _ b _ => ?_)
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  have hcomm' : Subgroup.center ↥(Max3.Q.subgroupOf Max3.M) ≤ fibrePsi.ker := by
    rwa [isExtraspecial_Q_M.2.1] at hcomm
  have hle : fibrePsi.ker ≤ Subgroup.center ↥(Max3.Q.subgroupOf Max3.M) :=
    fun x hx => (fibrePsi_ker_center x).mp hx
  rw [isExtraspecial_Q_M.2.1]
  exact le_antisymm hle hcomm'

private noncomputable def fibreL :
    Additive (Abelianization ↥(Max3.Q.subgroupOf Max3.M)) ≃ₗ[ZMod 2] V8 :=
  CFSG.ComponentClassification.BMCase.abelianizationEquiv fibrePsi fibrePsi_surj fibrePsi_ker

private theorem fibreL_apply : ∀ x : ↥(Max3.Q.subgroupOf Max3.M),
    fibreL (Additive.ofMul (Abelianization.of x)) = Multiplicative.toAdd (fibrePsi x) :=
  fun x => CFSG.ComponentClassification.BMCase.abelianizationEquiv_apply
    fibrePsi fibrePsi_surj fibrePsi_ker x


private theorem fibre_sq_same : ∀ (c w : ↥Max3.Q),
    c⁻¹ * w ∈ Subgroup.center ↥Max3.Q → c ^ 2 = w ^ 2 := by
  intro c w hk
  set k : ↥Max3.Q := c⁻¹ * w with hkdef
  have hk' : k ∈ Subgroup.center ↥Max3.Q := by rw [hkdef]; exact hk
  have hw : w = c * k := by rw [hkdef]; group
  have hcomm : k * c = c * k := (Subgroup.mem_center_iff.mp hk' c).symm
  have hk2 : k * k = 1 := by
    have := CFSG.RankThree.Literature.FSmith.sq_eq_one_of_mem_center
      Max3.isExtraspecialPGroup_Q hk'
    rwa [pow_two] at this
  calc c ^ 2 = c * c := by rw [pow_two]
    _ = c * (k * k) * c := by rw [hk2, mul_one]
    _ = (c * k) * (k * c) := by group
    _ = (c * k) * (c * k) := by rw [hcomm]
    _ = w ^ 2 := by rw [← hw, pow_two]

private theorem fibreHqf : ∀ u : Additive (Abelianization ↥(Max3.Q.subgroupOf Max3.M)),
    extraspecialQuadForm isExtraspecial_Q_M u = qf (fibreL u) := by
  intro u
  obtain ⟨x, rfl⟩ := CFSG.RankThree.Literature.FSmith.exists_ofMul_of u
  rw [fibreL_apply x, CFSG.RankThree.Literature.FSmith.extraspecialQuadForm_apply]
  set c : ↥Max3.Q := eQM x with hcdef
  set v : V8 := Multiplicative.toAdd (fibrePsi x) with hvdef
  have htheta : theta (Multiplicative.ofAdd v) = QuotientGroup.mk c := by
    rw [hvdef]
    show theta (fibrePsi x) = (QuotientGroup.mk (eQM x) :
      ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q)
    exact theta.apply_symm_apply _
  have hnf : (QuotientGroup.mk c : ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q) =
      (QuotientGroup.mk (⟨Max3.nf 0 v, Max3.nf_mem_Q 0 v⟩ : ↥Max3.Q) :
        ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q) := by
    rw [← htheta, Max3.theta_apply_nf 0 v]
  have hsq : eQM (x ^ 2) = (⟨Max3.nf 0 v, Max3.nf_mem_Q 0 v⟩ : ↥Max3.Q) ^ 2 := by
    have h1 : eQM (x ^ 2) = c ^ 2 := by
      rw [hcdef]
      exact map_pow eQM x 2
    rw [h1]
    exact fibre_sq_same c _ (QuotientGroup.eq.mp hnf)
  have hfin : (⟨Max3.nf 0 v, Max3.nf_mem_Q 0 v⟩ : ↥Max3.Q) ^ 2 = 1 ↔ qf v = 0 := by
    have hcoe : ((⟨Max3.nf 0 v, Max3.nf_mem_Q 0 v⟩ : ↥Max3.Q) ^ 2 = 1) ↔
        Max3.nf 0 v ^ 2 = 1 := by
      constructor
      · intro h
        simpa using congrArg Subtype.val h
      · intro h
        apply Subtype.ext
        simpa using h
    rw [hcoe, Max3.nf_eq_generic]
    exact CFSG.Certificates.ExtraspecialNF.nf_sq_eq_one_iff Max3.symplectic_rel
      Max3.nf_injective_generic 0 v
  have hiff : x ^ 2 = 1 ↔ qf v = 0 := by
    have hx1 : x ^ 2 = 1 ↔ eQM (x ^ 2) = 1 := by
      constructor
      · intro h
        rw [h, map_one]
      · intro h
        exact eQM.injective (by rw [map_one]; exact h)
    rw [hx1, hsq, hfin]
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (qf v) with h0 | h1
  · rw [if_pos (hiff.mpr h0), h0]
  · rw [if_neg (fun hx => by rw [hiff.mp hx] at h1; exact absurd h1 (by decide)), h1]

private theorem fibreHL_conj : ∀ (m : Max3.M) (y : ↥(Max3.Q.subgroupOf Max3.M)),
    fibreL (Additive.ofMul (Abelianization.of (conjAut instNormalQSubgroupOfM m y))) =
      rho8a (kap m) (fibreL (Additive.ofMul (Abelianization.of y))) := by
  intro m y
  have htheta : theta (Multiplicative.ofAdd (fibreL (Additive.ofMul (Abelianization.of y)))) =
      QuotientGroup.mk (eQM y) := by
    rw [fibreL_apply y]
    show theta (fibrePsi y) = (QuotientGroup.mk (eQM y) :
      ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q)
    exact theta.apply_symm_apply _
  have h2 : theta (Multiplicative.ofAdd (rho8a (kap m)
        (fibreL (Additive.ofMul (Abelianization.of y))))) =
      QuotientGroup.mk (eQM (conjAut instNormalQSubgroupOfM m y)) := by
    rw [theta_rho8a_kap m (eQM y) (fibreL (Additive.ofMul (Abelianization.of y))) htheta]
    congr 1
  have h1 : theta (Multiplicative.ofAdd (fibreL (Additive.ofMul (Abelianization.of
        (conjAut instNormalQSubgroupOfM m y))))) =
      QuotientGroup.mk (eQM (conjAut instNormalQSubgroupOfM m y)) := by
    rw [fibreL_apply]
    show theta (fibrePsi (conjAut instNormalQSubgroupOfM m y)) =
      (QuotientGroup.mk (eQM (conjAut instNormalQSubgroupOfM m y)) :
        ↥Max3.Q ⧸ Subgroup.center ↥Max3.Q)
    exact theta.apply_symm_apply _
  exact Multiplicative.ofAdd.injective (theta.injective (h1.trans h2.symm))


theorem nonempty_fibreData_of_iso (S : ThSetting G) {σ : Equiv.Perm (Fin 9)}
    {e : S.toSetting.Qt ≃ₗ[ZMod 2] V8}
    (he : ∀ g v, e (S.rho g v) = rho8a (conjA σ g) (e v))
    (hq : ∀ v, S.toSetting.q v = qf (e v)) : Nonempty (FibreData S) := by
  classical
  let toH : S.toSetting.M →* S.H :=
    { toFun := fun m => (⟨m, m.2⟩ : S.H)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have toH_surj : Function.Surjective toH := fun y => ⟨⟨y, y.2⟩, rfl⟩
  let θ : S.toSetting.M →* alternatingGroup (Fin 9) :=
    (conjA σ).toMonoidHom.comp (S.θ.comp toH)
  have θ_surj : Function.Surjective θ :=
    (conjA σ).surjective.comp (S.θ_surj.comp toH_surj)
  have θ_ker : θ.ker = S.toSetting.Q := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : S.θ (toH x) = 1 := (conjA σ).injective (by simpa [θ] using hx)
      have h2 : ((toH x : S.H) : G) ∈ S.Q := by
        have hmem : toH x ∈ S.θ.ker := MonoidHom.mem_ker.mpr h1
        rw [S.θ_ker, Subgroup.mem_subgroupOf] at hmem
        exact hmem
      exact (mem_toSetting_Q_iff S x).mpr h2
    · intro hx
      rw [MonoidHom.mem_ker]
      show conjA σ (S.θ (toH x)) = 1
      have h2 : ((toH x : S.H) : G) ∈ S.Q := (mem_toSetting_Q_iff S x).mp hx
      have h1 : toH x ∈ S.θ.ker := by
        rw [S.θ_ker, Subgroup.mem_subgroupOf]
        exact h2
      rw [MonoidHom.mem_ker] at h1
      rw [h1, map_one]
  let L := fibreL
  let a : S.toSetting.Qt ≃ₗ[ZMod 2]
      Additive (Abelianization ↥(Max3.Q.subgroupOf Max3.M)) := e.trans L.symm
  have ha : ∀ v, extraspecialQuadForm isExtraspecial_Q_M (a v) =
      extraspecialQuadForm S.toSetting.extraspecial v := by
    intro v
    show extraspecialQuadForm isExtraspecial_Q_M (a v) = S.toSetting.q v
    rw [fibreHqf (a v), show L (a v) = e v from L.apply_symm_apply (e v)]
    exact (hq v).symm
  obtain ⟨φQ, hφQ⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_mulEquiv_of_isometry
    S.toSetting.extraspecial isExtraspecial_Q_M a ha
  have hclass : ∀ (h : S.toSetting.M) (m : Max3.M), kap m = θ h → ∀ x : S.toSetting.Q,
      Additive.ofMul (Abelianization.of (φQ (conjAut S.toSetting.normal h x))) =
        Additive.ofMul (Abelianization.of (conjAut instNormalQSubgroupOfM m (φQ x))) := by
    intro h m hm x
    have hρθ : S.rho (S.θ (toH h)) = (↑(S.toSetting.ρ h) :
        S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) := by
      rw [S.rho_θ (toH h)]
      rfl
    have hLHS : e (S.toSetting.toQt (conjAut S.toSetting.normal h x)) =
        rho8a (kap m) (e (S.toSetting.toQt x)) := by
      rw [← S.toSetting.ρ_toQt h x, ← hρθ, he]
      rw [show conjA σ (S.θ (toH h)) = θ h from rfl, ← hm]
    have hRHS : e (S.toSetting.toQt (conjAut S.toSetting.normal h x)) =
        L (Additive.ofMul (Abelianization.of (conjAut instNormalQSubgroupOfM m (φQ x)))) := by
      rw [hLHS, fibreHL_conj m (φQ x), ← hφQ x]
      show rho8a (kap m) (e (S.toSetting.toQt x)) =
        rho8a (kap m) (L (a (S.toSetting.toQt x)))
      rw [show a (S.toSetting.toQt x) = L.symm (e (S.toSetting.toQt x)) from rfl,
        L.apply_symm_apply]
    calc Additive.ofMul (Abelianization.of (φQ (conjAut S.toSetting.normal h x)))
        = a (S.toSetting.toQt (conjAut S.toSetting.normal h x)) := (hφQ _).symm
      _ = L.symm (e (S.toSetting.toQt (conjAut S.toSetting.normal h x))) := rfl
      _ = L.symm (L (Additive.ofMul (Abelianization.of
            (conjAut instNormalQSubgroupOfM m (φQ x))))) := by rw [hRHS]
      _ = Additive.ofMul (Abelianization.of (conjAut instNormalQSubgroupOfM m (φQ x))) :=
        L.symm_apply_apply _
  have fwd : ∀ h : S.toSetting.M, ∃ m : Max3.M, kap m = θ h ∧ ∀ x : S.toSetting.Q,
      φQ (conjAut S.toSetting.normal h x) = conjAut instNormalQSubgroupOfM m (φQ x) := by
    intro h
    obtain ⟨m₀, hm₀⟩ := kap_surjective (θ h)
    obtain ⟨q, hq'⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_conj_compat
      (C := S.toSetting.M) (C' := Max3.M) (Q := S.toSetting.Q)
      (Q' := Max3.Q.subgroupOf Max3.M) (hQn := S.toSetting.normal)
      (hQn' := instNormalQSubgroupOfM) isExtraspecial_Q_M φQ h m₀
      (fun x => (ofMul_of_eq_iff isExtraspecial_Q_M _ _).mp (hclass h m₀ hm₀ x))
    refine ⟨(q : Max3.M) * m₀, ?_, fun x => hq' x⟩
    rw [map_mul, kap_eq_one_iff.mpr (Subgroup.mem_subgroupOf.mp q.2), one_mul]
    exact hm₀
  have bwd : ∀ m : Max3.M, ∃ h : S.toSetting.M, kap m = θ h ∧ ∀ x : S.toSetting.Q,
      φQ (conjAut S.toSetting.normal h x) = conjAut instNormalQSubgroupOfM m (φQ x) := by
    intro m
    obtain ⟨h₀, hh₀⟩ := S.θ_surj ((conjA σ).symm (kap m))
    have hh₀' : θ (S.toSettingE h₀) = kap m := by
      show conjA σ (S.θ (toH (S.toSettingE h₀))) = kap m
      rw [show toH (S.toSettingE h₀) = h₀ from rfl, hh₀, MulEquiv.apply_symm_apply]
    obtain ⟨q, hq'⟩ := CFSG.EvenSporadicStandard.HNRecog.ML1.exists_conj_compat'
      (C := S.toSetting.M) (C' := Max3.M) (Q := S.toSetting.Q)
      (Q' := Max3.Q.subgroupOf Max3.M) (hQn := S.toSetting.normal)
      (hQn' := instNormalQSubgroupOfM) S.toSetting.extraspecial φQ (S.toSettingE h₀) m
      (fun x => (ofMul_of_eq_iff isExtraspecial_Q_M _ _).mp (hclass (S.toSettingE h₀) m
        hh₀'.symm x))
    refine ⟨(q : S.toSetting.M) * S.toSettingE h₀, ?_, fun x => hq' x⟩
    have hq1 : θ (q : S.toSetting.M) = 1 := by
      rw [← MonoidHom.mem_ker, θ_ker]
      exact q.2
    show kap m = θ ((q : S.toSetting.M) * S.toSettingE h₀)
    rw [map_mul, hq1, one_mul]
    exact hh₀'.symm
  exact Nonempty.intro
    { θ := θ
      θ_surj := θ_surj
      θ_ker := θ_ker
      φQ := φQ
      fwd := fwd
      bwd := bwd }

end CFSG.Sporadic.Th.Recog
