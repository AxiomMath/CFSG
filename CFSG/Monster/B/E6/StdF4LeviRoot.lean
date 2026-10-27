module

public import CFSG.Monster.B.E6.StdF4LeviUnitary
public import CFSG.Monster.B.E6.StdF4Points
import all CFSG.Fischer.F4
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley.ExteriorCube
open CFSG.Monster.B.Classical
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Fischer (F4)
open CFSG.LinearGroups (frobeniusF4)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Monster.B.Classical.UnitarySix (ProjSU IsoPt tPt rep₁ rep₂ rep₃ invRank SU_ext isoGraph)
open CFSG.Monster.B.TwoA.Unitary.Clique (su6Equiv su6Mat toSU6 coe_su6Equiv)

theorem repRootL_two : repRootL 2 = (Pi.single (i6 3) 1 : Fin Tag.E6.rank → ℤ) := by
  decide

theorem coe_repPoint_two :
    (repPoint 2 : ModGL Tag.E6 K) = xUnit Tag.E6 K (i6 3) 1 := by
  rw [coe_repPoint]
  apply Units.ext
  rw [E6Adjoint.pinnedX_eq (isRoot_repRootL 2), coe_xUnit, E6Adjoint.xOp_eq, repRootL_two]

theorem repPoint_two_mem_rootClass :
    repPoint 2 ∈ rootClass :=
  (mem_rootClass_iff _).2 ⟨_, rfl⟩

theorem finrank_range_sub_one_of_mem_rootClass
    {x : stdGroup} (hx : x ∈ rootClass) :
    finrank K (LinearMap.range
      (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 22 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 ((isConj_comm.1 repPoint_two_mem_rootClass).trans hx)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_range_conj_sub_one,
    coe_repPoint_two, coe_xUnit]
  exact finrank_range_xOp_three

theorem stdLevi_firstJ_le_stdGroup :
    stdLevi firstJ ≤ stdGroup :=
  (stdLevi_le_nativeParabolic two_mem_firstJ).trans (nativeParabolic_le_stdGroup firstJ)

abbrev leviG :

    stdLevi firstJ →* stdGroup := Subgroup.inclusion stdLevi_firstJ_le_stdGroup

theorem leviG_injective :
    Function.Injective leviG := Subgroup.inclusion_injective _

abbrev rootLeviSet :
    Set stdGroup := {x | x ∈ rootClass ∧ (x : ModGL Tag.E6 K) ∈ stdLevi firstJ}

@[expose] def rootPt
    (p : IsoPt) : stdGroup := leviG (leviPSU.symm (tPt p))

theorem rootPt_injective :
    Function.Injective rootPt :=
  leviG_injective.comp (leviPSU.symm.injective.comp UnitarySix.tPt_injective)

theorem rootPt_pt
    (v : UnitarySix.V) (hv0 : v ≠ 0) (hv : UnitarySix.herm v v = 0) :
    rootPt (UnitarySix.pt v hv0 hv) = leviG (leviPSU.symm (UnitarySix.transvec v hv : ProjSU)) := by
  rw [rootPt, UnitarySix.tPt_pt]

theorem transvec_single_two :
    UnitarySix.transvec (Pi.single 2 1) (UnitarySix.herm_single_self 2) = rep₁ := by
  refine SU_ext ?_
  rw [UnitarySix.coe_transvec, UnitarySix.coe_rep₁]
  decide +kernel

theorem leviPSU_symm_rep₁ :
    leviPSU.symm (rep₁ : ProjSU) = leviOf rep₁ := by
  rw [MulEquiv.symm_apply_eq, leviPSU_leviOf]

theorem leviG_leviOf_rep₁ :
    leviG (leviOf rep₁) = repPoint 2 :=
  Subtype.ext (coe_leviOf_rep₁.trans coe_repPoint_two.symm)

theorem rep₁_mem_rankOneClass : (rep₁ : ProjSU) ∈ UnitarySix.rankOneClass :=
  ⟨rep₁, UnitarySix.rep₁_sq, UnitarySix.invRank_rep₁, rfl⟩

theorem rootPt_mem_rootLeviSet
    (p : IsoPt) : rootPt p ∈ rootLeviSet := by
  refine ⟨?_, (leviPSU.symm (tPt p)).2⟩
  have h1 : IsConj (rep₁ : ProjSU) (tPt p) := by
    have hp := UnitarySix.tPt_mem_rankOneClass p
    rw [UnitarySix.rankOneClass_eq_conj] at hp
    have hr := rep₁_mem_rankOneClass
    rw [UnitarySix.rankOneClass_eq_conj] at hr
    exact (isConj_comm.1 hr).trans hp
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  have h2 : IsConj (repPoint 2) (rootPt p) := by
    refine isConj_iff.2 ⟨leviG (leviPSU.symm c), ?_⟩
    rw [← leviG_leviOf_rep₁, ← leviPSU_symm_rep₁, ← map_inv, ← map_mul, ← map_mul,
      ← map_inv, ← map_mul, ← map_mul, hc]
    rfl
  exact repPoint_two_mem_rootClass.trans h2

theorem sq_of_mem_rootClass
    {x : stdGroup} (hx : x ∈ rootClass) : x ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  rw [pow_two, show c * rootInv * c⁻¹ * (c * rootInv * c⁻¹) = c * (rootInv * rootInv) * c⁻¹ by
    group, rootInv_mul_self, mul_one, mul_inv_cancel]

theorem ne_one_of_mem_rootClass
    {x : stdGroup} (hx : x ∈ rootClass) : x ≠ 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  intro h
  apply rootInv_ne_one
  rw [mul_inv_eq_one, mul_eq_left] at h
  exact h

theorem exists_rootPt_of_mem
    {x : stdGroup} (hx : x ∈ rootLeviSet) : ∃ p, rootPt p = x := by
  obtain ⟨hxG, hxL⟩ := hx
  set l : stdLevi firstJ := ⟨x, hxL⟩
  have hl2 : leviPSU l ^ 2 = 1 := by
    rw [← map_pow]
    have : l ^ 2 = 1 := Subtype.ext (by
      change ((x ^ 2 : stdGroup) : ModGL Tag.E6 K) = 1
      rw [sq_of_mem_rootClass hxG]
      rfl)
    rw [this, map_one]
  have hl1 : leviPSU l ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    intro h
    exact ne_one_of_mem_rootClass hxG
      (Subtype.ext (congrArg (Subtype.val : stdLevi firstJ → ModGL Tag.E6 K) h))
  obtain ⟨A, ⟨hA, hA2⟩, -⟩ := UnitarySix.exists_unique_involution_lift _ hl2 hl1
  have hA1 : A ≠ 1 := by
    rintro rfl
    exact hl1 hA.symm
  have h22 := finrank_range_sub_one_of_mem_rootClass hxG
  have hk : invRank A = 1 := by
    rcases UnitarySix.invRank_eq_one_or_two_or_three A hA2 hA1 with h | h | h
    · exact h
    · have := finrank_range_sub_one_of_invRank_two hA2 hA1 hA.symm h
      change finrank K (LinearMap.range
        (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 32 at this
      omega
    · have := finrank_range_sub_one_of_invRank_three hA2 hA1 hA.symm h
      change finrank K (LinearMap.range
        (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 38 at this
      omega
  obtain ⟨p, hp⟩ : (A : ProjSU) ∈ Set.range tPt := by
    rw [UnitarySix.range_tPt]
    exact ⟨A, hA2, hk, rfl⟩
  refine ⟨p, ?_⟩
  rw [rootPt, hp, hA, MulEquiv.symm_apply_apply]
  rfl

theorem rootLeviSet_eq_range :
    rootLeviSet = Set.range rootPt := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := exists_rootPt_of_mem hx
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact rootPt_mem_rootLeviSet p

theorem rootLeviSet_eq_transvec :
    rootLeviSet =
    {x | ∃ (v : UnitarySix.V) (_ : v ≠ 0) (hv : UnitarySix.herm v v = 0),
      x = leviG (leviPSU.symm (UnitarySix.transvec v hv : ProjSU))} := by
  rw [rootLeviSet_eq_range]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    induction p using UnitarySix.IsoPt.ind with
    | h v hv0 hv => exact ⟨v, hv0, hv, rootPt_pt v hv0 hv⟩
  · rintro ⟨v, hv0, hv, rfl⟩
    exact ⟨_, rootPt_pt v hv0 hv⟩

theorem betaSU_transvec (v : UnitarySix.V) (hv : UnitarySix.herm v v = 0) :
    UnitarySix.betaSU (UnitarySix.transvec v hv) =
      UnitarySix.transvec (UnitarySix.betaV v) (UnitarySix.herm_betaV_self_eq_zero hv) := by
  refine SU_ext ?_
  rw [UnitarySix.coe_betaSU, UnitarySix.coe_transvec, UnitarySix.coe_transvec]
  ext i j
  simp only [UnitarySix.betaM, UnitarySix.transvecMat, Matrix.map_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, UnitarySix.bar_add, UnitarySix.bar_mul, UnitarySix.betaV]
  congr 1
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem tPt_betaPt (p : IsoPt) : tPt (UnitarySix.betaPt p) = UnitarySix.betaL (tPt p) := by
  induction p using UnitarySix.IsoPt.ind with
  | h v hv0 hv =>
    rw [UnitarySix.betaPt_pt, UnitarySix.tPt_pt, UnitarySix.tPt_pt, UnitarySix.betaL_mk,
      betaSU_transvec]

theorem leviPSU_symm_betaL
    (y : ProjSU) :
    leviPSU.symm (UnitarySix.betaL y) = betaLevi (leviPSU.symm y) := by
  rw [MulEquiv.symm_apply_eq, leviPSU_betaLevi, MulEquiv.apply_symm_apply]

theorem rootPt_projAct
    (l : stdLevi firstJ) (p : IsoPt) :
    rootPt (UnitarySix.projAct (leviPSU l) p) = leviG l * rootPt p * (leviG l)⁻¹ := by
  have e : leviPSU.symm (leviPSU l * tPt p * (leviPSU l)⁻¹) =
      l * leviPSU.symm (tPt p) * l⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [rootPt, UnitarySix.tPt_projAct, e, map_mul, map_mul, map_inv]
  rfl

theorem rootPt_betaPt
    (p : IsoPt) : rootPt (UnitarySix.betaPt p) = betaG (rootPt p) := by
  rw [rootPt, tPt_betaPt, leviPSU_symm_betaL]
  rfl

theorem extAct_leviStarHom
    (γ : leviStar) (p : IsoPt) :
    UnitarySix.extAct (leviStarHom γ) p =
      UnitarySix.projAct (leviPSU ⟨_, γ.2⟩)
        (UnitarySix.betaPermHom (betaIdx (γ : GStar).right) p) := by
  have e : leviStarHom γ = SemidirectProduct.inl (leviPSU ⟨_, γ.2⟩) *
      SemidirectProduct.inr (betaIdx (γ : GStar).right) :=
    SemidirectProduct.ext (by simp [leviStarHom_left]) (by simp [leviStarHom_right])
  rw [e, map_mul, UnitarySix.extAct_inl, UnitarySix.extAct_inr]
  rfl

theorem rootPt_betaPermHom
    (b : betaGroup) (p : IsoPt) :
    rootPt (UnitarySix.betaPermHom (betaIdx b) p) = (b : MulAut stdGroup) (rootPt p) := by
  rcases mem_betaGroup_iff.mp b.2 with hb | hb
  · rw [betaIdx_of_eq_one hb, map_one, hb]
    rfl
  · rw [betaIdx_of_eq_betaG hb, hb]
    have : UnitarySix.betaPermHom (Multiplicative.ofAdd 1) = UnitarySix.betaPerm := by
      simp [UnitarySix.betaPermHom, show ¬((1 : ZMod 2) = 0) by decide]
    rw [this]
    exact rootPt_betaPt p

theorem conj_rootPt
    (γ : leviStar) (p : IsoPt) :
    (γ : GStar) * SemidirectProduct.inl (rootPt p) * (γ : GStar)⁻¹ =
      SemidirectProduct.inl (rootPt (UnitarySix.extAct (leviStarEquiv γ) p)) := by
  rw [conj_inl, leviStarEquiv_apply, extAct_leviStarHom, rootPt_projAct, rootPt_betaPermHom]
  rfl

theorem adj_iff_commute_rootPt
    (p q : IsoPt) :
    isoGraph.Adj p q ↔ p ≠ q ∧ Commute (rootPt p) (rootPt q) := by
  rw [UnitarySix.adj_iff_commute]
  refine and_congr_right fun _ => ?_
  have hinj : Function.Injective (leviG.comp leviPSU.symm.toMonoidHom) :=
    leviG_injective.comp leviPSU.symm.injective
  constructor
  · intro h
    exact h.map (leviG.comp leviPSU.symm.toMonoidHom)
  · intro h
    have e := h.eq
    change (leviG.comp leviPSU.symm.toMonoidHom) (tPt p) *
        (leviG.comp leviPSU.symm.toMonoidHom) (tPt q) =
      (leviG.comp leviPSU.symm.toMonoidHom) (tPt q) *
        (leviG.comp leviPSU.symm.toMonoidHom) (tPt p) at e
    rw [← map_mul, ← map_mul] at e
    exact hinj e

theorem finrank_rootModule :
    finrank K (RootModule Tag.E6 K) = 78 := by
  rw [Module.finrank_finsupp_self, card_label_E6']

theorem finrank_range_sub_one_of_leviPSU
    {l : stdLevi firstJ} {A : SU frobeniusF4 6}
    (hA : A ^ 2 = 1) (hA1 : A ≠ 1) (hl : leviPSU l = (A : ProjSU)) :
    (invRank A = 1 ∧ finrank K (LinearMap.range
      (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 22) ∨
    (invRank A = 2 ∧ finrank K (LinearMap.range
      (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 32) ∨
    (invRank A = 3 ∧ finrank K (LinearMap.range
      (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 38) := by
  rcases UnitarySix.invRank_eq_one_or_two_or_three A hA hA1 with h | h | h
  · exact Or.inl ⟨h, finrank_range_sub_one_of_invRank_one hA hA1 hl h⟩
  · exact Or.inr (Or.inl ⟨h, finrank_range_sub_one_of_invRank_two hA hA1 hl h⟩)
  · exact Or.inr (Or.inr ⟨h, finrank_range_sub_one_of_invRank_three hA hA1 hl h⟩)

theorem E6_unitary_Levi_root_involution_intersection :
    (rootInv : ModGL Tag.E6 K) = pinnedX Tag.E6 K theta 1 ∧ theta = e6HighestRoot ∧
    stdLevi firstJ ≤ stdGroup ∧
    (∀ (l : stdLevi firstJ) (h : SU6),
      psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
          cubeHom (h : Matrix.SpecialLinearGroup (Fin 6) K) →
        leviSUEquiv l = (h : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6) ∧
          leviPSU l = (su6Equiv h : ProjSU)) ∧
    (∀ h : SU6, (((su6Equiv h : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((h : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ∧
    (((leviOf rep₁ : stdLevi firstJ) : ModGL Tag.E6 K) = xUnit Tag.E6 K (i6 3) 1 ∧
      leviPSU (leviOf rep₁) = (rep₁ : ProjSU)) ∧
    (((leviOf rep₂ : stdLevi firstJ) : ModGL Tag.E6 K) =
        xUnit Tag.E6 K (i6 0) 1 * xUnit Tag.E6 K (i6 5) 1 ∧
      leviPSU (leviOf rep₂) = (rep₂ : ProjSU)) ∧
    (((leviOf rep₃ : stdLevi firstJ) : ModGL Tag.E6 K) =
        xUnit Tag.E6 K (i6 0) 1 * xUnit Tag.E6 K (i6 3) 1 * xUnit Tag.E6 K (i6 5) 1 ∧
      leviPSU (leviOf rep₃) = (rep₃ : ProjSU)) ∧
    finrank K (RootModule Tag.E6 K) = 78 ∧
    (∀ (l : stdLevi firstJ) (A : SU frobeniusF4 6), A ^ 2 = 1 → A ≠ 1 →
      leviPSU l = (A : ProjSU) →
      (invRank A = 1 ∧ finrank K (LinearMap.range
        (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 22) ∨
      (invRank A = 2 ∧ finrank K (LinearMap.range
        (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 32) ∨
      (invRank A = 3 ∧ finrank K (LinearMap.range
        (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 38)) ∧
    (∃ x ∈ rootClass, (x : ModGL Tag.E6 K) = xUnit Tag.E6 K (i6 3) 1) ∧
    rootLeviSet = {x | ∃ (v : UnitarySix.V) (_ : v ≠ 0) (hv : UnitarySix.herm v v = 0),
      x = leviG (leviPSU.symm (UnitarySix.transvec v hv : ProjSU))} ∧
    rootLeviSet = Set.range rootPt ∧ Function.Injective rootPt ∧ Fintype.card IsoPt = 693 ∧
    (∀ (v : UnitarySix.V) (hv0 : v ≠ 0) (hv : UnitarySix.herm v v = 0),
      rootPt (UnitarySix.pt v hv0 hv) =
        leviG (leviPSU.symm (UnitarySix.transvec v hv : ProjSU))) ∧
    (∀ g : stdGroup, (((betaG g : stdGroup) : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) = entrywise C2E6Overlap.barHom
        ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))) ∧
    (∀ γ : GStar, γ ∈ leviStar ↔ (γ.left : ModGL Tag.E6 K) ∈ stdLevi firstJ) ∧
    (∀ γ : leviStar, (leviStarEquiv γ).left = leviPSU ⟨_, γ.2⟩ ∧
      (leviStarEquiv γ).right = betaIdx (γ : GStar).right) ∧
    (∀ b : betaGroup, ((b : MulAut stdGroup) = 1 → betaIdx b = 1) ∧
      ((b : MulAut stdGroup) = betaG → betaIdx b = Multiplicative.ofAdd 1)) ∧
    (∀ (γ : leviStar) (p : IsoPt),
      (γ : GStar) * SemidirectProduct.inl (rootPt p) * (γ : GStar)⁻¹ =
        SemidirectProduct.inl (rootPt (UnitarySix.extAct (leviStarEquiv γ) p))) ∧
    isoGraph.IsSRGWith 693 180 51 45 ∧
    ∀ p q : IsoPt, isoGraph.Adj p q ↔ p ≠ q ∧ Commute (rootPt p) (rootPt q) :=
  ⟨rfl, rfl, stdLevi_firstJ_le_stdGroup,
    fun _ _ e => ⟨leviSUEquiv_apply e, leviPSU_apply e⟩, fun _ => rfl,
    ⟨coe_leviOf_rep₁, leviPSU_leviOf _⟩, ⟨coe_leviOf_rep₂, leviPSU_leviOf _⟩,
    ⟨coe_leviOf_rep₃, leviPSU_leviOf _⟩, finrank_rootModule,
    fun _ _ hA hA1 hl => finrank_range_sub_one_of_leviPSU hA hA1 hl,
    ⟨_, repPoint_two_mem_rootClass, coe_repPoint_two⟩, rootLeviSet_eq_transvec,
    rootLeviSet_eq_range, rootPt_injective, UnitarySix.card_isoPt, rootPt_pt,
    fun _ => rfl, fun _ => Iff.rfl, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨betaIdx_of_eq_one, betaIdx_of_eq_betaG⟩, conj_rootPt, UnitarySix.isSRGWith,
    adj_iff_commute_rootPt⟩

end CFSG.Monster.B.E6.StdF4
