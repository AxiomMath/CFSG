module

public import CFSG.Monster.B.E6.StdF4LeviRank
public import CFSG.Monster.B.TwoA.Unitary.CliqueBridge
import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidue

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
open CFSG.Monster.B.Classical.UnitarySix (ProjSU rep₁ rep₂ rep₃ involutionRep invRank SU_ext)
open CFSG.Monster.B.TwoA.Unitary.Clique (su6Equiv su6Mat toSU6 map_su6Equiv_scalars coe_su6Equiv)

@[expose] def projSUEquiv : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6 ≃* ProjSU :=
  QuotientGroup.congr _ _ su6Equiv map_su6Equiv_scalars

theorem projSUEquiv_mk (h : SU6) :
    projSUEquiv (h : SU6 ⧸ (LinearFlag.scalars 6 K).subgroupOf SU6) = (su6Equiv h : ProjSU) :=
  rfl

@[expose] def leviPSU :
    stdLevi firstJ ≃* ProjSU := leviSUEquiv.trans projSUEquiv

theorem leviPSU_apply
    {l : stdLevi firstJ} {h : SU6}
    (e : psiA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
      cubeHom (h : Matrix.SpecialLinearGroup (Fin 6) K)) :
    leviPSU l = (su6Equiv h : ProjSU) := by
  rw [leviPSU, MulEquiv.trans_apply, leviSUEquiv_apply e, projSUEquiv_mk]

theorem leviPSU_liftSU
    (h : SU6) : leviPSU (liftSU h) = (su6Equiv h : ProjSU) := by
  rw [leviPSU, MulEquiv.trans_apply, leviSUEquiv_liftSU, projSUEquiv_mk]

abbrev leviOf
    (A : SU frobeniusF4 6) : stdLevi firstJ := liftSU (toSU6 A)

theorem leviPSU_leviOf
    (A : SU frobeniusF4 6) : leviPSU (leviOf A) = (A : ProjSU) := by
  rw [leviPSU_liftSU]
  exact congrArg _ (su6Equiv.apply_symm_apply A)

theorem coe_leviOf
    (A : SU frobeniusF4 6) :
    ((leviOf A : stdLevi firstJ) : ModGL Tag.E6 K) =
      ((liftA (toSU6 A : Matrix.SpecialLinearGroup (Fin 6) K) : groupA) : ModGL Tag.E6 K) :=
  rfl

theorem toSU6_rep₁ : (toSU6 rep₁ : Matrix.SpecialLinearGroup (Fin 6) K) = upAdj 2 1 :=
  Subtype.ext rfl

theorem toSU6_rep₂ :
    (toSU6 rep₂ : Matrix.SpecialLinearGroup (Fin 6) K) = upAdj 0 1 * upAdj 4 1 := by
  apply Subtype.ext
  change (1 + Matrix.single 0 1 1 + Matrix.single 4 5 1 : Matrix (Fin 6) (Fin 6) F4) =
    (1 + Matrix.single 0 1 1) * (1 + Matrix.single 4 5 1)
  decide +kernel

theorem toSU6_rep₃ :
    (toSU6 rep₃ : Matrix.SpecialLinearGroup (Fin 6) K) = upAdj 0 1 * upAdj 2 1 * upAdj 4 1 := by
  apply Subtype.ext
  change (1 + Matrix.single 0 1 1 + Matrix.single 2 3 1 + Matrix.single 4 5 1 :
      Matrix (Fin 6) (Fin 6) F4) =
    (1 + Matrix.single 0 1 1) * (1 + Matrix.single 2 3 1) * (1 + Matrix.single 4 5 1)
  decide +kernel

theorem coe_leviOf_rep₁ :
    ((leviOf rep₁ : stdLevi firstJ) : ModGL Tag.E6 K) = xUnit Tag.E6 K (i6 3) 1 := by
  rw [coe_leviOf, toSU6_rep₁, liftA_upAdj]
  rfl

theorem coe_leviOf_rep₂ :
    ((leviOf rep₂ : stdLevi firstJ) : ModGL Tag.E6 K) =
      xUnit Tag.E6 K (i6 0) 1 * xUnit Tag.E6 K (i6 5) 1 := by
  rw [coe_leviOf, toSU6_rep₂, map_mul, liftA_upAdj, liftA_upAdj]
  rfl

theorem coe_leviOf_rep₃ :
    ((leviOf rep₃ : stdLevi firstJ) : ModGL Tag.E6 K) =
      xUnit Tag.E6 K (i6 0) 1 * xUnit Tag.E6 K (i6 3) 1 *
        xUnit Tag.E6 K (i6 5) 1 := by
  rw [coe_leviOf, toSU6_rep₃, map_mul, map_mul, liftA_upAdj, liftA_upAdj, liftA_upAdj]
  rfl

theorem finrank_range_conj_sub_one (c g : ModGL Tag.E6 K) :
    finrank K (LinearMap.range
        (((c * g * c⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) =
      finrank K (LinearMap.range ((g : Module.End K (RootModule Tag.E6 K)) - 1)) := by
  set C : Module.End K (RootModule Tag.E6 K) := (c : Module.End K (RootModule Tag.E6 K)) with hCdef
  set D : Module.End K (RootModule Tag.E6 K) := ((c⁻¹ : ModGL Tag.E6 K) :
    Module.End K (RootModule Tag.E6 K)) with hDdef
  have hCD : C * D = 1 := Units.mul_inv c
  have hDC : D * C = 1 := Units.inv_mul c
  have e : ((c * g * c⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1 =
      C ∘ₗ (((g : Module.End K (RootModule Tag.E6 K)) - 1) ∘ₗ D) := by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, Units.val_mul, Units.val_mul, sub_mul,
      one_mul, mul_sub, hCD, ← mul_assoc]
  have hD : LinearMap.range D = ⊤ := LinearMap.range_eq_top.2 fun v =>
    ⟨C v, by rw [← Module.End.mul_apply, hDC, Module.End.one_apply]⟩
  have hC : Function.Injective C := fun v w h => by
    have := congrArg D h
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hDC] at this
  rw [e, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hD]
  exact (Submodule.equivMapOfInjective C hC _).finrank_eq.symm

theorem finrank_range_sub_one_eq_rep
    {l : stdLevi firstJ} {A : SU frobeniusF4 6} (hA : A ^ 2 = 1)
    (hA1 : A ≠ 1) (hl : leviPSU l = (A : ProjSU)) :
    finrank K (LinearMap.range
        (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) =
      finrank K (LinearMap.range (((leviOf (involutionRep (invRank A)) : stdLevi firstJ) :
        ModGL Tag.E6 K) - 1 : Module.End K (RootModule Tag.E6 K))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (UnitarySix.isConj_involutionRep A hA hA1)
  set c' : stdLevi firstJ := leviPSU.symm (c : ProjSU)
  have h1 : c' * l * c'⁻¹ = leviOf (involutionRep (invRank A)) := by
    apply leviPSU.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hl, leviPSU_leviOf, ← hc]
    rfl
  rw [← h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_range_conj_sub_one]

theorem finrank_range_sub_one_of_invRank_one
    {l : stdLevi firstJ} {A : SU frobeniusF4 6}
    (hA : A ^ 2 = 1) (hA1 : A ≠ 1) (hl : leviPSU l = (A : ProjSU)) (hk : invRank A = 1) :
    finrank K (LinearMap.range
      (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 22 := by
  rw [finrank_range_sub_one_eq_rep hA hA1 hl, hk]
  change finrank K (LinearMap.range (((leviOf rep₁ : stdLevi firstJ) : ModGL Tag.E6 K) - 1 :
    Module.End K (RootModule Tag.E6 K))) = 22
  rw [coe_leviOf_rep₁, coe_xUnit]
  exact finrank_range_xOp_three

theorem finrank_range_sub_one_of_invRank_two
    {l : stdLevi firstJ} {A : SU frobeniusF4 6}
    (hA : A ^ 2 = 1) (hA1 : A ≠ 1) (hl : leviPSU l = (A : ProjSU)) (hk : invRank A = 2) :
    finrank K (LinearMap.range
      (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 32 := by
  rw [finrank_range_sub_one_eq_rep hA hA1 hl, hk]
  change finrank K (LinearMap.range (((leviOf rep₂ : stdLevi firstJ) : ModGL Tag.E6 K) - 1 :
    Module.End K (RootModule Tag.E6 K))) = 32
  rw [coe_leviOf_rep₂, Units.val_mul, coe_xUnit, coe_xUnit]
  exact finrank_range_xOp_zero_five

theorem finrank_range_sub_one_of_invRank_three
    {l : stdLevi firstJ} {A : SU frobeniusF4 6}
    (hA : A ^ 2 = 1) (hA1 : A ≠ 1) (hl : leviPSU l = (A : ProjSU)) (hk : invRank A = 3) :
    finrank K (LinearMap.range
      (((l : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 38 := by
  rw [finrank_range_sub_one_eq_rep hA hA1 hl, hk]
  change finrank K (LinearMap.range (((leviOf rep₃ : stdLevi firstJ) : ModGL Tag.E6 K) - 1 :
    Module.End K (RootModule Tag.E6 K))) = 38
  rw [coe_leviOf_rep₃, Units.val_mul, Units.val_mul, coe_xUnit, coe_xUnit, coe_xUnit]
  exact finrank_range_xOp_zero_three_five

theorem betaGL_mem_stdLevi
    {g : ModGL Tag.E6 K} (hg : g ∈ stdLevi firstJ) :
    betaGL g ∈ stdLevi firstJ := by
  rw [stdLevi_firstJ] at hg ⊢
  exact ⟨betaGL_mem_subsystemGroup hg.1, betaGL_mem_stdFixedGroup hg.2⟩

@[expose] def betaLevi :
    MulAut (stdLevi firstJ) where
  toFun l := ⟨betaGL l, betaGL_mem_stdLevi l.2⟩
  invFun l := ⟨betaGL l, betaGL_mem_stdLevi l.2⟩
  left_inv l := Subtype.ext (betaGL_betaGL l)
  right_inv l := Subtype.ext (betaGL_betaGL l)
  map_mul' l l' := Subtype.ext (map_mul betaGL (l : ModGL Tag.E6 K) l')

theorem coe_betaLevi
    (l : stdLevi firstJ) :
    ((betaLevi l : stdLevi firstJ) : ModGL Tag.E6 K) = betaGL l := rfl

theorem su6Equiv_barSU (h : SU6) : su6Equiv (barSU h) = UnitarySix.betaSU (su6Equiv h) := by
  refine SU_ext ?_
  rw [coe_su6Equiv, UnitarySix.coe_betaSU, coe_su6Equiv]
  exact coe_barSL h.1

theorem leviPSU_betaLevi
    (l : stdLevi firstJ) :
    leviPSU (betaLevi l) = UnitarySix.betaL (leviPSU l) := by
  have e := psiA_suOf l
  have hb : betaA ⟨(l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA l.2⟩ =
      ⟨((betaLevi l : stdLevi firstJ) : ModGL Tag.E6 K),
        stdLevi_firstJ_le_groupA (betaLevi l).2⟩ := Subtype.ext rfl
  have e' : psiA ⟨((betaLevi l : stdLevi firstJ) : ModGL Tag.E6 K),
      stdLevi_firstJ_le_groupA (betaLevi l).2⟩ =
        cubeHom ((barSU (suOf l) : SU6) : Matrix.SpecialLinearGroup (Fin 6) K) := by
    rw [← hb]
    exact psiA_betaA e
  rw [leviPSU_apply e', leviPSU_apply e, su6Equiv_barSU, UnitarySix.betaL_mk]


theorem apply_mem_stdLevi
    (b : betaGroup) {x : stdGroup}
    (hx : (x : ModGL Tag.E6 K) ∈ stdLevi firstJ) :
    (((b : MulAut stdGroup) x : stdGroup) : ModGL Tag.E6 K) ∈ stdLevi firstJ := by
  rcases mem_betaGroup_iff.mp b.2 with h | h
  · rw [h]
    exact hx
  · rw [h, coe_betaG_apply]
    exact betaGL_mem_stdLevi hx

@[expose] def leviStar :
    Subgroup GStar where
  carrier := {γ | (γ.left : ModGL Tag.E6 K) ∈ stdLevi firstJ}
  mul_mem' {γ γ'} hγ hγ' := by
    change (((γ * γ').left : stdGroup) : ModGL Tag.E6 K) ∈ stdLevi firstJ
    rw [SemidirectProduct.mul_left, Subgroup.coe_mul]
    exact mul_mem hγ (apply_mem_stdLevi γ.right hγ')
  one_mem' := one_mem (stdLevi firstJ)
  inv_mem' {γ} hγ := by
    change (((γ⁻¹).left : stdGroup) : ModGL Tag.E6 K) ∈ stdLevi firstJ
    rw [SemidirectProduct.inv_left]
    have h1 : ((γ.left⁻¹ : stdGroup) : ModGL Tag.E6 K) ∈ stdLevi firstJ := by
      rw [Subgroup.coe_inv]
      exact inv_mem hγ
    exact apply_mem_stdLevi γ.right⁻¹ h1

theorem mem_leviStar
    {γ : GStar} : γ ∈ leviStar ↔ (γ.left : ModGL Tag.E6 K) ∈ stdLevi firstJ :=
  Iff.rfl

@[expose] noncomputable def betaIdx :
    betaGroup →* Multiplicative (ZMod 2) :=
  betaGroupHom (Multiplicative.ofAdd 1) rfl

theorem betaIdx_of_eq_one
    {b : betaGroup} (hb : (b : MulAut stdGroup) = 1) : betaIdx b = 1 :=
  betaGroupHom_of_eq_one rfl hb

theorem betaIdx_of_eq_betaG
    {b : betaGroup} (hb : (b : MulAut stdGroup) = betaG) :
    betaIdx b = Multiplicative.ofAdd 1 :=
  betaGroupHom_of_eq_betaG rfl hb

theorem ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

theorem betaIdx_injective :
    Function.Injective betaIdx := by
  intro b b' h
  apply Subtype.ext
  rcases mem_betaGroup_iff.mp b.2 with hb | hb <;> rcases mem_betaGroup_iff.mp b'.2 with hb' | hb'
  · rw [hb, hb']
  · rw [betaIdx_of_eq_one hb, betaIdx_of_eq_betaG hb'] at h
    exact absurd h.symm ofAdd_one_ne_one
  · rw [betaIdx_of_eq_betaG hb, betaIdx_of_eq_one hb'] at h
    exact absurd h ofAdd_one_ne_one
  · rw [hb, hb']

theorem leviPSU_apply_beta
    (b : betaGroup) {x : stdGroup}
    (hx : (x : ModGL Tag.E6 K) ∈ stdLevi firstJ) :
    leviPSU ⟨_, apply_mem_stdLevi b hx⟩ = UnitarySix.betaHom (betaIdx b) (leviPSU ⟨_, hx⟩) := by
  rcases mem_betaGroup_iff.mp b.2 with hb | hb
  · have e : (⟨_, apply_mem_stdLevi b hx⟩ : stdLevi firstJ) = ⟨_, hx⟩ := by
      apply Subtype.ext
      change (((b : MulAut stdGroup) x : stdGroup) : ModGL Tag.E6 K) = x
      rw [hb]
      rfl
    rw [e, betaIdx_of_eq_one hb, map_one, MulAut.one_apply]
  · have e : (⟨_, apply_mem_stdLevi b hx⟩ : stdLevi firstJ) = betaLevi ⟨_, hx⟩ := by
      apply Subtype.ext
      change (((b : MulAut stdGroup) x : stdGroup) : ModGL Tag.E6 K) = betaGL x
      rw [hb]
      rfl
    rw [e, leviPSU_betaLevi, betaIdx_of_eq_betaG hb]
    rfl

@[expose] noncomputable def leviStarHom :
    leviStar →* UnitarySix.LBeta where
  toFun γ := ⟨leviPSU ⟨_, γ.2⟩, betaIdx (γ : GStar).right⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ ?_
    · change leviPSU ⟨_, (1 : leviStar).2⟩ = 1
      rw [← map_one leviPSU]
      rfl
    · exact map_one betaIdx
  map_mul' γ γ' := by
    refine SemidirectProduct.ext ?_ (map_mul betaIdx _ _)
    have e : (⟨_, (γ * γ').2⟩ : stdLevi firstJ) =
        ⟨_, γ.2⟩ * ⟨_, apply_mem_stdLevi (γ : GStar).right (mem_leviStar.1 γ'.2)⟩ := rfl
    change leviPSU ⟨_, (γ * γ').2⟩ =
      leviPSU ⟨_, γ.2⟩ * UnitarySix.betaHom (betaIdx (γ : GStar).right) (leviPSU ⟨_, γ'.2⟩)
    rw [e, map_mul, leviPSU_apply_beta _ (mem_leviStar.1 γ'.2)]

theorem leviStarHom_left
    (γ : leviStar) :
    (leviStarHom γ).left = leviPSU ⟨_, γ.2⟩ := rfl

theorem leviStarHom_right
    (γ : leviStar) :
    (leviStarHom γ).right = betaIdx (γ : GStar).right := rfl

theorem leviStarHom_bijective :
    Function.Bijective leviStarHom := by
  constructor
  · intro γ γ' h
    have hl := congrArg SemidirectProduct.left h
    have hr := congrArg SemidirectProduct.right h
    rw [leviStarHom_left, leviStarHom_left] at hl
    rw [leviStarHom_right, leviStarHom_right] at hr
    apply Subtype.ext
    refine SemidirectProduct.ext ?_ (betaIdx_injective hr)
    exact Subtype.ext (congrArg (Subtype.val : stdLevi firstJ → ModGL Tag.E6 K)
      (leviPSU.injective hl))
  · intro y
    set x := leviPSU.symm y.left
    have hx : (x : ModGL Tag.E6 K) ∈ stdGroup :=
      (stdLevi_le_nativeParabolic two_mem_firstJ).trans (nativeParabolic_le_stdGroup firstJ) x.2
    rcases UnitarySix.zmod2_cases' (Multiplicative.toAdd y.right) with he | he
    · refine ⟨⟨⟨⟨_, hx⟩, 1⟩, x.2⟩, SemidirectProduct.ext ?_ ?_⟩
      · exact leviPSU.apply_symm_apply y.left
      · rw [leviStarHom_right]
        change betaIdx 1 = y.right
        rw [map_one]
        exact (congrArg Multiplicative.ofAdd he).symm
    · refine ⟨⟨⟨⟨_, hx⟩, ⟨betaG, Subgroup.mem_zpowers betaG⟩⟩, x.2⟩,
        SemidirectProduct.ext ?_ ?_⟩
      · exact leviPSU.apply_symm_apply y.left
      · rw [leviStarHom_right, betaIdx_of_eq_betaG rfl]
        exact (congrArg Multiplicative.ofAdd he).symm

@[expose] noncomputable def leviStarEquiv :
    leviStar ≃* UnitarySix.LBeta :=
  MulEquiv.ofBijective leviStarHom leviStarHom_bijective

theorem leviStarEquiv_apply
    (γ : leviStar) : leviStarEquiv γ = leviStarHom γ := rfl

end CFSG.Monster.B.E6.StdF4
