module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN3MovedContradiction
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4UniqueAbstract
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4TransvectionAxisOnly

public section

noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.ASVolI.ChH
open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCRootAxis
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open CFSG.Quasithin.G11 CFSG.Quasithin.H13.H11P
open scoped Matrix

local notation "F₄" => GaloisField 2 2
local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

theorem huniq_of_axisOfTensorModel
    {W : Type} [CommGroup W] [Finite W] {Y : Subgroup (MulAut W)} {U : Subgroup W}
    [Module (ZMod 2) (Additive ↥U)]
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U)
    {H : Subgroup (GLV (Additive ↥U))} (hHY : H = (restrictActionHom hYU).range)
    {φ : ↥H ≃* ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄)}
    {ψ : Additive ↥U ≃ₗ[ZMod 2] M₄}
    (hψ : ∀ (h : ↥H) (v : Additive ↥U),
      ψ ((h : GLV (Additive ↥U)) v) =
        (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ v *
          ((((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ)
    (D : Subgroup (MulAut W)) (hD0 : D ⊓ centSub U = ⊥)
    (hDN : ∀ e ∈ D, Y.map (MulAut.conj e).toMonoidHom = Y)
    (hDU : ∀ e ∈ D, ∀ u ∈ U, e u ∈ U)
    (Hax : Submodule F₄ M₄)
    (hT : ∀ e (he : e ∈ D), e ∉ centSub U →
      IsFTransvectionOn F₄ M₄
          (transportedAutHom ψ (restrictLinearOf e (hDU e he))) ∧
        fixVSub (F := F₄) (M := M₄)
          (transportedAutHom ψ (restrictLinearOf e (hDU e he))) = Hax) :
    ∀ e ∈ D, e ∉ centSub U → ∀ f ∈ D, f ∉ centSub U →
      (∀ u ∈ U, e u = u ↔ f u = u) → e = f := by
  intro e heD henot f hfD hfnot _hfix
  let T := transportedAutHom ψ
  let re := restrictLinearOf e (hDU e heD)
  let rf := restrictLinearOf f (hDU f hfD)
  have hHmap : H.map T = Lm F₄ := isTensorModel_map_transportedAutHom_eq_Lm hψ
  have hreN : re ∈ Subgroup.normalizer (H : Set (GLV (Additive ↥U))) :=
    restrictLinearOf_mem_normalizer hYU H hHY (hDN e heD) (hDU e heD)
  have hrfN : rf ∈ Subgroup.normalizer (H : Set (GLV (Additive ↥U))) :=
    restrictLinearOf_mem_normalizer hYU H hHY (hDN f hfD) (hDU f hfD)
  have hteN : T re ∈ Subgroup.normalizer
      ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄))) :=
    transportedAutHom_mem_normalizer hHmap hreN
  have htfN : T rf ∈ Subgroup.normalizer
      ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄))) :=
    transportedAutHom_mem_normalizer hHmap hrfN
  have hteT : IsFTransvectionOn F₄ M₄ (T re) := (hT e heD henot).1
  have htfT : IsFTransvectionOn F₄ M₄ (T rf) := (hT f hfD hfnot).1
  have hteFix : fixVSub (F := F₄) (M := M₄) (T re) = Hax := (hT e heD henot).2
  have htfFix : fixVSub (F := F₄) (M := M₄) (T rf) = Hax := (hT f hfD hfnot).2
  have hHfin : Module.finrank F₄ Hax = 3 := by
    rw [← hteFix]
    have h := hteT.fixV_finrank
    have hdim : Module.finrank F₄ M₄ = 4 := by
      rw [Module.finrank_matrix, Module.finrank_self]
      norm_num
    rw [hdim] at h
    simpa using h
  let S : Set (MulAut (VM F₄)) :=
    {t | t ∈ Subgroup.normalizer
        ((Lm F₄ : Subgroup (MulAut (VM F₄))) : Set (MulAut (VM F₄)))
      ∧ IsFTransvectionOn F₄ M₄ t ∧ fixVSub (F := F₄) (M := M₄) t = Hax}
  have hS : Nat.card S ≤ 1 := ncard_fTransvectionSet_fixed_axis_le_one Hax hHfin
  haveI : Finite S := Subtype.finite
  have hsub : Subsingleton S := (Finite.card_le_one_iff_subsingleton).mp hS
  have hteS : T re ∈ S := ⟨hteN, hteT, hteFix⟩
  have htfS : T rf ∈ S := ⟨htfN, htfT, htfFix⟩
  have hTeq : T re = T rf :=
    congrArg Subtype.val (Subsingleton.elim (⟨T re, hteS⟩ : S) ⟨T rf, htfS⟩)
  have hreq : re = rf := transportedAutHom_injective ψ hTeq
  have heqU : ∀ u ∈ U, e u = f u :=
    restrictLinearOf_eq_on (hDU e heD) (hDU f hfD) hreq
  have hmem : e * f⁻¹ ∈ D := D.mul_mem heD (D.inv_mem hfD)
  have hfixU : e * f⁻¹ ∈ centSub U := by
    rw [mem_centSub]
    intro u hu
    have hfu : f⁻¹ u ∈ U := inv_mem_of_forall_mem f (hDU f hfD) u hu
    calc (e * f⁻¹) u = e (f⁻¹ u) := rfl
      _ = f (f⁻¹ u) := heqU (f⁻¹ u) hfu
      _ = u := by simp
  have hbot : e * f⁻¹ ∈ (⊥ : Subgroup (MulAut W)) := by
    rw [← hD0]
    exact ⟨hmem, hfixU⟩
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)

lemma mem_fixVSub_transportedAutHom_restrictLinearOf_iff
    {W : Type} [CommGroup W] [Finite W] {U A : Subgroup W}
    [Module (ZMod 2) (Additive ↥U)] {e : MulAut W} (he : ∀ u ∈ U, e u ∈ U)
    (ψ : Additive ↥U ≃ₗ[ZMod 2] M₄)
    (hT : IsFTransvectionOn F₄ M₄ (transportedAutHom ψ (restrictLinearOf e he)))
    (hA : ∀ u ∈ U, e u = u ↔ u ∈ A) (m : M₄) :
    m ∈ fixVSub (F := F₄) (M := M₄) (transportedAutHom ψ (restrictLinearOf e he)) ↔
      ∃ u : ↥U, (u : W) ∈ A ∧ ψ (Additive.ofMul u) = m := by
  obtain ⟨g, hg, -, -⟩ := hT
  have hgm : ∀ x : M₄, g x = ψ (restrictLinearOf e he (ψ.symm x)) := by
    intro x
    have h1 := congrArg (fun t : MulAut (VM F₄) => t (Multiplicative.ofAdd x)) hg
    simp only [linToMulAut_ofAdd, transportedAutHom_apply] at h1
    exact Multiplicative.ofAdd.injective h1
  rw [← hg, fixVSub_linToMulAut, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]
  rw [hgm m]
  constructor
  · intro h
    have h2 : restrictLinearOf e he (ψ.symm m) = ψ.symm m := by
      apply ψ.injective
      simpa using h
    obtain ⟨u, hum⟩ : ∃ u : ↥U, ψ.symm m = Additive.ofMul u := ⟨Additive.toMul (ψ.symm m), rfl⟩
    rw [hum, restrictLinearOf_ofMul he u] at h2
    have h3 : e (u : W) = (u : W) := congrArg Subtype.val (Additive.ofMul.injective h2)
    refine ⟨u, (hA (u : W) u.2).1 h3, ?_⟩
    rw [← hum]
    simp
  · rintro ⟨u, huA, rfl⟩
    rw [LinearEquiv.symm_apply_apply, restrictLinearOf_ofMul he u]
    have hfix : e (u : W) = (u : W) := (hA (u : W) u.2).2 huA
    have hsub : (⟨e (u : W), he (u : W) u.2⟩ : ↥U) = u := Subtype.ext hfix
    rw [hsub]

end CFSG.LocalAnalysis.WeakClosure81

end

end
