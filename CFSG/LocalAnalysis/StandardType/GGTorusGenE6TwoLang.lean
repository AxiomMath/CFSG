module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open TableBExc.E6Three TableBExcTwo TableBExcTwoFusion

namespace E6TwoGen

section Frame


@[expose] def frameE6Two : OrthFrame .E6 3 where
  root := bE6
  symm_one := fun i => by simp [Tag.symmetrizer]
  isRoot := isRoot_bE6
  orth := fun i j h => (iform_bE6 i j h).1

@[expose] noncomputable def wE6Two : WeylGroup .E6 :=
  rootReflection (bE6 0) * rootReflection (bE6 1) * rootReflection (bE6 2) *
    rootReflection (bE6 3)

end Frame

section Lang

variable
  {L : Type} [Field L]

theorem frameProd_inv_conj_rho {τ : Tag} {d : ℕ} (F : OrthFrame τ d) (i : Fin (d + 1))
    (A X : SL2 L) :
    (frameProd L F A)⁻¹ * rho L F i X * frameProd L F A = rho L F i (A⁻¹ * X * A) := by
  let f : Fin (d + 1) → adjointGroup τ L := fun j => if j = i then rho L F i A else 1
  let g : Fin (d + 1) → adjointGroup τ L := fun j => if j = i then 1 else rho L F j A
  have hfg : ∀ j, f j * g j = rho L F j A := by
    intro j
    by_cases h : j = i
    · rw [h]; simp [f, g]
    · simp [f, g, h]
  have hcomm : ∀ j k, j ≠ k → Commute (f j) (g k) := by
    intro j k hjk
    by_cases hj : j = i
    · have hik : i ≠ k := fun e => hjk (hj.trans e)
      have hki : k ≠ i := fun e => hik e.symm
      rw [show f j = rho L F i A by simp [f, hj],
        show g k = rho L F k A by simp [g, hki]]
      exact commute_rho F hik A A
    · rw [show f j = 1 by simp [f, hj]]
      exact Commute.one_left _
  have hframe : frameProd L F A = (List.ofFn f).prod * (List.ofFn g).prod := by
    rw [frameProd,
      show (fun j : Fin (d + 1) => rho L F j A) = fun j => f j * g j from
        funext fun j => (hfg j).symm]
    exact list_prod_ofFn_mul_of_ne f g hcomm
  have hf : (List.ofFn f).prod = rho L F i A := by
    rw [list_prod_ofFn_eq_of_ne_one f i fun j hj => by simp [f, hj]]
    simp [f]
  have hG : Commute (List.ofFn g).prod (rho L F i (A⁻¹ * X * A)) :=
    Commute.list_prod_left _ _ fun x hx => by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
      by_cases hk : k = i
      · rw [show g k = 1 by simp [g, hk]]
        exact Commute.one_left _
      · rw [show g k = rho L F k A by simp [g, hk]]
        exact commute_rho F hk A (A⁻¹ * X * A)
  have hA : (rho L F i A)⁻¹ * rho L F i X * rho L F i A = rho L F i (A⁻¹ * X * A) := by
    rw [← map_inv, ← map_mul, ← map_mul]
  rw [hframe, hf, mul_inv_rev]
  calc (List.ofFn g).prod⁻¹ * (rho L F i A)⁻¹ * rho L F i X * (rho L F i A * (List.ofFn g).prod)
      = (List.ofFn g).prod⁻¹ * ((rho L F i A)⁻¹ * rho L F i X * rho L F i A) *
          (List.ofFn g).prod := by group
    _ = (List.ofFn g).prod⁻¹ * rho L F i (A⁻¹ * X * A) * (List.ofFn g).prod := by rw [hA]
    _ = rho L F i (A⁻¹ * X * A) := by
        rw [mul_assoc, hG.eq.symm, ← mul_assoc, inv_mul_cancel, one_mul]

variable [CharP L 2]

theorem coe_frameProd_nSL_one :
    ((frameProd L frameE6Two (nSL 1) : adjointGroup .E6 L) : ModGL .E6 L) =
      canonicalRep (coxeterSystem .E6) L wE6Two := by
  have h : (List.ofFn fun i : Fin 4 =>
        ((rho L frameE6Two i (nSL 1) : adjointGroup .E6 L) : ModGL .E6 L)) =
      List.ofFn fun i : Fin 4 =>
        canonicalRep (coxeterSystem .E6) L (rootReflection (bE6 i)) := by
    apply congrArg List.ofFn
    funext i
    rw [coe_rho]
    exact CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
      (M := L) (isRoot_bE6 i)
  rw [frameProd, SubmonoidClass.coe_list_prod, List.map_ofFn]
  change (List.ofFn fun i : Fin 4 =>
      ((rho L frameE6Two i (nSL 1) : adjointGroup .E6 L) : ModGL .E6 L)).prod =
    canonicalRep (coxeterSystem .E6) L wE6Two
  rw [h]
  change [canonicalRep (coxeterSystem .E6) L (rootReflection (bE6 0)),
    canonicalRep (coxeterSystem .E6) L (rootReflection (bE6 1)),
    canonicalRep (coxeterSystem .E6) L (rootReflection (bE6 2)),
    canonicalRep (coxeterSystem .E6) L (rootReflection (bE6 3))].prod =
      canonicalRep (coxeterSystem .E6) L wE6Two
  simp only [List.prod_cons, List.prod_nil, mul_one]
  rw [wE6Two, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]
  simp only [mul_assoc]

theorem units_map_frameProd {τ : Tag} {d : ℕ} (σ : L →+* L) (F : OrthFrame τ d) (A : SL2 L) :
    Units.map (entrywiseHom σ) ((frameProd L F A : adjointGroup τ L) : ModGL τ L) =
      ((frameProd L F (Matrix.SpecialLinearGroup.map σ A) : adjointGroup τ L) : ModGL τ L) := by
  rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self, ← coe_adjointMap,
    adjointMap_frameProd]

theorem units_map_frameProd_langP {x : L} (hx : x ^ 2 + x + 1 = 0) (σ : L →+* L)
    (hσ : σ x = x ^ 2) :
    Units.map (entrywiseHom σ)
        ((frameProd L frameE6Two (langP hx) : adjointGroup .E6 L) : ModGL .E6 L) =
      ((frameProd L frameE6Two (langP hx) : adjointGroup .E6 L) : ModGL .E6 L) *
        canonicalRep (coxeterSystem .E6) L wE6Two := by
  rw [units_map_frameProd, map_langP hx σ hσ, frameProd_mul, Subgroup.coe_mul,
    coe_frameProd_nSL_one]

theorem frameProd_inv_conj_uE6Two {K : Type} [Field K] [CharP K 2] (f : K →+* L) {ω : Lˣ}
    (hx : (ω : L) ^ 2 + ω + 1 = 0) (i : Fin 4) :
    ((frameProd L frameE6Two (langP hx) : adjointGroup .E6 L) : ModGL .E6 L)⁻¹ *
        baseChangeGL f ((uE6Two (K := K) i : adjointGroup .E6 K) : ModGL .E6 K) *
        ((frameProd L frameE6Two (langP hx) : adjointGroup .E6 L) : ModGL .E6 L) =
      rootSL2 .E6 L (bE6 i) (HSL ω) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hmid : baseChangeGL f ((uE6Two (K := K) i : adjointGroup .E6 K) : ModGL .E6 K) =
      ((rho L frameE6Two i (uSL 1 * vSL 1) : adjointGroup .E6 L) : ModGL .E6 L) := by
    rw [coe_uE6Two_eq h2 i,
      CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo f (isRoot_bE6 i),
      map_uSL_mul_vSL]
    exact (coe_rho (K := L) frameE6Two i (uSL 1 * vSL 1)).symm
  have hP : (langP hx)⁻¹ * (uSL 1 * vSL 1) * langP hx = HSL ω := by
    calc (langP hx)⁻¹ * (uSL 1 * vSL 1) * langP hx
        = (langP hx)⁻¹ * ((uSL 1 * vSL 1) * langP hx) := by rw [mul_assoc]
      _ = (langP hx)⁻¹ * (langP hx * HSL ω) := by rw [← langP_mul_HSL hx]
      _ = HSL ω := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [hmid, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
    frameProd_inv_conj_rho frameE6Two i (langP hx) (uSL 1 * vSL 1), hP, coe_rho]
  rfl

end Lang

end E6TwoGen

end CFSG.StandardType
