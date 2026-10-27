module

public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
import CFSG.LocalAnalysis.StandardType.GGE6DepModelReflClass

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.TableBExc.E6Three
  CFSG.SeitzReduction CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.NoOffRest CFSG.StandardType.E6Dep

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Bridge

private def bridgeM : Mat6 :=
  !![0,0,1,2,0,1; 0,0,0,1,2,0; 0,0,0,0,1,2; 0,0,0,0,0,1; 0,1,0,0,2,1; 1,0,2,0,1,2]

private def bridgeMinv : Mat6 :=
  !![1,1,0,0,0,1; 0,0,1,0,1,0; 1,1,1,0,0,0; 0,1,1,1,0,0; 0,0,1,1,0,0; 0,0,0,1,0,0]

private def bridgeSigma : Fin 6 → Fin 6 := ![0, 5, 1, 2, 3, 4]

private theorem bridgeM_mul_inv : bridgeM * bridgeMinv = 1 := by decide +kernel

private theorem bridgeMinv_mul : bridgeMinv * bridgeM = 1 := by decide +kernel

private theorem bridge_gen : ∀ i : Fin 6, ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
    bridgeM.mulVec (adRefl Tag.E6 3 i x) = (gensL (bridgeSigma i)).mulVec (bridgeM.mulVec x) := by
  decide +kernel

private def rootReflMat (γ : Fin Tag.E6.rank → ℤ) : Mat6 :=
  1 - Matrix.vecMulVec (show Fin 6 → ZMod 3 from kgExpVec γ) (fun j : Fin 6 => ((γ j : ℤ) : ZMod 3))

private def projH : Mat6 := Matrix.diagonal ![1, 1, 1, 1, 1, 0]

private theorem bridge_refl36 : ∀ c : Fin 6 → ZMod 3, c 5 = 0 → norm6 c = 1 →
    ∃ m : Fin 72, bridgeM * rootReflMat (CFSG.RankThree.E6.e6RootVec m) * bridgeMinv * projH =
      reflNorm c * projH := by
  decide +kernel

end Bridge

section Layer

private def e5 : Vec6 := Pi.single (5 : Fin 6) (1 : ZMod 3)

private def toF6 (v : Fin Tag.E6.rank → ZMod 3) : Vec6 := fun i => v i

private def toFR (v : Vec6) : Fin Tag.E6.rank → ZMod 3 := fun i => v i

private theorem toFR_toF6 (v : Fin Tag.E6.rank → ZMod 3) : toFR (toF6 v) = v := rfl

private theorem toF6_injective : Function.Injective toF6 := by
  intro a b h
  funext i
  exact congrFun h i

private def bM (x : Fin Tag.E6.rank → ZMod 3) : Vec6 := bridgeM.mulVec (toF6 x)

private theorem bM_eq (x : Fin Tag.E6.rank → ZMod 3) : bM x = bridgeM.mulVec (toF6 x) := rfl

private theorem bM_toFR (v : Vec6) : bM (toFR v) = bridgeM.mulVec v := rfl

private theorem bM_five : ∀ x : Fin Tag.E6.rank → ZMod 3, (bM x) 5 = kDotP 3 x := by
  decide +kernel

private theorem bridgeM_mulVec_injective : Function.Injective bridgeM.mulVec := by
  intro a b h
  have := congrArg bridgeMinv.mulVec h
  simpa only [Matrix.mulVec_mulVec, bridgeMinv_mul, Matrix.one_mulVec] using this

private theorem bM_injective : Function.Injective bM := by
  intro a b h
  exact toF6_injective (bridgeM_mulVec_injective h)

private theorem bridgeMinv_bridgeM_mulVec (v : Vec6) : bridgeMinv.mulVec (bridgeM.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, bridgeMinv_mul, Matrix.one_mulVec]

private theorem bridgeM_bridgeMinv_mulVec (v : Vec6) : bridgeM.mulVec (bridgeMinv.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, bridgeM_mul_inv, Matrix.one_mulVec]

private theorem projH_mulVec_of_five : ∀ v : Vec6, v 5 = 0 → projH.mulVec v = v := by
  decide +kernel

private theorem gensL_fix_e5 : ∀ i : Fin 6, (gensL i).mulVec e5 = e5 := by
  decide +kernel

private theorem closureL_fix_e5 {T : Mat6} (hT : T ∈ closureL) : T.mulVec e5 = e5 := by
  induction hT using Submonoid.closure_induction with
  | mem T hT =>
    obtain ⟨i, rfl⟩ := hT
    exact gensL_fix_e5 i
  | one => rw [Matrix.one_mulVec]
  | mul a b _ _ iha ihb => rw [← Matrix.mulVec_mulVec, ihb, iha]

private theorem bridge_gen_bM (i : Fin 6) (x : Fin Tag.E6.rank → ZMod 3) (hx : kDotP 3 x = 0) :
    bM (adRefl Tag.E6 3 i x) = (gensL (bridgeSigma i)).mulVec (bM x) := by
  change bridgeM.mulVec (adRefl Tag.E6 3 i x) =
    (gensL (bridgeSigma i)).mulVec (bridgeM.mulVec x)
  exact bridge_gen i x hx

private theorem exists_transport (u : WeylGroup Tag.E6) :
    ∃ T ∈ closureL, ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x) := by
  induction u using (coxeterSystem Tag.E6).simple_induction_left with
  | one =>
    refine ⟨1, Submonoid.one_mem _, ?_⟩
    intro x _
    rw [adAct_one, Matrix.one_mulVec]
  | mul_simple_left w i ih =>
    obtain ⟨T, hT, hTspec⟩ := ih
    refine ⟨gensL (bridgeSigma i) * T, ?_, ?_⟩
    · have hgen : gensL (bridgeSigma i) ∈ closureL :=
        Submonoid.subset_closure (show gensL (bridgeSigma i) ∈ Set.range gensL from
          ⟨bridgeSigma i, rfl⟩)
      exact Submonoid.mul_mem closureL hgen hT
    · intro x hx
      have hwx : kDotP 3 (adAct Tag.E6 3 w x) = 0 :=
        mem_hypE6.mp (adAct_mem_hypE6 w (mem_hypE6.mpr hx))
      let i6 : Fin 6 := i
      have hi6 : i6 = i := rfl
      rw [adAct_mul, adAct_simple, ← hi6, bridge_gen_bM i6 (adAct Tag.E6 3 w x) hwx,
        ← Matrix.mulVec_mulVec, ← hTspec x hx]

private theorem mul_four_mulVec (A B C D : Mat6) (v : Vec6) :
    (A * B * C * D).mulVec v = A.mulVec (B.mulVec (C.mulVec (D.mulVec v))) := by
  simp only [← Matrix.mulVec_mulVec]

private theorem rootReflMat_mulVec (γ : Fin Tag.E6.rank → ℤ) (x : Vec6) :
    (rootReflMat γ).mulVec x = rootRefl γ x := by
  let a : Fin 6 → ZMod 3 := kgExpVec γ
  let b : Fin 6 → ZMod 3 := fun j => ((γ j : ℤ) : ZMod 3)
  have hM : rootReflMat γ = 1 - Matrix.vecMulVec a b := rfl
  have hfin : rootRefl γ x = (fun i : Fin 6 => x i - (∑ j : Fin 6, b j * x j) * a i) := rfl
  rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, hfin]
  ext i
  rw [Pi.sub_apply, Pi.smul_apply, op_smul_eq_mul]
  have hdot : b ⬝ᵥ x = ∑ j : Fin 6, b j * x j := rfl
  rw [hdot]
  ring

private theorem bM_rootRefl (γ : Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ZMod 3) :
    bM (rootRefl γ x) = bridgeM.mulVec ((rootReflMat γ).mulVec (toF6 x)) := by
  change bridgeM.mulVec (toF6 (rootRefl γ x)) =
    bridgeM.mulVec ((rootReflMat γ).mulVec (toF6 x))
  rw [rootReflMat_mulVec]
  rfl

private def decPsi (v : Vec6) : (Fin Tag.E6.rank → ZMod 3) × ZMod 3 :=
  (toFR (bridgeMinv.mulVec (v - v 5 • e5)), v 5)

private def decPhi (p : (Fin Tag.E6.rank → ZMod 3) × ZMod 3) : Vec6 :=
  bM p.1 + p.2 • e5

private theorem decPhi_psi (v : Vec6) : decPhi (decPsi v) = v := by
  change bM (toFR (bridgeMinv.mulVec (v - v 5 • e5))) + v 5 • e5 = v
  rw [bM_toFR, Matrix.mulVec_mulVec, bridgeM_mul_inv, Matrix.one_mulVec]
  abel

private theorem decPhi_five (p : (Fin Tag.E6.rank → ZMod 3) × ZMod 3) (hp : kDotP 3 p.1 = 0) :
    (decPhi p) 5 = p.2 := by
  change (bM p.1 + p.2 • e5) 5 = p.2
  rw [Pi.add_apply, Pi.smul_apply, bM_five p.1, hp]
  simp [e5, smul_eq_mul]

private theorem decPsi_phi (p : (Fin Tag.E6.rank → ZMod 3) × ZMod 3) (hp : kDotP 3 p.1 = 0) :
    decPsi (decPhi p) = p := by
  have hfive : (decPhi p) 5 = p.2 := decPhi_five p hp
  change (toFR (bridgeMinv.mulVec (decPhi p - (decPhi p) 5 • e5)), (decPhi p) 5) = (p.1, p.2)
  refine Prod.ext ?_ ?_
  · have hsub : decPhi p - (decPhi p) 5 • e5 = bM p.1 := by
      rw [hfive]
      change bM p.1 + p.2 • e5 - p.2 • e5 = bM p.1
      abel
    rw [hsub, bM_eq, Matrix.mulVec_mulVec, bridgeMinv_mul, Matrix.one_mulVec, toFR_toF6]
  · exact hfive

private theorem decPsi_mem (v : Vec6) : (decPsi v).1 ∈ hypE6 := by
  change toFR (bridgeMinv.mulVec (v - v 5 • e5)) ∈ hypE6
  apply mem_hypE6.mpr
  rw [← bM_five (toFR (bridgeMinv.mulVec (v - v 5 • e5))), bM_toFR,
    bridgeM_bridgeMinv_mulVec]
  simp [e5, Pi.sub_apply, Pi.smul_apply]

private theorem decPsi_fixed (u : WeylGroup Tag.E6) (T : Mat6)
    (hT : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x))
    (hTe5 : T.mulVec e5 = e5) (v : {v : Vec6 // T.mulVec v = v}) :
    adAct Tag.E6 3 u (decPsi v.1).1 = (decPsi v.1).1 := by
  let x : Fin Tag.E6.rank → ZMod 3 := (decPsi v.1).1
  have hx : x = (decPsi v.1).1 := rfl
  have hxK : kDotP 3 x = 0 := by rw [hx]; exact mem_hypE6.mp (decPsi_mem v.1)
  have hv : v.1 = bM x + (decPsi v.1).2 • e5 := by
    conv_lhs => rw [← decPhi_psi v.1]
    rfl
  have h1 : T.mulVec (bM x + (decPsi v.1).2 • e5) = bM x + (decPsi v.1).2 • e5 := by
    rw [← hv]; exact v.2
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hTe5, ← hT x hxK] at h1
  have h2 : bM (adAct Tag.E6 3 u x) = bM x := add_right_cancel h1
  rw [← hx]
  exact bM_injective h2

private theorem decPhi_fixed (u : WeylGroup Tag.E6) (T : Mat6)
    (hT : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x))
    (hTe5 : T.mulVec e5 = e5)
    (p : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} × ZMod 3) :
    T.mulVec (decPhi (p.1.1, p.2)) = decPhi (p.1.1, p.2) := by
  let x : Fin Tag.E6.rank → ZMod 3 := p.1.1
  let t : ZMod 3 := p.2
  have hx : x = p.1.1 := rfl
  have ht : t = p.2 := rfl
  have hxK : kDotP 3 x = 0 := by rw [hx]; exact mem_hypE6.mp p.1.2.1
  have hxfix : adAct Tag.E6 3 u x = x := by rw [hx]; exact p.1.2.2
  change T.mulVec (bM x + t • e5) = bM x + t • e5
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hTe5, ← hT x hxK, hxfix]

private def fixToFun (u : WeylGroup Tag.E6) (T : Mat6)
    (hT : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x))
    (hTe5 : T.mulVec e5 = e5) (v : {v : Vec6 // T.mulVec v = v}) :
    {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} × ZMod 3 :=
  (⟨(decPsi v.1).1, decPsi_mem v.1, decPsi_fixed u T hT hTe5 v⟩, (decPsi v.1).2)

private def fixInvFun (u : WeylGroup Tag.E6) (T : Mat6)
    (hT : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x))
    (hTe5 : T.mulVec e5 = e5)
    (p : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} × ZMod 3) :
    {v : Vec6 // T.mulVec v = v} :=
  ⟨decPhi (p.1.1, p.2), decPhi_fixed u T hT hTe5 p⟩

private theorem fixInvFun_toFun (u : WeylGroup Tag.E6) (T : Mat6)
    (hT : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x))
    (hTe5 : T.mulVec e5 = e5) :
    Function.LeftInverse (fixInvFun u T hT hTe5) (fixToFun u T hT hTe5) := by
  intro v
  apply Subtype.ext
  exact decPhi_psi v.1

private theorem fixToFun_invFun (u : WeylGroup Tag.E6) (T : Mat6)
    (hT : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x))
    (hTe5 : T.mulVec e5 = e5) :
    Function.RightInverse (fixInvFun u T hT hTe5) (fixToFun u T hT hTe5) := by
  intro p
  have hp : kDotP 3 p.1.1 = 0 := mem_hypE6.mp p.1.2.1
  have h := decPsi_phi (p.1.1, p.2) hp
  have h1 : (decPsi (decPhi (p.1.1, p.2))).1 = p.1.1 := congrArg Prod.fst h
  have h2 : (decPsi (decPhi (p.1.1, p.2))).2 = p.2 := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext h1) h2

private def fixEquiv (u : WeylGroup Tag.E6) (T : Mat6)
    (hT : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 →
      bM (adAct Tag.E6 3 u x) = T.mulVec (bM x))
    (hTe5 : T.mulVec e5 = e5) :
    {v : Vec6 // T.mulVec v = v} ≃
      ({x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} × ZMod 3) :=
  Equiv.mk (fixToFun u T hT hTe5) (fixInvFun u T hT hTe5)
    (fixInvFun_toFun u T hT hTe5) (fixToFun_invFun u T hT hTe5)

end Layer

theorem exists_root_of_isRefl (u : WeylGroup Tag.E6)
    (hsq : ∀ x ∈ hypE6, adAct Tag.E6 3 u (adAct Tag.E6 3 u x) = x)
    (hfix : Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} * 3 =
      3 ^ 5) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ ∀ x ∈ hypE6, adAct Tag.E6 3 u x = rootRefl γ x := by
  classical
  obtain ⟨T, hT, hTspec⟩ := exists_transport u
  have hTe5 : T.mulVec e5 = e5 := closureL_fix_e5 hT
  have hTT : T * T = 1 := by
    refine Matrix.mulVec_injective (funext fun v => ?_)
    show (T * T).mulVec v = (1 : Mat6).mulVec v
    rw [Matrix.one_mulVec]
    let x : Fin Tag.E6.rank → ZMod 3 := (decPsi v).1
    let t : ZMod 3 := v 5
    have hv : v = bM x + t • e5 := by
      conv_lhs => rw [← decPhi_psi v]
      rfl
    have hxK : kDotP 3 x = 0 := mem_hypE6.mp (decPsi_mem v)
    have hxH : x ∈ hypE6 := mem_hypE6.mpr hxK
    have hTx : T.mulVec (bM x) = bM (adAct Tag.E6 3 u x) := (hTspec x hxK).symm
    have hTx2 : T.mulVec (bM (adAct Tag.E6 3 u x)) =
        bM (adAct Tag.E6 3 u (adAct Tag.E6 3 u x)) :=
      (hTspec (adAct Tag.E6 3 u x) (mem_hypE6.mp (adAct_mem_hypE6 u hxH))).symm
    calc
      (T * T).mulVec v = T.mulVec (T.mulVec v) := (Matrix.mulVec_mulVec v T T).symm
      _ = T.mulVec (T.mulVec (bM x + t • e5)) := by rw [hv]
      _ = T.mulVec (bM (adAct Tag.E6 3 u x) + t • e5) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul, hTe5, hTx]
      _ = T.mulVec (bM (adAct Tag.E6 3 u x)) + t • e5 := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul, hTe5]
      _ = bM (adAct Tag.E6 3 u (adAct Tag.E6 3 u x)) + t • e5 := by rw [hTx2]
      _ = bM x + t • e5 := by rw [hsq x hxH]
      _ = v := by rw [hv]
  have hcard : Nat.card {v : Vec6 // T.mulVec v = v} =
      Nat.card ({x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} × ZMod 3) :=
    Nat.card_congr (fixEquiv u T hTspec hTe5)
  have hfix6 : Fintype.card {v : Vec6 // T.mulVec v = v} * 3 = 3 ^ 6 := by
    have h3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
    have hcard' : Nat.card {v : Vec6 // T.mulVec v = v} =
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 // x ∈ hypE6 ∧ adAct Tag.E6 3 u x = x} * 3 := by
      rw [hcard, Nat.card_prod, h3]
    have hmain : Nat.card {v : Vec6 // T.mulVec v = v} * 3 = 3 ^ 6 := by
      rw [hcard', hfix]
      norm_num
    rwa [Nat.card_eq_fintype_card] at hmain
  have hrefl : T ∈ refl36 := CFSG.StandardType.E6Dep.eq_refl36_of_isRefl hT hTT hfix6
  obtain ⟨c, hc, hcT⟩ := Finset.mem_image.mp hrefl
  obtain ⟨hc5, hcn⟩ := (Finset.mem_filter.mp hc).2
  obtain ⟨m, hm⟩ := bridge_refl36 c hc5 hcn
  refine ⟨CFSG.RankThree.E6.e6RootVec m, CFSG.RankThree.E6.isRoot_e6RootVec m, ?_⟩
  intro x hx
  have hw : (bM x) 5 = 0 := by
    rw [bM_five x]
    exact mem_hypE6.mp hx
  have hcomp : (reflNorm c).mulVec (bM x) =
      bridgeM.mulVec ((rootReflMat (CFSG.RankThree.E6.e6RootVec m)).mulVec (toF6 x)) := by
    calc
      (reflNorm c).mulVec (bM x)
          = (reflNorm c * projH).mulVec (bM x) := by
              conv_rhs => rw [← Matrix.mulVec_mulVec]
              rw [projH_mulVec_of_five (bM x) hw]
      _ = (bridgeM * rootReflMat (CFSG.RankThree.E6.e6RootVec m) * bridgeMinv * projH).mulVec
            (bM x) := by
              rw [← hm]
      _ = bridgeM.mulVec ((rootReflMat (CFSG.RankThree.E6.e6RootVec m)).mulVec (toF6 x)) := by
              rw [mul_four_mulVec, projH_mulVec_of_five (bM x) hw, bM_eq,
                bridgeMinv_bridgeM_mulVec]
  have h1 : bM (adAct Tag.E6 3 u x) = T.mulVec (bM x) := hTspec x (mem_hypE6.mp hx)
  have h2 : T.mulVec (bM x) =
      bridgeM.mulVec ((rootReflMat (CFSG.RankThree.E6.e6RootVec m)).mulVec (toF6 x)) := by
    rw [← hcT]
    exact hcomp
  have h3 : bM (adAct Tag.E6 3 u x) =
      bridgeM.mulVec ((rootReflMat (CFSG.RankThree.E6.e6RootVec m)).mulVec (toF6 x)) :=
    h1.trans h2
  have h4 : bM (adAct Tag.E6 3 u x) = bM (rootRefl (CFSG.RankThree.E6.e6RootVec m) x) := by
    rw [bM_rootRefl]
    exact h3
  exact bM_injective h4

end CFSG.StandardType.KGL

end
