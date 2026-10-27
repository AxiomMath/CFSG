module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.RankThree.Lattice.SteinbergBIE6QplusFold
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools

public section

namespace CFSG.StandardType.E6Two

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes

@[expose] def kerF (t : Fin Tag.F4.rank → ZMod 3) (γ : Fin Tag.E6.rank → ℤ) : Prop :=
  ∑ j, (γ j : ZMod 3) * ExcFrames.twE6ThreeFrame t j = 0

theorem rootChar_eq_one_iff_kerF {K : Type} [Field K] {ζ : Kˣ} {hζ : ζ ^ 3 = 1}
    (hζo : orderOf ζ = 3) (t : Fin Tag.F4.rank → ZMod 3) (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.twE6ThreeFrame t)) γ = 1 ↔ kerF t γ := by
  have hprim : IsPrimitiveRoot ζ 3 := hζo ▸ IsPrimitiveRoot.orderOf ζ
  rw [rootChar_eq_one_iff_dvd_pairing hprim _
    (fun j => (((ExcFrames.twE6ThreeFrame t j).val : ℕ) : ℤ)) (fun j => by
      rw [TableBExc.E6Three.zetaVec_apply, zpow_natCast]) γ]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold kerF
  push_cast
  simp only [ZMod.natCast_zmod_val]

private def kapL : List (List (ZMod 3)) :=
  [[2, 2, 0, 0],
   [0, 0, 2, 2],
   [2, 2, 2, 0],
   [0, 1, 2, 2],
   [2, 2, 2, 0],
   [2, 2, 0, 0],
   [1, 1, 0, 0],
   [1, 1, 2, 0],
   [0, 0, 1, 1],
   [0, 1, 1, 1],
   [1, 1, 1, 0],
   [2, 0, 1, 2],
   [0, 2, 1, 1],
   [2, 0, 1, 2],
   [1, 1, 1, 0],
   [1, 1, 2, 0],
   [1, 1, 0, 0],
   [2, 2, 1, 0],
   [1, 2, 1, 2],
   [0, 2, 2, 2],
   [2, 0, 0, 1],
   [2, 0, 0, 1],
   [1, 0, 2, 1],
   [1, 2, 0, 2],
   [1, 0, 2, 1],
   [1, 2, 1, 2],
   [2, 2, 1, 0],
   [2, 1, 2, 1],
   [1, 2, 0, 1],
   [0, 1, 0, 2],
   [1, 0, 0, 2],
   [1, 0, 0, 2],
   [1, 2, 2, 1],
   [1, 2, 0, 1],
   [2, 1, 0, 1],
   [0, 1, 0, 2],
   [2, 1, 2, 1],
   [2, 1, 0, 2],
   [0, 2, 0, 1],
   [0, 1, 2, 1],
   [2, 0, 0, 2],
   [2, 1, 1, 2],
   [2, 1, 0, 2],
   [1, 0, 1, 0],
   [0, 1, 2, 1],
   [0, 2, 0, 1],
   [0, 2, 1, 2],
   [1, 0, 0, 1],
   [0, 2, 1, 0],
   [2, 0, 2, 1],
   [2, 0, 2, 0],
   [0, 2, 1, 2],
   [0, 2, 1, 0],
   [0, 1, 2, 0],
   [1, 0, 1, 2],
   [2, 1, 0, 0],
   [2, 1, 1, 0],
   [0, 1, 2, 0],
   [2, 1, 0, 0],
   [1, 2, 0, 0],
   [1, 2, 2, 0],
   [1, 0, 0, 0],
   [1, 0, 0, 0],
   [1, 2, 0, 0],
   [2, 0, 0, 0],
   [2, 0, 0, 0],
   [0, 2, 2, 0],
   [0, 1, 1, 0],
   [0, 0, 1, 2],
   [0, 0, 2, 1],
   [0, 0, 0, 1],
   [0, 0, 0, 2]]

private def fixL : List Bool :=
  [false, true, false, true, false, false, false, false, true, true, false, false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, true, true, false, true, false, false, false, true, false, true, true, false, false, false, true, false, true, false, false, false, true, false, false, false, false, false, true, true, true, true, true, true]

private def ipvL : List (List ℕ) :=
  [[],
   [2, 4, 2, 1, 2, 2, 2, 2, 0, 3, 2, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 1],
   [],
   [2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3, 3, 0, 3, 3, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 3, 2, 3, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 2, 2],
   [],
   [],
   [],
   [],
   [2, 0, 2, 3, 2, 2, 2, 2, 4, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3, 3, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 1, 1, 3],
   [2, 3, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 3, 2, 0, 3, 3, 2, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 3, 2, 3, 3, 2, 1, 2, 3, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 3, 1],
   [],
   [],
   [2, 3, 3, 0, 3, 2, 2, 3, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 3, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2, 3, 2, 2, 3, 2, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2, 3, 1, 1, 3, 2, 2],
   [],
   [],
   [],
   [],
   [],
   [],
   [2, 1, 3, 1, 3, 2, 2, 3, 3, 0, 1, 2, 3, 2, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2, 2, 2, 2, 2, 3, 1, 2, 2, 1, 3],
   [],
   [],
   [],
   [1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 0, 3, 2, 3, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 1, 2, 2],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 2, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 3, 1, 0, 2, 3, 3, 2, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 2, 3, 1],
   [],
   [3, 3, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 0, 3, 2, 2, 2, 3, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 2, 2],
   [],
   [],
   [],
   [],
   [],
   [3, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 2, 0, 2, 3, 3, 2, 2, 2, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 2, 2],
   [3, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 3, 0, 2, 3, 2, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2, 2, 1, 3, 2, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 1, 3],
   [],
   [1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 2, 2, 2, 3, 3, 1, 0, 2, 3, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 1, 3, 1],
   [],
   [],
   [],
   [1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 0, 1, 2, 3, 2, 3, 2, 4, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2],
   [],
   [3, 3, 2, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 3, 3, 2, 2, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 2, 0, 2, 3, 2, 2, 2, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 3, 1],
   [3, 2, 2, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 2, 3, 2, 2, 2, 2, 2, 3, 3, 2, 0, 2, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2, 1, 3, 1, 3],
   [],
   [],
   [],
   [1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2, 0, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 3],
   [],
   [3, 2, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4, 1, 2, 2, 0, 3, 3, 2, 1, 1, 2, 2, 3, 1, 3, 1],
   [],
   [],
   [],
   [1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 2, 2, 1, 3, 3, 2, 0, 3, 2, 2, 4, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3],
   [],
   [],
   [],
   [],
   [],
   [2, 2, 3, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 3, 3, 1, 1, 1, 4, 0, 3, 1, 3, 1],
   [2, 2, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3, 3, 0, 4, 1, 3, 1, 3],
   [2, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2, 3, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 0, 3, 1],
   [2, 3, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3, 0, 4, 1, 3],
   [2, 3, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 4, 0],
   [2, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3, 1, 3, 1, 3, 0, 4]]

private def kapT (m : Fin 72) (c : Fin 4) : ZMod 3 := (kapL.getD m []).getD (c : ℕ) 0

private def fixT (m : Fin 72) : Bool := fixL.getD m false

private def ipvT (m n : Fin 72) : ℤ := (((ipvL.getD m []).getD n 2 : ℕ) : ℤ) - 2

private def kd (m : Fin 72) (a b c d : ZMod 3) : ZMod 3 :=
  kapT m 0 * a + kapT m 1 * b + kapT m 2 * c + kapT m 3 * d

private def inZ (δ α β : Fin 72) : Bool :=
  decide (e6RootVec β = e6RootVec δ ∨ e6RootVec β = -e6RootVec δ ∨ e6RootVec β = e6RootVec α ∨
    e6RootVec β = -e6RootVec α ∨ e6RootVec β = e6RootVec δ + e6RootVec α ∨
    e6RootVec β = -(e6RootVec δ + e6RootVec α))

private def hasMoved (δ : Fin 72) (a b c d : ZMod 3) : Bool :=
  (List.finRange 72).any fun γ => !(fixT γ) && decide (ipvT δ γ = -1) && decide (kd γ a b c d = 0)

private def closedZ (δ α : Fin 72) (a b c d : ZMod 3) : Bool :=
  (List.finRange 72).all fun β => !(decide (kd β a b c d = 0)) ||
    (decide (ipvT δ β = 0) && decide (ipvT α β = 0)) || inZ δ α β

private def hasA2 (δ : Fin 72) (a b c d : ZMod 3) : Bool :=
  (List.finRange 72).any fun α => fixT α && decide (ipvT δ α = -1) && decide (kd α a b c d = 0) &&
    closedZ δ α a b c d

private def coreB : Bool :=
  ([0, 1, 2] : List (ZMod 3)).all fun a => ([0, 1, 2] : List (ZMod 3)).all fun b =>
  ([0, 1, 2] : List (ZMod 3)).all fun c => ([0, 1, 2] : List (ZMod 3)).all fun d =>
    (decide (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) ||
    (List.finRange 72).all fun δ => !(fixT δ) || !(decide (kd δ a b c d = 0)) ||
      hasMoved δ a b c d || hasA2 δ a b c d

private theorem coreB_true : coreB = true := by decide +kernel

private theorem core_prop (a b c d : ZMod 3) (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0))
    (δ : Fin 72) (hf : fixT δ = true) (hk : kd δ a b c d = 0) :
    (∃ γ : Fin 72, fixT γ = false ∧ ipvT δ γ = -1 ∧ kd γ a b c d = 0) ∨
    (∃ α : Fin 72, fixT α = true ∧ ipvT δ α = -1 ∧ kd α a b c d = 0 ∧
      ∀ β : Fin 72, kd β a b c d = 0 → (ipvT δ β ≠ 0 ∨ ipvT α β ≠ 0) → inZ δ α β = true) := by
  have h := coreB_true
  unfold coreB at h
  simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_iff] at h
  have hz3 : ∀ x : ZMod 3, x ∈ ([0, 1, 2] : List (ZMod 3)) := by decide
  have h1 := h a (hz3 a) b (hz3 b) c (hz3 c) d (hz3 d)
  rcases h1 with h1 | h1
  · exact absurd h1 hne
  · have h2 := h1 δ (List.mem_finRange δ)
    have h3 : hasMoved δ a b c d = true ∨ hasA2 δ a b c d = true := by
      simpa [hf, hk] using h2
    rcases h3 with h3 | h3
    · left
      unfold hasMoved at h3
      simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_iff] at h3
      obtain ⟨γ, -, ⟨hγf, hγi⟩, hγk⟩ := h3
      exact ⟨γ, hγf, hγi, hγk⟩
    · right
      unfold hasA2 at h3
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h3
      obtain ⟨α, -, ⟨⟨hαf, hαi⟩, hαk⟩, hcl⟩ := h3
      refine ⟨α, hαf, hαi, hαk, fun β hβk hadj => ?_⟩
      unfold closedZ at hcl
      simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_iff, decide_eq_false_iff_not] at hcl
      rcases hcl β (List.mem_finRange β) with (hc | ⟨h3, h4⟩) | hc
      · exact absurd hβk hc
      · rcases hadj with h | h
        · exact absurd h3 h
        · exact absurd h4 h
      · exact hc

private abbrev orb4 (k : Fin Tag.E6.rank) : Fin 4 := ExcFrames.e6OrbitIdx k

private def kapOf (γ : Fin Tag.E6.rank → ℤ) (c : Fin 4) : ZMod 3 :=
  ∑ k, if orb4 k = c then
    ∑ j, (γ j : ZMod 3) * ((Tag.E6.cartan j k : ℤ) : ZMod 3) else 0

private theorem kapT_eq : ∀ m : Fin 72, ∀ c : Fin 4,
    kapT m c = kapOf (e6RootVec m) c := by
  decide +kernel

private theorem fixT_iff : ∀ m : Fin 72, fixT m = true ↔
    (permLattice TwistTag.E6.perm (e6RootVec m) : Fin Tag.E6.rank → ℤ) = e6RootVec m := by
  decide +kernel

private theorem ipvT_eq : ∀ m : Fin 72, fixT m = true → ∀ n : Fin 72,
    ipvT m n = iform (e6RootVec m) (e6RootVec n) := by
  decide +kernel

private theorem kerF_iff_kap (t : Fin Tag.F4.rank → ZMod 3) (γ : Fin Tag.E6.rank → ℤ) :
    kerF t γ ↔ ∑ c : Fin 4, kapOf γ c * t c = 0 := by
  unfold kerF
  have key : ∑ j, (γ j : ZMod 3) * ExcFrames.twE6ThreeFrame t j =
      ∑ c : Fin 4, kapOf γ c * t c := by
    calc ∑ j, (γ j : ZMod 3) * ExcFrames.twE6ThreeFrame t j
        = ∑ j, ∑ k, (γ j : ZMod 3) * ((Tag.E6.cartan j k : ℤ) : ZMod 3) *
            t (orb4 k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ExcFrames.twE6ThreeFrame_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, ∑ j, (γ j : ZMod 3) * ((Tag.E6.cartan j k : ℤ) : ZMod 3) *
            t (orb4 k) := Finset.sum_comm
      _ = ∑ k, (∑ j, (γ j : ZMod 3) * ((Tag.E6.cartan j k : ℤ) : ZMod 3)) *
            t (orb4 k) :=
          Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
      _ = ∑ k, ∑ c : Fin 4, (if orb4 k = c then
            ∑ j, (γ j : ZMod 3) * ((Tag.E6.cartan j k : ℤ) : ZMod 3) else 0) * t c := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_eq_single (orb4 k)]
          · simp
          · intro c _ hc
            simp [Ne.symm hc]
          · intro h
            exact absurd (Finset.mem_univ _) h
      _ = ∑ c : Fin 4, ∑ k, (if orb4 k = c then
            ∑ j, (γ j : ZMod 3) * ((Tag.E6.cartan j k : ℤ) : ZMod 3) else 0) * t c :=
          Finset.sum_comm
      _ = ∑ c : Fin 4, kapOf γ c * t c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [kapOf, Finset.sum_mul]
  rw [key]

private theorem kerF_rv (t : Fin Tag.F4.rank → ZMod 3) (m : Fin 72) :
    kerF t (e6RootVec m) ↔ kd m (t 0) (t 1) (t 2) (t 3) = 0 := by
  rw [kerF_iff_kap]
  have h4 : ∑ c : Fin 4, kapOf (e6RootVec m) c * t c =
      kapT m 0 * t 0 + kapT m 1 * t 1 + kapT m 2 * t 2 + kapT m 3 * t 3 := by
    rw [Fin.sum_univ_four]
    simp only [← kapT_eq]
    rfl
  rw [h4]
  rfl


private theorem iform_neg_left' {τ : Tag} (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, CFSG.LieType.Steinberg.Adjoint.iform_smul_left]
  ring

theorem fixed_cases
    (t : Fin Tag.F4.rank → ZMod 3) (ht : t ≠ 0) {δ : Fin Tag.E6.rank → ℤ}
    (hδ : IsRoot Tag.E6 δ) (hfix : permLattice TwistTag.E6.perm δ = δ) (hk : kerF t δ) :
    (∃ γ, IsRoot Tag.E6 γ ∧ permLattice TwistTag.E6.perm γ ≠ γ ∧ kerF t γ ∧ iform γ δ = -1) ∨
    (∃ α, IsA2Pair (τ := Tag.E6) δ α ∧ permLattice TwistTag.E6.perm α = α ∧ kerF t α ∧
      ∀ β, IsRoot Tag.E6 β → kerF t β → (iform β δ ≠ 0 ∨ iform β α ≠ 0) → β ∈ a2Roots δ α) := by
  classical
  have h22 : ∀ x, IsRoot Tag.E6 x → iform x x = 2 := fun x hx =>
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hx
  obtain ⟨m, hm⟩ := isRoot_iff_exists_e6RootVec.1 hδ
  subst hm
  have hfm : fixT m = true := (fixT_iff m).2 hfix
  have hkm : kd m (t 0) (t 1) (t 2) (t 3) = 0 := (kerF_rv t m).1 hk
  have hne : ¬(t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0 ∧ t 3 = 0) := by
    rintro ⟨h0, h1, h2, h3⟩
    apply ht
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  rcases core_prop (t 0) (t 1) (t 2) (t 3) hne m hfm hkm with
    ⟨g, hgf, hgi, hgk⟩ | ⟨a, haf, hai, hak, hcl⟩
  · left
    refine ⟨e6RootVec g, isRoot_e6RootVec g, ?_, (kerF_rv t g).2 hgk, ?_⟩
    · intro h
      have := (fixT_iff g).2 h
      rw [hgf] at this
      exact absurd this (by decide)
    · rw [CFSG.LieType.Steinberg.Adjoint.iform_comm, ← ipvT_eq m hfm g]
      exact hgi
  · right
    have hαr : IsRoot Tag.E6 (e6RootVec a) := isRoot_e6RootVec a
    have hda : iform (e6RootVec m) (e6RootVec a) = -1 := by rw [← ipvT_eq m hfm a]; exact hai
    have hne1 : e6RootVec m ≠ -e6RootVec a := fun h => by
      rw [h, iform_neg_left', h22 _ hαr] at hda
      omega
    refine ⟨e6RootVec a, ⟨hδ, hαr, ?_, ?_, ?_⟩, (fixT_iff a).1 haf, (kerF_rv t a).2 hak, ?_⟩
    · exact isRoot_add_of_iform_neg hδ hαr hne1 (by rw [hda]; decide)
    · rw [h22 _ hαr, h22 _ hδ]
    · rw [hda, h22 _ hδ]
      norm_num
    · intro β hβr hβk hadj
      obtain ⟨n, hn⟩ := isRoot_iff_exists_e6RootVec.1 hβr
      subst hn
      have hZ := hcl n ((kerF_rv t n).1 hβk) (by
        rcases hadj with h | h
        · left
          rw [ipvT_eq m hfm n, CFSG.LieType.Steinberg.Adjoint.iform_comm]
          exact h
        · right
          rw [ipvT_eq a haf n, CFSG.LieType.Steinberg.Adjoint.iform_comm]
          exact h)
      simp only [inZ, decide_eq_true_iff] at hZ
      simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hZ

end CFSG.StandardType.E6Two

end
