module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs
public import CFSG.LocalAnalysis.StandardType.GGD5AbsCoord
public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGR4PumpTransfer
import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem lup10c_card_Bs {G : Type} [Group G] {Bs : Subgroup G} {x y : G} {L H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis) :
    Nat.card Bs = 3 ^ 5 := by
  have h1 : Nat.card Bs = Nat.card M.V := Nat.card_congr M.model.toEquiv
  have h3 : Fintype.card M.ι = Module.finrank (ZMod 3) M.V := hbas.2
  have h2 : Module.finrank (ZMod 3) M.V = 5 := by
    rw [← h3, Fintype.card_congr e.symm, Fintype.card_fin]
  have : Module.Finite (ZMod 3) M.V := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod, h2]

private def lup10cg_s (i : Fin 4) : lup10fa_Mat := lup10fa_s i.castSucc

private def lup10cg_E : Fin 192 → lup10fa_Mat := ![
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 2, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 0, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 2, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 2, 1, 1, 0; 1, 2, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 2, 1, 1, 0; 0, 0, 1, 0, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 2, 1, 0; 0, 1, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 2, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 1, 2, 1; 0, 0, 1, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 0, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 0, 1, 1, 0; 2, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 0, 1, 1, 0; 0, 0, 1, 0, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 2, 1, 0; 0, 1, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 2, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 1, 2, 1; 0, 0, 1, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 2, 1, 1, 0; 1, 2, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 2, 1, 1, 0; 0, 0, 1, 0, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 2, 1, 0; 1, 2, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 2, 1, 1, 0; 1, 2, 0, 1, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 1, 2, 1; 0, 0, 1, 0, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 0, 2, 1, 0; 0, 1, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 2, 1, 0; 0, 1, 2, 0, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 1, 2, 2, 1; 0, 1, 2, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 0, 1, 2, 1; 0, 0, 1, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 1, 2, 1; 1, 0, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 0, 1, 1, 0; 2, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 0, 1, 1, 0; 0, 0, 1, 0, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 2, 1, 0; 2, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 0, 1, 1, 0; 2, 0, 0, 1, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 1, 2, 1; 0, 0, 1, 0, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 1, 2, 1, 0; 0, 1, 2, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 2, 1, 0; 0, 1, 2, 0, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 2, 2, 2, 1; 0, 1, 2, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 1, 1, 2, 1; 0, 0, 1, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 1, 2, 1; 2, 1, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 0, 2, 0; 1, 2, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 2, 1, 1, 0; 1, 2, 0, 1, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 2, 0, 1; 0, 0, 1, 0, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 0, 2, 1, 0; 1, 2, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 2, 1, 0; 1, 2, 0, 1, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 2, 2, 0, 0, 1; 1, 2, 0, 1, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 0, 1, 2, 1; 0, 0, 1, 0, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 0, 1, 2, 1; 1, 0, 0, 2, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 0, 2, 1, 0; 0, 1, 2, 0, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 1, 2, 2, 1; 0, 1, 2, 0, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 1, 2, 2, 1; 0, 1, 2, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 1, 2, 2, 1; 1, 0, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 0, 1, 2, 1; 1, 0, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 0, 2, 0; 2, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 0, 1, 1, 0; 2, 0, 0, 1, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 2, 0, 1; 0, 0, 1, 0, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 1, 2, 1, 0; 2, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 2, 1, 0; 2, 0, 0, 1, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 1, 1, 0, 0, 1; 2, 0, 0, 1, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 1, 1, 2, 1; 0, 0, 1, 0, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 1, 1, 2, 1; 2, 1, 0, 2, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 1, 2, 1, 0; 0, 1, 2, 0, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 2, 2, 2, 1; 0, 1, 2, 0, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 2, 2, 2, 1; 0, 1, 2, 0, 0; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 2, 2, 2, 1; 2, 1, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 1, 1, 2, 1; 2, 1, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 2, 0, 2, 0; 1, 2, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 0, 2, 0; 1, 2, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 1, 1, 1, 1; 1, 2, 0, 1, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 2, 2, 0, 1; 0, 0, 1, 0, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 2, 0, 1; 0, 2, 1, 0, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 0, 2, 1, 0; 1, 2, 0, 1, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 2, 2, 0, 0, 1; 1, 2, 0, 1, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 2, 2, 0, 0, 1; 1, 2, 0, 1, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 2, 2, 0, 0, 1; 1, 0, 0, 2, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 0, 1, 2, 1; 1, 0, 0, 2, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 1, 1, 0, 1; 0, 1, 2, 0, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 1, 2, 2, 1; 0, 1, 2, 0, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 1, 1, 2, 2, 1; 1, 0, 0, 2, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 1, 2, 2, 1; 1, 0, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 1, 0, 1, 2; 1, 0, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 2, 0, 2, 0; 2, 0, 0, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 0, 2, 0; 2, 0, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 2, 1, 1, 1; 2, 0, 0, 1, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 2, 2, 0, 1; 0, 0, 1, 0, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 0, 2, 2, 0, 1; 0, 2, 1, 0, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 1, 2, 1, 0; 2, 0, 0, 1, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 1, 1, 0, 0, 1; 2, 0, 0, 1, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 1, 1, 0, 0, 1; 2, 0, 0, 1, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 1, 1, 0, 0, 1; 2, 1, 0, 2, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 1, 1, 2, 1; 2, 1, 0, 2, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 1, 1, 0, 1; 0, 1, 2, 0, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 2, 2, 2, 1; 0, 1, 2, 0, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 2, 2, 2, 2, 1; 2, 1, 0, 2, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 2, 2, 2, 1; 2, 1, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 1, 0, 1, 2; 2, 1, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 2, 0, 2, 0; 1, 2, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 1, 1, 1, 1; 1, 2, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 1, 1, 1, 1; 1, 2, 0, 1, 0; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 1, 1, 1, 1; 0, 2, 1, 0, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 2, 2, 0, 1; 0, 2, 1, 0, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 2, 2, 1, 1; 1, 2, 0, 1, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 2, 2, 0, 0, 1; 1, 2, 0, 1, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 0, 0, 0, 0; 2, 2, 0, 0, 1; 1, 0, 0, 2, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 2, 2, 0, 0, 1; 1, 0, 0, 2, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 2, 1, 2, 2; 1, 0, 0, 2, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 1, 0, 1; 0, 1, 2, 0, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 1, 1, 0, 1; 0, 0, 2, 0, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 1, 2, 2, 1; 1, 0, 0, 2, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 0, 1, 2; 1, 0, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 1, 0, 1, 2; 1, 0, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 2, 0, 2, 0; 2, 0, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 2, 1, 1, 1; 2, 0, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 2, 1, 1, 1; 2, 0, 0, 1, 0; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 2, 1, 1, 1; 0, 2, 1, 0, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 2, 2, 0, 1; 0, 2, 1, 0, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 0, 2, 1, 1; 2, 0, 0, 1, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 1, 1, 0, 0, 1; 2, 0, 0, 1, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 1, 0, 0, 0; 1, 1, 0, 0, 1; 2, 1, 0, 2, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 1, 1, 0, 0, 1; 2, 1, 0, 2, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 0, 1, 2, 2; 2, 1, 0, 2, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 1, 0, 1; 0, 1, 2, 0, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 0, 1, 1, 0, 1; 0, 0, 2, 0, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 2, 2, 2, 1; 2, 1, 0, 2, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 0, 1, 2; 2, 1, 0, 2, 1; 0, 1, 0, 2, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 0, 1, 0, 1, 2; 2, 1, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 2, 2, 1, 1; 1, 2, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 1, 1, 1, 1; 1, 2, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 1, 1, 1, 1, 1; 0, 2, 1, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 1, 1, 1, 1; 0, 2, 1, 0, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 2, 1, 2, 2; 0, 2, 1, 0, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 2, 1, 1; 1, 2, 0, 1, 0; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 2, 2, 1, 1; 0, 0, 2, 0, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 2, 2, 0, 0, 1; 1, 0, 0, 2, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 1, 2, 2; 1, 0, 0, 2, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 2, 1, 2, 2; 1, 0, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 1, 0, 1; 0, 0, 2, 0, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 0, 2, 2, 2; 1, 0, 0, 2, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 0, 1, 2; 1, 0, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 0, 2, 1, 1; 2, 0, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 2, 1, 1, 1; 2, 0, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 2, 1, 1, 0; 2, 2, 1, 1, 1; 0, 2, 1, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 2, 1, 1, 1; 0, 2, 1, 0, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 0, 1, 2, 2; 0, 2, 1, 0, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 2, 1, 1; 2, 0, 0, 1, 0; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 0, 2, 1, 1; 0, 0, 2, 0, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 1, 1, 0, 0, 1; 2, 1, 0, 2, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 1, 2, 2; 2, 1, 0, 2, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 0, 1, 2, 2; 2, 1, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 1, 0, 1; 0, 0, 2, 0, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 1, 2, 2, 2; 2, 1, 0, 2, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 0, 1, 0, 1, 2; 2, 1, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 2, 1, 1; 1, 2, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 1, 2, 2, 1, 1; 0, 0, 2, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 1, 1, 1, 1; 0, 2, 1, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 1, 2, 2; 0, 2, 1, 0, 1; 1, 2, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 1, 2, 1, 2, 2; 0, 2, 1, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 2, 1, 1; 0, 0, 2, 0, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 0, 2, 2, 2; 1, 0, 0, 2, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 1, 2, 2; 1, 0, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 0, 2, 2, 2; 0, 0, 2, 0, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 0, 2, 2, 2; 1, 0, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 2, 1, 1; 2, 0, 0, 1, 0; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![0, 0, 2, 1, 0; 2, 0, 2, 1, 1; 0, 0, 2, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 2, 1, 1, 1; 0, 2, 1, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 1, 2, 2; 0, 2, 1, 0, 1; 2, 0, 1, 0, 1; 0, 0, 0, 0, 1],
  !![0, 0, 1, 2, 1; 2, 0, 1, 2, 2; 0, 2, 1, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 2, 1, 1; 0, 0, 2, 0, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 1, 2, 2, 2; 2, 1, 0, 2, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 1, 2, 2; 2, 1, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 1, 2, 2, 2; 0, 0, 2, 0, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 1, 2, 2, 2; 2, 1, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 2, 1, 1; 0, 0, 2, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 0, 2, 0, 0, 2; 0, 2, 1, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 2, 1, 2, 2; 0, 2, 1, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 0, 2, 2, 2; 0, 0, 2, 0, 1; 1, 0, 2, 0, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 0, 2, 2, 2; 1, 0, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 1, 0, 2, 2, 2; 0, 0, 2, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 2, 1, 1; 0, 0, 2, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 0, 2, 0, 0, 2; 0, 2, 1, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 0, 1, 2, 2; 0, 2, 1, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 1, 2, 2, 2; 0, 0, 2, 0, 1; 2, 1, 2, 0, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 1, 2, 2, 2; 2, 1, 0, 2, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![0, 1, 2, 2, 1; 2, 1, 2, 2, 2; 0, 0, 2, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 0, 2, 0, 0, 2; 0, 0, 2, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 0, 2, 0, 0, 2; 0, 2, 1, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 1, 0, 2, 2, 2; 0, 0, 2, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 0, 2, 0, 0, 2; 0, 0, 2, 0, 1; 0, 2, 0, 1, 1; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 0, 2, 0, 0, 2; 0, 2, 1, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 2, 1, 2, 2, 2; 0, 0, 2, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![1, 2, 0, 0, 1; 0, 2, 0, 0, 2; 0, 0, 2, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1],
  !![2, 0, 0, 0, 1; 0, 2, 0, 0, 2; 0, 0, 2, 0, 1; 0, 0, 0, 2, 2; 0, 0, 0, 0, 1]
]

private def lup10cg_t : Fin 4 → Fin 192 → Fin 192 := ![
  ![1, 0, 8, 6, 7, 14, 3, 4, 2, 20, 21, 25, 18, 28, 5, 30, 31, 35, 12, 38, 9, 10, 43, 41, 46, 11,
    48, 50, 13, 52, 15, 16, 56, 54, 59, 17, 61, 63, 19, 65, 66, 23, 69, 22, 71, 73, 24, 75, 26, 77,
    27, 79, 29, 81, 33, 84, 32, 86, 88, 34, 90, 36, 92, 37, 94, 39, 40, 96, 98, 42, 100, 44, 102,
    45, 104, 47, 106, 49, 108, 51, 109, 53, 111, 113, 55, 115, 57, 117, 58, 119, 60, 121, 62, 123,
    64, 124, 67, 127, 68, 129, 70, 131, 72, 133, 74, 134, 76, 136, 78, 80, 138, 82, 140, 83, 142,
    85, 144, 87, 146, 89, 147, 91, 149, 93, 95, 151, 152, 97, 154, 99, 155, 101, 157, 103, 105, 159,
    107, 158, 110, 162, 112, 164, 114, 165, 116, 167, 118, 120, 169, 122, 168, 125, 126, 172, 128,
    130, 174, 132, 137, 135, 175, 176, 139, 178, 141, 143, 180, 145, 150, 148, 181, 182, 153, 179,
    156, 160, 161, 186, 163, 173, 166, 170, 171, 189, 187, 188, 177, 184, 185, 183, 191, 190],
  ![2, 5, 0, 11, 13, 1, 17, 19, 14, 22, 24, 3, 27, 4, 8, 32, 34, 6, 37, 7, 40, 42, 9, 45, 10, 35,
    49, 12, 38, 51, 53, 55, 15, 58, 16, 25, 62, 18, 28, 64, 20, 68, 21, 66, 72, 23, 69, 74, 76, 26,
    63, 29, 80, 30, 83, 31, 81, 87, 33, 84, 89, 91, 36, 50, 39, 95, 43, 97, 41, 46, 99, 101, 44, 98,
    47, 105, 48, 106, 103, 109, 52, 56, 112, 54, 59, 114, 116, 57, 113, 60, 120, 61, 121, 118, 124,
    65, 126, 67, 73, 70, 130, 71, 131, 78, 134, 75, 77, 132, 137, 79, 135, 139, 82, 88, 85, 143, 86,
    144, 93, 147, 90, 92, 145, 150, 94, 148, 96, 152, 141, 155, 100, 102, 107, 158, 104, 110, 160,
    108, 161, 111, 162, 128, 165, 115, 117, 122, 168, 119, 125, 170, 123, 171, 127, 163, 173, 129,
    166, 175, 133, 176, 136, 138, 140, 153, 179, 142, 156, 181, 146, 182, 149, 151, 184, 154, 185,
    157, 159, 183, 187, 164, 188, 167, 169, 177, 172, 174, 190, 178, 180, 191, 186, 189],
  ![3, 6, 9, 0, 12, 15, 1, 18, 20, 2, 23, 22, 4, 29, 30, 5, 33, 32, 7, 39, 8, 41, 11, 10, 47, 43,
    44, 51, 52, 13, 14, 54, 17, 16, 60, 56, 57, 64, 65, 19, 53, 21, 70, 25, 26, 74, 75, 24, 71, 78,
    79, 27, 28, 40, 31, 85, 35, 36, 89, 90, 34, 86, 93, 94, 37, 38, 81, 82, 99, 100, 42, 48, 103,
    104, 45, 46, 107, 108, 49, 50, 95, 66, 67, 114, 115, 55, 61, 118, 119, 58, 59, 122, 123, 62, 63,
    80, 111, 128, 129, 68, 69, 132, 133, 72, 73, 130, 136, 76, 77, 124, 125, 96, 141, 142, 83, 84,
    145, 146, 87, 88, 143, 149, 91, 92, 109, 110, 153, 154, 97, 98, 105, 157, 101, 102, 155, 156,
    106, 160, 151, 163, 164, 112, 113, 120, 167, 116, 117, 165, 166, 121, 170, 138, 172, 126, 127,
    134, 135, 131, 175, 174, 137, 177, 178, 139, 140, 147, 148, 144, 181, 180, 150, 183, 152, 184,
    159, 158, 186, 161, 162, 187, 169, 168, 189, 171, 173, 190, 176, 179, 191, 182, 185, 188],
  ![4, 7, 10, 12, 0, 16, 18, 1, 21, 23, 2, 26, 3, 24, 31, 33, 5, 36, 6, 34, 41, 8, 44, 9, 13, 48,
    11, 49, 46, 47, 54, 14, 57, 15, 19, 61, 17, 62, 59, 60, 67, 20, 55, 71, 22, 72, 28, 29, 25, 27,
    77, 78, 75, 82, 30, 42, 86, 32, 87, 38, 39, 35, 37, 92, 93, 90, 96, 40, 97, 84, 85, 43, 45, 102,
    103, 52, 91, 50, 51, 108, 110, 111, 53, 112, 69, 70, 56, 58, 117, 118, 65, 76, 63, 64, 123, 125,
    66, 68, 127, 128, 115, 126, 73, 74, 133, 135, 121, 122, 79, 138, 80, 81, 83, 140, 141, 100, 139,
    88, 89, 146, 148, 106, 107, 94, 151, 95, 101, 98, 99, 154, 156, 152, 153, 104, 159, 105, 149,
    161, 109, 116, 113, 114, 164, 166, 162, 163, 119, 169, 120, 136, 171, 124, 131, 132, 129, 174,
    130, 172, 176, 134, 177, 137, 144, 145, 142, 180, 143, 178, 182, 147, 183, 150, 157, 185, 155,
    186, 158, 160, 167, 188, 165, 189, 168, 170, 190, 173, 175, 191, 179, 181, 184, 187]
]

private def lup10cg_g : Fin 192 → Fin 4 := ![
  0, 0, 1, 2, 3, 1, 2, 3, 0, 2, 3, 1, 3, 1, 0, 2, 3, 1, 3, 1, 2, 3, 1, 3, 1, 0, 3, 1, 0, 2, 2, 3,
  1, 3, 1, 0, 3, 1, 0, 2, 1, 3, 1, 0, 3, 1, 0, 2, 3, 1, 0, 2, 2, 1, 3, 1, 0, 3, 1, 0, 2, 3, 1, 0, 2,
  2, 0, 3, 1, 0, 2, 3, 1, 0, 2, 2, 1, 0, 2, 2, 1, 0, 3, 1, 0, 2, 3, 1, 0, 2, 2, 1, 0, 2, 2, 1, 3, 1,
  0, 2, 2, 1, 0, 2, 2, 1, 0, 2, 2, 1, 3, 3, 1, 0, 2, 2, 1, 0, 2, 2, 1, 0, 2, 2, 1, 3, 1, 0, 2, 2, 1,
  0, 2, 2, 1, 3, 2, 1, 3, 1, 0, 2, 2, 1, 0, 2, 2, 1, 3, 2, 1, 3, 0, 2, 2, 1, 3, 2, 1, 3, 1, 3, 0, 2,
  2, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 1, 3, 3, 2, 1, 3, 1, 3, 3, 1, 3, 3, 1, 3, 3, 3, 3]

private def lup10cg_par : Fin 192 → Fin 192 := ![
  0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5, 5, 5, 6, 6, 7, 8, 8, 9, 9, 10, 11, 11, 12, 13, 13,
  14, 14, 15, 15, 16, 17, 17, 18, 19, 19, 20, 20, 21, 22, 22, 23, 24, 24, 25, 26, 27, 27, 28, 30,
  30, 31, 32, 32, 33, 34, 34, 35, 36, 37, 37, 38, 40, 40, 41, 42, 42, 43, 44, 45, 45, 46, 48, 49,
  49, 50, 52, 53, 53, 54, 55, 55, 56, 57, 58, 58, 59, 61, 62, 62, 63, 65, 66, 67, 68, 68, 69, 71,
  72, 72, 73, 75, 76, 76, 77, 79, 80, 81, 82, 83, 83, 84, 86, 87, 87, 88, 90, 91, 91, 92, 94, 95,
  96, 97, 97, 98, 100, 101, 101, 102, 104, 105, 106, 108, 109, 111, 112, 112, 113, 115, 116, 116,
  117, 119, 120, 121, 123, 124, 126, 126, 127, 129, 130, 131, 133, 134, 136, 137, 139, 139, 140,
  142, 143, 144, 146, 147, 149, 150, 152, 154, 155, 157, 158, 160, 162, 164, 165, 167, 168, 170,
  172, 173, 175, 178, 179, 181, 184, 187]

private def lup10cg_key (m : lup10fa_Mat) : ℕ :=
  (∑ i : Fin 5, (m i 0).val * 3 ^ i.val) * 3 ^ 5 +
    ∑ i : Fin 5, (m i 1).val * 3 ^ i.val

private theorem lup10cg_E_closed :
    ∀ (i : Fin 4) (k : Fin 192), lup10cg_s i * lup10cg_E k = lup10cg_E (lup10cg_t i k) := by
  decide +kernel

private theorem lup10cg_E_zero : lup10cg_E 0 = 1 := by
  decide +kernel

private theorem lup10cg_E_step : ∀ k : Fin 192, 0 < k.val →
    lup10cg_E k = lup10cg_s (lup10cg_g k) * lup10cg_E (lup10cg_par k) ∧
      (lup10cg_par k).val < k.val := by
  decide +kernel

private theorem lup10cg_E_inj : Function.Injective lup10cg_E :=
  List.nodup_ofFn.mp (CFSG.Decide.nodup_of_bitsetNodup lup10cg_key (by decide +kernel))

private theorem lup10cg_s_sq (i : Fin 4) : lup10cg_s i * lup10cg_s i = 1 := by
  fin_cases i <;> decide +kernel

private theorem lup10cg_card_closure :
    Nat.card ↥(Submonoid.closure (Set.range lup10cg_s)) = 192 := by
  have hsub : (Submonoid.closure (Set.range lup10cg_s) : Set lup10fa_Mat) =
      Set.range lup10cg_E := by
    refine Set.Subset.antisymm ?_ ?_
    · intro m hm
      have hP : ∀ m ∈ Submonoid.closure (Set.range lup10cg_s),
          ∀ k : Fin 192, ∃ j : Fin 192, m * lup10cg_E k = lup10cg_E j := by
        intro m hm
        induction hm using Submonoid.closure_induction with
        | mem x hx =>
            obtain ⟨i, rfl⟩ := hx
            exact fun k => ⟨lup10cg_t i k, lup10cg_E_closed i k⟩
        | one => exact fun k => ⟨k, one_mul _⟩
        | mul x y _ _ ihx ihy =>
            intro k
            obtain ⟨j, hj⟩ := ihy k
            obtain ⟨j', hj'⟩ := ihx j
            exact ⟨j', by rw [mul_assoc, hj, hj']⟩
      obtain ⟨j, hj⟩ := hP m hm 0
      refine ⟨j, ?_⟩
      rw [lup10cg_E_zero, mul_one] at hj
      exact hj.symm
    · rintro _ ⟨k, rfl⟩
      have hmem : ∀ n : ℕ, ∀ k : Fin 192, k.val = n →
          lup10cg_E k ∈ Submonoid.closure (Set.range lup10cg_s) := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro k hk
          rcases Nat.eq_zero_or_pos n with h0 | hpos
          · have hk0 : k = 0 := Fin.ext (by omega)
            rw [hk0, lup10cg_E_zero]
            exact Submonoid.one_mem _
          · obtain ⟨hstep, hlt⟩ := lup10cg_E_step k (by omega)
            rw [hstep]
            exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨lup10cg_g k, rfl⟩)
              (ih (lup10cg_par k).val (by omega) (lup10cg_par k) rfl)
      exact hmem k.val k rfl
  calc Nat.card ↥(Submonoid.closure (Set.range lup10cg_s))
      = Nat.card (Submonoid.closure (Set.range lup10cg_s) : Set lup10fa_Mat) := rfl
    _ = Nat.card (Set.range lup10cg_E) := by rw [hsub]
    _ = Nat.card (Fin 192) := Nat.card_congr (Equiv.ofInjective lup10cg_E lup10cg_E_inj).symm
    _ = 192 := Nat.card_fin 192

private theorem lup10cg_closure_eq_submonoid {H : Type*} [Group H] {S : Set H}
    (hS : ∀ s ∈ S, s * s = 1) :
    (Subgroup.closure S : Set H) = (Submonoid.closure S : Set H) := by
  have hinv : ∀ x ∈ Submonoid.closure S, x⁻¹ ∈ Submonoid.closure S := by
    intro x hx
    induction hx using Submonoid.closure_induction with
    | mem s hs =>
        rw [inv_eq_of_mul_eq_one_right (hS s hs)]
        exact Submonoid.subset_closure hs
    | one => simp
    | mul a b _ _ iha ihb =>
        rw [mul_inv_rev]
        exact Submonoid.mul_mem _ ihb iha
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact Submonoid.subset_closure hs
    | one => exact Submonoid.one_mem _
    | mul a b _ _ iha ihb => exact Submonoid.mul_mem _ iha ihb
    | inv a _ iha => exact hinv a iha
  · exact Submonoid.closure_le.mpr (fun s hs => Subgroup.subset_closure hs)

private theorem lup10cg_gen_index {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (he0 : M.a = e 0) {k : M.ι} (hk : k ≠ M.a) :
    ∃ i : Fin 4, k = e (lup10ab_tau i.castSucc) := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 5, e j = k := ⟨e.symm k, e.apply_symm_apply k⟩
  have hj0 : j ≠ 0 := fun h => hk (by rw [h, he0])
  fin_cases j
  · exact absurd rfl hj0
  · exact ⟨3, congrArg e (by decide)⟩
  · exact ⟨1, congrArg e (by decide)⟩
  · exact ⟨0, congrArg e (by decide)⟩
  · exact ⟨2, congrArg e (by decide)⟩

private theorem lup10cg_tau_ne_zero : ∀ j : Fin 4, lup10ab_tau j.castSucc ≠ 0 := by
  decide +kernel

theorem lup10c_card_automizer {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
    {L H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hbas : M.toLin.Basis) :
    Nat.card (ggAutomizer L Bs) = 192 := by
  classical
  obtain ⟨κ, hκ, hκs, -⟩ := lup10ab_coord M e hecart he0 hbas
  let F : MulAut ↥Bs → ((Fin 5 → ZMod 3) →ₗ[ZMod 3] (Fin 5 → ZMod 3)) := fun ψ =>
    κ.toLinearMap.comp ((ggLin (p := 3) M.model ψ).toLinearMap.comp κ.symm.toLinearMap)
  have hF1 : F 1 = 1 := by
    ext v
    simp [F]
  have hFmul : ∀ ψ ψ' : MulAut ↥Bs, F (ψ * ψ') = F ψ * F ψ' := by
    intro ψ ψ'
    ext v
    simp [F, LinearEquiv.mul_apply]
  let matHom : MulAut ↥Bs →* Matrix (Fin 5) (Fin 5) (ZMod 3) :=
    { toFun := fun ψ => LinearMap.toMatrix' (F ψ)
      map_one' := by rw [hF1, LinearMap.toMatrix'_one]
      map_mul' := fun ψ ψ' => by rw [hFmul, LinearMap.toMatrix'_mul] }
  have hmatHom_inj : Function.Injective matHom := by
    intro ψ ψ' h
    have h1 : F ψ = F ψ' := LinearMap.toMatrix'.injective h
    have h2 : ∀ v : M.V, (ggLin (p := 3) M.model ψ).toLinearMap v =
        (ggLin (p := 3) M.model ψ').toLinearMap v := by
      intro v
      have h3 := LinearMap.congr_fun h1 (κ v)
      simp only [F, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.symm_apply_apply] at h3
      exact κ.injective h3
    exact ggLin_injective (p := 3) M.model
      (LinearEquiv.toLinearMap_injective (LinearMap.ext h2))
  have hgen_mat : ∀ j : Fin 5, matHom (M.simple (e (lup10ab_tau j))) = lup10fa_s j := by
    intro j
    show LinearMap.toMatrix' (F (M.simple (e (lup10ab_tau j)))) = lup10fa_s j
    rw [← LinearMap.toMatrix'_toLin' (lup10fa_s j)]
    congr 1
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply]
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    simpa using hκs j (κ.symm v)
  have hgen_sq : ∀ s ∈ M.simple '' {k : M.ι | k ≠ M.a}, s * s = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨i, rfl⟩ := lup10cg_gen_index M e he0 hk
    apply hmatHom_inj
    rw [map_mul, map_one, hgen_mat i.castSucc]
    exact lup10cg_s_sq i
  have himage : matHom '' (ggAutomizer L Bs : Set (MulAut ↥Bs)) =
      (Submonoid.closure (Set.range lup10cg_s) : Set lup10fa_Mat) := by
    rw [M.automizer_L, lup10cg_closure_eq_submonoid hgen_sq]
    apply Set.Subset.antisymm
    · rintro _ ⟨ψ, hψ, rfl⟩
      induction hψ using Submonoid.closure_induction with
      | mem x hx =>
          obtain ⟨k, hk, rfl⟩ := hx
          obtain ⟨i, rfl⟩ := lup10cg_gen_index M e he0 hk
          rw [hgen_mat i.castSucc]
          exact Submonoid.subset_closure ⟨i, rfl⟩
      | one => rw [map_one]; exact Submonoid.one_mem _
      | mul x y _ _ ihx ihy =>
          rw [map_mul]
          exact Submonoid.mul_mem _ ihx ihy
    · intro m hm
      induction hm using Submonoid.closure_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          refine ⟨M.simple (e (lup10ab_tau i.castSucc)), ?_, ?_⟩
          · apply Submonoid.subset_closure
            exact ⟨e (lup10ab_tau i.castSucc),
              fun h => lup10cg_tau_ne_zero i (e.injective (h.trans he0)), rfl⟩
          · rw [hgen_mat i.castSucc]
            rfl
      | one => exact ⟨1, Submonoid.one_mem _, map_one matHom⟩
      | mul x y _ _ ihx ihy =>
          obtain ⟨ψ, hψ, rfl⟩ := ihx
          obtain ⟨χ, hχ, rfl⟩ := ihy
          exact ⟨ψ * χ, Submonoid.mul_mem _ hψ hχ, map_mul matHom ψ χ⟩
  calc Nat.card (ggAutomizer L Bs)
      = Nat.card (matHom '' (ggAutomizer L Bs : Set (MulAut ↥Bs))) :=
        Nat.card_congr (Equiv.Set.image matHom _ hmatHom_inj)
    _ = Nat.card ((Submonoid.closure (Set.range lup10cg_s) : Submonoid lup10fa_Mat) :
          Set lup10fa_Mat) := by rw [himage]
    _ = 192 := lup10cg_card_closure

theorem lup10c_inf_centralizer {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hSs : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  exact inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hSs.2.2.1 hLx
    (fun S hSL hSp => hSs.2.2.2.2 S hSL hSp)

theorem lup10c_twoLocalRank_le {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis) :
    LargeEvenTwoLocalRank 3 G ≤ 5 := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSs : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  rw [hSs.1.2.1, lup10c_card_Bs M e hbas] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle

theorem lup10c_center_coprime {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (_M : GGQTwoAmbModel 3 Bs x y L H) :
    ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
  intro g hg
  rw [Nat.prime_three.coprime_iff_not_dvd]
  intro h3dvd
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, -, -, -⟩ := hcfg.tableB_facts
  have hstar : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs :=
    hcfg.2.1.2.2.2
  have hSs : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hSs.1.1.2 x hSs.2.1
  have hx1 : x ≠ 1 := hSs.2.2.1
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1
  have hZ3 : 3 ∣ Nat.card ↥(Subgroup.center ↥L) := by
    have hdvd : Nat.card ↥(Subgroup.zpowers g) ∣ Nat.card ↥(Subgroup.center ↥L) :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hg)
    rw [Nat.card_zpowers] at hdvd
    exact h3dvd.trans hdvd
  have hBsP : IsPGroup 3 ↥Bs := isPGroup_of_isElemAbelian hBsE
  let : MulDistribMulAction ↥Bs ↥(Subgroup.center ↥L) :=
    MulDistribMulAction.compHom (↥(Subgroup.center ↥L))
      ((MulAut.characteristic (Subgroup.center ↥L)).comp (ggGamma L hBsN))
  have hmod := hBsP.card_modEq_card_fixedPoints (↥(Subgroup.center ↥L))
  have h3fix : 3 ∣ Nat.card ↥(fixedPointSubgroup ↥Bs ↥(Subgroup.center ↥L)) := by
    have h0 : Nat.card ↥(Subgroup.center ↥L) ≡ 0 [MOD 3] :=
      Nat.modEq_zero_iff_dvd.mpr hZ3
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h0)
  obtain ⟨z, hz⟩ : ∃ z : ↥(fixedPointSubgroup ↥Bs ↥(Subgroup.center ↥L)), orderOf z = 3 :=
    exists_prime_orderOf_dvd_card' 3 h3fix
  have hzfix : ∀ b : ↥Bs, b • (z : ↥(Subgroup.center ↥L)) = (z : ↥(Subgroup.center ↥L)) :=
    fun b => (MulAction.mem_fixedPoints).mp z.2 b
  have hsmul : ∀ (b : ↥Bs) (w : ↥(Subgroup.center ↥L)),
      (((b • w : ↥(Subgroup.center ↥L)) : ↥L) : G) =
        (b : G) * ((w : ↥L) : G) * (b : G)⁻¹ := by
    intro b w
    rw [show ((b • w : ↥(Subgroup.center ↥L)) : ↥L) = (ggGamma L hBsN b) (w : ↥L) from rfl,
      ggGamma_coe]
  let u : ↥L := ((z : ↥(Subgroup.center ↥L)) : ↥L)
  have hucenter : u ∈ Subgroup.center ↥L := (z : ↥(Subgroup.center ↥L)).2
  have hzpow : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hu3 : (u : G) ^ 3 = 1 := by
    have h2 := congrArg (fun t : ↥(fixedPointSubgroup ↥Bs ↥(Subgroup.center ↥L)) =>
      ((t : ↥(Subgroup.center ↥L)) : G)) hzpow
    simpa [u, Subgroup.coe_pow] using h2
  have hu1 : (u : G) ≠ 1 := by
    intro h
    have h2 : (z : ↥(Subgroup.center ↥L)) = 1 := Subtype.ext (by simpa [u] using h)
    have h3 : z = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have huord : orderOf (u : G) = 3 := orderOf_eq_prime hu3 hu1
  have hzC : (u : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h := hzfix (⟨b, hb⟩ : ↥Bs)
    have h1 : ((((⟨b, hb⟩ : ↥Bs) • (z : ↥(Subgroup.center ↥L)) : ↥(Subgroup.center ↥L)) : ↥L) : G) =
        (((z : ↥(Subgroup.center ↥L)) : ↥L) : G) :=
      congrArg (fun t : ↥(Subgroup.center ↥L) => ((t : ↥L) : G)) h
    rw [hsmul] at h1
    have h' : b * (u : G) * b⁻¹ = (u : G) := h1
    calc b * (u : G) = (b * (u : G) * b⁻¹) * b := by group
      _ = (u : G) * b := by rw [h']
  have hzBs : (u : G) ∈ Bs := hstar _ hzC hu3
  have hzcentL : (u : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := Subgroup.mem_center_iff.mp hucenter ⟨l, hl⟩
    simpa using congrArg Subtype.val h
  have hzx : (u : G) ∈ Subgroup.zpowers x := by
    rw [← lup10c_inf_centralizer hS]
    exact ⟨hzBs, hzcentL⟩
  have hzgen : Subgroup.zpowers (u : G) = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzx) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, huord, hxord]
  have hxLmem : x ∈ L := by
    have hle : Subgroup.zpowers (u : G) ≤ L := Subgroup.zpowers_le.mpr u.2
    rw [hzgen] at hle
    exact Subgroup.zpowers_le.mp hle
  exact hxL hxLmem

theorem lup10c_card_range_ggGamma {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (_hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggGamma L hBsN).range = 3 ^ 4 := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hSs : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of Nat.prime_three hBs hxB hSs.2.2.1 hLx
    (fun S hSL hSp => hSs.2.2.2.2 S hSL hSp) hBsN
  rw [lup10c_card_Bs M e hbas,
    show (3 : ℕ) ^ 5 = 3 ^ 4 * 3 by norm_num] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : (0:ℕ) < 3) hmul

theorem lup10c_not_torusLift {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {H : Subgroup G}
    (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis)
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {r : ℕ} (hr : 5 ≤ r) :
    ¬ GGTorusLift 3 r R := by
  intro hlift
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have hSs : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hperf : commutator ↥L = ⊤ := hS.2.1.1
  have hx3 : x ^ 3 = 1 := hSs.1.1.2 x hSs.2.1
  have h5 := succ_le_twoLocalRank_of_torusLift Nat.prime_three hLx hx3 hSs.2.2.1 hperf θ hlift
  have hle := lup10c_twoLocalRank_le hS M e hbas
  omega

theorem lup10c_torusAutCard {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) {y : G}
    {H : Subgroup G} (M : GGQTwoAmbModel 3 Bs x y L H) (e : Fin 5 ≃ M.ι) (hbas : M.toLin.Basis)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {r N : ℕ} (hSC : GGTorusAutCardSC 3 R I r N) :
    r ≤ 4 ∧ (I ⊆ LargeEvenInnSet R → Nat.card (ggAutomizer L Bs) = N) := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨-, hBsE, -, hLx, -⟩ := hcfg.tableB_facts
  have hstar : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs :=
    hcfg.2.1.2.2.2
  have hperf : commutator ↥L = ⊤ := hS.2.1.1
  have hcardγ : Nat.card (ggGamma L hBsN).range = 3 ^ 4 :=
    lup10c_card_range_ggGamma hS hxL M e hbas hBsN
  have hBp : ∀ b : ↥Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBsE.2 b b.2)
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.Open.IsElemAbelian.comm hBsE a.2 b.2)
  have hA : IsElemAbelian 3 (ggGamma L hBsN).range := isElemAbelian_range hBc hBp _
  have hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ I, ∀ l : ↥L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggLAut_mem_of_induces L θ hBsN hBs3 b.2,
      fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hself : GGTorusSelfCent 3 (ggGamma L hBsN).range := ggTorusSelfCent_ggGamma hBsN hstar
  obtain ⟨hpow, haut⟩ := hSC ↥L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperf (ggGamma L hBsN).range hA hAI
    (by rw [hcardγ]; norm_num) hself
  refine ⟨?_, fun hIinn => ?_⟩
  · rw [hcardγ] at hpow
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  · have hInn : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ :=
      r4m_inn_of_subset_inn θ hperf hBsN hIinn hBs3
    have hZ' : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) :=
      lup10c_center_coprime hS hxL M
    obtain ⟨hsup, -, -, -, hcard47⟩ := ggLemma47c hBsE hstar hZ' hInn
    have hAb : IsElemAbelian 3 (Bs ⊓ L) := TableB.isElemAbelian_mono hBsE inf_le_left
    have hcardinn := ggAutomizer_card_eq_inn (X := L) (BX := Bs ⊓ L) inf_le_right hAb hZ'
    have hkey : ∀ (k : G) (hkB : k ∈ Bs) (hkL : k ∈ L),
        ggGamma L hBsN ⟨k, hkB⟩ = MulAut.conj (⟨k, hkL⟩ : ↥L) := by
      intro k hkB hkL
      ext l
      simp [MulAut.conj_apply, ggGamma_coe]
    have hkill : Subgroup.map (ggGamma L hBsN)
        ((Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_bot]
      exact (ggGamma_eq_one_iff L hBsN (c : ↥Bs)).mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).2
    have hsup' : (Bs ⊓ L).subgroupOf Bs ⊔
        (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs = (⊤ : Subgroup ↥Bs) := by
      rw [← Subgroup.subgroupOf_sup inf_le_left inf_le_left, ← hsup,
        Subgroup.subgroupOf_self]
    have himg : Subgroup.map (ggGamma L hBsN) ((Bs ⊓ L).subgroupOf Bs) =
        Subgroup.map (MulAut.conj : ↥L →* MulAut ↥L) ((Bs ⊓ L).subgroupOf L) := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨k, hk, rfl⟩
        obtain ⟨hkB, hkL⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_map.mpr ⟨⟨(k : G), hkL⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hkB, hkL⟩),
          (hkey (k : G) hkB hkL).symm⟩
      · rintro _ ⟨k, hk, rfl⟩
        obtain ⟨hkB, hkL⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_map.mpr ⟨⟨(k : G), hkB⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hkB, hkL⟩),
          hkey (k : G) hkB hkL⟩
    have hmap : Subgroup.map (MulAut.conj : ↥L →* MulAut ↥L) ((Bs ⊓ L).subgroupOf L) =
        (ggGamma L hBsN).range := by
      have h1 : Subgroup.map (ggGamma L hBsN) (⊤ : Subgroup ↥Bs) =
          Subgroup.map (ggGamma L hBsN) ((Bs ⊓ L).subgroupOf Bs) := by
        conv_lhs => rw [← hsup']
        rw [Subgroup.map_sup, hkill, sup_bot_eq]
      rw [MonoidHom.range_eq_map, h1, himg]
    rw [hcard47, hcardinn, hmap]
    exact haut

end CFSG.StandardType

end
