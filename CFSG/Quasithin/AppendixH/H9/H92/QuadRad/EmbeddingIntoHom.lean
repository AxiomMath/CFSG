module

public import CFSG.Quasithin.AppendixH.H9.H92.QuadRad.FixedSpace
public import CFSG.Quasithin.AppendixH.H9.H92.RadHom

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

theorem sub_one_mem_homMat {n : ℕ} {E : Subgroup (GL (Fin n) (ZMod 2))}
    {g : GL (Fin n) (ZMod 2)} (hg : g ∈ E) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 ∈
      homMat n (matMoveSpace n E) (matFixSpace n E) :=
  ⟨fun x => sub_one_mulVec_mem_matMoveSpace hg x,
    fun _ hu => sub_one_mulVec_eq_zero_of_mem_matFixSpace hg hu⟩

theorem natCard_le_two_pow_finrank_fix_move (n : ℕ) (E : Subgroup (GL (Fin n) (ZMod 2))) :
    Nat.card E ≤ 2 ^ ((n - Module.finrank (ZMod 2) (matFixSpace n E)) *
      Module.finrank (ZMod 2) (matMoveSpace n E)) := by
  let f : E → homMat n (matMoveSpace n E) (matFixSpace n E) :=
    fun g => ⟨((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1,
      sub_one_mem_homMat g.2⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h1 : ((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 =
        ((g' : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 :=
      congrArg Subtype.val h
    exact Subtype.ext (Units.ext (sub_left_inj.mp h1))
  calc Nat.card E ≤ Nat.card (homMat n (matMoveSpace n E) (matFixSpace n E)) :=
        Nat.card_le_card_of_injective f hf
    _ = 2 ^ ((n - Module.finrank (ZMod 2) (matFixSpace n E)) *
          Module.finrank (ZMod 2) (matMoveSpace n E)) := by
        have hfin : Module.Finite (ZMod 2) (homMat n (matMoveSpace n E) (matFixSpace n E)) :=
          inferInstance
        have h : Nat.card (homMat n (matMoveSpace n E) (matFixSpace n E)) =
            Nat.card (ZMod 2) ^
              Module.finrank (ZMod 2) (homMat n (matMoveSpace n E) (matFixSpace n E)) :=
          @Module.natCard_eq_pow_finrank (ZMod 2) (homMat n (matMoveSpace n E) (matFixSpace n E))
            _ (Submodule.addCommGroup _) (Submodule.module _) hfin
        rw [h, Nat.card_zmod, finrank_homMat]

end CFSG.ASVolI.ChH
