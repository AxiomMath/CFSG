
module

public import CFSG.Sporadic.Schreier.J4SGLBase1

public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem ρGL_injective :
    Function.Injective ρGL := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have h1 : ρK k = 1 := by
    ext n
    obtain ⟨a, rfl⟩ := eN.surjective n
    have e := etaV_ρGL k (Multiplicative.toAdd a)
    rw [hk, Units.val_one, Matrix.one_mulVec] at e
    rw [MulAut.one_apply, ρK_apply, eN_apply, ← e]
  exact ρK_injective (h1.trans (map_one ρK).symm)

end CFSG.Sporadic.J4Schreier
