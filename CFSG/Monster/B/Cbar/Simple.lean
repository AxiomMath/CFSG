
module

public import CFSG.Monster.B.Cbar.SimpleBase
import all CFSG.Monster.B.Cbar.SimpleBase

public import CFSG.Monster.B.Cbar.SylowTwo
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Co2.IrredAll

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short

theorem Kv_rStar_facts :
    IsSimpleGroup (Kstab (phi0 (coordOf rStar))) ∧
    Module.finrank (ZMod 2) (Wv (phi0 (coordOf rStar))) = 22 ∧
    ∀ U : Submodule (ZMod 2) (Wv (phi0 (coordOf rStar))),
      (∀ (k : Kstab (phi0 (coordOf rStar))) (w : Wv (phi0 (coordOf rStar))), w ∈ U →
        wAct (phi0 (coordOf rStar)) k w ∈ U) → U = ⊥ ∨ U = ⊤ := by
  rw [phi0_coordOf_rStar]
  obtain ⟨-, h22, hirr⟩ := Co2.native_short_stabilizer_irreducible vMinus_zero_one_mem
  exact ⟨(Co2.native_short_stabilizer_simple.1 _ vMinus_zero_one_mem).1, h22, hirr⟩

theorem short_centralizer_generated_quotient_simple :
    Finite Cbar ∧ Nontrivial Cbar ∧ IsSimpleGroup Cbar ∧
      ∃ m : ℕ, Odd m ∧ Nat.card Cbar = 2 ^ 41 * m := by
  obtain ⟨hsimpleK, h22, hirr⟩ := Kv_rStar_facts
  have := hsimpleK
  have hW : Nontrivial (Wv (phi0 (coordOf rStar))) :=
    Module.nontrivial_of_finrank_pos (by rw [h22]; norm_num)
  obtain ⟨h1, h2⟩ := simple_of_local centralizer_xbar map_center_Ebar jbarToKv_surjective hW hirr
  exact ⟨inferInstance, h1, h2, short_centralizer_quotient_sylow_two.2.1⟩

end CFSG.Monster.B
