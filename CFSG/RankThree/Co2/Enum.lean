module

public import CFSG.RankThree.Co2.Rows

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

@[expose, instance_reducible] def crMulAction : MulAction Cr (Module.End (ZMod 2) (Wv v0)) where
  smul g T := wAct v0 ((g : Kstab v0)⁻¹) * T
  one_smul T := by
    change wAct v0 ((1 : Kstab v0)⁻¹) * T = T
    rw [inv_one, wAct_one, one_mul]
  mul_smul g h T := by
    change wAct v0 ((g : Kstab v0) * h)⁻¹ * T =
      wAct v0 (g : Kstab v0)⁻¹ * (wAct v0 (h : Kstab v0)⁻¹ * T)
    rw [mul_inv_rev, wAct_mul, mul_assoc]

attribute [local instance] crMulAction

@[expose] def gensW (ws : Array (List ℕ)) (k : ℕ) : Cr := wordCr ws[k]!

@[expose] def subW (ws : Array (List ℕ)) : Subgroup Cr :=
  Subgroup.closure (gensW ws '' {k | k < ws.size})

theorem gensW_mem_subW {ws : Array (List ℕ)} {k : ℕ} (hk : k < ws.size) :
    gensW ws k ∈ subW ws :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

end CFSG.RankThree.Co2
