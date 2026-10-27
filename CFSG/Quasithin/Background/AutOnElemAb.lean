module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.AutOn

open CFSG.Open
open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem isElemAbelian2_autOn {A W : Subgroup G} [IsMulCommutative ↥W] (hA : IsElemAbelian 2 A) :
    IsElemAbelian2 (autOn A W) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have h := congrArg (Subtype.val : ↥A → G)
      (hA.1.is_comm.comm (⟨(x : G), hx⟩ : ↥A) ⟨(y : G), hy⟩)
    exact Subtype.ext h
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hA.2 (x : G) hx)
    rw [this, map_one]

end CFSG.Quasithin.AutOn
