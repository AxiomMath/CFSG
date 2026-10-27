module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem mul_fix_right (F : FanTree Γ G) (ℓ : Line Γ) {u w : G} {q : ℤ} (hu2 : u * u = 1)
    (hw2 : w * w = 1) (hu0 : u • ℓ.vert (q - 1) = ℓ.vert (q - 1)) (hu1 : u • ℓ.vert q = ℓ.vert q)
    (hu : u • ℓ.vert (q + 1) ≠ ℓ.vert (q + 1)) (hw0 : w • ℓ.vert (q - 1) = ℓ.vert (q - 1))
    (hw1 : w • ℓ.vert q = ℓ.vert q) (hw : w • ℓ.vert (q + 1) ≠ ℓ.vert (q + 1)) :
    (u * w) • ℓ.vert (q + 1) = ℓ.vert (q + 1) := by
  have h := F.mul_mem_nbrStab_of_sq_eq_one (ℓ.adj_pred q) (z := u) (z' := w)
    ⟨MulAction.mem_stabilizer_iff.2 hu1, MulAction.mem_stabilizer_iff.2 hu0⟩
    ⟨MulAction.mem_stabilizer_iff.2 hw1, MulAction.mem_stabilizer_iff.2 hw0⟩ hu2 hw2
    (fun hn => hu (mem_nbrStab.1 hn _ (ℓ.adj q))) (fun hn => hw (mem_nbrStab.1 hn _ (ℓ.adj q)))
  exact mem_nbrStab.1 h _ (ℓ.adj q)

theorem mul_fix_left (F : FanTree Γ G) (ℓ : Line Γ) {u w : G} {p : ℤ} (hu2 : u * u = 1)
    (hw2 : w * w = 1) (hu0 : u • ℓ.vert (p + 1) = ℓ.vert (p + 1)) (hu1 : u • ℓ.vert p = ℓ.vert p)
    (hu : u • ℓ.vert (p - 1) ≠ ℓ.vert (p - 1)) (hw0 : w • ℓ.vert (p + 1) = ℓ.vert (p + 1))
    (hw1 : w • ℓ.vert p = ℓ.vert p) (hw : w • ℓ.vert (p - 1) ≠ ℓ.vert (p - 1)) :
    (u * w) • ℓ.vert (p - 1) = ℓ.vert (p - 1) := by
  have h := F.mul_mem_nbrStab_of_sq_eq_one (ℓ.adj p) (z := u) (z' := w)
    ⟨MulAction.mem_stabilizer_iff.2 hu1, MulAction.mem_stabilizer_iff.2 hu0⟩
    ⟨MulAction.mem_stabilizer_iff.2 hw1, MulAction.mem_stabilizer_iff.2 hw0⟩ hu2 hw2
    (fun hn => hu (mem_nbrStab.1 hn _ (ℓ.adj_pred p)))
    (fun hn => hw (mem_nbrStab.1 hn _ (ℓ.adj_pred p)))
  exact mem_nbrStab.1 h _ (ℓ.adj_pred p)

end P514

end CFSG.Quasithin.Fan86
