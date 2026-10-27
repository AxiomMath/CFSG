module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCoverMat
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTablePerm
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.StandardType.SporadicShape

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem sporKRest_smul_eq_tablePerm {G : Type} [Group G] {n : ℕ} [MulAction G (Fin n)] {a : G}
    {Ta : Table} (ha : Rep n Ta a) (hTa : PermCover.tablePermOK n Ta = true) (i : Fin n) :
    a • i = PermCover.tablePerm n Ta i := by
  apply Fin.ext
  rw [PermCover.tablePerm_apply hTa i, ha i.1 i.2, idx_of_lt a i.2]

theorem sporKRest_cover_of_tableMat {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (hfaith : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) (a b : G) (Ta Tb : Table)
    (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card G).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkMat (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb) sylowOrder d =
      true) : SporKRestCover p G := by
  exact sporKRest_cover_of_actionMat hfaith a b (PermCover.tablePerm n Ta)
    (PermCover.tablePerm n Tb) (sporKRest_smul_eq_tablePerm ha hTa)
    (sporKRest_smul_eq_tablePerm hb hTb) hab hp sylowOrder hord d hcheck

theorem sporKRest_cover_of_tablePowMat {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (hfaith : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) (a b : G) (Ta Tb : Table)
    (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card G).factorization p) (d : PermCover.Data)
    (hcheck : PermCover.checkPowMat p (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb)
      sylowOrder d = true) : SporKRestCover p G := by
  exact sporKRest_cover_of_actionPowMat hfaith a b (PermCover.tablePerm n Ta)
    (PermCover.tablePerm n Tb) (sporKRest_smul_eq_tablePerm ha hTa)
    (sporKRest_smul_eq_tablePerm hb hTb) hab hp sylowOrder hord d hcheck

theorem sporKRest_cover_of_tableEMat {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (hfaith : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) (a b : G) (Ta Tb : Table)
    (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (sylowOrder : ℕ)
    (hord : sylowOrder = p ^ (Nat.card G).factorization p) (d : PermCover.DataE)
    (hcheck : PermCover.checkEMat p (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb)
      sylowOrder d = true) : SporKRestCover p G := by
  exact sporKRest_cover_of_actionEMat hfaith a b (PermCover.tablePerm n Ta)
    (PermCover.tablePerm n Tb) (sporKRest_smul_eq_tablePerm ha hTa)
    (sporKRest_smul_eq_tablePerm hb hTb) hab hp sylowOrder hord d hcheck

end CFSG.StandardType.SporadicShape
