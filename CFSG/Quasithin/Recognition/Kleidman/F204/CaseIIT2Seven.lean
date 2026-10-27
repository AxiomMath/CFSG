module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.Quasithin.EmptyFaithful.SzF53BasA
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Transv

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom
open CFSG.QuasithinUnique.A5.Delta5
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem dist_path_le {H M : Subgroup G} (p : ℕ → Geo H M) {n : ℕ}
    (hadj : ∀ k, k < n → (graph _ H M).Adj (p k) (p (k + 1))) :
    ∀ i j, i + j ≤ n → dist (p i) (p (i + j)) ≤ j := by
  intro i j
  induction j with
  | zero => intro _; simp [CosetGeom.dist_self]
  | succ j ih =>
    intro h
    have h1 := ih (by omega)
    have h2 : dist (p (i + j)) (p (i + j + 1)) = 1 :=
      CosetGeom.dist_eq_one_iff_adj.mpr (hadj (i + j) (by omega))
    have h3 := CosetGeom.dist_triangle (G₁ := H) (G₂ := M) rfl (p i) (p (i + j)) (p (i + j + 1))
    show dist (p i) (p (i + j + 1)) ≤ j + 1
    omega

end CFSG.Quasithin.Kleidman.F204
