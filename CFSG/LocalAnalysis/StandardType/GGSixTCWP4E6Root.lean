module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def e6RootList : List (List ℤ) := [
  [-1, -2, -2, -3, -2, -1],
  [-1, -1, -2, -3, -2, -1],
  [-1, -1, -2, -2, -2, -1],
  [-1, -1, -2, -2, -1, -1],
  [-1, -1, -2, -2, -1, 0],
  [-1, -1, -1, -2, -2, -1],
  [-1, -1, -1, -2, -1, -1],
  [-1, -1, -1, -2, -1, 0],
  [-1, -1, -1, -1, -1, -1],
  [-1, -1, -1, -1, -1, 0],
  [-1, -1, -1, -1, 0, 0],
  [-1, 0, -1, -1, -1, -1],
  [-1, 0, -1, -1, -1, 0],
  [-1, 0, -1, -1, 0, 0],
  [-1, 0, -1, 0, 0, 0],
  [-1, 0, 0, 0, 0, 0],
  [0, -1, -1, -2, -2, -1],
  [0, -1, -1, -2, -1, -1],
  [0, -1, -1, -2, -1, 0],
  [0, -1, -1, -1, -1, -1],
  [0, -1, -1, -1, -1, 0],
  [0, -1, -1, -1, 0, 0],
  [0, -1, 0, -1, -1, -1],
  [0, -1, 0, -1, -1, 0],
  [0, -1, 0, -1, 0, 0],
  [0, -1, 0, 0, 0, 0],
  [0, 0, -1, -1, -1, -1],
  [0, 0, -1, -1, -1, 0],
  [0, 0, -1, -1, 0, 0],
  [0, 0, -1, 0, 0, 0],
  [0, 0, 0, -1, -1, -1],
  [0, 0, 0, -1, -1, 0],
  [0, 0, 0, -1, 0, 0],
  [0, 0, 0, 0, -1, -1],
  [0, 0, 0, 0, -1, 0],
  [0, 0, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 1, 1],
  [0, 0, 0, 1, 0, 0],
  [0, 0, 0, 1, 1, 0],
  [0, 0, 0, 1, 1, 1],
  [0, 0, 1, 0, 0, 0],
  [0, 0, 1, 1, 0, 0],
  [0, 0, 1, 1, 1, 0],
  [0, 0, 1, 1, 1, 1],
  [0, 1, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 0],
  [0, 1, 0, 1, 1, 0],
  [0, 1, 0, 1, 1, 1],
  [0, 1, 1, 1, 0, 0],
  [0, 1, 1, 1, 1, 0],
  [0, 1, 1, 1, 1, 1],
  [0, 1, 1, 2, 1, 0],
  [0, 1, 1, 2, 1, 1],
  [0, 1, 1, 2, 2, 1],
  [1, 0, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 0],
  [1, 0, 1, 1, 0, 0],
  [1, 0, 1, 1, 1, 0],
  [1, 0, 1, 1, 1, 1],
  [1, 1, 1, 1, 0, 0],
  [1, 1, 1, 1, 1, 0],
  [1, 1, 1, 1, 1, 1],
  [1, 1, 1, 2, 1, 0],
  [1, 1, 1, 2, 1, 1],
  [1, 1, 1, 2, 2, 1],
  [1, 1, 2, 2, 1, 0],
  [1, 1, 2, 2, 1, 1],
  [1, 1, 2, 2, 2, 1],
  [1, 1, 2, 3, 2, 1],
  [1, 2, 2, 3, 2, 1]]

@[expose] def e6ip : List ℤ → List ℤ → ℤ
  | [x0, x1, x2, x3, x4, x5], [y0, y1, y2, y3, y4, y5] =>
    x0 * (2 * y0 - y2) + x1 * (2 * y1 - y3) + x2 * (2 * y2 - y0 - y3) +
      x3 * (2 * y3 - y1 - y2 - y4) + x4 * (2 * y4 - y3 - y5) + x5 * (2 * y5 - y4)
  | _, _ => 0

theorem rootFinset_E6_image_eq : (rootFinset .E6).image List.ofFn = e6RootList.toFinset := by
  decide +kernel

theorem mem_e6RootList_of_isRoot {γ : Fin Tag.E6.rank → ℤ}
    (h : IsRoot .E6 γ) : List.ofFn γ ∈ e6RootList := by
  have h1 : γ ∈ rootFinset .E6 := mem_rootFinset.2 h
  have h2 : List.ofFn γ ∈ (rootFinset .E6).image List.ofFn := Finset.mem_image_of_mem _ h1
  rw [rootFinset_E6_image_eq] at h2
  exact List.mem_toFinset.1 h2

theorem symmetrizedCartan_E6_apply (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan i j = Tag.cartanE 6 i j :=
  congrFun (congrFun (Matrix.one_mul (Tag.cartanE 6)) i) j

theorem iform_eq_e6ip (γ δ : Fin Tag.E6.rank → ℤ) :
    iform γ δ = e6ip (List.ofFn γ) (List.ofFn δ) := by
  have h : iform γ δ = ∑ i : Fin 6, ∑ j : Fin 6, γ i * Tag.cartanE 6 i j * δ j := by
    unfold iform
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [symmetrizedCartan_E6_apply]
  have e : List.ofFn γ =
      [γ (0 : Fin 6), γ (1 : Fin 6), γ (2 : Fin 6), γ (3 : Fin 6), γ (4 : Fin 6), γ (5 : Fin 6)] :=
    rfl
  have e' : List.ofFn δ =
      [δ (0 : Fin 6), δ (1 : Fin 6), δ (2 : Fin 6), δ (3 : Fin 6), δ (4 : Fin 6), δ (5 : Fin 6)] :=
    rfl
  rw [h, e, e']
  simp [Fin.sum_univ_succ, e6ip, Tag.cartanE]
  ring

@[expose] def tcA2Set (α β : Fin Tag.E6.rank → ℤ) : Set (Fin Tag.E6.rank → ℤ) :=
  {α, β, α + β, -α, -β, -(α + β)}

end CFSG.StandardType.TableCRes

end
