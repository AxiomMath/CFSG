module

public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

structure WreathData (G : Type) [Group G] (D : Set G) (M : Subgroup G) where
  r : ℕ
  two_le : 2 ≤ r
  S : Fin r → Subgroup G
  simple : ∀ i, IsSimpleGroup (S i)
  not_comm : ∀ i, ∃ a b : S i, a * b ≠ b * a
  le : ∀ i, S i ≤ M
  e : ((i : Fin r) → S i) ≃* M
  e_single : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : G) = x i
  π : G →* Equiv.Perm (Fin r)
  conj : ∀ (g : G) (i : Fin r), (S i).map (MulAut.conj g).toMonoidHom = S (π g i)
  transitive : ∀ i j : Fin r, ∃ g : G, π g i = j
  swap : ∀ u ∈ D, ∃ i j : Fin r, i ≠ j ∧ π u = Equiv.swap i j ∧
    ∀ k : Fin r, k ≠ i → k ≠ j → ∀ x ∈ S k, Commute u x

end CFSG.Timmesfeld.Bridge.Asc72
