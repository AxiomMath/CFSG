module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

inductive QTwoRowKind where
  | prime | suFull | suInner | psuInner | psuFull
  deriving DecidableEq

structure QTwoRowData (k : QTwoRowKind) (m d c : ℕ) (Bs L : Subgroup G) (x : G) : Prop where
  elemAb : IsElemAbelian 3 Bs
  mem : x ∈ Bs
  card : Nat.card Bs = 3 ^ d
  weyl : GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) (ggAutomizer L Bs)
  fixes : ∀ a ∈ ggAutomizer L Bs, a ⟨x, mem⟩ = ⟨x, mem⟩
  fixed : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x
  comm : Nat.card (ggCommSpace Bs (ggAutomizer L Bs)) = 3 ^ c
  dvd : k ≠ .prime → 3 ∣ m
  prime_ndvd : k = .prime → ¬ 3 ∣ m
  dc : (k = .prime → d = m ∧ c = m - 1) ∧ (k = .suFull → d = m ∧ c = m - 1) ∧
       (k = .suInner → d = m - 1 ∧ c = m - 1) ∧
       (k = .psuInner → d = m - 1 ∧ c = m - 2) ∧ (k = .psuFull → d = m ∧ c = m - 2)

end CFSG.StandardType.QTwo

end
