module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.MinimalInvariantCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerZpowers

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- The source-facing Fact 1.1(i) step: a minimal `H`-invariant odd-order
subgroup on which an involution `t ∈ Z(H)` acts nontrivially equals its
commutator with `t`. -/
public theorem commutator_zpowers_eq_self_of_minimal_invariant
    {G : Type u} [Group G] [Finite G]
    (H P : Subgroup G) {t : G}
    (ht : IsInvolution t) (htH : t ∈ H)
    (hHt : H ≤ Subgroup.centralizer ({t} : Set G))
    (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hPodd : Nat.Coprime 2 (Nat.card P))
    (hnontriv : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥)
    (hmin : ∀ R : Subgroup G, R ≤ P →
      H ≤ Subgroup.normalizer (R : Set G) →
      ⁅R, Subgroup.zpowers t⁆ ≠ ⊥ → P ≤ R) :
    ⁅P, Subgroup.zpowers t⁆ = P := by
  have hHQ : H ≤ Subgroup.normalizer
      ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    hHt.trans (centralizer_singleton_le_normalizer_zpowers t)
  have hQH : Subgroup.zpowers t ≤ H := Subgroup.zpowers_le.mpr htH
  have hQP : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) :=
    hQH.trans hHP
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ht.2) ht.1
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card P) := by
    simpa [Nat.card_zpowers, htorder] using hPodd
  exact commutator_eq_self_of_minimal_invariant_coprime
    H P (Subgroup.zpowers t) hHP hHQ hQP hcop hnontriv hmin

end CFSG.GorensteinWalter
