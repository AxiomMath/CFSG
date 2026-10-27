module

public import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.S12.Skeleton
public import CFSG.RankThree.PartOne.S12.Transfer

public section

namespace CFSG.RankThree.PartOne

@[expose] def Node12Fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → torusWeylHasPCore p E →
    ∃ P Q : Subgroup G, IsSylowOf p P ⊤ ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧
      (∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P) ∧ c ∈ P ∧ c ∉ Q ∧
      ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q

theorem node129_of_fusion (h : Node12Fusion) : Node129 := by
  intro G _ _ p A c L E hE hT hcore
  have : IsSimpleGroup G := hE.setup.1
  have : Fact p.Prime := ⟨hE.prime⟩
  have := hE.A_elem
  obtain ⟨P, Q, hP, hQP, hQn, hab, hcP, hcQ, hfus⟩ := h G p A c L E hE hT hcore
  have hcpow : c ^ p = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c hE.c_mem
  have hcp : orderOf c = p := orderOf_eq_prime hcpow hE.c_ne_one
  exact false_of_fusion_simple hE.setup.2.1 hP hQP hQn hab hcP hcp hcQ hfus

end CFSG.RankThree.PartOne
