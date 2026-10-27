module

public import CFSG.RankThree.PartOne.S11d.FieldCase
public import CFSG.RankThree.PartOne.S12.Transfer

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.Blueprint

@[expose] def FieldFusionData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Sec109.Config p A c L B n → ∀ (b : G) (S K : Subgroup G), Sec109.Witness A c B b S →
      K ∈ sectionTenAt p (sectionTenZeroStar p A) b → S ≤ K →
      EvenLieType (K ⧸ Subgroup.center K) → ¬ p ∣ Nat.card (Subgroup.center K) →
      ∀ a d : G, a ∈ A → d ∈ A → d ≠ 1 →
        A = zpowers a ⊔ zpowers b ⊔ zpowers d → zpowers d = A ⊓ K → InducesFieldAut p a K →
        c ∉ zpowers b ⊔ zpowers d → InducesFieldAut p c K →
        ∃ P Q : Subgroup G, IsSylowOf p P ⊤ ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧
          (∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P) ∧ c ∈ P ∧ c ∉ Q ∧
          ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q

theorem fieldCaseTail_of_fusion (h : FieldFusionData) : FieldCaseTail := by
  intro G _ _ p A c L B n cfg b S K hW hK hSK hEven hZ a d haA hdA hd1 hAeq hdK hfa hc hcind
  obtain ⟨P, Q, hP, hQP, hQn, hab, hcP, hcQ, hfus⟩ :=
    h G p A c L B n cfg b S K hW hK hSK hEven hZ a d haA hdA hd1 hAeq hdK hfa hc hcind
  have hsimple : IsSimpleGroup G := cfg.setup.1
  have : Fact p.Prime := ⟨cfg.prime⟩
  have hcpow : c ^ p = 1 := cfg.pow_p_eq_one cfg.c_mem
  have hcp : orderOf c = p := orderOf_eq_prime hcpow cfg.c_ne_one
  exact false_of_fusion_simple cfg.setup.2.1 hP hQP hQn hab hcP hcp hcQ hfus

end CFSG.RankThree.PartOne.TAIL
