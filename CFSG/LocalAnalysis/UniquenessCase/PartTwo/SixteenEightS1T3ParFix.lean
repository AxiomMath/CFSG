module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16t3_exists_conj_stabilizer {G S : Type*} [Group G] [MulAction G S] {E X : Subgroup G}
    (s₀ : S) (hX : IsPGroup 2 ↥X) (hodd : ¬2 ∣ Nat.card (MulAction.orbit ↥E s₀))
    (hinv : ∀ x ∈ X, ∀ t ∈ MulAction.orbit ↥E s₀, x • t ∈ MulAction.orbit ↥E s₀) :
    ∃ g ∈ E, ∀ x ∈ X, g⁻¹ * x * g ∈ MulAction.stabilizer G s₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAction.orbit ↥E s₀) :=
    Nat.finite_of_card_ne_zero fun h => hodd (h ▸ dvd_zero 2)
  obtain ⟨t, ⟨e, rfl⟩, hfix⟩ := s16c13bcA_exists_fixed_of_odd (Γ := ↥X) (p := 2) hX
    (MulAction.orbit ↥E s₀) (fun x t ht => hinv x x.2 t ht) hodd
  refine ⟨e, e.2, fun x hx => ?_⟩
  have h : x • ((e : G) • s₀) = (e : G) • s₀ := hfix ⟨x, hx⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, h, inv_smul_smul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
