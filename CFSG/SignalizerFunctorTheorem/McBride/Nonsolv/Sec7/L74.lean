module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T72
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.T73
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L74.Gen
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L74.Struct

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem lemma_7_4_a
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (_hS : IsSr p A θ r S)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ a ∉ E) :
    r ∣ Nat.card (θ a) := by
  exact L74.dvd_card_apply h hr ha ha1 hT

theorem lemma_7_4_bc
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ a ∉ E) :
    (∀ L ∈ Ind (θ a), zOf S ⊓ L ≠ ⊥) ∧
      IsDirectProduct {Y | ∃ L ∈ Ind (θ a), Y = zOf S ⊓ L} (zOf S ⊓ θ a) := by
  obtain ⟨N, hΩ⟩ := L74.exists_isRegFam_ind h ha ha1 hT
  obtain ⟨hPH, hP, hidx, hAP⟩ := sylow_of_isSr h hr hS ha ha1
  have hZ : zOf (S ⊓ Subgroup.centralizer {a}) = zOf S ⊓ Subgroup.centralizer {a} := by
    rcases hT with hA | ⟨E, K, hB, haE⟩
    · exact h.theorem_7_2 hr hS hA ha ha1
    · exact h.theorem_7_3 hr hS hB ha haE
  exact L74.inf_ne_bot_and_isDirectProduct_zOf hr.1 hΩ (h.isFunctor.le_centralizer a ha ha1) hPH hP
    hidx hAP (lemma_7_4_a h hr hS ha ha1 hT) hZ

theorem lemma_7_4_b
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ a ∉ E)
    {L : Subgroup G} (hL : L ∈ Ind (θ a)) : zOf S ⊓ L ≠ ⊥ :=
  (lemma_7_4_bc h hr hS ha ha1 hT).1 L hL

theorem lemma_7_4_c
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ a ∉ E) :
    IsDirectProduct {Y | ∃ L ∈ Ind (θ a), Y = zOf S ⊓ L} (zOf S ⊓ θ a) :=
  (lemma_7_4_bc h hr hS ha ha1 hT).2

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
