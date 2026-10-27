module

public import CFSG.Quasithin.EmptyFaithful.S146F21
public import CFSG.Quasithin.EmptyFaithful.S146zVA
public import CFSG.Quasithin.EmptyFaithful.SBc17Norm

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.C2Push CFSG.Quasithin.S146zV CFSG.Quasithin.SBc17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowTwoOf_le_iff_relIndex_odd {J A : Subgroup G} (hAJ : A ≤ J) :
    (∃ S : Subgroup G, IsSylowTwoOf S J ∧ S ≤ A) ↔ ¬ 2 ∣ A.relIndex J := by
  constructor
  · rintro ⟨S, hS, hSA⟩ hd
    have h1 : S.relIndex A * A.relIndex J = S.relIndex J :=
      Subgroup.relIndex_mul_relIndex S A J hSA hAJ
    have h2 : 2 ∣ S.relIndex J := h1 ▸ Dvd.dvd.mul_left hd _
    exact hS.2.2 h2
  · intro hodd
    obtain ⟨S, hS, -⟩ := exists_isSylowTwoOf_ge_of_isPGroup (bot_le : (⊥ : Subgroup G) ≤ A)
      IsPGroup.of_bot
    have hSJ : S ≤ J := hS.1.trans hAJ
    have h1 : S.relIndex A * A.relIndex J = S.relIndex J :=
      Subgroup.relIndex_mul_relIndex S A J hS.1 hAJ
    refine ⟨S, ⟨hSJ, hS.2.1, ?_⟩, hS.1⟩
    change ¬ 2 ∣ S.relIndex J
    rw [← h1]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact hS.2.2 h
    · exact hodd h

section Config

variable {T M H PQ : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}
  {K₁ K₂ : Subgroup G} {s : G}

theorem normalizer_inf_eq_g12 (hHyp : HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂)) :
    g2_14615 K₂ ⊓ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) = g12_14615 T K₂ := by
  apply le_antisymm
  · exact (inf_normalizer_le_cgsIn hHyp.radical.2.1).trans hHyp.cgs
  · exact le_inf hHyp.le (inf_le_left.trans (le_normalizer_pCoreOf 2 (mcOf T)))

end Config

end CFSG.Quasithin.S146zW
