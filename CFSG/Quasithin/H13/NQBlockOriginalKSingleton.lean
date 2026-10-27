module

public import CFSG.Quasithin.H13.NQBlockOriginalSupplements

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

@[expose] def OriginalKEscapingSourceY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
      ∃ Y : Subgroup G, Y ≤ H ∧ (Y.subgroupOf H).Normal ∧ ¬ Y ≤ M ∧
        ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y ∧
        ((∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ Monoid.exponent (Y ⧸ CFSG.pCore 2 Y) = r ∧
            Subgroup.upperCentralSeries (Y ⧸ CFSG.pCore 2 Y) 2 = ⊤ ∧
            CFSG.pRank r (Y ⧸ CFSG.pCore 2 Y) ≤ 2 ∧ Nat.card (Y ⧸ CFSG.pCore 2 Y) ≤ r ^ 3) ∨
          Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* GL (Fin 3) (ZMod 2)))

@[expose] def OriginalNoNormalSourceYEscapes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
      ∀ Y : Subgroup G, Y ≤ H → (Y.subgroupOf H).Normal → ¬ Y ≤ M →
        ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y →
        ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Monoid.exponent (Y ⧸ CFSG.pCore 2 Y) = p ∧
            Subgroup.upperCentralSeries (Y ⧸ CFSG.pCore 2 Y) 2 = ⊤ ∧
            CFSG.pRank p (Y ⧸ CFSG.pCore 2 Y) ≤ 2) ∨
          Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* GL (Fin 3) (ZMod 2))) → False

variable {G : Type} [Group G] [Finite G]

theorem original_K_singleton_of_inputs (hS : OriginalKEscapingSourceY)
    (hE : OriginalNoNormalSourceYEscapes) {T L M : Subgroup G} (h : QTNQ T L M) :
    quasithinIsMaxTwoLocal M ∧ nqOriginalK T L ⊔ T ≤ M ∧
      ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → nqOriginalK T L ⊔ T ≤ M' → M' = M := by
  obtain ⟨hKL, -, -⟩ := original_K_supplement h
  refine ⟨h.max_two_local, sup_le (hKL.trans h.l_le) h.t_le, fun M' hM' hKTM' => ?_⟩
  by_contra hne
  obtain ⟨Y, hYH, hYn, hYM, hKY, hbr⟩ := hS G T L M h M' hM' hKTM' hne
  refine hE G T L M h M' hM' hKTM' hne Y hYH hYn hYM hKY ?_
  rcases hbr with ⟨r, hr, hr2, hexp, hcl, hrk, -⟩ | hA5 | hL32
  · exact Or.inl ⟨r, hr, hr2, hexp, hcl, hrk⟩
  · exact Or.inr (Or.inl hA5)
  · exact Or.inr (Or.inr hL32)

end CFSG.Quasithin.H13.NQBlock
