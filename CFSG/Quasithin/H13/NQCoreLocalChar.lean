module

public import CFSG.Quasithin.Vol2.Ch1Nine

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem qt_positive_two_core_SQTK [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : quasithinIsQTKECat G) {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    H < ⊤ ∧ CFSG.SectionRank.IsSQTKCat ↥H :=
  ⟨lt_top_iff_ne_top.mpr (ne_top_of_pCoreOf_ne_bot_of_simple hnab hH),
    (qtkeCore_of_cat hnab hQ).1 H hH⟩

theorem qt_full_Sylow_local_characteristic_two (hQ : quasithinIsQTKECat G) {T L : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hL : quasithinIsLocal T L) :
    quasithinGenFitting L = pCoreOf 2 L ∧
      (∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
        (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L) ∧
      (quasithinIsFaithfulLocal T L ↔ quasithinV2 L ≠ ⊥) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := isXClass_of_isLocal hQ hT hL
  have hF : quasithinGenFitting L = pCoreOf 2 L :=
    (quasithinGenFitting_eq_pCoreOf_iff L 2).mpr hX.2.2
  have hO := (eq_oTwoUpper_iff_forall_normal L).mp hX.2.1
  exact ⟨hF, hO, ⟨fun h => h.2.2.2, fun hV => ⟨hL, hO, hF, hV⟩⟩⟩

end CFSG.Quasithin.H13.NQCore
