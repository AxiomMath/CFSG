module

public import CFSG.Quasithin.Background.RonanE43FamilyS5

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.E2P B6
  CFSG.Quasithin.E2P.SporB

variable {G : Type} [Group G] [Finite G]

theorem goodFamily_of_subgroups {T L Ah Ph Vh : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hLT : L ⊔ T = ⊤) (hA5 : IsA5Ext Ah Vh) (hAn : T ≤ Subgroup.normalizer (Ah : Set G))
    (hPn : T ≤ Subgroup.normalizer (Ph : Set G)) (hPL : Ph ≤ L) (hTP : T ⊓ L ≤ Ph)
    (hP3 : Nat.card Ph = 3 * Nat.card ↥(T ⊓ L)) (hgen : L ≤ (Ah ⊔ T) ⊔ (Ph ⊔ T)) :
    GoodFamily T 3 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVG : Vh = pCoreOf 2 Ah := hA5.pCoreOf_eq.symm
  set H₂ : Subgroup G := Ah ⊔ T with hH₂
  set H₃ : Subgroup G := Ph ⊔ T with hH₃
  have hH₂n : H₂ ≤ Subgroup.normalizer (Ah : Set G) :=
    sup_le (Subgroup.le_normalizer) hAn
  have hH₂V : H₂ ≤ Subgroup.normalizer (Vh : Set G) := by
    rw [hVG]
    exact hH₂n.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Ah)
  obtain ⟨hVA, hV2, φ, hφs, hφk⟩ := hA5
  have hgood₂ : GoodAt T H₂ := fun Y hYH hYn hYT =>
    s5_good hT le_sup_right le_sup_left hVA hH₂n hH₂V hV2 φ hφs hφk rfl hYH hYn hYT
  have hrank₂ : CFSG.Open.pRank 2 (⊤ : Subgroup (↥H₂ ⧸ CFSG.pCore 2 ↥H₂)) ≤ 2 :=
    s5_pRank hT le_sup_left hVA hH₂n hH₂V hV2 φ hφs hφk rfl
  have hPT : Ph ⊓ T = T ⊓ L := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.2, hPL hx.1⟩
    · exact le_inf hTP inf_le_left
  have hcardH : Nat.card ↥(Ph ⊔ T) = 3 * Nat.card T := by
    rw [card_sup_eq_relIndex_mul hPn, hP3]
    have h1 := Subgroup.relIndex_mul_card (H := Ph) (K := T)
    rw [hPT] at h1
    calc Ph.relIndex T * (3 * Nat.card ↥(T ⊓ L)) =
        3 * (Ph.relIndex T * Nat.card ↥(T ⊓ L)) := by ring
      _ = 3 * Nat.card T := by rw [h1]
  have h2₃ : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H₃) :=
    card_le_two_mul_pCoreOf le_sup_right hT.isPGroup hcardH
  have hgood₃ : GoodAt T H₃ := goodAt_of_card_le hT le_sup_right h2₃
  have hrank₃ : CFSG.Open.pRank 2 (⊤ : Subgroup (↥H₃ ⧸ CFSG.pCore 2 ↥H₃)) ≤ 1 :=
    pRank_le_one_of_card_le hT le_sup_right h2₃
  refine ⟨{H₂, H₃}, ⟨H₂, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH'
    · exact le_sup_right
    · rw [Finset.mem_singleton.mp hH']
      exact le_sup_right
  · rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [eq_top_iff, ← hLT]
    exact sup_le hgen (le_sup_right.trans le_sup_left)
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH'
    · exact hgood₂
    · rw [Finset.mem_singleton.mp hH']
      exact hgood₃
  · by_cases hEq : H₂ = H₃
    · rw [hEq, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.sum_singleton]
      omega
    · rw [Finset.sum_pair hEq]
      omega

end CFSG.Quasithin.RonanE43
