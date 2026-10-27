module

public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Bound

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B V₂ : Subgroup D} {c : D}

omit [Finite D] in
theorem mem_normalizer_of_cjSub_eq {g : D} {X : Subgroup D} (h : cjSub g X = X) :
    g ∈ Subgroup.normalizer (X : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ cjSub g X := by
      rw [mem_cjSub]
      simpa [mul_assoc] using hx
    rwa [h] at this
  · intro hx
    rw [← h, mem_cjSub] at hx
    simpa [mul_assoc] using hx

omit [Finite D] in
theorem mem_normalizer_thompsonJ {S : Subgroup D} {g : D}
    (hg : g ∈ Subgroup.normalizer (S : Set D)) :
    g ∈ Subgroup.normalizer (CFSG.Quasithin.thompsonJ S : Set D) :=
  mem_normalizer_of_cjSub_eq (cjSub_thompsonJ hg)

theorem not_thompsonJ_le_centralizer (h : GoldHyp A B)
    (hN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
    (hn : IsNaturalAt B (A ⊓ B) c V₂) (hV₂A : V₂ ≤ pCoreOf 2 A) :
    ¬ CFSG.Quasithin.thompsonJ (pCoreOf 2 A) ≤ Subgroup.centralizer (V₂ : Set D) := by
  intro hJC
  have hJS : CFSG.Quasithin.thompsonJ (pCoreOf 2 A) ≤ pCoreOf 2 A :=
    CFSG.Quasithin.thompsonJ_le_self _
  have hSB : pCoreOf 2 A ≤ B := h.pCoreOf_left_le.trans inf_le_right
  have hJR : CFSG.Quasithin.thompsonJ (pCoreOf 2 A) ≤ pCoreOf 2 A ⊓ pCoreOf 2 B := by
    intro x hx
    refine ⟨hJS hx, ?_⟩
    rw [← hn.centralizer_eq]
    exact ⟨hSB (hJS hx), hJC hx⟩
  have hEq := CFSG.Quasithin.thompsonJ_eq_of_le hJR inf_le_left
  have hAJ : A ≤ Subgroup.normalizer (CFSG.Quasithin.thompsonJ (pCoreOf 2 A) : Set D) :=
    fun a ha => mem_normalizer_thompsonJ (le_normalizer_pCoreOf 2 A ha)
  have hBJ : B ≤ Subgroup.normalizer (CFSG.Quasithin.thompsonJ (pCoreOf 2 A) : Set D) := by
    rw [hEq]
    exact fun b hb => mem_normalizer_thompsonJ (hN hb)
  have h0 := h.eq_bot_of_normalizes hAJ hBJ (hJS.trans h.pCoreOf_left_le)
  obtain ⟨E, hE⟩ := CFSG.Quasithin.exists_isMaxElemAbelian (pCoreOf 2 A)
  have hcard : Nat.card V₂ ≤ Nat.card E := hE.2.2 V₂ hV₂A hn.reduced.2.2.1
  have hEJ : E ≤ CFSG.Quasithin.thompsonJ (pCoreOf 2 A) := le_iSup₂_of_le E hE le_rfl
  rw [h0, le_bot_iff] at hEJ
  rw [hEJ, Subgroup.card_bot, hn.card_eq] at hcard
  omega

end GoldAmLab7

end F6

end CFSG.Quasithin
