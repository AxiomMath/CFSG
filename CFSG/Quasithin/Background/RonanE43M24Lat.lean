module

public import CFSG.Quasithin.Background.RonanE43Basic
public import CFSG.Quasithin.EmptyFaithful.S151S9TM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import Certificates.Certificate3017
public import Certificates.Certificate4068
public import Certificates.Certificate4075
public import Certificates.Certificate4194

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Quasithin.S151S9T


theorem m24_card_pCoreOf (j : ℕ) (hj : j < 13) :
    Nat.card (pCoreOf 2 (m24Ctx.Y j)) = (m24Mems.getD j ⟨0, 0, 0⟩).o2 := by
  have hJ : j < m24Ctx.J := by rw [m24_J]; exact hj
  have h := (m24Ctx.memStmt_default (Ot := m24OtK) m24_o2OK hJ).2.1
  have hrow : m24Mems.getD j ⟨0, 0, 0⟩ = defaultRow m24Ctx.k m24Ctx.D m24OtK j := by
    have := m24_rows
    rw [← this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hj]
    rfl
  rw [hrow]
  exact h

theorem m24_two_le (j : ℕ) (hj : j = 7 ∨ j = 9 ∨ j = 11) :
    Nat.card m24Ctx.S ≤ 2 * Nat.card (pCoreOf 2 (m24Ctx.Y j)) := by
  have hj13 : j < 13 := by omega
  rw [m24_card_pCoreOf j hj13, m24Ctx.S_card]
  have hk : m24Ctx.k = 10 := rfl
  rw [hk]
  rcases hj with rfl | rfl | rfl <;> decide

theorem m24_gen :
    (⨆ Y ∈ ({m24Ctx.Y 7, m24Ctx.Y 9, m24Ctx.Y 11} : Set (Subgroup ↥CFSG.Blueprint.NativeSporadic.M24)),
      Y) = ⊤ := by
  set J : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24 :=
    ⨆ Y ∈ ({m24Ctx.Y 7, m24Ctx.Y 9, m24Ctx.Y 11} : Set (Subgroup ↥CFSG.Blueprint.NativeSporadic.M24)),
      Y with hJ
  have h7 : m24Ctx.Y 7 ≤ J := le_iSup₂_of_le (m24Ctx.Y 7) (by simp) le_rfl
  have h9 : m24Ctx.Y 9 ≤ J := le_iSup₂_of_le (m24Ctx.Y 9) (by simp) le_rfl
  have h11 : m24Ctx.Y 11 ≤ J := le_iSup₂_of_le (m24Ctx.Y 11) (by simp) le_rfl
  obtain ⟨j, hj, hjeq⟩ := m24_complete J ((m24Ctx.S_le_Y 7).trans h7)
  by_cases hj13 : j < 13
  · exfalso
    simp only [memberOrTop, m24_J, hj13, ite_true] at hjeq
    have e7 := (m24_Y_le_iff (j := 7) (jj := j) (by norm_num) hj13).mp (hjeq ▸ h7)
    have e9 := (m24_Y_le_iff (j := 9) (jj := j) (by norm_num) hj13).mp (hjeq ▸ h9)
    have e11 := (m24_Y_le_iff (j := 11) (jj := j) (by norm_num) hj13).mp (hjeq ▸ h11)
    have hfin : ∀ j < 13, j ∈ m24Incl[7]! → j ∈ m24Incl[9]! → j ∈ m24Incl[11]! → False := by
      decide
    exact hfin j hj13 e7 e9 e11
  · have : j = 13 := by omega
    subst this
    rw [hjeq]
    simp [memberOrTop, m24_J]


theorem m24_isSylowIn : IsSylowIn 2 m24Ctx.S ⊤ := m24_S_sylow

theorem m24_family :
    ∃ F : Finset (Subgroup ↥CFSG.Blueprint.NativeSporadic.M24), F.card ≤ 3 ∧ F.Nonempty ∧
      (∀ Y ∈ F, m24Ctx.S ≤ Y) ∧
      (∀ Y ∈ F, Nat.card m24Ctx.S ≤ 2 * Nat.card (pCoreOf 2 Y)) ∧ (⨆ Y ∈ F, Y) = ⊤ := by
  classical
  refine ⟨{m24Ctx.Y 7, m24Ctx.Y 9, m24Ctx.Y 11}, Finset.card_le_three, ⟨m24Ctx.Y 7, by simp⟩, ?_, ?_, ?_⟩
  · intro Y hY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl | rfl <;> exact m24Ctx.S_le_Y _
  · intro Y hY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl | rfl
    · exact m24_two_le 7 (by simp)
    · exact m24_two_le 9 (by simp)
    · exact m24_two_le 11 (by simp)
  · have h := m24_gen
    simpa using h

end CFSG.Quasithin.RonanE43
