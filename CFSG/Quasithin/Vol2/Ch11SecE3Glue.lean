module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T V M H : Subgroup G}

theorem e3_39_of_le (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hyp : E3.HypE336 T V M)
    (hCM : Subgroup.centralizer (V : Set G) ≤ M)
    (hnr : (E3.nPrime (autI hV ⊤) : ℕ∞) < E3.rParam V) (hH : IsHStar T M H)
    (hup : E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞)) :
    (E3.wParam T V ≤ E1.nParam H ∧ E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞)) ∧
      (E3.aParam (autI hV ⊤) < E3.sParam hV →
        0 < E3.sParam hV - E3.aParam (autI hV ⊤) ∧
          ((E3.sParam hV - E3.aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ E3.wParam T V) := by
  have hmin := ASInputs.min_le_nParam_of_le hV hV1 hyp hH fun _ hx => hCM hx.2
  refine ⟨⟨?_, hup⟩, fun has => ?_⟩
  · rcases le_total (E3.wParam T V) (E3.rParam V) with h | h
    · rwa [min_eq_left h] at hmin
    · rw [min_eq_right h] at hmin
      exact absurd (hmin.trans hup) (not_le.mpr hnr)
  · obtain ⟨h1, h2⟩ := E3.e3_34_one hV hyp.hyp322 has
    exact ⟨h2, h1⟩

end CFSG.Quasithin.Vol2.Ch11.SecE3
