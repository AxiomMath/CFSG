module

public import CFSG.Quasithin.Background.RonanE338Upper
public import CFSG.Quasithin.Background.RonanE338Lower

public section

namespace CFSG.Quasithin.RonanE338

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T V M H : Subgroup G}

theorem e3_38 (hE22 : E2.E22StatementC) (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hyp : E3.HypE336 T V M) (hH : IsHStar T M H) :
    min (E3.wParam T V) (E3.rParam V) ≤ E1.nParam H ∧
      E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) :=
  ⟨min_le_nParam hV hV1 hyp hH, nParam_le_nPrime hE22 hV hyp hH⟩

theorem e3_39 (hE22 : E2.E22StatementC) (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥)
    (hyp : E3.HypE336 T V M) (hnr : (E3.nPrime (autI hV ⊤) : ℕ∞) < E3.rParam V)
    (hH : IsHStar T M H) :
    (E3.wParam T V ≤ E1.nParam H ∧ E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) ∧
        (E3.nPrime (autI hV ⊤) : ℕ∞) < E3.rParam V) ∧
      (E3.aParam (autI hV ⊤) < E3.sParam hV →
        0 < E3.sParam hV - E3.aParam (autI hV ⊤) ∧
          ((E3.sParam hV - E3.aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ E3.wParam T V ∧
          E3.wParam T V ≤ E1.nParam H ∧ E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) ∧
          (E3.nPrime (autI hV ⊤) : ℕ∞) < E3.rParam V) := by
  obtain ⟨hmin, hup⟩ := e3_38 hE22 hV hV1 hyp hH
  have hw : E3.wParam T V ≤ E1.nParam H := by
    rcases le_total (E3.wParam T V) (E3.rParam V) with h | h
    · rwa [min_eq_left h] at hmin
    · rw [min_eq_right h] at hmin
      exact absurd (hmin.trans hup) (not_le.mpr hnr)
  refine ⟨⟨hw, hup, hnr⟩, fun has => ?_⟩
  obtain ⟨h1, h2⟩ := E3.e3_34_one hV hyp.hyp322 has
  exact ⟨h2, h1, hw, hup, hnr⟩

end CFSG.Quasithin.RonanE338

end
