module

public import CFSG.Quasithin.Background.SimsE214FourSp4

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem e214_four
    (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V)
    (_hc : CharTwo H) (hTI : IsTISetIn V M) (I : Subgroup Γ) (g : Γ) (hI : IsInIHTV H T M V I)
    (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g) (hZ : V ⊓ conjSubgroup V g ≠ ⊥)
    (MI TI JI B A P Z : Subgroup Γ) (k : ℕ) (hMI : MI = M ⊓ I) (hTI' : TI = T ⊓ I)
    (_hJI : JI = kerIn MI I) (hB : B = V ⊓ pCoreOf 2 I)
    (hA : A = conjSubgroup V g ⊓ pCoreOf 2 I) (hP : P = A ⊔ B)
    (hZdef : Z = V ⊓ conjSubgroup V g)
    (_hk : E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞))
    (hV : IsSp4Full k (E2.StarQuot MI I) → E2.star MI I V = centerOf (E2.star MI I TI)) :
    (IsSz k (E2.StarQuot MI I) ∨ (1 ≤ k ∧ IsSp4Full k (E2.StarQuot MI I))) →
      ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P → I ≤ Subgroup.normalizer (Y₁ : Set Γ) →
        I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
        (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
          Y = Y₂ ∨ Y = Y₁) →
        4 * k ≤ E3.mQuot Y₁ Y₂ := by
  subst hMI hTI' hB hA hP hZdef
  rintro (hSz | ⟨hk, hSp⟩) Y₁ Y₂ hZY hY hY₁P hIY₁ hIY₂ -
  · exact E214F.four_of_sz h hTI hI hg hIV hZ hSz hZY hY hY₁P hIY₁ hIY₂
  · exact E214F.four_of_sp4 h hI hg hIV hk hSp (hV hSp) hZY hY hY₁P hIY₁ hIY₂

end CFSG.Quasithin.SimsE2
