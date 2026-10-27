module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Rechoice

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_choice_of_cyclic {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {p d : ℕ} (hpd : (p = 3 ∧ d = 2) ∨ (p = 7 ∧ d = 3))
    (hsig : D.sig = {p})
    (h : ∀ t : MulAut (Vtil V₀ V hV), t ∈ Mbar D.M V₀ V hV → t ^ 2 = 1 → t ≠ 1 →
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
        Conc4_136W (Mbar D.M V₀ V hV) t (lBar V₀ V hV L) →
          ∃ K : Subgroup (MulAut (Vtil V₀ V hV)), Conc4_136W (Mbar D.M V₀ V hV) t K ∧
            IsCyclicOrd ↥K p ∧ rk ↥(commSub ⊤ K) = d ∧
            Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
              ∃ φ ∈ Mbar D.M V₀ V hV, X = K.map (MulAut.conj φ).toMonoidHom} = 2) :
    Choice168F D V₀ V hV := by
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := c.conc
  obtain ⟨K, hK, hKc, hKrk, hKn⟩ := h t ht ht2 ht1 htr hW
  obtain ⟨L', hS, hbar, hconc, hs⟩ :=
    s16e_d5_rechoice D hV c.setting.hyp16 ht ht2 ht1 htr hK
  have hlbar : lBar V₀ V hV L' = K := hbar
  have hwTil : wTil V₀ V hV L' = commSub ⊤ K := by
    show commSub ⊤ (barSub V₀ V hV L') = _
    rw [hbar]
  have hs2 : s15 D.M V₀ V hV L' = 2 := hs.trans hKn
  refine ⟨L', hS, ?_, hconc, ?_⟩
  · rw [hbar]
    exact hK.ne_bot
  · rcases hpd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Final168F.of_case167_3 ⟨hlbar ▸ hKc, hwTil ▸ hKrk, hs2, hsig⟩
    · exact Final168F.of_case168_11 ⟨hlbar ▸ hKc, hwTil ▸ hKrk, hs2, hsig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
