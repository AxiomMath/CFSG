module

public import CFSG.Quasithin.Background.RonanE114SevenCase
public import CFSG.Quasithin.Background.RonanE114U33
public import CFSG.Quasithin.Vol2.Ch11SecU1EpsOut
public import CFSG.Quasithin.Vol2.Ch11SecD551A

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11

@[expose] def L35OutSolvablePair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup ↥(CFSG.generalizedFitting G) → IsSylowIn 2 T ⊤ →
    CFSG.generalizedFitting G ⊔ T = ⊤ → IsPSL 3 5 1 ↥(CFSG.generalizedFitting G) →
    ¬ T ≤ CFSG.generalizedFitting G →
    ∃ X Y : Subgroup G, T ≤ X ∧ T ≤ Y ∧ Group.IsSolvable ↥X ∧ Group.IsSolvable ↥Y ∧ X ⊔ Y = ⊤

section Main


theorem clause_seven_of (h5 : L35OutSolvablePair)
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ (s : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 s p 1 ↥(CFSG.generalizedFitting G) →
      E1.nParam (⊤ : Subgroup G) = 1 := by
  intro s p hp hp2 hP
  haveI : Fact p.Prime := ⟨hp⟩
  have hT' := Seven.quasithinIsSylowTwo_of_isSylowIn_top hT
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    have h2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    omega
  have h2L : 2 ∣ Nat.card ↥(CFSG.generalizedFitting G) := by
    cases s with
    | true =>
      obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 hP
      rw [Nat.card_congr e.toEquiv, ← SecU1.L3I.orderOf_zc hp2]
      exact orderOf_dvd_natCard _
    | false =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := E2P.Asc80.exists_equiv_psu3 hP
      rw [Nat.card_congr e.toEquiv, ← SecU1.U3.orderOf_zcU hp2 hF]
      exact orderOf_dvd_natCard _
  have heven : Even (Nat.card (⊤ : Subgroup G)) := by
    rw [even_iff_two_dvd, Subgroup.card_top]
    exact h2L.trans (Subgroup.card_subgroup_dvd_card _)
  have hle : E1.nParam (⊤ : Subgroup G) ≤ 1 := by
    cases s with
    | true =>
      by_cases hTL : T ≤ CFSG.generalizedFitting G
      · exact SecU1.L3I.nParam_le_one_of_psl3_inner hp hp2 hP hTL hFT
      · rcases hmod with h1 | h3
        · by_cases hp5 : p = 5
          · subst hp5
            obtain ⟨X, Y, hX, hY, hXs, hYs, hXY⟩ := h5 G T hSQ hFs hT hFT hP hTL
            exact SecU1.nParam_le_one_of_solvable_pair hT hX hY hXs hYs hXY
          · have hp13 : 13 ≤ p := by
              by_contra hlt
              have hp9 : p ≠ 9 := by
                rintro rfl
                norm_num at hp
              have := hp.two_le
              omega
            exact Seven.nParam_le_one_of_psl3_wreathed A38c15.sl3OddIrr hp hp13 h1 hFs hP hT hFT hTL
        · exact E2.E22N.e114ResRestL3EpsOut_holds G T hSQ hFs hT' hFT
            ⟨true, p, hp, hp2, fun _ => h3, fun h => absurd h (by simp), hP, fun _ => hTL⟩
    | false =>
      by_cases hp3 : p = 3
      · subst hp3
        exact (nParam_eq_one_of_isPSU33 hP hT' hFT).le
      · rcases hmod with h1 | h3
        · exact E2.E22N.e114ResRestL3EpsOut_holds G T hSQ hFs hT' hFT
            ⟨false, p, hp, hp2, fun h => absurd h (by simp), fun _ => h1, hP,
              fun h => absurd h (by simp)⟩
        · have hp7 : 7 ≤ p := by
            have := hp.two_le
            omega
          exact Seven.nParam_le_one_of_psu3_wreathed hp hp7 h3 hFs hP hT hFT
  exact SecD.nParam_eq_one_of_le_one hle heven

end Main

end CFSG.Quasithin.RonanE114
