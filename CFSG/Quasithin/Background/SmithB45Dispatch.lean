module

public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB42Dispatch
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

theorem asB45_caseOne (hB42 : AsB42) {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L)
    (hq : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ)) :
    (∃ A, IsFFStarOffender G A) ∧ ∀ A, IsFFStarOffender G A → B42Conclusion G L A := by
  obtain ⟨A, hA, -, hr⟩ := kq_le_iff.mp hq
  obtain ⟨B, -, hB, -⟩ := B1_4_4_le hV hA hr
  exact ⟨⟨B, hB⟩, fun A hA => hB42 V hV G L hHyp A hA⟩

namespace B45Dispatch

theorem sporadic_of_quotient
    {X : Type} [Group X] [Finite X] (hS : SQTKGroup X) (hq : CFSG.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) {s : TauCeti.SporadicName}
    (hs : s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2)
    (e : X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier s) :
    B45TypeSpor .M12 X ∨ B45TypeHatM22 X ∨ B45TypeSpor .M22 X ∨ B45TypeSpor .M23 X ∨
      B45TypeSpor .M24 X ∨ B45TypeSpor .J2 X := by
  have : Group.IsPerfect X := hq.1
  rcases catalogStepFact X hq hS hodd with h1 | h3
  · have hZ : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hX : IsSporadic s X :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨hZ, hX⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hZ, hX⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hZ, hX⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hZ, hX⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hZ, hX⟩))))
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact (Ch1.false_of_odd_cover_trivial h3 e fun π hπ hC hodd' =>
        CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd').elim
    · exact Or.inr (Or.inl ⟨hq, h3, ⟨e⟩⟩)
    · exact (Ch1.false_of_odd_cover_trivial h3 e fun π hπ hC hodd' =>
        Ch1.M23_perfect_odd_cover_trivial π hπ hC hodd').elim
    · exact (Ch1.false_of_odd_cover_trivial h3 e fun π hπ hC hodd' =>
        CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC hodd').elim
    · exact (Ch1.false_of_odd_cover_trivial h3 e fun π hπ hC hodd' =>
        CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hC hodd').elim

end B45Dispatch

theorem b45FamilyType_of_cubic
    (hD : AsB45DichotomyNat) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L A : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hA : IsA2 G A) (hA3 : commSeries A 3 = ⊥)
    (hr : rAV A ≤ 2) :
    B42FamilyType (↥L) ∨ B45TypeSpor .M12 (↥L) ∨ B45TypeHatM22 (↥L) ∨ B45TypeSpor .M22 (↥L) ∨
      B45TypeSpor .M23 (↥L) ∨ B45TypeSpor .M24 (↥L) ∨ B45TypeSpor .J2 (↥L) := by
  obtain ⟨hSG, hLeq, hq, hirr⟩ := hHyp
  have hLG : L ≤ G := by
    rw [hLeq]
    exact quasithinGenFitting_le G
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hLeq]
    exact le_normalizer_quasithinGenFitting G
  have hW : ∀ v : V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact hV v
  have hodd :=
    Setup.Family.odd_card_center_of_irreducible hW (Bridge.TypeList.irr_of_isIrrSec hirr)
  have hSL := B42Dispatch.sqtkGroup_of_le hSG hLG
  obtain ⟨hDL, h7⟩ := hD V hW L hq hirr (B42Dispatch.a23List_center_quotient hSG hLG hq) A
    (hA.1.trans hGN) hA.2.1 hA.2.2 hA3 ((rAV_le_two_iff hV hA).1 hr)
  rcases hDL with hCA | ⟨s, hs, ⟨e⟩⟩
  · exact Or.inl (B42Dispatch.b42FamilyType_of_charTwoOrAlt hSL hq hodd hCA h7)
  · exact Or.inr (B45Dispatch.sporadic_of_quotient hSL hq hodd hs e)

theorem asB45_of_families
    (hB42 : AsB42) (hD : AsB45DichotomyNat)
    (hD4 : AsB45TrialityD4) (hF4 : AsB45ReeF4) (hG2 : AsB45G2Even) (hL32 : AsB45L32)
    (hL42 : AsB45L42) (hL52 : AsB45L52) (hA6 : AsB45Alt6) (hHA6 : AsB45HatA6)
    (hA7 : AsB45Alt7) (hA5 : AsB45Alt5) (hL2 : AsB45L2Even) (hU3 : AsB45U3Even) (hSz : AsB45Sz)
    (hL3 : AsB45L3Even) (hU33 : AsB45U33) (hSp4 : AsB45Sp4Even) (hM12 : AsB45M12)
    (hHM22 : AsB45HatM22) (hM22 : AsB45M22) (hM23 : AsB45M23) (hM24 : AsB45M24)
    (hJ2 : AsB45J2) : AsB45 := by
  intro V _ _ hV G L hHyp hq2
  by_cases hq1 : qhatOf G ≤ ((1 : ℚ) : WithTop ℚ)
  · exact Or.inl ⟨hq1, asB45_caseOne hB42 hV hHyp hq1⟩
  have hlt : ((1 : ℚ) : WithTop ℚ) < qhatOf G := not_le.mp hq1
  obtain ⟨A, hA, hA3, hr⟩ := kq_le_iff.mp hq2
  have key : AsB45Table G L ∨ AsB45Part3 G L := by
    rcases b45FamilyType_of_cubic hD hV hHyp hA hA3 hr with
      (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | h | h | h | h | h | h
    · exact hU3 V hV G L hHyp h hlt hq2
    · exact hSz V hV G L hHyp h hlt hq2
    · exact AsB45No2FFor.asB45For hD4 V hV G L hHyp h hlt hq2
    · exact AsB45No2FFor.asB45For hF4 V hV G L hHyp h hlt hq2
    · exact hL2 V hV G L hHyp h hlt hq2
    · exact AsB45FFOnlyFor.asB45For hL32 V hV G L hHyp h hlt hq2
    · exact hL3 V hV G L hHyp h hlt hq2
    · exact hSp4 V hV G L hHyp h hlt hq2
    · exact AsB45FFOnlyFor.asB45For hG2 V hV G L hHyp h hlt hq2
    · exact hU33 V hV G L hHyp h hlt hq2
    · exact AsB45FFOnlyFor.asB45For hL42 V hV G L hHyp h hlt hq2
    · exact AsB45FFOnlyFor.asB45For hL52 V hV G L hHyp h hlt hq2
    · exact hA5 V hV G L hHyp h hlt hq2
    · exact AsB45FFOnlyFor.asB45For hA6 V hV G L hHyp h hlt hq2
    · exact AsB45FFOnlyFor.asB45For hHA6 V hV G L hHyp h hlt hq2
    · exact hA7 V hV G L hHyp h hlt hq2
    · exact hM12 V hV G L hHyp h hlt hq2
    · exact hHM22 V hV G L hHyp h hlt hq2
    · exact hM22 V hV G L hHyp h hlt hq2
    · exact hM23 V hV G L hHyp h hlt hq2
    · exact hM24 V hV G L hHyp h hlt hq2
    · exact hJ2 V hV G L hHyp h hlt hq2
  rcases key with h | h
  · exact Or.inr (Or.inl ⟨hlt, h⟩)
  · exact Or.inr (Or.inr h)

end CFSG.Quasithin
