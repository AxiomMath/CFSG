module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporFinal
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairsOne
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairsKill
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.Sporadic.Bridge.Converse
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicP2Table)
open CFSG.RankThree.PartOne.Census3 (sporadicsThm3)
open CFSG.AGLEmbeddingD2 (d2SporadicOrder)

namespace Spor

theorem exists_noncomm_of_simple_card {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] {n : ℕ}
    (hc : Nat.card X = n) (h2 : 2 ∣ n) (hn : 2 < n) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
  have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
  rw [hc] at hp
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

theorem sporFacts_of
    (hOut : SporadicOuterLeTwo) {s : TauCeti.SporadicName} (hs : s ≠ .M) :
    SporFacts s := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  obtain ⟨hfin, hsim⟩ := CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M s hs
  have hcard := CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder s hs
  have hfinK : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ e.toEquiv
  have hsimK : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := e.symm.isSimpleGroup
  have h2 : 2 ∣ d2SporadicOrder s ∧ 2 < d2SporadicOrder s := by
    cases s <;> first
      | exact absurd rfl hs
      | (simp only [d2SporadicOrder]; norm_num)
  have hnab : ∃ a b : (TauCeti.CFSGIndex.sporadic s).Group, a * b ≠ b * a :=
    exists_noncomm_of_simple_card (Nat.card_congr e.toEquiv.symm |>.trans hcard) h2.1 h2.2
  exact ⟨hfinK, hsimK, hnab, hOut _ hsimK hnab s ⟨MulEquiv.refl _⟩, ⟨e⟩⟩

theorem noPlaneAt_thm3
    (hOut : SporadicOuterLeTwo) (hTab : SporadicP2Table)
    {s : TauCeti.SporadicName} (hs : s ∈ sporadicsThm3) (hne : s ≠ .M12 ∧ s ≠ .M22 ∧ s ≠ .J2)
    (F : SporFacts s) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : NoPlaneAt s p := by
  by_cases h2 : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group
  · rcases hTab s p hp hp2 h2 with h | h
    · rcases h with ⟨rfl, hs3⟩ | ⟨rfl, hs5⟩ | ⟨rfl, rfl⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hs3
        rcases hs3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact noPlaneAt_J3_three F
        · exact noPlaneAt_McL_three F
        · exact noPlaneAt_Suz_three F
        · exact noPlaneAt_ONan_three F
        · exact noPlaneAt_Co3_three F
        · exact noPlaneAt_Co2_three F
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
        · exact noPlaneAt_HN_three F
        · exact noPlaneAt_Ly_three F
        · exact noPlaneAt_Th_three F
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hs5
        rcases hs5 with rfl | rfl | rfl | rfl | rfl
        · exact absurd hs (by decide)
        · exact noPlaneAt_HN_five F
        · exact noPlaneAt_Ly_five F
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
      · exact absurd hs (by decide)
    · rcases h with ⟨rfl, hs3⟩ | ⟨rfl, hs5⟩ | ⟨rfl, hs7⟩ | ⟨rfl, hs11⟩ | ⟨rfl, rfl⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hs3
        rcases hs3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact noPlaneAt_M11_three hOut F
        · exact absurd rfl hne.1
        · exact absurd rfl hne.2.1
        · exact noPlaneAt_M23_three hOut F
        · exact noPlaneAt_M24_three hOut F
        · exact absurd rfl hne.2.2
        · exact noPlaneAt_J4_three hOut F
        · exact noPlaneAt_HS_three hOut F
        · exact noPlaneAt_Ru_three hOut F
        · exact noPlaneAt_He_three hOut F
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hs5
        rcases hs5 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hne.2.2
        · exact noPlaneAt_HS_five hOut F
        · exact noPlaneAt_McL_five hOut F
        · exact noPlaneAt_Suz_five F
        · exact noPlaneAt_He_five hOut F
        · exact noPlaneAt_Ru_five hOut F
        · exact noPlaneAt_Co2_five hOut F
        · exact noPlaneAt_Co3_five hOut F
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
        · exact noPlaneAt_Th_five hOut F
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hs7
        rcases hs7 with rfl | rfl | rfl | rfl | rfl | rfl
        · exact noPlaneAt_He_seven hOut F
        · exact noPlaneAt_ONan_seven hOut F
        · exact absurd hs (by decide)
        · exact absurd hs (by decide)
        · exact noPlaneAt_Th_seven hOut F
        · exact absurd hs (by decide)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hs11
        rcases hs11 with rfl | rfl
        · exact noPlaneAt_J4_eleven hOut F
        · exact absurd hs (by decide)
      · exact absurd hs (by decide)
  · exact noPlaneAt_of_not_dvd F hp hp2 h2

end Spor

theorem k315Spor_holds
    : K315Spor := by
  intro s hs p hp hp2 Ē R hconf
  by_contra hne
  have hne' : s ≠ .M12 ∧ s ≠ .M22 ∧ s ≠ .J2 :=
    ⟨fun h => hne (Or.inl h), fun h => hne (Or.inr (Or.inl h)), fun h => hne (Or.inr (Or.inr h))⟩
  have hM : s ≠ .M := by
    rintro rfl
    exact absurd hs (by decide)
  have hOut : SporadicOuterLeTwo := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hTab : SporadicP2Table := CFSG.HardMathSupport.Solomon.Coordinator.sporadicP2Table_holds
  exact Spor.noPlaneAt_thm3 hOut hTab hs hne' (Spor.sporFacts_of hOut hM) hp hp2 Ē R hconf

end CFSG.LocalAnalysis.UniquenessCase.UCK
