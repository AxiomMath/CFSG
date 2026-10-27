module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFC1U33
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved
import CFSG.LocalAnalysis.UniquenessCase.UC7P3LinTwoIrr
import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (ActsIrr Gls3ConclusionPlus)

private theorem le_commutator_or_eq_of_actsIrr {X : Type} [Group X] {K P N W : Subgroup X}
    (hN : N ≤ K ⊓ normalizer (P : Set X)) (hirr : ActsIrr N P) (hWP : W ≤ P)
    (hW : K ⊓ normalizer (P : Set X) ≤ normalizer (W : Set X)) : W ≤ ⁅P, P⁆ ∨ W = P :=
  (hirr W hWP (hN.trans hW)).imp (fun h => h.le.trans bot_le) id

theorem irreducible_or_psl28_of_gls3ConclusionPlus {X : Type} [Group X] [Finite X]
    {K : Subgroup X} [K.Normal] {p : ℕ} (hp3 : p = 3) (P : Sylow p X)
    (h : Gls3ConclusionPlus X K P) (hR : ∀ m : ℕ, ¬ IsoLie ↥K (.reeG2 m))
    (hU : ∀ q : TauCeti.PrimePower, q.p = 3 → IsoLie ↥K (.twistedA 2 q) → q.exponent = 1) :
    ((P : Subgroup X) ≤ K ∧ (∀ x ∈ (P : Subgroup X), x ^ 3 = 1) ∧
      ∀ W : Subgroup X, W ≤ P →
        K ⊓ normalizer ((P : Subgroup X) : Set X) ≤ normalizer (W : Set X) →
          W ≤ ⁅(P : Subgroup X), (P : Subgroup X)⁆ ∨ W = P) ∨
    (IsoLie ↥K (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩) ∧ K.index = 3 ∧
      Nat.card ↥((P : Subgroup X) ⊓ K) = 9 ∧
      Nat.card ↥(K ⊓ normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X)) = 18 ∧
      Nat.card (P : Subgroup X) = 27) := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPK : ¬ 3 ∣ K.index → (P : Subgroup X) ≤ K :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1810_le_of_not_dvd_index P.isPGroup'
  obtain ⟨-, -, h⟩ := h
  rcases h with ⟨q, hq3, hI, hidx, -, -, hEl, hcard⟩ | ⟨q, hq3, hI, hidx, -⟩ | ⟨m, hI, -⟩ |
      ⟨hI, hidx, -, h9, hΓ, ⟨e⟩, h27, -⟩ | ⟨-, hidx, hEl, -, hΓ, J, -, hJ, hJirr⟩ |
      ⟨-, ⟨j, hidx⟩, -, hEl, -, hΓ, S, hSΓ, -, -, -, hSirr⟩ |
      ⟨-, hK, hEl, -, hΓ, S, hSΓ, -, -, -, -, hSirr⟩
  ·
    have hPK' := hPK hidx
    rw [inf_of_le_left hPK'] at hEl hcard
    refine Or.inl ⟨hPK', hEl.2, fun W hWP hW => ?_⟩
    exact (eq_bot_or_eq_of_le_of_isoLie_A1 (by rw [hq3]; norm_num) hI hPK' hcard hWP hW).imp
      (fun h => h.le.trans bot_le) id
  ·
    have hPK' := hPK hidx
    have hq1 := hU q hq3 hI
    have hexp : ∀ x ∈ (P : Subgroup X), x ^ 3 = 1 := fun x hx => by
      have h3 := (CFSG.LocalAnalysis.RankThreeTheoremC.u3SylowData_proved ↥K
        ⟨q, hq3, hq1, hI⟩ (P.subtype hPK')).2.1 ⟨x, hPK' hx⟩
        (by rw [Sylow.coe_subtype]; exact mem_subgroupOf.mpr hx)
      simpa using congrArg Subtype.val h3
    have hidxK : ¬ 3 ∣ (P : Subgroup X).relIndex K := by
      have h3 := (P.subtype hPK').not_dvd_index
      rwa [Sylow.coe_subtype] at h3
    refine Or.inl ⟨hPK', hexp, fun W hWP hW => ?_⟩
    rcases CFSG.LocalAnalysis.RankThreeTheoremC.kFactU33SylowIrr X K
        ⟨q, hq3, by rw [q.card_def, hq3, hq1, pow_one], hI⟩ P hPK' P.isPGroup' hidxK W hWP hW
      with h | h
    · exact Or.inl (h.trans
        (CFSG.Quasithin.Ch1Sec3.frattiniIn_eq_commutator P.isPGroup' hexp).le)
    · exact Or.inr h
  · exact absurd hI (hR m)
  ·
    refine Or.inr ⟨hI, hidx, h9, ?_, h27⟩
    rw [← hΓ, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  ·
    have hPK' := hPK hidx
    rw [inf_of_le_left hPK'] at hEl hΓ hJ hJirr
    exact Or.inl ⟨hPK', hEl.2, fun W hWP hW => le_commutator_or_eq_of_actsIrr
      ((le_sup_right.trans hJ.ge).trans hΓ.le) hJirr hWP hW⟩
  ·
    have hPK' := hPK (by
      rw [hidx]
      exact fun hd => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num))
    rw [inf_of_le_left hPK'] at hEl hΓ hSΓ hSirr
    exact Or.inl ⟨hPK', hEl.2, fun W hWP hW => le_commutator_or_eq_of_actsIrr
      (hSΓ.trans hΓ.le) hSirr hWP hW⟩
  ·
    have hPK' : (P : Subgroup X) ≤ K := by
      rw [hK]
      exact le_top
    rw [inf_of_le_left hPK'] at hEl hΓ hSΓ hSirr
    exact Or.inl ⟨hPK', hEl.2, fun W hWP hW => le_commutator_or_eq_of_actsIrr
      (hSΓ.trans hΓ.le) hSirr hWP hW⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
