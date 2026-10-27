module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLieAut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLieSurvivor
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K6c K7 LieFam811 IsLie811 qPlusPi)

variable {G : Type} [Group G] [Finite G] {D : Data G}

@[expose] def Case811Sylow.Sp6Excluded {c : Ctx82E3 D} (h : Case811Sylow c) : Prop :=
  ∀ {f p : ℕ}, IsLie811 c.Lbar .psp6 2 f → p ∈ D.sig → p ∣ qPlusPi 2 f →
    ¬ p ∣ Nat.card (D.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G) → False

theorem Ctx82E3.lie3_exit (c : Ctx82E3 D) (h : Case811Sylow c) (hK6c : K6c) (hK7 : K7)
    (hN1 : LieOddCharRank) (hN2 : LieL67PlusRank) (hN3 : K7cSharp) (hN4 : K7L67TwoSharp)
    (hN5 : K7L4Mech) (hN6 : K7L7TwoMech) {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 c.Lbar fam r f) :
    r = 2 ∧ ∀ p ∈ D.sig, h.Lie3Survivor fam f p := by
  classical
  have hr2 : r = 2 := by
    by_contra hr
    have hrprime : r.Prime := by
      rcases fam with _ | _ | _ | _ | _ | _ <;> exact hlie.2.2.1
    haveI : Fact r.Prime := ⟨hrprime⟩
    have h4 := hN1 c.Lbar fam r f hlie hr
    simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h4
    rw [Ctx82E3.pRank_lbar c hr] at h4
    have h5 : CFSG.Open.pRank r c.L ≤ CFSG.Open.pRank r D.M :=
      CFSG.SectionRank.pRank_mono hrprime.one_lt c.hyp81.1
    have h6 := c.pRank_le_three hrprime hr
    omega
  subst hr2
  refine ⟨rfl, fun p hp => ?_⟩
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  exact h.lie3Survivor_of_ne_char hK7 hN2 hN3 hN4 hN5 hN6 hlie hp (c.conclusion76 hp)
    (h.mem_centralizer_of_isPGroup hK6c hlie (c.five_le_of_mem_sigma hp))

theorem Ctx82E3.lie3_final (c : Ctx82E3 D) (h : Case811Sylow c) (hK6c : K6c) (hK7 : K7)
    (hN1 : LieOddCharRank) (hN2 : LieL67PlusRank) (hN3 : K7cSharp) (hN4 : K7L67TwoSharp)
    (hN5 : K7L4Mech) (hN6 : K7L7TwoMech) (hSp6 : h.Sp6Excluded) {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 c.Lbar fam r f) :
    fam = .l6 ∧ r = 2 ∧ f = 1 ∧ D.sig = {7} := by
  obtain ⟨hr2, hsurv⟩ := c.lie3_exit h hK6c hK7 hN1 hN2 hN3 hN4 hN5 hN6 hlie
  subst hr2
  have hl6 : ∀ p ∈ D.sig, fam = .l6 ∧ f = 1 ∧ p = 7 := by
    intro p hp
    rcases hsurv p hp with ⟨hfam, hq, hC⟩ | hl6
    · subst hfam
      exact (hSp6 hlie hp hq hC).elim
    · exact hl6
  obtain ⟨p₀, hp₀⟩ := c.sig_nonempty
  obtain ⟨hfam, hf, hp7⟩ := hl6 p₀ hp₀
  refine ⟨hfam, rfl, hf, ?_⟩
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hp7 ▸ hp₀, fun p hp => (hl6 p hp).2.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
