module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofSporadic
public import CFSG.RankThree.PartTwo.Sec4.Item413Classical
public import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item223CensusProof

theorem census223Fact_projSp_two {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : 4 ≤ p ^ f) : Census223Fact (projSp 2 (GaloisField p f)) := by
  set F := GaloisField p f
  have hF : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out hp3 hF
  have hs : IsSimpleGroup (projSp 2 F) := by
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hF]; exact hq)))
    exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm.isSimpleGroup
  refine Or.inl (pRank_le_two_of_card_le_nine fun B hB =>
    Sec4.card_le_of_projImage _ hs (m := 2) (by norm_num)
      (fun c hc => Sec4.sq_of_scalar_mem_closure_sp (by norm_num) hc) (by norm_num)
      (fun P hPH hcomm hexp => ?_) B hB)
  have h := Sec4.card_sq_le_of_mem_closure_sp h3 P hPH hcomm hexp
  norm_num at h
  nlinarith

theorem card_projSp_two_two : Nat.card (projSp 2 (GaloisField 2 1)) = 720 :=
  CFSG.RankThree.PartTwo.Sec8.Item812Res2.card_projSp_two_one

theorem census223Fact_projSp_two_even {n : ℕ} (hn : 1 ≤ n) :
    Census223Fact (projSp 2 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    have : Finite (projSp 2 (GaloisField 2 1)) :=
      Nat.finite_of_card_ne_zero (by rw [card_projSp_two_two]; norm_num)
    exact census223Fact_of_not_dvd (by rw [card_projSp_two_two]; norm_num)
  · exact census223Fact_projSp_two (by norm_num) hn
      ((Nat.pow_le_pow_right (by norm_num) hn2).trans' (by norm_num))

theorem census223Fact_tits
    {X : Type} [Group X] {p f : ℕ}
    (h : Blueprint.ReeTitsModel X .Tits p f) : Census223Fact X := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X p f h
  have hX : Nat.card X = 17971200 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  exact census223Fact_of_card_dvd (N := 17971200) (b := 25) (by rw [hX]) (by norm_num)
    (by norm_num) (by decide)

end Item223CensusProof

open Item223CensusProof

@[expose] def Census223RankTwoOddRest : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    (∀ (X : Type) [Group X], Blueprint.ChevalleyExceptionalModel X .G2 p 1 →
      Census223Fact X) ∧
    (p % 3 = 1 → Census223Fact (projSU 4 p 1)) ∧
    (p % 3 = 2 → Census223Fact (projSL 4 (GaloisField p 1)))

theorem census223RankTwoOdd_of (h : Census223RankTwoOddRest) : Census223RankTwoOdd :=
  fun p _ hp3 => ⟨(h p hp3).1, census223Fact_projSp_two (by omega) le_rfl (by rw [pow_one]; omega),
    (h p hp3).2.1, (h p hp3).2.2⟩

@[expose] def Census223RankTwoEvenRest : Prop :=
  (∀ n : ℕ, 1 ≤ n → Even n → Census223Fact (projSU 4 2 n)) ∧
  (∀ (X : Type) [Group X] (f : ℕ),
    (Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
      Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f ∨
      Blueprint.ReeTitsModel X .twistedF4 2 f) →
    Census223Fact X)

theorem census223RankTwoEven_of
    (h : Census223RankTwoEvenRest) : Census223RankTwoEven := by
  refine ⟨fun _ hn => census223Fact_projSp_two_even hn, h.1, fun X _ f hX => ?_⟩
  rcases hX with hX | hX | hX | hX
  · exact h.2 X f (Or.inl hX)
  · exact h.2 X f (Or.inr (Or.inl hX))
  · exact h.2 X f (Or.inr (Or.inr hX))
  · exact census223Fact_tits hX

end CFSG.RankThree.PartTwo.Sec21
