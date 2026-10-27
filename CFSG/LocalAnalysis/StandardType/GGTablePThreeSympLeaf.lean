module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSympDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeSympShape
import CFSG.LocalAnalysis.StandardType.GGTablePThreeSympCells
import CFSG.LocalAnalysis.StandardType.GGTablePThreeSympB2der

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section LeafCerts

private theorem sympSplit_of_tag_B_or_C {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (h : LargeEvenSplit 3 lab) :
    3 ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 := by
  obtain ⟨tag, rank, n⟩ := lab
  rcases htag with hB | hC
  · subst hB
    simp only [LargeEvenSplit, LargeEvenUntwisted] at h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact absurd trivial h
    · exact absurd h (by decide)
    · exact Or.inr h
  · subst hC
    simp only [LargeEvenSplit, LargeEvenUntwisted] at h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact absurd trivial h
    · exact absurd h (by decide)
    · exact Or.inr h

private theorem sympFrame {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 2) X A δ J) : ∃ n : ℕ, SympShapeConcl n A J ∧ 3 ^ 3 ≤ Nat.card A := by
  have hshape := sympShape_holds
  unfold DatumOn at hd
  dsimp only [fam] at hd
  obtain ⟨hK, huniq, h27, hmarkX⟩ := hd
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmarkX
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθP₀⟩ := hQ₀
  obtain ⟨-, hfam, -, -⟩ := hθP₀
  obtain ⟨tag, rank, n⟩ := lab
  rcases hfam with hB | hC | hB2
  · subst hB
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, hfieldK, hfiniteK, hcardK, hQ⟩ := hraw
    obtain ⟨-, -, hθP⟩ := hQ
    obtain ⟨θ, -, hsplit, hin⟩ := hθP
    letI := hfieldK
    letI := hfiniteK
    have hthree : 3 ∣ 2 ^ n - 1 ∨ n = 1 :=
      sympSplit_of_tag_B_or_C (lab := ⟨.B, rank, n⟩) (Or.inl rfl) hsplit
    exact ⟨n, hshape K n rank hcardK hthree X hcomm θ A δ J hK huniq h27 hin, h27⟩
  · subst hC
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, hfieldK, hfiniteK, hcardK, hQ⟩ := hraw
    obtain ⟨-, -, hθP⟩ := hQ
    obtain ⟨θ, -, hsplit, hin⟩ := hθP
    letI := hfieldK
    letI := hfiniteK
    have hthree : 3 ∣ 2 ^ n - 1 ∨ n = 1 :=
      sympSplit_of_tag_B_or_C (lab := ⟨.C, rank, n⟩) (Or.inr rfl) hsplit
    exact ⟨n, hshape K n rank hcardK hthree X hcomm θ A δ J hK huniq h27 hin, h27⟩
  · have hd2 : DatumOn (fun t => t = .B2der) X A δ J :=
      ⟨hK, huniq, h27, hcomm, ⟨tag, rank, n⟩, hlab,
        largeEvenRawDatum_mono
          (fun R _ I F hQ => by
            obtain ⟨hs, hna, hθP⟩ := hQ
            obtain ⟨θ, -, hs3, hin⟩ := hθP
            exact ⟨hs, hna, θ, hB2, hs3, hin⟩) hraw⟩
    exact absurd hd2 (sympB2der_noDatum X hcomm A δ J)

theorem leafSymp_holds :
    KnownOverSix (DatumOn (fam 2)) := by
  unfold KnownOverSix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    obtain ⟨n, hS, -⟩ := sympFrame hd
    exact sympCell_noG2 hS
  · intro X _ _ hX A δ J hd hmarkJ hZ
    obtain ⟨n, hS, -⟩ := sympFrame hd
    exact fun _ => absurd hZ (sympCell_noA2 hS hmarkJ)
  · intro X _ _ hX A δ J hd hmarkJ hZ
    obtain ⟨n, hS, -⟩ := sympFrame hd
    exact fun _ => absurd hmarkJ (sympCell_noTwA2 hS)
  · intro X _ _ hX A δ J hd hmarkJ
    obtain ⟨n, hS, -⟩ := sympFrame hd
    exact fun _ => absurd hmarkJ (sympCell_noTriD4 hS)
  · intro X _ _ hX A δ J hd hmarkJ
    obtain ⟨n, hS, -⟩ := sympFrame hd
    exact fun _ => absurd hmarkJ (sympCell_noD4Odd hS)
  · intro X _ _ hX A δ J hd hmarkJ
    obtain ⟨n, hS, h27⟩ := sympFrame hd
    exact absurd hmarkJ (sympCell_noA1 hS h27)

end LeafCerts

end CFSG.StandardType.TablePThreeKG

end
