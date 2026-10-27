module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Cases
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4EmbLong
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4EmbLine
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4EmbSemi

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem sp4Sl2Emb_of_tis {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {A : Subgroup (StatedSp 2 F)}
    (hAZ : A ≤ unipotent 2 F ⊓ centralizer
      ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)))
    (hA4 : Nat.card ↥A = 4) (hT : TISIn (⊤ : Subgroup (StatedSp 2 F)) A) : Sp4Sl2Emb A := by
  have hX := sp4_tis_axes hF hAZ hA4 hT
  rcases sp4_cases_of_axes hF hAZ hA4 hX with ⟨b, c, hbc, hA'⟩ | ⟨b, hb, hA'⟩
  · by_cases hc : c = 0
    · apply sp4_emb_long hF
      intro g
      rw [hA' g]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t * b, by rw [ht, hc, mul_zero]⟩
      · rintro ⟨b', hb'⟩
        rcases hbc with hb0 | hc0
        · refine ⟨b' / b, ?_⟩
          rw [hb', hc, mul_zero, div_mul_cancel₀ b' hb0]
        · exact absurd hc hc0
    · exact sp4_emb_line hF b c hc hA'
  · exact sp4_emb_semi hF b hb hA'

theorem centralKData_unipotent_sp4 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {A : Subgroup (StatedSp 2 F)} (hAU : A ≤ unipotent 2 F)
    (hAc : A ≤ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)))
    (hA4 : Nat.card ↥A = 4) (hT : TISIn (⊤ : Subgroup (StatedSp 2 F)) A) :
    CentralKData (unipotent 2 F : Subgroup (StatedSp 2 F)) A := by
  have hAZ : A ≤ unipotent 2 F ⊓ centralizer
      ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) := le_inf hAU hAc
  obtain ⟨ι, hι, hAι, hTι⟩ := sp4Sl2Emb_of_tis hF hAZ hA4 hT
  have hU : IsPGroup 2 (unipotent 2 F : Subgroup (StatedSp 2 F)) :=
    IsPGroup.of_card (n := 8) (by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_unipotent, hF]
      norm_num)
  exact centralKData_of_sl2_embedding (S := unipotent 2 F) (A := A) hU hAU hF ι hι hAι hTι

end CFSG.LocalAnalysis.WeakClosure81

end
