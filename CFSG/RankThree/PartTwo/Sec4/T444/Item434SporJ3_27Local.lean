module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInv

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporJ3

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.J3Sylow
  CFSG.AGLEmbedding.KFactProofs.J3OuterInv CFSG.Quasithin CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_outerSetup
    (hOR : KFactJ3OuterRank) (J : Type) [Group J] [Finite J]
    (hJ : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    ∃ (S : Sylow 3 J) (Z : Subgroup J) (φ : MulAut J), OuterSetup J (S : Subgroup J) Z φ := by
  obtain ⟨-, hover⟩ := j3CoverFacts J hJ
  obtain ⟨hOut, hrk⟩ := hOR J hJ
  obtain ⟨eJ⟩ := hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let f := eJ.trans b.symm
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsimple : IsSimpleGroup J := MulEquiv.isSimpleGroup (H := Blueprint.NativeSporadic.J3) f
  have hJcard : Nat.card J = 50232960 := by
    rw [Nat.card_congr f.toEquiv]; exact CFSG.Sporadic.J3.card_J3
  obtain ⟨PJS, φ, hφT, hφout, hcent, hfinal⟩ := outer_check J ⟨eJ⟩ hsimple hJcard
  have hF : J3SylowFacts J (PJS : Subgroup J) := kFactJ3Sylow J ⟨eJ⟩ PJS
  have hnonab : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, -, y, -, hxy⟩ := hF.nonabelian
    exact ⟨x, y, hxy⟩
  have hsetup : OuterSetup J (PJS : Subgroup J) (centerOf (PJS : Subgroup J)) φ :=
    { cen := fun z hz => by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
        · have : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g => hz g
          rwa [h, Subgroup.mem_bot] at this
        · obtain ⟨x, y, hxy⟩ := hnonab
          have hx : x ∈ Subgroup.center J := h ▸ Subgroup.mem_top x
          exact absurd (Subgroup.mem_center_iff.1 hx y).symm hxy
      overgroup := hover PJS
      Zc := fun z hz x hx => (mem_centerOf.1 hz).2 x hx
      Zcomm := by
        have := hF.center_elem.1.1
        exact this
      Z3 := hF.center_elem.1.2
      Z9 := hF.center_elem.2
      rank := by
        rintro ⟨W, hW1, hW2, hW3⟩
        have h4 : 4 ≤ Open.pRank 3 (⊤ : Subgroup J) :=
          le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three _)
            ⟨W, le_top, ⟨hW1, hW2⟩, by rw [hW3]; norm_num⟩
        omega
      cent := hcent
      out := fun β γ hβ hγ => outer_mul_inv_mem hOut hβ hγ
      phiT := hφT
      phiOut := hφout
      final := hfinal }
  exact ⟨PJS, centerOf (PJS : Subgroup J), φ, hsetup⟩

end CFSG.RankThree.PartTwo.Sec4.Item434SporJ3
