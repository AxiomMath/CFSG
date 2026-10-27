module

public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.Config
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.BarTriple
public import CFSG.Quasithin.Background.F7TwoInvSz
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81.SevenK


theorem sevenSevenTwoInput_holds (G : Type) [Group G] [Finite G] : SevenSevenTwoInput G := by
  intro V H E h X _ φ hφ hV2 hodd n hn hSz
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  obtain ⟨a, -, hB⟩ := CFSG.Quasithin.F7Two.benderType_of_suzukiModel hSz
  have hne : barSub (kSub V H E) φ V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hV2
    omega
  obtain ⟨t, htV, ht1⟩ : ∃ t ∈ barSub (kSub V H E) φ V, t ≠ 1 := by
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨t, t.2, fun h1 => ht (Subtype.ext h1)⟩
  have ht : t * t = 1 := OddCentral.mul_self_of_mem_card_two hV2 htV
  obtain ⟨v, hvV, rfl⟩ := mem_barSub.mp htV
  obtain ⟨c₂, c₃, g, hT⟩ :=
    exists_szBarTriple (pCore_eq_bot_of_isBarMap hφ) hodd hB ht ht1
  obtain ⟨k₂, rfl⟩ := hφ.surjective c₂
  obtain ⟨k₃, rfl⟩ := hφ.surjective c₃
  exact false_of_szBarTriple h hφ hV2 hvV hT

theorem sevenSevenTwoInput_forall :
    ∀ (X : Type) [Group X] [Finite X], SevenSevenTwoInput X :=
  fun X _ _ => sevenSevenTwoInput_holds X

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
