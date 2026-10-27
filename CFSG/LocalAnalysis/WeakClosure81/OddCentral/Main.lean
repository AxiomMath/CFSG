module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.LeCenterOfFrame
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.LeCenterOrFrame

public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK


theorem sevenSevenOddCentral (G : Type) [Group G] [Finite G] : SevenSevenOddCentral G := by
  intro V H E h X _ φ hφ hS Y _ ι hι hVle hone n hn hL
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  haveI : Finite Y := Finite.of_injective ι hι
  have hSne : barSub (kSub V H E) φ V ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (⊥ : Subgroup X) = 1 := by simp
    rw [hbot, h1] at hS
    norm_num at hS
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  obtain ⟨s, hs⟩ := hVle v.2
  have hsV : ι s ∈ barSub (kSub V H E) φ V := hs ▸ v.2
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hv1 (Subtype.ext (by simpa using hs.symm))
  have hncl := hone s hsV hs1
  have hD := OddCentral.isOddTransp_of_embedding G h hφ hS hι hsV hs1
  rcases OddCentral.le_center_or_frame hD hncl hn hL with hle | ⟨rfl, d₁, d₂, d₃, t, hF⟩
  · exact hle
  · exact le_center_of_frame G h hφ hS hι hsV hs1 hncl hL hF
      (fun A B hA hB hBA hAR hmin hmove =>
        OddCentral.propositionS hD hncl hL hF hA hB hBA hAR hmin hmove)

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
