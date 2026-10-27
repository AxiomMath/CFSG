module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3Cov
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3Sylow

public section

namespace CFSG.AGLEmbedding

open KFactProofs.J3Sylow CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen CFSG.Quasithin

theorem kFactJ3Cover :
    ∀ (J : Type) [Group J] [Finite J], Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
      ∀ T : Sylow 3 J, ∃ s : J, J3CoverFacts (T : Subgroup J) (centerOf (T : Subgroup J)) s := by
  intro J _ _ ⟨eJ⟩ T
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let f := eJ.trans b.symm
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsimple : IsSimpleGroup J := MulEquiv.isSimpleGroup (H := Blueprint.NativeSporadic.J3) f
  have hJcard : Nat.card J = 50232960 := by
    rw [Nat.card_congr f.toEquiv]; exact CFSG.Sporadic.J3.card_J3
  obtain ⟨H, t₁, t₂, s, Z, w₁, w₂, hT, -, D⟩ := sylow_check J ⟨eJ⟩ hsimple hJcard T
  have hfacts := D.coverFacts
  rw [hT] at hfacts
  exact ⟨s, hfacts⟩

end CFSG.AGLEmbedding
