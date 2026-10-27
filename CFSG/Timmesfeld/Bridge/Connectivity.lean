module

public import CFSG.Timmesfeld.Closure.Bender
public import CFSG.Timmesfeld.Moufang.Exceptional

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld.Connectivity

@[expose] def Asc73Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hN : IsNormalSet D),
    IsRootInvolutionSet D → Subgroup.closure D = ⊤ → Moufang.NoPolar D → Disconnected D →
      ∀ d ∈ D, BenderSuzuki.IsStronglyEmbeddedOrder (compStab hN d)

@[expose] def DisconnectedNoPolarInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (hS : Setting D), Disconnected D → IsSimpleGroup G →
    ker hS.normal = ⊥ →
    (∀ L : Subgroup G, L ≠ ⊤ → ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → d ∈ L → e ∈ L →
      L ≤ compStab hS.normal d) →
    Moufang.NoPolar D

theorem strongEmbeddingInput_of_asc73 (hA : Asc73Input) (hP : DisconnectedNoPolarInput) :
    StrongEmbeddingInput.{0} := by
  intro G _ D hS hdisc hsimp hfaith hM2 d hd
  have := hS.finite
  exact hA G D hS.normal hS.root hS.gen (hP G D hS hdisc hsimp hfaith hM2) hdisc d hd

theorem simpleCaseInput_of_asc73 (hA : Asc73Input) (hP : DisconnectedNoPolarInput) :
    SimpleCaseInput.{0} :=
  simpleCaseInput_of_strongEmbedding (strongEmbeddingInput_of_asc73 hA hP)

theorem commConnected_of_asc73 (hA : Asc73Input) (hP : DisconnectedNoPolarInput) {G : Type}
    [Group G] {D : Set G} (h : Hyp G D) : Closure.CommConnected D :=
  commConnected_of_strongEmbedding (strongEmbeddingInput_of_asc73 hA hP) h

end CFSG.Timmesfeld.Bridge
