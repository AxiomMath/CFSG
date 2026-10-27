module

public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.StandardType.GGCompFieldCatalogue
public import CFSG.LocalAnalysis.StandardType.GGE0ChevStMarking

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggTwE6CompFieldInputQ_general
    (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut ↥(twistedE6RootGroup K σ))
    (hα : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hαp : α ^ p = 1)
    (X : Subgroup ↥(twistedE6RootGroup K σ))
    (hX : CFSG.Open.IsComponentOf X
      (CFSG.StandardType.LayerSixE.autFix (Subgroup.zpowers α))) :
    GGCompFieldDataQ (2 ^ f) X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q₀ : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
  have hq₀ : q₀.card = 2 ^ f := TauCeti.PrimePower.card_def q₀
  have hv : (TauCeti.LieTypeIndex.twistedE6 q₀).Valid :=
    TauCeti.LieTypeIndex.valid_twistedE6 q₀
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_twistedE6_of_field q₀ hv
    K (by rw [hq₀, hK]) σ (fun c => by rw [hq₀]; exact hσ c)
  have hC : commutator (twistedE6RootGroup K σ) = ⊤ :=
    commutator_twistedE6RootGroup_eq_top Nat.prime_two hf hK σ hσ
  have hle := CFSG.HardMathSupport.Dickson.Sec6.I923.twistedE6Inndiag_le_commutator σ hK hσ hC
  have hβ : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      ↥(twistedE6RootGroup K σ) :=
    CFSG.ComponentClassification.OuterAutomorphisms.commutator_le_innAutDerived _ (hle hα)
  rw [LayerSixE.autFix_zpowers_eq] at hX
  have hres := ggCompFieldDataQ_of_catalogue (S := ↥(twistedE6RootGroup K σ)) ⟨_, hv⟩
    (TauCeti.LieTypeIndex.characteristic_twistedE6 q₀) (fun h => h) hq₀ e.symm hp hp2 hβ hαp hX
  rw [show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize
      (TauCeti.LieTypeIndex.twistedE6 q₀) = 2 ^ f from hq₀] at hres
  exact hres

theorem excNoSuzukiReeTwE6_holds
    : ExcNoSuzukiReeTwE6 := by
  intro f K _ _ hf hK σ hσ p β hp hp2 _ hβp hβmem X hX hm
  have hX' : CFSG.Open.IsComponentOf X (LayerSixE.autFix (Subgroup.zpowers β)) := by
    rw [LayerSixE.autFix_zpowers_eq]
    exact CFSG.Assembly.isComponentOf_iff_open.1 hX
  exact ggChevStMarking_of_compFieldDataQ
    (ggTwE6CompFieldInputQ_general f hf K hK σ hσ p hp hp2 β hβmem hβp X hX') hm

end CFSG.StandardType