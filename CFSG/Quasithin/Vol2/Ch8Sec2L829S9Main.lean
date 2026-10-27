module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN5
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.KG82CoverCore
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

theorem s9main_closure_image {G M : Type} [Group G] [Group M] {Λ : Subgroup G} (f : Λ →* M)
    (S : Set G) (hS : ∀ x ∈ S, x ∈ Λ) :
    ∀ g ∈ Subgroup.closure S, ∃ hg : g ∈ Λ,
      f ⟨g, hg⟩ ∈ Subgroup.closure {m : M | ∃ x ∈ S, ∃ hx : x ∈ Λ, m = f ⟨x, hx⟩} := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨hS x hx, Subgroup.subset_closure ⟨x, hx, hS x hx, rfl⟩⟩
  | one =>
    refine ⟨Λ.one_mem, ?_⟩
    have h1 : f ⟨1, Λ.one_mem⟩ = 1 := map_one f
    rw [h1]
    exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨Λ.mul_mem ha1 hb1, ?_⟩
    have e : f ⟨a * b, Λ.mul_mem ha1 hb1⟩ = f ⟨a, ha1⟩ * f ⟨b, hb1⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact Subgroup.mul_mem _ ha2 hb2
  | inv a _ ha =>
    obtain ⟨ha1, ha2⟩ := ha
    refine ⟨Λ.inv_mem ha1, ?_⟩
    have e : f ⟨a⁻¹, Λ.inv_mem ha1⟩ = (f ⟨a, ha1⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    exact Subgroup.inv_mem _ ha2

end CFSG.Quasithin.H13.L829N
