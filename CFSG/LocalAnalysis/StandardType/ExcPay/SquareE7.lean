module

public import CFSG.LocalAnalysis.StandardType.ExcPay.SquareGen
public import CFSG.LocalAnalysis.StandardType.ExcPay.SquareModelE7
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.LocalAnalysis.StandardType.ExcPay.ModelE7
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem exists_excPaySquare_E7_of_model {G : Type} [Group G] [Finite G] {p f : ℕ}
    {Bs X : Subgroup G} {ht : GGExcFive .E7} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hinn : ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G) ∧
      ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (M : GGDatumModel .E7 f p ht) (η : ↥X ≃* ↥M.D.Γ)
    (hη : ∀ z : ModGL (langTag .E7) GGL,
      (∃ x : ↥X, (x : G) ∈ Bs ∧ (η x : ModGL (langTag .E7) GGL) = z) ↔
        ∃ a : Fin (langTag .E7).rank → GGLˣ, (∀ i, a i ^ p = 1) ∧
          rootDiagUnit (langTag .E7) a = z) :
    Nonempty (ExcPaySquare .E7 ht f p Bs X) := by
  classical
  have hZ : Subgroup.center ↥X = ⊥ := by
    have hmap := Subgroup.map_center_eq κ
    rw [← hmap, center_adjointGroup_eq_bot (τ := .E7) (K := GaloisField 2 f),
      Subgroup.map_bot]
  obtain ⟨hsplit, -⟩ := excPay_inner_split hBs hSC hZ (fun b hb => (hinn b hb).2)
  have hnk : ∀ k, canonicalRep (coxeterSystem (langTag .E7)) GGL (simple (langTag .E7) k) ∈
      M.D.Γ := by
    intro k
    rw [datumModel_Γ_eq_model_E7 hf M]
    exact canonicalRep_simple_mem_model_E7 hp2 hplus M k
  obtain ⟨S, -⟩ :=
    exists_excPaySquare_of_model (t := .E7) (ht := ht) hp hp2
      M η hη hsplit hZ hnk
  exact ⟨S⟩

theorem exists_excPaySquare_E7 {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs X : Subgroup G}
    {ht : GGExcFive .E7} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hplus : p ∣ 2 ^ f + 1)
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hinn : ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G) ∧
      ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    Nonempty (ExcPaySquare .E7 ht f p Bs X) := by
  obtain ⟨M, η, hη⟩ := exists_excPayModel_E7 (ht := ht) hp hp5 hf hplus hBs hSC κ hinn
  exact exists_excPaySquare_E7_of_model hp (by omega) hf hplus hBs hSC κ hinn M η hη

theorem exists_excPaySquare_E7_of_toral {G : Type} [Group G] [Finite G] {p f : ℕ}
    {Bs X : Subgroup G} {ht : GGExcFive .E7} (hp : p.Prime) (hp3 : 3 ≤ p) (hf : 1 ≤ f)
    (hplus : p ∣ 2 ^ f + 1) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (κ : ↥(adjointGroup .E7 (GaloisField 2 f)) ≃* ↥X)
    (hinn : ∀ b ∈ Bs, b ∈ Subgroup.normalizer (X : Set G) ∧
      ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hinf : p ^ 7 ≤ Nat.card ↥(X ⊓ Bs : Subgroup G))
    (htor : ∀ A : Subgroup (ModGL (langTag .E7) GGL), A ≤ ggFixGp .E7 f → IsElemAbelian p A →
      p ^ 7 ≤ Nat.card A → IsToralSubgroup .E7 GGL A) :
    Nonempty (ExcPaySquare .E7 ht f p Bs X) := by
  obtain ⟨M, η, hη⟩ :=
    exists_excPayModel_E7_of_toral (ht := ht) hp hp3 hf hplus hBs κ hinf htor
  exact exists_excPaySquare_E7_of_model hp (by omega) hf hplus hBs hSC κ hinn M η hη

end CFSG.StandardType.ExcPay
