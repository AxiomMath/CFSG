module

public import CFSG.RankThree.GF2n.Parrott.SpinRigidity
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentification

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}

theorem generatorConjugacy_of_agree_on_spinE27
    (h : Tim79a.ParrottHyp z) {hN : ((J z).subgroupOf (H z)).Normal}
    (D : QuotientData (z := z) hN) (P₀ : GL8)
    (hP : ∀ m ∈ spinE27, actionQA45 (z := z) h D m = P₀ * rhoA m * P₀⁻¹) :
    GeneratorConjugacy (z := z) h D := by
  let ρ : A45 →* GL8 := (MulAut.conj P₀⁻¹).toMonoidHom.comp (actionQA45 (z := z) h D)
  have hρ : ∀ m ∈ spinE27, ρ m = rhoA m := by
    intro m hm
    show P₀⁻¹ * actionQA45 (z := z) h D m * P₀⁻¹⁻¹ = rhoA m
    rw [hP m hm]
    group
  obtain ⟨P, hPρ⟩ := spinRep_rigid_of_forall ρ hρ
  have hall : ∀ a : A45,
      actionQA45 (z := z) h D a = (P₀ * P) * rhoAct (toQAct a) * (P₀ * P)⁻¹ := by
    intro a
    have h1 := hPρ a
    have h2 : ρ a = P₀⁻¹ * actionQA45 (z := z) h D a * P₀ := by
      show P₀⁻¹ * actionQA45 (z := z) h D a * P₀⁻¹⁻¹ = _
      rw [inv_inv]
    rw [← rhoA_apply a]
    rw [h2] at h1
    have h3 : actionQA45 (z := z) h D a =
        P₀ * (P₀⁻¹ * actionQA45 (z := z) h D a * P₀) * P₀⁻¹ := by
      group
    rw [h3, h1]
    group
  exact ⟨P₀ * P, hall x45A, hall y45A, hall f45A⟩

end CFSG.RankThree.GF2n.Parrott
