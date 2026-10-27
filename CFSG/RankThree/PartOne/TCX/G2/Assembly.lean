module

public import CFSG.RankThree.PartOne.TCX.G2.Group
public import CFSG.RankThree.PartOne.TCX.G2.StdForm
public import CFSG.RankThree.PartOne.TCX.AssemblyTools
public import CFSG.RankThree.PartOne.TCX.Transport
public import CFSG.RankThree.PartOne.TCX.ParabolicConj
public import CFSG.RankThree.PartOne.TCX.Interface
public import CFSG.RankThree.PartOne.S11c.Sec66PSUFrame

public section

namespace CFSG.RankThree.PartOne.TCX.G2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.PartOne.KLC (map_centralizer_singleton_mulEquiv' pRank_congr_mulEquiv
  StdForm)

open CFSG.RankThree.PartOne.TCX

section Main


theorem g2_stdForm {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n f₀ : ℕ}
    (hf₀ : 1 ≤ f₀) (hM : LieModel T .G2 n 2 (p * f₀)) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K) (φ : T ≃* adjointGroup Tag.G2 K),
      Nat.card K = 2 ^ (p * f₀) ∧ orderOf σ = p ∧
        MulAut.congr φ α = entrywiseAdjointAut Tag.G2 σ := by
  obtain ⟨hn, -⟩ := CFSG.RankThree.PartOne.KLC.chevalleyModel_of_lieModel (by decide) hM
  subst hn
  exact stdForm_G2 T p f₀ hp hp5 hf₀ hM α hαp hαinn

theorem threeCompT_G2 : ThreeCompT .G2 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, σ, φ, hKcard, hσord, hφα⟩ := g2_stdForm hp hp5 hf₀ hM hαp hαinn
  have hφα' : ∀ t, entrywiseAdjointAut Tag.G2 σ (φ t) = φ (α t) := fun t => by
    rw [← hφα]
    simp [MulAut.congr_apply]
  have hxGp : φ x ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hxG1 : φ x ≠ 1 := fun h => hx1 (φ.injective (by rw [h, map_one]))
  have hxGσ : entrywiseAdjointAut Tag.G2 σ (φ x) = φ x := by rw [hφα', hαx]
  have hprG : 2 ≤ CFSG.pRank p (adjointGroup Tag.G2 K) := by
    rw [← pRank_congr_mulEquiv φ hp.one_lt]
    exact hpr
  have hcases := g2_group_cases hp hp5 hf₀ hKcard hσord hprG hxGp hxG1 hxGσ
  have hplaneF : ¬ (∃ R U : Subgroup (adjointGroup Tag.G2 K),
        IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
          (∀ r ∈ R, entrywiseAdjointAut Tag.G2 σ r = r) ∧ U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
          (∀ u ∈ U, entrywiseAdjointAut Tag.G2 σ u ∈ U) ∧
          R ≤ Subgroup.normalizer (U : Set (adjointGroup Tag.G2 K))) := by
    rintro ⟨R, U, hR, hRc, hRfix, hU, hU2, hUα, hRU⟩
    have hLRG := localRankAut_congr φ hp hLRA
    rw [hφα] at hLRG
    have hαp' : entrywiseAdjointAut Tag.G2 σ ^ p = 1 := by rw [← hφα, ← map_pow, hαp, map_one]
    have hout : entrywiseAdjointAut Tag.G2 σ ∉ innerAut (adjointGroup Tag.G2 K) := by
      rw [← hφα]
      exact fun h => hαinn ((mem_innerAut_congr φ α).mp h)
    exact hLRG hαp' hout R hR hRc hRfix U hU hU2 hUα hRU
  have hcases' := hcases.resolve_left hplaneF
  refine ⟨fun D hD hDst => ?_, fun S hS hS2 hSα hxS => ?_⟩
  · rcases hcases' with ⟨hab, -⟩ | hlay
    · exact (no_component_of_comm (centralizer_comm_of_map φ hab) hD).elim
    · have hlay' : SingleLayerData p (entrywiseAdjointAut Tag.G2 σ)
          ((Subgroup.centralizer ({x} : Set T)).map φ.toMonoidHom) := by
        rw [map_centralizer_singleton_mulEquiv']
        exact hlay
      obtain ⟨D₀, hD₀, hst, huniq, hfix, hclaims⟩ :=
        singleLayerData_of_mulEquiv (p := p) φ hφα' hlay'
      have hDD₀ := huniq D hD
      subst hDD₀
      exact hclaims
  · rcases hcases' with ⟨hab, N, hN, hexp⟩ | hlay
    ·
      exfalso
      have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two (Nat.mul_pos hp.pos hf₀) hKcard
      have hxGord : orderOf (φ x) = p := orderOf_eq_prime hxGp hxG1
      have hSG : S.map φ.toMonoidHom ≠ ⊥ := fun hbot =>
        hS ((Subgroup.map_eq_bot_iff_of_injective S φ.injective).mp hbot)
      obtain ⟨z, hz, hzo⟩ := exists_centralizer_elt_orderOf_of_normalizes (r := 2)
        (fun a => CFSG.RankThree.PartOne.KFU.rootDiagUnit_mem_adjointGroup_g2 a) hp (by omega)
        hxGord hSG (hS2.map φ.toMonoidHom) (normalizer_map_of_mem φ hxS)
      exact hN (by rw [← hzo]; exact orderOf_dvd_of_pow_eq_one (hexp z hz))
    · have hlay' : SingleLayerData p (entrywiseAdjointAut Tag.G2 σ)
          ((Subgroup.centralizer ({x} : Set T)).map φ.toMonoidHom) := by
        rw [map_centralizer_singleton_mulEquiv']
        exact hlay
      obtain ⟨D₀, hD₀, hst, huniq, hfix, -⟩ := singleLayerData_of_mulEquiv (p := p) φ hφα' hlay'
      exact ⟨D₀, hD₀, hst, huniq, hfix⟩

end Main

end CFSG.RankThree.PartOne.TCX.G2
