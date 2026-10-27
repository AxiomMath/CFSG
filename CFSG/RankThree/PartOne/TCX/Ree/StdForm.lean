module

public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.PartOne.S11d.FixedFacts

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)


theorem stdForm_twistedF4 {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .twistedF4 n 2 (p * f₀)) {α : MulAut T}
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime) (σ : K ≃+* K)
      (φ : T ≃* F4.reeGamma K a), 1 ≤ a ∧ Nat.card K = 2 ^ (2 * a + 1) ∧
        2 * a + 1 = p * f₀ ∧ (∀ c, σ c = c ^ 2 ^ f₀) ∧ orderOf σ = p ∧
        Subgroup.zpowers (MulAut.congr φ α) = Subgroup.zpowers (F4.reeGammaFieldAut K a σ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hn0, hR⟩ := lieModel_twistedF4_iff.mp hM
  subst hn0
  obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨e⟩⟩ := reeF4_model_data hR
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have : Finite (F4.reeGamma K a) := Finite.of_equiv T e.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (F4.reeGamma K a) := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [← hα'ord]; exact pow_orderOf_eq_one α'
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := RF4.largeReeFieldAutCoset a ha K hK p hp hp5 β hβord α' hα'p ⟨x, hxβ⟩
  set ψ : MulAut (F4.reeGamma K a) := (MulAut.conj g)⁻¹ with hψdef
  have hψ : ψ * MulAut.congr e α * ψ⁻¹ = F4.reeGammaFieldAut K a β := by
    have : MulAut.congr e α = MulAut.conj g * F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹ := hg
    rw [hψdef, this]
    group
  have hff : 2 * a + 1 = p * f₀ := by
    rw [hfa]
  obtain ⟨σ, hσ, hzp⟩ := exists_canonical_generator (f := 2 * a + 1) (p := p) (f' := f₀)
    (by omega) hK hβord hp.pos hff
  have hσord : orderOf σ = p := by
    have h1 : Nat.card (Subgroup.zpowers β) = p := by rw [Nat.card_zpowers, hβord]
    rw [hzp, Nat.card_zpowers] at h1
    exact h1
  refine ⟨a, K, inferInstance, inferInstance, inferInstance, σ, e.trans ψ, ha, hK, hff, hσ,
    hσord, ?_⟩
  have h2 : MulAut.congr (e.trans ψ) α = F4.reeGammaFieldAut K a β := hψ
  rw [h2]
  have h4 : ∀ ε : K ≃+* K, Subgroup.zpowers (F4.reeGammaFieldAut K a ε) =
      (Subgroup.zpowers ε).map (F4.reeGammaFieldAutHom K a) := fun ε =>
    (MonoidHom.map_zpowers (F4.reeGammaFieldAutHom K a) ε).symm
  rw [h4 β, h4 σ, hzp]

end CFSG.RankThree.PartOne.TCX.Ree
