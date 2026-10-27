module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.PartOne.RF4.FinalSec66

public section

namespace CFSG.RankThree.PartOne.TCF

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

theorem exists_twoExc_model {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .twistedF4 0 2 p) (α : MulAut T) (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime)
      (β : K ≃+* K) (φ : T ≃* ReeTag.F4.reeGamma K a),
      1 ≤ a ∧ p = 2 * a + 1 ∧ Nat.card K = 2 ^ (2 * a + 1) ∧ orderOf β = p ∧
      MulAut.congr φ α = ReeTag.F4.reeGammaFieldAut K a β ∧ Nat.card (fixSubfield β) = 2 ∧
      ∃ (_ : CharP (fixSubfield β) ReeTag.F4.prime),
        Nonempty (↥(fixSub (ReeTag.F4.reeGammaFieldAut K a β)) ≃*
          ReeTag.F4.reeGamma (fixSubfield β) 0) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hM' : ReeTitsModel T .twistedF4 2 p := (lieModel_twistedF4_iff.mp hM).2
  obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨e⟩⟩ := reeF4_model_data hM'
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv T e.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (ReeTag.F4.reeGamma K a) := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [← hα'ord]; exact pow_orderOf_eq_one α'
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := RF4.largeReeFieldAutCoset a ha K hK p hp hp5 β hβord α' hα'p ⟨x, hxβ⟩
  set ψ : MulAut (ReeTag.F4.reeGamma K a) := (MulAut.conj g)⁻¹ with hψdef
  have hψ : ψ * MulAut.congr e α * ψ⁻¹ = ReeTag.F4.reeGammaFieldAut K a β := by
    have : MulAut.congr e α =
        MulAut.conj g * ReeTag.F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹ := hg
    rw [hψdef, this]
    group
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := reeF4_fixed_data ha hK hp (by omega) hβord
  have hb0 : b = 0 := by
    have h1 : (2 * b + 1) * p = 1 * p := by rw [one_mul, hbp, hfa]
    have h2 := Nat.eq_of_mul_eq_mul_right hp.pos h1
    omega
  subst hb0
  refine ⟨a, K, inferInstance, inferInstance, inferInstance, β, e.trans ψ, ha, hfa, hK, hβord,
    hψ, ?_, hchar, ⟨eC⟩⟩
  simpa using hbcard

end CFSG.RankThree.PartOne.TCF
