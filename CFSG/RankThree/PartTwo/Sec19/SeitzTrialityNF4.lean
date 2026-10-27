module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF3
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4G2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19

section Model


variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem gsub_eq_range_g2Incl (hK : ringChar X = 2) :
    (KFacts.trialityG2Incl σ hK).range = Gsub σ := by
  ext g
  rw [KFacts.mem_range_trialityG2Incl_iff σ hK]
  rfl

theorem gsub_three_conj (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x : C0 σ}
    (hx : x ∈ Gsub σ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ g ∈ Gsub σ, g * x * g⁻¹ ∈ A0sub σ ∨ g * x * g⁻¹ ∈ Bsub σ := by
  have hn1 : 1 ≤ n := by omega
  have hchar : CharP X 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := n * 3) (by omega) (by rw [hX, pow_mul])
  have hK : ringChar X = 2 := ringChar.eq X 2
  have hkc : Nat.card (fixSubfield σ) = 2 ^ n := KFacts.card_fixSubfield_of_cube hn1 hX hσ
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hkc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3k : ringChar (fixSubfield σ) ≠ 3 := by
    intro h
    have h3 : (3 : fixSubfield σ) ≠ 0 := three_ne_zero_fixSubfield σ (three_ne_zero_of_cube n hn1 hX)
    have h30 : ((3 : ℕ) : fixSubfield σ) = 0 := (ringChar.spec (fixSubfield σ) 3).mpr (by rw [h])
    exact h3 (by exact_mod_cast h30)
  obtain ⟨w, hwS, hwL⟩ := g2_pair_conj_AB σ ⟨hn1, hX, hσ⟩ hK hk4
  have hxr : x ∈ (KFacts.trialityG2Incl σ hK).range := by
    rw [gsub_eq_range_g2Incl σ hK]; exact hx
  obtain ⟨y, rfl⟩ := hxr
  have hinj := KFacts.trialityG2Incl_injective σ hK
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hx3, map_one])
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨c, hc⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds (fixSubfield σ) h3k hk4 y hy3 hy1
  refine ⟨KFacts.trialityG2Incl σ hK (w * c), ?_, ?_⟩
  · rw [← gsub_eq_range_g2Incl σ hK]; exact ⟨_, rfl⟩
  · have key : KFacts.trialityG2Incl σ hK (w * c) * KFacts.trialityG2Incl σ hK y *
        (KFacts.trialityG2Incl σ hK (w * c))⁻¹ =
        KFacts.trialityG2Incl σ hK (w * (c * y * c⁻¹) * w⁻¹) := by
      simp only [map_mul, map_inv]
      group
    rw [key]
    rcases hc with hc | hc
    · left
      exact hwS ⟨_, ⟨_, hc, rfl⟩, rfl⟩
    · right
      exact hwL ⟨_, ⟨_, hc, rfl⟩, rfl⟩

theorem plane_through_tau (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x g : C0 σ} {e : ℕ}
    (he : e = 1 ∨ e = 2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hβ3 : (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1)
    (hcomm : Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e)) (hG : HasGLine σ x g e) :
    ∃ (φ : MulAut (C0 σ)), φ x ∈ Gsub σ ∧ (φ x) ^ 3 = 1 ∧ φ x ≠ 1 ∧
      (Subgroup.closure ({MulAut.conj x, MulAut.conj g * tauAut σ ^ e} :
          Set (MulAut (C0 σ)))).map (MulAut.congr φ).toMonoidHom =
        Subgroup.closure ({MulAut.conj (φ x), tauAut σ} : Set (MulAut (C0 σ))) := by
  have hn1 : 1 ≤ n := by omega
  have hinj := conj_injective_C0 σ n hn1 hX hσ
  obtain ⟨φ, i, hφ⟩ := hG
  set β : MulAut (C0 σ) := MulAut.conj g * tauAut σ ^ e with hβ
  set x' : C0 σ := φ x with hx'
  set β' : MulAut (C0 σ) := φ * β * φ⁻¹ with hβ'
  have hcx : φ * MulAut.conj x * φ⁻¹ = MulAut.conj x' := aut_conj_conj φ x
  have hτs : β' * MulAut.conj x' ^ i = tauAut σ ∨ β' * MulAut.conj x' ^ i = (tauAut σ)⁻¹ := by
    have h1 : β' * MulAut.conj x' ^ i = φ * (β * MulAut.conj x ^ i) * φ⁻¹ := by
      rw [← hcx, conj_pow, hβ']
      group
    rw [h1]
    exact hφ
  have hE : (Subgroup.closure ({MulAut.conj x, β} : Set (MulAut (C0 σ)))).map
      (MulAut.congr φ).toMonoidHom = Subgroup.closure ({MulAut.conj x', β'} : Set (MulAut (C0 σ))) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, congr_apply_eq, hcx]
    rfl
  have hcomm' : Commute (MulAut.conj x') β' := by
    have := hcomm.map (MulAut.congr φ).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom, congr_apply_eq, hcx] using this
  have hcτ : Commute (MulAut.conj x') (tauAut σ) := by
    have hc2 : Commute (MulAut.conj x') (β' * MulAut.conj x' ^ i) :=
      hcomm'.mul_right ((Commute.refl _).pow_right i)
    rcases hτs with h | h
    · rwa [h] at hc2
    · rw [h] at hc2
      exact (Commute.inv_right_iff.mp hc2)
  have hτx' : tauAut σ x' = x' := by
    apply hinj
    rw [← aut_conj_conj, ← hcτ.eq]
    group
  refine ⟨φ, hτx', ?_, ?_, ?_⟩
  · show (φ x) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  · intro h
    exact hx1 (φ.injective (by rw [h, map_one]))
  · rw [hE]
    exact closure_pair_eq_of_mul_pow _ _ _ i hτs

theorem outer_G_case (hAB : TrialityABFacts σ) (n : ℕ) (hn : 2 ≤ n)
    (hX : Nat.card X = (2 ^ n) ^ 3) (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) {x g : C0 σ} {e : ℕ}
    (he : e = 1 ∨ e = 2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hβ3 : (MulAut.conj g * tauAut σ ^ e) ^ 3 = 1)
    (hcomm : Commute (MulAut.conj x) (MulAut.conj g * tauAut σ ^ e)) (hG : HasGLine σ x g e) :
    ∃ (ψ : MulAut (C0 σ)) (a : C0 σ), (a ∈ A0sub σ ∨ a ∈ Bsub σ) ∧ a ^ 3 = 1 ∧ a ≠ 1 ∧
      (Subgroup.closure ({MulAut.conj x, MulAut.conj g * tauAut σ ^ e} :
          Set (MulAut (C0 σ)))).map (MulAut.congr ψ).toMonoidHom =
        Subgroup.closure ({MulAut.conj a, tauAut σ} : Set (MulAut (C0 σ))) := by
  obtain ⟨φ, hxG, hx'3, hx'1, hE⟩ := plane_through_tau σ hAB n hn hX hσ he hx3 hx1 hβ3 hcomm hG
  obtain ⟨g₂, hg₂G, hg₂⟩ := gsub_three_conj σ hAB n hn hX hσ hxG hx'3 hx'1
  have hτg₂ : tauAut σ g₂ = g₂ := hg₂G
  have hcg : MulAut.conj g₂ * tauAut σ = tauAut σ * MulAut.conj g₂ := by
    have := aut_conj_conj (tauAut σ) g₂
    rw [hτg₂] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  refine ⟨MulAut.conj g₂ * φ, g₂ * φ x * g₂⁻¹, hg₂, ?_, ?_, ?_⟩
  · rw [conj_pow, hx'3]
    group
  · intro h
    apply hx'1
    have : φ x = g₂⁻¹ * (g₂ * φ x * g₂⁻¹) * g₂ := by group
    rw [this, h]
    group
  · have hτ : (MulAut.congr (MulAut.conj g₂)).toMonoidHom (tauAut σ) = tauAut σ := by
      rw [MulEquiv.coe_toMonoidHom, congr_apply_eq, hcg, mul_assoc, mul_inv_cancel, mul_one]
    rw [congr_mul_toMonoidHom, ← Subgroup.map_map, hE, MonoidHom.map_closure, Set.image_pair,
      congr_conj_conj, hτ]

end Model

end CFSG.RankThree.PartTwo.Sec19
