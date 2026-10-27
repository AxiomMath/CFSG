module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCenterT
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocOrient

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open scoped commutatorElement
open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin

set_option linter.unusedSectionVars false


section Commutator

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem comm_x1_mem_Zz {a b c d e f : K} (hb : σ b = b)
    (h : ⁅d4x₁ K σ a, d4v K σ b c d e f⁆ ∈ d4Zz K σ) :
    b * a = 0 ∧ b * (σ a * σ (σ a)) + (σ a * σ (σ c) + σ (σ a) * σ c) = 0 ∧
      b * (a * σ a * σ (σ a)) + ((σ a * σ (σ a) * c + σ (σ a * σ (σ a) * c) +
        σ (σ (σ a * σ (σ a) * c))) + (a * d + σ (a * d) + σ (σ (a * d)))) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨F, hF⟩ := d4x₁_conj_d4v σ hσ a b c d e f hb
  obtain ⟨f', hf'⟩ := (NFq.mem_Zg_iff σ hσ).1 h
  rw [commutatorElement_def, hF, d4v_inv σ hσ, d4v_mul σ hσ, ← NFq.x6_eq_vmk,
    d4x₆_eq_d4v σ] at hf'
  obtain ⟨-, h3, h4, h5, -⟩ := d4v_injective σ hf'
  refine ⟨?_, ?_, ?_⟩
  · have : b * a = 0 := by linear_combination h3 - c * h2
    exact this
  · linear_combination h4 - d * h2
  · linear_combination h5 - e * h2

end Commutator

section Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hσ hf hK hσq in
theorem exists_not_fixed : ∃ u : K, σ u ≠ u := by
  by_contra hcon
  push Not at hcon
  have hk := NFq.card_d4k σ hf hK hσq
  have hcard : Nat.card (d4k K σ) = Nat.card K :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun x => (hcon x : x ∈ d4k K σ))
  rw [hk, hK] at hcard
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have : (2 ^ f) ^ 1 < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right h2 (by norm_num)
  rw [pow_one] at this
  omega

include hσ hf hK hσq in
theorem exists_coord_of_cent_mod_Z {x : Cm σ} (hxQ : x ∈ QC σ)
    (H : ∀ s ∈ Ust σ, ⁅s, x⁆ ∈ ZC σ) :
    ∃ e f : K, σ e = e ∧ σ f = f ∧ (x : ModGL TwistTag.D4.tag K) = d4v K σ 0 0 0 e f := by
  obtain ⟨b, c, d, e, f', hb, he, hf', hx⟩ :=
    exists_d4v σ (toRingHom_pow_three_d4 σ hσ) ((mem_QC σ).1 hxQ)
  have hcomm : ∀ a : K, b * a = 0 ∧
      b * (σ a * σ (σ a)) + (σ a * σ (σ c) + σ (σ a) * σ c) = 0 ∧
      b * (a * σ a * σ (σ a)) + ((σ a * σ (σ a) * c + σ (σ a * σ (σ a) * c) +
        σ (σ (σ a * σ (σ a) * c))) + (a * d + σ (a * d) + σ (σ (a * d)))) = 0 := fun a => by
    have h1 := (mem_ZC σ).1 (H (x1S σ hσ a) (x1S_mem_Ust σ hσ a))
    have h1' : ⁅d4x₁ K σ a, d4v K σ b c d e f'⁆ ∈ d4Zz K σ := by
      rw [← hx]
      exact h1
    exact comm_x1_mem_Zz σ hσ hb h1'
  obtain ⟨hb1, hc1, -⟩ := hcomm 1
  have hb0 : b = 0 := by simpa using hb1
  have hsc : σ c = c := by
    rw [hb0, map_one, map_one] at hc1
    have h3 : σ (σ c) = σ c := CharTwo.add_eq_zero.1 (by linear_combination hc1)
    have h4 := congrArg σ h3
    rw [hσ] at h4
    exact h3.symm.trans h4.symm
  have hc0 : c = 0 := by
    by_contra hc
    obtain ⟨u, hu⟩ := exists_not_fixed σ hσ hf hK hσq
    have ha1 : σ (σ.symm u) = u := σ.apply_symm_apply u
    obtain ⟨-, hca, -⟩ := hcomm (σ.symm u)
    have hscc : σ (σ c) = c := by rw [hsc, hsc]
    rw [hb0, ha1, hscc, hsc] at hca
    have h5 : (u + σ u) * c = 0 := by linear_combination hca
    have h6 : u + σ u = 0 := (mul_eq_zero.1 h5).resolve_right hc
    exact hu (CharTwo.add_eq_zero.1 h6).symm
  have hd0 : d = 0 := by
    refine eq_zero_of_trace_d4 σ fun δ => ?_
    obtain ⟨-, -, hE⟩ := hcomm δ
    rw [hb0, hc0] at hE
    simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add] at hE
    rw [mul_comm d δ]
    exact hE
  exact ⟨e, f', he, hf', by rw [hx, hb0, hc0, hd0]⟩

end Coord

end CFSG.Quasithin.H13.F431.D4q.Loc
