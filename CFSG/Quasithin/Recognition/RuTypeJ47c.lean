module

public import CFSG.Quasithin.Recognition.RuTypeJ47Sig
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin

namespace Sigma47

variable {X : Type*} [Group X]

@[expose] def PowOfG (σ τ : X) : Prop := ∃ k : Fin 5, τ = σ ^ (k : ℕ)

theorem powOfG_pow (σ : X) (k : ℕ) (hσ : σ ^ 5 = 1) : PowOfG σ (σ ^ k) := by
  refine ⟨⟨k % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  show σ ^ k = σ ^ (k % 5)
  conv_lhs => rw [← Nat.div_add_mod k 5, pow_add, pow_mul, hσ, one_pow, one_mul]

theorem powOfG_trans {σ τ ρ : X} (hσ : σ ^ 5 = 1) (h1 : PowOfG σ τ) (h2 : PowOfG τ ρ) :
    PowOfG σ ρ := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  rw [← pow_mul]
  exact powOfG_pow σ _ hσ

theorem powOfG_symm {σ τ : X} (hσ : σ ^ 5 = 1) (hτ : τ ≠ 1) (h : PowOfG σ τ) : PowOfG τ σ := by
  obtain ⟨k, rfl⟩ := h
  fin_cases k
  · exact absurd (pow_zero σ) hτ
  · exact ⟨1, by simp⟩
  · refine ⟨3, ?_⟩
    show σ = (σ ^ 2) ^ 3
    rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_add, hσ, one_mul, pow_one]
  · refine ⟨2, ?_⟩
    show σ = (σ ^ 3) ^ 2
    rw [← pow_mul, show 3 * 2 = 5 + 1 by norm_num, pow_add, hσ, one_mul, pow_one]
  · refine ⟨4, ?_⟩
    show σ = (σ ^ 4) ^ 4
    rw [← pow_mul, show 4 * 4 = 5 * 3 + 1 by norm_num, pow_add, pow_mul, hσ, one_pow, one_mul,
      pow_one]

theorem powOfG_conj {σ τ : X} (g : X) (h : PowOfG σ τ) : PowOfG (g * σ * g⁻¹) (g * τ * g⁻¹) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, (conj_pow).symm⟩

theorem powOf_iff (σ τ : SigmaL2F4) : PowOf σ τ ↔ PowOfG σ τ := Iff.rfl

@[expose] def NormByG (x σ : X) : Prop := ∃ k : Fin 5, x * σ * x⁻¹ = σ ^ (k : ℕ)

theorem normBy_iff (x σ : SigmaL2F4) : NormBy x σ ↔ NormByG x σ := Iff.rfl

theorem normByG_iff_powOfG (x σ : X) : NormByG x σ ↔ PowOfG σ (x * σ * x⁻¹) := Iff.rfl

theorem normByG_of_powOfG {x σ τ : X} (hσ : σ ^ 5 = 1) (hτ : τ ≠ 1) (hστ : PowOfG σ τ)
    (h : NormByG x σ) : NormByG x τ := by
  rw [normByG_iff_powOfG] at h ⊢
  have h1 := powOfG_conj x hστ
  have hτσ := powOfG_symm hσ hτ hστ
  have h5 : τ ^ 5 = 1 := by
    obtain ⟨k, rfl⟩ := hστ
    rw [← pow_mul, mul_comm, pow_mul, hσ, one_pow]
  exact powOfG_trans h5 hτσ (powOfG_trans hσ h h1)

theorem pow_five_conj {σ : SigmaL2F4} (g : SigmaL2F4) (h : σ ^ 5 = 1) :
    (g * σ * g⁻¹) ^ 5 = 1 := by rw [conj_pow, h, mul_one, mul_inv_cancel]

theorem ne_one_conj {σ : SigmaL2F4} (g : SigmaL2F4) (h : σ ≠ 1) : g * σ * g⁻¹ ≠ 1 := by
  intro h'
  apply h
  calc σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
    _ = 1 := by rw [h']; group

theorem normBy_conj {d σ : SigmaL2F4} (g : SigmaL2F4) (h : NormBy d σ) :
    NormBy (g * d * g⁻¹) (g * σ * g⁻¹) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [conj_pow, ← hk]
  group

theorem conjInv_pow {X : Type*} [Group X] (g x : X) :
    ∀ n : ℕ, (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g
  | 0 => by rw [pow_zero, pow_zero, mul_one, inv_mul_cancel]
  | n + 1 => by rw [pow_succ, conjInv_pow g x n, pow_succ]; group

theorem powOf_ab_of_normBy {d g τ : SigmaL2F4} (hdg : d = g * d0 * g⁻¹) (hτ5 : τ ^ 5 = 1)
    (hτ1 : τ ≠ 1) (hτ : NormBy d τ) :
    PowOfG (g * σa * g⁻¹) τ ∨ PowOfG (g * σb * g⁻¹) τ := by
  have h' : NormBy d0 (g⁻¹ * τ * g) := by
    have h1 := normBy_conj g⁻¹ hτ
    rw [inv_inv, hdg] at h1
    have e : g⁻¹ * (g * d0 * g⁻¹) * g = d0 := by group
    rwa [e] at h1
  have h5 : (g⁻¹ * τ * g) ^ 5 = 1 := by rw [conjInv_pow, hτ5]; group
  have h1' : g⁻¹ * τ * g ≠ 1 := fun h => hτ1 (by
    calc τ = g * (g⁻¹ * τ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have e : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
  rcases normBy_d0_iff (g⁻¹ * τ * g) h5 h1' h' with h | h
  · left
    have h2 := powOfG_conj g ((powOf_iff _ _).mp h)
    rwa [e] at h2
  · right
    have h2 := powOfG_conj g ((powOf_iff _ _).mp h)
    rwa [e] at h2

theorem powOf_of_two_classes {d σ σ' τ : SigmaL2F4} (hd : d * d = 1) (hd1 : d ≠ 1)
    (hσ5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) (hσ : NormBy d σ)
    (hσ'5 : σ' ^ 5 = 1) (hσ'1 : σ' ≠ 1) (hσ' : NormBy d σ') (hne : ¬ PowOfG σ σ')
    (hτ5 : τ ^ 5 = 1) (hτ1 : τ ≠ 1) (hτ : NormBy d τ) : PowOfG σ τ ∨ PowOfG σ' τ := by
  obtain ⟨g, hdg⟩ := exists_conj_d0 hd hd1 hσ5 hσ1 hσ
  have ha5 : (g * σa * g⁻¹) ^ 5 = 1 := pow_five_conj g σa_pow_five.1
  have hb5 : (g * σb * g⁻¹) ^ 5 = 1 := pow_five_conj g σb_pow_five.1
  rcases powOf_ab_of_normBy hdg hσ5 hσ1 hσ with hs | hs
  · rcases powOf_ab_of_normBy hdg hσ'5 hσ'1 hσ' with hs' | hs'
    · exact absurd (powOfG_trans hσ5 (powOfG_symm ha5 hσ1 hs) hs') hne
    · rcases powOf_ab_of_normBy hdg hτ5 hτ1 hτ with ht | ht
      · exact Or.inl (powOfG_trans hσ5 (powOfG_symm ha5 hσ1 hs) ht)
      · exact Or.inr (powOfG_trans hσ'5 (powOfG_symm hb5 hσ'1 hs') ht)
  · rcases powOf_ab_of_normBy hdg hσ'5 hσ'1 hσ' with hs' | hs'
    · rcases powOf_ab_of_normBy hdg hτ5 hτ1 hτ with ht | ht
      · exact Or.inr (powOfG_trans hσ'5 (powOfG_symm ha5 hσ'1 hs') ht)
      · exact Or.inl (powOfG_trans hσ5 (powOfG_symm hb5 hσ1 hs) ht)
    · exact absurd (powOfG_trans hσ5 (powOfG_symm hb5 hσ1 hs) hs') hne

theorem eq_one_of_comm_of_pow_three {d σ c : SigmaL2F4} (hd : d * d = 1) (hd1 : d ≠ 1)
    (hσ5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) (hσ : NormBy d σ) (hcd : c * d = d * c) (hc3 : c ^ 3 = 1) :
    c = 1 := by
  obtain ⟨g, hdg⟩ := exists_conj_d0 hd hd1 hσ5 hσ1 hσ
  have hc' : g⁻¹ * c * g * d0 = d0 * (g⁻¹ * c * g) := by
    rw [hdg] at hcd
    calc g⁻¹ * c * g * d0 = g⁻¹ * (c * (g * d0 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * d0 * g⁻¹) * c) * g := by rw [hcd]
      _ = d0 * (g⁻¹ * c * g) := by group
  have hc3' : (g⁻¹ * c * g) ^ 3 = 1 := by rw [conjInv_pow, hc3]; group
  have h := eq_one_of_comm_d0_of_pow_three (g⁻¹ * c * g) hc' hc3'
  calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem not_powOf_conj_of_comm {d σ c : SigmaL2F4} (hd : d * d = 1) (hd1 : d ≠ 1)
    (hσ5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) (hσ : NormBy d σ) (hcd : c * d = d * c) (hc2 : c * c = 1)
    (hc1 : c ≠ 1) (hcd' : c ≠ d) : ¬ PowOfG σ (c * σ * c⁻¹) := by
  obtain ⟨g, hdg⟩ := exists_conj_d0 hd hd1 hσ5 hσ1 hσ
  set c' := g⁻¹ * c * g with hc'
  have hc'd : c' * d0 = d0 * c' := by
    rw [hdg] at hcd
    calc c' * d0 = g⁻¹ * (c * (g * d0 * g⁻¹)) * g := by rw [hc']; group
      _ = g⁻¹ * ((g * d0 * g⁻¹) * c) * g := by rw [hcd]
      _ = d0 * c' := by rw [hc']; group
  have hc'2 : c' * c' = 1 := by
    rw [hc']
    calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [hc2]; group
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    calc c = g * c' * g⁻¹ := by rw [hc']; group
      _ = 1 := by rw [h]; group
  have hc'd0 : c' ≠ d0 := by
    intro h
    apply hcd'
    calc c = g * c' * g⁻¹ := by rw [hc']; group
      _ = d := by rw [h, hdg]
  have hab : PowOfG σa (c' * σb * c'⁻¹) ∧ PowOfG σb (c' * σa * c'⁻¹) := by
    have h0 := swap_of_comm_d0 c' hc'd hc'2 hc'1 hc'd0
    have hba : PowOfG σb (c' * σa * c'⁻¹) := (powOf_iff _ _).mp h0
    refine ⟨?_, hba⟩
    have h1 := powOfG_conj c' hba
    have e : c' * (c' * σa * c'⁻¹) * c'⁻¹ = σa := by
      calc c' * (c' * σa * c'⁻¹) * c'⁻¹ = (c' * c') * σa * (c' * c')⁻¹ := by group
        _ = σa := by rw [hc'2]; group
    rw [e] at h1
    exact powOfG_symm (pow_five_conj c' σb_pow_five.1) σa_pow_five.2 h1
  have hσ' : NormBy d0 (g⁻¹ * σ * g) := by
    have h1 := normBy_conj g⁻¹ hσ
    rw [inv_inv, hdg] at h1
    have e : g⁻¹ * (g * d0 * g⁻¹) * g = d0 := by group
    rwa [e] at h1
  have hg5 : (g⁻¹ * σ * g) ^ 5 = 1 := by rw [conjInv_pow, hσ5]; group
  have hg1 : g⁻¹ * σ * g ≠ 1 := fun h => hσ1 (by
    calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  intro hpow
  have hpow' : PowOfG (g⁻¹ * σ * g) (c' * (g⁻¹ * σ * g) * c'⁻¹) := by
    have h1 := powOfG_conj g⁻¹ hpow
    rw [inv_inv] at h1
    have e : g⁻¹ * (c * σ * c⁻¹) * g = c' * (g⁻¹ * σ * g) * c'⁻¹ := by rw [hc']; group
    rwa [e] at h1
  have hnab : ¬ PowOfG σa σb := fun h => not_powOf_σa_σb ((powOf_iff _ _).mpr h)
  rcases normBy_d0_iff _ hg5 hg1 hσ' with h | h
  · have ha := (powOf_iff _ _).mp h
    have h1 := powOfG_conj c' ha
    have h2 : PowOfG σb (c' * (g⁻¹ * σ * g) * c'⁻¹) := powOfG_trans σb_pow_five.1 hab.2 h1
    have h3 := powOfG_trans σa_pow_five.1 ha hpow'
    have h4 := powOfG_symm σb_pow_five.1 (ne_one_conj c' hg1) h2
    exact hnab (powOfG_trans σa_pow_five.1 h3 h4)
  · have hb := (powOf_iff _ _).mp h
    have h1 := powOfG_conj c' hb
    have h2 : PowOfG σa (c' * (g⁻¹ * σ * g) * c'⁻¹) := powOfG_trans σa_pow_five.1 hab.1 h1
    have h3 := powOfG_trans σb_pow_five.1 hb hpow'
    have h4 := powOfG_symm σa_pow_five.1 (ne_one_conj c' hg1) h2
    exact hnab (powOfG_symm σb_pow_five.1 σa_pow_five.2 (powOfG_trans σb_pow_five.1 h3 h4))

theorem normBy_of_normBy_of_comm {d σ σ' c : SigmaL2F4} (hd : d * d = 1) (hd1 : d ≠ 1)
    (hσ5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) (hσ : NormBy d σ)
    (hσ'5 : σ' ^ 5 = 1) (hσ'1 : σ' ≠ 1) (hσ' : NormBy d σ')
    (hcd : c * d = d * c) (hcσ : NormBy c σ) : NormBy c σ' := by
  by_cases hss : PowOfG σ σ'
  · exact (normBy_iff _ _).mpr (normByG_of_powOfG hσ5 hσ'1 hss ((normBy_iff _ _).mp hcσ))
  have hn : NormBy d (c * σ' * c⁻¹) := by
    obtain ⟨k, hk⟩ := hσ'
    refine ⟨k, ?_⟩
    have hdci : c⁻¹ * d⁻¹ = d⁻¹ * c⁻¹ := by rw [← mul_inv_rev, ← hcd, mul_inv_rev]
    calc d * (c * σ' * c⁻¹) * d⁻¹ = (d * c) * σ' * (c⁻¹ * d⁻¹) := by group
      _ = (c * d) * σ' * (d⁻¹ * c⁻¹) := by rw [← hcd, hdci]
      _ = c * (d * σ' * d⁻¹) * c⁻¹ := by group
      _ = c * σ' ^ (k : ℕ) * c⁻¹ := by rw [hk]
      _ = (c * σ' * c⁻¹) ^ (k : ℕ) := conj_pow.symm
  have h5 : (c * σ' * c⁻¹) ^ 5 = 1 := pow_five_conj c hσ'5
  have h1 : c * σ' * c⁻¹ ≠ 1 := ne_one_conj c hσ'1
  rcases powOf_of_two_classes hd hd1 hσ5 hσ1 hσ hσ'5 hσ'1 hσ' hss h5 h1 hn with h | h
  · exfalso
    apply hss
    have hcσG : PowOfG σ (c * σ * c⁻¹) := (normByG_iff_powOfG _ _).mp ((normBy_iff _ _).mp hcσ)
    have hcσ' : PowOfG (c * σ * c⁻¹) σ :=
      powOfG_symm hσ5 (ne_one_conj c hσ1) hcσG
    have h2 : PowOfG (c * σ * c⁻¹) (c * σ' * c⁻¹) :=
      powOfG_trans (pow_five_conj c hσ5) hcσ' h
    have h3 := powOfG_conj c⁻¹ h2
    have e1 : c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ := by group
    have e2 : c⁻¹ * (c * σ' * c⁻¹) * c⁻¹⁻¹ = σ' := by group
    rwa [e1, e2] at h3
  · exact (normBy_iff _ _).mpr ((normByG_iff_powOfG _ _).mpr h)

end Sigma47

end CFSG.Quasithin.RuType
