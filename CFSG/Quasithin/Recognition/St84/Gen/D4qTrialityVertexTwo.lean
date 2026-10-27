module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviModules
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviCentralizers

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.LocalAnalysis.EvenBN.TrialityD4
open Subgroup
open scoped commutatorElement Matrix

variable {X : Type} [Group X] [Finite X] {f : ℕ}

private theorem x₁_add_one_mul_mem (d : TrialityD4Data X (2 ^ f)) {N : Subgroup X}
    (hFN : d.F ≤ N) (hJN : d.J₂ ≤ normalizer (N : Set X))
    {a : d.Γ} {n : X} (hn : n ∈ d.F) (hs : d.x₁ a * n ∈ N) (μ : d.Γˣ) :
    d.x₁ (((μ : d.Γ) + 1) * a) ∈ N := by
  let h := d.torus (1, μ)
  have hJ : h ∈ d.J := d.torus_mem_J (1, μ)
  have hJ₂ : h ∈ d.J₂ := (d.torus_mem_J₂_iff (1, μ)).2 rfl
  have hN : h ∈ normalizer (N : Set X) := hJN hJ₂
  have hn' : h * n * h⁻¹ ∈ d.F := (mem_normalizer_iff.1 (d.J_le_normalizer_F hJ) n).1 hn
  have hf : d.x₁ a * (h * n * h⁻¹ * n⁻¹) * (d.x₁ a)⁻¹ ∈ d.F := by
    refine (mem_normalizer_iff.1 (d.S_le_normalizer_F (d.U₁_le_S (d.x₁_mem_U₁ a)))
      (h * n * h⁻¹ * n⁻¹)).1 ?_
    exact mul_mem hn' (inv_mem hn)
  have hgs : h * (d.x₁ a * n) * h⁻¹ * (d.x₁ a * n)⁻¹ ∈ N :=
    mul_mem ((mem_normalizer_iff.1 hN (d.x₁ a * n)).1 hs) (inv_mem hs)
  have heq : h * (d.x₁ a * n) * h⁻¹ * (d.x₁ a * n)⁻¹ =
      d.x₁ ((μ : d.Γ) * a) * (d.x₁ a)⁻¹ *
        (d.x₁ a * (h * n * h⁻¹ * n⁻¹) * (d.x₁ a)⁻¹) := by
    dsimp only [h]
    rw [show d.torus (1, μ) * (d.x₁ a * n) * (d.torus (1, μ))⁻¹ =
        (d.torus (1, μ) * d.x₁ a * (d.torus (1, μ))⁻¹) *
          (d.torus (1, μ) * n * (d.torus (1, μ))⁻¹) by group, d.torus_x₁]
    group
  have hA : d.x₁ ((μ : d.Γ) * a) * (d.x₁ a)⁻¹ ∈ N := by
    have h' := mul_mem hgs (inv_mem (hFN hf))
    rw [heq, mul_assoc, mul_inv_cancel, mul_one] at h'
    exact h'
  have hcoef : (μ : d.Γ) * a + -a = ((μ : d.Γ) + 1) * a := by
    rw [CharTwo.neg_eq, add_mul, one_mul]
  have hA' : d.x₁ ((μ : d.Γ) * a + -a) ∈ N := by
    rw [d.x₁_add, map_neg_of_add d.x₁_add]
    exact hA
  rwa [hcoef] at hA'

private theorem eq_one_of_forall_smul {d : TrialityD4Data X (2 ^ f)} {ν : d.Γ₀} (hν : ν ≠ 0)
    {A : Matrix.SpecialLinearGroup (Fin 2) d.Γ₀}
    (hA : ∀ w : Fin 2 → d.Γ₀, A *ᵥ (ν • w) = w) : ν = 1 := by
  have hv0 : (ν • (![1, 0] : Fin 2 → d.Γ₀)) = ![ν, 0] := by
    ext i
    fin_cases i <;> simp
  have hv1 : (ν • (![0, 1] : Fin 2 → d.Γ₀)) = ![0, ν] := by
    ext i
    fin_cases i <;> simp
  have e0 := hA ![1, 0]
  rw [hv0] at e0
  have e1 := hA ![0, 1]
  rw [hv1] at e1
  have e00 : A 0 0 * ν = 1 := by
    have := congrFun e0 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e10 : A 1 0 * ν = 0 := by
    have := congrFun e0 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e01 : A 0 1 * ν = 0 := by
    have := congrFun e1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e11 : A 1 1 * ν = 1 := by
    have := congrFun e1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hA10 : A 1 0 = 0 := (mul_eq_zero.1 e10).resolve_right hν
  have hA01 : A 0 1 = 0 := (mul_eq_zero.1 e01).resolve_right hν
  have hdet : A 0 0 * A 1 1 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    rw [hA10, hA01, mul_zero, sub_zero] at this
    exact this
  have h1 : ν * ν = 1 := by
    have h2 : (A 0 0 * ν) * (A 1 1 * ν) = 1 := by rw [e00, e11, one_mul]
    rw [show (A 0 0 * ν) * (A 1 1 * ν) = (A 0 0 * A 1 1) * (ν * ν) by ring, hdet,
      one_mul] at h2
    exact h2
  have h2 : (ν + 1) * (ν + 1) = 0 := by
    have h3 : (ν + 1) * (ν + 1) = ν * ν + 1 := by
      rw [show (ν + 1) * (ν + 1) = ν * ν + (ν + ν) + 1 by ring, d.add_self_Γ₀, add_zero]
    rw [h3, h1, d.add_self_Γ₀]
  have h3 : ν + 1 = 0 := mul_self_eq_zero.1 h2
  calc ν = ν + 0 := (add_zero ν).symm
    _ = ν + (1 + 1) := by rw [← d.add_self_Γ₀ (1 : d.Γ₀)]
    _ = (ν + 1) + 1 := (add_assoc ν 1 1).symm
    _ = 0 + 1 := by rw [h3]
    _ = 1 := zero_add 1

theorem eq_M_of_F_le_of_le_S (d : TrialityD4Data X (2 ^ f)) {N : Subgroup X} (hFN : d.F ≤ N)
    (hNS : N ≤ d.S) (hJN : d.J₂ ≤ normalizer (N : Set X))
    (hcard : Nat.card N = (2 ^ f) ^ 11) : N = d.M := by
  have hNM : N ≤ normalizer (d.M : Set X) := hNS.trans d.S_le_normalizer_M
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := N) (B := d.M) hNM
  have hsupcard : Nat.card ↥(N ⊔ d.M) ≤ (2 ^ f) ^ 12 := by
    have hle : N ⊔ d.M ≤ d.S := sup_le hNS d.M_le_S
    have h := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    rwa [d.card_S] at h
  have h22 : (2 ^ f) ^ 12 * (2 ^ f) ^ 10 ≤ (2 ^ f) ^ 12 * Nat.card ↥(N ⊓ d.M) := by
    calc (2 ^ f) ^ 12 * (2 ^ f) ^ 10 = Nat.card N * Nat.card d.M := by
          rw [hcard, d.card_M, ← pow_add, ← pow_add]
      _ = Nat.card ↥(N ⊔ d.M) * Nat.card ↥(N ⊓ d.M) := hprod.symm
      _ ≤ (2 ^ f) ^ 12 * Nat.card ↥(N ⊓ d.M) := Nat.mul_le_mul_right _ hsupcard
  have hcard_inf : (2 ^ f) ^ 10 ≤ Nat.card ↥(N ⊓ d.M) :=
    Nat.le_of_mul_le_mul_left h22 (pow_pos (by norm_num) 12)
  have hq2 : 1 < 2 ^ f := by
    have := d.two_le_q
    omega
  have hlt : (2 ^ f) ^ 8 < Nat.card ↥(N ⊓ d.M) :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right hq2 (by norm_num : 8 < 10)) hcard_inf
  have hFle : d.F ≤ N ⊓ d.M := le_inf hFN d.F_le_M
  have hne : d.F ≠ N ⊓ d.M := by
    intro he
    rw [← he, d.card_F] at hlt
    exact (lt_irrefl _) hlt
  obtain ⟨s, hs, hsF⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hFle hne)
  obtain ⟨a, n, hn, rfl⟩ := d.mem_M_iff.1 hs.2
  have ha : a ≠ 0 := by
    rintro rfl
    exact hsF (by rw [d.x₁_zero, one_mul]; exact hn)
  have hU₁ : d.U₁ ≤ N := by
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_rangeSubgroup (hx := d.x₁_add)).1 hx
    by_cases hca : c = a
    · rw [hca]
      have h : (d.x₁ a * n) * n⁻¹ ∈ N := mul_mem hs.1 (inv_mem (hFN hn))
      simpa [mul_assoc] using h
    · let μ : d.Γˣ := Units.mk0 (1 + c / a) (by
        intro hzero
        have h1 : (1 : d.Γ) = c / a := CharTwo.add_eq_zero.1 hzero
        have h2 : a = c := by
          have := congrArg (· * a) h1
          rwa [one_mul, div_mul_cancel₀ c ha] at this
        exact hca h2.symm)
      have hμa : ((μ : d.Γ) + 1) * a = c := by
        have hμval : (μ : d.Γ) = 1 + c / a := rfl
        rw [hμval]
        have h2 : (1 + c / a) + 1 = c / a := by
          calc (1 + c / a) + 1 = 1 + (1 + c / a) := add_comm _ _
            _ = (1 + 1) + c / a := (add_assoc _ _ _).symm
            _ = c / a := by rw [CharTwo.add_self_eq_zero, zero_add]
        rw [h2, div_mul_cancel₀ c ha]
      have hmain := x₁_add_one_mul_mem d hFN hJN hn hs.1 μ
      rwa [hμa] at hmain
  have hMN : d.M ≤ N := by
    change d.U₁ ⊔ d.F ≤ N
    exact sup_le hU₁ hFN
  exact (Subgroup.eq_of_le_of_card_ge hMN (by rw [hcard, d.card_M])).symm

theorem S_inf_centralizer_J₂ (hf : 2 ≤ f) (d : TrialityD4Data X (2 ^ f)) :
    d.S ⊓ centralizer (d.J₂ : Set X) = d.U₂ := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine le_antisymm ?_ ?_
  · intro x hx
    exact d.mem_U₂_of_mem_S_of_mem_centralizer_J₂ hq hx.1 hx.2
  · refine le_inf d.U₂_le_S ?_
    exact le_centralizer_iff.2 (inf_le_right : d.J₂ ≤ centralizer (d.U₂ : Set X))

theorem M_inf_centralizer_J₂ (hf : 2 ≤ f) (d : TrialityD4Data X (2 ^ f)) :
    d.M ⊓ centralizer (d.J₂ : Set X) = ⊥ := by
  have hbot : d.U₂ ⊓ d.M = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := (mem_rangeSubgroup (hx := d.x₂_add)).1 hy.1
    rw [mem_bot]
    rw [d.x₂_mem_M_iff.1 hy.2, d.x₂_zero]
  rw [eq_bot_iff]
  intro x hx
  have hU : x ∈ d.U₂ := by
    rw [← S_inf_centralizer_J₂ hf d]
    exact Subgroup.mem_inf.2 ⟨d.M_le_S hx.1, hx.2⟩
  rw [← hbot]
  exact Subgroup.mem_inf.2 ⟨hU, hx.1⟩

theorem mem_J₂_iff_forall_mem_M (d : TrialityD4Data X (2 ^ f)) {h : X} (hh : h ∈ d.J) :
    h ∈ d.J₂ ↔ ∀ s ∈ d.S, h * s * h⁻¹ * s⁻¹ ∈ d.M := by
  constructor
  · intro hJ₂ s hs
    obtain ⟨b, n, hn, rfl⟩ := d.mem_S_iff_x₂.1 hs
    have hcent : h ∈ centralizer (d.U₂ : Set X) := (Subgroup.mem_inf.1 hJ₂).2
    have hc : h * d.x₂ b * h⁻¹ = d.x₂ b := by
      have := (mem_centralizer_iff.1 hcent) (d.x₂ b) (d.x₂_mem_U₂ b)
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    have hJ : h ∈ d.J := (Subgroup.mem_inf.1 hJ₂).1
    have hn' : h * n * h⁻¹ ∈ d.M :=
      (mem_normalizer_iff.1 (d.J_le_normalizer_M hJ) n).1 hn
    have hcomm : h * (d.x₂ b * n) * h⁻¹ * (d.x₂ b * n)⁻¹ =
        d.x₂ b * (h * n * h⁻¹ * n⁻¹) * (d.x₂ b)⁻¹ := by
      rw [show h * (d.x₂ b * n) * h⁻¹ = (h * d.x₂ b * h⁻¹) * (h * n * h⁻¹) by group, hc]
      group
    rw [hcomm]
    refine (mem_normalizer_iff.1 (d.S_le_normalizer_M (d.U₂_le_S (d.x₂_mem_U₂ b)))
      (h * n * h⁻¹ * n⁻¹)).1 ?_
    exact mul_mem hn' (inv_mem hn)
  · intro hM
    obtain ⟨⟨l, μ⟩, hμ⟩ := d.mem_J.1 hh
    have hmem := hM (d.x₂ 1) (d.U₂_le_S (d.x₂_mem_U₂ 1))
    rw [← hμ] at hmem
    rw [d.torus_x₂, mul_one, inv_eq_of_mul_eq_one_right (d.x₂_mul_self 1), ← d.x₂_add]
      at hmem
    have hlval : (l : d.Γ₀) = 1 := by
      have h0 : (l : d.Γ₀) + 1 = 0 := d.x₂_mem_M_iff.1 hmem
      calc (l : d.Γ₀) = (l : d.Γ₀) + 0 := (add_zero _).symm
        _ = (l : d.Γ₀) + (1 + 1) := by rw [← d.add_self_Γ₀ (1 : d.Γ₀)]
        _ = ((l : d.Γ₀) + 1) + 1 := (add_assoc _ _ _).symm
        _ = 0 + 1 := by rw [h0]
        _ = 1 := zero_add 1
    rw [← hμ]
    exact (d.torus_mem_J₂_iff (l, μ)).2 (Units.ext hlval)

theorem mem_J₄_iff_forall_mem_Y (d : TrialityD4Data X (2 ^ f)) {h : X} (hh : h ∈ d.J) :
    h ∈ d.J₄ ↔ ∀ w ∈ d.W, h * w * h⁻¹ * w⁻¹ ∈ d.Y := by
  constructor
  · intro hJ₄ w hw
    obtain ⟨a, n, hn, rfl⟩ := d.mem_W_iff.1 hw
    have hcent : h ∈ centralizer (d.U₄ : Set X) := (Subgroup.mem_inf.1 hJ₄).2
    have hc : h * d.x₄ a * h⁻¹ = d.x₄ a := by
      have := (mem_centralizer_iff.1 hcent) (d.x₄ a) (d.x₄_mem_U₄ a)
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    have hJ : h ∈ d.J := (Subgroup.mem_inf.1 hJ₄).1
    have hn' : h * n * h⁻¹ ∈ d.Y :=
      (mem_normalizer_iff.1 (d.J_le_normalizer_Y hJ) n).1 hn
    have hcomm : h * (d.x₄ a * n) * h⁻¹ * (d.x₄ a * n)⁻¹ =
        d.x₄ a * (h * n * h⁻¹ * n⁻¹) * (d.x₄ a)⁻¹ := by
      rw [show h * (d.x₄ a * n) * h⁻¹ = (h * d.x₄ a * h⁻¹) * (h * n * h⁻¹) by group, hc]
      group
    rw [hcomm]
    refine (mem_normalizer_iff.1 (d.S_le_normalizer_Y (d.W_le_S (d.x₄_mem_W a)))
      (h * n * h⁻¹ * n⁻¹)).1 ?_
    exact mul_mem hn' (inv_mem hn)
  · intro hY
    obtain ⟨⟨l, μ⟩, hμ⟩ := d.mem_J.1 hh
    have hmem := hY (d.x₄ 1) (d.x₄_mem_W 1)
    rw [← hμ] at hmem
    rw [d.torus_x₄, mul_one, inv_eq_of_mul_eq_one_right (d.x₄_mul_self 1), ← d.x₄_add]
      at hmem
    have hχ : ((l : d.Γ₀) : d.Γ) * d.σ (μ : d.Γ) * d.σ (d.σ (μ : d.Γ)) = 1 :=
      CharTwo.add_eq_zero.1 (d.x₄_mem_Y_iff.1 hmem)
    rw [← hμ]
    exact (d.torus_mem_J₄_iff (l, μ)).2 hχ

theorem eq_one_of_mem_leviLong_sup_J₂_of_commute (d : TrialityD4Data X (2 ^ f)) {r : X}
    (hr : r ∈ d.leviLong ⊔ d.J₂) (hc : ∀ x ∈ d.M, r * x = x * r) : r = 1 := by
  have hJ : d.J₂ ≤ normalizer (d.leviLong : Set X) :=
    (le_centralizer_iff.2 d.leviLong_le_centralizer_J₂).trans (centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left d.leviLong d.J₂ hJ,
    Set.mem_mul] at hr
  obtain ⟨l, hl, j, hj, rfl⟩ := hr
  obtain ⟨⟨l₀, μ⟩, hμ, hμ1⟩ := d.mem_J₂.1 hj
  subst hμ1
  have hj_eq : j = d.torus (1, μ) := hμ.symm
  have hjyv : ∀ w : Fin 2 → d.Γ₀, j * d.yv w * j⁻¹ = d.yv (d.nm (μ : d.Γ) • w) := by
    intro w
    rw [hj_eq]
    simp only [TrialityD4Data.yv, Pi.smul_apply, smul_eq_mul]
    rw [show d.torus (1, μ) * (d.x₅ (w 0) * d.x₆ (w 1)) * (d.torus (1, μ))⁻¹ =
        (d.torus (1, μ) * d.x₅ (w 0) * (d.torus (1, μ))⁻¹) *
          (d.torus (1, μ) * d.x₆ (w 1) * (d.torus (1, μ))⁻¹) by group,
      d.torus_x₅, d.torus_x₆]
    simp only [Units.val_one, one_mul]
  have hact : ∀ w : Fin 2 → d.Γ₀,
      d.leviLongRep ⟨l, hl⟩ *ᵥ (d.nm (μ : d.Γ) • w) = w := by
    intro w
    have hyY : d.yv w ∈ d.Y := by
      have h : d.yv w ∈ Set.range d.yv := ⟨w, rfl⟩
      rwa [d.range_yv] at h
    have h1 := hc (d.yv w) (d.F_le_M (d.W_le_F (d.Y_le_W hyY)))
    have h2 : l * (j * d.yv w * j⁻¹) = d.yv w * l := by
      calc l * (j * d.yv w * j⁻¹) = (l * j) * d.yv w * j⁻¹ := by group
        _ = d.yv w * (l * j) * j⁻¹ := by rw [h1]
        _ = d.yv w * l := by group
    have h3 : ((⟨l, hl⟩ : d.leviLong) : X) * d.yv (d.nm (μ : d.Γ) • w) *
        ((⟨l, hl⟩ : d.leviLong) : X)⁻¹ = d.yv w := by
      change l * d.yv (d.nm (μ : d.Γ) • w) * l⁻¹ = d.yv w
      rw [← hjyv w, h2]
      group
    have h4 : ((⟨l, hl⟩ : d.leviLong) : X) * d.yv (d.nm (μ : d.Γ) • w) *
        ((⟨l, hl⟩ : d.leviLong) : X)⁻¹ =
        d.yv (d.leviLongRep ⟨l, hl⟩ *ᵥ (d.nm (μ : d.Γ) • w)) :=
      d.leviLongRep_spec ⟨l, hl⟩ _
    have h5 : d.yv (d.leviLongRep ⟨l, hl⟩ *ᵥ (d.nm (μ : d.Γ) • w)) = d.yv w := by
      rw [← h4, h3]
    exact d.yv_injective h5
  have hν0 : d.nm (μ : d.Γ) ≠ 0 := by
    have h := (d.nmUnits μ).ne_zero
    rwa [d.coe_nmUnits] at h
  have hν1 : d.nm (μ : d.Γ) = 1 := eq_one_of_forall_smul hν0 hact
  have hact1 : ∀ w : Fin 2 → d.Γ₀, d.leviLongRep ⟨l, hl⟩ *ᵥ w = w := by
    intro w
    simpa [hν1] using hact w
  have hA1 : d.leviLongRep ⟨l, hl⟩ = 1 := by
    refine d.sl_eq_of_yv fun w => ?_
    rw [hact1 w, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hl1 : l = 1 := by
    refine d.eq_one_of_mem_leviLong_of_conj_yv hl ?_
    intro w
    have h := d.leviLongRep_spec ⟨l, hl⟩ w
    rw [hA1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
    simpa using h
  rw [hl1, one_mul]
  have hjM : ∀ x ∈ d.M, j * x = x * j := by
    intro x hx
    have := hc x hx
    rwa [hl1, one_mul] at this
  have hjJ : j ∈ d.J := (inf_le_left : d.J₂ ≤ d.J) hj
  have hjJ₁ : j ∈ d.J₁ := by
    refine Subgroup.mem_inf.2 ⟨hjJ, ?_⟩
    rw [mem_centralizer_iff]
    intro x hx
    exact (hjM x (d.U₁_le_M hx)).symm
  have hμ1 : μ = 1 := (d.torus_mem_J₁_iff (1, μ)).1 (hj_eq ▸ hjJ₁)
  rw [hj_eq, hμ1]
  exact map_one d.torus

theorem card_leviLong_sup_J₂ (d : TrialityD4Data X (2 ^ f)) :
    Nat.card ↥(d.leviLong ⊔ d.J₂) = 2 ^ f * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
  have hJ : d.leviLong ≤ normalizer (d.J₂ : Set X) :=
    d.leviLong_le_centralizer_J₂.trans (centralizer_le_normalizer _)
  have h := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := d.leviLong) (B := d.J₂) hJ
  rw [d.yamada_three_eight_five.2.2.2.1, Subgroup.card_bot, mul_one, d.card_leviLong,
    d.yamada_three_five_one.2.2.2.2.2] at h
  exact h

end CFSG.Quasithin.F112R.St84
