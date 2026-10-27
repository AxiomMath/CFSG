module

public import CFSG.RankThree.PartOne.LIT.JPOmegaMatrices
public import CFSG.RankThree.PartOne.LIT.CohomologyBasic
public import CFSG.RankThree.PartOne.LIT.OrthogonalTransport
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix Module CFSG.RankThree.SubgroupLists

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

theorem two_ne_zero_of_seven (hp : 7 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem three_ne_zero_of_seven (hp : 7 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem sixteen_ne_one_of_seven (hp : 7 ≤ p) : (16 : ZMod p) ≠ 1 := by
  intro h
  have h15 : ((15 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h
  have := (ZMod.natCast_eq_zero_iff 15 p).mp h15
  have hpp : p.Prime := Fact.out
  have h3 : p ∣ 3 * 5 := this
  rcases (Nat.Prime.dvd_mul hpp).mp h3 with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem adU_mulVec_zero (s : ZMod p) (w : Fin 3 → ZMod p) :
    (adU s *ᵥ w) 0 = w 0 + (-2 * s) * w 1 + (-s ^ 2) * w 2 := by
  simp [adU, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem adU_mulVec_one (s : ZMod p) (w : Fin 3 → ZMod p) :
    (adU s *ᵥ w) 1 = w 1 + s * w 2 := by
  simp [adU, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem adU_mulVec_two (s : ZMod p) (w : Fin 3 → ZMod p) : (adU s *ᵥ w) 2 = w 2 := by
  simp [adU, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem adD_mulVec_zero (σ : ZMod p) (w : Fin 3 → ZMod p) : (adD σ *ᵥ w) 0 = σ * w 0 := by
  simp [adD, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem adD_mulVec_one (σ : ZMod p) (w : Fin 3 → ZMod p) : (adD σ *ᵥ w) 1 = w 1 := by
  simp [adD, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem adD_mulVec_two (σ : ZMod p) (w : Fin 3 → ZMod p) : (adD σ *ᵥ w) 2 = σ⁻¹ * w 2 := by
  simp [adD, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem jp_omega_cocycle (hp : 7 ≤ p) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (B : Submodule (ZMod p) V) (θ : B ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    (ρ : omegaGL (splitFormK (ZMod p)) →* (V ≃ₗ[ZMod p] V))
    (hB : ∀ (y : omegaGL (splitFormK (ZMod p))) (b : B),
      ρ y (b : V) = ((θ.symm (((y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        θ b) : B) : V))
    (hq : ∀ y v, ρ y v - v ∈ B) {v₁ : V}
    (ht : ρ ⟨dGL 4 (four_ne_zero' (two_ne_zero_of_seven hp)),
      dGL_four_mem_omega (two_ne_zero_of_seven hp)⟩ v₁ = v₁) :
    ∃ e : ZMod p, ∀ s : ZMod p,
      θ ⟨ρ ⟨uGL s, uGL_mem_omega (two_ne_zero_of_seven hp) s⟩ v₁ - v₁, hq _ _⟩ =
        ![s * e, 0, 0] := by
  have h2 := two_ne_zero_of_seven hp
  have h4 := four_ne_zero' h2
  let ũ : ZMod p → omegaGL (splitFormK (ZMod p)) := fun s => ⟨uGL s, uGL_mem_omega h2 s⟩
  let t : omegaGL (splitFormK (ZMod p)) := ⟨dGL 4 h4, dGL_four_mem_omega h2⟩
  have hadd_mul : ∀ s r, ũ (s + r) = ũ s * ũ r := fun s r =>
    Subtype.ext (Units.ext (by show adU (s + r) = adU s * adU r; rw [adU_add]))
  have htor_mul : ∀ s, t * ũ s = ũ (4 * s) * t := fun s =>
    Subtype.ext (Units.ext (by
      show adD 4 * adU s = adU (4 * s) * adD 4
      exact adD_mul_adU h4 s))
  let δ : ZMod p → B := fun s => ⟨ρ (ũ s) v₁ - v₁, hq _ _⟩
  let c : Fin 3 → ZMod p → ZMod p := fun k s => θ (δ s) k
  have hδadd : ∀ s r, θ (δ (s + r)) = θ (δ s) + adU s *ᵥ θ (δ r) := by
    intro s r
    have h1 : ρ (ũ (s + r)) v₁ - v₁ =
        (ρ (ũ s) v₁ - v₁) + ρ (ũ s) (ρ (ũ r) v₁ - v₁) := by
      rw [hadd_mul, map_mul]
      simp [LinearEquiv.mul_apply, map_sub]
    have h2' : δ (s + r) = δ s + θ.symm (adU s *ᵥ θ (δ r)) := by
      apply Subtype.ext
      show ρ (ũ (s + r)) v₁ - v₁ = _
      rw [h1]
      have this' : ρ (ũ s) (δ r : V) = ((θ.symm (adU s *ᵥ θ (δ r)) : B) : V) := hB (ũ s) (δ r)
      simp only [Submodule.coe_add]
      rw [← this']
    rw [h2']
    simp only [map_add, LinearEquiv.apply_symm_apply]
  have hδtor : ∀ s, θ (δ (4 * s)) = adD 4 *ᵥ θ (δ s) := by
    intro s
    have h1 : ρ t (ρ (ũ s) v₁) = ρ (ũ (4 * s)) v₁ := by
      have := congrArg (fun g => ρ g v₁) (htor_mul s)
      simp only [map_mul, LinearEquiv.mul_apply] at this
      rw [ht] at this
      exact this
    have h2' : δ (4 * s) = θ.symm (adD 4 *ᵥ θ (δ s)) := by
      apply Subtype.ext
      show ρ (ũ (4 * s)) v₁ - v₁ = _
      have this' : ρ t (δ s : V) = ((θ.symm (adD 4 *ᵥ θ (δ s)) : B) : V) := hB t (δ s)
      rw [← h1, ← this']
      show ρ t (ρ (ũ s) v₁) - v₁ = ρ t (ρ (ũ s) v₁ - v₁)
      rw [map_sub, ht]
    rw [h2']
    simp only [LinearEquiv.apply_symm_apply]
  have h2add : ∀ s r, c 2 (s + r) = c 2 s + c 2 r := by
    intro s r
    have := congrFun (hδadd s r) 2
    simpa [c, adU_mulVec_two] using this
  have h1add : ∀ s r, c 1 (s + r) = c 1 s + c 1 r + s * c 2 r := by
    intro s r
    have := congrFun (hδadd s r) 1
    simp only [Pi.add_apply, adU_mulVec_one] at this
    simp only [c]
    rw [this]
    ring
  have h0add : ∀ s r, c 0 (s + r) = c 0 s + c 0 r + (-2 * s) * c 1 r + (-s ^ 2) * c 2 r := by
    intro s r
    have := congrFun (hδadd s r) 0
    simp only [Pi.add_apply, adU_mulVec_zero] at this
    simp only [c]
    rw [this]
    ring
  have h2tor : ∀ s, c 2 (4 * s) = 4⁻¹ * c 2 s := fun s => by
    have := congrFun (hδtor s) 2
    simpa [c, adD_mulVec_two] using this
  have h1tor : ∀ s, c 1 (4 * s) = c 1 s := fun s => by
    have := congrFun (hδtor s) 1
    simpa [c, adD_mulVec_one] using this
  have hc2 : ∀ s, c 2 s = 0 := by
    intro s
    rw [additive_eq_mul (c 2) h2add s]
    have h := h2tor 1
    rw [additive_eq_mul (c 2) h2add (4 * 1), additive_eq_mul (c 2) h2add 1] at h
    have key : (4 - 4⁻¹) * c 2 1 = 0 := by linear_combination h
    have h4' : (4 : ZMod p) - 4⁻¹ ≠ 0 := by
      intro h0
      apply sixteen_ne_one_of_seven hp
      have := (inv_ne_zero h4)
      field_simp at h0
      linear_combination h0
    have := (mul_eq_zero.mp key).resolve_left h4'
    rw [this, mul_zero]
  have hc1 : ∀ s, c 1 s = 0 := by
    have hadd1 : ∀ s r, c 1 (s + r) = c 1 s + c 1 r := fun s r => by
      rw [h1add, hc2 r, mul_zero, add_zero]
    intro s
    rw [additive_eq_mul (c 1) hadd1 s]
    have h := h1tor 1
    rw [additive_eq_mul (c 1) hadd1 (4 * 1), additive_eq_mul (c 1) hadd1 1] at h
    have key : (3 : ZMod p) * c 1 1 = 0 := by linear_combination h
    have := (mul_eq_zero.mp key).resolve_left (three_ne_zero_of_seven hp)
    rw [this, mul_zero]
  have hadd0 : ∀ s r, c 0 (s + r) = c 0 s + c 0 r := fun s r => by
    rw [h0add, hc1 r, hc2 r]
    ring
  refine ⟨c 0 1, fun s => ?_⟩
  funext k
  fin_cases k
  · show c 0 s = s * c 0 1
    exact additive_eq_mul (c 0) hadd0 s
  · exact hc1 s
  · exact hc2 s

theorem uGL_pow_val (s : ZMod p) (k : ℕ) :
    (((uGL s) ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = adU (k * s) := by
  induction k with
  | zero => simp [adU_zero]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ih]
    show adU (k * s) * adU s = _
    rw [adU_add]
    congr 1
    push_cast
    ring

theorem dGL_pow_val (σ : ZMod p) (h : σ ≠ 0) (k : ℕ) :
    (((dGL σ h) ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = adD (σ ^ k) := by
  induction k with
  | zero => simp [adD_one]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ih]
    show adD (σ ^ k) * adD σ = _
    rw [adD_mul, pow_succ]

theorem jp_omega_standard (hp : 7 ≤ p)
    (hcard : Nat.card (soGL (splitFormK (ZMod p))) = p * (p ^ 2 - 1))
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (B : Submodule (ZMod p) V)
    (θ : B ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    (ρ : omegaGL (splitFormK (ZMod p)) →* (V ≃ₗ[ZMod p] V))
    (hB : ∀ (y : omegaGL (splitFormK (ZMod p))) (b : B),
      ρ y (b : V) = ((θ.symm (((y : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        θ b) : B) : V))
    (hq : ∀ y v, ρ y v - v ∈ B) (v₀ : V) :
    ∃ v : V, v - v₀ ∈ B ∧ ∀ y, ρ y v = v := by
  have h2 := two_ne_zero_of_seven hp
  have h4 := four_ne_zero' h2
  have hpp : p.Prime := Fact.out
  let Ω := omegaGL (splitFormK (ZMod p))
  let ũ : ZMod p → Ω := fun s => ⟨uGL s, uGL_mem_omega h2 s⟩
  let t : Ω := ⟨dGL 4 h4, dGL_four_mem_omega h2⟩
  have htpow : t ^ (p - 1) = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (((dGL 4 h4) ^ (p - 1) : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1
    rw [dGL_pow_val, ZMod.pow_card_sub_one_eq_one h4, adD_one]
  have hcardt : ((Nat.card (Subgroup.zpowers t) : ℕ) : ZMod p) ≠ 0 := by
    rw [Nat.card_zpowers]
    intro h0
    have hd := (ZMod.natCast_eq_zero_iff _ p).mp h0
    have hdv : orderOf t ∣ p - 1 := orderOf_dvd_of_pow_eq_one htpow
    have := Nat.le_of_dvd (by have := hpp.two_le; omega) (hd.trans hdv)
    have := hpp.two_le
    omega
  obtain ⟨v₁, hv₁B, hv₁⟩ := exists_fixed_vector_of_index
    (ρ.comp (Subgroup.zpowers t).subtype) B (fun g v => hq _ v) ⊥
    (by rw [Subgroup.index_bot]; exact hcardt) (v₁ := v₀)
    (fun h hh => by rw [Subgroup.mem_bot.mp hh, map_one]; rfl)
  have ht : ρ t v₁ = v₁ := hv₁ ⟨t, Subgroup.mem_zpowers t⟩
  obtain ⟨e, he⟩ := jp_omega_cocycle hp B θ ρ hB hq ht
  let b₀ : B := θ.symm (Pi.single 1 (e / 2))
  let v₂ : V := v₁ + (b₀ : V)
  have hb₀ : θ b₀ = Pi.single 1 (e / 2) := by simp [b₀]
  have hv₂B : v₂ - v₀ ∈ B := by
    have : v₂ - v₀ = (v₁ - v₀) + (b₀ : V) := by simp only [v₂]; abel
    rw [this]
    exact B.add_mem hv₁B b₀.2
  have hv₂t : ρ t v₂ = v₂ := by
    have : ρ t (b₀ : V) = (b₀ : V) := by
      rw [show ρ t (b₀ : V) =
          ((θ.symm (((t : GL (Fin 3) (ZMod p)) : Matrix _ _ _) *ᵥ θ b₀) : B) : V) from hB t b₀,
        hb₀]
      congr 2
      funext k
      fin_cases k <;> simp [show ((t : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        adD 4 from rfl, adD_mulVec_zero, adD_mulVec_one, adD_mulVec_two]
    simp only [v₂, map_add, ht, this]
  have hv₂u : ∀ s, ρ (ũ s) v₂ = v₂ := by
    intro s
    have h1 : ρ (ũ s) (b₀ : V) = ((θ.symm (adU s *ᵥ θ b₀) : B) : V) := hB (ũ s) b₀
    have h2' : (⟨ρ (ũ s) v₁ - v₁, hq _ _⟩ : B) + θ.symm (adU s *ᵥ θ b₀) = b₀ := by
      apply θ.injective
      rw [map_add, LinearEquiv.apply_symm_apply, he s, hb₀]
      have e0 : (Pi.single 1 (e / 2) : Fin 3 → ZMod p) 0 = 0 := by simp
      have e1 : (Pi.single 1 (e / 2) : Fin 3 → ZMod p) 1 = e / 2 := by simp
      have e2 : (Pi.single 1 (e / 2) : Fin 3 → ZMod p) 2 = 0 := by simp
      funext k
      fin_cases k
      · show s * e + (adU s *ᵥ Pi.single 1 (e / 2)) 0 = (Pi.single 1 (e / 2) : Fin 3 → ZMod p) 0
        rw [adU_mulVec_zero, e0, e1, e2]
        field_simp
        ring
      · show 0 + (adU s *ᵥ Pi.single 1 (e / 2)) 1 = (Pi.single 1 (e / 2) : Fin 3 → ZMod p) 1
        rw [adU_mulVec_one, e1, e2]
        ring
      · show 0 + (adU s *ᵥ Pi.single 1 (e / 2)) 2 = (Pi.single 1 (e / 2) : Fin 3 → ZMod p) 2
        rw [adU_mulVec_two, e2]
        ring
    have h3 := congrArg Subtype.val h2'
    simp only [Submodule.coe_add] at h3
    simp only [v₂, map_add, h1]
    rw [show ρ (ũ s) v₁ = v₁ + (ρ (ũ s) v₁ - v₁) by abel, add_assoc, h3]
  let H₀ : Subgroup Ω := Subgroup.closure (insert t (Set.range ũ))
  have hH₀ : ∀ g ∈ H₀, ρ g v₂ = v₂ := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => ρ g v₂ = v₂) ?_ ?_ ?_ ?_ hg
    · rintro g (rfl | ⟨s, rfl⟩)
      · exact hv₂t
      · exact hv₂u s
    · simp
    · intro g h _ _ hg hh
      rw [map_mul, LinearEquiv.mul_apply, hh, hg]
    · intro g _ hg
      calc ρ g⁻¹ v₂ = ρ g⁻¹ (ρ g v₂) := by rw [hg]
        _ = v₂ := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hindex : ((H₀.index : ℕ) : ZMod p) ≠ 0 := by
    have hΩdvd : Nat.card Ω ∣ p * (p ^ 2 - 1) := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (omegaGL_le_soGL _)
    have hu1 : ũ 1 ∈ H₀ := Subgroup.subset_closure (Or.inr ⟨1, rfl⟩)
    have hpow : (ũ 1) ^ p = 1 := by
      apply Subtype.ext
      apply Units.ext
      show (((uGL (1 : ZMod p)) ^ p : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1
      rw [uGL_pow_val, ZMod.natCast_self, zero_mul, adU_zero]
    have hne : ũ 1 ≠ 1 := by
      intro h
      have := congrArg
        (fun g : Ω => ((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1) h
      simp [ũ, uGL, adU] at this
      exact h2 (by linear_combination this)
    have hord : orderOf (ũ 1) = p := orderOf_eq_prime hpow hne
    have hpH : p ∣ Nat.card H₀ := by
      have := orderOf_dvd_natCard (⟨ũ 1, hu1⟩ : H₀)
      rwa [← Subgroup.orderOf_coe, show (((⟨ũ 1, hu1⟩ : H₀) : Ω)) = ũ 1 from rfl, hord] at this
    intro h0
    have hpi : p ∣ H₀.index := (ZMod.natCast_eq_zero_iff _ p).mp h0
    have hmul := Subgroup.card_mul_index H₀
    have hpp2 : p * p ∣ Nat.card Ω := hmul ▸ Nat.mul_dvd_mul hpH hpi
    have h3 : p * p ∣ p * (p ^ 2 - 1) := hpp2.trans hΩdvd
    have h4' : p ∣ p ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left hpp.pos h3
    have h5 : p ∣ 1 := by
      have h6 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
      have := Nat.dvd_sub h6 h4'
      have hsq : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hpp.pos
      rwa [Nat.sub_sub_self hsq] at this
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h5)
  obtain ⟨v, hvB, hv⟩ := exists_fixed_vector_of_index ρ B hq H₀ hindex (v₁ := v₂) hH₀
  refine ⟨v, ?_, hv⟩
  have : v - v₀ = (v - v₂) + (v₂ - v₀) := by abel
  rw [this]
  exact B.add_mem hvB hv₂B

end CFSG.RankThree.PartOne.LIT
