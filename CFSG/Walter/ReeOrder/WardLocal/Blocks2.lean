module

public import CFSG.Walter.ReeOrder.WardLocal.Trans

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

section Had

variable {α : Type*} [DecidableEq α]

theorem hadamardC (R : Finset α) (hR : R.card = 4) (u₀ u₁ u₂ : α → ℤ)
    (h0 : ∀ y ∈ R, u₀ y * u₀ y = 1) (h1 : ∀ y ∈ R, u₁ y * u₁ y = 1)
    (h2 : ∀ y ∈ R, u₂ y * u₂ y = 1)
    (s01 : ∑ y ∈ R, u₀ y * u₁ y = 0) (s02 : ∑ y ∈ R, u₀ y * u₂ y = 0)
    (s12 : ∑ y ∈ R, u₁ y * u₂ y = 0) (f : α → ℂ) (f0 : ∑ y ∈ R, f y * u₀ y = 0)
    (f1 : ∑ y ∈ R, f y * u₁ y = 0) (f2 : ∑ y ∈ R, f y * u₂ y = 0) {x : α} (hx : x ∈ R) :
    4 * (f x * ((u₀ x * u₁ x * u₂ x : ℤ) : ℂ)) =
      ∑ y ∈ R, f y * ((u₀ y * u₁ y * u₂ y : ℤ) : ℂ) := by
  set w₀ : α → ℤ := fun y => u₁ y * u₂ y with hw₀
  set w₁ : α → ℤ := fun y => u₀ y * u₂ y with hw₁
  set w₂ : α → ℤ := fun y => u₀ y * u₁ y with hw₂
  have hw₀sq : ∀ y ∈ R, w₀ y * w₀ y = 1 := fun y hy => by
    simp only [hw₀]; linear_combination (u₂ y * u₂ y) * h1 y hy + h2 y hy
  have hw₁sq : ∀ y ∈ R, w₁ y * w₁ y = 1 := fun y hy => by
    simp only [hw₁]; linear_combination (u₂ y * u₂ y) * h0 y hy + h2 y hy
  have hw₂sq : ∀ y ∈ R, w₂ y * w₂ y = 1 := fun y hy => by
    simp only [hw₂]; linear_combination (u₁ y * u₁ y) * h0 y hy + h1 y hy
  have hs01 : ∑ y ∈ R, w₀ y * w₁ y = 0 := by
    rw [← s01]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [hw₀, hw₁]
    linear_combination (u₀ y * u₁ y) * h2 y hy
  have hs02 : ∑ y ∈ R, w₀ y * w₂ y = 0 := by
    rw [← s02]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [hw₀, hw₂]
    linear_combination (u₀ y * u₂ y) * h1 y hy
  have hs12 : ∑ y ∈ R, w₁ y * w₂ y = 0 := by
    rw [← s12]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [hw₁, hw₂]
    linear_combination (u₁ y * u₂ y) * h0 y hy
  set g : α → ℤ := fun y => 1 + w₀ x * w₀ y + w₁ x * w₁ y + w₂ x * w₂ y with hg
  have hgx : g x = 4 := by
    simp only [hg]
    have := hw₀sq x hx
    have := hw₁sq x hx
    have := hw₂sq x hx
    linarith
  have hgsq := sum_sq_g R hR w₀ w₁ w₂ hw₀sq hw₁sq hw₂sq s12 s02 s01 hs01 hs02 hs12 (w₀ x)
    (w₁ x) (w₂ x) (hw₀sq x hx) (hw₁sq x hx) (hw₂sq x hx)
  have hg0 : ∀ y ∈ R, y ≠ x → g y = 0 := by
    have hsplit := Finset.add_sum_erase R (fun y => g y ^ 2) hx
    have hgsq' : ∑ y ∈ R, g y ^ 2 = 16 := hgsq
    rw [hgsq', hgx] at hsplit
    have hrest : ∑ y ∈ R.erase x, g y ^ 2 = 0 := by linarith
    intro y hy hyx
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg (g z))).mp hrest y
      (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  set a : α → ℂ := fun y => f y * ((u₀ y * u₁ y * u₂ y : ℤ) : ℂ) with ha
  have ha0 : ∑ y ∈ R, a y * (w₀ y : ℂ) = 0 := by
    rw [← f0]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [ha, hw₀]
    have e1 : ((u₂ y * u₂ y : ℤ) : ℂ) = 1 := by rw [h2 y hy]; simp
    have e2 : ((u₁ y * u₁ y : ℤ) : ℂ) = 1 := by rw [h1 y hy]; simp
    push_cast at e1 e2 ⊢
    linear_combination (f y * u₀ y * u₁ y * u₁ y) * e1 + (f y * u₀ y) * e2
  have ha1 : ∑ y ∈ R, a y * (w₁ y : ℂ) = 0 := by
    rw [← f1]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [ha, hw₁]
    have e1 : ((u₂ y * u₂ y : ℤ) : ℂ) = 1 := by rw [h2 y hy]; simp
    have e0 : ((u₀ y * u₀ y : ℤ) : ℂ) = 1 := by rw [h0 y hy]; simp
    push_cast at e1 e0 ⊢
    linear_combination (f y * u₁ y * u₀ y * u₀ y) * e1 + (f y * u₁ y) * e0
  have ha2 : ∑ y ∈ R, a y * (w₂ y : ℂ) = 0 := by
    rw [← f2]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [ha, hw₂]
    have e1 : ((u₁ y * u₁ y : ℤ) : ℂ) = 1 := by rw [h1 y hy]; simp
    have e0 : ((u₀ y * u₀ y : ℤ) : ℂ) = 1 := by rw [h0 y hy]; simp
    push_cast at e1 e0 ⊢
    linear_combination (f y * u₂ y * u₀ y * u₀ y) * e1 + (f y * u₂ y) * e0
  have hag : ∑ y ∈ R, a y * (g y : ℂ) = ∑ y ∈ R, a y := by
    have : ∀ y ∈ R, a y * (g y : ℂ) = a y + (w₀ x : ℂ) * (a y * w₀ y) + (w₁ x : ℂ) * (a y * w₁ y) +
        (w₂ x : ℂ) * (a y * w₂ y) := fun y _ => by simp only [hg]; push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ha0, ha1, ha2]
    ring
  have hag' : ∑ y ∈ R, a y * (g y : ℂ) = a x * 4 := by
    rw [Finset.sum_eq_single x (fun y hy hyx => by rw [hg0 y hy hyx]; simp)
      (fun h => absurd hx h), hgx]
    push_cast; ring
  have := hag.symm.trans hag'
  simp only [ha] at this ⊢
  linear_combination -this

end Had

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

include B hq hK hG hP1P hPc hPn hN1c in
theorem alpha_fpf (ρ : S.W.So) (hρ : S.α ρ = ρ) : ρ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 (Subgroup.zpowers S.A) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.orderOf_A, pow_one])
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (sylP hq hG hPc) Q
  have hQ : ∀ x, x ∈ (Q : Subgroup G) ↔ g⁻¹ * x * g ∈ P := fun x => by
    rw [← hg, Sylow.coe_subgroup_smul, coe_sylP, mem_conj_smul_iff]
  have hAQ' : S.A ∈ (Q : Subgroup G) := hAQ (Subgroup.mem_zpowers _)
  set c := S.κ ρ with hc
  have hcA : c * S.A * c⁻¹ = S.A := by
    have h1 := S.α_spec ρ
    rw [hρ] at h1
    have : c * S.A = S.A * c := by
      calc c * S.A = S.A * (S.A⁻¹ * c * S.A) := by group
        _ = S.A * c := by rw [h1]
    rw [this]; group
  have hA1 : S.A ≠ 1 := by
    intro h; have := S.orderOf_A; rw [h, orderOf_one] at this; omega
  have hcN : c ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    rcases B.inf_conj hq hK hG hP1P hPc hPn hN1c hQ c⁻¹ with h | h
    · exfalso
      have hmem : S.A ∈ (Q : Subgroup G) ⊓ (MulAut.conj c⁻¹ • (Q : Subgroup G)) := by
        refine Subgroup.mem_inf.mpr ⟨hAQ', ?_⟩
        rw [mem_conj_smul_iff, inv_inv, hcA]
        exact hAQ'
      rw [h, Subgroup.mem_bot] at hmem
      exact hA1 hmem
    · have hle : (Q : Subgroup G) ≤ MulAut.conj c⁻¹ • (Q : Subgroup G) :=
        calc (Q : Subgroup G) = (Q : Subgroup G) ⊓ MulAut.conj c⁻¹ • (Q : Subgroup G) := h.symm
          _ ≤ _ := inf_le_right
      have heq : MulAut.conj c⁻¹ • (Q : Subgroup G) = Q := (Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Nat.card_congr (Subgroup.equivSMul (MulAut.conj c⁻¹)
          (Q : Subgroup G)).toEquiv).symm)).symm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hx : x ∈ MulAut.conj c⁻¹ • (Q : Subgroup G) ↔ x ∈ (Q : Subgroup G) := by rw [heq]
      rw [mem_conj_smul_iff, inv_inv] at hx
      exact hx.symm
  have h1 : orderOf c ∣ q ^ 3 * (q - 1) := by
    rw [← B.card_normalizer_Q_eq hq hK hG hP1P hPc hPn hN1c hQ]
    exact Subgroup.orderOf_dvd_natCard _ hcN
  have hco : orderOf c = orderOf ρ := by
    rw [hc, S.orderOf_κ, Subgroup.orderOf_coe]
  have h2 : orderOf ρ ∣ Nat.card S.W.So := orderOf_dvd_natCard ρ
  have hSo : 4 * Nat.card S.W.So = q + 1 := by have := S.W.So_card; omega
  have hq8 : q % 8 = 3 := by have := S.W.q_mod; omega
  have hcop : Nat.Coprime (Nat.card S.W.So) (q ^ 3 * (q - 1)) := by
    apply Nat.Coprime.mul_right
    · rw [show q ^ 3 = 3 ^ (3 * (2 * k + 1)) by rw [hq, ← pow_mul, mul_comm]]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro h3
      have : 3 ∣ q := hq ▸ dvd_pow_self 3 (by omega)
      omega
    · rw [Nat.coprime_iff_gcd_eq_one]
      set d := Nat.gcd (Nat.card S.W.So) (q - 1) with hd
      have hd1 : d ∣ Nat.card S.W.So := Nat.gcd_dvd_left _ _
      have hd2 : d ∣ q - 1 := Nat.gcd_dvd_right _ _
      have hd3 : d ∣ 2 := by
        have h4 : d ∣ q + 1 := hSo ▸ Dvd.dvd.mul_left hd1 4
        have : 2 = (q + 1) - (q - 1) := by omega
        rw [this]; exact Nat.dvd_sub h4 hd2
      rcases (Nat.dvd_prime Nat.prime_two).mp hd3 with h | h
      · exact h
      · exfalso
        rw [h] at hd1
        obtain ⟨t, ht⟩ := hd1
        omega
  have hcop' := Nat.Coprime.coprime_dvd_left h2 hcop
  have h4 : orderOf ρ ∣ q ^ 3 * (q - 1) := hco ▸ h1
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop' h4)

end Block

section Chars

variable {H : Type*} [Group H] [Finite H]

theorem comp_ne_of_fpf (hcomm : ∀ a b : H, a * b = b * a) (β : H →* H)
    (hβ : ∀ ρ, β ρ = ρ → ρ = 1) {ν : H →* ℂˣ} (hν : ν ≠ 1) : ν.comp β ≠ ν := by
  intro h
  have hψinj : Function.Injective (fun ρ : H => β ρ * ρ⁻¹) := by
    intro ρ σ hρσ
    simp only at hρσ
    have : β (ρ * σ⁻¹) = ρ * σ⁻¹ := by
      rw [map_mul, map_inv]
      calc β ρ * (β σ)⁻¹ = (β ρ * ρ⁻¹) * ρ * (β σ)⁻¹ := by group
        _ = (β σ * σ⁻¹) * ρ * (β σ)⁻¹ := by rw [hρσ]
        _ = β σ * (σ⁻¹ * ρ) * (β σ)⁻¹ := by group
        _ = β σ * (ρ * σ⁻¹) * (β σ)⁻¹ := by rw [hcomm σ⁻¹ ρ]
        _ = ρ * σ⁻¹ := by rw [hcomm (β σ) (ρ * σ⁻¹)]; group
    have h1 := hβ _ this
    exact (mul_inv_eq_one.mp h1)
  have hψsurj := Finite.injective_iff_surjective.mp hψinj
  apply hν
  ext ρ
  obtain ⟨σ, hσ⟩ := hψsurj ρ
  simp only at hσ
  rw [← hσ, map_mul, map_inv, MonoidHom.one_apply]
  have := congrArg (fun f : H →* ℂˣ => f σ) h
  simp only [MonoidHom.comp_apply] at this
  rw [this, mul_inv_cancel]

omit [Finite H] in
theorem eq_one_of_sq (hodd : Odd (Nat.card H)) {ν : H →* ℂˣ} (h : ∀ x, ν x * ν x = 1) :
    ν = 1 := by
  ext x
  obtain ⟨t, ht⟩ := hodd
  have hx : x = (x ^ 2) ^ (t + 1) := by
    rw [← pow_mul, show 2 * (t + 1) = Nat.card H + 1 by omega, pow_succ, pow_card_eq_one',
      one_mul]
  rw [hx, map_pow, map_pow, sq, h, one_pow, MonoidHom.one_apply]

end Chars

namespace Block

omit [CharP K 3] in
theorem So_comm (a b : S.W.So) : a * b = b * a := by
  have := S.W.So_cyclic
  exact mul_comm' a b

include B hq hK hG hP1P hPc hPn hN1c in
theorem lam_comp_ne {ν : S.W.So →* ℂˣ} (hν : ν ≠ 1) : ν.comp S.α ≠ ν ∧ ν.comp S.α ≠ ν⁻¹ := by
  refine ⟨comp_ne_of_fpf So_comm S.α (B.alpha_fpf hq hK hG hP1P hPc hPn hN1c) hν, fun h => ?_⟩
  apply hν
  have hx : ∀ x, ν (S.α x) = (ν x)⁻¹ := fun x => by
    have := congrArg (fun f : S.W.So →* ℂˣ => f x) h
    simpa using this
  refine eq_one_of_sq (by rw [Nat.card_eq_fintype_card]; exact S.So_odd) fun x => ?_
  have h3 := S.α_cube x
  have : ν x = (ν x)⁻¹ := by
    calc ν x = ν (S.α (S.α (S.α x))) := by rw [h3]
      _ = (ν (S.α (S.α x)))⁻¹ := hx _
      _ = ((ν (S.α x))⁻¹)⁻¹ := by rw [hx (S.α x)]
      _ = ν (S.α x) := inv_inv _
      _ = (ν x)⁻¹ := hx x
  calc ν x * ν x = ν x * (ν x)⁻¹ := by nth_rewrite 2 [this]; rfl
    _ = 1 := mul_inv_cancel _

include B hq hK hG hP1P hPc hPn hN1c in
theorem lam_comp_comp_ne {ν : S.W.So →* ℂˣ} (hν : ν ≠ 1) :
    (ν.comp S.α).comp S.α ≠ ν ∧ (ν.comp S.α).comp S.α ≠ ν⁻¹ := by
  have hβ : ∀ ρ, (S.α.comp S.α) ρ = ρ → ρ = 1 := by
    intro ρ h
    simp only [MonoidHom.comp_apply] at h
    apply B.alpha_fpf hq hK hG hP1P hPc hPn hN1c
    have := congrArg S.α h
    rw [S.α_cube] at this
    exact this.symm
  refine ⟨fun h => comp_ne_of_fpf So_comm (S.α.comp S.α) hβ hν
    (by rw [← MonoidHom.comp_assoc]; exact h), fun h => ?_⟩
  apply (B.lam_comp_ne hq hK hG hP1P hPc hPn hN1c hν).2
  ext y
  have := congrArg (fun f : S.W.So →* ℂˣ => f (S.α y)) h
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, S.α_cube] at this
  simp only [MonoidHom.comp_apply, MonoidHom.inv_apply]
  rw [this, inv_inv]

omit [CharP K 3] in
theorem exists_lift' {ν : S.W.So →* ℂˣ} (hν : ν ≠ 1) :
    ∃ θ ∈ S.W.SFam, (S.W.lam θ).comp S.α = ν ∨ (S.W.lam θ).comp S.α = ν⁻¹ := by
  let αe : S.W.So ≃* S.W.So := MulEquiv.ofBijective S.α S.α_bijective
  have hν1 : ν.comp αe.symm.toMonoidHom ≠ 1 := by
    intro h
    apply hν
    ext ρ
    have := congrArg (fun f : S.W.So →* ℂˣ => f (αe ρ)) h
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      MonoidHom.one_apply] at this
    rw [this, MonoidHom.one_apply]
  have hsymm : ∀ ρ : S.W.So, αe.symm (S.α ρ) = ρ := fun ρ => αe.symm_apply_apply ρ
  obtain ⟨θ, hθ, h | h⟩ := S.W.lam_surj _ hν1
  · refine ⟨θ, hθ, Or.inl ?_⟩
    rw [h]
    ext ρ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm]
  · refine ⟨θ, hθ, Or.inr ?_⟩
    rw [h]
    ext ρ
    simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, MulEquiv.coe_toMonoidHom, hsymm]

include B hq hK hG hP1P hPc hPn hN1c in
theorem exists_orbit_of {θ : PSL(2, K) → ℂ} (hθ : θ ∈ S.W.SFam) : ∃ O : S.Orbit, O.θ₀ = θ := by
  have hl₀ := S.W.lam_ne θ hθ
  obtain ⟨θ₁, h₁, hα₁⟩ := exists_lift' (S := S) hl₀
  have hl₁ := S.W.lam_ne θ₁ h₁
  obtain ⟨θ₂, h₂, hα₂⟩ := exists_lift' (S := S) hl₁
  have hne := fun {ν : S.W.So →* ℂˣ} (hν : ν ≠ 1) =>
    B.lam_comp_ne hq hK hG hP1P hPc hPn hN1c hν
  have hne2 := fun {ν : S.W.So →* ℂˣ} (hν : ν ≠ 1) =>
    B.lam_comp_comp_ne hq hK hG hP1P hPc hPn hN1c hν
  refine ⟨⟨θ, θ₁, θ₂, hθ, h₁, h₂, hα₁, hα₂, ?_, ?_, ?_⟩, rfl⟩
  · intro h
    rw [← h] at hα₁
    exact hα₁.elim (hne hl₀).1 (hne hl₀).2
  · intro h
    rw [← h] at hα₂
    exact hα₂.elim (hne hl₁).1 (hne hl₁).2
  · intro h
    rw [← h] at hα₂
    have key : ((S.W.lam θ).comp S.α).comp S.α = S.W.lam θ ∨
        ((S.W.lam θ).comp S.α).comp S.α = (S.W.lam θ)⁻¹ := by
      rcases hα₂ with h1 | h1 <;> rcases hα₁ with h2 | h2
      · left; rw [h1, h2]
      · right; rw [h1, h2]
      · right; rw [h1, ← S.comp_α_inv, h2]
      · left; rw [h1, ← S.comp_α_inv, h2]; exact inv_inv (S.W.lam θ)
    exact key.elim (hne2 hl₀).1 (hne2 hl₀).2

omit [CharP K 3] in
theorem orbit_val_const (O : S.Orbit) {x : G} (hx : Odd (orderOf x)) {χ χ' : G → ℂ}
    (hχ : χ ∈ O.R) (hχ' : χ' ∈ O.R) : χ x = χ' x := by
  set f : (G → ℂ) → ℂ := fun ψ => starRingEnd ℂ (ψ x) with hf
  have horth : ∀ (θ : PSL(2, K) → ℂ) (hθ : θ ∈ S.W.SFam), supp (S.dS · θ) = O.R →
      ∑ ψ ∈ O.R, f ψ * (S.dS ψ θ : ℂ) = 0 := by
    intro θ hθ hsupp
    have h := S.orth (S.dS · θ) (fun ψ hψ => S.hS_inner θ hθ ψ hψ) hx
    rw [sum_irr_eq_sum_of_vanish O.R_sub _ (fun ψ hψ hnot => by
      rw [Set.Finite.mem_toFinset] at hψ
      rw [show S.dS ψ θ = 0 from eq_zero_of_not_mem_supp (d := (S.dS · θ)) hψ (hsupp ▸ hnot)]
      simp)] at h
    rw [← h]
    exact Finset.sum_congr rfl fun ψ _ => by simp only [hf]; ring
  have f0 := horth O.θ₀ O.h₀ rfl
  have f1 := horth O.θ₁ O.h₁ O.supp₁
  have f2 := horth O.θ₂ O.h₂ O.supp₂
  have hv : ∀ ψ ∈ O.R, ((O.u₀ ψ * O.u₁ ψ * O.u₂ ψ : ℤ) : ℂ) = 1 := by
    intro ψ hψ
    have := (O.deg_const hψ).2
    rw [O.δ_eq_one] at this
    rw [show O.u₀ ψ * O.u₁ ψ * O.u₂ ψ = O.v ψ from rfl, this]; simp
  have hh := fun ψ (hψ : ψ ∈ O.R) => hadamardC O.R O.card_R O.u₀ O.u₁ O.u₂ (fun _ h => O.sq₀ h)
    (fun _ h => O.sq₁ h) (fun _ h => O.sq₂ h) O.orth₀₁ O.orth₀₂ O.orth₁₂ f f0 f1 f2 hψ
  have e1 := hh χ hχ
  have e2 := hh χ' hχ'
  rw [hv χ hχ, mul_one] at e1
  rw [hv χ' hχ', mul_one] at e2
  have : f χ = f χ' := by linear_combination (e1 - e2) / 4
  simp only [hf] at this
  exact (starRingEnd ℂ).injective this

include B hq hK hG hP1P hPc hPn hN1c in
theorem sum_dS_mul {θ : PSL(2, K) → ℂ} (hθ : θ ∈ S.W.SFam) {x y : G} (hx : Odd (orderOf x))
    (hy : Odd (orderOf y)) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, (S.dS χ θ : ℂ) * (χ x * χ y / χ 1) = 0 := by
  obtain ⟨O, rfl⟩ := B.exists_orbit_of hq hK hG hP1P hPc hPn hN1c hθ
  rw [sum_irr_eq_sum_of_vanish O.R_sub _ (fun ψ hψ hnot => by
    rw [Set.Finite.mem_toFinset] at hψ
    rw [show S.dS ψ O.θ₀ = 0 from O.van₀ hψ hnot]; simp)]
  have hconst : ∀ ψ ∈ O.R, (S.dS ψ O.θ₀ : ℂ) * (ψ x * ψ y / ψ 1) =
      (O.u₀ ψ : ℂ) * (O.x₀ x * O.x₀ y / O.f) := by
    intro ψ hψ
    rw [orbit_val_const O hx hψ O.x₀_mem, orbit_val_const O hy hψ O.x₀_mem,
      ← deg_eq (O.R_mem hψ), (O.deg_const hψ).1]
    rfl
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
  have := O.sum_u₀
  have : ∑ ψ ∈ O.R, (O.u₀ ψ : ℂ) = 0 := by exact_mod_cast this
  rw [this, zero_mul]

omit [CharP K 3] in
include B in
theorem sum_dR_mul (i : S.W.RFam) {x y : G} (hx : Odd (orderOf x)) (hy : Odd (orderOf y)) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, (S.dR χ i.1 : ℂ) * (χ x * χ y / χ 1) = 0 := by
  rw [D.sum_split]
  have h1 : ∑ j, (S.dR (D.η j) i.1 : ℂ) * (D.η j x * D.η j y / D.η j 1) =
      D.ε * (D.η i x * D.η i y / D.η i 1) := by
    simp only [D.dR_η, apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have h2 : ∑ j, (S.dR (D.η' j) i.1 : ℂ) * (D.η' j x * D.η' j y / D.η' j 1) =
      -D.ε' * (D.η' i x * D.η' i y / D.η' i 1) := by
    simp only [D.dR_η', apply_ite (fun t : ℤ => (t : ℂ)), Int.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Int.cast_neg]
  have h3 : ∑ χ ∈ D.NE, (S.dR χ i.1 : ℂ) * (χ x * χ y / χ 1) = 0 := by
    refine Finset.sum_eq_zero fun χ hχ => ?_
    rw [D.dR_other (D.mem_NE.mp hχ).1 (D.NE_ne_η hχ) (D.NE_ne_η' hχ) i]
    simp
  rw [h1, h2, h3, B.eta_eq_eta' hx i, B.eta_eq_eta' hy i, ← (D.ε_eq_ε').2 i, ← (D.ε_eq_ε').1]
  ring

end Block

end CFSG.Walter.WardLocal

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

omit [CharP K 3] in
theorem val_J {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    starRingEnd ℂ (χ S.J) = (S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ) +
      ((q : ℂ) + 1) * ∑ θ ∈ S.W.RFam, (S.dR χ θ : ℂ) +
        ((q : ℂ) - 1) / 2 * ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) := by
  have hreal : starRingEnd ℂ (χ S.J) = χ S.J := by rw [← inv_eq_conj hχ, S.J_inv]
  have hd := S.σ_decomp hχ (y := 1) (by rw [orderOf_one]; exact odd_one)
  have hσ : S.σ χ 1 = χ S.J := by simp [WardSetup.σ]
  have hR1 : ∑ θ ∈ S.W.RFam, (S.dR χ θ : ℂ) * θ 1 =
      ((q : ℂ) + 1) * ∑ θ ∈ S.W.RFam, (S.dR χ θ : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [S.W.degR θ hθ]; push_cast; ring
  have hS1 : ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) * θ 1 =
      ((q : ℂ) - 1) * ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [S.W.degS θ hθ]; push_cast; ring
  rw [hreal, ← hσ, hd, S.W.deg2, S.W.deg3, hR1, hS1]
  push_cast
  ring

include B hq hK hG hP1P hPc hPn hN1c in
theorem sum_J {x y : G} (hx : Odd (orderOf x)) (hy : Odd (orderOf y)) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, χ x * χ y * starRingEnd ℂ (χ S.J) / χ 1 =
      ∑ χ ∈ (irreducibles_finite G).toFinset, (χ x * χ y / χ 1) *
        ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) := by
  have h1 : ∀ χ ∈ (irreducibles_finite G).toFinset, χ x * χ y * starRingEnd ℂ (χ S.J) / χ 1 =
      (χ x * χ y / χ 1) * ((S.d1 χ : ℂ) + ((q : ℂ) - 1) / 2 * ((S.d2 χ : ℂ) + S.d3 χ)) +
      ((q : ℂ) + 1) * ∑ θ ∈ S.W.RFam, (S.dR χ θ : ℂ) * (χ x * χ y / χ 1) +
      ((q : ℂ) - 1) / 2 * ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) * (χ x * χ y / χ 1) := by
    intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    rw [mul_div_right_comm, val_J hχ, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_comm (s := (irreducibles_finite G).toFinset),
    Finset.sum_comm (s := (irreducibles_finite G).toFinset)]
  have hR : ∑ θ ∈ S.W.RFam, ∑ χ ∈ (irreducibles_finite G).toFinset,
      (S.dR χ θ : ℂ) * (χ x * χ y / χ 1) = 0 := by
    refine Finset.sum_eq_zero fun θ hθ => ?_
    exact B.sum_dR_mul ⟨θ, hθ⟩ hx hy
  have hS : ∑ θ ∈ S.W.SFam, ∑ χ ∈ (irreducibles_finite G).toFinset,
      (S.dS χ θ : ℂ) * (χ x * χ y / χ 1) = 0 :=
    Finset.sum_eq_zero fun θ hθ => B.sum_dS_mul hq hK hG hP1P hPc hPn hN1c hθ hx hy
  rw [hR, hS]
  ring

end Block

end CFSG.Walter.WardLocal
