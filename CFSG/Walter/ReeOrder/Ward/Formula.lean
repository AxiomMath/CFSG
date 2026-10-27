module

public import CFSG.Walter.ReeOrder.Ward.Principal
public import CFSG.Walter.ReeOrder.Ward.Seven

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct
open CFSG.PSL2Table

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

theorem irr_C : (irreducibles_finite (Subgroup.centralizer ({S.J} : Set G))).toFinset =
    ((({1, signChar _} : Finset (Subgroup.zpowers S.J → ℂ)) ×ˢ
      (irreducibles_finite L).toFinset).image fun p => S.ψ p.1 p.2) := by
  obtain ⟨hIrr, -⟩ := blocksIrr_prod_card_two S.card_Z L
  ext ψ'
  simp only [Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Prod.exists]
  constructor
  · intro h
    have h' := CFSG.BrauerThirdMainTheorem.Helpers.irr_comp_equiv S.eC h
    rw [hIrr] at h'
    obtain ⟨θ, hθ, heq | heq⟩ := h'
    · refine ⟨1, θ, ⟨Or.inl rfl, hθ⟩, ?_⟩
      funext x
      have := congrFun heq (S.eC.symm x)
      simp only [Function.comp_apply, MulEquiv.apply_symm_apply] at this
      rw [this]
      rfl
    · refine ⟨signChar _, θ, ⟨Or.inr rfl, hθ⟩, ?_⟩
      funext x
      have := congrFun heq (S.eC.symm x)
      simp only [Function.comp_apply, MulEquiv.apply_symm_apply] at this
      rw [this]
      rfl
  · rintro ⟨ε, θ, ⟨hε | hε, hθ⟩, rfl⟩
    · subst hε
      exact S.ψ_one_mem hθ
    · subst hε
      exact S.ψ_sgn_mem hθ

theorem ψ_injOn_irr : Set.InjOn (fun p : (Subgroup.zpowers S.J → ℂ) × (L → ℂ) => S.ψ p.1 p.2)
    ↑(({1, signChar _} : Finset (Subgroup.zpowers S.J → ℂ)) ×ˢ
      (irreducibles_finite L).toFinset) := by
  rintro ⟨ε, θ⟩ h ⟨ε', θ'⟩ h' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton, Set.Finite.mem_toFinset] at h h'
  simp only at heq
  have hsgn1 : signChar (Subgroup.zpowers S.J) 1 = 1 := by simp [signChar]
  rcases h.1 with rfl | rfl <;> rcases h'.1 with rfl | rfl
  · rw [S.ψ_inj 1 rfl heq]
  · exact absurd heq (S.ψ_one_ne_sgn h.2 h'.2)
  · exact absurd heq.symm (S.ψ_one_ne_sgn h'.2 h.2)
  · rw [S.ψ_inj _ hsgn1 heq]

theorem sum_irr_C {M : Type*} [AddCommMonoid M]
    (F : (Subgroup.centralizer ({S.J} : Set G) → ℂ) → M) :
    ∑ ψ' ∈ (irreducibles_finite (Subgroup.centralizer ({S.J} : Set G))).toFinset, F ψ' =
      ∑ θ ∈ (irreducibles_finite L).toFinset, (F (S.ψ 1 θ) + F (S.ψ (signChar _) θ)) := by
  rw [S.irr_C, Finset.sum_image S.ψ_injOn_irr, Finset.sum_product, Finset.sum_pair S.one_ne_sgn,
    ← Finset.sum_add_distrib]

theorem κ_isConj_J_iff (w : L) : IsConj (S.κ w) S.J ↔ orderOf w = 2 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have ho : orderOf (c * S.κ w * c⁻¹) = orderOf (S.κ w) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hc, S.orderOf_J, S.orderOf_κ] at ho
    exact ho.symm
  · intro h
    apply S.involution_conj
    rw [S.orderOf_κ, h]

theorem Jκ_isConj_J_iff (w : L) : IsConj (S.J * S.κ w) S.J ↔ w * w = 1 := by
  have hsq : (S.J * S.κ w) ^ 2 = S.κ (w * w) := by
    rw [sq, map_mul]
    calc S.J * S.κ w * (S.J * S.κ w) = S.J * S.J * (S.κ w * S.κ w) := by
          rw [mul_assoc, ← mul_assoc (S.κ w), ← S.κ_comm', mul_assoc, mul_assoc]
      _ = S.κ w * S.κ w := by rw [S.J_mul, one_mul]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have ho : orderOf (c * (S.J * S.κ w) * c⁻¹) = orderOf (S.J * S.κ w) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hc, S.orderOf_J] at ho
    have h2 : (S.J * S.κ w) ^ 2 = 1 := by rw [ho]; exact pow_orderOf_eq_one _
    rw [hsq] at h2
    apply S.κ_inj
    rw [h2, map_one]
  · intro h
    apply S.involution_conj
    apply orderOf_eq_prime
    · rw [hsq, h, map_one]
    · intro h1
      apply S.J_mul_ne w 1
      rw [h1, map_one]

noncomputable def N : ℕ := Nat.card (ConjClasses.mk S.W.J').carrier

theorem sum_inv (θ : L → ℂ) (hθ : θ ∈ BlocksIrr L) :
    ∑ w : L, (if orderOf w = 2 then θ w else 0) = S.N * θ S.W.J' := by
  rw [← Finset.sum_filter, S.W.sum_involutions hθ, N]

theorem classSum_ψ (ε : Subgroup.zpowers S.J → ℂ) (hε : ε 1 = 1) {θ : L → ℂ}
    (hθ : θ ∈ BlocksIrr L) :
    ∑ c ∈ Finset.univ.filter (fun c : Subgroup.centralizer ({S.J} : Set G) => IsConj (c : G) S.J),
      S.ψ ε θ c = ε S.Jz * θ 1 + (1 + ε S.Jz) * S.N * θ S.W.J' := by
  rw [Finset.sum_filter]
  rw [← S.eC.toEquiv.sum_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [Fintype.sum_prod_type, S.sum_Z]
  have h1 : ∀ w : L, (if IsConj ((S.eC (1, w) : Subgroup.centralizer ({S.J} : Set G)) : G) S.J
      then S.ψ ε θ (S.eC (1, w)) else 0) = if orderOf w = 2 then θ w else 0 := by
    intro w
    have hx : ((S.eC (1, w) : Subgroup.centralizer ({S.J} : Set G)) : G) = S.κ w := by
      rw [eC_apply, ι_apply]
      simp
    rw [hx]
    simp only [S.κ_isConj_J_iff]
    congr 1
    simp [ψ, outerProductCharacter_apply, hε]
  have h2 : ∀ w : L, (if IsConj ((S.eC (S.Jz, w) : Subgroup.centralizer ({S.J} : Set G)) : G) S.J
      then S.ψ ε θ (S.eC (S.Jz, w)) else 0) =
        ε S.Jz * ((if w = 1 then θ 1 else 0) + if orderOf w = 2 then θ w else 0) := by
    intro w
    have hx : ((S.eC (S.Jz, w) : Subgroup.centralizer ({S.J} : Set G)) : G) = S.J * S.κ w := by
      rw [eC_apply, ι_apply]
      rfl
    rw [hx]
    simp only [S.Jκ_isConj_J_iff]
    have hval : S.ψ ε θ (S.eC (S.Jz, w)) = ε S.Jz * θ w := by
      simp [ψ, outerProductCharacter_apply]
    rw [hval]
    by_cases hw : w = 1
    · subst hw
      have : orderOf (1 : L) ≠ 2 := by rw [orderOf_one]; norm_num
      simp
    · have hiff : w * w = 1 ↔ orderOf w = 2 := by
        constructor
        · intro h
          exact orderOf_eq_prime (by rw [sq, h]) hw
        · intro h
          rw [← sq, ← h]
          exact pow_orderOf_eq_one w
      by_cases h2 : orderOf w = 2
      · rw [ite_eq_left (hiff.mpr h2), ite_eq_right hw, ite_eq_left h2, zero_add]
      · rw [ite_eq_right (fun h => h2 (hiff.mp h)), ite_eq_right hw, ite_eq_right h2]
        ring
  rw [Finset.sum_congr rfl fun w _ => h1 w, Finset.sum_congr rfl fun w _ => h2 w, S.sum_inv θ hθ,
    ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq', S.sum_inv θ hθ]
  simp only [Finset.mem_univ, ↓reduceIte]
  ring

theorem sum_conj_mul (f Φ : L → ℂ) :
    ∑ ρ : L, starRingEnd ℂ (f ρ) * Φ ρ = Nat.card L * starRingEnd ℂ (BlocksInnerProduct f Φ) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast Nat.card_pos.ne' : (Nat.card L : ℂ) ≠ 0), one_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [map_mul, Complex.conj_conj]

noncomputable def H (θ : L → ℂ) : ℂ :=
  ((θ 1 + 2 * S.N * θ S.W.J') ^ 2 - θ 1 ^ 2) / θ 1

theorem formula {Φ : L → ℂ} (hΦ : ∀ y : L, Even (orderOf y) → Φ y = 0) (d : (G → ℂ) → ℤ)
    (hd : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) Φ = d χ) :
    (Nat.card G : ℂ) * ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * d χ / χ 1 =
      Nat.card (Subgroup.centralizer ({S.J} : Set G)) *
        ∑ θ ∈ (irreducibles_finite L).toFinset,
          starRingEnd ℂ (BlocksInnerProduct θ Φ) * S.H θ := by
  set C := Subgroup.centralizer ({S.J} : Set G) with hCdef
  have hpt : ∀ ρ : L, Odd (orderOf ρ) →
      (Nat.card (ConjClasses.mk S.J).carrier : ℂ) ^ 2 / Nat.card G *
        ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * starRingEnd ℂ (S.σ χ ρ) / χ 1 =
      (Nat.card C : ℂ)⁻¹ * ∑ θ ∈ (irreducibles_finite L).toFinset,
        (((θ 1 + 2 * S.N * θ S.W.J') ^ 2 - θ 1 ^ 2) / θ 1) * starRingEnd ℂ (θ ρ) := by
    intro ρ hρ
    have hJ : S.J ∈ Subgroup.zpowers (S.J * S.κ ρ) :=
      Subgroup.mem_zpowers_iff.mpr ⟨orderOf ρ, by rw [zpow_natCast, S.pow_J_mul hρ]⟩
    have hyC : S.J * S.κ ρ ∈ C := Subgroup.mul_mem _ S.J_mem_centralizer (S.κ_mem_centralizer ρ)
    have h := involution_pair_formula S.J_mul hJ hyC
    simp only [σ]
    rw [h, S.sum_irr_C]
    congr 1
    refine Finset.sum_congr rfl fun θ hθ => ?_
    rw [Set.Finite.mem_toFinset] at hθ
    have hsgn1 : signChar (Subgroup.zpowers S.J) 1 = 1 := by simp [signChar]
    rw [S.classSum_ψ 1 rfl hθ, S.classSum_ψ _ hsgn1 hθ, S.ψ_Jκ, S.ψ_Jκ, S.signChar_Jz]
    have h1C : (1 : C) = ⟨S.κ 1, S.κ_mem_centralizer 1⟩ := Subtype.ext (by simp)
    have h1 : S.ψ 1 θ 1 = θ 1 := by rw [h1C, S.ψ_κ 1 rfl θ 1]
    have h2 : S.ψ (signChar _) θ 1 = θ 1 := by rw [h1C, S.ψ_κ _ hsgn1 θ 1]
    rw [h1, h2]
    simp only [Pi.one_apply, one_mul, map_neg, map_mul, map_one]
    have hθ1 : θ 1 ≠ 0 := by
      obtain ⟨n, hn, hn'⟩ := exists_deg hθ
      rw [hn']
      exact_mod_cast hn.ne'
    field_simp
    ring
  have hsum : ∀ ρ : L,
      (Nat.card (ConjClasses.mk S.J).carrier : ℂ) ^ 2 / Nat.card G *
        ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * starRingEnd ℂ (S.σ χ ρ) / χ 1 * Φ ρ =
      (Nat.card C : ℂ)⁻¹ * ∑ θ ∈ (irreducibles_finite L).toFinset,
        (((θ 1 + 2 * S.N * θ S.W.J') ^ 2 - θ 1 ^ 2) / θ 1) * starRingEnd ℂ (θ ρ) * Φ ρ := by
    intro ρ
    rcases Nat.even_or_odd (orderOf ρ) with he | ho
    · rw [hΦ ρ he]
      simp
    · rw [← Finset.sum_mul, ← Finset.sum_mul, ← mul_assoc, ← mul_assoc, hpt ρ ho]
  have htot := Finset.sum_congr rfl (fun ρ (_ : ρ ∈ Finset.univ) => hsum ρ)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_comm (γ := L)] at htot
  have hL : ∀ χ ∈ (irreducibles_finite G).toFinset,
      ∑ ρ : L, χ S.J ^ 2 * starRingEnd ℂ (S.σ χ ρ) / χ 1 * Φ ρ =
        χ S.J ^ 2 * d χ / χ 1 * Nat.card L := by
    intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    have h := sum_conj_mul (S.σ χ) Φ
    rw [hd χ hχ, map_intCast] at h
    calc ∑ ρ : L, χ S.J ^ 2 * starRingEnd ℂ (S.σ χ ρ) / χ 1 * Φ ρ
        = χ S.J ^ 2 / χ 1 * ∑ ρ : L, starRingEnd ℂ (S.σ χ ρ) * Φ ρ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ρ _ => by ring
      _ = _ := by rw [h]; ring
  have hR : ∀ θ ∈ (irreducibles_finite L).toFinset,
      ∑ ρ : L, (((θ 1 + 2 * S.N * θ S.W.J') ^ 2 - θ 1 ^ 2) / θ 1) *
        starRingEnd ℂ (θ ρ) * Φ ρ =
          S.H θ * (Nat.card L * starRingEnd ℂ (BlocksInnerProduct θ Φ)) := by
    intro θ _
    rw [← sum_conj_mul θ Φ, Finset.mul_sum, H]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at htot
  have hclass := card_conjClass_mul_card_centralizer S.J
  have hG0 : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hC0 : (Nat.card C : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hL0 : (Nat.card L : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hK : (Nat.card (ConjClasses.mk S.J).carrier : ℂ) = Nat.card G / Nat.card C := by
    rw [eq_div_iff hC0]
    exact_mod_cast hclass
  have e1 : ∑ θ ∈ (irreducibles_finite L).toFinset,
      S.H θ * (Nat.card L * starRingEnd ℂ (BlocksInnerProduct θ Φ)) =
      Nat.card L * ∑ θ ∈ (irreducibles_finite L).toFinset,
        starRingEnd ℂ (BlocksInnerProduct θ Φ) * S.H θ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun θ _ => by ring
  rw [hK, e1, ← Finset.sum_mul] at htot
  set A := ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * (d χ : ℂ) / χ 1 with hA
  set B := ∑ θ ∈ (irreducibles_finite L).toFinset,
    starRingEnd ℂ (BlocksInnerProduct θ Φ) * S.H θ with hB
  calc (Nat.card G : ℂ) * A
      = ((Nat.card G / Nat.card C : ℂ) ^ 2 / Nat.card G * (A * Nat.card L)) *
          ((Nat.card C : ℂ) ^ 2 / Nat.card L) := by
        field_simp
    _ = ((Nat.card C : ℂ)⁻¹ * (Nat.card L * B)) * ((Nat.card C : ℂ) ^ 2 / Nat.card L) := by
        rw [htot]
    _ = Nat.card C * B := by
        field_simp

theorem card_C : (Nat.card (Subgroup.centralizer ({S.J} : Set G)) : ℂ) = q * ((q : ℂ) ^ 2 - 1) := by
  rw [← Nat.card_congr S.eC.toEquiv, S.card_prod]
  have h := S.W.card
  have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by have := S.q_ge; omega)
  have h' : ((2 * Nat.card L : ℕ) : ℂ) = ((q * (q ^ 2 - 1) : ℕ) : ℂ) := by rw [h]
  push_cast [Nat.cast_sub hq] at h' ⊢
  exact h'

include S in
theorem q_ne_zero : (q : ℂ) ≠ 0 := by
  have := S.q_ge
  exact_mod_cast (show q ≠ 0 by omega)

include S in
theorem q_add_e_ne_zero : (q : ℂ) + e ≠ 0 := by
  have h1 := S.q_ge
  have h2 := S.W.e_eq
  have : (q : ℤ) + e ≠ 0 := by rcases h2 with h | h <;> rw [h] <;> omega
  exact_mod_cast this

include S in
theorem q_sub_e_ne_zero : (q : ℂ) - e ≠ 0 := by
  have h1 := S.q_ge
  have h2 := S.W.e_eq
  have : (q : ℤ) - e ≠ 0 := by rcases h2 with h | h <;> rw [h] <;> omega
  exact_mod_cast this

include S in
theorem e_sq_c : (e : ℂ) * e = 1 := S.W.e_sq_complex

theorem N_eq : (S.N : ℂ) = q * (q + e) / 2 := by
  have h := S.W.card_class_J'
  have hL : (Nat.card L : ℂ) * 2 = q * ((q : ℂ) ^ 2 - 1) := by
    have h' := S.W.card
    have hq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by have := S.q_ge; omega)
    have h'' : ((2 * Nat.card L : ℕ) : ℂ) = ((q * (q ^ 2 - 1) : ℕ) : ℂ) := by rw [h']
    push_cast [Nat.cast_sub hq] at h''
    linear_combination h''
  rw [N]
  apply mul_right_cancel₀ S.q_sub_e_ne_zero
  have he := S.e_sq_c
  linear_combination h + hL / 2 + (q : ℂ) / 2 * he

theorem val_J' : S.W.θ2 S.W.J' = -e ∧ S.W.θ3 S.W.J' = -e ∧ S.W.θ4 S.W.J' = e ∧
    (∀ θ ∈ S.W.RFam, θ S.W.J' = 0) ∧
    (∀ θ ∈ S.W.SFam, θ S.W.J' = 2 * e * S.W.eps θ) := by
  obtain ⟨h2, h3, h4, hR⟩ := S.W.val_J'So 1 (Subgroup.one_mem _)
  rw [mul_one] at h2 h3 h4 hR
  refine ⟨h2, h3, h4, hR, fun θ hθ => ?_⟩
  have h := S.W.valS_J'So θ hθ 1
  simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, inv_one] at h
  rw [h]
  ring

include S in
theorem e_cases : (e : ℂ) = 1 ∨ (e : ℂ) = -1 := by
  rcases S.W.e_eq with h | h <;> [left; right] <;> rw [h] <;> norm_num

theorem H_one : S.H 1 = q * (q + e) * (q * (q + e) + 2) := by
  rw [H, Pi.one_apply, Pi.one_apply, S.N_eq]
  ring

omit [Fintype L] in
theorem H2_alg (q E : ℂ) (hE : E = 1 ∨ E = -1) (hq : q + E ≠ 0) :
    (((q + E) / 2 + 2 * (q * (q + E) / 2) * (-E)) ^ 2 - ((q + E) / 2) ^ 2) / ((q + E) / 2) =
      2 * q * (q ^ 2 - 1) := by
  rcases hE with rfl | rfl <;> field_simp <;> ring

omit [Fintype L] in
theorem H4_alg (q E : ℂ) (hE : E = 1 ∨ E = -1) (hq : q ≠ 0) :
    ((q + 2 * (q * (q + E) / 2) * E) ^ 2 - q ^ 2) / q = q * (E * q + 1) * (E * q + 3) := by
  rcases hE with rfl | rfl <;> field_simp <;> ring

omit [Fintype L] in
theorem HS_alg (q E F : ℂ) (hE : E = 1 ∨ E = -1) (hF : F = 1 ∨ F = -1) (hq : q + E ≠ 0) :
    ((q + E + 2 * (q * (q + E) / 2) * (2 * E * F)) ^ 2 - (q + E) ^ 2) / (q + E) =
      4 * q * (q + E) * (E * F + q) := by
  rcases hE with rfl | rfl <;> rcases hF with rfl | rfl <;> field_simp <;> ring

theorem H_θ2 : S.H S.W.θ2 = 2 * q * ((q : ℂ) ^ 2 - 1) := by
  rw [H, S.val_J'.1, S.N_eq, S.W.deg2]
  exact H2_alg q e S.e_cases S.q_add_e_ne_zero

theorem H_θ3 : S.H S.W.θ3 = 2 * q * ((q : ℂ) ^ 2 - 1) := by
  rw [H, S.val_J'.2.1, S.N_eq, S.W.deg3]
  exact H2_alg q e S.e_cases S.q_add_e_ne_zero

theorem H_θ4 : S.H S.W.θ4 = q * (e * q + 1) * (e * q + 3) := by
  rw [H, S.val_J'.2.2.1, S.N_eq, S.W.deg4]
  exact H4_alg q e S.e_cases S.q_ne_zero

theorem H_S {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    S.H θ = 4 * q * (q + e) * (e * S.W.eps θ + q) := by
  rw [H, S.val_J'.2.2.2.2 θ hθ, S.N_eq, S.W.degS θ hθ]
  have hF : (S.W.eps θ : ℂ) = 1 ∨ (S.W.eps θ : ℂ) = -1 := by
    rcases S.W.eps_eq θ hθ with h | h <;> [left; right] <;> rw [h] <;> norm_num
  exact HS_alg q e (S.W.eps θ) S.e_cases hF S.q_add_e_ne_zero

theorem formula_Φ1 :
    (Nat.card G : ℂ) * ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * S.d1 χ / χ 1 =
      q ^ 2 * ((q : ℂ) ^ 2 - 1) ^ 2 * (q + e) := by
  rw [S.formula (fun y hy => S.W.Φ1_even hy) S.d1 (fun χ hχ => S.inner_Φ1 hχ), S.card_C,
    S.W.sum_irr]
  obtain ⟨i11, -, -, i14, i21, -, -, i24, i31, -, -, i34, i41, -, -, i44⟩ :=
    S.W.inner_principal
  have hR : ∑ θ ∈ S.W.RFam, starRingEnd ℂ (BlocksInnerProduct θ S.W.Φ1) * S.H θ = 0 :=
    Finset.sum_eq_zero fun θ hθ => by
      rw [(S.W.gram_principal_other (Or.inl hθ)).2.2.2.1, map_zero, zero_mul]
  have hS : ∑ θ ∈ S.W.SFam, starRingEnd ℂ (BlocksInnerProduct θ S.W.Φ1) * S.H θ = 0 :=
    Finset.sum_eq_zero fun θ hθ => by
      rw [(S.W.gram_principal_other (Or.inr hθ)).2.2.2.1, map_zero, zero_mul]
  rw [hR, hS]
  simp only [WardL.Φ1, blocksInnerProduct_sub_right, blocksInnerProduct_smul_right, WardL.conj_e,
    i11, i14, i21, i24, i31, i34, i41, i44]
  rw [S.H_one, S.H_θ4]
  simp only [mul_zero, sub_zero, mul_one, zero_sub, map_one, map_zero, zero_mul, add_zero,
    map_neg, map_intCast]
  rcases S.e_cases with he | he <;> rw [he] <;> ring

theorem formula_Φ2 :
    (Nat.card G : ℂ) * ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * S.d2 χ / χ 1 =
      -e * q ^ 2 * ((q : ℂ) ^ 2 - 1) * (q + e) * (3 * q + e) := by
  rw [S.formula (fun y hy => S.W.Φ2_even hy) S.d2 (fun χ hχ => S.inner_Φ2 hχ), S.card_C,
    S.W.sum_irr]
  obtain ⟨-, i12, -, i14, -, i22, -, i24, -, i32, -, i34, -, i42, -, i44⟩ :=
    S.W.inner_principal
  have hR : ∑ θ ∈ S.W.RFam, starRingEnd ℂ (BlocksInnerProduct θ S.W.Φ2) * S.H θ = 0 :=
    Finset.sum_eq_zero fun θ hθ => by
      rw [(S.W.gram_principal_other (Or.inl hθ)).2.2.2.2.1, map_zero, zero_mul]
  have hS : ∑ θ ∈ S.W.SFam, starRingEnd ℂ (BlocksInnerProduct θ S.W.Φ2) * S.H θ = 0 :=
    Finset.sum_eq_zero fun θ hθ => by
      rw [(S.W.gram_principal_other (Or.inr hθ)).2.2.2.2.1, map_zero, zero_mul]
  rw [hR, hS]
  simp only [WardL.Φ2, blocksInnerProduct_add_right, blocksInnerProduct_smul_right, map_neg,
    WardL.conj_e, i12, i14, i22, i24, i32, i34, i42, i44]
  rw [S.H_θ2, S.H_θ4]
  simp only [mul_zero, add_zero, zero_add, mul_one, map_neg, map_intCast, map_zero, zero_mul]
  rcases S.e_cases with he | he <;> rw [he] <;> ring

theorem formula_ΦS {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    (Nat.card G : ℂ) * ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * S.dS χ θ / χ 1 =
      8 * q ^ 3 * ((q : ℂ) ^ 2 - 1) * (q + e) := by
  rw [S.formula (fun y hy => S.W.ΦS_even hθ hy) (S.dS · θ) (fun χ hχ => S.inner_ΦS hχ hθ),
    S.card_C, S.W.sum_irr]
  have hsθ := S.W.sbar_mem θ hθ
  obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := S.W.inner_principal_other (Or.inr hθ)
  obtain ⟨b1, b2, b3, b4, -, -, -, -⟩ := S.W.inner_principal_other (Or.inr hsθ)
  have hR : ∑ θ' ∈ S.W.RFam, starRingEnd ℂ (BlocksInnerProduct θ' (S.W.ΦS θ)) * S.H θ' = 0 :=
    Finset.sum_eq_zero fun θ' hθ' => by
      rw [(S.W.gram_R_S hθ' hθ).1, map_zero, zero_mul]
  have hS : ∑ θ' ∈ S.W.SFam, starRingEnd ℂ (BlocksInnerProduct θ' (S.W.ΦS θ)) * S.H θ' =
      S.H θ + S.H (S.W.sbar θ) := by
    have hval : ∀ θ' ∈ S.W.SFam, starRingEnd ℂ (BlocksInnerProduct θ' (S.W.ΦS θ)) * S.H θ' =
        (if θ' = θ then S.H θ' else 0) + (if θ' = S.W.sbar θ then S.H θ' else 0) := by
      intro θ' hθ'
      rw [WardL.ΦS, blocksInnerProduct_add_right, S.W.inner_RS (Or.inr hθ') (Or.inr hθ),
        S.W.inner_RS (Or.inr hθ') (Or.inr hsθ)]
      split_ifs <;> simp; ring
    rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
      ite_eq_left hθ, ite_eq_left hsθ]
  rw [hR, hS]
  simp only [WardL.ΦS, blocksInnerProduct_add_right, a1, a2, a3, a4, b1, b2, b3, b4, add_zero,
    map_zero, zero_mul]
  rw [S.H_S hθ, S.H_S hsθ, S.W.eps_sbar θ hθ]
  push_cast
  rcases S.e_cases with he | he <;> rw [he] <;> ring

end WardSetup

end CFSG.Walter.Ward
