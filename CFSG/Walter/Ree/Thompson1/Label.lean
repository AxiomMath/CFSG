module

public import CFSG.Walter.Ree.Thompson1.FunEq
public import CFSG.Walter.Ree.ThompsonN
import Mathlib.Tactic.ReduceModChar
public import CFSG.Walter.Ree.Thompson1.Layers

public section

namespace CFSG.Walter.Ree.Thompson1

variable {N : Type*} [Group N] {q : ℕ} {P R : Subgroup N}
  (h : ThompsonIConditions q P R) {K : Type*} [Field K]
  {σ : K ≃+* K} {r : Kˣ →* N} {ℓ₁ ℓ₂ ℓ₃ : N → K} (hc : NormalCoords P R σ r ℓ₁ ℓ₂ ℓ₃)

section Z

include hc

noncomputable def zf (γ : K) : N := Classical.choose (hc.c3.surj γ)

theorem zf_mem (γ : K) : zf hc γ ∈ zc P := (Classical.choose_spec (hc.c3.surj γ)).1

theorem l3_zf (γ : K) : ℓ₃ (zf hc γ) = γ := (Classical.choose_spec (hc.c3.surj γ)).2

theorem eq_zf {w : N} (hw : w ∈ zc P) : w = zf hc (ℓ₃ w) := by
  have := (hc.c3.eq_iff hw (zf_mem hc _)).1 (l3_zf hc _).symm
  rw [Subgroup.mem_bot, inv_mul_eq_one] at this
  exact this.symm

theorem zf_add (γ γ' : K) : zf hc (γ + γ') = zf hc γ * zf hc γ' := by
  rw [eq_zf hc ((zc P).mul_mem (zf_mem hc γ) (zf_mem hc γ')),
    hc.c3.add _ (zf_mem hc γ) _ (zf_mem hc γ'), l3_zf hc γ, l3_zf hc γ']

theorem zf_zero : zf hc 0 = 1 := by
  have := eq_zf hc (zc P).one_mem
  rw [hc.c3.one] at this
  exact this.symm

end Z

section J

include hc

theorem invol_mem : r (-1) ∈ R := hc.r_mem _

theorem invol_order [CharP K 3] : orderOf (r (-1)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← map_pow, neg_one_sq, map_one]
  · have := hc.r_inj (h1.trans (map_one r).symm)
    have h2 : ((-1 : Kˣ) : K) = 1 := by rw [this]; rfl
    have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    have h4 : (1 : K) = 0 := by
      have : (2 : K) = 0 := by rw [Units.val_neg, Units.val_one] at h2; linear_combination -h2
      linear_combination h3 - this
    exact one_ne_zero h4

omit hc in
theorem r_comm (κ κ' : Kˣ) : r κ * r κ' = r κ' * r κ := by
  rw [← map_mul, mul_comm, map_mul]

include h

theorem conj_zf (κ : Kˣ) (γ : K) :
    (r κ)⁻¹ * zf hc γ * r κ = zf hc ((κ : K) ^ 2 * σ κ * γ) := by
  rw [eq_zf hc (conj_mem_zc h (zf_mem hc γ)), hc.eq3 κ _ (zf_mem hc γ), l3_zf hc γ]

theorem invol_conj_zf [CharP K 3] (γ : K) : (r (-1))⁻¹ * zf hc γ * r (-1) = zf hc (-γ) := by
  rw [conj_zf h hc]
  congr 1
  simp

end J

section Y

variable [Finite N] [Fintype K] [CharP K 3] (hK : Fintype.card K = q)
include h hc hK

theorem exists_P0 (β : K) : ∃ c ∈ P ⊓ Subgroup.centralizer {r (-1)}, ℓ₂ c = β := by
  have hJ := invol_mem hc
  have hJ2 := invol_order hc
  let f : (P ⊓ Subgroup.centralizer {r (-1)} : Subgroup N) → K := fun c => ℓ₂ c.1
  have hf : Function.Injective f := by
    intro c c' he
    have hc2 := P0_le h hJ hJ2 c.2
    have hc2' := P0_le h hJ hJ2 c'.2
    have hz := (hc.c2.eq_iff hc2 hc2').1 he
    have hw : c'.1⁻¹ * c.1 ∈ (P ⊓ Subgroup.centralizer {r (-1)}) ⊓ zc P :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ c'.2) c.2, hz⟩
    rw [P0_inf_zc h hJ hJ2, Subgroup.mem_bot, inv_mul_eq_one] at hw
    exact Subtype.ext hw.symm
  have hcard : Nat.card K ≤ Nat.card (P ⊓ Subgroup.centralizer {r (-1)} : Subgroup N) := by
    rw [card_P0 h hJ hJ2, Nat.card_eq_fintype_card, hK]
  obtain ⟨c, hc'⟩ := (hf.bijective_of_nat_card_le hcard).2 β
  exact ⟨c.1, c.2, hc'⟩

noncomputable def yf (β : K) : N := Classical.choose (exists_P0 h hc hK β)

theorem yf_mem (β : K) : yf h hc hK β ∈ P ⊓ Subgroup.centralizer {r (-1)} :=
  (Classical.choose_spec (exists_P0 h hc hK β)).1

theorem yf_mem' (β : K) : yf h hc hK β ∈ ⁅P, P⁆ :=
  P0_le h (invol_mem hc) (invol_order hc) (yf_mem h hc hK β)

theorem yf_mem_P (β : K) : yf h hc hK β ∈ P := commutator_le h (yf_mem' h hc hK β)

theorem l2_yf (β : K) : ℓ₂ (yf h hc hK β) = β := (Classical.choose_spec (exists_P0 h hc hK β)).2

theorem eq_yf {c : N} (hc' : c ∈ P ⊓ Subgroup.centralizer {r (-1)}) : c = yf h hc hK (ℓ₂ c) := by
  have hJ := invol_mem hc
  have hJ2 := invol_order hc
  have hz := (hc.c2.eq_iff (P0_le h hJ hJ2 hc') (yf_mem' h hc hK (ℓ₂ c))).1
    (l2_yf h hc hK _).symm
  have hw : (yf h hc hK (ℓ₂ c))⁻¹ * c ∈ (P ⊓ Subgroup.centralizer {r (-1)}) ⊓ zc P :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (yf_mem h hc hK _)) hc', hz⟩
  rw [P0_inf_zc h hJ hJ2, Subgroup.mem_bot, inv_mul_eq_one] at hw
  exact hw.symm

theorem yf_add (β β' : K) : yf h hc hK (β + β') = yf h hc hK β * yf h hc hK β' := by
  rw [eq_yf h hc hK (Subgroup.mul_mem _ (yf_mem h hc hK β) (yf_mem h hc hK β')),
    hc.c2.add _ (yf_mem' h hc hK β) _ (yf_mem' h hc hK β'), l2_yf h hc hK β,
    l2_yf h hc hK β']

theorem yf_zero : yf h hc hK 0 = 1 := by
  have := eq_yf h hc hK (Subgroup.one_mem (P ⊓ Subgroup.centralizer {r (-1)}))
  rw [hc.c2.one] at this
  exact this.symm

theorem conj_yf (κ : Kˣ) (β : K) :
    (r κ)⁻¹ * yf h hc hK β * r κ = yf h hc hK ((κ : K) * σ κ * β) := by
  have hm := yf_mem h hc hK β
  have hmem : (r κ)⁻¹ * yf h hc hK β * r κ ∈ P ⊓ Subgroup.centralizer {r (-1)} := by
    refine mem_P0.2 ⟨conj_mem_P h hm.1, ?_⟩
    have e : (r (-1))⁻¹ * ((r κ)⁻¹ * yf h hc hK β * r κ) * r (-1) =
        (r κ)⁻¹ * ((r (-1))⁻¹ * yf h hc hK β * r (-1)) * r κ := by
      have e1 : r κ * r (-1) = r (-1) * r κ := r_comm κ (-1)
      have e2 : (r (-1))⁻¹ * (r κ)⁻¹ = (r κ)⁻¹ * (r (-1))⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, e1]
      calc (r (-1))⁻¹ * ((r κ)⁻¹ * yf h hc hK β * r κ) * r (-1)
          = ((r (-1))⁻¹ * (r κ)⁻¹) * yf h hc hK β * (r κ * r (-1)) := by group
        _ = ((r κ)⁻¹ * (r (-1))⁻¹) * yf h hc hK β * (r (-1) * r κ) := by rw [e1, e2]
        _ = (r κ)⁻¹ * ((r (-1))⁻¹ * yf h hc hK β * r (-1)) * r κ := by group
    rw [e, (mem_P0.1 hm).2]
  rw [eq_yf h hc hK hmem, hc.eq2 κ _ (yf_mem' h hc hK β), l2_yf h hc hK β]

theorem invol_conj_yf (β : K) : (r (-1))⁻¹ * yf h hc hK β * r (-1) = yf h hc hK β :=
  (mem_P0.1 (yf_mem h hc hK β)).2

end Y

open Classical in
@[expose] noncomputable def x0f (r : Kˣ →* N) (p : N) (α : K) : N :=
  if hα : α = 0 then 1 else (r (Units.mk0 α hα))⁻¹ * p * r (Units.mk0 α hα)

section X

variable {p : N}

theorem x0f_zero : x0f r p (0 : K) = 1 := by simp [x0f]

theorem x0f_units (κ : Kˣ) : x0f r p (κ : K) = (r κ)⁻¹ * p * r κ := by
  simp only [x0f, κ.ne_zero, dite_false, Units.mk0_val]

theorem conj_x0f (κ : Kˣ) (α : K) : (r κ)⁻¹ * x0f r p α * r κ = x0f r p (α * κ) := by
  rcases eq_or_ne α 0 with rfl | hα
  · simp [x0f_zero]
  · obtain ⟨κ₀, rfl⟩ : ∃ κ₀ : Kˣ, (κ₀ : K) = α := ⟨Units.mk0 α hα, rfl⟩
    rw [← Units.val_mul, x0f_units, x0f_units, map_mul]
    group

include h in
theorem x0f_mem (hp : p ∈ P) (α : K) : x0f r p α ∈ P := by
  unfold x0f
  split_ifs
  · exact P.one_mem
  · exact conj_mem_P h hp

include hc in
theorem l1_x0f (hp : p ∈ P) (hp1 : ℓ₁ p = 1) (α : K) : ℓ₁ (x0f r p α) = α := by
  rcases eq_or_ne α 0 with rfl | hα
  · rw [x0f_zero, hc.c1.one]
  · obtain ⟨κ₀, rfl⟩ : ∃ κ₀ : Kˣ, (κ₀ : K) = α := ⟨Units.mk0 α hα, rfl⟩
    rw [x0f_units, hc.eq1 _ _ hp, hp1, mul_one]

theorem x0f_neg (hpinv : (r (-1))⁻¹ * p * r (-1) = p⁻¹) (α : K) :
    x0f r p (-α) = (x0f r p α)⁻¹ := by
  rcases eq_or_ne α 0 with rfl | hα
  · simp [x0f_zero]
  · obtain ⟨κ₀, rfl⟩ : ∃ κ₀ : Kˣ, (κ₀ : K) = α := ⟨Units.mk0 α hα, rfl⟩
    have e : -(κ₀ : K) = (κ₀ : K) * ((-1 : Kˣ) : K) := by simp
    rw [e, ← conj_x0f, x0f_units]
    set u := r κ₀
    have hu : u * r (-1) = r (-1) * u := r_comm _ _
    calc (r (-1))⁻¹ * (u⁻¹ * p * u) * r (-1) = u⁻¹ * ((r (-1))⁻¹ * p * r (-1)) * u := by
          have e2 : (r (-1))⁻¹ * u⁻¹ = u⁻¹ * (r (-1))⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, hu]
          calc (r (-1))⁻¹ * (u⁻¹ * p * u) * r (-1) = ((r (-1))⁻¹ * u⁻¹) * p * (u * r (-1)) := by
                group
            _ = (u⁻¹ * (r (-1))⁻¹) * p * (r (-1) * u) := by rw [e2, hu]
            _ = u⁻¹ * ((r (-1))⁻¹ * p * r (-1)) * u := by group
      _ = (u⁻¹ * p * u)⁻¹ := by rw [hpinv]; group

include h hc in
theorem exists_p [CharP K 3] : ∃ p ∈ P, ℓ₁ p = 1 ∧ (r (-1))⁻¹ * p * r (-1) = p⁻¹ := by
  obtain ⟨x₁, hx₁, hx₁1⟩ := hc.c1.surj 1
  refine ⟨x₁⁻¹ * ((r (-1))⁻¹ * x₁ * r (-1)), P.mul_mem (P.inv_mem hx₁) (conj_mem_P h hx₁), ?_,
    invol_conj_inverted (invol_order hc) x₁⟩
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  rw [hc.c1.add _ (P.inv_mem hx₁) _ (conj_mem_P h hx₁), hc.c1.inv hx₁, hc.eq1 _ _ hx₁, hx₁1]
  simp only [Units.val_neg, Units.val_one]
  linear_combination -h3

end X

section GF

variable (σ) in
@[expose] def gF (α β : K) : K := σ α * β ^ 2 + α * β * σ β - α ^ 2 * σ β

theorem gF_cocycle [CharP K 3] (α l ξ : K) :
    gF σ α l + gF σ (α + l) ξ - gF σ l ξ - gF σ α (l + ξ) = ξ * (σ α * l - α * σ l) := by
  simp only [gF, map_add]
  linear_combination (norm := skip)
  ring_nf
  reduce_mod_char!

theorem gF_homog (κ α β : K) : gF σ (α * κ) (β * κ) = κ ^ 2 * σ κ * gF σ α β := by
  simp only [gF, map_mul]
  ring

theorem gF_zero_right (α : K) : gF σ α 0 = 0 := by simp [gF]

theorem kk_eq19 [CharP K 3] : Eq19 σ (kk σ) := by
  intro x y
  rcases eq_or_ne x 0 with rfl | hx
  · simp [kk, pw]
  rcases eq_or_ne (1 + x) 0 with hx1 | hx1
  · have hx' : x = -1 := by linear_combination hx1
    subst hx'
    simp only [kk, pw, hx1, div_zero, map_zero, sub_zero, mul_zero, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero, map_neg, map_one, div_neg, div_one,
      map_add]
    linear_combination (norm := skip)
    ring_nf
    reduce_mod_char!
  have hsx : σ x ≠ 0 := by simpa using hx
  have hsx1 : 1 + σ x ≠ 0 := by
    rw [← map_one σ, ← map_add]; exact (map_ne_zero σ).2 hx1
  simp only [kk, pw, map_div₀, map_add, map_one]
  field_simp
  rw [← sub_eq_zero]
  ring_nf
  reduce_mod_char!

theorem kk_div_pw {α β : K} (hβ : β ≠ 0) :
    kk σ (α / β) * pw σ β = (α - β) * (α * σ β - σ α * β) := by
  have hsβ : σ β ≠ 0 := by simpa using hβ
  simp only [kk, pw, map_div₀]
  field_simp

end GF

section Product

variable [Finite N] [Fintype K] [CharP K 3] (hK : Fintype.card K = q)

@[expose] noncomputable def NF (p : N) (γ β η : K) : N :=
  x0f r p γ * yf h hc hK β * zf hc η

omit [Finite N] [Fintype K] [CharP K 3] in
theorem zf_comm {x : N} (hx : x ∈ P) (η : K) : zf hc η * x = x * zf hc η :=
  zc_comm (zf_mem hc η) hx

include h hc hK

theorem yf_comm (β β' : K) : yf h hc hK β * yf h hc hK β' = yf h hc hK β' * yf h hc hK β :=
  commutator_comm h (yf_mem' h hc hK β) (yf_mem' h hc hK β')

theorem yf_mul {x : N} (hx : x ∈ P) (β : K) :
    yf h hc hK β * x = x * yf h hc hK β * zf hc (β * ℓ₁ x) := by
  have hm := tc_mem_zc h (yf_mem' h hc hK β) hx
  have e : tc (yf h hc hK β) x = zf hc (β * ℓ₁ x) := by
    rw [eq_zf hc hm, hc.br2 _ _ (yf_mem' h hc hK β) hx, l2_yf h hc hK β]
  rw [← e]
  unfold tc
  group

variable {p : N} (hp : p ∈ P) (hp1 : ℓ₁ p = 1) (hpinv : (r (-1))⁻¹ * p * r (-1) = p⁻¹)
include hp hp1

omit hp1 in
theorem NF_mem (γ β η : K) : NF h hc hK p γ β η ∈ P :=
  P.mul_mem (P.mul_mem (x0f_mem h hp γ) (yf_mem_P h hc hK β)) (zc_le P (zf_mem hc η))

theorem l1_NF (γ β η : K) : ℓ₁ (NF h hc hK p γ β η) = γ := by
  have hy := yf_mem' h hc hK β
  have hz := zc_le_commutator h (zf_mem hc η)
  rw [NF, hc.c1.add _ (P.mul_mem (x0f_mem h hp γ) (commutator_le h hy)) _ (commutator_le h hz),
    hc.c1.add _ (x0f_mem h hp γ) _ (commutator_le h hy), l1_x0f hc hp hp1,
    (hc.c1.ker _ (commutator_le h hy)).2 hy, (hc.c1.ker _ (commutator_le h hz)).2 hz,
    add_zero, add_zero]

omit hp hp1 in
theorem l2_yf_zf (β η : K) : ℓ₂ (yf h hc hK β * zf hc η) = β := by
  have hz := zc_le_commutator h (zf_mem hc η)
  rw [hc.c2.add _ (yf_mem' h hc hK β) _ hz, l2_yf h hc hK β, (hc.c2.ker _ hz).2 (zf_mem hc η),
    add_zero]

theorem NF_inj {γ β η γ' β' η' : K} (he : NF h hc hK p γ β η = NF h hc hK p γ' β' η') :
    γ = γ' ∧ β = β' ∧ η = η' := by
  have h1 : γ = γ' := by
    have := congrArg ℓ₁ he
    rwa [l1_NF h hc hK hp hp1, l1_NF h hc hK hp hp1] at this
  subst h1
  have he' : yf h hc hK β * zf hc η = yf h hc hK β' * zf hc η' := by
    unfold NF at he
    rw [mul_assoc, mul_assoc] at he
    exact mul_left_cancel he
  have h2 : β = β' := by
    have := congrArg ℓ₂ he'
    rwa [l2_yf_zf h hc hK, l2_yf_zf h hc hK] at this
  subst h2
  have he'' : zf hc η = zf hc η' := mul_left_cancel he'
  have := congrArg ℓ₃ he''
  rw [l3_zf hc η, l3_zf hc η'] at this
  exact ⟨rfl, rfl, this⟩

omit [Finite N] [Fintype K] [CharP K 3] hK in
theorem W_mem (α β : K) : (x0f r p (α + β))⁻¹ * x0f r p α * x0f r p β ∈ ⁅P, P⁆ := by
  have hx := fun γ => x0f_mem h hp (r := r) γ
  refine (hc.c1.ker _ (P.mul_mem (P.mul_mem (P.inv_mem (hx _)) (hx α)) (hx β))).1 ?_
  rw [hc.c1.add _ (P.mul_mem (P.inv_mem (hx _)) (hx α)) _ (hx β),
    hc.c1.add _ (P.inv_mem (hx _)) _ (hx α), hc.c1.inv (hx _), l1_x0f hc hp hp1,
    l1_x0f hc hp hp1, l1_x0f hc hp hp1]
  ring

omit [Finite N] [Fintype K] [CharP K 3] hK hp hp1 in
theorem l2_conj {u v : N} (hu : u ∈ P) (hv : v ∈ ⁅P, P⁆) : ℓ₂ (u⁻¹ * v * u) = ℓ₂ v := by
  have hm := tc_mem_zc h hv hu
  rw [conj_eq_mul_tc, hc.c2.add _ hv _ (zc_le_commutator h hm), (hc.c2.ker _ (zc_le_commutator h
    hm)).2 hm, add_zero]

omit h [Finite N] [Fintype K] [CharP K 3] hK hp hp1 in
theorem l2_invol_conj {v : N} (hv : v ∈ ⁅P, P⁆) : ℓ₂ ((r (-1))⁻¹ * v * r (-1)) = ℓ₂ v := by
  rw [hc.eq2 _ _ hv]
  simp

omit [Finite N] [Fintype K] hK in
include hpinv in
theorem l2_W (α β : K) :
    ℓ₂ ((x0f r p (α + β))⁻¹ * x0f r p α * x0f r p β) = α * σ β - σ α * β := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hx := fun γ => x0f_mem h hp (r := r) γ
  have e : ∀ γ : K, x0f r p (-γ) = (r (-1))⁻¹ * x0f r p γ * r (-1) := fun γ => by
    rw [conj_x0f]; simp
  have hWneg : (x0f r p (-α + -β))⁻¹ * x0f r p (-α) * x0f r p (-β) =
      (r (-1))⁻¹ * ((x0f r p (α + β))⁻¹ * x0f r p α * x0f r p β) * r (-1) := by
    rw [show -α + -β = -(α + β) by ring, e, e, e]
    group
  have htc : tc (x0f r p α) (x0f r p β) =
      (x0f r p (α + β))⁻¹ * ((x0f r p (-α + -β))⁻¹ * x0f r p (-α) * x0f r p (-β)) *
        x0f r p (α + β) * ((x0f r p (α + β))⁻¹ * x0f r p α * x0f r p β) := by
    unfold tc
    rw [x0f_neg hpinv, x0f_neg hpinv, show -α + -β = -(α + β) by ring, x0f_neg hpinv]
    group
  have hWm := W_mem h hc hp hp1 (-α) (-β)
  have hWp := W_mem h hc hp hp1 α β
  have hb := hc.br1 _ _ (hx α) (hx β)
  rw [l1_x0f hc hp hp1, l1_x0f hc hp hp1, htc,
    hc.c2.add _ (conj_mem_commutator h hWm) _ hWp, l2_conj h hc (hx _) hWm, hWneg,
    l2_invol_conj hc hWp] at hb
  linear_combination -hb + ℓ₂ ((x0f r p (α + β))⁻¹ * x0f r p α * x0f r p β) * h3

omit hp hp1 in
variable (p) in
@[expose] noncomputable def Hf (α β : K) : K :=
  ℓ₃ ((yf h hc hK (α * σ β - σ α * β))⁻¹ * ((x0f r p (α + β))⁻¹ * x0f r p α * x0f r p β))

include hpinv in
theorem x0f_mul (α β : K) :
    x0f r p α * x0f r p β = NF h hc hK p (α + β) (α * σ β - σ α * β) (Hf h hc hK p α β) := by
  have hWp := W_mem h hc hp hp1 α β
  have hl := l2_W h hc hp hp1 hpinv α β
  set W := (x0f r p (α + β))⁻¹ * x0f r p α * x0f r p β with hW
  have hv : (yf h hc hK (α * σ β - σ α * β))⁻¹ * W ∈ zc P := by
    have hm : (yf h hc hK (α * σ β - σ α * β))⁻¹ * W ∈ ⁅P, P⁆ :=
      (⁅P, P⁆ : Subgroup N).mul_mem ((⁅P, P⁆ : Subgroup N).inv_mem (yf_mem' h hc hK _)) hWp
    refine (hc.c2.ker _ hm).1 ?_
    rw [hc.c2.add _ ((⁅P, P⁆ : Subgroup N).inv_mem (yf_mem' h hc hK _)) _ hWp,
      hc.c2.inv (yf_mem' h hc hK _), l2_yf h hc hK, hl, neg_add_cancel]
  have e := eq_zf hc hv
  unfold NF Hf
  rw [← hW, ← e]
  rw [hW]
  group

include hpinv in
theorem NF_mul_x0f (γ β η ξ : K) : NF h hc hK p γ β η * x0f r p ξ =
    NF h hc hK p (γ + ξ) (γ * σ ξ - σ γ * ξ + β) (Hf h hc hK p γ ξ + β * ξ + η) := by
  have hx := x0f_mem h hp (r := r) ξ
  have e1 : yf h hc hK β * x0f r p ξ = x0f r p ξ * yf h hc hK β * zf hc (β * ξ) := by
    rw [yf_mul h hc hK hx, l1_x0f hc hp hp1]
  unfold NF
  calc x0f r p γ * yf h hc hK β * zf hc η * x0f r p ξ
      = x0f r p γ * (yf h hc hK β * x0f r p ξ) * zf hc η := by
        rw [mul_assoc _ (zf hc η), zf_comm hc hx η]; group
    _ = (x0f r p γ * x0f r p ξ) * yf h hc hK β * (zf hc (β * ξ) * zf hc η) := by
        rw [e1]; group
    _ = x0f r p (γ + ξ) * yf h hc hK (γ * σ ξ - σ γ * ξ) * (zf hc (Hf h hc hK p γ ξ) *
          yf h hc hK β) * (zf hc (β * ξ) * zf hc η) := by
        rw [x0f_mul h hc hK hp hp1 hpinv]; unfold NF; group
    _ = x0f r p (γ + ξ) * yf h hc hK (γ * σ ξ - σ γ * ξ + β) *
          zf hc (Hf h hc hK p γ ξ + β * ξ + η) := by
        rw [zf_comm hc (yf_mem_P h hc hK β), yf_add h hc hK, zf_add hc, zf_add hc]; group

omit hp hp1 in
theorem NF_mul_yf (γ β η b : K) :
    NF h hc hK p γ β η * yf h hc hK b = NF h hc hK p γ (β + b) η := by
  unfold NF
  rw [mul_assoc _ (zf hc η), zf_comm hc (yf_mem_P h hc hK b), yf_add h hc hK]
  group

omit hp hp1 in
theorem NF_mul_zf (γ β η e : K) : NF h hc hK p γ β η * zf hc e = NF h hc hK p γ β (η + e) := by
  unfold NF
  rw [zf_add hc]
  group

include hpinv in
theorem Hf_cocycle (α l ξ : K) :
    Hf h hc hK p α l + Hf h hc hK p (α + l) ξ - Hf h hc hK p l ξ - Hf h hc hK p α (l + ξ) =
      ξ * (σ α * l - α * σ l) := by
  have e1 : x0f r p α * x0f r p l * x0f r p ξ = NF h hc hK p (α + l + ξ)
      ((α + l) * σ ξ - σ (α + l) * ξ + (α * σ l - σ α * l))
      (Hf h hc hK p (α + l) ξ + (α * σ l - σ α * l) * ξ + Hf h hc hK p α l) := by
    rw [x0f_mul h hc hK hp hp1 hpinv, NF_mul_x0f h hc hK hp hp1 hpinv]
  have e2 : x0f r p α * (x0f r p l * x0f r p ξ) = NF h hc hK p (α + l + ξ)
      (α * σ (l + ξ) - σ α * (l + ξ) + (l * σ ξ - σ l * ξ))
      (Hf h hc hK p α (l + ξ) + Hf h hc hK p l ξ) := by
    rw [x0f_mul h hc hK hp hp1 hpinv l ξ]
    unfold NF
    rw [← mul_assoc, ← mul_assoc, x0f_mul h hc hK hp hp1 hpinv, ← NF, NF_mul_yf h hc hK,
      NF_mul_zf h hc hK, add_assoc]
  rw [mul_assoc, e2] at e1
  have := (NF_inj h hc hK hp hp1 e1).2.2
  linear_combination -this

include hpinv in
theorem Hf_homog (κ : Kˣ) (α β : K) :
    Hf h hc hK p (α * κ) (β * κ) = (κ : K) ^ 2 * σ κ * Hf h hc hK p α β := by
  have e1 : (r κ)⁻¹ * (x0f r p α * x0f r p β) * r κ = x0f r p (α * κ) * x0f r p (β * κ) := by
    rw [← conj_x0f, ← conj_x0f]; group
  rw [x0f_mul h hc hK hp hp1 hpinv, x0f_mul h hc hK hp hp1 hpinv] at e1
  unfold NF at e1
  have e2 : (r κ)⁻¹ * (x0f r p (α + β) * yf h hc hK (α * σ β - σ α * β) *
      zf hc (Hf h hc hK p α β)) * r κ = NF h hc hK p ((α + β) * κ)
        ((κ : K) * σ κ * (α * σ β - σ α * β)) ((κ : K) ^ 2 * σ κ * Hf h hc hK p α β) := by
    unfold NF
    rw [← conj_x0f, ← conj_yf h hc hK, ← conj_zf h hc]
    group
  rw [e2, ← NF] at e1
  exact ((NF_inj h hc hK hp hp1 e1).2.2).symm

include hpinv in
theorem Hf_neg (α : K) : Hf h hc hK p α (-α) = 0 := by
  have e := x0f_mul h hc hK hp hp1 hpinv α (-α)
  rw [x0f_neg hpinv, mul_inv_cancel] at e
  have e2 : (1 : N) = NF h hc hK p 0 0 0 := by
    unfold NF; rw [x0f_zero, yf_zero h hc hK, zf_zero hc]; group
  rw [e2] at e
  have := (NF_inj h hc hK hp hp1 e).2.2
  exact this.symm

include hpinv in
theorem Hf_zero_right (α : K) : Hf h hc hK p α 0 = 0 := by
  have e := x0f_mul h hc hK hp hp1 hpinv α 0
  have e2 : x0f r p α * x0f r p 0 = NF h hc hK p α 0 0 := by
    unfold NF; rw [x0f_zero, yf_zero h hc hK, zf_zero hc]; group
  rw [e2] at e
  have := (NF_inj h hc hK hp hp1 e).2.2
  exact this.symm

include hpinv in
theorem Hf_zero_left (β : K) : Hf h hc hK p 0 β = 0 := by
  have e := x0f_mul h hc hK hp hp1 hpinv 0 β
  have e2 : x0f r p 0 * x0f r p β = NF h hc hK p β 0 0 := by
    unfold NF; rw [x0f_zero, yf_zero h hc hK, zf_zero hc]; group
  rw [e2] at e
  have := (NF_inj h hc hK hp hp1 e).2.2
  exact this.symm

omit [Field K] hc [Finite N] [Fintype K] [CharP K 3] hK hp hp1 in
theorem cube_mul_commutator {u w : N} (hu : u ∈ P) (hw : w ∈ ⁅P, P⁆) : (u * w) ^ 3 = u ^ 3 := by
  have hcz := tc_mem_zc h hw hu
  have hd : tc (tc w u) u = 1 := tc_zc_left hcz hu
  have he : tc (tc w u) w = 1 := tc_zc_left hcz (commutator_le h hw)
  have := cube_formula (x := u) (y := w) rfl rfl rfl (by rw [hd, one_mul, mul_one])
    (by rw [hd, one_mul, mul_one]) (by rw [he, one_mul, mul_one]) (by rw [he, one_mul, mul_one])
    (by rw [hd, he]) (zc_pow_three h hcz) (by rw [he, one_pow])
  rw [this, hd, he, commutator_pow_three h hw]
  group

include hpinv in
theorem x0f_cube (α : K) : (x0f r p α) ^ 3 = zf hc (Hf h hc hK p α α) := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have e := x0f_mul h hc hK hp hp1 hpinv α α
  have e2 : α + α = -α := by linear_combination h3 * α
  rw [e2, show α * σ α - σ α * α = 0 by ring, NF, x0f_neg hpinv, yf_zero h hc hK,
    mul_one] at e
  rw [pow_succ, pow_two, mul_assoc, e]
  group

include hpinv in
theorem Hf_diag_add (α β : K) : Hf h hc hK p (α + β) (α + β) =
    Hf h hc hK p α α + Hf h hc hK p β β + (σ β * α - β * σ α) * (α - β) := by
  have hx := fun γ => x0f_mem h hp (r := r) γ
  set c := tc (x0f r p β) (x0f r p α) with hcdef
  have hc2 : c ∈ ⁅P, P⁆ := tc_mem_commutator (hx β) (hx α)
  have hd := tc_mem_zc h hc2 (hx α)
  have he := tc_mem_zc h hc2 (hx β)
  have key := cube_formula (x := x0f r p α) (y := x0f r p β) hcdef rfl rfl
    (zc_comm hd (hx β)) (zc_comm hd (commutator_le h hc2)) (zc_comm he (hx β))
    (zc_comm he (commutator_le h hc2)) (zc_comm hd (zc_le P he)) (commutator_pow_three h hc2)
    (zc_pow_three h he)
  rw [x0f_mul h hc hK hp hp1 hpinv, NF, mul_assoc,
    cube_mul_commutator h (hx _) ((⁅P, P⁆ : Subgroup N).mul_mem (yf_mem' h hc hK _)
      (zc_le_commutator h (zf_mem hc _))), x0f_cube h hc hK hp hp1 hpinv,
    x0f_cube h hc hK hp hp1 hpinv, x0f_cube h hc hK hp hp1 hpinv] at key
  have hl := congrArg ℓ₃ key
  have hz1 := zf_mem hc (Hf h hc hK p α α)
  have hz2 := zf_mem hc (Hf h hc hK p β β)
  rw [l3_zf hc, hc.c3.add _ ((zc P).mul_mem ((zc P).mul_mem hz1 hz2) hd) _ ((zc P).inv_mem he),
    hc.c3.add _ ((zc P).mul_mem hz1 hz2) _ hd, hc.c3.add _ hz1 _ hz2, hc.c3.inv he, l3_zf hc,
    l3_zf hc, hc.br2 _ _ hc2 (hx α), hc.br2 _ _ hc2 (hx β), hc.br1 _ _ (hx β) (hx α),
    l1_x0f hc hp hp1, l1_x0f hc hp hp1] at hl
  rw [hl]
  ring

include hpinv in
theorem Hf_diag (hq3 : 3 < Fintype.card K) (γ : K) : Hf h hc hK p γ γ = γ ^ 2 * σ γ := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hhom : ∀ γ : K, Hf h hc hK p γ γ = γ ^ 2 * σ γ * Hf h hc hK p 1 1 := by
    intro γ
    rcases eq_or_ne γ 0 with rfl | hγ
    · rw [Hf_zero_left h hc hK hp hp1 hpinv]; simp
    · have := Hf_homog h hc hK hp hp1 hpinv (Units.mk0 γ hγ) 1 1
      simpa using this
  obtain ⟨β₀, hβ₀⟩ : ∃ β : K, σ β ≠ β := by
    by_contra hcon
    push Not at hcon
    classical
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := fun x _ => by
      rcases hc.fix x (hcon x) with h' | h' | h' <;> simp [h']
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h3' : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
    omega
  have hβ1 : β₀ ≠ 1 := fun h' => hβ₀ (by rw [h', map_one])
  have key := Hf_diag_add h hc hK hp hp1 hpinv 1 β₀
  rw [hhom (1 + β₀), hhom β₀] at key
  simp only [map_one, mul_one, map_add] at key
  have hX : (σ β₀ - β₀) * (1 - β₀) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 hβ₀) (sub_ne_zero.2 (Ne.symm hβ1))
  have hc0 : Hf h hc hK p 1 1 = 1 := by
    have : (Hf h hc hK p 1 1 - 1) * ((σ β₀ - β₀) * (1 - β₀)) = 0 := by
      linear_combination key - (Hf h hc hK p 1 1) * β₀ * (1 + σ β₀) * h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hX)
  rw [hhom, hc0, mul_one]

include hpinv in
theorem Hf_formula (hq3 : 3 < Fintype.card K) (hsq : ∀ x : K, x ^ 2 ≠ -1) :
    ∃ c : K, ∀ α β, Hf h hc hK p α β = gF σ α β + c * ((α - β) * (α * σ β - σ α * β)) := by
  classical
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f : K → K := fun α => Hf h hc hK p α 1 - gF σ α 1 with hf
  have h13 : ∀ α β, Hf h hc hK p α β - gF σ α β = f (α / β) * pw σ β := by
    intro α β
    rcases eq_or_ne β 0 with rfl | hβ
    · simp [Hf_zero_right h hc hK hp hp1 hpinv, gF_zero_right, pw]
    · have e1 := Hf_homog h hc hK hp hp1 hpinv (Units.mk0 β hβ) (α / β) 1
      have e2 := gF_homog (σ := σ) β (α / β) 1
      simp only [Units.val_mk0, one_mul, div_mul_cancel₀ α hβ] at e1 e2
      rw [e1, e2, hf, pw]
      ring
  have h10 : ∀ α l ξ, (Hf h hc hK p α l - gF σ α l) + (Hf h hc hK p (α + l) ξ - gF σ (α + l) ξ)
      - (Hf h hc hK p l ξ - gF σ l ξ) - (Hf h hc hK p α (l + ξ) - gF σ α (l + ξ)) = 0 := by
    intro α l ξ
    linear_combination Hf_cocycle h hc hK hp hp1 hpinv α l ξ - gF_cocycle (σ := σ) α l ξ
  have h19 : Eq19 σ f := by
    intro x y
    have := h10 y x 1
    rw [h13, h13, h13, h13, div_one, div_one, pw_one, mul_one, mul_one, add_comm y x,
      add_comm x 1] at this
    exact this
  have h18 : Norm18 f := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hf, Hf_zero_left h hc hK hp hp1 hpinv, gF]
    · simp only [hf, Hf_diag h hc hK hp hp1 hpinv hq3, gF]; simp
    · have := Hf_neg h hc hK hp hp1 hpinv (-1)
      rw [neg_neg] at this
      simp only [hf, this, gF, map_neg, map_one]
      linear_combination h3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgen : ∀ x : K, x ≠ 0 → ∃ i : ℕ, (g : K) ^ i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers).2 (hg (Units.mk0 x hx))
    refine ⟨i, ?_⟩
    have := congrArg Units.val hi
    simpa using this
  have hbig : ∃ y : K, y ≠ 0 ∧ y ≠ 1 ∧ y ≠ -1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := fun x _ => by
      by_cases h0 : x = 0
      · simp [h0]
      by_cases h1 : x = 1
      · simp [h1]
      simp [hcon x h0 h1]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h3' : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
    omega
  have ha0 : (g : K) ≠ 0 := g.ne_zero
  have hpm : (g : K) ≠ 1 ∧ (g : K) ≠ -1 := by
    obtain ⟨y, hy0, hy1, hy2⟩ := hbig
    obtain ⟨i, hi⟩ := hgen y hy0
    constructor
    · intro h1; apply hy1; rw [← hi, h1, one_pow]
    · intro h1
      rw [h1] at hi
      rcases neg_one_pow_eq_or K i with h' | h'
      · exact hy1 (hi ▸ h')
      · exact hy2 (hi ▸ h')
  have ha1 : 1 + (g : K) ≠ 0 := fun h' => hpm.2 (by linear_combination h')
  have hkk : kk σ (g : K) ≠ 0 := by
    refine mul_ne_zero (sub_ne_zero.2 hpm.1) (sub_ne_zero.2 fun h' => ?_)
    rcases hc.fix _ h'.symm with h'' | h'' | h''
    · exact ha0 h''
    · exact hpm.1 h''
    · exact hpm.2 h''
  set c := f g / kk σ g with hcdef
  have hf1 := funEq_eq_zero hc.fix hsq ha0 ha1 hgen (f := fun x => 1 * f x - c * kk σ x)
    (eq19_lin h19 kk_eq19 1 c) (norm18_lin h18 ⟨by simp [kk], by simp [kk], by simp [kk]⟩ 1 c)
    (by simp only [one_mul, hcdef]; field_simp; ring)
  have hfc : ∀ x, f x = c * kk σ x := fun x => by
    have := congrFun hf1 x
    simp only [one_mul, Pi.zero_apply] at this
    linear_combination this
  refine ⟨c, fun α β => ?_⟩
  rcases eq_or_ne β 0 with rfl | hβ
  · simp [Hf_zero_right h hc hK hp hp1 hpinv, gF_zero_right]
  · have := h13 α β
    rw [hfc, mul_assoc, kk_div_pw hβ] at this
    linear_combination this

end Product

@[expose] noncomputable def xf (p : N) (c α : K) : N := x0f r p α * zf hc (c * (α ^ 2 * σ α))

section Final

variable [Finite N] [Fintype K] [CharP K 3] (hK : Fintype.card K = q) {p : N} (hp : p ∈ P)
  (hp1 : ℓ₁ p = 1) (hpinv : (r (-1))⁻¹ * p * r (-1) = p⁻¹) {c : K}
  (hcf : ∀ α β, Hf h hc hK p α β = gF σ α β + c * ((α - β) * (α * σ β - σ α * β)))
include h hc

omit [Finite N] [Fintype K] [CharP K 3] in
theorem xf_mem (hp : p ∈ P) (α : K) : xf hc p c α ∈ P :=
  P.mul_mem (x0f_mem h hp α) (zc_le P (zf_mem hc _))

omit [Finite N] [Fintype K] [CharP K 3] in
theorem l1_xf (hp : p ∈ P) (hp1 : ℓ₁ p = 1) (α : K) : ℓ₁ (xf hc p c α) = α := by
  have hz := zf_mem hc (c * (α ^ 2 * σ α))
  rw [xf, hc.c1.add _ (x0f_mem h hp α) _ (zc_le P hz), l1_x0f hc hp hp1,
    (hc.c1.ker _ (zc_le P hz)).2 (zc_le_commutator h hz), add_zero]

omit [Finite N] [Fintype K] [CharP K 3] in
theorem conj_xf (κ : Kˣ) (α : K) : (r κ)⁻¹ * xf hc p c α * r κ = xf hc p c (α * κ) := by
  rw [xf, xf, show (r κ)⁻¹ * (x0f r p α * zf hc (c * (α ^ 2 * σ α))) * r κ =
    ((r κ)⁻¹ * x0f r p α * r κ) * ((r κ)⁻¹ * zf hc (c * (α ^ 2 * σ α)) * r κ) by group,
    conj_x0f, conj_zf h hc]
  congr 2
  rw [map_mul]
  ring

omit h [Finite N] [Fintype K] [CharP K 3] in
theorem xf_zero : xf hc p c 0 = 1 := by
  rw [xf, x0f_zero]
  simp [zf_zero hc]

include hK hp hp1 hpinv hcf in
theorem xf_mul (α β : K) : xf hc p c α * xf hc p c β =
    xf hc p c (α + β) * yf h hc hK (α * σ β - σ α * β) * zf hc (gF σ α β) := by
  have hx := fun γ => x0f_mem h hp (r := r) γ
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have e1 : xf hc p c α * xf hc p c β = x0f r p α * x0f r p β *
      zf hc (c * (α ^ 2 * σ α) + c * (β ^ 2 * σ β)) := by
    unfold xf
    rw [zf_add hc, mul_assoc (x0f r p α), ← mul_assoc (zf hc _), zf_comm hc (hx β)]
    group
  have hyP := yf_mem_P h hc hK (α * σ β - σ α * β)
  calc xf hc p c α * xf hc p c β = x0f r p α * x0f r p β *
        zf hc (c * (α ^ 2 * σ α) + c * (β ^ 2 * σ β)) := e1
    _ = x0f r p (α + β) * yf h hc hK (α * σ β - σ α * β) *
          zf hc (Hf h hc hK p α β + (c * (α ^ 2 * σ α) + c * (β ^ 2 * σ β))) := by
        rw [x0f_mul h hc hK hp hp1 hpinv, NF, mul_assoc _ (zf hc _), ← zf_add hc]
    _ = x0f r p (α + β) * yf h hc hK (α * σ β - σ α * β) *
          zf hc (c * ((α + β) ^ 2 * σ (α + β)) + gF σ α β) := by
        rw [hcf]
        congr 2
        simp only [gF, map_add]
        linear_combination (norm := skip)
        ring_nf
        reduce_mod_char!
    _ = x0f r p (α + β) * zf hc (c * ((α + β) ^ 2 * σ (α + β))) *
          yf h hc hK (α * σ β - σ α * β) * zf hc (gF σ α β) := by
        rw [zf_add hc, mul_assoc (x0f r p (α + β)) (yf h hc hK _), ← mul_assoc (yf h hc hK _),
          ← zf_comm hc hyP]
        group
    _ = xf hc p c (α + β) * yf h hc hK (α * σ β - σ α * β) * zf hc (gF σ α β) := rfl

omit hcf in
include hK hp hp1 in
theorem yf_mul_xf (β ξ : K) :
    yf h hc hK β * xf hc p c ξ = xf hc p c ξ * yf h hc hK β * zf hc (β * ξ) := by
  rw [yf_mul h hc hK (xf_mem h hc hp ξ), l1_xf h hc hp hp1]

omit hcf in
include hK in
theorem conj_yf' (κ : Kˣ) (β : K) :
    yf h hc hK β * r κ = r κ * yf h hc hK ((κ : K) * σ κ * β) := by
  rw [← conj_yf h hc hK]; group

omit [Finite N] [Fintype K] [CharP K 3] hK hcf in
theorem conj_zf' (κ : Kˣ) (γ : K) : zf hc γ * r κ = r κ * zf hc ((κ : K) ^ 2 * σ κ * γ) := by
  rw [← conj_zf h hc]; group

omit [Finite N] [Fintype K] [CharP K 3] hK hcf in
theorem conj_xf' (κ : Kˣ) (α : K) : xf hc p c α * r κ = r κ * xf hc p c (α * κ) := by
  rw [← conj_xf h hc]; group

variable (p c) in
@[expose] noncomputable def labelMap (u : ThompsonN K σ) : N :=
  r u.κ * xf hc p c u.α * yf h hc hK u.β * zf hc u.γ

include hK hp hp1 hpinv hcf in
theorem labelMap_mul (u v : ThompsonN K σ) :
    labelMap h hc hK p c (u * v) = labelMap h hc hK p c u * labelMap h hc hK p c v := by
  have R1 : ∀ (α : K) (κ : Kˣ) (w : N), xf hc p c α * (r κ * w) = r κ * (xf hc p c (α * κ) * w) :=
    fun α κ w => by rw [← mul_assoc, conj_xf' h hc, mul_assoc]
  have R2 : ∀ (β : K) (κ : Kˣ) (w : N), yf h hc hK β * (r κ * w) =
      r κ * (yf h hc hK ((κ : K) * σ κ * β) * w) :=
    fun β κ w => by rw [← mul_assoc, conj_yf' h hc hK, mul_assoc]
  have R3 : ∀ (γ : K) (κ : Kˣ) (w : N), zf hc γ * (r κ * w) =
      r κ * (zf hc ((κ : K) ^ 2 * σ κ * γ) * w) :=
    fun γ κ w => by rw [← mul_assoc, conj_zf' h hc, mul_assoc]
  have R4 : ∀ (γ ξ : K) (w : N), zf hc γ * (xf hc p c ξ * w) = xf hc p c ξ * (zf hc γ * w) :=
    fun γ ξ w => by rw [← mul_assoc, zf_comm hc (xf_mem h hc hp ξ), mul_assoc]
  have R5 : ∀ (β ξ : K) (w : N), yf h hc hK β * (xf hc p c ξ * w) =
      xf hc p c ξ * (yf h hc hK β * (zf hc (β * ξ) * w)) :=
    fun β ξ w => by rw [← mul_assoc, yf_mul_xf h hc hK hp hp1]; group
  have R6 : ∀ (γ β : K) (w : N), zf hc γ * (yf h hc hK β * w) = yf h hc hK β * (zf hc γ * w) :=
    fun γ β w => by rw [← mul_assoc, zf_comm hc (yf_mem_P h hc hK β), mul_assoc]
  have R7 : ∀ (α ξ : K) (w : N), xf hc p c α * (xf hc p c ξ * w) = xf hc p c (α + ξ) *
      (yf h hc hK (α * σ ξ - σ α * ξ) * (zf hc (gF σ α ξ) * w)) :=
    fun α ξ w => by rw [← mul_assoc, xf_mul h hc hK hp hp1 hpinv hcf]; group
  have R8 : ∀ (β β' : K) (w : N), yf h hc hK β * (yf h hc hK β' * w) = yf h hc hK (β + β') * w :=
    fun β β' w => by rw [← mul_assoc, ← yf_add h hc hK]
  have R9 : ∀ (γ γ' : K) (w : N), zf hc γ * (zf hc γ' * w) = zf hc (γ + γ') * w :=
    fun γ γ' w => by rw [← mul_assoc, ← zf_add hc]
  have R10 : ∀ (κ κ' : Kˣ) (w : N), r κ * (r κ' * w) = r (κ * κ') * w :=
    fun κ κ' w => by rw [← mul_assoc, ← map_mul]
  suffices labelMap h hc hK p c (u * v) * 1 =
      labelMap h hc hK p c u * labelMap h hc hK p c v * 1 by simpa using this
  simp only [labelMap, mul_assoc, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10]
  rw [ThompsonN.mul_κ, ThompsonN.mul_α, ThompsonN.mul_β, ThompsonN.mul_γ]
  congr 3
  · congr 1
    simp only [map_mul]
    ring
  · congr 2
    simp only [gF, map_mul]
    ring

omit hp1 hpinv hcf in
include hK hp in
theorem labelMap_eq_one {u : ThompsonN K σ} (hPR : P ⊓ R = ⊥) (hp1 : ℓ₁ p = 1)
    (hu : labelMap h hc hK p c u = 1) : u = 1 := by
  have hx := xf_mem h hc hp (c := c) u.α
  have hy := yf_mem_P h hc hK u.β
  have hz := zc_le P (zf_mem hc u.γ)
  have hm : xf hc p c u.α * yf h hc hK u.β * zf hc u.γ ∈ P := P.mul_mem (P.mul_mem hx hy) hz
  have hr : r u.κ = (xf hc p c u.α * yf h hc hK u.β * zf hc u.γ)⁻¹ := by
    unfold labelMap at hu
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_assoc, ← mul_assoc]
    exact hu
  have hrPR : r u.κ ∈ P ⊓ R := ⟨hr ▸ P.inv_mem hm, hc.r_mem _⟩
  rw [hPR, Subgroup.mem_bot] at hrPR
  have hκ : u.κ = 1 := hc.r_inj (hrPR.trans (map_one r).symm)
  have hrest : xf hc p c u.α * yf h hc hK u.β * zf hc u.γ = 1 := by
    rw [← inv_inv (xf hc p c u.α * yf h hc hK u.β * zf hc u.γ), ← hr, hrPR, inv_one]
  have hα : u.α = 0 := by
    have := congrArg ℓ₁ hrest
    rw [hc.c1.add _ (P.mul_mem hx hy) _ hz, hc.c1.add _ hx _ hy, l1_xf h hc hp hp1,
      (hc.c1.ker _ hy).2 (yf_mem' h hc hK u.β), (hc.c1.ker _ hz).2
        (zc_le_commutator h (zf_mem hc u.γ)), hc.c1.one, add_zero, add_zero] at this
    exact this
  rw [hα, xf_zero hc, one_mul] at hrest
  have hβ : u.β = 0 := by
    have := congrArg ℓ₂ hrest
    rw [l2_yf_zf h hc hK, hc.c2.one] at this
    exact this
  rw [hβ, yf_zero h hc hK, one_mul] at hrest
  have hγ : u.γ = 0 := by
    have := congrArg ℓ₃ hrest
    rw [l3_zf hc, hc.c3.one] at this
    exact this
  ext
  · rw [hκ]; rfl
  · rw [hα]; rfl
  · rw [hβ]; rfl
  · rw [hγ]; rfl

include hK hp hp1 hpinv hcf in
theorem nonempty_mulEquiv (hPR : P ⊓ R = ⊥)
    (hN : Nat.card N = Fintype.card K ^ 3 * (Fintype.card K - 1)) :
    Nonempty (ThompsonN K σ ≃* N) := by
  let f : ThompsonN K σ →* N := MonoidHom.mk' (labelMap h hc hK p c)
    (labelMap_mul h hc hK hp hp1 hpinv hcf)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact labelMap_eq_one h hc hK hp hPR hp1 hu
  have hcard : Nat.card N ≤ Nat.card (ThompsonN K σ) := by
    rw [ThompsonN.card, hN, Nat.card_eq_fintype_card]
  exact ⟨MulEquiv.ofBijective f (hinj.bijective_of_nat_card_le hcard)⟩

end Final

end CFSG.Walter.Ree.Thompson1
