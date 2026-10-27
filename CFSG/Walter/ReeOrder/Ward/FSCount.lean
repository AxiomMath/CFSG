module

public import CFSG.Walter.ReeOrder.Ward.Principal
public import CFSG.CharacterTheory.SmallDefect.FrobeniusSchur
public import CFSG.Walter.ReeOrder.Ward.Columns4

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

theorem inner_finset_sum_left {G : Type} {ι : Type*} [Group G] [Fintype G] (s : Finset ι)
    (c : ι → ℂ)
    (f : ι → G → ℂ) (Φ : G → ℂ) :
    BlocksInnerProduct (∑ i ∈ s, c i • f i) Φ = ∑ i ∈ s, c i * BlocksInnerProduct (f i) Φ := by
  unfold BlocksInnerProduct
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun y _ => by ring

variable {G : Type} [Group G] [Fintype G]

@[expose] noncomputable def nu (χ : G → ℂ) : ℤ :=
  if fsIndicator χ = 1 then 1 else if fsIndicator χ = -1 then -1 else 0

theorem nu_spec {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : (nu χ : ℂ) = fsIndicator χ := by
  obtain ⟨h3, -, -⟩ := fsIndicator_spec hχ
  unfold nu
  rcases h3 with h | h | h <;> rw [h] <;> norm_num

theorem nu_eq_zero_iff {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    nu χ = 0 ↔ starRingEnd ℂ ∘ χ ≠ χ := by
  rw [← (fsIndicator_spec hχ).2.1, ← nu_spec hχ]
  exact_mod_cast Iff.rfl

theorem nu_cases {χ : G → ℂ} : nu χ = 0 ∨ nu χ = 1 ∨ nu χ = -1 := by
  unfold nu
  split_ifs <;> simp

theorem nu_eq_one {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hreal : starRingEnd ℂ ∘ χ = χ)
    (hodd : Odd (deg χ)) : nu χ = 1 := by
  rcases nu_cases (χ := χ) with h | h | h
  · exact absurd hreal ((nu_eq_zero_iff hχ).mp h)
  · exact h
  · exfalso
    have hfs : fsIndicator χ = -1 := by rw [← nu_spec hχ, h]; norm_num
    obtain ⟨n, hn⟩ := (fsIndicator_spec hχ).2.2 hfs
    have : deg χ = 2 * n := by
      have h' : ((deg χ : ℤ) : ℂ) = ((2 * n : ℤ) : ℂ) := by rw [deg_eq hχ, hn]; push_cast; ring
      exact_mod_cast h'
    rw [this] at hodd
    exact Int.not_even_iff_odd.mpr hodd ⟨n, by ring⟩

namespace WardSetup

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (S : WardSetup G L q e)

theorem no_sqrt {ρ : L} (hρ : Odd (orderOf ρ)) (x : G) : x * x ≠ S.J * S.κ ρ := by
  intro h
  have hJx : x * S.J = S.J * x := by
    have hcomm : x * (S.J * S.κ ρ) = (S.J * S.κ ρ) * x := by rw [← h, mul_assoc]
    have hpow := S.pow_J_mul hρ
    rw [← hpow]
    exact ((Commute.pow_right hcomm (orderOf ρ))).eq
  obtain ⟨w, rfl | rfl⟩ := S.centralizer x hJx
  · rw [← map_mul] at h
    exact S.J_mul_ne ρ (w * w) h.symm
  · have : S.J * S.κ w * (S.J * S.κ w) = S.κ (w * w) := by
      rw [map_mul]
      calc S.J * S.κ w * (S.J * S.κ w) = S.J * S.J * (S.κ w * S.κ w) := by
            rw [mul_assoc, ← mul_assoc (S.κ w), ← S.κ_comm', mul_assoc, mul_assoc]
        _ = S.κ w * S.κ w := by rw [S.J_mul, one_mul]
    rw [this] at h
    exact S.J_mul_ne ρ (w * w) h.symm

theorem fs_sum_σ {ρ : L} (hρ : Odd (orderOf ρ)) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, (nu χ : ℂ) * S.σ χ ρ = 0 := by
  have h := card_sq_eq_sum_fsIndicator (S.J * S.κ ρ)
  have h0 : (Finset.univ.filter fun x : G => x * x = S.J * S.κ ρ) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact S.no_sqrt hρ x
  rw [h0, Finset.card_empty, Nat.cast_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Set.Finite.mem_toFinset] at hχ
  rw [nu_spec hχ]
  rfl

theorem fs_col {Φ : L → ℂ} (hΦ : ∀ y : L, Even (orderOf y) → Φ y = 0) (d : (G → ℂ) → ℤ)
    (hd : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) Φ = d χ) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, nu χ * d χ = 0 := by
  have hF : ∀ y : L, Odd (orderOf y) →
      (∑ χ ∈ (irreducibles_finite G).toFinset, (nu χ : ℂ) • S.σ χ) y = (0 : L → ℂ) y := by
    intro y hy
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact S.fs_sum_σ hy
  have h := inner_eq_of_odd hF hΦ
  rw [inner_finset_sum_left, blocksInnerProduct_zero_left] at h
  have h' : ((∑ χ ∈ (irreducibles_finite G).toFinset, nu χ * d χ : ℤ) : ℂ) = 0 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Set.Finite.mem_toFinset] at hχ
    rw [hd χ hχ]
  exact_mod_cast h'

@[expose] noncomputable def Kfin : Finset G := Finset.univ.filter fun g : G => IsConj g S.J

theorem Kfin_invariant : ∀ x ∈ S.Kfin, ∀ g : G, g * x * g⁻¹ ∈ S.Kfin := by
  intro x hx g
  simp only [Kfin, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact (isConj_iff.mpr ⟨g, rfl⟩).symm.trans hx

theorem mem_Kfin_iff (x : G) : x ∈ S.Kfin ↔ orderOf x = 2 := by
  simp only [Kfin, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have ho : orderOf (c * x * c⁻¹) = orderOf x := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hc, S.orderOf_J] at ho
    exact ho.symm
  · exact S.involution_conj x

theorem sq_of_order_two {M : Type*} [Monoid M] {x : M} (h : orderOf x = 2) : x * x = 1 := by
  rw [← sq, ← h]
  exact pow_orderOf_eq_one x

theorem order_two_of_sq {M : Type*} [Monoid M] {x : M} (h : x * x = 1) (h1 : x ≠ 1) :
    orderOf x = 2 :=
  orderOf_eq_prime (by rw [sq, h]) h1

@[expose] noncomputable def pairsL (r : L) : Finset (L × L) :=
  ((Finset.univ.filter fun x : L => orderOf x = 2) ×ˢ
    (Finset.univ.filter fun x : L => orderOf x = 2)).filter fun p => p.1 * p.2 = r

theorem Jκ_sq (w : L) : S.J * S.κ w * (S.J * S.κ w) = S.κ (w * w) := by
  rw [map_mul]
  calc S.J * S.κ w * (S.J * S.κ w) = S.J * S.J * (S.κ w * S.κ w) := by
        rw [mul_assoc, ← mul_assoc (S.κ w), ← S.κ_comm', mul_assoc, mul_assoc]
    _ = S.κ w * S.κ w := by rw [S.J_mul, one_mul]

theorem Jκ_mul_Jκ (w w' : L) : S.J * S.κ w * (S.J * S.κ w') = S.κ (w * w') := by
  rw [map_mul]
  calc S.J * S.κ w * (S.J * S.κ w') = S.J * S.J * (S.κ w * S.κ w') := by
        rw [mul_assoc, ← mul_assoc (S.κ w), ← S.κ_comm', mul_assoc, mul_assoc]
    _ = S.κ w * S.κ w' := by rw [S.J_mul, one_mul]

theorem order_two_Jκ {w : L} (h : w * w = 1) : orderOf (S.J * S.κ w) = 2 := by
  apply order_two_of_sq
  · rw [S.Jκ_sq, h, map_one]
  · intro h1
    exact S.J_mul_ne w 1 (by rw [h1, map_one])

theorem count_pairs {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    (((S.Kfin ×ˢ S.Kfin).filter fun p => p.1 * p.2 = S.κ r).card : ℂ) = q + e := by
  have hodd : Odd (orderOf r) := S.orderOf_Ro_odd hr
  have hrr : r * r ≠ 1 := by
    intro h
    have h2 : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h])
    have h1 : orderOf r = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
      · exact h'
      · rw [h'] at hodd; exact absurd hodd (by decide)
    exact hr1 (orderOf_eq_one_iff.mp h1)
  set f₁ : L × L → G × G := fun p => (S.κ p.1, S.κ p.2) with hf₁
  set f₂ : L × L → G × G := fun p => (S.J * S.κ p.1, S.J * S.κ p.2) with hf₂
  have hunion : (S.Kfin ×ˢ S.Kfin).filter (fun p => p.1 * p.2 = S.κ r) =
      (pairsL r).image f₁ ∪ (pairsL r).image f₂ := by
    ext ⟨x₁, x₂⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_image, pairsL,
      Finset.mem_univ, true_and, Prod.exists, Prod.mk.injEq, hf₁, hf₂, S.mem_Kfin_iff]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, hprod⟩
      have hs₁ := sq_of_order_two h₁
      have hs₂ := sq_of_order_two h₂
      have hinv : x₁⁻¹ * S.κ r * x₁ ∈ Subgroup.zpowers (S.κ r) := by
        have hx₁ : x₁⁻¹ = x₁ := inv_eq_of_mul_eq_one_right hs₁
        have : x₁⁻¹ * S.κ r * x₁ = (S.κ r)⁻¹ := by
          rw [← hprod, hx₁, mul_inv_rev, inv_eq_of_mul_eq_one_right hs₂, hx₁]
          calc x₁ * (x₁ * x₂) * x₁ = (x₁ * x₁) * x₂ * x₁ := by group
            _ = x₂ * x₁ := by rw [hs₁, one_mul]
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      have hJ := S.normalizer rfl r hr hr1 x₁ hinv
      have hx₂ : x₂ = x₁ * S.κ r := by
        rw [← hprod, ← mul_assoc, hs₁, one_mul]
      obtain ⟨w, rfl | rfl⟩ := S.centralizer x₁ hJ
      · left
        refine ⟨w, w⁻¹ * r, ⟨⟨by rwa [S.orderOf_κ] at h₁, ?_⟩, by group⟩, rfl, ?_⟩
        · have : x₂ = S.κ (w⁻¹ * r) := by
            rw [hx₂, map_mul, map_inv, inv_eq_of_mul_eq_one_right (by rw [← map_mul,
              sq_of_order_two (by rwa [S.orderOf_κ] at h₁), map_one])]
          rw [this, S.orderOf_κ] at h₂
          exact h₂
        · rw [hx₂, map_mul, map_inv, inv_eq_of_mul_eq_one_right (by rw [← map_mul,
            sq_of_order_two (by rwa [S.orderOf_κ] at h₁), map_one])]
      · right
        have hw : w * w = 1 := by
          have := hs₁
          rw [S.Jκ_sq] at this
          apply S.κ_inj
          rw [this, map_one]
        have hw1 : w ≠ 1 := by
          rintro rfl
          apply hrr
          have hx₂' : x₂ = S.J * S.κ r := by rw [hx₂, map_one, mul_one]
          have := hs₂
          rw [hx₂', S.Jκ_sq] at this
          apply S.κ_inj
          rw [this, map_one]
        have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
        have hx₂' : x₂ = S.J * S.κ (w * r) := by
          rw [hx₂, map_mul]
          group
        refine ⟨w, w * r, ⟨⟨order_two_of_sq hw hw1, ?_⟩, ?_⟩, rfl, hx₂'.symm⟩
        · have hw2 : (w * r) * (w * r) = 1 := by
            have := hs₂
            rw [hx₂', S.Jκ_sq] at this
            apply S.κ_inj
            rw [this, map_one]
          apply order_two_of_sq hw2
          intro h
          apply hrr
          have : r = w := by
            calc r = w⁻¹ * (w * r) := by group
              _ = w := by rw [h, mul_one, hwinv]
          rw [this, hw]
        · rw [← mul_assoc, hw, one_mul]
    · rintro (⟨w₁, w₂, ⟨⟨h₁, h₂⟩, hprod⟩, rfl, rfl⟩ | ⟨w₁, w₂, ⟨⟨h₁, h₂⟩, hprod⟩, rfl, rfl⟩)
      · refine ⟨⟨by rwa [S.orderOf_κ], by rwa [S.orderOf_κ]⟩, by rw [← map_mul, hprod]⟩
      · refine ⟨⟨S.order_two_Jκ (sq_of_order_two h₁), S.order_two_Jκ (sq_of_order_two h₂)⟩, ?_⟩
        rw [S.Jκ_mul_Jκ, hprod]
  have hdisj : Disjoint ((pairsL r).image f₁) ((pairsL r).image f₂) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h2
    simp only [hf₁, hf₂, Prod.mk.injEq] at hb
    exact S.J_mul_ne b.1 a.1 hb.1
  have hinj₁ : Set.InjOn f₁ ↑(pairsL r) := by
    intro a _ b _ h
    simp only [hf₁, Prod.mk.injEq] at h
    exact Prod.ext (S.κ_inj h.1) (S.κ_inj h.2)
  have hinj₂ : Set.InjOn f₂ ↑(pairsL r) := by
    intro a _ b _ h
    simp only [hf₂, Prod.mk.injEq, mul_right_inj] at h
    exact Prod.ext (S.κ_inj h.1) (S.κ_inj h.2)
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj₁,
    Finset.card_image_of_injOn hinj₂]
  have h : ((pairsL r).card : ℂ) = ((q : ℂ) + e) / 2 := S.W.card_inv_pairs hr hr1
  push_cast
  rw [h]
  ring

theorem formula8 {r : L} (hr : r ∈ S.W.Ro) (hr1 : r ≠ 1) :
    (q : ℂ) + e = (Nat.card (ConjClasses.mk S.J).carrier : ℂ) ^ 2 / Nat.card G *
      ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * starRingEnd ℂ (χ (S.κ r)) / χ 1 := by
  rw [← S.count_pairs hr hr1, card_mul_eq _ _ S.Kfin_invariant S.Kfin_invariant]
  have hsum : ∀ χ ∈ (irreducibles_finite G).toFinset,
      (∑ x ∈ S.Kfin, χ x) * (∑ x ∈ S.Kfin, χ x) * starRingEnd ℂ (χ (S.κ r)) / χ 1 =
        (Nat.card (ConjClasses.mk S.J).carrier : ℂ) ^ 2 *
          (χ S.J ^ 2 * starRingEnd ℂ (χ (S.κ r)) / χ 1) := by
    intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    have hK : ∑ x ∈ S.Kfin, χ x = (Nat.card (ConjClasses.mk S.J).carrier : ℂ) * χ S.J := by
      have h := sum_isConj_mul (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)) S.J
      rw [← h, Kfin, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [hK]
    ring
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum]
  ring

end WardSetup

end CFSG.Walter.Ward
