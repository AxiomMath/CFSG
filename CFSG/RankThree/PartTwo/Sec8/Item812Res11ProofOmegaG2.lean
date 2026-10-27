module

public import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item812Res11

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem conj_injective_of_center_eq_bot' {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  intro g h hgh
  have hc : h⁻¹ * g ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun φ : MulAut M => φ x) hgh
    simp only [MulAut.conj_apply] at h1
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = h⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem card_range_le_nine {A M : Type*} [Group A] [Finite A] [Group M] (hA81 : Nat.card A = 81)
    (ρ : A →* M) {e w : A} (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (hekr : ρ e = 1) (hwkr : ρ w = 1)
    (hwe : w ∉ Subgroup.zpowers e) : Nat.card ρ.range ≤ 9 := by
  have heord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hkercard : 9 ≤ Nat.card ρ.ker := by
    have hdvd : Nat.card ρ.ker ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = Nat.card A by rw [hA81]; norm_num]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hgt : 3 < Nat.card ρ.ker := by
      by_contra hle
      push Not at hle
      have heq : Subgroup.zpowers e = ρ.ker :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := ρ.ker)).mpr hekr)
          (by rw [Nat.card_zpowers, heord]; exact hle)
      exact hwe (heq ▸ hwkr)
    rw [hieq] at hgt ⊢
    interval_cases i <;> simp_all
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker, hA81] at h1
  have h2 : 9 * Nat.card ρ.range ≤ 81 := h1 ▸ Nat.mul_le_mul_right _ hkercard
  omega

theorem card_inf_inn_le_three {M : Type*} [Group M] [Finite M] (R : Subgroup (MulAut M))
    (hRc : ∀ β ∈ R, ∀ γ ∈ R, β * γ = γ * β) (hR3 : ∀ β ∈ R, β ^ 3 = 1)
    (hR9 : Nat.card R ≤ 9) {α : MulAut M} (hαR : α ∈ R) (hα : ¬ IsInnerAut α) :
    Nat.card (R ⊓ (MulAut.conj : M →* MulAut M).range : Subgroup (MulAut M)) ≤ 3 := by
  classical
  have : Finite (MulAut M) := Finite.of_injective (fun f : MulAut M => (f : M → M))
    (fun f g h => MulEquiv.ext (congrFun h))
  set Inn := (MulAut.conj : M →* MulAut M).range with hInn
  set S : Subgroup (MulAut M) := R ⊓ Inn with hS
  have hα3 : α ^ 3 = 1 := hR3 α hαR
  have hα1 : α ≠ 1 := fun h1 => hα (h1 ▸ ⟨1, map_one _⟩)
  have hαo : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  set T := Subgroup.zpowers α with hT
  have hTR : T ≤ R := (Subgroup.zpowers_le).mpr hαR
  have hST : S ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro σ ⟨hσS, hσT⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, α ^ k = σ :=
      (Submonoid.mem_powers_iff _ _).mp
        ((isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hα3⟩).mem_powers_iff_mem_zpowers.mpr
          hσT)
    rw [← pow_mod_orderOf, hαo] at hσS ⊢
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · rw [h0, pow_zero]
    · rw [h1, pow_one] at hσS
      exact absurd hσS.2 hα
    · rw [h2] at hσS
      exfalso
      apply hα
      have h2' : α ^ 2 ∈ Inn := hσS.2
      have : α = (α ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hα3, one_mul]
      rw [this]
      exact Inn.pow_mem h2' 2
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S T fun σ hσ τ hτ =>
    hRc σ hσ.1 τ (hTR hτ)).1
  rw [hST, Subgroup.card_bot, mul_one, Nat.card_zpowers, hαo] at hcard
  have hle : Nat.card (S ⊔ T : Subgroup (MulAut M)) ≤ Nat.card R :=
    Subgroup.card_le_of_le (sup_le inf_le_left hTR)
  omega

theorem fixed_of_fixed_inner {M : Type*} [Group M] (R : Subgroup (MulAut M)) {α : MulAut M}
    (hαR : α ∈ R) (htri : ∀ γ ∈ R, IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α))
    {j : M} (hjα : α j = j)
    (hjS : ∀ σ ∈ R, IsInnerAut σ → σ j = j) : ∀ γ ∈ R, γ j = j := by
  have hαinv : α⁻¹ j = j := by
    conv_lhs => rw [← hjα]
    exact MulAut.inv_apply_self M α j
  intro γ hγ
  rcases htri γ hγ with h | h | h
  · exact hjS γ hγ h
  · have e : γ = (γ * α⁻¹) * α := by group
    rw [e, MulAut.mul_apply, hjα, hjS _ (R.mul_mem hγ (R.inv_mem hαR)) h]
  · have e : γ = (γ * α) * α⁻¹ := by group
    rw [e, MulAut.mul_apply, hαinv, hjS _ (R.mul_mem hγ hαR) h]

theorem fixed_of_trichotomy_conj {M : Type*} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥)
    (R : Subgroup (MulAut M)) (hRc : ∀ β ∈ R, ∀ γ ∈ R, β * γ = γ * β)
    (hR3 : ∀ β ∈ R, β ^ 3 = 1) (hR9 : Nat.card R ≤ 9) {α : MulAut M} (hαR : α ∈ R)
    (hα : ¬ IsInnerAut α)
    (htri : ∀ γ ∈ R, IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α))
    {w₀ : M} (hw₀R : MulAut.conj w₀ ∈ R) (hw₀1 : w₀ ≠ 1) {v : M} (hαv : α v = v)
    (hvw : v * w₀ = w₀ * v) : ∀ γ ∈ R, γ v = v := by
  classical
  have : Finite (MulAut M) := Finite.of_injective (fun f : MulAut M => (f : M → M))
    (fun f g h => MulEquiv.ext (congrFun h))
  set S : Subgroup (MulAut M) := R ⊓ (MulAut.conj : M →* MulAut M).range with hS
  have hS3 : Nat.card S ≤ 3 := card_inf_inn_le_three R hRc hR3 hR9 hαR hα
  have hc1 : MulAut.conj w₀ ≠ 1 := fun h1 =>
    hw₀1 (conj_injective_of_center_eq_bot' hZ (h1.trans (map_one _).symm))
  have hco : orderOf (MulAut.conj w₀) = 3 := orderOf_eq_prime (hR3 _ hw₀R) hc1
  have hSeq : S = Subgroup.zpowers (MulAut.conj w₀) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr ⟨hw₀R, ⟨w₀, rfl⟩⟩) ?_
    rw [Nat.card_zpowers, hco]
    exact hS3
  refine fixed_of_fixed_inner R hαR htri hαv fun σ hσR hσ => ?_
  have hσS : σ ∈ S := ⟨hσR, hσ⟩
  rw [hSeq] at hσS
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσS
  rw [← map_zpow, MulAut.conj_apply]
  have hc : Commute v (w₀ ^ k) := Commute.zpow_right hvw k
  rw [← hc.eq, mul_inv_cancel_right]

theorem exists_fixed_involution_of_trichotomy {M : Type*} [Group M] [Finite M]
    (hZ : Subgroup.center M = ⊥) (R : Subgroup (MulAut M))
    (hRc : ∀ β ∈ R, ∀ γ ∈ R, β * γ = γ * β) (hR3 : ∀ β ∈ R, β ^ 3 = 1)
    (hR9 : Nat.card R ≤ 9) {α : MulAut M} (hαR : α ∈ R) (hα : ¬ IsInnerAut α)
    (htri : ∀ γ ∈ R, IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α))
    (F : Subgroup M) (hF : ∀ z, z ∈ F ↔ α z = z) (hF2 : ∃ j ∈ F, orderOf j = 2)
    (hF3 : ∀ d ∈ F, orderOf d = 3 → ∃ s ∈ F, orderOf s = 2 ∧ s * d = d * s) :
    ∃ j : M, orderOf j = 2 ∧ ∀ γ ∈ R, γ j = j := by
  classical
  by_cases hS1 : ∀ σ ∈ R, IsInnerAut σ → σ = 1
  · obtain ⟨j, hjF, hj2⟩ := hF2
    refine ⟨j, hj2, fixed_of_fixed_inner R hαR htri ((hF j).mp hjF) fun σ hσR hσ => ?_⟩
    rw [hS1 σ hσR hσ, MulAut.one_apply]
  push Not at hS1
  obtain ⟨γ₀, hγ₀R, ⟨d₀, hd₀⟩, hγ₀1⟩ := hS1
  have hd₀1 : d₀ ≠ 1 := fun h1 => hγ₀1 (by rw [← hd₀, h1, map_one])
  have hd₀3 : d₀ ^ 3 = 1 := by
    apply conj_injective_of_center_eq_bot' hZ
    rw [map_pow, hd₀, hR3 γ₀ hγ₀R, map_one]
  have hd₀o : orderOf d₀ = 3 := orderOf_eq_prime hd₀3 hd₀1
  have hαd₀ : α d₀ = d₀ := by
    apply conj_injective_of_center_eq_bot' hZ
    rw [← mul_mulAutConj_mul_inv, hd₀, hRc α hαR γ₀ hγ₀R, mul_inv_cancel_right]
  obtain ⟨s, hsF, hs2, hsd⟩ := hF3 d₀ ((hF d₀).mpr hαd₀) hd₀o
  exact ⟨s, hs2, fixed_of_trichotomy_conj hZ R hRc hR3 hR9 hαR hα htri (hd₀ ▸ hγ₀R) hd₀1
    ((hF s).mp hsF) hsd⟩


theorem g2_trichotomy {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) {α γ : MulAut (adjointGroup Tag.G2 K)} (hα3 : α ^ 3 = 1)
    (hα : ¬ IsInnerAut α) (hγ3 : γ ^ 3 = 1) :
    IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α) := by
  classical
  by_cases hγ : IsInnerAut γ
  · exact Or.inl hγ
  right
  obtain ⟨σ, hσo, k, rfl⟩ := g2_order_three_field_descent hK3 hK4 hγ3 hγ
  obtain ⟨σ₀, hσ₀o, k₀, rfl⟩ := g2_order_three_field_descent hK3 hK4 hα3 hα
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  have hKn : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨-, hσf⟩ := eq_frobenius_pow_of_orderOf_eq_three hp n.pos hKn hσo
  obtain ⟨⟨r, hr⟩, hσ₀f⟩ := eq_frobenius_pow_of_orderOf_eq_three hp n.pos hKn hσ₀o
  set φ := g2FieldHom K σ with hφ
  have key : IsInnerAut (MulAut.conj k * (φ * MulAut.conj (k⁻¹ * k₀) * φ⁻¹) *
      (MulAut.conj k₀)⁻¹) := by
    rw [mul_mulAutConj_mul_inv]
    exact ⟨k * φ (k⁻¹ * k₀) * k₀⁻¹, by simp only [map_mul, map_inv]⟩
  have hpn : ∀ c : K, c ^ p ^ (n : ℕ) = c := fun c => by
    rw [← hKn, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hn3 : (n : ℕ) / 3 = r := by omega
  have hn23 : 2 * (n : ℕ) / 3 = 2 * r := by omega
  rw [hn3, hn23] at hσf hσ₀f
  have hcases : σ₀ = σ ∨ σ * σ₀ = 1 := by
    rcases hσf with h1 | h1 <;> rcases hσ₀f with h2 | h2
    · left
      ext c
      rw [h1, h2]
    · right
      ext c
      rw [RingAut.mul_apply, h2, h1, RingAut.one_apply, ← pow_mul, ← pow_add,
        show 2 * r + r = (n : ℕ) by omega, hpn]
    · right
      ext c
      rw [RingAut.mul_apply, h2, h1, RingAut.one_apply, ← pow_mul, ← pow_add,
        show r + 2 * r = (n : ℕ) by omega, hpn]
    · left
      ext c
      rw [h1, h2]
  rcases hcases with heq | hinv
  · left
    subst heq
    convert key using 1
    simp only [hφ, map_mul, map_inv]
    group
  · right
    have hσ₀ : g2FieldHom K σ₀ = φ⁻¹ := by
      rw [hφ, ← map_inv, eq_inv_of_mul_eq_one_right hinv]
    rw [hσ₀]
    convert key using 1
    simp only [map_mul, map_inv]
    group

end CFSG.RankThree.PartTwo.Sec8.Item812Res11
