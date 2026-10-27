module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofSylow

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148OneRepair

open CFSG CFSG.RankThree.PartTwo.KFacts

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf148 {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B))
  have h3 : Nat.card (B.subgroupOf A) = Nat.card (A ⊓ B : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem exists_mul_of_mem_sup148 {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * (b * a' * b⁻¹), A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) a').mp
          ha'), b * b', B.mul_mem hb hb', by group⟩
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨b⁻¹ * a⁻¹ * b⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer _).inv_mem (hBA hb)) a⁻¹).mp (A.inv_mem ha), b⁻¹, B.inv_mem hb,
          by group⟩ }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem le_normalizer_of_commute148 {A B : Subgroup G} (h : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h b hb x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have hc := h b hb (b * x * b⁻¹) hx
    have h1 : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hc]
        _ = b * x * b⁻¹ := by group
    rw [h1]
    exact hx

theorem mul_conj_mul_inv148 (σ : MulAut G) (w : G) :
    σ * MulAut.conj w * σ⁻¹ = MulAut.conj (σ w) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_injective148 (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro w w' h
  have hc : w'⁻¹ * w ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun σ : MulAut G => σ y) h
    simp only [MulAut.conj_apply] at h1
    calc y * (w'⁻¹ * w) = w'⁻¹ * (w' * y * w'⁻¹) * w := by group
      _ = w'⁻¹ * (w * y * w⁻¹) * w := by rw [h1]
      _ = w'⁻¹ * w * y := by group
  rw [hZ, Subgroup.mem_bot] at hc
  calc w = w' * (w'⁻¹ * w) := by group
    _ = w' := by rw [hc, mul_one]

theorem zpow_eq_one_of_isInnerAut148 {α : MulAut G} (h3 : α ^ 3 = 1) (hα : ¬ IsInnerAut α)
    {j : ℤ} (hj : IsInnerAut (α ^ j)) : α ^ j = 1 := by
  have h3' : α ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact h3
  rw [zpow_eq_zpow_emod j h3'] at hj ⊢
  have hk : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hk with h | h | h <;> rw [h] at hj ⊢
  · exact zpow_zero α
  · exact absurd (by rwa [zpow_one] at hj) hα
  · exfalso
    apply hα
    have h4 : α = (α ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul]
      calc α = α ^ (3 : ℤ) * α := by rw [h3', one_mul]
        _ = α ^ ((2 : ℤ) * 2) := by rw [← zpow_add_one]; norm_num
    rw [h4]
    obtain ⟨w, hw⟩ := hj
    exact ⟨w ^ (2 : ℤ), by rw [map_zpow, hw]⟩

end General

section Action

variable {Γ : Type*} [Group Γ] {X E : Subgroup Γ}

theorem coe_normalizerMonoidHom148 {g : Γ} (hg : g ∈ Subgroup.normalizer (X : Set Γ)) (x : X) :
    ((X.normalizerMonoidHom ⟨g, hg⟩ x : X) : Γ) = g * x * g⁻¹ :=
  rfl

theorem normalizerMonoidHom_of_mem148 (w : X) :
    X.normalizerMonoidHom ⟨(w : Γ), Subgroup.le_normalizer w.2⟩ = MulAut.conj w := by
  ext y
  rfl

theorem normalizerMonoidHom_of_mem_centralizer148 {c : Γ}
    (hc : c ∈ Subgroup.centralizer (X : Set Γ)) (hcN : c ∈ Subgroup.normalizer (X : Set Γ)) :
    X.normalizerMonoidHom ⟨c, hcN⟩ = 1 := by
  ext y
  rw [coe_normalizerMonoidHom148, MulAut.one_apply,
    ← Subgroup.mem_centralizer_iff.mp hc y y.2, mul_inv_cancel_right]

theorem mem_centralizer_of_normalizerMonoidHom148 {c : Γ}
    (hcN : c ∈ Subgroup.normalizer (X : Set Γ)) (h1 : X.normalizerMonoidHom ⟨c, hcN⟩ = 1) :
    c ∈ Subgroup.centralizer (X : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h2 := congrArg (fun σ : MulAut X => ((σ ⟨y, hy⟩ : X) : Γ)) h1
  simp only [coe_normalizerMonoidHom148, MulAut.one_apply] at h2
  calc y * c = c * y * c⁻¹ * c := by rw [h2]
    _ = c * y := by group

theorem mem_of_normalizerMonoidHom_eq_conj148 (hZ : Subgroup.center X = ⊥)
    (hEN : E ≤ Subgroup.normalizer (X : Set Γ)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hcent : ∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) {g : Γ} (hg : g ∈ E)
    {w : X} (hw : X.normalizerMonoidHom ⟨g, hEN hg⟩ = MulAut.conj w) :
    (w : Γ) ∈ E ∧ g * (w : Γ)⁻¹ ∈ Subgroup.centralizer (X : Set Γ) := by
  have hwE : (w : Γ) ∈ Subgroup.centralizer (E : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : X.normalizerMonoidHom ⟨b, hEN hb⟩ * MulAut.conj w *
        (X.normalizerMonoidHom ⟨b, hEN hb⟩)⁻¹ = MulAut.conj w := by
      rw [← hw, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change b * g * b⁻¹ = g
      rw [hEc b hb g hg, mul_inv_cancel_right]
    rw [mul_conj_mul_inv148] at h1
    have h2 := congrArg Subtype.val (conj_injective148 hZ h1)
    rw [coe_normalizerMonoidHom148] at h2
    calc b * (w : Γ) = b * w * b⁻¹ * b := by group
      _ = w * b := by rw [h2]
  have hw3 : (w : Γ) ^ 3 = 1 := by
    have h1 : MulAut.conj (w ^ 3) = MulAut.conj (1 : X) := by
      rw [map_pow, ← hw, ← map_pow, map_one]
      have : (⟨g, hEN hg⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hE3 g hg)
      rw [this, map_one]
    have h2 := congrArg Subtype.val (conj_injective148 hZ h1)
    simpa using h2
  refine ⟨hcent _ hwE hw3, ?_⟩
  have hgw : g * (w : Γ)⁻¹ ∈ Subgroup.normalizer (X : Set Γ) :=
    Subgroup.mul_mem _ (hEN hg) (Subgroup.inv_mem _ (Subgroup.le_normalizer w.2))
  refine mem_centralizer_of_normalizerMonoidHom148 hgw ?_
  have h1 : (⟨g * (w : Γ)⁻¹, hgw⟩ : Subgroup.normalizer (X : Set Γ)) =
      ⟨g, hEN hg⟩ * (⟨(w : Γ), Subgroup.le_normalizer w.2⟩)⁻¹ := rfl
  rw [h1, map_mul, map_inv, hw, normalizerMonoidHom_of_mem148, mul_inv_cancel]

theorem normalizerMonoidHom_pow_three148 (hEN : E ≤ Subgroup.normalizer (X : Set Γ))
    {g : Γ} (hg : g ∈ E) (hg3 : g ^ 3 = 1) : X.normalizerMonoidHom ⟨g, hEN hg⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨g, hEN hg⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
  rw [this, map_one]

theorem exists_decomp148 (hZ : Subgroup.center X = ⊥)
    (h2 : ∀ α β : MulAut X, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α → ¬ IsInnerAut α →
      ∃ k : ℕ, IsInnerAut (β * α ^ k))
    (hEN : E ≤ Subgroup.normalizer (X : Set Γ)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hcent : ∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) {a : Γ} (haE : a ∈ E)
    (ha : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩)) {e : Γ} (he : e ∈ E) :
    ∃ (k : ℕ) (w : X), (w : Γ) ∈ E ∧
      e * a ^ k * (w : Γ)⁻¹ ∈ Subgroup.centralizer (X : Set Γ) := by
  have hcomm : X.normalizerMonoidHom ⟨a, hEN haE⟩ * X.normalizerMonoidHom ⟨e, hEN he⟩ =
      X.normalizerMonoidHom ⟨e, hEN he⟩ * X.normalizerMonoidHom ⟨a, hEN haE⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc a haE e he)
  obtain ⟨k, w, hw⟩ := h2 _ _ (normalizerMonoidHom_pow_three148 hEN haE (hE3 a haE))
    (normalizerMonoidHom_pow_three148 hEN he (hE3 e he)) hcomm ha
  have hek : e * a ^ k ∈ E := E.mul_mem he (E.pow_mem haE k)
  have h1 : X.normalizerMonoidHom ⟨e * a ^ k, hEN hek⟩ = MulAut.conj w := by
    rw [hw]
    have : (⟨e * a ^ k, hEN hek⟩ : Subgroup.normalizer (X : Set Γ)) =
        ⟨e, hEN he⟩ * ⟨a, hEN haE⟩ ^ k := rfl
    rw [this, map_mul, map_pow]
  obtain ⟨hwE, hc⟩ := mem_of_normalizerMonoidHom_eq_conj148 hZ hEN hEc hE3 hcent hek h1
  exact ⟨k, w, hwE, hc⟩

theorem zpow_eq_one_of_mul_mem148 (hEN : E ≤ Subgroup.normalizer (X : Set Γ))
    {a : Γ} (haE : a ∈ E) (ha3 : a ^ 3 = 1)
    (ha : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩)) {j : ℤ} {c : Γ}
    (hc : c ∈ Subgroup.centralizer (X : Set Γ)) (hcN : c ∈ Subgroup.normalizer (X : Set Γ))
    (hx : a ^ j * c ∈ X) : a ^ j = 1 := by
  set α := X.normalizerMonoidHom ⟨a, hEN haE⟩ with hαdef
  have hα3 : α ^ 3 = 1 := normalizerMonoidHom_pow_three148 hEN haE ha3
  have hxN : a ^ j * c ∈ Subgroup.normalizer (X : Set Γ) := Subgroup.le_normalizer hx
  have h1 : X.normalizerMonoidHom ⟨a ^ j * c, hxN⟩ = α ^ j := by
    have : (⟨a ^ j * c, hxN⟩ : Subgroup.normalizer (X : Set Γ)) =
        ⟨a, hEN haE⟩ ^ j * ⟨c, hcN⟩ := rfl
    rw [this, map_mul, map_zpow, normalizerMonoidHom_of_mem_centralizer148 hc hcN, mul_one]
  have h2 : IsInnerAut (α ^ j) := by
    rw [← h1]
    exact ⟨⟨a ^ j * c, hx⟩, (normalizerMonoidHom_of_mem148 ⟨a ^ j * c, hx⟩).symm⟩
  have hαj := zpow_eq_one_of_isInnerAut148 hα3 ha h2
  have hα1 : α ≠ 1 := fun h => ha (h ▸ ⟨1, map_one _⟩)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have h3j : (3 : ℤ) ∣ j := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hord] at hαj
    exact_mod_cast hαj
  obtain ⟨m, rfl⟩ := h3j
  rw [zpow_mul, zpow_ofNat, ha3, one_zpow]

theorem exists_inf_eq_zpowers148 [Finite Γ] (hZ : Subgroup.center X = ⊥)
    (hEN : E ≤ Subgroup.normalizer (X : Set Γ)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE27 : Nat.card E = 27) {z : Γ} (hz1 : z ≠ 1)
    (hzE : E ⊓ Subgroup.centralizer (X : Set Γ) = Subgroup.zpowers z) {a : Γ} (haE : a ∈ E)
    (ha : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩)) :
    ∃ u : X, (u : Γ) ^ 3 = 1 ∧ E ⊓ X = Subgroup.zpowers (u : Γ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzEm : Subgroup.zpowers z ≤ E ⊓ Subgroup.centralizer (X : Set Γ) := hzE.ge
  have hz : z ∈ E := (hzEm (Subgroup.mem_zpowers z)).1
  have hzC : z ∈ Subgroup.centralizer (X : Set Γ) := (hzEm (Subgroup.mem_zpowers z)).2
  have hzCX : Subgroup.zpowers z ≤ Subgroup.centralizer (X : Set Γ) :=
    Subgroup.zpowers_le.mpr hzC
  have hzNX : Subgroup.zpowers z ≤ Subgroup.normalizer (X : Set Γ) :=
    Subgroup.zpowers_le.mpr (hEN hz)
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply ha
    have : (⟨1, hEN haE⟩ : Subgroup.normalizer (X : Set Γ)) = 1 := rfl
    rw [this, map_one]
    exact ⟨1, map_one _⟩
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 a haE) ha1
  have hcard_z : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 z hz) hz1
  have hinf_az : Subgroup.zpowers a ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxz⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa
    have hxC := hzCX hxz
    rw [Subgroup.mem_bot]
    exact zpow_eq_one_of_mul_mem148 hEN haE (hE3 a haE) ha (Subgroup.inv_mem _ hxC)
      (Subgroup.inv_mem _ (hzNX hxz)) (by rw [mul_inv_cancel]; exact X.one_mem)
  have haE' : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.mpr haE
  have hzE' : Subgroup.zpowers z ≤ E := Subgroup.zpowers_le.mpr hz
  have haNz : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers z : Set Γ) :=
    le_normalizer_of_commute148 fun b hb y hy => hEc b (haE' hb) y (hzE' hy)
  have hcard_Z1 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers z : Subgroup Γ) = 9 := by
    have h := card_sup_mul_card_inf148 haNz
    rw [hinf_az, Subgroup.card_bot, mul_one, hcard_a, hcard_z] at h
    exact h
  have hZ1E : Subgroup.zpowers a ⊔ Subgroup.zpowers z ≤ E := sup_le haE' hzE'
  have hinf_W : (E ⊓ X) ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers z) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hxX⟩, hxZ1⟩
    have hzNa : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers a : Set Γ) :=
      le_normalizer_of_commute148 fun b hb y hy => hEc b (hzE' hb) y (haE' hy)
    obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_mem_sup148 hzNa hxZ1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 := zpow_eq_one_of_mul_mem148 hEN haE (hE3 a haE) ha (hzCX hc) (hzNX hc) hxX
    rw [h1, one_mul] at hxX ⊢
    rw [Subgroup.mem_bot]
    have hcen : (⟨c, hxX⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hzCX hc) y y.2
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hWN : E ⊓ X ≤ Subgroup.normalizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers z : Subgroup Γ) : Set Γ) :=
    le_normalizer_of_commute148 fun b hb y hy => hEc b hb.1 y (hZ1E hy)
  have hcard : Nat.card ((E ⊓ X) ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers z) : Subgroup Γ) =
      Nat.card (E ⊓ X : Subgroup Γ) * 9 := by
    have h := card_sup_mul_card_inf148 hWN
    rw [hinf_W, Subgroup.card_bot, mul_one, hcard_Z1] at h
    exact h
  have hle : Nat.card ((E ⊓ X) ⊔ (Subgroup.zpowers a ⊔ Subgroup.zpowers z) : Subgroup Γ) ≤
      27 := by
    rw [← hE27]
    exact Subgroup.card_le_of_le (sup_le inf_le_left hZ1E)
  have hW3 : Nat.card (E ⊓ X : Subgroup Γ) ≤ 3 := by omega
  have hWdvd : Nat.card (E ⊓ X : Subgroup Γ) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hiW⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hWdvd
  have hi01 : i = 0 ∨ i = 1 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) h
      omega
  rcases hi01 with rfl | rfl
  · refine ⟨1, by simp, ?_⟩
    rw [pow_zero, Subgroup.card_eq_one] at hiW
    rw [hiW, OneMemClass.coe_one, Subgroup.zpowers_one_eq_bot]
  · rw [pow_one] at hiW
    have hne : E ⊓ X ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hiW
      omega
    obtain ⟨⟨x, hxW⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    refine ⟨⟨x, hxW.2⟩, hE3 x hxW.1, ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxW)
    rw [hiW, Nat.card_zpowers, orderOf_eq_prime (hE3 x hxW.1) hx1']

theorem mem_of_not_isInnerAut148 [Finite Γ] (D : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥)
    (h2 : ∀ α β : MulAut X, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α → ¬ IsInnerAut α →
      ∃ k : ℕ, IsInnerAut (β * α ^ k))
    (h3 : ∀ α : MulAut X, α ^ 3 = 1 → α ∉ D → ∃ s t : X, α s = s ∧ α t = t ∧ s ≠ 1 ∧
      s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ s * t = t * s ∧ t ∉ Subgroup.zpowers s)
    (hEN : E ≤ Subgroup.normalizer (X : Set Γ)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hcent : ∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) {a : Γ} (haE : a ∈ E)
    (ha : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩)) {u : X}
    (hW : E ⊓ X = Subgroup.zpowers (u : Γ)) : X.normalizerMonoidHom ⟨a, hEN haE⟩ ∈ D := by
  set α := X.normalizerMonoidHom ⟨a, hEN haE⟩ with hαdef
  by_contra hD
  obtain ⟨s, t, hs, ht, hs1, hs3, ht3, hst, htn⟩ :=
    h3 α (normalizerMonoidHom_pow_three148 hEN haE (hE3 a haE)) hD
  let M : Subgroup X := MonoidHom.eqLocus (α : X →* X) (MonoidHom.id X)
  have hmemM : ∀ x : X, x ∈ M ↔ α x = x := fun x => Iff.rfl
  have huW : (u : Γ) ∈ E ⊓ X := hW.ge (Subgroup.mem_zpowers _)
  have huE : (u : Γ) ∈ E := huW.1
  have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hE3 _ huE)
  have huM : u ∈ M := by
    rw [hmemM]
    apply Subtype.ext
    rw [hαdef, coe_normalizerMonoidHom148, hEc a haE u huE, mul_inv_cancel_right]
  have hsM : s ∈ M := (hmemM s).mpr hs
  have htM : t ∈ M := (hmemM t).mpr ht
  obtain ⟨v, hvu, hv3, hvn⟩ := exists_commute_pow_three_not_mem148 (M := M)
    (s := ⟨s, hsM⟩) (t := ⟨t, htM⟩) (fun h => hs1 (congrArg Subtype.val h))
    (Subtype.ext (by simpa using hs3)) (Subtype.ext (by simpa using ht3))
    (Subtype.ext (by simpa using hst))
    (by
      intro h
      apply htn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩)
    ⟨u, huM⟩ (Subtype.ext (by simpa using hu3))
  set v' : Γ := ((v : X) : Γ) with hv'
  have hvX : v' ∈ X := (v : X).2
  have hvM : α (v : X) = (v : X) := (hmemM _).mp v.2
  have hva : a * v' = v' * a := by
    have h1 := congrArg Subtype.val hvM
    rw [hαdef, coe_normalizerMonoidHom148] at h1
    calc a * v' = a * v' * a⁻¹ * a := by group
      _ = v' * a := by rw [h1]
  have hvu' : (u : Γ) * v' = v' * (u : Γ) := by
    have h1 := congrArg (fun y : M => ((y : X) : Γ)) hvu
    simpa using h1
  have hvE : v' ∈ Subgroup.centralizer (E : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨k, w, hwE, hc⟩ := exists_decomp148 hZ h2 hEN hEc hE3 hcent haE ha he
    have hwu : (w : Γ) ∈ Subgroup.zpowers (u : Γ) := hW ▸ (⟨hwE, w.2⟩ : (w : Γ) ∈ E ⊓ X)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hwu
    have hvc : v' * (e * a ^ k * (w : Γ)⁻¹) = (e * a ^ k * (w : Γ)⁻¹) * v' :=
      Subgroup.mem_centralizer_iff.mp hc v' hvX
    have hvw : (w : Γ) * v' = v' * (w : Γ) := by
      rw [← hm]
      exact ((Commute.zpow_left (hvu' : Commute (u : Γ) v') m)).eq
    have hvak : a ^ k * v' = v' * a ^ k := ((Commute.pow_left (hva : Commute a v') k)).eq
    have he_eq : e = (e * a ^ k * (w : Γ)⁻¹) * (w : Γ) * (a ^ k)⁻¹ := by group
    have hc' : Commute (e * a ^ k * (w : Γ)⁻¹) v' := hvc.symm
    have hw' : Commute (w : Γ) v' := hvw
    have hak' : Commute (a ^ k)⁻¹ v' := Commute.inv_left (show Commute (a ^ k) v' from hvak)
    rw [he_eq]
    exact ((hc'.mul_left hw').mul_left hak').eq
  have hv3' : v' ^ 3 = 1 := by
    have h1 := congrArg (fun y : M => ((y : X) : Γ)) hv3
    simpa using h1
  have hvW : v' ∈ Subgroup.zpowers (u : Γ) := hW ▸ (⟨hcent _ hvE hv3', hvX⟩ : v' ∈ E ⊓ X)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hvW
  apply hvn
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simpa using hm

theorem injective_and_range148 (D : Subgroup (MulAut X)) (hZ : Subgroup.center X = ⊥)
    (hInn : ∀ w : X, MulAut.conj w ∈ D)
    (h4 : ∀ α ∈ D, ¬ IsInnerAut α → ∀ β ∈ D, ∃ k : ℕ, IsInnerAut (β * α ^ k))
    (hEN : E ≤ Subgroup.normalizer (X : Set Γ)) (hE3 : ∀ a ∈ E, a ^ 3 = 1) {a : Γ}
    (haE : a ∈ E) (ha : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩))
    (haD : X.normalizerMonoidHom ⟨a, hEN haE⟩ ∈ D)
    (hHN : X ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set Γ)) :
    Function.Injective (X.normalizerMonoidHom.comp (Subgroup.inclusion hHN)) ∧
      (X.normalizerMonoidHom.comp (Subgroup.inclusion hHN)).range = D := by
  set α := X.normalizerMonoidHom ⟨a, hEN haE⟩ with hαdef
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set Γ) :=
    Subgroup.zpowers_le.mpr (hEN haE)
  have himg : ∀ (h : ↥(X ⊔ Subgroup.zpowers a)) (x : X) (j : ℤ), (h : Γ) = x * a ^ j →
      (X.normalizerMonoidHom.comp (Subgroup.inclusion hHN)) h = MulAut.conj x * α ^ j := by
    intro h x j hxj
    rw [MonoidHom.comp_apply]
    have : Subgroup.inclusion hHN h =
        ⟨(x : Γ), Subgroup.le_normalizer x.2⟩ * ⟨a, hEN haE⟩ ^ j := Subtype.ext hxj
    rw [this, map_mul, map_zpow, normalizerMonoidHom_of_mem148]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro h h1
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup148 haN h.2
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [himg h ⟨x, hx⟩ j hxy] at h1
    have hαj : IsInnerAut (α ^ j) := ⟨(⟨x, hx⟩ : X)⁻¹, by
      rw [map_inv, inv_eq_iff_mul_eq_one, h1]⟩
    have hαj1 := zpow_eq_one_of_isInnerAut148
      (normalizerMonoidHom_pow_three148 hEN haE (hE3 a haE)) ha hαj
    rw [hαj1, mul_one] at h1
    have hx1 : (⟨x, hx⟩ : X) = 1 := conj_injective148 hZ (h1.trans (map_one _).symm)
    have hajC : a ^ j ∈ Subgroup.centralizer (X : Set Γ) := by
      refine mem_centralizer_of_normalizerMonoidHom148 (Subgroup.zpow_mem _ (hEN haE) j) ?_
      have : (⟨a ^ j, Subgroup.zpow_mem _ (hEN haE) j⟩ : Subgroup.normalizer (X : Set Γ)) =
          ⟨a, hEN haE⟩ ^ j := rfl
      rw [this, map_zpow]
      exact hαj1
    have haj : a ^ j = 1 := zpow_eq_one_of_mul_mem148 hEN haE (hE3 a haE) ha
      (Subgroup.inv_mem _ hajC) (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (hEN haE) j))
      (by rw [mul_inv_cancel]; exact X.one_mem)
    apply Subtype.ext
    rw [hxy, haj, mul_one]
    exact congrArg Subtype.val hx1
  · ext d
    constructor
    · rintro ⟨h, rfl⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup148 haN h.2
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [himg h ⟨x, hx⟩ j hxy]
      exact D.mul_mem (hInn _) (D.zpow_mem haD j)
    · intro hd
      obtain ⟨k, w, hw⟩ := h4 α haD ha d hd
      have hmem : (w : Γ) * a ^ (-(k : ℤ)) ∈ X ⊔ Subgroup.zpowers a :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left w.2)
          (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _))
      refine ⟨⟨_, hmem⟩, ?_⟩
      rw [himg ⟨_, hmem⟩ w (-(k : ℤ)) rfl, hw, zpow_neg, zpow_natCast, mul_inv_cancel_right]

theorem nonempty_mulEquiv_prod148 [Finite Γ] (D : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hInn : ∀ w : X, MulAut.conj w ∈ D)
    (h2 : ∀ α β : MulAut X, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α → ¬ IsInnerAut α →
      ∃ k : ℕ, IsInnerAut (β * α ^ k))
    (h3 : ∀ α : MulAut X, α ^ 3 = 1 → α ∉ D → ∃ s t : X, α s = s ∧ α t = t ∧ s ≠ 1 ∧
      s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ s * t = t * s ∧ t ∉ Subgroup.zpowers s)
    (h4 : ∀ α ∈ D, ¬ IsInnerAut α → ∀ β ∈ D, ∃ k : ℕ, IsInnerAut (β * α ^ k))
    (hEN : E ≤ Subgroup.normalizer (X : Set Γ)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hE27 : Nat.card E = 27)
    (hcent : ∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) {z : Γ} (hz1 : z ≠ 1)
    (hzE : E ⊓ Subgroup.centralizer (X : Set Γ) = Subgroup.zpowers z) {a : Γ} (haE : a ∈ E)
    (ha : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩)) :
    Nonempty (↥(X ⊔ E) ≃* Multiplicative (ZMod 3) × ↥D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, -, hW⟩ := exists_inf_eq_zpowers148 hZ hEN hEc hE3 hE27 hz1 hzE haE ha
  have haD := mem_of_not_isInnerAut148 D hZ h2 h3 hEN hEc hE3 hcent haE ha hW
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set Γ) :=
    Subgroup.zpowers_le.mpr (hEN haE)
  have hHN : X ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (X : Set Γ) :=
    sup_le Subgroup.le_normalizer haN
  obtain ⟨hinj, hrange⟩ := injective_and_range148 D hZ hInn h4 hEN hE3 haE ha haD hHN
  set H := X ⊔ Subgroup.zpowers a with hHdef
  set Z0 := Subgroup.zpowers z with hZ0def
  have hzEm : Z0 ≤ E ⊓ Subgroup.centralizer (X : Set Γ) := hzE.ge
  have hZ0E : Z0 ≤ E := fun x hx => (hzEm hx).1
  have hZ0C : Z0 ≤ Subgroup.centralizer (X : Set Γ) := fun x hx => (hzEm hx).2
  have hz : z ∈ E := hZ0E (Subgroup.mem_zpowers z)
  let eH : ↥H ≃* ↥D :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hdisj : Disjoint H Z0 := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxH, hxZ⟩
    rw [Subgroup.mem_bot]
    have h1 : (X.normalizerMonoidHom.comp (Subgroup.inclusion hHN)) ⟨x, hxH⟩ = 1 :=
      normalizerMonoidHom_of_mem_centralizer148 (hZ0C hxZ) _
    have h2 := hinj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  have hcomm : ∀ (h : ↥H) (w : ↥Z0), Commute (H.subtype h) (Z0.subtype w) := by
    intro h w
    have hwC : (w : Γ) ∈ Subgroup.centralizer (X : Set Γ) := hZ0C w.2
    have hwE : (w : Γ) ∈ E := hZ0E w.2
    have hle : H ≤ Subgroup.centralizer ({(w : Γ)} : Set Γ) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hwC x hx
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hEc a haE w hwE
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle h.2)
  let f := MonoidHom.noncommCoprod H.subtype Z0.subtype hcomm
  have hfinj : Function.Injective f := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, Z0.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hdisj
  have hfrange : f.range = H ⊔ Z0 := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hXE : X ⊔ E = H ⊔ Z0 := by
    apply le_antisymm
    · refine sup_le (le_sup_left.trans le_sup_left) ?_
      intro e he
      obtain ⟨k, w, hwE, hc⟩ := exists_decomp148 hZ h2 hEN hEc hE3 hcent haE ha he
      have hcE : e * a ^ k * (w : Γ)⁻¹ ∈ E :=
        E.mul_mem (E.mul_mem he (E.pow_mem haE k)) (E.inv_mem hwE)
      have hcZ : e * a ^ k * (w : Γ)⁻¹ ∈ Z0 := hzE ▸ (⟨hcE, hc⟩ : _ ∈ E ⊓ _)
      have he_eq : e = (e * a ^ k * (w : Γ)⁻¹) * (w : Γ) * (a ^ k)⁻¹ := by group
      rw [he_eq]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hcZ)
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left w.2))) ?_
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k)))
    · refine sup_le (sup_le le_sup_left ?_) (hZ0E.trans le_sup_right)
      exact (Subgroup.zpowers_le.mpr haE).trans le_sup_right
  have hcardZ : Nat.card Z0 = 3 := by
    rw [hZ0def, Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 z hz) hz1
  have hcard3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  let e3 : ↥Z0 ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hcardZ hcard3
  let e2 : ↥(H ⊔ Z0) ≃* ↥H × ↥Z0 :=
    ((MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hfrange)).symm
  exact ⟨((MulEquiv.subgroupCongr hXE).trans e2).trans
    ((MulEquiv.prodCongr eH e3).trans (MulEquiv.prodComm))⟩

end Action

section Facts

structure AutFacts148 (L : Type*) [Group L] (D : Subgroup (MulAut L)) : Prop where
  center_eq_bot : Subgroup.center L = ⊥
  conj_mem : ∀ w : L, MulAut.conj w ∈ D
  inner_mul_pow : ∀ α β : MulAut L, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α →
    ¬ IsInnerAut α → ∃ k : ℕ, IsInnerAut (β * α ^ k)
  fixed_e9 : ∀ α : MulAut L, α ^ 3 = 1 → α ∉ D → ∃ s t : L, α s = s ∧ α t = t ∧ s ≠ 1 ∧
    s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ s * t = t * s ∧ t ∉ Subgroup.zpowers s
  diag_mul_pow : ∀ α ∈ D, ¬ IsInnerAut α → ∀ β ∈ D, ∃ k : ℕ, IsInnerAut (β * α ^ k)

variable {L M : Type*} [Group L] [Group M]

theorem congr_conj148 (e : L ≃* M) (w : L) :
    MulAut.congr e (MulAut.conj w) = MulAut.conj (e w) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

theorem congr_apply_apply148 (e : L ≃* M) (α : MulAut L) (x : L) :
    MulAut.congr e α (e x) = e (α x) := by
  simp [MulAut.congr_apply]

theorem AutFacts148.congr (e : L ≃* M) {D : Subgroup (MulAut M)} (h : AutFacts148 M D) :
    AutFacts148 L (D.comap (MulAut.congr e).toMonoidHom) where
  center_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hx y']
    rw [h.center_eq_bot, Subgroup.mem_bot] at hex
    rw [Subgroup.mem_bot]
    exact e.injective (hex.trans (map_one e).symm)
  conj_mem := fun w => by
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, congr_conj148]
    exact h.conj_mem (e w)
  inner_mul_pow := fun α β hα3 hβ3 hαβ hα => by
    obtain ⟨k, hk⟩ := h.inner_mul_pow (MulAut.congr e α) (MulAut.congr e β)
      (by rw [← map_pow, hα3, map_one]) (by rw [← map_pow, hβ3, map_one])
      (by rw [← map_mul, ← map_mul, hαβ]) (fun h' => hα ((isInnerAut_congr e α).mp h'))
    refine ⟨k, (isInnerAut_congr e _).mp ?_⟩
    rwa [map_mul, map_pow]
  fixed_e9 := fun α hα3 hαD => by
    obtain ⟨s, t, hs, ht, hs1, hs3, ht3, hst, htn⟩ := h.fixed_e9 (MulAut.congr e α)
      (by rw [← map_pow, hα3, map_one]) hαD
    have hfix : ∀ y : M, MulAut.congr e α y = y → α (e.symm y) = e.symm y := by
      intro y hy
      apply e.injective
      rw [← congr_apply_apply148, MulEquiv.apply_symm_apply]
      exact hy
    refine ⟨e.symm s, e.symm t, hfix s hs, hfix t ht, ?_, ?_, ?_, ?_, ?_⟩
    · intro h1
      apply hs1
      rw [← e.apply_symm_apply s, h1, map_one]
    · rw [← map_pow, hs3, map_one]
    · rw [← map_pow, ht3, map_one]
    · rw [← map_mul, ← map_mul, hst]
    · intro h1
      apply htn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h2 := congrArg e hk
      rwa [map_zpow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
  diag_mul_pow := fun α hαD hα β hβD => by
    obtain ⟨k, hk⟩ := h.diag_mul_pow (MulAut.congr e α) hαD
      (fun h' => hα ((isInnerAut_congr e α).mp h')) (MulAut.congr e β) hβD
    refine ⟨k, (isInnerAut_congr e _).mp ?_⟩
    rwa [map_mul, map_pow]

theorem nonempty_comap_congr_mulEquiv148 (e : L ≃* M) (D : Subgroup (MulAut M)) :
    Nonempty (↥(D.comap (MulAut.congr e).toMonoidHom) ≃* ↥D) := by
  refine ⟨(MulEquiv.subgroupMap (MulAut.congr e) _).trans (MulEquiv.subgroupCongr ?_)⟩
  exact Subgroup.map_comap_eq_self_of_surjective (MulAut.congr e).surjective D

end Facts

theorem nonempty_mulEquiv_prod_of_autFacts148 {Γ : Type*} [Group Γ] [Finite Γ]
    {X E : Subgroup Γ} {L : Type*} [Group L] (e : ↥X ≃* L) {D : Subgroup (MulAut L)}
    (hD : AutFacts148 L D) (hEN : E ≤ Subgroup.normalizer (X : Set Γ))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE27 : Nat.card E = 27)
    (hcent : ∀ g ∈ Subgroup.centralizer (E : Set Γ), g ^ 3 = 1 → g ∈ E) {z : Γ} (hz1 : z ≠ 1)
    (hzE : E ⊓ Subgroup.centralizer (X : Set Γ) = Subgroup.zpowers z) {a : Γ} (haE : a ∈ E)
    (ha : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩)) :
    Nonempty (↥(X ⊔ E) ≃* Multiplicative (ZMod 3) × ↥D) := by
  have hX := hD.congr e
  obtain ⟨e1⟩ := nonempty_mulEquiv_prod148 _ hX.center_eq_bot hX.conj_mem hX.inner_mul_pow
    hX.fixed_e9 hX.diag_mul_pow hEN hEc hE3 hE27 hcent hz1 hzE haE ha
  obtain ⟨e2⟩ := nonempty_comap_congr_mulEquiv148 e D
  exact ⟨e1.trans (MulEquiv.prodCongr (MulEquiv.refl _) e2)⟩

end CFSG.RankThree.PartTwo.Sec14.Item148OneRepair
