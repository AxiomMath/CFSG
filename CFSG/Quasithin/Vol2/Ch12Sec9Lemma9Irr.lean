module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Para

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem eq_or_eq_of_lOne_le_normalizer [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {W : Subgroup G}
    (hV₁W : V₁ ≤ W) (hWV : W ≤ V) (hXW : lOne L V₁ ≤ Subgroup.normalizer (W : Set G)) :
    W = V₁ ∨ W = V := by
  obtain ⟨hcard, hsq, -⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  by_contra hne
  push Not at hne
  obtain ⟨hW1, hWV'⟩ := hne
  obtain ⟨a, haW, haV₁⟩ : ∃ a ∈ W, a ∉ V₁ := by
    by_contra hall
    push Not at hall
    exact hW1 (le_antisymm hall hV₁W)
  obtain ⟨b, hbV, hbW⟩ : ∃ b ∈ V, b ∉ W := by
    by_contra hall
    push Not at hall
    exact hWV' (le_antisymm hWV hall)
  let _ := zmodModuleOf hsq
  have haV := hWV haW
  set a' : Additive ↥V := Additive.ofMul ⟨a, haV⟩ with ha'def
  set b' : Additive ↥V := Additive.ofMul ⟨b, hbV⟩ with hb'def
  have ha'W : a' ∈ subOf (V := V) W := mem_subOf.2 haW
  have hb'W : b' ∉ subOf (V := V) W := fun h => hbW (mem_subOf.1 h)
  have ha' : a' ∉ subOf (V := V) V₁ ⊔ (ZMod 2) ∙ b' := by
    intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul, add_zero] at hyz
      exact haV₁ (mem_subOf.1 (hyz ▸ hy))
    · rw [one_smul] at hyz
      apply hb'W
      have hb : b' = a' - y := by rw [← hyz]; abel
      rw [hb]
      exact (subOf (V := V) W).sub_mem ha'W (subOf_mono hV₁W hy)
  have hb' : b' ∉ subOf (V := V) V₁ ⊔ (ZMod 2) ∙ a' := fun hmem => hb'W
    (sup_le (subOf_mono hV₁W) ((Submodule.span_singleton_le_iff_mem _ _).2 ha'W) hmem)
  obtain ⟨ρ, hρ3, hρa, hρb, hρP⟩ := exists_rotation ha' hb'
  have hαL : mulAutOfLin ρ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ =
      ((Additive.toMul (ρ (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
    intro x hx
    rw [← mulAutOfLin_apply, ← hlα]
    rfl
  have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxV := hV₁.1 hx
      rw [hconj x hxV, hρP _ ((mem_subOf (x := Additive.ofMul ⟨x, hxV⟩)).2 hx)]
      exact hx
    · intro hx
      have hxV : x ∈ V := (Subgroup.mem_normalizer_iff.1 hlN x).2 (hV₁.1 hx)
      rw [hconj x hxV] at hx
      have hy : ρ (Additive.ofMul ⟨x, hxV⟩) ∈ subOf (V := V) V₁ := mem_subOf.2 hx
      have e : Additive.ofMul (⟨x, hxV⟩ : ↥V) = ρ (Additive.ofMul ⟨x, hxV⟩) := by
        have h2 := hρ3 (Additive.ofMul ⟨x, hxV⟩)
        rw [hρP _ hy, hρP _ hy] at h2
        exact h2.symm
      rw [← e] at hy
      exact mem_subOf.1 hy
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G))
    (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hlL, hlV₁⟩)
  have hkX : l ^ 2 ^ k ∈ Subgroup.normalizer (W : Set G) := hXW hk
  have hpow : ∀ (m : ℕ) (x : G) (hx : x ∈ V), l ^ m * x * (l ^ m)⁻¹ =
      ((Additive.toMul ((ρ ^ m) (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp
    | succ m ih =>
      intro x hx
      rw [show l ^ (m + 1) * x * (l ^ (m + 1))⁻¹ = l * (l ^ m * x * (l ^ m)⁻¹) * l⁻¹ by group,
        ih x hx, hconj _ (Additive.toMul ((ρ ^ m) (Additive.ofMul ⟨x, hx⟩))).2, pow_succ',
        LinearEquiv.mul_apply]
      rfl
  have hW' : (ρ ^ 2 ^ k) a' ∈ subOf (V := V) W := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hkX a).1 haW
    rw [hpow (2 ^ k) a haV] at h1
    exact mem_subOf.2 h1
  have hρ3' : ρ ^ 3 = 1 := LinearEquiv.ext fun x => by
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hρ3 x
  have hred : ρ ^ 2 ^ k = ρ ^ (2 ^ k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ k) 3, pow_add, pow_mul, hρ3', one_pow, one_mul]
  rcases two_pow_mod_three k with h1 | h2
  · rw [hred, h1, pow_one, hρa] at hW'
    exact hb'W hW'
  · rw [hred, h2, pow_two, LinearEquiv.mul_apply, hρa, hρb] at hW'
    apply hb'W
    have e : b' = -(-a' - b') - a' := by abel
    rw [e]
    exact (subOf (V := V) W).sub_mem ((subOf (V := V) W).neg_mem hW') ha'W

namespace L1299

theorem le_centralizer_of_commutator_le_lOne [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (V₁ : Set G))
    (hVY : ∀ v ∈ V, ∀ y ∈ Y, y * v * y⁻¹ * v⁻¹ ∈ V₁)
    (hLY : ∀ l ∈ lOne L V₁, ∀ y ∈ Y, l * y * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    Y ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hlOne : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  intro y hy
  set W := V ⊓ Subgroup.centralizer ({y} : Set G) with hWdef
  have hV₁W : V₁ ≤ W := by
    refine le_inf hV₁.1 fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact Subgroup.mem_centralizer_iff.1
      (le_centralizer_normalizer_of_card_eq_two hV₁2 hx) y (hYN hy)
  have hWN : lOne L V₁ ≤ Subgroup.normalizer (W : Set G) := by
    refine LinearS3.le_normalizer_of_conj_mem fun l hl w hw => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hLV (hlOne hl).1) w).1 hw.1
    · show l * w * l⁻¹ ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hc := hLY l⁻¹ (inv_mem hl) y hy
      have hwy : y * w = w * y := Subgroup.mem_centralizer_iff.1 hw.2 y rfl
      have hcw := Subgroup.mem_centralizer_iff.1 hc w hw.1
      set c := l⁻¹ * y * l⁻¹⁻¹ * y⁻¹ with hcdef
      have e1 : l⁻¹ * y * l = c * y := by rw [hcdef]; group
      calc y * (l * w * l⁻¹) = l * ((l⁻¹ * y * l) * w) * l⁻¹ := by group
        _ = l * (c * (y * w)) * l⁻¹ := by rw [e1]; group
        _ = l * (c * (w * y)) * l⁻¹ := by rw [hwy]
        _ = l * ((c * w) * y) * l⁻¹ := by group
        _ = l * ((w * c) * y) * l⁻¹ := by rw [hcw]
        _ = l * w * l⁻¹ * (l * (c * y) * l⁻¹) := by group
        _ = l * w * l⁻¹ * y := by rw [← e1]; group
  rcases eq_or_eq_of_lOne_le_normalizer h hV₁ hV₁W inf_le_left hWN with hW | hW
  · exfalso
    obtain ⟨R, hRV, -, hcardV⟩ := exists_commutator_image (A := V) (W := V₁) (v := y)
      (fun a ha b hb => hab a (hV₁.1 ha) b (hV₁.1 hb))
      (fun a ha w hw => hab a ha w (hV₁.1 hw))
      (fun a ha => by
        have h1 := V₁.inv_mem (hVY a ha y hy)
        rwa [show (y * a * y⁻¹ * a⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ by group] at h1)
    rw [← hWdef, hW, hcard, hV₁2] at hcardV
    have h1 := Subgroup.card_le_of_le hRV
    rw [hV₁2] at h1
    have h2 : 2 ^ n ≤ 2 ^ 2 := by
      rw [hcardV]
      calc Nat.card R * 2 ≤ 2 * 2 := Nat.mul_le_mul_right _ h1
        _ = 2 ^ 2 := by norm_num
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
    rcases h.n_mem with rfl | rfl | rfl <;> omega
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvW : v ∈ W := hW ▸ hv
    exact (Subgroup.mem_centralizer_iff.1 hvW.2 y rfl).symm

end L1299

end CFSG.Quasithin.H13
