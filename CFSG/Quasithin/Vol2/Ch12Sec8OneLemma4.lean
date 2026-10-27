module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma3
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

theorem exists_rotation {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {P : Submodule K W} {a b : W} (ha : a ∉ P ⊔ K ∙ b) (hb : b ∉ P ⊔ K ∙ a) :
    ∃ ρ : W ≃ₗ[K] W, (∀ x, ρ (ρ (ρ x)) = x) ∧ ρ a = b ∧ ρ b = -a - b ∧
      ∀ x ∈ P, ρ x = x := by
  obtain ⟨fa₀, hfa, hPa⟩ := Submodule.exists_le_ker_of_notMem ha
  obtain ⟨fb₀, hfb, hPb⟩ := Submodule.exists_le_ker_of_notMem hb
  set fa := (fa₀ a)⁻¹ • fa₀ with hfadef
  set fb := (fb₀ b)⁻¹ • fb₀ with hfbdef
  have hfa1 : fa a = 1 := by
    rw [hfadef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfa]
  have hfb1 : fb b = 1 := by
    rw [hfbdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfb]
  have hker : ∀ {f₀ : W →ₗ[K] K} {c : K} {x : W}, f₀ x = 0 → (c • f₀) x = 0 := by
    intro f₀ c x h
    rw [LinearMap.smul_apply, h, smul_zero]
  have hfab : fa b = 0 := hker
    (LinearMap.mem_ker.1 (hPa (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))))
  have hfba : fb a = 0 := hker
    (LinearMap.mem_ker.1 (hPb (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))))
  have hfaP : ∀ x ∈ P, fa x = 0 := fun x hx =>
    hker (LinearMap.mem_ker.1 (hPa (Submodule.mem_sup_left hx)))
  have hfbP : ∀ x ∈ P, fb x = 0 := fun x hx =>
    hker (LinearMap.mem_ker.1 (hPb (Submodule.mem_sup_left hx)))
  let ρ0 : W →ₗ[K] W := LinearMap.id + fa.smulRight (b - a) + fb.smulRight (-a - b - b)
  have hρ0 : ∀ x, ρ0 x = x + fa x • (b - a) + fb x • (-a - b - b) := fun x => rfl
  have hfaρ : ∀ y, fa (ρ0 y) = -fb y := by
    intro y
    rw [hρ0, map_add, map_add, map_smul, map_smul, map_sub, map_sub, map_sub, map_neg,
      hfa1, hfab, smul_eq_mul, smul_eq_mul]
    ring
  have hfbρ : ∀ y, fb (ρ0 y) = fa y - fb y := by
    intro y
    rw [hρ0, map_add, map_add, map_smul, map_smul, map_sub, map_sub, map_sub, map_neg,
      hfb1, hfba, smul_eq_mul, smul_eq_mul]
    ring
  have h3 : ∀ x, ρ0 (ρ0 (ρ0 x)) = x := by
    intro x
    rw [hρ0 (ρ0 (ρ0 x)), hfaρ (ρ0 x), hfbρ (ρ0 x), hfaρ x, hfbρ x, hρ0 (ρ0 x), hfaρ x, hfbρ x,
      hρ0 x]
    module
  let ρ : W ≃ₗ[K] W := LinearEquiv.ofLinearMap ρ0 (ρ0 ∘ₗ ρ0)
    (LinearMap.ext fun x => h3 x) (LinearMap.ext fun x => h3 x)
  refine ⟨ρ, h3, ?_, ?_, fun x hx => ?_⟩
  · show ρ0 a = b
    rw [hρ0, hfa1, hfba, one_smul, zero_smul, add_zero]
    abel
  · show ρ0 b = -a - b
    rw [hρ0, hfab, hfb1, one_smul, zero_smul, add_zero]
    abel
  · show ρ0 x = x
    rw [hρ0, hfaP x hx, hfbP x hx, zero_smul, zero_smul, add_zero, add_zero]

theorem two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  have h : ¬ 3 ∣ 2 ^ k := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)) (by norm_num)
  omega

variable {G : Type} [Group G]

theorem subOf_mono {V : Subgroup G} [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)]
    {W W' : Subgroup G} (h : W ≤ W') : subOf (V := V) W ≤ subOf (V := V) W' :=
  fun _ hx => mem_subOf.2 (h (mem_subOf.1 hx))

theorem irred_lOne (h1222 : Stmt12_2_2) [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    IsIrredOnSection (lOne L V₁ ⊔ T) V V₁ := by
  obtain ⟨hcard, hsq, -⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hlOne : lOne L V₁ ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) := oTwoUpper_le _
  refine ⟨lt_of_le_of_ne hV₁.1 fun heq => ?_,
    sup_le ((hlOne.trans inf_le_left).trans hLV) hTV,
    sup_le (hlOne.trans inf_le_right) hV₁.2.2, fun W hV₁W hWV hXW => ?_⟩
  · have h1 := hV₁.2.1
    rw [heq, hcard] at h1
    have := Nat.pow_right_injective le_rfl h1
    rcases h.n_mem with rfl | rfl | rfl <;> omega
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
  have hkX : l ^ 2 ^ k ∈ Subgroup.normalizer (W : Set G) :=
    hXW (Subgroup.mem_sup_left hk)
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

theorem lemma12_8_4_one (h1222 : Stmt12_2_2) [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ H : Subgroup G} (hV₁ : IsTSub T V V₁ 1)
    (hH : IsHzOne T L V₁ H) : AlmostSpecialHyp V V₁ L T H := by
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes h1222
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.hyp.sylow
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hO2 : oTwoUpper L = L := h.hyp.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).2 (le_normalizer_oTwoUpper L))
    (fun x hx => exists_pow_mem_oTwoUpper L hx)
  refine
    { elemAbelian := ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩, hsq⟩
      ne_bot := fun hb => by
        have h1 := hV₁.2.1
        rw [hb, Subgroup.card_bot] at h1
        norm_num at h1
      le_V := hV₁.1
      oTwo_eq := hO2.symm
      V_le_T := hVT
      T_le_normV₁ := hV₁.2.2
      T_le_normV := hTV
      T_le_normL := h.hyp.normalizes
      sylow_LT := ?_
      H_le := hH.2.1
      lOne_sup_le := hH.1.1
      sylow_H := ?_
      charTwo := ?_
      irred := irred_lOne h1222 h hV₁ }
  · have := isSylowTwoOf_of_sylow S (hS ▸ (le_sup_right : T ≤ L ⊔ T))
    rwa [hS] at this
  · have := isSylowTwoOf_of_sylow S (hS ▸ hTH)
    rwa [hS] at this
  · exact charTwo_of_inH h.hyp.qtke.2.1 S (hS ▸ ⟨hTH, hH.1.2⟩)

@[expose] def Lemma12_8_4_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
    ∀ V₁ H : Subgroup G, IsTSub T V V₁ 1 → IsHzOne T L V₁ H →
      centralizerMod V₁ H (conjClosure V H) = pCoreOf 2 H

theorem lemma12_8_4_of_four (h1222 : Stmt12_2_2) (h4 : Lemma12_8_4_four) : Lemma12_8_4 := by
  intro G _ _ T L V n h V₁ H hV₁ hH
  have hA := lemma12_8_4_one h1222 h hV₁ hH
  exact ⟨hA, ⟨hA.G22_one.2, hA.G22_four⟩, hA.G22_two, h4 G T L V n h V₁ H hV₁ hH⟩

end CFSG.Quasithin.H13
