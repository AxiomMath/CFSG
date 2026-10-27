module

public import CFSG.Quasithin.Vol2.Ch11SecANat

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

theorem eq_one_of_mul_self {K : Type} [Field K] [CharP K 2] {x : K} (h : x * x = 1) : x = 1 :=
  (mul_self_eq_one_iff.mp h).elim id fun h' => h'.trans (CharTwo.neg_eq 1)

theorem relIndex_le_card_of_fiber {G : Type} [Group G] {A H : Subgroup G} {S : Type} [Finite S]
    (P : S → ↥A → Prop) (hP : ∀ a, ∃ s, P s a)
    (hfib : ∀ s a b, P s a → P s b → ((a⁻¹ * b : ↥A) : G) ∈ H) :
    H.relIndex A ≤ Nat.card S := by
  classical
  let g : S → ↥A ⧸ H.subgroupOf A := fun s =>
    if h : ∃ a, P s a then QuotientGroup.mk h.choose else QuotientGroup.mk 1
  have hg : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨s, hs⟩ := hP a
      have h : ∃ a, P s a := ⟨a, hs⟩
      refine ⟨s, ?_⟩
      change (if h : ∃ a, P s a then QuotientGroup.mk h.choose else QuotientGroup.mk 1) = _
      rw [dite_eq_left h]
      exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (hfib s _ a h.choose_spec hs))
  have := Nat.card_le_card_of_surjective g hg
  rw [Subgroup.relIndex, Subgroup.index]
  exact this

variable {G : Type} [Group G] {V : Subgroup G} {K M : Type} [Field K] [AddCommGroup M]
  [Module K M]

theorem conjV_mul_apply {a b : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hb : b ∈ Subgroup.normalizer (V : Set G)) (hab : a * b ∈ Subgroup.normalizer (V : Set G))
    (v : ↥V) : SecA.conjV V (a * b) hab v = SecA.conjV V a ha (SecA.conjV V b hb v) := by
  apply Subtype.ext
  simp only [SecA.conjV_apply_coe]
  group

theorem conjV_conjV_of_sq {a : G} (haV : a ∈ Subgroup.normalizer (V : Set G)) (ha2 : a ^ 2 = 1)
    (w : ↥V) : SecA.conjV V a haV (SecA.conjV V a haV w) = w := by
  have ha : a * a = 1 := by rw [← pow_two, ha2]
  apply Subtype.ext
  rw [SecA.conjV_apply_coe, SecA.conjV_apply_coe, inv_eq_of_mul_eq_one_right ha]
  calc a * (a * (w : G) * a) * a = (a * a) * w * (a * a) := by simp only [mul_assoc]
    _ = w := by rw [ha, one_mul, mul_one]

theorem coord_eq {u₀ u₁ : M}
    (hind : ∀ c d : K, c • u₀ + d • u₁ = 0 → c = 0 ∧ d = 0) {c d c' d' : K}
    (h : c • u₀ + d • u₁ = c' • u₀ + d' • u₁) : c = c' ∧ d = d' := by
  have h0 : (c - c') • u₀ + (d - d') • u₁ = 0 := by
    calc (c - c') • u₀ + (d - d') • u₁ = (c • u₀ + d • u₁) - (c' • u₀ + d' • u₁) := by
          rw [sub_smul, sub_smul]; abel
      _ = 0 := by rw [h, sub_self]
  obtain ⟨h1, h2⟩ := hind _ _ h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

theorem coeff_eq_of_smul_eq {u₀ : M} (hu₀ : u₀ ≠ 0) {c d : K} (h : c • u₀ = d • u₀) : c = d := by
  rw [← sub_eq_zero, ← sub_smul] at h
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hu₀)

theorem exists_scalar_inv {f : ↥V → M} (hsurj : Function.Surjective f) {u₀ : M} (hu₀ : u₀ ≠ 0)
    {V₁ : Subgroup G} (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀) {a : G}
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (haV₁ : a ∈ Subgroup.normalizer (V₁ : Set G))
    (ha2 : a ^ 2 = 1) {T : M →+ M} {σ : K →+* K}
    (hσ : ∀ (c : K) (x : M), T (c • x) = σ c • T x)
    (hT : ∀ w, T (f w) = f (SecA.conjV V a haV w)) :
    ∃ α : K, T u₀ = α • u₀ ∧ (∀ x, T (T x) = x) ∧ (∀ c, σ (σ c) = c) ∧ σ α * α = 1 := by
  obtain ⟨w₀, hw₀⟩ := hsurj u₀
  have hmV₁ : ((SecA.conjV V a haV w₀ : ↥V) : G) ∈ V₁ := by
    rw [SecA.conjV_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp haV₁ w₀).mp ((hV₁ w₀).mpr ⟨1, by rw [hw₀, one_smul]⟩)
  obtain ⟨α, hα⟩ := (hV₁ _).mp hmV₁
  have h0 : T u₀ = α • u₀ := by rw [← hw₀, hT, hα, hw₀]
  have hTT : ∀ x, T (T x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hsurj x
    rw [hT, hT, conjV_conjV_of_sq haV ha2]
  have hu : ∀ c : K, T (T (c • u₀)) = (σ (σ c) * (σ α * α)) • u₀ := fun c => by
    rw [hσ, h0, smul_smul, hσ, h0, smul_smul, map_mul, mul_assoc]
  have hαα : σ α * α = 1 := by
    have h1 := hu 1
    rw [hTT, map_one, map_one, one_mul] at h1
    exact (coeff_eq_of_smul_eq hu₀ h1).symm
  refine ⟨α, h0, hTT, fun c => ?_, hαα⟩
  have h1 := hu c
  rw [hTT, hαα, mul_one] at h1
  exact (coeff_eq_of_smul_eq hu₀ h1).symm

omit [AddCommGroup M] in
theorem mem_centralizer_of_fixes {f : ↥V → M} (hinj : Function.Injective f) {W : Subgroup G}
    (hWV : W ≤ V) {a : G} (haV : a ∈ Subgroup.normalizer (V : Set G))
    (h : ∀ v : ↥V, (v : G) ∈ W → f (SecA.conjV V a haV v) = f v) :
    a ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h2 := congrArg Subtype.val (hinj (h ⟨g, hWV hg⟩ hg))
  rw [SecA.conjV_apply_coe] at h2
  calc g * a = a * g * a⁻¹ * a := by rw [h2]
    _ = a * g := by group

theorem exists_ne_of_not_mem_centralizer [CharP K 2] {f : ↥V → M} (hinj : Function.Injective f)
    {u₀ : M} {V₁ : Subgroup G} (hV₁V : V₁ ≤ V)
    (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀) {a : G}
    (haV : a ∈ Subgroup.normalizer (V : Set G)) {T : M →+ M} {σ : K →+* K}
    (hσ : ∀ (c : K) (x : M), T (c • x) = σ c • T x)
    (hT : ∀ w, T (f w) = f (SecA.conjV V a haV w)) {α : K} (h0 : T u₀ = α • u₀)
    (hαα : σ α * α = 1) (haC : a ∉ Subgroup.centralizer (V₁ : Set G)) : ∃ x, σ x ≠ x := by
  by_contra hne
  push Not at hne
  have hα1 : α = 1 := eq_one_of_mul_self (by rw [← hαα, hne])
  exact haC (mem_centralizer_of_fixes hinj hV₁V haV fun v hv => by
    obtain ⟨c, hc⟩ := (hV₁ v).mp hv
    rw [← hT, hc, hσ, hne, h0, hα1, one_smul])

theorem exists_transv [CharP K 2] {f : ↥V → M} (hsurj : Function.Surjective f) {u₀ u₁ : M}
    (hind : ∀ c d : K, c • u₀ + d • u₁ = 0 → c = 0 ∧ d = 0) {V₁ V₂ : Subgroup G}
    (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • u₀)
    (hV₂ : ∀ v : ↥V, (v : G) ∈ V₂ ↔ ∃ c d : K, f v = c • u₀ + d • u₁) {a : G}
    (haV : a ∈ Subgroup.normalizer (V : Set G)) (haV₂ : a ∈ Subgroup.normalizer (V₂ : Set G))
    (haC : a ∈ Subgroup.centralizer (V₁ : Set G)) (ha2 : a ^ 2 = 1) {T : M →+ M}
    {σ : K →+* K} (hσ : ∀ (c : K) (x : M), T (c • x) = σ c • T x)
    (hT : ∀ w, T (f w) = f (SecA.conjV V a haV w)) :
    ∃ s : K, ∀ (v : ↥V) (x y : K), f v = x • u₀ + y • u₁ →
      f (SecA.conjV V a haV v) = (x + y * s) • u₀ + y • u₁ := by
  have hu₀ : u₀ ≠ 0 := fun h =>
    one_ne_zero (hind 1 0 (by rw [h, smul_zero, zero_smul, add_zero])).1
  have hfix : ∀ w : ↥V, (w : G) ∈ V₁ → SecA.conjV V a haV w = w := fun w hw => by
    apply Subtype.ext
    rw [SecA.conjV_apply_coe, ← Subgroup.mem_centralizer_iff.mp haC w hw, mul_inv_cancel_right]
  have hTV₁ : ∀ c : K, T (c • u₀) = c • u₀ := fun c => by
    obtain ⟨w, hw⟩ := hsurj (c • u₀)
    rw [← hw, hT, hfix w ((hV₁ w).mpr ⟨c, hw⟩)]
  have h0 : T u₀ = u₀ := by simpa using hTV₁ 1
  have hσ1 : ∀ c, σ c = c := fun c => by
    have h1 := hTV₁ c
    rw [hσ, h0] at h1
    exact coeff_eq_of_smul_eq hu₀ h1
  obtain ⟨w₁, hw₁⟩ := hsurj u₁
  have hm : ((SecA.conjV V a haV w₁ : ↥V) : G) ∈ V₂ := by
    rw [SecA.conjV_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp haV₂ w₁).mp
      ((hV₂ w₁).mpr ⟨0, 1, by rw [hw₁, zero_smul, zero_add, one_smul]⟩)
  obtain ⟨s, t, hst⟩ := (hV₂ _).mp hm
  have h1 : T u₁ = s • u₀ + t • u₁ := by rw [← hw₁, hT, hst, hw₁]
  have hlin : ∀ x y : K, T (x • u₀ + y • u₁) = (x + y * s) • u₀ + (y * t) • u₁ := fun x y => by
    rw [map_add, hσ, hσ, hσ1, hσ1, h0, h1, smul_add, smul_smul, smul_smul, add_smul]
    abel
  have ht : t = 1 := by
    have h2 : T (T u₁) = u₁ := by rw [← hw₁, hT, hT, conjV_conjV_of_sq haV ha2]
    rw [h1, hlin] at h2
    have h3 := (coord_eq hind (c' := 0) (d' := 1)
      (h2.trans (by rw [zero_smul, zero_add, one_smul]))).2
    exact eq_one_of_mul_self h3
  refine ⟨s, fun v x y hv => ?_⟩
  rw [← hT, hv, hlin, ht, mul_one]

end CFSG.Quasithin.Vol2.Ch11.SecO1b
