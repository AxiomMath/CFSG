module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6Rad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement Pointwise

namespace L1297

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_centralizerMod_sup (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    IsPGroup 2 ↥(centralizerMod V₁ (L ⊔ T) V) := by
  obtain ⟨-, hsq, -⟩ := h.card_sq
  have hT2 : IsPGroup 2 T := h.hyp.sylow.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hQ := (inf_centralizer_eq_sup_inf_centralizer h1222 h).1
  intro x
  obtain ⟨hxX, hxN, hxc⟩ := x.2
  have hx2 : (x : G) * (x : G) ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hQ]
    refine ⟨Subgroup.mul_mem _ hxX hxX, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    set c := (x : G) * u * (x : G)⁻¹ * u⁻¹ with hcdef
    have hd : c ∈ V₁ := hxc u hu
    have hxc' : (x : G) * c * (x : G)⁻¹ = c := by
      have h1 := Subgroup.mem_centralizer_iff.1
        (le_centralizer_normalizer_of_card_eq_two hV₁2 hd) _ hxN
      rw [h1, mul_inv_cancel_right]
    have hcc : c * c = 1 := by rw [← sq]; exact hsq _ (hV₁.1 hd)
    have hxu : (x : G) * u * (x : G)⁻¹ = c * u := by rw [hcdef]; group
    have key : (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ = u := by
      calc (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ =
            (x : G) * ((x : G) * u * (x : G)⁻¹) * (x : G)⁻¹ := by group
        _ = (x : G) * (c * u) * (x : G)⁻¹ := by rw [hxu]
        _ = ((x : G) * c * (x : G)⁻¹) * ((x : G) * u * (x : G)⁻¹) := by group
        _ = c * (c * u) := by rw [hxc', hxu]
        _ = u := by rw [← mul_assoc, hcc, one_mul]
    calc u * ((x : G) * (x : G)) =
          ((x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹) * ((x : G) * (x : G)) := by
          rw [key]
      _ = (x : G) * (x : G) * u := by group
  obtain ⟨k, hk⟩ := (hT2.to_le inf_le_left) ⟨_, hx2⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
  rw [pow_succ', pow_mul, sq]
  exact h1

theorem centralizerMod_sup_le_T (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    centralizerMod V₁ (L ⊔ T) V ≤ T := by
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  exact L1296.le_of_isPGroup h.hyp.sylow (isPGroup_centralizerMod_sup h1222 h hV₁)
    (L1296.le_normalizer_centralizerMod (le_sup_right.trans Subgroup.le_normalizer) hV₁.2.2 hTV)

theorem exists_mem_T_conj_mul (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {z : G}
    (hz : z ∈ V₁) (hz1 : z ≠ 1) {u : G} (hu : u ∈ V) (huV₁ : u ∉ V₁) :
    ∃ t ∈ T, t * u * t⁻¹ = u * z ∧ ∀ x ∈ V₁, t * x * t⁻¹ = x := by
  classical
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hzV := hV₁.1 hz
  let _ := zmodModuleOf hsq
  set a₁ : Additive ↥V := Additive.ofMul ⟨z, hzV⟩ with ha₁
  set a₂ : Additive ↥V := Additive.ofMul ⟨u, hu⟩ with ha₂
  have ha : a₂ ∉ (ZMod 2) ∙ a₁ := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul] at hc
      apply huV₁
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₂, toMul_ofMul, toMul_zero, OneMemClass.coe_one] at this
      rw [← this]
      exact V₁.one_mem
    · rw [one_smul] at hc
      apply huV₁
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₁, ha₂, toMul_ofMul] at this
      rw [← this]
      exact hz
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem ha
  have hfa₁ : f a₁ = 0 := LinearMap.mem_ker.1 (hf2 (Submodule.mem_span_singleton_self a₁))
  have hfa₂ : f a₂ = 1 := Flag.zmod_two_eq_one hf1
  let τ0 : Additive ↥V →ₗ[ZMod 2] Additive ↥V := LinearMap.id + f.smulRight a₁
  have hτ0 : ∀ x, τ0 x = x + f x • a₁ := fun x => rfl
  have hinv : Function.Involutive τ0 := by
    intro x
    rw [hτ0, hτ0, map_add, map_smul, hfa₁, smul_zero, add_zero, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  let α : MulAut ↥V :=
    { toFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      invFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      left_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      right_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, toMul_add] }
  have hα : ∀ x : ↥V, ((α x : ↥V) : G) = (x : G) ∨ ((α x : ↥V) : G) = (x : G) * z := by
    intro x
    have e : α x = x * Additive.toMul (f (Additive.ofMul x) • a₁) := by
      show Additive.toMul (τ0 (Additive.ofMul x)) = _
      rw [hτ0, toMul_add, toMul_ofMul]
    rcases zmod_two_cases (f (Additive.ofMul x)) with h0 | h1
    · left
      rw [e, h0, zero_smul, toMul_zero, mul_one]
    · right
      rw [e, h1, one_smul, Subgroup.coe_mul, ha₁, toMul_ofMul]
  have hαu : ((α ⟨u, hu⟩ : ↥V) : G) = u * z := by
    show ((Additive.toMul (τ0 a₂) : ↥V) : G) = _
    rw [hτ0, hfa₂, one_smul, toMul_add, Subgroup.coe_mul, ha₁, ha₂, toMul_ofMul, toMul_ofMul]
  have hαL : α ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨g, hgN⟩, hgL, hgα⟩ := hαL
  have hgL' : g ∈ L := Subgroup.mem_subgroupOf.1 hgL
  have hconj : ∀ x (hx : x ∈ V), g * x * g⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hgα]
    rfl
  have hgV₁ : ∀ x ∈ V₁, g * x * g⁻¹ = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      group
    have e := SteinbergBS.eq_of_card_le_two hV₁2.le hx hz hx1 hz1
    subst e
    rw [hconj x hzV]
    show ((Additive.toMul (τ0 a₁) : ↥V) : G) = x
    rw [hτ0, hfa₁, zero_smul, add_zero, ha₁, toMul_ofMul]
  have hgN₁ : g ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => by
      have := hgV₁ x hx
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group)
  have hgE : g ∈ centralizerMod V₁ (L ⊔ T) V := by
    refine ⟨Subgroup.mem_sup_left hgL', hgN₁, fun w hw => ?_⟩
    rw [hconj w hw]
    rcases hα ⟨w, hw⟩ with e | e
    · rw [e, mul_inv_cancel]
      exact V₁.one_mem
    · rw [e, show w * z * w⁻¹ = z from by rw [hab w hw z hzV]; group]
      exact hz
  exact ⟨g, centralizerMod_sup_le_T h1222 h hV₁ hgE, by rw [hconj u hu, hαu], hgV₁⟩

theorem exists_mem_lOne_conj {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {u u' : G} (hu : u ∈ V) (hu' : u' ∈ V)
    (huV₁ : u ∉ V₁) (hu'V₁ : u' ∉ V₁) :
    ∃ σ ∈ lOne L V₁, σ * u * σ⁻¹ * u'⁻¹ ∈ V₁ := by
  classical
  by_cases huu : u * u'⁻¹ ∈ V₁
  · exact ⟨1, (lOne L V₁).one_mem, by simpa using huu⟩
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  let _ := zmodModuleOf hsq
  set a : Additive ↥V := Additive.ofMul ⟨u, hu⟩ with hadef
  set b : Additive ↥V := Additive.ofMul ⟨u', hu'⟩ with hbdef
  have hmem : ∀ x : Additive ↥V, x ∈ subOf (V := V) V₁ ↔
      ((Additive.toMul x : ↥V) : G) ∈ V₁ := fun x => mem_subOf
  have hab' : ∀ {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hxV₁ : x ∉ V₁) (hxy : x * y⁻¹ ∉ V₁),
      Additive.ofMul (⟨x, hx⟩ : ↥V) ∉ subOf (V := V) V₁ ⊔ (ZMod 2) ∙
        Additive.ofMul (⟨y, hy⟩ : ↥V) := by
    intro x y hx hy hxV₁ hxy hmem'
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hmem'
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hq
    rcases zmod_two_cases t with rfl | rfl
    · rw [zero_smul, add_zero] at hpq
      exact hxV₁ (by have := (hmem p).1 hp; rwa [hpq] at this)
    · rw [one_smul] at hpq
      apply hxy
      have h1 := (hmem p).1 hp
      have h2 : p = Additive.ofMul (⟨x, hx⟩ : ↥V) - Additive.ofMul ⟨y, hy⟩ := by
        rw [← hpq]; abel
      rw [h2, toMul_sub, toMul_ofMul, toMul_ofMul, Subgroup.coe_div, div_eq_mul_inv] at h1
      exact h1
  have huu' : u' * u⁻¹ ∉ V₁ := fun h1 => huu (by
    have := V₁.inv_mem h1
    rwa [show (u' * u⁻¹)⁻¹ = u * u'⁻¹ by group] at this)
  obtain ⟨ρ, hρ3, hρa, -, hρP⟩ := exists_rotation (hab' hu hu' huV₁ huu) (hab' hu' hu hu'V₁ huu')
  have hαL : mulAutOfLin ρ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.1 hlL
  have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ =
      ((Additive.toMul (ρ (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
    intro x hx
    rw [← mulAutOfLin_apply, ← hlα]
    rfl
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
  have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    have h1 := hconj x (hV₁.1 hx)
    rw [hρP _ ((hmem (Additive.ofMul ⟨x, hV₁.1 hx⟩)).2 hx), toMul_ofMul] at h1
    have h2 : l * x = x * l := by
      calc l * x = (l * x * l⁻¹) * l := by group
        _ = x * l := by rw [h1]
    exact h2.symm
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G))
    (Subgroup.mem_inf.2 ⟨hlL', hlV₁⟩)
  have hρ3' : ρ ^ 3 = 1 := LinearEquiv.ext fun x => by
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hρ3 x
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (2 ^ k * r) % 3 = 1 ∧ l ^ (2 ^ k * r) ∈ lOne L V₁ := by
    rcases two_pow_mod_three k with h1 | h2
    · refine ⟨1, by rw [mul_one, h1], by rw [mul_one]; exact hk⟩
    · refine ⟨2, by rw [Nat.mul_mod, h2], by rw [pow_mul]; exact (lOne L V₁).pow_mem hk 2⟩
  refine ⟨l ^ (2 ^ k * r), hr.2, ?_⟩
  have hred : ρ ^ (2 ^ k * r) = ρ := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ k * r) 3, pow_add, pow_mul, hρ3', one_pow, one_mul,
      hr.1, pow_one]
  rw [hpow _ u hu, hred]
  show ((Additive.toMul (ρ a) : ↥V) : G) * u'⁻¹ ∈ V₁
  rw [hρa, toMul_ofMul, mul_inv_cancel]
  exact V₁.one_mem

theorem conj_eq_of_mem_normalizer {V₁ : Subgroup G} (hV₁2 : Nat.card V₁ = 2) {z g : G}
    (hz : z ∈ V₁) (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) : g * z * g⁻¹ = z := by
  have h1 := Subgroup.mem_centralizer_iff.1 (le_centralizer_normalizer_of_card_eq_two hV₁2 hz) g hg
  rw [h1, mul_inv_cancel_right]

theorem mem_normalizer_of_conj_eq {V₁ : Subgroup G} (hV₁2 : Nat.card V₁ = 2) {z g : G}
    (hz : z ∈ V₁) (hz1 : z ≠ 1) (hg : g * z * g⁻¹ = z) :
    g ∈ Subgroup.normalizer (V₁ : Set G) := by
  have hfix : ∀ x ∈ V₁, g * x * g⁻¹ = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      group
    rw [SteinbergBS.eq_of_card_le_two hV₁2.le hx hz hx1 hz1, hg]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hfix x hx]
    exact hx
  · intro hx
    by_cases hx1 : g * x * g⁻¹ = 1
    · have : x = 1 := by
        have := congrArg (fun y => g⁻¹ * y * g) hx1
        simpa [mul_assoc] using this
      rw [this]
      exact V₁.one_mem
    have e := SteinbergBS.eq_of_card_le_two hV₁2.le hx hz hx1 hz1
    have : x = z := by
      have h2 : g * x * g⁻¹ = g * z * g⁻¹ := by rw [e, hg]
      have := congrArg (fun y => g⁻¹ * y * g) h2
      simpa [mul_assoc] using this
    rw [this]
    exact hz

theorem conj_not_mem_of_not_mem_normalizer {V₁ : Subgroup G} (hV₁2 : Nat.card V₁ = 2) {z g : G}
    (hz : z ∈ V₁) (hz1 : z ≠ 1) (hg : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    g * z * g⁻¹ ∉ V₁ := by
  intro h
  have hne : g * z * g⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    have := congrArg (fun y => g⁻¹ * y * g) h1
    simpa [mul_assoc] using this
  exact hg (mem_normalizer_of_conj_eq hV₁2 hz hz1
    (SteinbergBS.eq_of_card_le_two hV₁2.le h hz hne hz1))

theorem exists_mem_sup_conj_eq (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {u u' : G}
    (hu : u ∈ V) (hu' : u' ∈ V) (huV₁ : u ∉ V₁) (hu'V₁ : u' ∉ V₁) :
    ∃ s ∈ lOne L V₁ ⊔ T, s * u * s⁻¹ = u' := by
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  obtain ⟨σ, hσ, hσu⟩ := exists_mem_lOne_conj h hV₁ hu hu' huV₁ hu'V₁
  set c := σ * u * σ⁻¹ * u'⁻¹ with hc
  by_cases hc1 : c = 1
  · refine ⟨σ, Subgroup.mem_sup_left hσ, ?_⟩
    calc σ * u * σ⁻¹ = c * u' := by rw [hc]; group
      _ = u' := by rw [hc1, one_mul]
  have hu'c : u' * c ∈ V := V.mul_mem hu' (hV₁.1 hσu)
  have hu'cV₁ : u' * c ∉ V₁ := fun h1 => hu'V₁ (by
    have := V₁.mul_mem h1 (V₁.inv_mem hσu)
    rwa [mul_inv_cancel_right] at this)
  obtain ⟨t, htT, htu, -⟩ := exists_mem_T_conj_mul h1222 h hV₁ hσu hc1 hu'c hu'cV₁
  refine ⟨t * σ, Subgroup.mul_mem _ (Subgroup.mem_sup_right htT) (Subgroup.mem_sup_left hσ), ?_⟩
  have hcc : c * c = 1 := by rw [← sq]; exact hsq _ (hV₁.1 hσu)
  have hσu' : σ * u * σ⁻¹ = u' * c := by
    rw [hab u' hu' c (hV₁.1 hσu), hc]
    group
  calc t * σ * u * (t * σ)⁻¹ = t * (σ * u * σ⁻¹) * t⁻¹ := by group
    _ = t * (u' * c) * t⁻¹ := by rw [hσu']
    _ = u' * c * c := htu
    _ = u' := by rw [mul_assoc, hcc, mul_one]

theorem normalizer_sup_inf_le {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    (L ⊔ T) ⊓ Subgroup.normalizer (V₁ : Set G) ≤ lOne L V₁ ⊔ T := by
  intro x ⟨hxLT, hxN⟩
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T h.hyp.normalizes
  obtain ⟨l, hl, t, ht, rfl⟩ : x ∈ (L : Set G) * (T : Set G) := by rw [← hmul]; exact hxLT
  have hlN : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    have := Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ (hV₁.2.2 ht))
    simpa using this
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    F7.isSylowTwoOf_mono_right (F7.isSylowTwoOf_inf_normal
      (isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.sylow le_top) (le_top : L ≤ ⊤) h.hyp.normalizes)
      (le_inf inf_le_right (inf_le_left.trans hV₁.2.2)) inf_le_left
  have hl' := F7.isSylowTwoOf_le_sup_of_two_power hsyl
    (le_normalizer_oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G)))
    (fun y hy => exists_pow_mem_oTwoUpper _ hy) ⟨hl, hlN⟩
  have hle : lOne L V₁ ⊔ (T ⊓ L) ≤ lOne L V₁ ⊔ T := sup_le_sup le_rfl inf_le_left
  exact Subgroup.mul_mem _ (hle hl') (Subgroup.mem_sup_right ht)

theorem sup_le_of_not_le_normalizer (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {X : Subgroup G}
    (hL₁X : lOne L V₁ ⊔ T ≤ X) (hXLT : X ≤ L ⊔ T)
    (hXN : ¬ X ≤ Subgroup.normalizer (V₁ : Set G)) : L ⊔ T ≤ X := by
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le h.hyp.irrPlus.2.2.1 hTV
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ V₁, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall V₁).2 hall
    rw [this, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  have hzV := hV₁.1 hz
  obtain ⟨x, hxX, hxN⟩ := IsConcreteLE.not_le_iff_exists.1 hXN
  have hxLT := hXLT hxX
  intro l hl
  by_cases hlN : l ∈ Subgroup.normalizer (V₁ : Set G)
  · exact hL₁X (normalizer_sup_inf_le h hV₁ ⟨hl, hlN⟩)
  have ha := conj_not_mem_of_not_mem_normalizer hV₁2 hz hz1 hxN
  have hb := conj_not_mem_of_not_mem_normalizer hV₁2 hz hz1 hlN
  have haV : x * z * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLTV hxLT) z).1 hzV
  have hbV : l * z * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLTV hl) z).1 hzV
  obtain ⟨s, hs, hsab⟩ := exists_mem_sup_conj_eq h1222 h hV₁ haV hbV ha hb
  have hsLT : s ∈ L ⊔ T := (sup_le_sup_right ((oTwoUpper_le _).trans inf_le_left) T) hs
  set g := l⁻¹ * s * x with hg
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = l⁻¹ * (s * (x * z * x⁻¹) * s⁻¹) * l := by rw [hg]; group
      _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [hsab]
      _ = z := by group
  have hgN := mem_normalizer_of_conj_eq hV₁2 hz hz1 hgz
  have hgLT : g ∈ L ⊔ T := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) hsLT)
    hxLT
  have hgX : g ∈ X := hL₁X (normalizer_sup_inf_le h hV₁ ⟨hgLT, hgN⟩)
  have hl' : l = s * x * g⁻¹ := by rw [hg]; group
  rw [hl']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hL₁X hs) hxX) (Subgroup.inv_mem _ hgX)

theorem mem_centralizer_of_odd {V₁ V₂ : Subgroup G} (hV₁2 : Nat.card V₁ = 2)
    (hV₂4 : Nat.card V₂ = 4) (hV₁₂ : V₁ ≤ V₂) (hsq : ∀ v ∈ V₂, v ^ 2 = 1) {g : G}
    (hg₁ : g ∈ Subgroup.normalizer (V₁ : Set G)) (hg₂ : g ∈ Subgroup.normalizer (V₂ : Set G))
    (hodd : Odd (orderOf g)) : g ∈ Subgroup.centralizer (V₂ : Set G) := by
  have hidx : (V₁.subgroupOf V₂).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card V₁ V₂
    rw [inf_eq_left.2 hV₁₂, hV₁2, hV₂4] at h1
    have h2 : V₁.relIndex V₂ = 2 := by omega
    exact h2
  refine mem_centralizer_of_odd_of_commutator_mem hV₁₂ hV₁2 hsq hg₁ (fun v hv => ?_) hodd
  have hgv : g * v * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 hg₂ v).1 hv
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g * v * g⁻¹, hgv⟩)
    (b := ⟨v, hv⟩⁻¹)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
  rw [key]
  have hiff : g * v * g⁻¹ ∈ V₁ ↔ v ∈ V₁ := by
    constructor
    · intro h1
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg₁) _).1 h1
      simpa [mul_assoc] using this
    · exact fun h1 => (Subgroup.mem_normalizer_iff.1 hg₁ v).1 h1
  rw [hiff, V₁.inv_mem_iff]

theorem pRank_three_le {V₁ V₂ Y : Subgroup G} (hV₁2 : Nat.card V₁ = 2) (hV₂4 : Nat.card V₂ = 4)
    (hV₁₂ : V₁ ≤ V₂) (hsq : ∀ v ∈ V₂, v ^ 2 = 1) (hY₁ : Y ≤ Subgroup.normalizer (V₁ : Set G))
    (hY₂ : Y ≤ Subgroup.normalizer (V₂ : Set G)) :
    CFSG.Open.pRank 3 Y ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (V₂ : Set G)) := by
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Y
  refine CFSG.SectionRank.le_pRank (by norm_num) (fun g hg => ?_) hE hcard
  have h3 : g ^ 3 = 1 := hE.2 g hg
  have hodd : Odd (orderOf g) := by
    have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hd with h1 | h1 <;> rw [h1] <;> decide
  exact mem_centralizer_of_odd hV₁2 hV₂4 hV₁₂ hsq (hY₁ (hEY hg)) (hY₂ (hEY hg)) hodd

theorem card_sl_three : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem card_sl_four : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_four]

end L1297

end CFSG.Quasithin.H13
