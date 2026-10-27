module

public import CFSG.RankThree.Classical.TransvectionGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Module CFSG.RankThree.Classical

section General

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem det_eq_one_of_isTransvectionWith [FiniteDimensional F V] {t : V ≃ₗ[F] V} {v : V}
    {f : Dual F V} (ht : IsTransvectionWith t v f) : LinearMap.det (t : V →ₗ[F] V) = 1 := by
  have h : (t : V →ₗ[F] V) = LinearMap.transvection f v := LinearMap.ext fun x => by
    rw [LinearEquiv.coe_coe, ht.2.2.2, LinearMap.transvection.apply]
  rw [h, LinearMap.transvection.det, ht.2.2.1, add_zero]

theorem ne_one_of_isTransvectionWith {t : V ≃ₗ[F] V} {v : V} {f : Dual F V}
    (ht : IsTransvectionWith t v f) : t ≠ 1 := by
  intro h1
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact ht.2.1 (LinearMap.ext h)
  have h2 := ht.2.2.2 x
  rw [h1, LinearEquiv.coe_one, id, left_eq_add, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hx h2
  · exact ht.1 h2

theorem apply_eq_self_of_isTransvectionWith_of_mem {t : V ≃ₗ[F] V} {v : V} {f : Dual F V}
    (ht : IsTransvectionWith t v f) {y : V} (hy : t y ∈ Submodule.span F {y}) : t y = y := by
  rw [ht.2.2.2] at hy ⊢
  by_cases hfy : f y = 0
  · rw [hfy, zero_smul, add_zero]
  exfalso
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  have hv : v = (f y)⁻¹ • ((a - 1) • y) := by
    rw [sub_smul, one_smul, ha, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hfy, one_smul]
  have hfv := ht.2.2.1
  rw [hv, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hfv
  have ha1 : a - 1 = 0 := by
    rcases mul_eq_zero.mp hfv with h | h
    · exact absurd h (inv_ne_zero hfy)
    · exact (mul_eq_zero.mp h).resolve_right hfy
  apply ht.1
  rw [hv, ha1, zero_smul, smul_zero]

@[expose] def IsFlagUnipotent (F₁ F₂ : Submodule F V) (x : V ≃ₗ[F] V) : Prop :=
  (∀ y, x y - y ∈ F₂) ∧ (∀ y ∈ F₂, x y - y ∈ F₁) ∧ ∀ y ∈ F₁, x y = y

theorem isFlagUnipotent_one (F₁ F₂ : Submodule F V) : IsFlagUnipotent F₁ F₂ 1 :=
  ⟨fun y => by simp, fun y _ => by simp, fun y _ => rfl⟩

theorem isFlagUnipotent_mul {F₁ F₂ : Submodule F V} (hF : F₁ ≤ F₂) {x y : V ≃ₗ[F] V}
    (hx : IsFlagUnipotent F₁ F₂ x) (hy : IsFlagUnipotent F₁ F₂ y) :
    IsFlagUnipotent F₁ F₂ (x * y) := by
  refine ⟨fun z => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have : (x * y) z - z = (x (y z) - y z) + (y z - z) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [this]
    exact F₂.add_mem (hx.1 _) (hy.1 z)
  · have hyz : y z ∈ F₂ := by
      have := F₂.add_mem (hF (hy.2.1 z hz)) hz
      rwa [sub_add_cancel] at this
    have : (x * y) z - z = (x (y z) - y z) + (y z - z) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [this]
    exact F₁.add_mem (hx.2.1 _ hyz) (hy.2.1 z hz)
  · rw [LinearEquiv.mul_apply, hy.2.2 z hz, hx.2.2 z hz]

end General

section ThreeElements

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

theorem zmod3_three_smul (y : V) : (3 : ℕ) • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_smul]

theorem pow_three_eq_one_of_isFlagUnipotent {F₁ F₂ : Submodule (ZMod 3) V}
    {x : V ≃ₗ[ZMod 3] V} (hx : IsFlagUnipotent F₁ F₂ x) : x ^ 3 = 1 := by
  ext y
  set a := x y - y with ha
  set b := x a - a with hb
  have hxy : x y = y + a := by rw [ha]; abel
  have hxa : x a = a + b := by rw [hb]; abel
  have hxb : x b = b := hx.2.2 b (hx.2.1 a (hx.1 y))
  have h3 : (x ^ 3) y = y + 3 • a + 3 • b := by
    have e : (x ^ 3) y = x (x (x y)) := by
      rw [pow_succ, pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [e, hxy, map_add, map_add, hxy, hxa, map_add, map_add, hxa, hxb, hxy]
    abel
  rw [h3, zmod3_three_smul, zmod3_three_smul, add_zero, add_zero, LinearEquiv.coe_one, id]

@[expose] def flagUnipotentSubgroup (F₁ F₂ : Submodule (ZMod 3) V) (hF : F₁ ≤ F₂) :
    Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {x | IsFlagUnipotent F₁ F₂ x}
  mul_mem' hx hy := isFlagUnipotent_mul hF hx hy
  one_mem' := isFlagUnipotent_one F₁ F₂
  inv_mem' {x} hx := by
    have h3 := pow_three_eq_one_of_isFlagUnipotent hx
    have hinv : x⁻¹ = x * x := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, ← pow_succ, h3]
    change IsFlagUnipotent F₁ F₂ x⁻¹
    rw [hinv]
    exact isFlagUnipotent_mul hF hx hx

theorem mem_flagUnipotentSubgroup {F₁ F₂ : Submodule (ZMod 3) V} {hF : F₁ ≤ F₂}
    {x : V ≃ₗ[ZMod 3] V} : x ∈ flagUnipotentSubgroup F₁ F₂ hF ↔ IsFlagUnipotent F₁ F₂ x :=
  Iff.rfl

theorem isPGroup_flagUnipotentSubgroup (F₁ F₂ : Submodule (ZMod 3) V) (hF : F₁ ≤ F₂) :
    IsPGroup 3 (flagUnipotentSubgroup F₁ F₂ hF) := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one]; exact pow_three_eq_one_of_isFlagUnipotent x.2)⟩

theorem isPGroup_closure_pair_of_mul_eq_zero {t₁ t₂ : V ≃ₗ[ZMod 3] V} {v w : V}
    {f g : Dual (ZMod 3) V} (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g)
    (h0 : f w * g v = 0) : IsPGroup 3 (Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V))) := by
  obtain ⟨F₁, F₂, hF, hu₁, hu₂⟩ : ∃ (F₁ F₂ : Submodule (ZMod 3) V) (hF : F₁ ≤ F₂),
      IsFlagUnipotent F₁ F₂ t₁ ∧ IsFlagUnipotent F₁ F₂ t₂ := by
    rcases mul_eq_zero.mp h0 with hfw | hgv
    ·
      have hle : Submodule.span (ZMod 3) {w} ≤ LinearMap.ker f := by
        rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
        exact hfw
      refine ⟨Submodule.span (ZMod 3) {w}, LinearMap.ker f, hle, ⟨fun y => ?_, fun y hy => ?_,
        fun y hy => ?_⟩, ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩⟩
      · rw [h₁.2.2.2, add_sub_cancel_left, LinearMap.mem_ker, map_smul, h₁.2.2.1, smul_zero]
      · rw [h₁.2.2.2, LinearMap.mem_ker.mp hy, zero_smul, add_zero, sub_self]
        exact Submodule.zero_mem _
      · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [h₁.2.2.2, map_smul, hfw, smul_zero, zero_smul, add_zero]
      · rw [h₂.2.2.2, add_sub_cancel_left]
        exact hle (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
      · rw [h₂.2.2.2, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [h₂.2.2.2, map_smul, h₂.2.2.1, smul_zero, zero_smul, add_zero]
    ·
      have hle : Submodule.span (ZMod 3) {v} ≤ LinearMap.ker g := by
        rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
        exact hgv
      refine ⟨Submodule.span (ZMod 3) {v}, LinearMap.ker g, hle, ⟨fun y => ?_, fun y hy => ?_,
        fun y hy => ?_⟩, ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩⟩
      · rw [h₁.2.2.2, add_sub_cancel_left]
        exact hle (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      · rw [h₁.2.2.2, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
      · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [h₁.2.2.2, map_smul, h₁.2.2.1, smul_zero, zero_smul, add_zero]
      · rw [h₂.2.2.2, add_sub_cancel_left, LinearMap.mem_ker, map_smul, h₂.2.2.1, smul_zero]
      · rw [h₂.2.2.2, LinearMap.mem_ker.mp hy, zero_smul, add_zero, sub_self]
        exact Submodule.zero_mem _
      · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [h₂.2.2.2, map_smul, hgv, smul_zero, zero_smul, add_zero]
  have hle : Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) ≤
      flagUnipotentSubgroup F₁ F₂ hF := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu₁
    · exact hu₂
  exact (isPGroup_flagUnipotentSubgroup F₁ F₂ hF).to_le hle

theorem apply_eq_self_of_map_eq {x : V ≃ₗ[ZMod 3] V} {k : ℕ} (hx : x ^ (3 ^ k) = 1) {u : V}
    (hu : x u ∈ Submodule.span (ZMod 3) {u}) : x u = u := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  have hpow : ∀ n : ℕ, (x ^ n) u = c ^ n • u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ, mul_comm]
  have h1 := hpow (3 ^ k)
  rw [hx, LinearEquiv.coe_one, id] at h1
  have hc3 : ∀ n : ℕ, c ^ (3 ^ n) = c := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_one]
    | succ n ih =>
      rw [pow_succ, pow_mul, ih]
      exact ZMod.pow_card c
  rw [hc3] at h1
  rw [← hc]
  exact h1.symm

theorem mem_pCore_of_isFlagUnipotent (G : Subgroup (V ≃ₗ[ZMod 3] V))
    {F₁ F₂ : Submodule (ZMod 3) V} (hF : F₁ ≤ F₂) (hG₁ : ∀ g ∈ G, ∀ y ∈ F₁, g y ∈ F₁)
    (hG₂ : ∀ g ∈ G, ∀ y ∈ F₂, g y ∈ F₂) {k : G}
    (hk : IsFlagUnipotent F₁ F₂ (k : V ≃ₗ[ZMod 3] V)) : k ∈ CFSG.pCore 3 G := by
  have hG₁' : ∀ g ∈ G, ∀ y ∈ F₁, g⁻¹ y ∈ F₁ := fun g hg y hy => hG₁ g⁻¹ (G.inv_mem hg) y hy
  have hG₂' : ∀ g ∈ G, ∀ y ∈ F₂, g⁻¹ y ∈ F₂ := fun g hg y hy => hG₂ g⁻¹ (G.inv_mem hg) y hy
  set K : Subgroup G := (flagUnipotentSubgroup F₁ F₂ hF).subgroupOf G with hKdef
  have hKn : K.Normal := by
    refine ⟨fun n hn c => ?_⟩
    have hn' : IsFlagUnipotent F₁ F₂ (n : V ≃ₗ[ZMod 3] V) := hn
    change IsFlagUnipotent F₁ F₂ ((c : V ≃ₗ[ZMod 3] V) * n * (c : V ≃ₗ[ZMod 3] V)⁻¹)
    refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
    · have : ((c : V ≃ₗ[ZMod 3] V) * n * (c : V ≃ₗ[ZMod 3] V)⁻¹) y - y =
          (c : V ≃ₗ[ZMod 3] V) ((n : V ≃ₗ[ZMod 3] V) ((c : V ≃ₗ[ZMod 3] V)⁻¹ y) -
            (c : V ≃ₗ[ZMod 3] V)⁻¹ y) := by
        rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        congr 1
        change y = c.1 (c.1.symm y)
        rw [LinearEquiv.apply_symm_apply]
      rw [this]
      exact hG₂ _ c.2 _ (hn'.1 _)
    · have : ((c : V ≃ₗ[ZMod 3] V) * n * (c : V ≃ₗ[ZMod 3] V)⁻¹) y - y =
          (c : V ≃ₗ[ZMod 3] V) ((n : V ≃ₗ[ZMod 3] V) ((c : V ≃ₗ[ZMod 3] V)⁻¹ y) -
            (c : V ≃ₗ[ZMod 3] V)⁻¹ y) := by
        rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        congr 1
        change y = c.1 (c.1.symm y)
        rw [LinearEquiv.apply_symm_apply]
      rw [this]
      exact hG₁ _ c.2 _ (hn'.2.1 _ (hG₂' _ c.2 y hy))
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hn'.2.2 _ (hG₁' _ c.2 y hy)]
      change c.1 (c.1.symm y) = y
      rw [LinearEquiv.apply_symm_apply]
  have hKp : IsPGroup 3 K :=
    (isPGroup_flagUnipotentSubgroup F₁ F₂ hF).comap_of_injective G.subtype Subtype.val_injective
  have hle : K ≤ CFSG.pCore 3 G := le_sSup ⟨hKn, hKp⟩
  exact hle hk

end ThreeElements

section Irreducible

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

theorem exists_eq_span_of_finrank_eq_one {W : Submodule (ZMod 3) V}
    (hW : finrank (ZMod 3) W = 1) : ∃ y : V, y ≠ 0 ∧ W = Submodule.span (ZMod 3) {y} := by
  obtain ⟨y, hy0, hy⟩ := finrank_eq_one_iff'.mp hW
  refine ⟨y, fun h => hy0 (Subtype.ext h), le_antisymm (fun z hz => ?_) ?_⟩
  · obtain ⟨c, hc⟩ := hy ⟨z, hz⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact y.2

theorem det_eq_one_mem_of_irreducible (hV : finrank (ZMod 3) V = 3)
    (G : Subgroup (V ≃ₗ[ZMod 3] V))
    (hirr : ∀ W : Submodule (ZMod 3) V, (∀ g ∈ G, ∀ x ∈ W, g x ∈ W) → W = ⊥ ∨ W = ⊤)
    {r : V ≃ₗ[ZMod 3] V} (hrG : r ∈ G) {v : V} {f : Dual (ZMod 3) V}
    (hr : IsTransvectionWith r v f) :
    ∀ g : V ≃ₗ[ZMod 3] V, LinearMap.det (g : V →ₗ[ZMod 3] V) = 1 → g ∈ G := by
  set S : Set (V ≃ₗ[ZMod 3] V) := {t | ∃ g ∈ G, t = g * r * g⁻¹} with hSdef
  set T : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure S with hTdef
  have hrT : r ∈ T := Subgroup.subset_closure ⟨1, G.one_mem, by group⟩
  have hTG : T ≤ G := by
    rw [hTdef, Subgroup.closure_le]
    rintro t ⟨g, hg, rfl⟩
    exact G.mul_mem (G.mul_mem hg hrG) (G.inv_mem hg)
  have hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f := by
    rintro t ⟨g, -, rfl⟩
    exact ⟨_, _, hr.conj g⟩
  have hTn : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨h, hh, rfl⟩ := ht
      exact Subgroup.subset_closure ⟨g * h, G.mul_mem hg hh, by group⟩
    | one => simp
    | mul a b _ _ iha ihb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact T.mul_mem iha ihb
    | inv a _ iha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact T.inv_mem iha
  have hdet : ∀ t ∈ T, LinearMap.det (t : V →ₗ[ZMod 3] V) = 1 := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨v', f', h'⟩ := hS t ht
      exact det_eq_one_of_isTransvectionWith h'
    | one => simp
    | mul a b _ _ iha ihb =>
      rw [LinearEquiv.coe_toLinearMap_mul, map_mul, iha, ihb, one_mul]
    | inv a _ iha =>
      have h1 : LinearMap.det ((a⁻¹ * a : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) = 1 := by
        rw [inv_mul_cancel]; simp
      rw [LinearEquiv.coe_toLinearMap_mul, map_mul, iha, mul_one] at h1
      exact h1
  have htrans : ∀ W : Submodule (ZMod 3) V, (∀ t ∈ T, ∀ x ∈ W, t x ∈ W) → ∀ g ∈ G,
      ∀ t ∈ T, ∀ x ∈ W.map (g : V →ₗ[ZMod 3] V), t x ∈ W.map (g : V →ₗ[ZMod 3] V) := by
    intro W hW g hg t ht x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have hc : g⁻¹ * t * g ∈ T := by
      have := hTn g⁻¹ (G.inv_mem hg) t ht
      rwa [inv_inv] at this
    refine Submodule.mem_map.mpr ⟨(g⁻¹ * t * g) y, hW _ hc y hy, ?_⟩
    change g ((g⁻¹ * t * g) y) = t (g y)
    rw [← LinearEquiv.mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      LinearEquiv.mul_apply]
  have hline : ∀ W : Submodule (ZMod 3) V, (∀ t ∈ T, ∀ x ∈ W, t x ∈ W) →
      finrank (ZMod 3) W = 1 → ∀ x ∈ W, r x = x := by
    intro W hW h1 x hx
    obtain ⟨y, -, rfl⟩ := exists_eq_span_of_finrank_eq_one h1
    have hry : r y = y := apply_eq_self_of_isTransvectionWith_of_mem hr
      (hW r hrT y (Submodule.mem_span_singleton_self y))
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hry]
  have hnoline : ∀ W : Submodule (ZMod 3) V, (∀ t ∈ T, ∀ x ∈ W, t x ∈ W) →
      finrank (ZMod 3) W ≠ 1 := by
    intro W hW h1
    set M : Submodule (ZMod 3) V := ⨆ g ∈ G, W.map (g : V →ₗ[ZMod 3] V) with hMdef
    have hMG : ∀ g ∈ G, ∀ x ∈ M, g x ∈ M := by
      intro g hg x hx
      have hle : M ≤ M.comap (g : V →ₗ[ZMod 3] V) := by
        refine iSup₂_le fun g' hg' => ?_
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
        have : (g : V →ₗ[ZMod 3] V) ((g' : V →ₗ[ZMod 3] V) z) =
            ((g * g' : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) z := rfl
        change (g : V →ₗ[ZMod 3] V) ((g' : V →ₗ[ZMod 3] V) z) ∈ M
        rw [this]
        exact (le_iSup₂_of_le (g * g') (G.mul_mem hg hg') le_rfl :
          W.map ((g * g' : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) ≤ M)
          (Submodule.mem_map_of_mem hz)
      exact hle hx
    have hWM : W ≤ M := by
      have : W.map ((1 : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) ≤ M :=
        le_iSup₂_of_le (1 : V ≃ₗ[ZMod 3] V) G.one_mem le_rfl
      simpa using this
    have hM : M = ⊤ := by
      rcases hirr M hMG with h | h
      · exfalso
        have hW0 : W = ⊥ := le_bot_iff.mp (h ▸ hWM)
        rw [hW0, finrank_bot] at h1
        exact absurd h1 (by norm_num)
      · exact h
    have hfix : M ≤ LinearMap.ker ((r : V →ₗ[ZMod 3] V) - LinearMap.id) := by
      refine iSup₂_le fun g hg => ?_
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      refine hline _ (htrans W hW g hg) ?_ x hx
      rw [LinearEquiv.finrank_map_eq]
      exact h1
    apply ne_one_of_isTransvectionWith hr
    ext x
    have hx := hfix (hM ▸ Submodule.mem_top : x ∈ M)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
    exact hx
  have hTirr : ∀ W : Submodule (ZMod 3) V, (∀ t ∈ T, ∀ x ∈ W, t x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hne
    rw [not_or] at hne
    have hpos : 0 < finrank (ZMod 3) W :=
      Nat.pos_of_ne_zero fun h => hne.1 (Submodule.finrank_eq_zero.mp h)
    have hlt : finrank (ZMod 3) W < 3 := lt_of_lt_of_eq (Submodule.finrank_lt hne.2) hV
    have h2 : finrank (ZMod 3) W = 2 := by
      have := hnoline W hW
      omega
    obtain ⟨g, hg, x, hxW, hgx⟩ : ∃ g ∈ G, ∃ x ∈ W, g x ∉ W := by
      by_contra! h
      rcases hirr W h with h' | h'
      · exact hne.1 h'
      · exact hne.2 h'
    set W' := W.map (g : V →ₗ[ZMod 3] V) with hW'def
    have hW'T := htrans W hW g hg
    have hW'2 : finrank (ZMod 3) W' = 2 := by rw [hW'def, LinearEquiv.finrank_map_eq, h2]
    have hint := Submodule.finrank_sup_add_finrank_inf_eq W W'
    have hsup : finrank (ZMod 3) ↥(W ⊔ W') ≤ 3 := (Submodule.finrank_le _).trans hV.le
    have hne' : W ⊓ W' ≠ W := by
      intro h
      have hle : W ≤ W' := h ▸ inf_le_right
      have heq : W = W' := Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, hW'2])
      apply hgx
      rw [heq]
      exact Submodule.mem_map_of_mem hxW
    have hlt' : finrank (ZMod 3) ↥(W ⊓ W') < 2 := by
      have hle : W ⊓ W' ≤ W := inf_le_left
      have := Submodule.finrank_mono hle
      rcases this.lt_or_eq with h | h
      · omega
      · exact absurd (Submodule.eq_of_le_of_finrank_eq hle h) hne'
    have hinvT : ∀ t ∈ T, ∀ y ∈ W ⊓ W', t y ∈ W ⊓ W' := fun t ht y hy =>
      Submodule.mem_inf.mpr ⟨hW t ht y (Submodule.mem_inf.mp hy).1,
        hW'T t ht y (Submodule.mem_inf.mp hy).2⟩
    exact hnoline (W ⊓ W') hinvT (by omega)
  have hTSL := prime_three_space_irreducible_transvection_generation hV T hdet hTirr ⟨S, hS, rfl⟩
  intro g hg
  exact hTG ((hTSL g).mpr hg)

end Irreducible

section Pair

open scoped MatrixGroups

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {t₁ t₂ : V ≃ₗ[ZMod 3] V} {v w : V} {f g : Dual (ZMod 3) V}

omit [FiniteDimensional (ZMod 3) V] in
theorem linearIndependent_pair_of_transvections (h₁ : IsTransvectionWith t₁ v f)
    (hfw : f w ≠ 0) (hv : v ≠ 0) : LinearIndependent (ZMod 3) ![v, w] :=
  LinearIndependent.pair_iff.mpr fun s t hst => by
    have hf := congrArg f hst
    rw [map_add, map_smul, map_smul, h₁.2.2.1, smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
      map_zero] at hf
    have ht : t = 0 := (mul_eq_zero.mp hf).resolve_right hfw
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hv, ht⟩

omit [FiniteDimensional (ZMod 3) V] in
theorem mapsTo_of_isTransvectionWith {t : V ≃ₗ[ZMod 3] V} {c : V} {e : Dual (ZMod 3) V}
    (ht : IsTransvectionWith t c e) {P : Submodule (ZMod 3) V} (hc : c ∈ P) :
    ∀ y ∈ P, t y ∈ P := fun y hy => by
  rw [ht.2.2.2]
  exact P.add_mem hy (P.smul_mem _ hc)

theorem map_eq_of_mapsTo {x : V ≃ₗ[ZMod 3] V} {P : Submodule (ZMod 3) V}
    (hx : ∀ y ∈ P, x y ∈ P) : P.map (x : V →ₗ[ZMod 3] V) = P :=
  Submodule.eq_of_le_of_finrank_eq (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
      exact hx y hy)
    (LinearEquiv.finrank_map_eq x P)

theorem inv_mapsTo {x : V ≃ₗ[ZMod 3] V} {P : Submodule (ZMod 3) V}
    (hx : ∀ y ∈ P, x y ∈ P) : ∀ y ∈ P, x⁻¹ y ∈ P := fun y hy => by
  rw [← map_eq_of_mapsTo hx] at hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  change x.symm (x z) ∈ P
  rw [LinearEquiv.symm_apply_apply]
  exact hz

omit [FiniteDimensional (ZMod 3) V] in
theorem eq_of_eqOn_isCompl {x y : V ≃ₗ[ZMod 3] V} {P L : Submodule (ZMod 3) V}
    (hPL : IsCompl P L) (hP : ∀ p ∈ P, x p = y p) (hL : ∀ l ∈ L, x l = y l) : x = y := by
  ext z
  have hz : z ∈ P ⊔ L := by rw [hPL.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add, map_add, hP p hp, hL l hl]

section Hyp

variable (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g) (hfw : f w ≠ 0)
  (hgv : g v ≠ 0)
include h₁ h₂

theorem pair_mapsTo_and_fix {x : V ≃ₗ[ZMod 3] V}
    (hx : x ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V))) :
    (∀ y ∈ Submodule.span (ZMod 3) {v, w}, x y ∈ Submodule.span (ZMod 3) {v, w}) ∧
      ∀ l ∈ LinearMap.ker f ⊓ LinearMap.ker g, x l = l := by
  have hvP : v ∈ Submodule.span (ZMod 3) {v, w} := Submodule.subset_span (by simp)
  have hwP : w ∈ Submodule.span (ZMod 3) {v, w} := Submodule.subset_span (by simp)
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · refine ⟨mapsTo_of_isTransvectionWith h₁ hvP, fun l hl => ?_⟩
      rw [h₁.2.2.2, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1, zero_smul, add_zero]
    · refine ⟨mapsTo_of_isTransvectionWith h₂ hwP, fun l hl => ?_⟩
      rw [h₂.2.2.2, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).2, zero_smul, add_zero]
  | one => exact ⟨fun y hy => hy, fun l _ => rfl⟩
  | mul a b _ _ iha ihb =>
    exact ⟨fun y hy => iha.1 _ (ihb.1 y hy), fun l hl => by
      rw [LinearEquiv.mul_apply, ihb.2 l hl, iha.2 l hl]⟩
  | inv a _ iha =>
    refine ⟨inv_mapsTo iha.1, fun l hl => ?_⟩
    change a.symm l = l
    rw [LinearEquiv.symm_apply_eq, iha.2 l hl]

theorem det_restrict_pair {x : V ≃ₗ[ZMod 3] V}
    (hx : x ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V))) :
    LinearMap.det ((x : V →ₗ[ZMod 3] V).restrict (pair_mapsTo_and_fix h₁ h₂ hx).1) = 1 := by
  set P := Submodule.span (ZMod 3) {v, w}
  have hvP : v ∈ P := Submodule.subset_span (by simp)
  have hwP : w ∈ P := Submodule.subset_span (by simp)
  have htr : ∀ (t : V ≃ₗ[ZMod 3] V) (c : V) (e : Dual (ZMod 3) V)
      (ht : IsTransvectionWith t c e) (hc : c ∈ P),
      LinearMap.det ((t : V →ₗ[ZMod 3] V).restrict (mapsTo_of_isTransvectionWith ht hc)) = 1 := by
    intro t c e ht hc
    have : (t : V →ₗ[ZMod 3] V).restrict (mapsTo_of_isTransvectionWith ht hc) =
        LinearMap.transvection (e.comp P.subtype) ⟨c, hc⟩ := by
      ext y
      simp [LinearMap.restrict_apply, ht.2.2.2, LinearMap.transvection.apply]
    rw [this, LinearMap.transvection.det]
    simp [ht.2.2.1]
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact htr _ _ _ h₁ hvP
    · exact htr _ _ _ h₂ hwP
  | one =>
    convert LinearMap.det_id (A := ZMod 3) (M := P) using 2
    ext y
    rfl
  | mul a b ha hb iha ihb =>
    have hmul : ((a * b : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict
        (pair_mapsTo_and_fix h₁ h₂ (Subgroup.mul_mem _ ha hb)).1 =
        (a : V →ₗ[ZMod 3] V).restrict (pair_mapsTo_and_fix h₁ h₂ ha).1 *
          (b : V →ₗ[ZMod 3] V).restrict (pair_mapsTo_and_fix h₁ h₂ hb).1 := by
      ext y; rfl
    rw [hmul, map_mul, iha, ihb, one_mul]
  | inv a ha iha =>
    have hmul : (a : V →ₗ[ZMod 3] V).restrict (pair_mapsTo_and_fix h₁ h₂ ha).1 *
        ((a⁻¹ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V).restrict
          (pair_mapsTo_and_fix h₁ h₂ (Subgroup.inv_mem _ ha)).1 = 1 := by
      ext y
      change a (a.symm (y : V)) = y
      rw [LinearEquiv.apply_symm_apply]
    have := congrArg LinearMap.det hmul
    rw [map_mul, iha, one_mul, map_one] at this
    exact this

omit [FiniteDimensional (ZMod 3) V] in
include hfw hgv in
theorem mem_pair_of {y : V ≃ₗ[ZMod 3] V}
    (hyP : ∀ p ∈ Submodule.span (ZMod 3) {v, w}, y p ∈ Submodule.span (ZMod 3) {v, w})
    (hdet : LinearMap.det ((y : V →ₗ[ZMod 3] V).restrict hyP) = 1)
    (hyL : ∀ l ∈ LinearMap.ker f ⊓ LinearMap.ker g, y l = l) :
    y ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) := by
  obtain ⟨x, hx, hxP, hxL⟩ := exists_mem_of_det_eq_one
    (H := Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V))) h₁ h₂
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hfw hgv
    ((y : V →ₗ[ZMod 3] V).restrict hyP) hdet
  have hxy : x = y :=
    eq_of_eqOn_isCompl (isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv)
      (fun p hp => hxP ⟨p, hp⟩) (fun l hl => (hxL l hl).trans (hyL l hl).symm)
  exact hxy ▸ hx

include hfw hgv in
theorem nonempty_pair_mulEquiv :
    Nonempty (Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) ≃* SL(2, ZMod 3)) := by
  set X := Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) with hXdef
  set P := Submodule.span (ZMod 3) {v, w}
  have hvw : LinearIndependent (ZMod 3) ![v, w] :=
    linearIndependent_pair_of_transvections h₁ hfw h₁.1
  set B := pairBasis hvw with hBdef
  let ρ : X →* SL(2, ZMod 3) :=
    { toFun := fun x => ⟨LinearMap.toMatrix B B
          ((x : V →ₗ[ZMod 3] V).restrict (pair_mapsTo_and_fix h₁ h₂ x.2).1), by
        rw [LinearMap.det_toMatrix]
        exact det_restrict_pair h₁ h₂ x.2⟩
      map_one' := by
        apply Subtype.ext
        change LinearMap.toMatrix B B _ = 1
        convert LinearMap.toMatrix_id B using 2
        ext y
        rfl
      map_mul' := fun x y => by
        apply Subtype.ext
        change LinearMap.toMatrix B B _ = LinearMap.toMatrix B B _ * LinearMap.toMatrix B B _
        rw [← LinearMap.toMatrix_comp]
        rfl }
  have hρ : ∀ x : X, ((ρ x : SL(2, ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      LinearMap.toMatrix B B
        ((x : V →ₗ[ZMod 3] V).restrict (pair_mapsTo_and_fix h₁ h₂ x.2).1) := fun x => rfl
  refine ⟨MulEquiv.ofBijective ρ ⟨fun x y hxy => ?_, fun A => ?_⟩⟩
  · have h := congrArg (fun A : SL(2, ZMod 3) => (A : Matrix (Fin 2) (Fin 2) (ZMod 3))) hxy
    simp only [hρ] at h
    have hres := (LinearMap.toMatrix B B).injective h
    apply Subtype.ext
    refine eq_of_eqOn_isCompl (isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv)
      (fun p hp => ?_) (fun l hl => ?_)
    · have := congrArg (fun φ : P →ₗ[ZMod 3] P => (φ ⟨p, hp⟩ : V)) hres
      exact this
    · rw [(pair_mapsTo_and_fix h₁ h₂ x.2).2 l hl, (pair_mapsTo_and_fix h₁ h₂ y.2).2 l hl]
  · set φ : P →ₗ[ZMod 3] P := Matrix.toLin B B (A : Matrix (Fin 2) (Fin 2) (ZMod 3))
    have hφ : LinearMap.det φ = 1 := by rw [LinearMap.det_toLin]; exact A.2
    obtain ⟨y, hy, hyP, hyL⟩ := exists_mem_of_det_eq_one (H := X) h₁ h₂
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hfw hgv φ hφ
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    rw [hρ]
    have hres : (y : V →ₗ[ZMod 3] V).restrict (pair_mapsTo_and_fix h₁ h₂ hy).1 = φ := by
      ext u
      exact hyP u
    change LinearMap.toMatrix B B ((y : V →ₗ[ZMod 3] V).restrict
      (pair_mapsTo_and_fix h₁ h₂ hy).1) = _
    rw [hres, LinearMap.toMatrix_toLin]

end Hyp

end Pair

end CFSG.RankThree.PartTwo.Sec3
