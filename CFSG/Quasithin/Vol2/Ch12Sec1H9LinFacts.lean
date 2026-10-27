module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9Lin

public section

namespace CFSG.Quasithin.H13.H9Lin

open CFSG.Open CFSG.Quasithin.E3 H9Coord

variable {W : Type} [CommGroup W]

@[expose] def commHom (s : MulAut W) : W →* W where
  toFun w := s w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commHom_apply (s : MulAut W) (w : W) : commHom s w = s w * w⁻¹ := rfl

@[expose] def commOn (X : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup W :=
  Subgroup.closure {w | ∃ x ∈ X, ∃ u ∈ U, w = x u * u⁻¹}

theorem mem_commOn_of {X : Subgroup (MulAut W)} {U : Subgroup W} {x : MulAut W} (hx : x ∈ X)
    {u : W} (hu : u ∈ U) : x u * u⁻¹ ∈ commOn X U :=
  Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩

theorem commOn_le {X : Subgroup (MulAut W)} {U : Subgroup W} (hX : X ≤ stabV U) :
    commOn X U ≤ U := by
  rw [commOn, Subgroup.closure_le]
  rintro _ ⟨x, hx, u, hu, rfl⟩
  exact U.mul_mem ((hX hx u).mp hu) (U.inv_mem hu)

theorem commOn_le_commV (X : Subgroup (MulAut W)) (U : Subgroup W) : commOn X U ≤ commV X := by
  rw [commOn, Subgroup.closure_le]
  rintro _ ⟨x, hx, u, -, rfl⟩
  exact Subgroup.subset_closure ⟨x, hx, u, rfl⟩

theorem commOn_eq_bot {X : Subgroup (MulAut W)} {U : Subgroup W} (h : commOn X U = ⊥) :
    ∀ x ∈ X, ∀ u ∈ U, x u = u := fun x hx u hu => by
  have := mem_commOn_of hx hu
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at this
  exact this

theorem zpowers_eq_of_sq {s : MulAut W} (hs : s ^ 2 = 1) {x : MulAut W}
    (hx : x ∈ Subgroup.zpowers s) : x = 1 ∨ x = s := by
  obtain ⟨k, rfl⟩ := hx
  have h2 : s ^ (2 : ℤ) = 1 := by exact_mod_cast hs
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · left
    show s ^ (2 * j) = 1
    rw [zpow_mul, h2, one_zpow]
  · right
    show s ^ (2 * j + 1) = s
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem commOn_zpowers {s : MulAut W} (hs : s ^ 2 = 1) (U : Subgroup W) :
    commOn (Subgroup.zpowers s) U = U.map (commHom s) := by
  apply le_antisymm
  · rw [commOn, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    rcases zpowers_eq_of_sq hs hx with rfl | rfl
    · rw [MulAut.one_apply, mul_inv_cancel]
      exact Subgroup.one_mem _
    · exact ⟨u, hu, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact mem_commOn_of (Subgroup.mem_zpowers s) hu

theorem card_fix_mul_card_commOn [Finite W] {s : MulAut W} (hs : s ^ 2 = 1) (U : Subgroup W) :
    Nat.card ↥(fixV (Subgroup.zpowers s) ⊓ U) * Nat.card (commOn (Subgroup.zpowers s) U) =
      Nat.card U := by
  let f : ↥U →* W := (commHom s).comp U.subtype
  have hker : Nat.card f.ker = Nat.card ↥(fixV (Subgroup.zpowers s) ⊓ U) := Nat.card_congr
    { toFun := fun u => ⟨u.1, Subgroup.mem_inf.mpr ⟨H.mem_fixV_zpowers_iff.mpr (by
        have := u.2
        rw [MonoidHom.mem_ker] at this
        exact mul_inv_eq_one.mp this), u.1.2⟩⟩
      invFun := fun w => ⟨⟨w.1, (Subgroup.mem_inf.mp w.2).2⟩, by
        rw [MonoidHom.mem_ker]
        show s w.1 * (w.1 : W)⁻¹ = 1
        rw [H.mem_fixV_zpowers_iff.mp (Subgroup.mem_inf.mp w.2).1, mul_inv_cancel]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hrange : f.range = U.map (commHom s) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hker, commOn_zpowers hs, ← hrange, ← Subgroup.index_ker f, Subgroup.card_mul_index]

theorem commOn_le_fix (hexp : ∀ w : W, w ^ 2 = 1) {s : MulAut W} (hs : s ^ 2 = 1)
    (U : Subgroup W) : commOn (Subgroup.zpowers s) U ≤ fixV (Subgroup.zpowers s) := by
  rw [commOn_zpowers hs]
  rintro _ ⟨u, -, rfl⟩
  rw [H.mem_fixV_zpowers_iff, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, ← pow_two, hs,
    MulAut.one_apply]
  have h1 := hexp (s u * u⁻¹)
  rw [pow_two, mul_eq_one_iff_eq_inv] at h1
  rw [h1, mul_inv_rev, inv_inv]

theorem card_le_of_eval_injective [Finite W] {X : Subgroup (MulAut W)} {K : Subgroup W} {v₀ : W}
    (hinj : ∀ x ∈ X, x v₀ = v₀ → x = 1) (hK : ∀ x ∈ X, x v₀ * v₀⁻¹ ∈ K) :
    Nat.card X ≤ Nat.card K := by
  refine Nat.card_le_card_of_injective (fun x => ⟨(x : MulAut W) v₀ * v₀⁻¹, hK x x.2⟩) ?_
  intro x y h
  have h1 : (x : MulAut W) v₀ = (y : MulAut W) v₀ := by
    have := congrArg Subtype.val h
    simpa using this
  have h2 : ((y : MulAut W)⁻¹ * x) v₀ = v₀ := by
    rw [MulAut.mul_apply, h1, MulAut.inv_apply_self]
  have h3 := hinj _ (X.mul_mem (X.inv_mem y.2) x.2) h2
  rw [inv_mul_eq_one] at h3
  exact Subtype.ext h3.symm

theorem mem_or_mul_mem {H U : Subgroup W} (h2 : (H.subgroupOf U).index = 2)
    {v₀ : W} (hv₀ : v₀ ∈ U) (hv₀H : v₀ ∉ H) {w : W} (hw : w ∈ U) : w ∈ H ∨ w * v₀⁻¹ ∈ H := by
  by_cases hwH : w ∈ H
  · exact Or.inl hwH
  · right
    have h := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨w, hw⟩ : ↥U)) (b := ⟨v₀, hv₀⟩⁻¹)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h.mpr ⟨fun h1 => absurd h1 hwH, fun h1 => absurd (by simpa using H.inv_mem h1) hv₀H⟩

variable {n : ℕ} {M L T : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}

theorem exp_of_hyp (hyp : H9Hyp n M L T W₁ W₂) (w : W) : w⁻¹ = w := by
  have h := hyp.exp w
  rw [pow_two, mul_eq_one_iff_inv_eq] at h
  exact h

theorem exists_decomp (hyp : H9Hyp n M L T W₁ W₂) (w : W) :
    ∃ a ∈ W₁, ∃ c ∈ W₂, w = a * c := by
  have hw : w ∈ W₁ ⊔ W₂ := by rw [hyp.sup]; exact Subgroup.mem_top w
  obtain ⟨a, ha, c, hc, h⟩ := Subgroup.mem_sup.mp hw
  exact ⟨a, ha, c, hc, h.symm⟩

theorem decomp_unique (hyp : H9Hyp n M L T W₁ W₂) {a a' c c' : W} (ha : a ∈ W₁) (ha' : a' ∈ W₁)
    (hc : c ∈ W₂) (hc' : c' ∈ W₂) (h : a * c = a' * c') : a = a' ∧ c = c' := by
  have h1 : a'⁻¹ * a = c' * c⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * c) * c⁻¹ := by group
      _ = c' * c⁻¹ := by rw [h]; group
  have h2 : a'⁻¹ * a ∈ W₁ ⊓ W₂ :=
    ⟨W₁.mul_mem (W₁.inv_mem ha') ha, h1 ▸ W₂.mul_mem hc' (W₂.inv_mem hc)⟩
  rw [hyp.inf, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

theorem map_W₂_of_not_mem (hyp : H9Hyp n M L T W₁ W₂) {m : MulAut W} (hm : m ∈ M) (hmL : m ∉ L)
    (hm2 : m ^ 2 = 1) {c : W} (hc : c ∈ W₂) : m c ∈ W₁ := by
  have h := H9Conj.map_W₁_of_not_mem hyp hm hmL
  rw [← h] at hc
  obtain ⟨a, ha, rfl⟩ := hc
  rw [MulEquiv.coe_toMonoidHom, ← MulAut.mul_apply, ← pow_two, hm2, MulAut.one_apply]
  exact ha

theorem card_fixV_of_not_mem [Finite W] (hyp : H9Hyp n M L T W₁ W₂) {m : MulAut W} (hm : m ∈ M)
    (hmL : m ∉ L) (hm2 : m ^ 2 = 1) : Nat.card (fixV (Subgroup.zpowers m)) = Nat.card W₁ := by
  have hW₁₂ : ∀ a ∈ W₁, m a ∈ W₂ := fun a ha => by
    rw [← H9Conj.map_W₁_of_not_mem hyp hm hmL]
    exact Subgroup.mem_map_of_mem _ ha
  have hmm : ∀ w, m (m w) = w := fun w => by
    rw [← MulAut.mul_apply, ← pow_two, hm2, MulAut.one_apply]
  symm
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1 * m a.1, H.mem_fixV_zpowers_iff.mpr (by
        rw [map_mul, hmm, mul_comm])⟩
      invFun := fun w => ⟨(exists_decomp hyp w.1).choose,
        (exists_decomp hyp w.1).choose_spec.1⟩
      left_inv := fun a => Subtype.ext ?_
      right_inv := fun w => Subtype.ext ?_ }
  · obtain ⟨ha, c, hc, h⟩ := (exists_decomp hyp (a.1 * m a.1)).choose_spec
    exact (decomp_unique hyp ha a.2 hc (hW₁₂ _ a.2) h.symm).1
  · obtain ⟨ha, c, hc, h⟩ := (exists_decomp hyp w.1).choose_spec
    set a := (exists_decomp hyp w.1).choose
    have hw := H.mem_fixV_zpowers_iff.mp w.2
    rw [h, map_mul] at hw
    have h1 := decomp_unique hyp (map_W₂_of_not_mem hyp hm hmL hm2 hc) ha (hW₁₂ a ha) hc
      (by rw [mul_comm]; exact hw)
    show a * m a = w.1
    rw [h, h1.2]

variable {β : W → W → ZMod 2}

theorem pairing_one_left (hβ : IsDualH9 L W₁ W₂ β) {c : W} (hc : c ∈ W₂) : β 1 c = 0 := by
  have h := hβ.1 1 W₁.one_mem 1 W₁.one_mem c hc
  rw [mul_one] at h
  have h2 : β 1 c + β 1 c = 0 := CharTwo.add_self_eq_zero _
  rw [← h] at h2
  exact h2

theorem pairing_one_right (hβ : IsDualH9 L W₁ W₂ β) {a : W} (ha : a ∈ W₁) : β a 1 = 0 := by
  have h := hβ.2.1 a ha 1 W₂.one_mem 1 W₂.one_mem
  rw [mul_one] at h
  have h2 : β a 1 + β a 1 = 0 := CharTwo.add_self_eq_zero _
  rw [← h] at h2
  exact h2

theorem mem_fixV_iff₂ (hyp : H9Hyp n M L T W₁ W₂) (hβ : IsDualH9 L W₁ W₂ β)
    {X : Subgroup (MulAut W)} (hXL : X ≤ L) {c : W} (hc : c ∈ W₂) :
    c ∈ fixV X ↔ ∀ g ∈ commOn X W₁, β g c = 0 := by
  have hX₁ : X ≤ stabV W₁ := hXL.trans hyp.inv₁
  have hX₂ : X ≤ stabV W₂ := hXL.trans hyp.inv₂
  constructor
  · intro hfix g hg
    have key : ∀ g ∈ commOn X W₁, g ∈ W₁ ∧ β g c = 0 := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨x, hx, u, hu, rfl⟩ := hg
        have hxu : x u ∈ W₁ := (hX₁ hx u).mp hu
        refine ⟨W₁.mul_mem hxu (W₁.inv_mem hu), ?_⟩
        rw [hβ.1 _ hxu _ (W₁.inv_mem hu) c hc, exp_of_hyp hyp u]
        have h1 := hβ.2.2.2.2 x (hXL hx) u hu c hc
        rw [hfix x hx] at h1
        rw [h1]
        exact CharTwo.add_self_eq_zero _
      | one => exact ⟨W₁.one_mem, pairing_one_left hβ hc⟩
      | mul g h _ _ hg hh =>
        refine ⟨W₁.mul_mem hg.1 hh.1, ?_⟩
        rw [hβ.1 _ hg.1 _ hh.1 c hc, hg.2, hh.2, add_zero]
      | inv g _ hg =>
        rw [exp_of_hyp hyp g]
        exact hg
    exact (key g hg).2
  · intro h x hx
    by_contra hne
    have hc' : x c * c⁻¹ ∈ W₂ := W₂.mul_mem ((hX₂ hx c).mp hc) (W₂.inv_mem hc)
    obtain ⟨a, ha, hac⟩ := hβ.2.2.2.1 _ hc' (fun h1 => hne (mul_inv_eq_one.mp h1))
    have hxa : x⁻¹ a ∈ W₁ := (hX₁ (X.inv_mem hx) a).mp ha
    have h1 : β a (x c) = β (x⁻¹ a) c := by
      have := hβ.2.2.2.2 x (hXL hx) (x⁻¹ a) hxa c hc
      rwa [MulAut.apply_inv_self] at this
    have h2 := h _ (mem_commOn_of (X.inv_mem hx) ha)
    rw [hβ.2.1 a ha _ ((hX₂ hx c).mp hc) _ (W₂.inv_mem hc), exp_of_hyp hyp c, h1] at hac
    rw [hβ.1 _ hxa _ (W₁.inv_mem ha) c hc, exp_of_hyp hyp a] at h2
    rw [h2] at hac
    exact zero_ne_one hac

theorem mem_fixV_iff₁ (hyp : H9Hyp n M L T W₁ W₂) (hβ : IsDualH9 L W₁ W₂ β)
    {X : Subgroup (MulAut W)} (hXL : X ≤ L) {a : W} (ha : a ∈ W₁) :
    a ∈ fixV X ↔ ∀ g ∈ commOn X W₂, β a g = 0 := by
  have hX₁ : X ≤ stabV W₁ := hXL.trans hyp.inv₁
  have hX₂ : X ≤ stabV W₂ := hXL.trans hyp.inv₂
  constructor
  · intro hfix g hg
    have key : ∀ g ∈ commOn X W₂, g ∈ W₂ ∧ β a g = 0 := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨x, hx, u, hu, rfl⟩ := hg
        have hxu : x u ∈ W₂ := (hX₂ hx u).mp hu
        refine ⟨W₂.mul_mem hxu (W₂.inv_mem hu), ?_⟩
        rw [hβ.2.1 a ha _ hxu _ (W₂.inv_mem hu), exp_of_hyp hyp u]
        have h1 := hβ.2.2.2.2 x (hXL hx) a ha u hu
        rw [hfix x hx] at h1
        rw [h1]
        exact CharTwo.add_self_eq_zero _
      | one => exact ⟨W₂.one_mem, pairing_one_right hβ ha⟩
      | mul g h _ _ hg hh =>
        refine ⟨W₂.mul_mem hg.1 hh.1, ?_⟩
        rw [hβ.2.1 a ha _ hg.1 _ hh.1, hg.2, hh.2, add_zero]
      | inv g _ hg =>
        rw [exp_of_hyp hyp g]
        exact hg
    exact (key g hg).2
  · intro h x hx
    by_contra hne
    have ha' : x a * a⁻¹ ∈ W₁ := W₁.mul_mem ((hX₁ hx a).mp ha) (W₁.inv_mem ha)
    obtain ⟨c, hc, hac⟩ := hβ.2.2.1 _ ha' (fun h1 => hne (mul_inv_eq_one.mp h1))
    have hxc : x⁻¹ c ∈ W₂ := (hX₂ (X.inv_mem hx) c).mp hc
    have h1 : β (x a) c = β a (x⁻¹ c) := by
      have := hβ.2.2.2.2 x (hXL hx) a ha (x⁻¹ c) hxc
      rwa [MulAut.apply_inv_self] at this
    have h2 := h _ (mem_commOn_of (X.inv_mem hx) hc)
    rw [hβ.1 _ ((hX₁ hx a).mp ha) _ (W₁.inv_mem ha) c hc, exp_of_hyp hyp a, h1] at hac
    rw [hβ.2.1 a ha _ hxc _ (W₂.inv_mem hc), exp_of_hyp hyp c] at h2
    rw [h2] at hac
    exact zero_ne_one hac

theorem card_fix₂_mul [Finite W] (hyp : H9Hyp n M L T W₁ W₂) (hβ : IsDualH9 L W₁ W₂ β)
    (hcard : ∀ U : Subgroup W, U ≤ W₁ →
      Nat.card U * Nat.card {c : W // c ∈ W₂ ∧ ∀ u ∈ U, β u c = 0} = 2 ^ n)
    {X : Subgroup (MulAut W)} (hXL : X ≤ L) :
    Nat.card ↥(fixV X ⊓ W₂) * Nat.card (commOn X W₁) = 2 ^ n := by
  rw [mul_comm, ← hcard _ (commOn_le (hXL.trans hyp.inv₁))]
  congr 1
  exact Nat.card_congr
    { toFun := fun c => ⟨c.1, (Subgroup.mem_inf.mp c.2).2,
        (mem_fixV_iff₂ hyp hβ hXL (Subgroup.mem_inf.mp c.2).2).mp (Subgroup.mem_inf.mp c.2).1⟩
      invFun := fun c => ⟨c.1, Subgroup.mem_inf.mpr
        ⟨(mem_fixV_iff₂ hyp hβ hXL c.2.1).mpr c.2.2, c.2.1⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_fix₁_mul [Finite W] (hyp : H9Hyp n M L T W₁ W₂) (hβ : IsDualH9 L W₁ W₂ β)
    (hcard : ∀ U : Subgroup W, U ≤ W₂ →
      Nat.card U * Nat.card {a : W // a ∈ W₁ ∧ ∀ c ∈ U, β a c = 0} = 2 ^ n)
    {X : Subgroup (MulAut W)} (hXL : X ≤ L) :
    Nat.card ↥(fixV X ⊓ W₁) * Nat.card (commOn X W₂) = 2 ^ n := by
  rw [mul_comm, ← hcard _ (commOn_le (hXL.trans hyp.inv₂))]
  congr 1
  exact Nat.card_congr
    { toFun := fun a => ⟨a.1, (Subgroup.mem_inf.mp a.2).2,
        (mem_fixV_iff₁ hyp hβ hXL (Subgroup.mem_inf.mp a.2).2).mp (Subgroup.mem_inf.mp a.2).1⟩
      invFun := fun a => ⟨a.1, Subgroup.mem_inf.mpr
        ⟨(mem_fixV_iff₁ hyp hβ hXL a.2.1).mpr a.2.2, a.2.1⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem commOn_eq_of_fix₂_eq [Finite W] (hyp : H9Hyp n M L T W₁ W₂) (hβ : IsDualH9 L W₁ W₂ β)
    (hcard₁ : ∀ U : Subgroup W, U ≤ W₁ →
      Nat.card U * Nat.card {c : W // c ∈ W₂ ∧ ∀ u ∈ U, β u c = 0} = 2 ^ n)
    (hcard₂ : ∀ U : Subgroup W, U ≤ W₂ →
      Nat.card U * Nat.card {a : W // a ∈ W₁ ∧ ∀ c ∈ U, β a c = 0} = 2 ^ n)
    {b c : MulAut W} (hb : b ∈ L) (hc : c ∈ L)
    (h : fixV (Subgroup.zpowers b) ⊓ W₂ = fixV (Subgroup.zpowers c) ⊓ W₂) :
    commOn (Subgroup.zpowers b) W₁ = commOn (Subgroup.zpowers c) W₁ := by
  have hbL : Subgroup.zpowers b ≤ L := (Subgroup.zpowers_le).mpr hb
  have hcL : Subgroup.zpowers c ≤ L := (Subgroup.zpowers_le).mpr hc
  set P := fixV (Subgroup.zpowers b) ⊓ W₂ with hP
  let Q : Subgroup W :=
    { carrier := {a | a ∈ W₁ ∧ ∀ d ∈ P, β a d = 0}
      mul_mem' := fun {x y} hx hy => ⟨W₁.mul_mem hx.1 hy.1, fun d hd => by
        rw [hβ.1 x hx.1 y hy.1 d (Subgroup.mem_inf.mp hd).2, hx.2 d hd, hy.2 d hd, add_zero]⟩
      one_mem' := ⟨W₁.one_mem, fun d hd => pairing_one_left hβ (Subgroup.mem_inf.mp hd).2⟩
      inv_mem' := fun {x} hx => by
        show x⁻¹ ∈ W₁ ∧ ∀ d ∈ P, β x⁻¹ d = 0
        rw [exp_of_hyp hyp x]
        exact hx }
  have hcardQ : Nat.card Q = Nat.card {a : W // a ∈ W₁ ∧ ∀ d ∈ P, β a d = 0} := rfl
  have key : ∀ x : MulAut W, Subgroup.zpowers x ≤ L →
      fixV (Subgroup.zpowers x) ⊓ W₂ = P → commOn (Subgroup.zpowers x) W₁ = Q := by
    intro x hxL hxP
    have hle : commOn (Subgroup.zpowers x) W₁ ≤ Q := fun g hg =>
      ⟨commOn_le (hxL.trans hyp.inv₁) hg, fun d hd => by
        rw [← hxP] at hd
        exact (mem_fixV_iff₂ hyp hβ hxL (Subgroup.mem_inf.mp hd).2).mp
          (Subgroup.mem_inf.mp hd).1 g hg⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 := card_fix₂_mul hyp hβ hcard₁ hxL
    have h2 := hcard₂ P inf_le_right
    rw [hxP] at h1
    rw [← hcardQ] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : Nat.card P * Nat.card Q = Nat.card P * Nat.card (commOn (Subgroup.zpowers x) W₁) :=
      h2.trans h1.symm
    exact (Nat.eq_of_mul_eq_mul_left hpos this).le
  rw [key b hbL rfl, key c hcL h.symm]

theorem eq_one_of_fix₂ (hyp : H9Hyp n M L T W₁ W₂) (hβ : IsDualH9 L W₁ W₂ β) {x : MulAut W}
    (hx : x ∈ L) (h : ∀ c ∈ W₂, x c = c) : x = 1 := by
  have hxL : Subgroup.zpowers x ≤ L := (Subgroup.zpowers_le).mpr hx
  refine hyp.faith x hx fun a ha => ?_
  have h1 : a ∈ fixV (Subgroup.zpowers x) := by
    refine (mem_fixV_iff₁ hyp hβ hxL ha).mpr fun g hg => ?_
    have hbot : commOn (Subgroup.zpowers x) W₂ = ⊥ := by
      rw [eq_bot_iff, commOn, Subgroup.closure_le]
      rintro _ ⟨y, hy, u, hu, rfl⟩
      obtain ⟨k, rfl⟩ := hy
      have hyu : (x ^ k) u = u := by
        have := (H.mem_fixV_zpowers_iff (x := x) (v := u)).mpr (h u hu)
        exact this _ ⟨k, rfl⟩
      rw [hyu, mul_inv_cancel]
      exact Subgroup.one_mem _
    rw [hbot, Subgroup.mem_bot] at hg
    rw [hg]
    exact pairing_one_right hβ ha
  exact H.mem_fixV_zpowers_iff.mp h1

theorem card_le_two_of_commOn [Finite W] (hyp : H9Hyp n M L T W₁ W₂) (hβ : IsDualH9 L W₁ W₂ β)
    (hcard : ∀ U : Subgroup W, U ≤ W₂ →
      Nat.card U * Nat.card {a : W // a ∈ W₁ ∧ ∀ c ∈ U, β a c = 0} = 2 ^ n)
    {X : Subgroup (MulAut W)} (hXL : X ≤ L)
    (h4 : Nat.card (commOn X W₁) * Nat.card (commOn X W₂) ≤ 4) : Nat.card X ≤ 2 := by
  by_contra h2
  push Not at h2
  have hX₁ : X ≤ stabV W₁ := hXL.trans hyp.inv₁
  have hne : ∀ U : Subgroup W, U = W₁ ∨ U = W₂ → 2 ≤ Nat.card (commOn X U) := by
    intro U hU
    by_contra hlt
    push Not at hlt
    have hbot : commOn X U = ⊥ := by
      rw [← Subgroup.card_eq_one]
      have := Nat.card_pos (α := commOn X U)
      omega
    have h1 := commOn_eq_bot hbot
    have hX1 : X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      rcases hU with rfl | rfl
      · exact hyp.faith x (hXL hx) (h1 x hx)
      · exact eq_one_of_fix₂ hyp hβ (hXL hx) (h1 x hx)
    rw [hX1, Subgroup.card_bot] at h2
    omega
  have hk₁ := hne W₁ (Or.inl rfl)
  have hk₂ := hne W₂ (Or.inr rfl)
  have hk₁2 : Nat.card (commOn X W₁) = 2 := by
    have : Nat.card (commOn X W₁) * 2 ≤ 4 :=
      (Nat.mul_le_mul_left _ hk₂).trans h4
    omega
  have hk₂2 : Nat.card (commOn X W₂) = 2 := by
    have : 2 * Nat.card (commOn X W₂) ≤ 4 :=
      (Nat.mul_le_mul_right _ hk₁).trans h4
    omega
  have hF := card_fix₁_mul hyp hβ hcard hXL
  rw [hk₂2] at hF
  have hW₁ := hyp.card₁
  have hidx : ((fixV X ⊓ W₁).subgroupOf W₁).index = 2 := by
    have h := Subgroup.relIndex_mul_card (H := fixV X ⊓ W₁) (K := W₁)
    rw [inf_eq_left.2 inf_le_right, hW₁, ← hF, mul_comm (Nat.card _) 2] at h
    have hpos : 0 < Nat.card ↥(fixV X ⊓ W₁) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  obtain ⟨v₀, hv₀, hv₀F⟩ : ∃ v₀ ∈ W₁, v₀ ∉ fixV X ⊓ W₁ := by
    by_contra hall
    push Not at hall
    have h1 : (fixV X ⊓ W₁).subgroupOf W₁ = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨w, hw⟩ -
      rw [Subgroup.mem_subgroupOf]
      exact hall w hw
    rw [h1, Subgroup.index_top] at hidx
    omega
  have hle := card_le_of_eval_injective (X := X) (K := commOn X W₁) (v₀ := v₀)
    (fun x hx hxv => hyp.faith x (hXL hx) fun w hw => by
      rcases mem_or_mul_mem hidx hv₀ hv₀F hw with h | h
      · exact (Subgroup.mem_inf.mp h).1 x hx
      · have h1 := (Subgroup.mem_inf.mp h).1 x hx
        rw [map_mul, map_inv, hxv] at h1
        exact mul_right_cancel h1)
    (fun x hx => mem_commOn_of hx hv₀)
  omega

theorem three_le (hyp : H9Hyp n M L T W₁ W₂) : 3 ≤ n := by
  rcases hyp.rank with rfl | rfl <;> norm_num

theorem card_fixV_split (hyp : H9Hyp n M L T W₁ W₂) {X : Subgroup (MulAut W)} (hXL : X ≤ L) :
    Nat.card (fixV X) = Nat.card ↥(fixV X ⊓ W₁) * Nat.card ↥(fixV X ⊓ W₂) := by
  have hX₁ : X ≤ stabV W₁ := hXL.trans hyp.inv₁
  have hX₂ : X ≤ stabV W₂ := hXL.trans hyp.inv₂
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p => (⟨p.1.1 * p.2.1,
    (fixV X).mul_mem (Subgroup.mem_inf.mp p.1.2).1 (Subgroup.mem_inf.mp p.2.2).1⟩ : fixV X))
    ⟨fun p q h => ?_, fun w => ?_⟩)
  · have h1 := congrArg Subtype.val h
    obtain ⟨h2, h3⟩ := decomp_unique hyp (Subgroup.mem_inf.mp p.1.2).2
      (Subgroup.mem_inf.mp q.1.2).2 (Subgroup.mem_inf.mp p.2.2).2 (Subgroup.mem_inf.mp q.2.2).2 h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  · obtain ⟨a, ha, c, hc, h⟩ := exists_decomp hyp w.1
    have hfix : ∀ x ∈ X, x a = a ∧ x c = c := fun x hx => by
      have hw := w.2 x hx
      rw [h, map_mul] at hw
      exact decomp_unique hyp ((hX₁ hx a).mp ha) ha ((hX₂ hx c).mp hc) hc hw
    exact ⟨(⟨a, Subgroup.mem_inf.mpr ⟨fun x hx => (hfix x hx).1, ha⟩⟩,
      ⟨c, Subgroup.mem_inf.mpr ⟨fun x hx => (hfix x hx).2, hc⟩⟩), Subtype.ext h.symm⟩

variable [Finite W]

theorem card_W_eq (hyp : H9Hyp n M L T W₁ W₂) : Nat.card W = 2 ^ n * 2 ^ n :=
  H9Conj.card_W hyp

theorem card_commOn_mul_le (hyp : H9Hyp n M L T W₁ W₂) {X : Subgroup (MulAut W)} (hXL : X ≤ L) :
    Nat.card (commOn X W₁) * Nat.card (commOn X W₂) ≤ Nat.card (commV X) := by
  have h1 := commOn_le (hXL.trans hyp.inv₁)
  have h2 := commOn_le (hXL.trans hyp.inv₂)
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => (⟨p.1.1 * p.2.1,
    (commV X).mul_mem (commOn_le_commV X W₁ p.1.2) (commOn_le_commV X W₂ p.2.2)⟩ : commV X))
    fun p q h => ?_
  have h3 := congrArg Subtype.val h
  obtain ⟨h4, h5⟩ := decomp_unique hyp (h1 p.1.2) (h1 q.1.2) (h2 p.2.2) (h2 q.2.2) h3
  exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)

theorem big_of_not_le (hyp : H9Hyp n M L T W₁ W₂) {X : Subgroup (MulAut W)} (hXM : X ≤ M)
    (hX : IsElemAbelian2 X) {x : MulAut W} (hx : x ∈ X) (hxL : x ∉ L) :
    2 ^ n ≤ Nat.card (commV X) ∧ 2 ^ n * Nat.card (fixV X) ≤ Nat.card W := by
  have hx2 := hX.2 x hx
  have hfix := card_fixV_of_not_mem hyp (hXM hx) hxL hx2
  rw [hyp.card₁] at hfix
  have hcomm : Nat.card (commOn (Subgroup.zpowers x) ⊤) = 2 ^ n := by
    have h := card_fix_mul_card_commOn hx2 (⊤ : Subgroup W)
    rw [inf_top_eq, hfix, Subgroup.card_top, card_W_eq hyp] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  refine ⟨?_, ?_⟩
  · rw [← hcomm]
    exact Subgroup.card_le_of_le ((commOn_le_commV _ ⊤).trans
      (Subgroup.closure_mono fun _ ⟨y, hy, v, hv⟩ => ⟨y, (Subgroup.zpowers_le).mpr hx hy, v, hv⟩))
  · have hle : fixV X ≤ fixV (Subgroup.zpowers x) := fun w hw y hy => by
      obtain ⟨k, rfl⟩ := hy
      have hw' : x w = w := hw x hx
      exact (H.mem_fixV_zpowers_iff (x := x)).mpr hw' _ ⟨k, rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hfix] at h1
    rw [card_W_eq hyp]
    exact Nat.mul_le_mul_left _ h1

theorem lemH9Comm_holds : LemH9Comm := by
  intro W _ _ n M L T W₁ W₂ hyp X hXM hX hc
  have hn := three_le hyp
  obtain ⟨β, hβ, -, hcard₂⟩ := exists_goodDual hyp hn
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hXL : X ≤ L := fun x hx => by
    by_contra hxL
    have := (big_of_not_le hyp hXM hX hx hxL).1
    omega
  exact card_le_two_of_commOn hyp hβ hcard₂ hXL ((card_commOn_mul_le hyp hXL).trans hc)

theorem lemH9Cent_holds : LemH9Cent := by
  intro W _ _ n M L T W₁ W₂ hyp X hXM hX hc
  have hn := three_le hyp
  obtain ⟨β, hβ, hcard₁, hcard₂⟩ := exists_goodDual hyp hn
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpos : 0 < Nat.card (fixV X) := Nat.card_pos
  have hXL : X ≤ L := fun x hx => by
    by_contra hxL
    have h1 := (big_of_not_le hyp hXM hX hx hxL).2
    have h2 : 8 * Nat.card (fixV X) ≤ 2 ^ 2 * Nat.card (fixV X) :=
      ((Nat.mul_le_mul_right _ h8).trans h1).trans hc
    have h3 : 8 ≤ 2 ^ 2 := Nat.le_of_mul_le_mul_right h2 hpos
    norm_num at h3
  refine card_le_two_of_commOn hyp hβ hcard₂ hXL ?_
  have h1 := card_fix₁_mul hyp hβ hcard₂ hXL
  have h2 := card_fix₂_mul hyp hβ hcard₁ hXL
  rw [card_fixV_split hyp hXL, card_W_eq hyp] at hc
  have h3 : 2 ^ n * 2 ^ n * (Nat.card (commOn X W₁) * Nat.card (commOn X W₂)) ≤
      2 ^ n * 2 ^ n * 4 := by
    calc 2 ^ n * 2 ^ n * (Nat.card (commOn X W₁) * Nat.card (commOn X W₂))
        ≤ 2 ^ 2 * (Nat.card ↥(fixV X ⊓ W₁) * Nat.card ↥(fixV X ⊓ W₂)) *
          (Nat.card (commOn X W₁) * Nat.card (commOn X W₂)) := Nat.mul_le_mul_right _ hc
      _ = 4 * ((Nat.card ↥(fixV X ⊓ W₁) * Nat.card (commOn X W₂)) *
          (Nat.card ↥(fixV X ⊓ W₂) * Nat.card (commOn X W₁))) := by ring
      _ = 2 ^ n * 2 ^ n * 4 := by rw [h1, h2]; ring
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

theorem lemH9Axes_holds : LemH9Axes := by
  intro W _ _ n M L T W₁ W₂ hyp B hBL hB hcard hfix
  have hn := three_le hyp
  obtain ⟨β, hβ, hcard₁, hcard₂⟩ := exists_goodDual hyp hn
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b₀ ∈ B, b₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (h x hx)
    rw [this, Subgroup.card_bot] at hcard
    have : 2 ^ 1 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set U := fixV (Subgroup.zpowers b₀) ⊓ W₁ with hU
  set K := commOn (Subgroup.zpowers b₀) W₁ with hK
  have hb₀2 := hB.2 b₀ hb₀
  have hUK : Nat.card U * Nat.card K = 2 ^ n := by
    rw [hU, hK, card_fix_mul_card_commOn hb₀2, hyp.card₁]
  have hKU : K ≤ U := le_inf (commOn_le_fix hyp.exp hb₀2 W₁)
    (commOn_le (((Subgroup.zpowers_le).mpr (hBL hb₀)).trans hyp.inv₁))
  have hKb : ∀ b ∈ B, b ≠ 1 → commOn (Subgroup.zpowers b) W₁ = K := fun b hb hb1 =>
    commOn_eq_of_fix₂_eq hyp hβ hcard₁ hcard₂ (hBL hb) (hBL hb₀) (hfix b hb b₀ hb₀ hb1 hb₀1).2
  obtain ⟨v₀, hv₀, hv₀U⟩ : ∃ v₀ ∈ W₁, v₀ ∉ U := by
    by_contra h
    push Not at h
    exact hb₀1 (hyp.faith b₀ (hBL hb₀) fun w hw =>
      H.mem_fixV_zpowers_iff.mp (Subgroup.mem_inf.mp (h w hw)).1)
  have hBK := card_le_of_eval_injective (X := B) (K := K) (v₀ := v₀)
    (fun x hx hxv => by
      by_contra hx1
      apply hv₀U
      rw [hU, ← (hfix x hx b₀ hb₀ hx1 hb₀1).1]
      exact Subgroup.mem_inf.mpr ⟨H.mem_fixV_zpowers_iff.mpr hxv, hv₀⟩)
    (fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1, MulAut.one_apply, mul_inv_cancel]
        exact K.one_mem
      · rw [← hKb x hx hx1]
        exact mem_commOn_of (Subgroup.mem_zpowers x) hv₀)
  have hKU' := Subgroup.card_le_of_le hKU
  have hsq : Nat.card B * Nat.card B ≤ 2 ^ n := by
    rw [← hUK]
    calc Nat.card B * Nat.card B ≤ Nat.card U * Nat.card K :=
          Nat.mul_le_mul (hBK.trans hKU') hBK
      _ = Nat.card U * Nat.card K := rfl
  rcases hyp.rank with rfl | rfl
  · norm_num at hcard hsq hUK
    have hB4 : Nat.card B = 4 := by nlinarith
    refine ⟨rfl, by rw [hB4]; norm_num, fun b hb hb1 => ?_⟩
    rw [(hfix b hb b₀ hb₀ hb1 hb₀1).1]
    show Nat.card U = 2 ^ 2
    nlinarith
  · norm_num at hcard hsq
    nlinarith

theorem lemH9FF5_holds : LemH9FF5 := by
  intro W _ _ M L T W₁ W₂ hyp A hAM hA hA1 hA16 hff
  obtain ⟨β, hβ, hcard₁, hcard₂⟩ := exists_goodDual hyp (by norm_num)
  have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have hAL : A ≤ L := fun x hx => by
    by_contra hxL
    have h1 := (big_of_not_le hyp hAM hA hx hxL).2
    have h2 : 2 ^ 5 * Nat.card (fixV A) ≤ 2 ^ 4 * Nat.card (fixV A) :=
      h1.trans (hff.trans (Nat.mul_le_mul_right _ hA16))
    have h3 := Nat.le_of_mul_le_mul_right h2 hpos
    norm_num at h3
  have h1 := card_fix₁_mul hyp hβ hcard₂ hAL
  have h2 := card_fix₂_mul hyp hβ hcard₁ hAL
  rw [card_fixV_split hyp hAL, card_W_eq hyp] at hff
  set k₁ := Nat.card (commOn A W₁) with hk₁
  set k₂ := Nat.card (commOn A W₂) with hk₂
  set f₁ := Nat.card ↥(fixV A ⊓ W₁) with hf₁
  set f₂ := Nat.card ↥(fixV A ⊓ W₂) with hf₂
  have hkk : k₁ * k₂ ≤ Nat.card A := by
    have h3 : 2 ^ 5 * 2 ^ 5 * (k₁ * k₂) ≤ 2 ^ 5 * 2 ^ 5 * Nat.card A := by
      calc 2 ^ 5 * 2 ^ 5 * (k₁ * k₂) ≤ Nat.card A * (f₁ * f₂) * (k₁ * k₂) :=
            Nat.mul_le_mul_right _ hff
        _ = Nat.card A * ((f₁ * k₂) * (f₂ * k₁)) := by ring
        _ = 2 ^ 5 * 2 ^ 5 * Nat.card A := by rw [h1, h2]; ring
    exact Nat.le_of_mul_le_mul_left h3 (by positivity)
  have hdvd₁ : k₁ ∣ 2 ^ 5 := ⟨f₂, by rw [← h2, mul_comm]⟩
  have hdvd₂ : k₂ ∣ 2 ^ 5 := ⟨f₁, by rw [← h1, mul_comm]⟩
  obtain ⟨i₁, hi₁, hk₁e⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd₁
  obtain ⟨i₂, hi₂, hk₂e⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd₂
  have hA1' : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    exact hA1 (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx))
  obtain ⟨a, ha, ha1⟩ := hA1'
  have hne₁ : k₁ ≠ 1 := fun h => ha1 (hyp.faith a (hAL ha)
    (commOn_eq_bot (Subgroup.card_eq_one.mp h) a ha))
  have hne₂ : k₂ ≠ 1 := fun h => ha1 (eq_one_of_fix₂ hyp hβ (hAL ha)
    (commOn_eq_bot (Subgroup.card_eq_one.mp h) a ha))
  have hnot2 : ∀ (U V : Subgroup W), (U = W₁ ∧ V = W₂) ∨ (U = W₂ ∧ V = W₁) →
      Nat.card (commOn A V) = 2 → Nat.card A ≤ Nat.card (commOn A U) := by
    intro U V hUV hV2
    have hAU : A ≤ stabV U := by
      rcases hUV with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hAL.trans hyp.inv₁
      · exact hAL.trans hyp.inv₂
    have hfaith : ∀ x ∈ A, (∀ u ∈ U, x u = u) → x = 1 := fun x hx h => by
      rcases hUV with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hyp.faith x (hAL hx) h
      · exact eq_one_of_fix₂ hyp hβ (hAL hx) h
    have hcardU : Nat.card U = 2 ^ 5 := by
      rcases hUV with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hyp.card₁
      · obtain ⟨t, -, -, ht⟩ := hyp.swap
        rw [ht, Subgroup.card_map_of_injective (f := t.toMonoidHom) t.injective, hyp.card₁]
    have hFU : Nat.card ↥(fixV A ⊓ U) * Nat.card (commOn A V) = 2 ^ 5 := by
      rcases hUV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1
      · exact h2
    rw [hV2] at hFU
    have hidx : ((fixV A ⊓ U).subgroupOf U).index = 2 := by
      have h := Subgroup.relIndex_mul_card (H := fixV A ⊓ U) (K := U)
      rw [inf_eq_left.2 inf_le_right, hcardU, ← hFU, mul_comm (Nat.card _) 2] at h
      have hpos' : 0 < Nat.card ↥(fixV A ⊓ U) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos' h
    obtain ⟨v₀, hv₀, hv₀F⟩ : ∃ v₀ ∈ U, v₀ ∉ fixV A ⊓ U := by
      by_contra hall
      push Not at hall
      have h3 : (fixV A ⊓ U).subgroupOf U = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨w, hw⟩ -
        rw [Subgroup.mem_subgroupOf]
        exact hall w hw
      rw [h3, Subgroup.index_top] at hidx
      omega
    exact card_le_of_eval_injective (X := A) (K := commOn A U) (v₀ := v₀)
      (fun x hx hxv => hfaith x hx fun w hw => by
        rcases mem_or_mul_mem hidx hv₀ hv₀F hw with h | h
        · exact (Subgroup.mem_inf.mp h).1 x hx
        · have h3 := (Subgroup.mem_inf.mp h).1 x hx
          rw [map_mul, map_inv, hxv] at h3
          exact mul_right_cancel h3)
      (fun x hx => mem_commOn_of hx hv₀)
  have hk₁2 : k₁ ≠ 2 := fun h => by
    have := hnot2 W₂ W₁ (Or.inr ⟨rfl, rfl⟩) h
    rw [← hk₂] at this
    have hpos₂ : 0 < k₂ := Nat.card_pos
    rw [h] at hkk
    omega
  have hk₂2 : k₂ ≠ 2 := fun h => by
    have := hnot2 W₁ W₂ (Or.inl ⟨rfl, rfl⟩) h
    rw [← hk₁] at this
    have hpos₁ : 0 < k₁ := Nat.card_pos
    rw [h] at hkk
    omega
  have h4₁ : 4 ≤ k₁ := by
    rw [hk₁e] at hne₁ hk₁2 ⊢
    rcases i₁ with _ | _ | i₁
    · exact absurd rfl hne₁
    · exact absurd rfl hk₁2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (i₁ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4₂ : 4 ≤ k₂ := by
    rw [hk₂e] at hne₂ hk₂2 ⊢
    rcases i₂ with _ | _ | i₂
    · exact absurd rfl hne₂
    · exact absurd rfl hk₂2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (i₂ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk1 : k₁ = 4 := by nlinarith
  have hk2 : k₂ = 4 := by nlinarith
  refine ⟨?_, ?_⟩
  · show k₁ ≤ 2 ^ 2
    omega
  ·
    have h3 := Subgroup.relIndex_mul_card (H := fixV A ⊓ W₁) (K := W₁)
    rw [inf_eq_left.2 inf_le_right, hyp.card₁, ← hf₁] at h3
    have h7 : f₁ * 4 = 2 ^ 5 := by rw [← hk2]; exact h1
    have hf₁pos : 0 < f₁ := Nat.card_pos
    have : (fixV A ⊓ W₁).relIndex W₁ = 4 := by nlinarith
    omega

end CFSG.Quasithin.H13.H9Lin
