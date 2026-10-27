module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4

public section

namespace CFSG.Quasithin.S14110.Commute

open Subgroup

variable {G : Type*} [Group G]

theorem two_pow_mod_three (m : ℕ) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem mem_of_pow_three_mem {B : Subgroup G} {a : G} (h3 : a ^ 3 ∈ B)
    (h2 : ∃ m : ℕ, a ^ 2 ^ m = 1) : a ∈ B := by
  obtain ⟨m, hm⟩ := h2
  have hmod := two_pow_mod_three m
  have hdecomp : a ^ 2 ^ m = (a ^ 3) ^ (2 ^ m / 3) * a ^ (2 ^ m % 3) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hr : a ^ (2 ^ m % 3) ∈ B := by
    have : a ^ (2 ^ m % 3) = ((a ^ 3) ^ (2 ^ m / 3))⁻¹ := by
      rw [hm] at hdecomp
      exact eq_inv_of_mul_eq_one_right hdecomp.symm
    rw [this]
    exact B.inv_mem (B.pow_mem h3 _)
  rcases hmod with h | h
  · rw [h, pow_one] at hr; exact hr
  · rw [h] at hr
    have : a = a ^ 3 * (a ^ 2)⁻¹ := by group
    rw [this]
    exact B.mul_mem h3 (B.inv_mem hr)

theorem mem_of_sq_mem_of_pow_mem {B : Subgroup G} {a : G} {n : ℕ} (hn : Odd n) (h2 : a ^ 2 ∈ B)
    (hk : a ^ n ∈ B) : a ∈ B := by
  obtain ⟨t, rfl⟩ := hn
  have h1 : a ^ (2 * t + 1) = (a ^ 2) ^ t * a := by rw [pow_succ, pow_mul]
  have : a = ((a ^ 2) ^ t)⁻¹ * a ^ (2 * t + 1) := by rw [h1]; group
  rw [this]
  exact B.mul_mem (B.inv_mem (B.pow_mem h2 _)) hk

variable {X W : Subgroup G} {c : G}

theorem pow_three_mem_W (h : A4Data X W c) {x : G} (hx : x ∈ X) : x ^ 3 ∈ W := by
  obtain ⟨w, hw, k, rfl⟩ := h.mem_decomp hx
  have hk : ∀ j : ℤ, ∀ u ∈ W, c ^ j * u * (c ^ j)⁻¹ ∈ W := fun j u hu =>
    (mem_normalizer_iff.1 (zpow_mem h.mem_normalizer j) u).1 hu
  have h3 : c ^ (3 * k) = 1 := by
    have : c ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact h.c_pow_three
    rw [zpow_mul, this, one_zpow]
  have : (w * c ^ k) ^ 3 = w * (c ^ k * w * (c ^ k)⁻¹) * (c ^ (2 * k) * w * (c ^ (2 * k))⁻¹) *
      c ^ (3 * k) := by rw [pow_three']; group
  rw [this, h3, mul_one]
  exact W.mul_mem (W.mul_mem hw (hk k w hw)) (hk (2 * k) w hw)

theorem mem_W_of_pow_two_pow_eq_one (h : A4Data X W c) {x : G} (hx : x ∈ X)
    (h2 : ∃ m : ℕ, x ^ 2 ^ m = 1) : x ∈ W :=
  mem_of_pow_three_mem (pow_three_mem_W h hx) h2

theorem eq_one_or_eq_conj (h : A4Data X W c) {u : G} (hu : u ∈ W) (hu1 : u ≠ 1) {w : G}
    (hw : w ∈ W) :
    w = 1 ∨ w = u ∨ w = c * u * c⁻¹ ∨ w = c * (c * u * c⁻¹) * c⁻¹ := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hw1, hwu, hwv, hwv'⟩ := hne
  have hWfin : Finite W := h.finite_W
  set v : G := c * u * c⁻¹ with hv_def
  set v' : G := c * v * c⁻¹ with hv'_def
  have hv : v ∈ W := h.conj_mem hu
  have hv' : v' ∈ W := h.conj_mem hv
  have hccc : c * c * c = 1 := by rw [← pow_three']; exact h.c_pow_three
  have hc3 : c * v' * c⁻¹ = u := by
    have : c * v' * c⁻¹ = (c * c * c) * u * (c * c * c)⁻¹ := by rw [hv'_def, hv_def]; group
    rw [this, hccc]; simp
  have hconj_ne : ∀ a : G, a ≠ 1 → c * a * c⁻¹ ≠ 1 := fun a ha h1 => ha (by
    have h2 : a = c⁻¹ * (c * a * c⁻¹) * c := by group
    rw [h2, h1]; group)
  have hv1 : v ≠ 1 := hconj_ne u hu1
  have hv'1 : v' ≠ 1 := hconj_ne v hv1
  have huv : u ≠ v := fun h' => h.fpf u hu hu1 h'.symm
  have huv' : u ≠ v' := fun h' => by
    apply huv
    calc u = c * v' * c⁻¹ := hc3.symm
      _ = c * u * c⁻¹ := by rw [← h']
  have hvv' : v ≠ v' := fun h' => h.fpf v hv hv1 h'.symm
  have hcard : ({1, u, v, v', w} : Finset G).card = 5 := by
    have e1 := hu1.symm
    have e2 := hv1.symm
    have e3 := hv'1.symm
    have e4 := hw1.symm
    have e5 := hwu.symm
    have e6 := hwv.symm
    have e7 := hwv'.symm
    simp [e1, e2, e3, e4, e5, e6, e7, huv, huv', hvv']
  have hsub : (({1, u, v, v', w} : Finset G) : Set G) ⊆ (W : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact hu
    · exact hv
    · exact hv'
    · exact hw
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at h1
  have h2 : (W : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact h.card_W
  omega

@[expose] def CommutesOn (c : G) (W : Subgroup G) (g : G) : Prop :=
  ∀ w ∈ W, g * (c * w * c⁻¹) * g⁻¹ = c * (g * w * g⁻¹) * c⁻¹

theorem CommutesOn.of_commute {g : G} (hg : g * c = c * g) : CommutesOn c W g := by
  intro w _
  calc g * (c * w * c⁻¹) * g⁻¹ = (g * c) * w * (g * c)⁻¹ := by group
    _ = (c * g) * w * (c * g)⁻¹ := by rw [hg]
    _ = c * (g * w * g⁻¹) * c⁻¹ := by group

theorem CommutesOn.mul_left {g : G} (hg : CommutesOn c W g) : CommutesOn c W (c * g) := by
  intro w hw
  have := hg w hw
  calc c * g * (c * w * c⁻¹) * (c * g)⁻¹ = c * (g * (c * w * c⁻¹) * g⁻¹) * c⁻¹ := by group
    _ = c * (c * (g * w * g⁻¹) * c⁻¹) * c⁻¹ := by rw [this]
    _ = c * (c * g * w * (c * g)⁻¹) * c⁻¹ := by group

theorem CommutesOn.inv_mul_left {g : G} (hg : CommutesOn c W g) : CommutesOn c W (c⁻¹ * g) := by
  intro w hw
  have := hg w hw
  calc c⁻¹ * g * (c * w * c⁻¹) * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * (c * w * c⁻¹) * g⁻¹) * c := by group
    _ = c⁻¹ * (c * (g * w * g⁻¹) * c⁻¹) * c := by rw [this]
    _ = c * (c⁻¹ * g * w * (c⁻¹ * g)⁻¹) * c⁻¹ := by group

theorem CommutesOn.pow_conj (h : A4Data X W c) {g : G} (hg : CommutesOn c W g) (i : ℕ) :
    ∀ w ∈ W, g * (c ^ i * w * (c ^ i)⁻¹) * g⁻¹ = c ^ i * (g * w * g⁻¹) * (c ^ i)⁻¹ := by
  induction i with
  | zero => intro w _; simp
  | succ i ih =>
    intro w hw
    have hw' : c ^ i * w * (c ^ i)⁻¹ ∈ W :=
      (mem_normalizer_iff.1 (pow_mem h.mem_normalizer i) w).1 hw
    have e1 : c ^ (i + 1) * w * (c ^ (i + 1))⁻¹ = c * (c ^ i * w * (c ^ i)⁻¹) * c⁻¹ := by
      rw [pow_succ']; group
    have e2 : c ^ (i + 1) * (g * w * g⁻¹) * (c ^ (i + 1))⁻¹ =
        c * (c ^ i * (g * w * g⁻¹) * (c ^ i)⁻¹) * c⁻¹ := by
      rw [pow_succ']; group
    rw [e1, e2, hg _ hw', ih w hw]

theorem centralizes_of_fixes (h : A4Data X W c) {g u : G} (hg : CommutesOn c W g) (hu : u ∈ W)
    (hu1 : u ≠ 1) (hgu : g * u * g⁻¹ = u) : ∀ w ∈ W, g * w * g⁻¹ = w := by
  intro w hw
  rcases eq_one_or_eq_conj h hu hu1 hw with rfl | rfl | rfl | rfl
  · simp
  · exact hgu
  · rw [hg u hu, hgu]
  · rw [hg _ (h.conj_mem hu), hg u hu, hgu]

theorem exists_pow_conj_eq (h : A4Data X W c) {g : G} (hg : CommutesOn c W g)
    (hgW : ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    ∃ j : ℕ, ∀ w ∈ W, g * w * g⁻¹ = c ^ j * w * (c ^ j)⁻¹ := by
  obtain ⟨u, hu, hu1⟩ := h.exists_ne_one_mem_W
  have hccc : c * c * c = 1 := by rw [← pow_three']; exact h.c_pow_three
  rcases eq_one_or_eq_conj h hu hu1 (hgW u hu) with h1 | h1 | h1 | h1
  · exfalso
    apply hu1
    have : u = g⁻¹ * (g * u * g⁻¹) * g := by group
    rw [this, h1]; group
  · refine ⟨0, fun w hw => ?_⟩
    simpa using centralizes_of_fixes h hg hu hu1 h1 w hw
  · refine ⟨1, fun w hw => ?_⟩
    have hfix : c⁻¹ * g * u * (c⁻¹ * g)⁻¹ = u := by
      calc c⁻¹ * g * u * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * u * g⁻¹) * c := by group
        _ = u := by rw [h1]; group
    have := centralizes_of_fixes h hg.inv_mul_left hu hu1 hfix w hw
    calc g * w * g⁻¹ = c * (c⁻¹ * g * w * (c⁻¹ * g)⁻¹) * c⁻¹ := by group
      _ = c ^ 1 * w * (c ^ 1)⁻¹ := by rw [this]; simp
  · refine ⟨2, fun w hw => ?_⟩
    have hfix : c * g * u * (c * g)⁻¹ = u := by
      calc c * g * u * (c * g)⁻¹ = c * (g * u * g⁻¹) * c⁻¹ := by group
        _ = (c * c * c) * u * (c * c * c)⁻¹ := by rw [h1]; group
        _ = u := by rw [hccc]; simp
    have := centralizes_of_fixes h hg.mul_left hu hu1 hfix w hw
    have hc2 : c ^ 2 = c⁻¹ := by rw [pow_two]; exact eq_inv_of_mul_eq_one_left hccc
    calc g * w * g⁻¹ = c⁻¹ * (c * g * w * (c * g)⁻¹) * c := by group
      _ = c ^ 2 * w * (c ^ 2)⁻¹ := by rw [this, hc2]; group

theorem centralizes_of_two_power (h : A4Data X W c) {q : G} (hqW : ∀ w ∈ W, q * w * q⁻¹ ∈ W)
    (hqc : q * c * q⁻¹ * c⁻¹ ∈ W) (hq2 : ∃ m : ℕ, q ^ 2 ^ m = 1) :
    ∀ w ∈ W, q * w * q⁻¹ = w := by
  obtain ⟨m, hm⟩ := hq2
  have hcomm : CommutesOn c W q := by
    intro w hw
    have hw' : c * (q * w * q⁻¹) * c⁻¹ ∈ W := h.conj_mem (hqW w hw)
    have hqc' : q * c = (q * c * q⁻¹ * c⁻¹) * (c * q) := by group
    have hzw := h.comm _ hqc _ hw'
    calc q * (c * w * c⁻¹) * q⁻¹ = (q * c) * w * (q * c)⁻¹ := by group
      _ = ((q * c * q⁻¹ * c⁻¹) * (c * q)) * w * ((q * c * q⁻¹ * c⁻¹) * (c * q))⁻¹ := by
        rw [← hqc']
      _ = (q * c * q⁻¹ * c⁻¹) * (c * (q * w * q⁻¹) * c⁻¹) * (q * c * q⁻¹ * c⁻¹)⁻¹ := by group
      _ = c * (q * w * q⁻¹) * c⁻¹ := by rw [hzw]; group
  obtain ⟨j, hj⟩ := exists_pow_conj_eq h hcomm hqW
  have hpow : ∀ k : ℕ, ∀ w ∈ W,
      q ^ k * w * (q ^ k)⁻¹ = c ^ (j * k) * w * (c ^ (j * k))⁻¹ := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have e1 : q ^ (k + 1) * w * (q ^ (k + 1))⁻¹ = q * (q ^ k * w * (q ^ k)⁻¹) * q⁻¹ := by
        rw [pow_succ']; group
      rw [e1, ih w hw, CommutesOn.pow_conj h hcomm (j * k) w hw, hj w hw]
      have : c ^ (j * (k + 1)) = c ^ (j * k) * c ^ j := by rw [mul_add, mul_one, pow_add]
      rw [this]; group
  have hcen : ∀ u ∈ W, c ^ ((j * 2 ^ m : ℕ) : ℤ) * u * (c ^ ((j * 2 ^ m : ℕ) : ℤ))⁻¹ = u := by
    intro u hu
    rw [zpow_natCast]
    have := hpow (2 ^ m) u hu
    rw [hm] at this
    simpa using this.symm
  have h1 : c ^ ((j * 2 ^ m : ℕ) : ℤ) = 1 := h.zpow_c_eq_one_of_centralizes hcen
  rw [zpow_natCast] at h1
  have h2 : 3 ∣ j * 2 ^ m := by
    rw [← h.order_c]; exact orderOf_dvd_of_pow_eq_one h1
  have h3 : 3 ∣ j :=
    (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h2
  have h4 : c ^ j = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, h.order_c]; exact h3
  intro w hw
  rw [hj w hw, h4]; simp

theorem exists_mul_conj_inv_eq_of_fpf (h : A4Data X W c) {g : G}
    (hgW : ∀ w ∈ W, g * w * g⁻¹ ∈ W) (hfpf : ∀ w ∈ W, w ≠ 1 → g * w * g⁻¹ ≠ w) {w₁ : G}
    (hw₁ : w₁ ∈ W) : ∃ w₀ ∈ W, w₀ * (g * w₀⁻¹ * g⁻¹) = w₁ := by
  classical
  have hWfin : Finite W := h.finite_W
  let _ : CommGroup W := { (inferInstance : Group W) with
    mul_comm := fun a b => Subtype.ext (h.comm a a.2 b b.2) }
  let ψ : W →* W :=
    (((MulAut.conj g).toMonoidHom.comp W.subtype).codRestrict W (fun a => hgW a a.2))
  let φ : W →* W := MonoidHom.id W * ψ⁻¹
  have hφ : ∀ a : W, ((φ a : W) : G) = a * (g * a⁻¹ * g⁻¹) := fun a => by
    change (a : G) * ((ψ a)⁻¹ : W) = _
    simp [ψ, MulAut.conj_apply, mul_assoc]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : G) * (g * a⁻¹ * g⁻¹) = 1 := by rw [← hφ a, ha]; rfl
    by_contra hne
    have hne' : (a : G) ≠ 1 := fun h' => hne (Subtype.ext h')
    apply hfpf a a.2 hne'
    have h2 : g * (a : G)⁻¹ * g⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    calc g * (a : G) * g⁻¹ = (g * (a : G)⁻¹ * g⁻¹)⁻¹ := by group
      _ = a := by rw [h2, inv_inv]
  obtain ⟨⟨w₀, hw₀⟩, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨w₁, hw₁⟩
  refine ⟨w₀, hw₀, ?_⟩
  have := hφ ⟨w₀, hw₀⟩
  rw [hw] at this
  exact this.symm

theorem a4Data_conj (h : A4Data X W c) {w₀ : G} (hw₀ : w₀ ∈ W) :
    A4Data X W (w₀ * c * w₀⁻¹) where
  le := h.le
  card_W := h.card_W
  sq_eq_one := h.sq_eq_one
  comm := h.comm
  mem_X := X.mul_mem (X.mul_mem (h.le hw₀) h.mem_X) (X.inv_mem (h.le hw₀))
  order_c := by
    have := MulEquiv.orderOf_eq (MulAut.conj w₀) c
    rw [MulAut.conj_apply] at this
    rw [this]; exact h.order_c
  mem_normalizer :=
    mul_mem (mul_mem (Subgroup.le_normalizer hw₀) h.mem_normalizer)
      (inv_mem (Subgroup.le_normalizer hw₀))
  fpf := by
    intro w hw hw1 hfix
    apply h.fpf w hw hw1
    have hcw : c * w * c⁻¹ ∈ W := h.conj_mem hw
    have h1 : w₀⁻¹ * w * w₀ = w := by
      calc w₀⁻¹ * w * w₀ = w₀⁻¹ * (w * w₀) := by group
        _ = w₀⁻¹ * (w₀ * w) := by rw [h.comm w₀ hw₀ w hw]
        _ = w := by group
    have h2 : w₀ * (c * w * c⁻¹) * w₀⁻¹ = c * w * c⁻¹ := by
      calc w₀ * (c * w * c⁻¹) * w₀⁻¹ = (w₀ * (c * w * c⁻¹)) * w₀⁻¹ := by group
        _ = ((c * w * c⁻¹) * w₀) * w₀⁻¹ := by rw [h.comm w₀ hw₀ _ hcw]
        _ = c * w * c⁻¹ := by group
    have e : w₀ * c * w₀⁻¹ * w * (w₀ * c * w₀⁻¹)⁻¹ = c * w * c⁻¹ := by
      calc w₀ * c * w₀⁻¹ * w * (w₀ * c * w₀⁻¹)⁻¹
          = w₀ * (c * (w₀⁻¹ * w * w₀) * c⁻¹) * w₀⁻¹ := by group
        _ = w₀ * (c * w * c⁻¹) * w₀⁻¹ := by rw [h1]
        _ = c * w * c⁻¹ := h2
    rw [← e]; exact hfix
  eq_sup := by
    have hmem : w₀ * c * w₀⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (h.le hw₀) h.mem_X) (X.inv_mem (h.le hw₀))
    refine le_antisymm ?_ (sup_le h.le (zpowers_le.2 hmem))
    conv_lhs => rw [h.eq_sup]
    refine sup_le le_sup_left (zpowers_le.2 ?_)
    have hm : w₀⁻¹ * (w₀ * c * w₀⁻¹) * w₀ ∈ W ⊔ zpowers (w₀ * c * w₀⁻¹) :=
      mul_mem (mul_mem (inv_mem (Subgroup.mem_sup_left hw₀))
        (Subgroup.mem_sup_right (mem_zpowers _))) (Subgroup.mem_sup_left hw₀)
    have e : w₀⁻¹ * (w₀ * c * w₀⁻¹) * w₀ = c := by group
    rwa [e] at hm
  card_X := h.card_X
  center := h.center

theorem exists_fixed_conj {S : Set G} (hS : S.ncard = 4) {g : G} (hg3 : g ^ 3 = 1)
    (hmap : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : ∃ s ∈ S, g * s * g⁻¹ = s := by
  classical
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have : Fintype S := hfin.fintype
  let f : Function.End S := fun s => ⟨g * s * g⁻¹, hmap s s.2⟩
  have hfn : ∀ n : ℕ, ∀ s : S, (((f ^ n) s : S) : G) = g ^ n * s * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro s; show (s : G) = _; simp
    | succ n ih =>
      intro s
      rw [pow_succ']
      show (((f ((f ^ n) s)) : S) : G) = _
      show g * (((f ^ n) s : S) : G) * g⁻¹ = _
      rw [ih s, pow_succ']; group
  have hf : f ^ 3 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    rw [pow_one, hfn, hg3]
    simp
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have hcard : Fintype.card S = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact hS
  by_contra hno
  have hempty : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    apply hno
    refine ⟨s, s.2, ?_⟩
    have := congrArg Subtype.val hs
    exact this
  rw [hcard, hempty] at hmod
  revert hmod
  decide

end CFSG.Quasithin.S14110.Commute
