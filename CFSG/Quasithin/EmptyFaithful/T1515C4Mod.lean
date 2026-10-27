module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.Quasithin

open scoped Pointwise

instance instFiniteMulAutOfFinite {V : Type*} [Group V] [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun f : MulAut V => (f : V → V)) (DFunLike.coe_injective (F := MulAut V))

section FourMod

variable {V : Type*} [CommGroup V]

@[expose] def fixOf (g : MulAut V) : Subgroup V where
  carrier := {v | g v = v}
  one_mem' := map_one g
  mul_mem' := fun {a b} ha hb => by
    show g (a * b) = a * b
    rw [map_mul, show g a = a from ha, show g b = b from hb]
  inv_mem' := fun {a} ha => by
    show g a⁻¹ = a⁻¹
    rw [map_inv, show g a = a from ha]

theorem mem_fixOf {g : MulAut V} {v : V} : v ∈ fixOf g ↔ g v = v := Iff.rfl

@[expose] def normOf (g : MulAut V) : V →* V where
  toFun v := v * g v * g (g v)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    ac_rfl

theorem normOf_apply (g : MulAut V) (v : V) : normOf g v = v * g v * g (g v) := rfl

theorem apply_cube_c4 {g : MulAut V} (hg : g ^ 3 = 1) (v : V) : g (g (g v)) = v := by
  have h3 : g * (g * g) = 1 := by
    have : g ^ 3 = g * (g * g) := by rw [pow_succ, pow_succ, pow_one, mul_assoc]
    rwa [this] at hg
  exact congrArg (fun φ : MulAut V => φ v) h3

theorem normOf_mem_fixOf {g : MulAut V} (hg : g ^ 3 = 1) (v : V) : normOf g v ∈ fixOf g := by
  rw [mem_fixOf, normOf_apply, map_mul, map_mul, apply_cube_c4 hg]
  ac_rfl

theorem normOf_apply_of_mem {g : MulAut V} (hsq : ∀ v : V, v * v = 1) {w : V} (hw : w ∈ fixOf g) :
    normOf g w = w := by
  have h1 : g w = w := hw
  rw [normOf_apply, h1, h1]
  calc w * w * w = (w * w) * w := rfl
    _ = w := by rw [hsq, one_mul]

theorem normOf_ker_apply {g : MulAut V} {w : V} (hw : w ∈ (normOf g).ker) :
    w * g w * g (g w) = 1 := hw

theorem fixOf_inf_ker {g : MulAut V} (hsq : ∀ v : V, v * v = 1) :
    fixOf g ⊓ (normOf g).ker = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have h1 := normOf_apply_of_mem hsq hw.1
  have h2 : normOf g w = 1 := hw.2
  rw [h1] at h2
  exact h2

theorem fixOf_sup_ker {g : MulAut V} (hg : g ^ 3 = 1) (hsq : ∀ v : V, v * v = 1) :
    fixOf g ⊔ (normOf g).ker = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hinv : ∀ x : V, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hn : g v * g (g v) ∈ (normOf g).ker := by
    show normOf g (g v * g (g v)) = 1
    rw [normOf_apply]
    simp only [map_mul]
    rw [apply_cube_c4 hg v]
    calc g v * g (g v) * (g (g v) * v) * (v * g v) = (v * v) * (g v * g v) * (g (g v) * g (g v)) := by
          ac_rfl
      _ = 1 := by rw [hsq v, hsq (g v), hsq (g (g v)), one_mul, one_mul]
  have hv : v = normOf g v * (g v * g (g v)) := by
    rw [normOf_apply]
    calc v = v * (1 : V) := (mul_one v).symm
      _ = v * ((g v * g v) * (g (g v) * g (g v))) := by rw [hsq (g v), hsq (g (g v)), one_mul]
      _ = v * g v * g (g v) * (g v * g (g v)) := by ac_rfl
  rw [hv]
  exact Subgroup.mul_mem_sup (normOf_mem_fixOf hg v) hn

theorem card_eq_fixOf_mul_ker [Finite V] {g : MulAut V} (hg : g ^ 3 = 1)
    (hsq : ∀ v : V, v * v = 1) :
    Nat.card V = Nat.card (fixOf g) * Nat.card (normOf g).ker := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixOf g) (normOf g).ker
    (fun x _ y _ => mul_comm x y)).1
  rw [fixOf_sup_ker hg hsq, fixOf_inf_ker hsq, Subgroup.card_top, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_modEq_fixOf [Finite V] {g : MulAut V} (hg : g ^ 3 = 1) :
    Nat.card V ≡ Nat.card (fixOf g) [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers g) := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hg, one_zpow]
  have h := hP.card_modEq_card_fixedPoints V
  have hc : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) = Nat.card (fixOf g) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hv
      exact hv ⟨g, Subgroup.mem_zpowers g⟩
    · intro hv m
      have hgv : g ∈ MulAction.stabilizer (MulAut V) v := hv
      have hm : (m : MulAut V) ∈ MulAction.stabilizer (MulAut V) v := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp m.2
        rw [← hn]
        exact (MulAction.stabilizer (MulAut V) v).zpow_mem hgv n
      exact hm
  rw [hc] at h
  exact h

theorem card_fixOf_dvd [Finite V] (g : MulAut V) : Nat.card (fixOf g) ∣ Nat.card V :=
  Subgroup.card_subgroup_dvd_card _

theorem fixOf_ne_top {g : MulAut V} (hg1 : g ≠ 1) : fixOf g ≠ ⊤ := by
  intro h
  apply hg1
  ext v
  have : v ∈ fixOf g := by rw [h]; trivial
  exact this

theorem card_fixOf_one_or_four [Finite V] {g : MulAut V} (hg : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hV : Nat.card V = 16) : Nat.card (fixOf g) = 1 ∨ Nat.card (fixOf g) = 4 := by
  have h1 := card_modEq_fixOf hg
  have h2 := card_fixOf_dvd g
  rw [hV] at h1 h2
  have h3 : Nat.card (fixOf g) ≠ 16 := by
    intro h16
    apply fixOf_ne_top hg1
    apply Subgroup.eq_top_of_card_eq
    rw [h16, hV]
  have h4 : Nat.card (fixOf g) ≤ 16 := Nat.le_of_dvd (by norm_num) h2
  have h5 : 0 < Nat.card (fixOf g) := Nat.card_pos
  unfold Nat.ModEq at h1
  interval_cases hc : Nat.card (fixOf g) <;> simp_all

theorem exists_fixOf_card_four [Finite V] {P : Subgroup (MulAut V)} (hP9 : Nat.card P = 9)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hV : Nat.card V = 16) :
    ∃ g ∈ P, g ≠ 1 ∧ Nat.card (fixOf g) = 4 := by
  by_contra hcon
  push Not at hcon
  have hfix : ∀ g ∈ P, g ≠ 1 → ∀ v : V, g v = v → v = 1 := by
    intro g hg hg1 v hv
    have h1 : Nat.card (fixOf g) = 1 := by
      rcases card_fixOf_one_or_four (hP3 g hg) hg1 hV with h | h
      · exact h
      · exact absurd h (hcon g hg hg1)
    have : fixOf g = ⊥ := Subgroup.card_eq_one.mp h1
    have hv' : v ∈ fixOf g := hv
    rw [this] at hv'
    exact hv'
  have hinj : ∀ v : V, v ≠ 1 → Function.Injective (fun x : P => (x : MulAut V) v) := by
    intro v hv x y hxy
    by_contra hne
    have hxy' : (x : MulAut V) v = (y : MulAut V) v := hxy
    have h1 : ((y : MulAut V)⁻¹ * (x : MulAut V)) v = v := by
      show (y : MulAut V)⁻¹ ((x : MulAut V) v) = v
      rw [hxy']
      simp
    have hmem : (y : MulAut V)⁻¹ * (x : MulAut V) ∈ P := P.mul_mem (P.inv_mem y.2) x.2
    by_cases h2 : (y : MulAut V)⁻¹ * (x : MulAut V) = 1
    · apply hne
      apply Subtype.ext
      exact (inv_mul_eq_one.mp h2).symm
    · exact hv (hfix _ hmem h2 v h1)
  have hcard : ∀ v : V, v ≠ 1 →
      (Set.range (fun x : P => (x : MulAut V) v)).ncard = 9 := by
    intro v hv
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (hinj v hv), hP9]
  have h1not : ∀ v : V, v ≠ 1 → (1 : V) ∉ Set.range (fun x : P => (x : MulAut V) v) := by
    rintro v hv ⟨x, hx⟩
    apply hv
    have : (x : MulAut V)⁻¹ ((x : MulAut V) v) = (x : MulAut V)⁻¹ 1 := by
      have hx' : (x : MulAut V) v = 1 := hx
      rw [hx']
    simpa using this
  obtain ⟨v, hv1⟩ : ∃ v : V, v ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card V = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  set S : Set V := Set.range (fun x : P => (x : MulAut V) v) with hS
  obtain ⟨w, hw1, hwS⟩ : ∃ w : V, w ≠ 1 ∧ w ∉ S := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set V) ⊆ S ∪ {1} := by
      intro w _
      by_cases hw : w = 1
      · right
        exact hw
      · left
        exact h w hw
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le S ({1} : Set V)
    rw [Set.ncard_univ, hV, Set.ncard_singleton, hcard v hv1] at *
    omega
  set S' : Set V := Set.range (fun x : P => (x : MulAut V) w) with hS'
  have hdisj : Disjoint S S' := by
    rw [Set.disjoint_left]
    rintro a ⟨x, hx⟩ ⟨y, hy⟩
    apply hwS
    have hx' : (x : MulAut V) v = a := hx
    have hy' : (y : MulAut V) w = a := hy
    refine ⟨y⁻¹ * x, ?_⟩
    show ((y⁻¹ * x : P) : MulAut V) v = w
    have : (y : MulAut V) w = (x : MulAut V) v := hy'.trans hx'.symm
    calc ((y⁻¹ * x : P) : MulAut V) v = (y : MulAut V)⁻¹ ((x : MulAut V) v) := rfl
      _ = (y : MulAut V)⁻¹ ((y : MulAut V) w) := by rw [this]
      _ = w := by simp
  have hdisj1 : Disjoint (S ∪ S') ({1} : Set V) := by
    rw [Set.disjoint_singleton_right]
    rintro (h | h)
    · exact h1not v hv1 h
    · exact h1not w hw1 h
  have hle := Set.ncard_le_ncard (Set.subset_univ (S ∪ S' ∪ {1})) (Set.toFinite _)
  rw [Set.ncard_univ, hV, Set.ncard_union_eq hdisj1 (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton,
    hcard v hv1, hcard w hw1] at hle
  omega

theorem apply_eq_of_mem_zpowers {h : MulAut V} {w : V} (hw : h w = w) {x : MulAut V}
    (hx : x ∈ Subgroup.zpowers h) : x w = w := by
  have hh : h ∈ MulAction.stabilizer (MulAut V) w := hw
  have : x ∈ MulAction.stabilizer (MulAut V) w := Subgroup.zpowers_le.mpr hh hx
  exact this

theorem fixOf_zpowers {g : MulAut V} {x : MulAut V} (hx : x ∈ Subgroup.zpowers g) :
    fixOf g ≤ fixOf x := fun _ hv => apply_eq_of_mem_zpowers hv hx

theorem apply_mem_ker_normOf {g x : MulAut V} (hxg : x * g = g * x) {w : V}
    (hw : w ∈ (normOf g).ker) : x w ∈ (normOf g).ker := by
  have hc : ∀ v : V, x (g v) = g (x v) := fun v => congrArg (fun φ : MulAut V => φ v) hxg
  have h1 : normOf g (x w) = x (normOf g w) := by
    rw [normOf_apply, normOf_apply, map_mul, map_mul, hc, hc, hc]
  show normOf g (x w) = 1
  rw [h1, show normOf g w = 1 from hw, map_one]

theorem card_pow_gen {g : MulAut V} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    Nat.card (Subgroup.zpowers g) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hg hg1

theorem exists_nat_pow_eq_zpow {x : MulAut V} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (m : ℤ) :
    ∃ i : ℕ, x ^ m = x ^ i := by
  have hord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  refine ⟨(m % (orderOf x : ℤ)).toNat, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [hord]; norm_num)),
    zpow_mod_orderOf]

theorem exists_pair [Finite V] {P : Subgroup (MulAut V)} (hP9 : Nat.card P = 9)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hV : Nat.card V = 16)
    (hsq : ∀ v : V, v * v = 1) :
    ∃ g ∈ P, ∃ h ∈ P, g ≠ 1 ∧ h ≠ 1 ∧ Nat.card (fixOf g) = 4 ∧ Nat.card (fixOf h) = 4 ∧
      fixOf g ⊓ fixOf h = ⊥ ∧ fixOf g ⊔ fixOf h = ⊤ ∧ (∀ x ∈ P, ∃ i j : ℕ, x = g ^ i * h ^ j) := by
  obtain ⟨g, hgP, hg1, hg4⟩ := exists_fixOf_card_four hP9 hP3 hV
  have hg3 := hP3 g hgP
  have hWc : Nat.card (normOf g).ker = 4 := by
    have := card_eq_fixOf_mul_ker hg3 hsq
    rw [hV, hg4] at this
    omega
  have hWinv : ∀ x ∈ P, ∀ w ∈ (normOf g).ker, x w ∈ (normOf g).ker := fun x hx w hw =>
    apply_mem_ker_normOf (hPc x hx g hgP) hw
  obtain ⟨w₀, hw₀W, hw₀1⟩ : ∃ w ∈ (normOf g).ker, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (normOf g).ker = ⊥ := by
      rw [eq_bot_iff]
      exact fun w hw => hcon w hw
    rw [this, Subgroup.card_bot] at hWc
    omega
  have hgw₀ : g w₀ ≠ w₀ := by
    intro h
    have : w₀ ∈ fixOf g ⊓ (normOf g).ker := ⟨h, hw₀W⟩
    rw [fixOf_inf_ker hsq, Subgroup.mem_bot] at this
    exact hw₀1 this
  have hOW : MulAction.orbit P w₀ ⊆ {w | w ∈ (normOf g).ker ∧ w ≠ 1} := by
    rintro _ ⟨x, rfl⟩
    refine ⟨hWinv x x.2 w₀ hw₀W, ?_⟩
    intro h1
    apply hw₀1
    have : (x : MulAut V)⁻¹ ((x : MulAut V) w₀) = (x : MulAut V)⁻¹ 1 := by
      have : (x : MulAut V) w₀ = 1 := h1
      rw [this]
    simpa using this
  have hWne : ({w | w ∈ (normOf g).ker ∧ w ≠ 1} : Set V).ncard = 3 := by
    have h1 : ({w | w ∈ (normOf g).ker ∧ w ≠ 1} : Set V) = ((normOf g).ker : Set V) \ {1} := by
      ext w
      simp
    rw [h1, Set.ncard_sdiff_singleton_of_mem (normOf g).ker.one_mem, ← Nat.card_coe_set_eq]
    show Nat.card (normOf g).ker - 1 = 3
    omega
  have hOS : Nat.card (MulAction.orbit P w₀) * Nat.card (MulAction.stabilizer P w₀) = 9 := by
    have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup P w₀)
    rwa [Nat.card_prod, hP9] at h
  have hOle : (MulAction.orbit P w₀).ncard ≤ 3 := by
    rw [← hWne]
    exact Set.ncard_le_ncard hOW (Set.toFinite _)
  have hOge : 2 ≤ (MulAction.orbit P w₀).ncard := by
    have hsub : ({w₀, g w₀} : Set V) ⊆ MulAction.orbit P w₀ := by
      intro a ha
      rcases ha with rfl | rfl
      · exact ⟨1, one_smul P a⟩
      · exact ⟨⟨g, hgP⟩, rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair (Ne.symm hgw₀)] at this
  have hOdvd : (MulAction.orbit P w₀).ncard ∣ 9 := by
    rw [← Nat.card_coe_set_eq]
    exact Dvd.intro _ hOS
  have hOcard : (MulAction.orbit P w₀).ncard = 3 := by
    generalize (MulAction.orbit P w₀).ncard = n at hOle hOge hOdvd
    interval_cases n <;> simp_all
  have hOeq : ∀ w ∈ (normOf g).ker, w ≠ 1 → w ∈ MulAction.orbit P w₀ := by
    have : MulAction.orbit P w₀ = {w | w ∈ (normOf g).ker ∧ w ≠ 1} :=
      Set.eq_of_subset_of_ncard_le hOW (by rw [hWne, hOcard]) (Set.toFinite _)
    intro w hw hw1
    rw [this]
    exact ⟨hw, hw1⟩
  have hStab : Nat.card (MulAction.stabilizer P w₀) = 3 := by
    have h3 : Nat.card (MulAction.orbit P w₀) = 3 := by rw [Nat.card_coe_set_eq]; exact hOcard
    rw [h3] at hOS
    omega
  obtain ⟨y, hy1⟩ : ∃ y : MulAction.stabilizer P w₀, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card (MulAction.stabilizer P w₀) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
    omega
  set h : MulAut V := ((y : P) : MulAut V) with hh
  have hhP : h ∈ P := (y : P).2
  have hh1 : h ≠ 1 := by
    intro h1
    apply hy1
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  have hh3 := hP3 h hhP
  have hhw₀ : h w₀ = w₀ := y.2
  have hhW : ∀ w ∈ (normOf g).ker, h w = w := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, map_one]
    · obtain ⟨x, hx⟩ := hOeq w hw hw1
      rw [← hx]
      show h ((x : MulAut V) w₀) = (x : MulAut V) w₀
      have hc : h * (x : MulAut V) = (x : MulAut V) * h := hPc h hhP x x.2
      calc h ((x : MulAut V) w₀) = ((h * (x : MulAut V)) w₀) := rfl
        _ = (((x : MulAut V) * h) w₀) := by rw [hc]
        _ = (x : MulAut V) (h w₀) := rfl
        _ = (x : MulAut V) w₀ := by rw [hhw₀]
  have hWh : (normOf g).ker ≤ fixOf h := fun w hw => hhW w hw
  have hh4 : Nat.card (fixOf h) = 4 := by
    rcases card_fixOf_one_or_four hh3 hh1 hV with h1 | h4
    · exfalso
      have := Subgroup.card_le_of_le hWh
      omega
    · exact h4
  have hWeq : fixOf h = (normOf g).ker :=
    (Subgroup.eq_of_le_of_card_ge hWh (by omega)).symm
  have hinf : fixOf g ⊓ fixOf h = ⊥ := by rw [hWeq]; exact fixOf_inf_ker hsq
  have hsup : fixOf g ⊔ fixOf h = ⊤ := by rw [hWeq]; exact fixOf_sup_ker hg3 hsq
  refine ⟨g, hgP, h, hhP, hg1, hh1, hg4, hh4, hinf, hsup, ?_⟩
  have hgc : ∀ x ∈ Subgroup.zpowers g, ∀ y ∈ Subgroup.zpowers h, x * y = y * x := by
    intro x hx y hy
    have hxP : x ∈ P := Subgroup.zpowers_le.mpr hgP hx
    have hyP : y ∈ P := Subgroup.zpowers_le.mpr hhP hy
    exact hPc x hxP y hyP
  have hbot : Subgroup.zpowers g ⊓ Subgroup.zpowers h = ⊥ := by
    set K := Subgroup.zpowers g ⊓ Subgroup.zpowers h with hK
    have hdvd : Nat.card K ∣ 3 := by
      rw [← card_pow_gen hg3 hg1]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hKg : K = Subgroup.zpowers g :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, card_pow_gen hg3 hg1])
      have hgK : g ∈ K := by rw [hKg]; exact Subgroup.mem_zpowers g
      have hgh : g ∈ Subgroup.zpowers h := hgK.2
      exact hgw₀ (apply_eq_of_mem_zpowers (hhW w₀ hw₀W) hgh)
  obtain ⟨hc9, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers g)
    (Subgroup.zpowers h) hgc
  rw [hbot, Subgroup.card_bot, mul_one, card_pow_gen hg3 hg1, card_pow_gen hh3 hh1] at hc9
  have hsupP : Subgroup.zpowers g ⊔ Subgroup.zpowers h ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr hgP) (Subgroup.zpowers_le.mpr hhP)
  have hsupeq : Subgroup.zpowers g ⊔ Subgroup.zpowers h = P :=
    Subgroup.eq_of_le_of_card_ge hsupP (by rw [hc9, hP9])
  intro x hx
  have hx' : x ∈ ((Subgroup.zpowers g ⊔ Subgroup.zpowers h : Subgroup (MulAut V)) :
      Set (MulAut V)) := by
    rw [hsupeq]
    exact hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  obtain ⟨i, hi⟩ := exists_nat_pow_eq_zpow hg3 hg1 m
  obtain ⟨j, hj⟩ := exists_nat_pow_eq_zpow hh3 hh1 n
  exact ⟨i, j, by rw [hi, hj]⟩

end FourMod

end CFSG.Quasithin
