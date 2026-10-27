module

public import CFSG.Quasithin.EmptyFaithful.SBc6Sl2
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin CFSG.QuasithinUnique

namespace L2Borel

open CFSG.Quasithin.SBc5SL2 Matrix

variable {F : Type} [Field F]

theorem coe_xm' (t : F) : ((xm t : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem coe_dm' (c : Fˣ) :
    ((dm c : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] := rfl

theorem entry00_mul {g h : SL2 F} (hh : h ∈ Tplus F) :
    ((g * h : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have hh' : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hh
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh']

theorem entry00_xm_dm (t : F) (c : Fˣ) :
    ((xm t * dm c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_xm', coe_dm']
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mem_Uplus_of_entry00 {g : SL2 F} (hg : g ∈ Tplus F)
    (h1 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) : g ∈ Uplus F := by
  obtain ⟨t, c, rfl⟩ := (mem_Tplus_iff).mp hg
  rw [entry00_xm_dm] at h1
  have hc : c = 1 := Units.ext h1
  subst hc
  refine ⟨t, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_xm', coe_dm']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dm_conj_xm (c : Fˣ) (s : F) : dm c * xm s * (dm c)⁻¹ = xm ((c : F) ^ 2 * s) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, coe_xm', coe_dm', coe_xm']
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem xm_comm (s t : F) : xm t * xm s = xm s * xm t := by
  rw [xm_mul, xm_mul, add_comm]

theorem eq_one_of_sq [CharP F 2] {c : F} (h : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h0 : (c - 1) ^ 2 = 0 := by linear_combination h - (c - 1) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)

theorem entry_of_order_three [CharP F 2] {t : F} {c : Fˣ} (h3 : (xm t * dm c) ^ 3 = 1)
    (h1 : xm t * dm c ≠ 1) : (c : F) ^ 3 = 1 ∧ (c : F) ≠ 1 := by
  have hT : xm t * dm c ∈ Tplus F := (mem_Tplus_iff).mpr ⟨t, c, rfl⟩
  have h00 : ((xm t * dm c : SL2 F) ^ 3 : SL2 F) 0 0 = (c : F) ^ 3 := by
    rw [pow_three, entry00_mul (Subgroup.mul_mem _ hT hT), entry00_mul hT, entry00_xm_dm]
    ring
  refine ⟨?_, fun hc => h1 ?_⟩
  · rw [← h00, h3]
    simp
  · have hc1 : c = 1 := Units.ext hc
    subst hc1
    have hd : dm (1 : Fˣ) = (1 : SL2 F) := by
      ext i j
      rw [coe_dm']
      fin_cases i <;> fin_cases j <;> simp
    rw [hd, mul_one] at h3 ⊢
    have h2 : xm t * xm t = (1 : SL2 F) := by
      rw [xm_mul]
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have : t + t = 0 := by rw [← two_mul, h2, zero_mul]
      rw [this]
      ext i j
      rw [coe_xm']
      fin_cases i <;> fin_cases j <;> simp
    rw [pow_three, ← mul_assoc, h2, one_mul] at h3
    exact h3

theorem eq_one_of_conj_eq_model [CharP F 2] {x : SL2 F} (hx : x ∈ Tplus F) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {u : SL2 F} (hu : u ∈ Uplus F) (hxu : x * u * x⁻¹ = u) : u = 1 := by
  obtain ⟨t, c, rfl⟩ := (mem_Tplus_iff).mp hx
  obtain ⟨s, rfl⟩ := hu
  obtain ⟨-, hc1⟩ := entry_of_order_three hx3 hx1
  have e : xm t * dm c * xm s * (xm t * dm c)⁻¹ = xm ((c : F) ^ 2 * s) := by
    rw [_root_.mul_inv_rev, show xm t * dm c * xm s * ((dm c)⁻¹ * (xm t)⁻¹) =
        xm t * (dm c * xm s * (dm c)⁻¹) * (xm t)⁻¹ by group, dm_conj_xm, xm_comm,
      mul_inv_cancel_right]
  rw [e] at hxu
  have hs : (c : F) ^ 2 * s = s := by
    have := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hxu
    simpa [coe_xm'] using this
  have hc2 : (c : F) ^ 2 ≠ 1 := fun h => hc1 (eq_one_of_sq h)
  have hs0 : s = 0 := by
    have : ((c : F) ^ 2 - 1) * s = 0 := by rw [sub_mul, hs, one_mul, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hc2
    · exact h
  subst hs0
  ext i j
  rw [coe_xm']
  fin_cases i <;> fin_cases j <;> simp

theorem mul_mem_or_model [CharP F 2] {x x' : SL2 F} (hx : x ∈ Tplus F) (hx' : x' ∈ Tplus F)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hx'3 : x' ^ 3 = 1) (hx'1 : x' ≠ 1) :
    x' * x⁻¹ ∈ Uplus F ∨ x' * x ∈ Uplus F := by
  obtain ⟨t, c, rfl⟩ := (mem_Tplus_iff).mp hx
  obtain ⟨t', c', rfl⟩ := (mem_Tplus_iff).mp hx'
  obtain ⟨h3, h1⟩ := entry_of_order_three hx3 hx1
  obtain ⟨h3', h1'⟩ := entry_of_order_three hx'3 hx'1
  have hq : (c : F) ^ 2 + c + 1 = 0 := by
    have : ((c : F) - 1) * ((c : F) ^ 2 + c + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h1
    · exact h
  have hq' : (c' : F) ^ 2 + c' + 1 = 0 := by
    have : ((c' : F) - 1) * ((c' : F) ^ 2 + c' + 1) = 0 := by linear_combination h3'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h1'
    · exact h
  have hroot : ((c' : F) - c) * ((c' : F) - c ^ 2) = 0 := by
    linear_combination hq' - (c' : F) * hq + h3
  have hT : xm t * dm c ∈ Tplus F := (mem_Tplus_iff).mpr ⟨t, c, rfl⟩
  have hT' : xm t' * dm c' ∈ Tplus F := (mem_Tplus_iff).mpr ⟨t', c', rfl⟩
  have hinv00 : (((xm t * dm c)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (c : F) ^ 2 := by
    have h := entry00_mul (g := xm t * dm c) (Subgroup.inv_mem _ hT)
    rw [mul_inv_cancel, entry00_xm_dm] at h
    have h' : (1 : F) = c * (((xm t * dm c)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      simpa using h
    calc (((xm t * dm c)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0
        = (((xm t * dm c)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 * (c : F) ^ 3 := by
          rw [h3, mul_one]
      _ = (c * (((xm t * dm c)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0) * (c : F) ^ 2 := by
          ring
      _ = (c : F) ^ 2 := by rw [← h', one_mul]
  rcases mul_eq_zero.mp hroot with h | h
  · left
    refine mem_Uplus_of_entry00 (Subgroup.mul_mem _ hT' (Subgroup.inv_mem _ hT)) ?_
    rw [entry00_mul (Subgroup.inv_mem _ hT), entry00_xm_dm, hinv00, sub_eq_zero.mp h]
    have : (c : F) ^ 3 = 1 := h3
    linear_combination this
  · right
    refine mem_Uplus_of_entry00 (Subgroup.mul_mem _ hT' hT) ?_
    rw [entry00_mul hT, entry00_xm_dm, entry00_xm_dm, sub_eq_zero.mp h]
    have : (c : F) ^ 3 = 1 := h3
    linear_combination this

theorem isSylowTwoOf_top_comap {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    {Q : Subgroup B} (hQ : IsSylowTwoOf Q ⊤) : IsSylowTwoOf (Q.comap (φ : A →* B)) ⊤ := by
  have h := (SBd3T.isSylowTwoOf_map_iff (φ : A →* B) φ.injective (Q.comap (φ : A →* B)) ⊤).1
  rw [Subgroup.map_comap_eq_self_of_surjective φ.surjective,
    Subgroup.map_top_of_surjective _ φ.surjective] at h
  exact h hQ

theorem mem_normalizer_iff_of_conj {G : Type} [Group G] {Q U : Subgroup G} {g : G}
    (hg : ∀ x : G, x ∈ Q ↔ g⁻¹ * x * g ∈ U) (d : G) :
    d ∈ Subgroup.normalizer (Q : Set G) ↔ g⁻¹ * d * g ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have h1 := h (g * y * g⁻¹)
    simp only [hg] at h1
    have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    have e2 : g⁻¹ * (d * (g * y * g⁻¹) * d⁻¹) * g = (g⁻¹ * d * g) * y * (g⁻¹ * d * g)⁻¹ := by
      group
    rwa [e1, e2] at h1
  · intro h x
    simp only [hg]
    have h1 := h (g⁻¹ * x * g)
    have e2 : g⁻¹ * (d * x * d⁻¹) * g =
        (g⁻¹ * d * g) * (g⁻¹ * x * g) * (g⁻¹ * d * g)⁻¹ := by group
    rwa [e2]

theorem conj_pow' {G : Type} [Group G] (g x : G) (n : ℕ) :
    (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  have h := conj_pow (a := g⁻¹) (b := x) (i := n)
  rwa [inv_inv] at h

theorem exists_model {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X) {Q : Subgroup X}
    (hQ : IsSylowTwoOf Q ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : CharP F 2) (φ : SL2 F ≃* X) (g : SL2 F),
      (∀ x : X, x ∈ Q ↔ g⁻¹ * φ.symm x * g ∈ Uplus F) ∧
      (∀ x : X, x ∈ Subgroup.normalizer (Q : Set X) ↔ g⁻¹ * φ.symm x * g ∈ Tplus F) := by
  obtain ⟨F, hFf, hFfin, hFchar, hFcard, hn, ⟨φ⟩⟩ := SBc6.exists_sl2_equiv_of_psl hX
  classical
  have := Fintype.ofFinite F
  have hQ' := isSylowTwoOf_top_comap φ hQ
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_Uplus hn hFcard) hQ'
  have hQg : ∀ y : SL2 F, y ∈ Q.comap (φ : SL2 F →* X) ↔ g⁻¹ * y * g ∈ Uplus F := fun y => by
    rw [hg, B6.mem_conjSub]
  refine ⟨F, hFf, hFchar, φ, g, fun x => ?_, fun x => ?_⟩
  · rw [← hQg]
    simp
  · rw [← normalizer_Uplus, ← mem_normalizer_iff_of_conj hQg,
      ← Subgroup.comap_normalizer_eq_of_surjective Q φ.surjective]
    simp

theorem eq_one_of_conj_eq {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X) {Q : Subgroup X}
    (hQ : IsSylowTwoOf Q ⊤) {x : X} (hx : x ∈ Subgroup.normalizer (Q : Set X)) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) {u : X} (hu : u ∈ Q) (hxu : x * u * x⁻¹ = u) : u = 1 := by
  obtain ⟨F, _, _, φ, g, hQg, hNg⟩ := exists_model hX hQ
  have hy := (hNg x).mp hx
  have hy3 : (g⁻¹ * φ.symm x * g) ^ 3 = 1 := by
    rw [conj_pow', ← map_pow, hx3, map_one, mul_one, inv_mul_cancel]
  have hy1 : g⁻¹ * φ.symm x * g ≠ 1 := by
    intro h
    apply hx1
    have h2 : φ.symm x = 1 := by
      have : φ.symm x = g * (g⁻¹ * φ.symm x * g) * g⁻¹ := by group
      rw [this, h, mul_one, mul_inv_cancel]
    simpa using congrArg φ h2
  have hv := (hQg u).mp hu
  have hyv : (g⁻¹ * φ.symm x * g) * (g⁻¹ * φ.symm u * g) * (g⁻¹ * φ.symm x * g)⁻¹ =
      g⁻¹ * φ.symm u * g := by
    have e : (g⁻¹ * φ.symm x * g) * (g⁻¹ * φ.symm u * g) * (g⁻¹ * φ.symm x * g)⁻¹ =
        g⁻¹ * φ.symm (x * u * x⁻¹) * g := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e, hxu]
  have h1 := eq_one_of_conj_eq_model hy hy3 hy1 hv hyv
  have h2 : φ.symm u = 1 := by
    have : φ.symm u = g * (g⁻¹ * φ.symm u * g) * g⁻¹ := by group
    rw [this, h1, mul_one, mul_inv_cancel]
  simpa using congrArg φ h2

theorem mul_mem_or {X : Type} [Group X] {n : ℕ} (hX : IsPSL 2 2 n X) {Q : Subgroup X}
    (hQ : IsSylowTwoOf Q ⊤) {x x' : X} (hx : x ∈ Subgroup.normalizer (Q : Set X))
    (hx' : x' ∈ Subgroup.normalizer (Q : Set X)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hx'3 : x' ^ 3 = 1) (hx'1 : x' ≠ 1) : x' * x⁻¹ ∈ Q ∨ x' * x ∈ Q := by
  obtain ⟨F, _, _, φ, g, hQg, hNg⟩ := exists_model hX hQ
  have hne : ∀ z : X, z ≠ 1 → g⁻¹ * φ.symm z * g ≠ 1 := fun z hz h => hz (by
    have h2 : φ.symm z = 1 := by
      have : φ.symm z = g * (g⁻¹ * φ.symm z * g) * g⁻¹ := by group
      rw [this, h, mul_one, mul_inv_cancel]
    simpa using congrArg φ h2)
  have h3 : ∀ z : X, z ^ 3 = 1 → (g⁻¹ * φ.symm z * g) ^ 3 = 1 := fun z hz => by
    rw [conj_pow', ← map_pow, hz, map_one, mul_one, inv_mul_cancel]
  rcases mul_mem_or_model ((hNg x).mp hx) ((hNg x').mp hx') (h3 x hx3) (hne x hx1)
      (h3 x' hx'3) (hne x' hx'1) with h | h
  · left
    rw [hQg]
    have e : g⁻¹ * φ.symm (x' * x⁻¹) * g =
        (g⁻¹ * φ.symm x' * g) * (g⁻¹ * φ.symm x * g)⁻¹ := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact h
  · right
    rw [hQg]
    have e : g⁻¹ * φ.symm (x' * x) * g = (g⁻¹ * φ.symm x' * g) * (g⁻¹ * φ.symm x * g) := by
      rw [map_mul]
      group
    rw [e]
    exact h

end L2Borel

namespace L2Wt

variable {W : Type} [CommGroup W]

@[expose] def cmod (X : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup W where
  carrier := {w | ∀ x ∈ X, x w * w⁻¹ ∈ U}
  one_mem' := fun x _ => by simp
  mul_mem' := fun {a b} ha hb x hx => by
    have e : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv]
      ac_rfl
    show x (a * b) * (a * b)⁻¹ ∈ U
    rw [e]
    exact U.mul_mem (ha x hx) (hb x hx)
  inv_mem' := fun {a} ha x hx => by
    have e : x a⁻¹ * a⁻¹⁻¹ = (x a * a⁻¹)⁻¹ := by rw [map_inv, inv_inv, mul_inv, inv_inv]
    show x a⁻¹ * a⁻¹⁻¹ ∈ U
    rw [e]
    exact U.inv_mem (ha x hx)

theorem map_mem_cmod {X : Subgroup (MulAut W)} {U : Subgroup W} {h : MulAut W}
    (hU : ∀ w ∈ U, h w ∈ U) {w : W} (hw : w ∈ cmod X U) :
    h w ∈ cmod (X.map (MulAut.conj h).toMonoidHom) U := by
  rintro _ ⟨x, hx, rfl⟩
  have e : ((MulAut.conj h).toMonoidHom x) (h w) * (h w)⁻¹ = h (x w * w⁻¹) := by
    simp [MulAut.conj_apply, MulAut.mul_apply]
  rw [e]
  exact hU _ (hw x hx)

theorem false_of_sum {X₁ X₂ Hs : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x) (hX₁ : X₁ ≤ Hs) (hX₂ : X₂ ≤ Hs)
    (hperm : ∀ h ∈ Hs, (X₁.map (MulAut.conj h).toMonoidHom = X₁ ∧
        X₂.map (MulAut.conj h).toMonoidHom = X₂) ∨
      (X₁.map (MulAut.conj h).toMonoidHom = X₂ ∧ X₂.map (MulAut.conj h).toMonoidHom = X₁))
    {Wm : Subgroup W} (hWm : ∀ h ∈ Hs, ∀ w ∈ Wm, h w ∈ Wm)
    (hmax : ∀ Y : Subgroup W, Wm ≤ Y → (∀ h ∈ Hs, ∀ y ∈ Y, h y ∈ Y) → Y = Wm ∨ Y = ⊤)
    {Z : Subgroup W} (hZ : ¬ Z ≤ Wm) (hZWm : ∀ z ∈ Z, z ∈ Wm → z = 1)
    {a b u u' : MulAut W} (ha : a ∈ X₁) (hb : b ∈ X₂) (hu : u ∈ X₁) (hu' : u' ∈ X₂)
    (hab : ∀ z ∈ Z, (a * b) z = z) (huZ : ∀ z ∈ Z, u z = z) (hu'Z : ∀ z ∈ Z, u' z = z)
    (e f : ℕ) (hc : ∀ z ∈ Z, ((a ^ e * u) * (b ^ f * u')) z = z → z = 1)
    (hcZ : ∀ z ∈ Z, ((a ^ e * u) * (b ^ f * u')) z ∈ Z)
    {w₀ : W} (hw₀ : w₀ ∈ cmod X₂ Wm) (hw₀' : w₀ ∉ Wm) : False := by
  set Y₁ := cmod X₂ Wm with hY₁
  set Y₂ := cmod X₁ Wm with hY₂
  have hWY : ∀ {X : Subgroup (MulAut W)}, X ≤ Hs → Wm ≤ cmod X Wm := fun hX w hw x hx =>
    Wm.mul_mem (hWm x (hX hx) w hw) (Wm.inv_mem hw)
  have hinv : ∀ h ∈ Hs, (∀ y ∈ Y₁, h y ∈ Y₁) ∧ (∀ y ∈ Y₂, h y ∈ Y₂) ∨
      (∀ y ∈ Y₁, h y ∈ Y₂) ∧ (∀ y ∈ Y₂, h y ∈ Y₁) := by
    intro h hh
    rcases hperm h hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · have := map_mem_cmod (hWm h hh) hy
        rwa [h2] at this
      · have := map_mem_cmod (hWm h hh) hy
        rwa [h1] at this
    · right
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · have := map_mem_cmod (hWm h hh) hy
        rwa [h2] at this
      · have := map_mem_cmod (hWm h hh) hy
        rwa [h1] at this
  have hinvsup : ∀ h ∈ Hs, ∀ y ∈ Y₁ ⊔ Y₂, h y ∈ Y₁ ⊔ Y₂ := by
    intro h hh y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Subgroup.mem_sup.mp hy
    rw [map_mul]
    rcases hinv h hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (h1 y₁ hy₁))
        (Subgroup.mem_sup_right (h2 y₂ hy₂))
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (h1 y₁ hy₁))
        (Subgroup.mem_sup_left (h2 y₂ hy₂))
  have hsup : Y₁ ⊔ Y₂ = ⊤ := by
    rcases hmax (Y₁ ⊔ Y₂) ((hWY hX₂).trans le_sup_left) hinvsup with h | h
    · exact absurd (h ▸ (le_sup_left : Y₁ ≤ Y₁ ⊔ Y₂) hw₀) hw₀'
    · exact h
  have hX₁Y₁ : ∀ g ∈ X₁, ∀ y ∈ Y₁, g y ∈ Y₁ := fun g hg y hy x hx => by
    have e : x (g y) * (g y)⁻¹ = g (x y * y⁻¹) := by
      have := congrArg (fun φ : MulAut W => φ y) (hcomm g hg x hx)
      simp only [MulAut.mul_apply] at this
      rw [map_mul, map_inv, this]
    rw [e]
    exact hWm g (hX₁ hg) _ (hy x hx)
  have hX₂Y₂ : ∀ g ∈ X₂, ∀ y ∈ Y₂, g y ∈ Y₂ := fun g hg y hy x hx => by
    have e : x (g y) * (g y)⁻¹ = g (x y * y⁻¹) := by
      have := congrArg (fun φ : MulAut W => φ y) (hcomm x hx g hg)
      simp only [MulAut.mul_apply] at this
      rw [map_mul, map_inv, ← this]
    rw [e]
    exact hWm g (hX₂ hg) _ (hy x hx)
  have hX₁Y₂ : ∀ g ∈ X₁, ∀ y ∈ Y₂, g y ∈ Y₂ := fun g hg y hy x hx => by
    have h1 : g y * y⁻¹ ∈ Wm := hy g hg
    have h2 : g y ∈ Y₂ := by
      have : g y = (g y * y⁻¹) * y := by rw [inv_mul_cancel_right]
      rw [this]
      exact Y₂.mul_mem (hWY hX₁ h1) hy
    exact h2 x hx
  have hX₂Y₁ : ∀ g ∈ X₂, ∀ y ∈ Y₁, g y ∈ Y₁ := fun g hg y hy => by
    have h1 : g y * y⁻¹ ∈ Wm := hy g hg
    have : g y = (g y * y⁻¹) * y := by rw [inv_mul_cancel_right]
    rw [this]
    exact Y₁.mul_mem (hWY hX₂ h1) hy
  have hinvinf : ∀ h ∈ Hs, ∀ y ∈ Y₁ ⊓ Y₂, h y ∈ Y₁ ⊓ Y₂ := by
    intro h hh y hy
    rcases hinv h hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 y hy.1, h2 y hy.2⟩
    · exact ⟨h2 y hy.2, h1 y hy.1⟩
  have hinf : Y₁ ⊓ Y₂ = Wm := by
    rcases hmax (Y₁ ⊓ Y₂) (le_inf (hWY hX₂) (hWY hX₁)) hinvinf with h | h
    · exact h
    · exfalso
      apply hZ
      intro z hz
      have hz1 : z ∈ Y₁ := (h ▸ Subgroup.mem_top z : z ∈ Y₁ ⊓ Y₂).1
      have hz2 : z ∈ Y₂ := (h ▸ Subgroup.mem_top z : z ∈ Y₁ ⊓ Y₂).2
      have hb' : b ^ f * u' ∈ X₂ := X₂.mul_mem (X₂.pow_mem hb f) hu'
      have ha' : a ^ e * u ∈ X₁ := X₁.mul_mem (X₁.pow_mem ha e) hu
      have hbz : (b ^ f * u') z ∈ Y₂ := hX₂Y₂ _ hb' z hz2
      have hmem : ((a ^ e * u) * (b ^ f * u')) z * z⁻¹ ∈ Wm := by
        have e1 : ((a ^ e * u) * (b ^ f * u')) z * z⁻¹ =
            ((a ^ e * u) ((b ^ f * u') z) * ((b ^ f * u') z)⁻¹) * ((b ^ f * u') z * z⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [e1]
        exact Wm.mul_mem (hbz _ ha') (hz1 _ hb')
      have hZm : ((a ^ e * u) * (b ^ f * u')) z * z⁻¹ ∈ Z := Z.mul_mem (hcZ z hz) (Z.inv_mem hz)
      have h1 := hZWm _ hZm hmem
      have h2 : ((a ^ e * u) * (b ^ f * u')) z = z := by
        rw [← mul_inv_eq_one]
        exact h1
      rw [hc z hz h2]
      exact Wm.one_mem
  have hdec : ∀ y₁ ∈ Y₁, ∀ y₁' ∈ Y₁, ∀ y₂ ∈ Y₂, ∀ y₂' ∈ Y₂,
      (y₁ * y₂) * (y₁' * y₂')⁻¹ ∈ Wm → y₁ * y₁'⁻¹ ∈ Wm ∧ y₂ * y₂'⁻¹ ∈ Wm := by
    intro y₁ hy₁ y₁' hy₁' y₂ hy₂ y₂' hy₂' h
    have hd₁ : y₁ * y₁'⁻¹ ∈ Y₁ := Y₁.mul_mem hy₁ (Y₁.inv_mem hy₁')
    have hd₂ : y₂ * y₂'⁻¹ ∈ Y₂ := Y₂.mul_mem hy₂ (Y₂.inv_mem hy₂')
    have e1 : (y₁ * y₂) * (y₁' * y₂')⁻¹ = (y₁ * y₁'⁻¹) * (y₂ * y₂'⁻¹) := by
      rw [mul_inv]
      ac_rfl
    rw [e1] at h
    have h₁ : y₁ * y₁'⁻¹ ∈ Y₂ := by
      have : y₁ * y₁'⁻¹ = ((y₁ * y₁'⁻¹) * (y₂ * y₂'⁻¹)) * (y₂ * y₂'⁻¹)⁻¹ := by
        rw [mul_inv_cancel_right]
      rw [this]
      exact Y₂.mul_mem (hWY hX₁ h) (Y₂.inv_mem hd₂)
    have h₂ : y₂ * y₂'⁻¹ ∈ Y₁ := by
      have : y₂ * y₂'⁻¹ = (y₁ * y₁'⁻¹)⁻¹ * ((y₁ * y₁'⁻¹) * (y₂ * y₂'⁻¹)) := by
        rw [inv_mul_cancel_left]
      rw [this]
      exact Y₁.mul_mem (Y₁.inv_mem hd₁) (hWY hX₂ h)
    exact ⟨hinf ▸ ⟨hd₁, h₁⟩, hinf ▸ ⟨h₂, hd₂⟩⟩
  apply hZ
  intro z hz
  obtain ⟨y₁, hy₁, y₂, hy₂, hyz⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top z :
    z ∈ Y₁ ⊔ Y₂)
  have hfix₁ : ∀ g ∈ X₁, g z = z → g y₁ * y₁⁻¹ ∈ Wm := by
    intro g hg hgz
    have h1 := hdec (g y₁) (hX₁Y₁ g hg y₁ hy₁) y₁ hy₁ (g y₂) (hX₁Y₂ g hg y₂ hy₂) y₂ hy₂
      (by rw [← map_mul, hyz, hgz, mul_inv_cancel]; exact Wm.one_mem)
    exact h1.1
  have hfix₂ : ∀ g ∈ X₂, g z = z → g y₂ * y₂⁻¹ ∈ Wm := by
    intro g hg hgz
    have h1 := hdec (g y₁) (hX₂Y₁ g hg y₁ hy₁) y₁ hy₁ (g y₂) (hX₂Y₂ g hg y₂ hy₂) y₂ hy₂
      (by rw [← map_mul, hyz, hgz, mul_inv_cancel]; exact Wm.one_mem)
    exact h1.2
  have hab2 := hdec (a y₁) (hX₁Y₁ a ha y₁ hy₁) y₁ hy₁ (b y₂) (hX₂Y₂ b hb y₂ hy₂) y₂ hy₂ (by
    have hb1 : b y₁ * y₁⁻¹ ∈ Wm := hy₁ b hb
    have ha2 : a y₂ * y₂⁻¹ ∈ Wm := hy₂ a ha
    have habz := hab z hz
    rw [← hyz] at habz
    have e1 : (a y₁ * b y₂) * (y₁ * y₂)⁻¹ =
        ((a * b) (y₁ * y₂) * (y₁ * y₂)⁻¹) * (a (b y₁ * y₁⁻¹))⁻¹ * (b (a y₂ * y₂⁻¹))⁻¹ := by
      have hcab := congrArg (fun φ : MulAut W => φ y₂) (hcomm a ha b hb)
      simp only [MulAut.mul_apply] at hcab ⊢
      rw [map_mul, map_mul, map_mul, map_inv, map_mul, map_inv, hcab]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e1, habz, mul_inv_cancel, one_mul]
    exact Wm.mul_mem (Wm.inv_mem (hWm a (hX₁ ha) _ hb1)) (Wm.inv_mem (hWm b (hX₂ hb) _ ha2)))
  have hfm : ∀ {g g' : MulAut W} {w : W}, g ∈ Hs → g w * w⁻¹ ∈ Wm → g' w * w⁻¹ ∈ Wm →
      (g * g') w * w⁻¹ ∈ Wm := by
    intro g g' w hg h1 h2
    have e1 : (g * g') w * w⁻¹ = g (g' w * w⁻¹) * (g w * w⁻¹) := by
      rw [MulAut.mul_apply, map_mul, map_inv]
      group
    rw [e1]
    exact Wm.mul_mem (hWm g hg _ h2) h1
  have hfp : ∀ {g : MulAut W} {w : W}, g ∈ Hs → g w * w⁻¹ ∈ Wm → ∀ k : ℕ,
      (g ^ k) w * w⁻¹ ∈ Wm := by
    intro g w hg h k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ']
      exact hfm hg h ih
  have hfw : ∀ {g : MulAut W} {w w' : W}, g w * w⁻¹ ∈ Wm → g w' * w'⁻¹ ∈ Wm →
      g (w * w') * (w * w')⁻¹ ∈ Wm := by
    intro g w w' h1 h2
    have e1 : g (w * w') * (w * w')⁻¹ = (g w * w⁻¹) * (g w' * w'⁻¹) := by
      rw [map_mul, mul_inv]
      ac_rfl
    rw [e1]
    exact Wm.mul_mem h1 h2
  have ha' : a ^ e * u ∈ X₁ := X₁.mul_mem (X₁.pow_mem ha e) hu
  have hb' : b ^ f * u' ∈ X₂ := X₂.mul_mem (X₂.pow_mem hb f) hu'
  have h1 : (a ^ e * u) z * z⁻¹ ∈ Wm := by
    rw [← hyz]
    exact hfw (hfm (Hs.pow_mem (hX₁ ha) e) (hfp (hX₁ ha) hab2.1 e) (hfix₁ u hu (huZ z hz)))
      (hy₂ _ ha')
  have h2 : (b ^ f * u') z * z⁻¹ ∈ Wm := by
    rw [← hyz]
    exact hfw (hy₁ _ hb')
      (hfm (Hs.pow_mem (hX₂ hb) f) (hfp (hX₂ hb) hab2.2 f) (hfix₂ u' hu' (hu'Z z hz)))
  have h3 := hfm (hX₁ ha') h1 h2
  have h4 := hZWm _ (Z.mul_mem (hcZ z hz) (Z.inv_mem hz)) h3
  rw [hc z hz (mul_inv_eq_one.mp h4)]
  exact Wm.one_mem

end L2Wt

end CFSG.Quasithin.H13.A6
