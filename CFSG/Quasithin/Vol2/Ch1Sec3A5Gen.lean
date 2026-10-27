module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.L139A5

open Equiv Equiv.Perm

@[expose] def c5 : alternatingGroup (Fin 5) :=
  ⟨finRotate 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def s4 : Perm (Fin 5) := swap 1 3 * swap 1 4 * swap 1 2

theorem s4_conj : s4 * (c5 : Perm (Fin 5)) * s4⁻¹ = (c5 : Perm (Fin 5)) ^ 2 := by
  unfold s4 c5
  decide

theorem sign_s4 : sign s4 = -1 := by
  unfold s4
  decide

theorem c5_ne_one : c5 ≠ 1 := by
  intro h
  have : (finRotate 5 : Perm (Fin 5)) = 1 := congrArg Subtype.val h
  revert this
  decide

theorem c5_pow_five : c5 ^ 5 = 1 := by
  apply Subtype.ext
  show (finRotate 5 : Perm (Fin 5)) ^ 5 = 1
  decide

section Section

variable {X : Type*} [Group X]

@[expose] def stb (A N : Subgroup X) : Subgroup (MulAut X) where
  carrier := {β | (∀ x, β x ∈ A ↔ x ∈ A) ∧ ∀ x, β x ∈ N ↔ x ∈ N}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  mul_mem' {β γ} hβ hγ :=
    ⟨fun x => (hβ.1 (γ x)).trans (hγ.1 x), fun x => (hβ.2 (γ x)).trans (hγ.2 x)⟩
  inv_mem' {β} hβ := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have h := hβ.1 (β⁻¹ x)
      rw [MulAut.apply_inv_self] at h
      exact h.symm
    · have h := hβ.2 (β⁻¹ x)
      rw [MulAut.apply_inv_self] at h
      exact h.symm

variable {A N : Subgroup X}

theorem apply_mem_iff_of_maps [Finite X] {H : Subgroup X} {β : MulAut X}
    (h : ∀ x ∈ H, β x ∈ H) (x : X) : β x ∈ H ↔ x ∈ H := by
  have hle : H.map β.toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : H.map β.toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective β.injective])
  refine ⟨fun hx => ?_, h x⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := β.injective hyx
  rwa [← this]

theorem mem_stb_of_maps [Finite X] {β : MulAut X} (hA : ∀ x ∈ A, β x ∈ A)
    (hN : ∀ x ∈ N, β x ∈ N) : β ∈ stb A N :=
  ⟨apply_mem_iff_of_maps hA, apply_mem_iff_of_maps hN⟩

theorem conj_mem_stb (hNA : N ≤ A) [hN : (N.subgroupOf A).Normal] {a : X} (ha : a ∈ A) :
    MulAut.conj a ∈ stb A N := by
  have hA : ∀ {a : X}, a ∈ A → ∀ x ∈ N, a * x * a⁻¹ ∈ N := by
    intro a ha x hx
    have h := hN.conj_mem ⟨x, hNA hx⟩ hx ⟨a, ha⟩
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  refine ⟨fun x => ?_, fun x => ⟨fun hx => ?_, fun hx => hA ha x hx⟩⟩
  · rw [MulAut.conj_apply]
    refine ⟨fun hx => ?_, fun hx => mul_mem (mul_mem ha hx) (inv_mem ha)⟩
    have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem ha) hx) ha
  · rw [MulAut.conj_apply] at hx
    have h := hA (inv_mem ha) _ hx
    have e1 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e1] at h

@[expose] def conjOn (β : stb A N) : ↥A ≃* ↥A where
  toFun a := ⟨(β : MulAut X) a, (β.2.1 a).mpr a.2⟩
  invFun a := ⟨(β : MulAut X)⁻¹ a, ((inv_mem β.2).1 a).mpr a.2⟩
  left_inv a := by ext; simp
  right_inv a := by ext; simp
  map_mul' a b := by ext; simp

@[simp]
theorem conjOn_apply (β : stb A N) (a : ↥A) : ((conjOn β a : ↥A) : X) = (β : MulAut X) a := rfl

theorem conjOn_map (β : stb A N) :
    (N.subgroupOf A).map ((conjOn β : ↥A ≃* ↥A) : ↥A →* ↥A) = N.subgroupOf A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (β.2.2 y).mpr hy
  · intro hx
    refine ⟨(conjOn β).symm x, ?_, (conjOn β).apply_symm_apply x⟩
    exact ((inv_mem β.2).2 x).mpr hx

variable [hN : (N.subgroupOf A).Normal]

@[expose] noncomputable def secRho : stb A N →* MulAut (↥A ⧸ N.subgroupOf A) where
  toFun β := QuotientGroup.congr _ _ (conjOn β) (conjOn_map β)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [QuotientGroup.congr_mk]
      congr 1
  map_mul' β₁ β₂ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H a =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      congr 1

theorem secRho_mk (β : stb A N) (a : ↥A) :
    secRho β (a : ↥A ⧸ N.subgroupOf A) = ((conjOn β a : ↥A) : ↥A ⧸ N.subgroupOf A) :=
  QuotientGroup.congr_mk _ _ (conjOn β) (conjOn_map β) a

@[expose] noncomputable def autA5 : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))

@[expose] noncomputable def secPi (e : (↥A ⧸ N.subgroupOf A) ≃* alternatingGroup (Fin 5)) :
    stb A N →* Perm (Fin 5) :=
  autA5.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp secRho)

variable (e : (↥A ⧸ N.subgroupOf A) ≃* alternatingGroup (Fin 5))

theorem secPi_spec (β : stb A N) (x : ↥A ⧸ N.subgroupOf A) :
    ((e (secRho β x) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      secPi e β * (e x : Perm (Fin 5)) * (secPi e β)⁻¹ := by
  have h : autA5 (secPi e β) = MulAut.congr e (secRho β) := by
    simp [secPi]
  have h2 := congrArg (fun φ : MulAut (alternatingGroup (Fin 5)) => (φ (e x) : Perm (Fin 5))) h
  simp only [autA5, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply] at h2
  rw [h2]
  simp [MulAut.congr_apply]

theorem secPi_conj (hNA : N ≤ A) (a : X) (ha : a ∈ A) :
    secPi e ⟨MulAut.conj a, conj_mem_stb hNA ha⟩ =
      ((e ((⟨a, ha⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
  apply autA5.injective
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := e.surjective y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  apply Subtype.ext
  have h1 := secPi_spec e ⟨MulAut.conj a, conj_mem_stb hNA ha⟩ (b : ↥A ⧸ N.subgroupOf A)
  rw [secRho_mk] at h1
  simp only [autA5, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply]
  rw [← h1]
  have hconj : ((conjOn ⟨MulAut.conj a, conj_mem_stb hNA ha⟩ b : ↥A) : ↥A ⧸ N.subgroupOf A) =
      (⟨a, ha⟩ : ↥A) * (b : ↥A ⧸ N.subgroupOf A) * ((⟨a, ha⟩ : ↥A) : ↥A ⧸ N.subgroupOf A)⁻¹ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
  rw [hconj, map_mul, map_mul, map_inv]
  rfl

theorem mem_of_secPi_eq_one {β : stb A N} (h : secPi e β = 1) (x : X) (hx : x ∈ A) :
    ((β : MulAut X) x)⁻¹ * x ∈ N := by
  have h1 := secPi_spec e β ((⟨x, hx⟩ : ↥A) : ↥A ⧸ N.subgroupOf A)
  rw [h, one_mul, inv_one, mul_one, secRho_mk] at h1
  have h2 := e.injective (Subtype.ext h1)
  rw [QuotientGroup.eq] at h2
  exact h2

theorem exists_inner_sec (e : (↥A ⧸ N.subgroupOf A) ≃* alternatingGroup (Fin 5)) (hNA : N ≤ A)
    {β : MulAut X} (hβ : β ∈ stb A N)
    (hno : ∀ γ ∈ stb A N, ∀ a ∈ A, a ∉ N → a ^ 5 ∈ N → (γ a)⁻¹ * a ^ 2 ∉ N) :
    ∃ ℓ ∈ A, ∀ x ∈ A, (β x)⁻¹ * (ℓ * x * ℓ⁻¹) ∈ N := by
  have heven : ∀ σ : Perm (Fin 5), sign σ = 1 →
      ∃ (y : X) (hy : y ∈ A), secPi e ⟨MulAut.conj y, conj_mem_stb hNA hy⟩ = σ := by
    intro σ hσ
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
    refine ⟨b, b.2, ?_⟩
    rw [secPi_conj e hNA b b.2]
    have : ((⟨(b : X), b.2⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) = e.symm ⟨σ, hσ⟩ := hb
    rw [this, MulEquiv.apply_symm_apply]
  have hsign : sign (secPi e ⟨β, hβ⟩) = 1 := by
    by_contra hodd
    have hodd' : sign (secPi e ⟨β, hβ⟩) = -1 := by
      rcases Int.units_eq_one_or (sign (secPi e ⟨β, hβ⟩)) with h | h
      · exact absurd h hodd
      · exact h
    obtain ⟨y, hy, hyπ⟩ := heven (s4 * (secPi e ⟨β, hβ⟩)⁻¹) (by
      rw [map_mul, map_inv, sign_s4, hodd']
      decide)
    set γ : stb A N := ⟨MulAut.conj y, conj_mem_stb hNA hy⟩ * ⟨β, hβ⟩ with hγ
    have hπγ : secPi e γ = s4 := by
      rw [hγ, map_mul, hyπ, inv_mul_cancel_right]
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm c5)
    set a : X := (b : X) with ha
    have haA : a ∈ A := b.2
    have hbmk : ((⟨a, haA⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) = e.symm c5 := hb
    have ha1 : a ∉ N := by
      intro haN
      apply c5_ne_one
      have h1 : ((⟨a, haA⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr haN
      rw [hbmk] at h1
      rw [← e.apply_symm_apply c5, h1, map_one]
    have ha5 : a ^ 5 ∈ N := by
      have h1 : ((⟨a, haA⟩ ^ 5 : ↥A) : ↥A ⧸ N.subgroupOf A) = 1 := by
        rw [QuotientGroup.mk_pow, hbmk, ← map_pow, c5_pow_five, map_one]
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_subgroupOf] at h2
      simpa using h2
    apply hno γ γ.2 a haA ha1 ha5
    have hmem1 : (γ : MulAut X) a ∈ A := (γ.2.1 a).mpr haA
    have key : ((⟨(γ : MulAut X) a, hmem1⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) =
        ((⟨a, haA⟩ ^ 2 : ↥A) : ↥A ⧸ N.subgroupOf A) := by
      apply e.injective
      apply Subtype.ext
      have h1 := secPi_spec e γ ((⟨a, haA⟩ : ↥A) : ↥A ⧸ N.subgroupOf A)
      rw [secRho_mk] at h1
      have e1 : ((conjOn γ ⟨a, haA⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) =
          ((⟨(γ : MulAut X) a, hmem1⟩ : ↥A) : ↥A ⧸ N.subgroupOf A) := rfl
      rw [e1] at h1
      rw [h1, hπγ, hbmk, MulEquiv.apply_symm_apply, s4_conj, QuotientGroup.mk_pow, map_pow,
        hbmk, MulEquiv.apply_symm_apply]
      rfl
    rw [QuotientGroup.eq] at key
    exact key
  obtain ⟨ℓ, hℓ, hℓπ⟩ := heven (secPi e ⟨β, hβ⟩) hsign
  refine ⟨ℓ, hℓ, fun x hx => ?_⟩
  set w : stb A N := ⟨MulAut.conj ℓ, conj_mem_stb hNA hℓ⟩⁻¹ * ⟨β, hβ⟩ with hw
  have hk : secPi e w = 1 := by
    rw [hw, map_mul, map_inv, hℓπ, inv_mul_cancel]
  have hc := mem_of_secPi_eq_one e hk x hx
  have hwx : (w : MulAut X) x = ℓ⁻¹ * β x * ℓ := by
    rw [hw]
    simp
  rw [hwx] at hc
  have hcN := ((conj_mem_stb hNA hℓ).2 _).mpr hc
  have e1 : MulAut.conj ℓ ((ℓ⁻¹ * β x * ℓ)⁻¹ * x) = (β x)⁻¹ * (ℓ * x * ℓ⁻¹) := by
    rw [MulAut.conj_apply]
    group
  rwa [e1] at hcN

end Section

@[expose] def A5SecInner (X : Type*) [Group X] : Prop :=
  ∀ (A N : Subgroup X) [(N.subgroupOf A).Normal], N ≤ A → IsPGroup 2 ↥N →
    Nonempty ((↥A ⧸ N.subgroupOf A) ≃* alternatingGroup (Fin 5)) →
    ∀ β : MulAut X, (∀ x ∈ A, β x ∈ A) → (∀ x ∈ N, β x ∈ N) →
      ∃ a ∈ A, ∀ x ∈ A, (β x)⁻¹ * (a * x * a⁻¹) ∈ N

section Orders

variable {Q : Type*} [Group Q]

theorem aut_pow_apply {ρ : MulAut Q} {b : Q} (hρ : ρ b = b ^ 2) (k : ℕ) :
    (ρ ^ k) b = b ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, map_pow, hρ, ← pow_mul, pow_succ, mul_comm]

theorem four_dvd_of_two_pow_mod_five {n : ℕ} (h : 2 ^ n % 5 = 1) : 4 ∣ n := by
  have hmod : ∀ q r : ℕ, 2 ^ (4 * q + r) % 5 = 2 ^ r % 5 := by
    intro q r
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have := hmod (n / 4) (n % 4)
  rw [Nat.div_add_mod] at this
  rw [this] at h
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h0 : n % 4 = 0 := by
    interval_cases hn : n % 4 <;> simp_all
  omega

theorem four_dvd_orderOf_of_aut {ρ : MulAut Q} {b : Q} (hb : orderOf b = 5) (hρ : ρ b = b ^ 2) :
    4 ∣ orderOf ρ := by
  have h := aut_pow_apply hρ (orderOf ρ)
  rw [pow_orderOf_eq_one, MulAut.one_apply] at h
  have h2 : b ^ 1 = b ^ (2 ^ orderOf ρ) := by rw [pow_one]; exact h
  rw [pow_eq_pow_iff_modEq, hb] at h2
  apply four_dvd_of_two_pow_mod_five
  have := h2.symm
  unfold Nat.ModEq at this
  rw [this]

theorem exists_orderOf_eq_four {W : Type*} [Group W] {γ : W} (hfin : IsOfFinOrder γ)
    (h : 4 ∣ orderOf γ) : ∃ δ : W, orderOf δ = 4 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨γ ^ k, ?_⟩
  have hpos : 0 < orderOf γ := hfin.orderOf_pos
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      omega
    · exact h0
  rw [orderOf_pow' γ hk0.ne', hk, Nat.gcd_mul_left_left]
  exact Nat.mul_div_cancel _ hk0

end Orders

end CFSG.Quasithin.L139A5
