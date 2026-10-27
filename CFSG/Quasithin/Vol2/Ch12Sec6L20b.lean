module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126N S126L20 S126L20a Equiv

namespace S126L20b

theorem xor_xor_self : ∀ x k : Fin 8, (x ^^^ k) ^^^ k = x := by
  decide

theorem zero_xor' : ∀ k : Fin 8, 0 ^^^ k = k := by
  decide

theorem xor_zero' : ∀ k : Fin 8, k ^^^ 0 = k := by
  decide

theorem xor_self' : ∀ k : Fin 8, k ^^^ k = 0 := by
  decide

theorem xor_assoc' : ∀ x k l : Fin 8, (x ^^^ l) ^^^ k = x ^^^ (k ^^^ l) := by
  decide

theorem xor_eq_zero' : ∀ x y : Fin 8, x ^^^ y = 0 → x = y := by
  decide

@[expose] def xt (k : Fin 8) : Perm (Fin 8) where
  toFun x := x ^^^ k
  invFun x := x ^^^ k
  left_inv x := xor_xor_self x k
  right_inv x := xor_xor_self x k

theorem xt_apply (k x : Fin 8) : xt k x = x ^^^ k := rfl

theorem xt_mul (k l : Fin 8) : xt k * xt l = xt (k ^^^ l) :=
  Equiv.ext fun x => xor_assoc' x k l

theorem xt_zero : xt 0 = 1 :=
  Equiv.ext fun x => xor_zero' x

theorem xt_inv (k : Fin 8) : (xt k)⁻¹ = xt k := by
  rw [inv_eq_iff_mul_eq_one, xt_mul, xor_self', xt_zero]

theorem xt_apply_zero (k : Fin 8) : xt k 0 = k := zero_xor' k

theorem sign_xt : ∀ k : Fin 8, Perm.sign (xt k) = 1 := by
  decide

theorem xt_mem_A8 (k : Fin 8) : xt k ∈ alternatingGroup (Fin 8) :=
  Perm.mem_alternatingGroup.2 (sign_xt k)

@[expose] def B0 : Subgroup (Perm (Fin 8)) where
  carrier := {σ | ∃ k, σ = xt k}
  one_mem' := ⟨0, xt_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨k, rfl⟩ ⟨l, rfl⟩
    exact ⟨k ^^^ l, xt_mul k l⟩
  inv_mem' := by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, xt_inv k⟩

theorem xt_mem (k : Fin 8) : xt k ∈ B0 := ⟨k, rfl⟩

theorem B0_le_A8 : B0 ≤ alternatingGroup (Fin 8) := by
  rintro _ ⟨k, rfl⟩
  exact xt_mem_A8 k

section Regular

variable {b₁ b₂ b₃ : Perm (Fin 8)}

@[expose] def wd (b₁ b₂ b₃ : Perm (Fin 8)) (x : Fin 8) : Perm (Fin 8) :=
  b₁ ^ (x.val % 2) * b₂ ^ (x.val / 2 % 2) * b₃ ^ (x.val / 4 % 2)

theorem xor_bits : ∀ x k : Fin 8, (x ^^^ k).val % 2 = (k.val % 2 + x.val % 2) % 2 ∧
    (x ^^^ k).val / 2 % 2 = (k.val / 2 % 2 + x.val / 2 % 2) % 2 ∧
    (x ^^^ k).val / 4 % 2 = (k.val / 4 % 2 + x.val / 4 % 2) % 2 := by
  decide

theorem pow_mod_two {b : Perm (Fin 8)} (hb : b * b = 1) (n : ℕ) : b ^ n = b ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, pow_two, hb, one_pow, one_mul]

theorem pow_mul_pow_mod {b : Perm (Fin 8)} (hb : b * b = 1) (a c : ℕ) :
    b ^ a * b ^ c = b ^ ((a + c) % 2) := by
  rw [← pow_add, pow_mod_two hb]

theorem wd_mul (h1 : b₁ * b₁ = 1) (h2 : b₂ * b₂ = 1) (h3 : b₃ * b₃ = 1)
    (h12 : Commute b₁ b₂) (h13 : Commute b₁ b₃) (h23 : Commute b₂ b₃) (k x : Fin 8) :
    wd b₁ b₂ b₃ k * wd b₁ b₂ b₃ x = wd b₁ b₂ b₃ (x ^^^ k) := by
  have c1 : Commute (b₃ ^ (k.val / 4 % 2)) (b₁ ^ (x.val % 2) * b₂ ^ (x.val / 2 % 2)) :=
    (h13.symm.pow_pow _ _).mul_right (h23.symm.pow_pow _ _)
  have c2 : Commute (b₂ ^ (k.val / 2 % 2)) (b₁ ^ (x.val % 2)) := h12.symm.pow_pow _ _
  obtain ⟨e1, e2, e3⟩ := xor_bits x k
  simp only [wd]
  rw [c1.mul_mul_mul_comm, c2.mul_mul_mul_comm, pow_mul_pow_mod h1, pow_mul_pow_mod h2,
    pow_mul_pow_mod h3, e1, e2, e3]

theorem wd_one : wd b₁ b₂ b₃ 1 = b₁ := by
  show b₁ ^ 1 * b₂ ^ 0 * b₃ ^ 0 = b₁
  rw [pow_one, pow_zero, pow_zero, mul_one, mul_one]

theorem wd_two : wd b₁ b₂ b₃ 2 = b₂ := by
  show b₁ ^ 0 * b₂ ^ 1 * b₃ ^ 0 = b₂
  rw [pow_one, pow_zero, pow_zero, mul_one, one_mul]

theorem wd_three : wd b₁ b₂ b₃ 3 = b₁ * b₂ := by
  show b₁ ^ 1 * b₂ ^ 1 * b₃ ^ 0 = b₁ * b₂
  rw [pow_one, pow_one, pow_zero, mul_one]

theorem wd_four : wd b₁ b₂ b₃ 4 = b₃ := by
  show b₁ ^ 0 * b₂ ^ 0 * b₃ ^ 1 = b₃
  rw [pow_one, pow_zero, pow_zero, mul_one, one_mul]

theorem wd_five : wd b₁ b₂ b₃ 5 = b₁ * b₃ := by
  show b₁ ^ 1 * b₂ ^ 0 * b₃ ^ 1 = b₁ * b₃
  rw [pow_one, pow_one, pow_zero, mul_one]

theorem wd_six : wd b₁ b₂ b₃ 6 = b₂ * b₃ := by
  show b₁ ^ 0 * b₂ ^ 1 * b₃ ^ 1 = b₂ * b₃
  rw [pow_one, pow_one, pow_zero, one_mul]

theorem wd_seven : wd b₁ b₂ b₃ 7 = b₁ * b₂ * b₃ := by
  show b₁ ^ 1 * b₂ ^ 1 * b₃ ^ 1 = b₁ * b₂ * b₃
  rw [pow_one, pow_one, pow_one]

end Regular

theorem exists_conj_B0 {B : Subgroup (Perm (Fin 8))} (h8 : 8 ≤ Nat.card B)
    (hfpf : ∀ σ ∈ B, σ ≠ 1 → ∀ i, σ i ≠ i) (hinv : ∀ σ ∈ B, σ * σ = 1)
    (hcomm : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ) :
    ∃ τ : Perm (Fin 8), ∀ σ, σ ∈ B ↔ τ⁻¹ * σ * τ ∈ B0 := by
  have hsr : ∀ σ ∈ B, ∀ σ' ∈ B, σ 0 = σ' 0 → σ = σ' := by
    intro σ hσ σ' hσ' h
    by_contra hne
    have h1 : σ'⁻¹ * σ ≠ 1 := fun h' => hne (inv_mul_eq_one.1 h').symm
    exact hfpf _ (B.mul_mem (B.inv_mem hσ') hσ) h1 0
      (by rw [Perm.mul_apply, h, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply])
  have hsurj : ∀ k : Fin 8, ∃ σ ∈ B, σ 0 = k := by
    have hinj : Function.Injective fun σ : ↥B => (σ : Perm (Fin 8)) 0 :=
      fun σ σ' h => Subtype.ext (hsr _ σ.2 _ σ'.2 h)
    have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; exact h8)
    intro k
    obtain ⟨σ, hσ⟩ := hbij.2 k
    exact ⟨σ, σ.2, hσ⟩
  have hinv' : ∀ σ ∈ B, ∀ i, σ (σ i) = i := fun σ hσ i => by
    rw [← Perm.mul_apply, hinv σ hσ, Perm.one_apply]
  obtain ⟨b₁, hb₁, hb₁0⟩ := hsurj 1
  obtain ⟨b₂, hb₂, hb₂0⟩ := hsurj 2
  set k₃ : Fin 8 := if b₁ 2 = 3 then 4 else 3 with hk₃
  obtain ⟨b₃, hb₃, hb₃0⟩ := hsurj k₃
  have hk0 : k₃ ≠ 0 := by rw [hk₃]; split_ifs <;> decide
  have hk1 : k₃ ≠ 1 := by rw [hk₃]; split_ifs <;> decide
  have hk2 : k₃ ≠ 2 := by rw [hk₃]; split_ifs <;> decide
  have hkb : k₃ ≠ b₁ 2 := by
    rw [hk₃]
    split_ifs with h
    · rw [h]
      decide
    · exact Ne.symm h
  have hwB : ∀ x, wd b₁ b₂ b₃ x ∈ B := fun x =>
    B.mul_mem (B.mul_mem (B.pow_mem hb₁ _) (B.pow_mem hb₂ _)) (B.pow_mem hb₃ _)
  have hwm := wd_mul (hinv _ hb₁) (hinv _ hb₂) (hinv _ hb₃) (hcomm _ hb₁ _ hb₂)
    (hcomm _ hb₁ _ hb₃) (hcomm _ hb₂ _ hb₃)
  have h12 : b₂ (b₁ 0) = b₁ 2 := by
    rw [← hb₂0, ← Perm.mul_apply, ← Perm.mul_apply, hcomm _ hb₂ _ hb₁]
  have hφ0 : ∀ z : Fin 8, wd b₁ b₂ b₃ z 0 = 0 → z = 0 := by
    intro z hz
    fin_cases z
    · rfl
    · change wd b₁ b₂ b₃ (1 : Fin 8) 0 = 0 at hz
      rw [wd_one, hb₁0] at hz
      exact absurd hz (by decide)
    · change wd b₁ b₂ b₃ (2 : Fin 8) 0 = 0 at hz
      rw [wd_two, hb₂0] at hz
      exact absurd hz (by decide)
    · change wd b₁ b₂ b₃ (3 : Fin 8) 0 = 0 at hz
      rw [wd_three, Perm.mul_apply, hb₂0] at hz
      have := congrArg b₁ hz
      rw [hinv' _ hb₁, hb₁0] at this
      exact absurd this (by decide)
    · change wd b₁ b₂ b₃ (4 : Fin 8) 0 = 0 at hz
      rw [wd_four, hb₃0] at hz
      exact absurd hz hk0
    · change wd b₁ b₂ b₃ (5 : Fin 8) 0 = 0 at hz
      rw [wd_five, Perm.mul_apply, hb₃0] at hz
      have := congrArg b₁ hz
      rw [hinv' _ hb₁, hb₁0] at this
      exact absurd this hk1
    · change wd b₁ b₂ b₃ (6 : Fin 8) 0 = 0 at hz
      rw [wd_six, Perm.mul_apply, hb₃0] at hz
      have := congrArg b₂ hz
      rw [hinv' _ hb₂, hb₂0] at this
      exact absurd this hk2
    · change wd b₁ b₂ b₃ (7 : Fin 8) 0 = 0 at hz
      rw [wd_seven, Perm.mul_apply, Perm.mul_apply, hb₃0] at hz
      have h1 := congrArg b₁ hz
      rw [hinv' _ hb₁, hb₁0] at h1
      have h2 := congrArg b₂ h1
      rw [hinv' _ hb₂, ← hb₁0, h12] at h2
      exact absurd h2 hkb
  set φ : Fin 8 → Fin 8 := fun x => wd b₁ b₂ b₃ x 0 with hφ
  have hφinj : Function.Injective φ := by
    intro x y h
    have h1 : wd b₁ b₂ b₃ x = wd b₁ b₂ b₃ y := hsr _ (hwB x) _ (hwB y) h
    have h2 : wd b₁ b₂ b₃ (y ^^^ x) 0 = 0 := by
      rw [← hwm x y, h1, hinv _ (hwB y), Perm.one_apply]
    exact (xor_eq_zero' y x (hφ0 _ h2)).symm
  have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hφinj
  set τ : Perm (Fin 8) := Equiv.ofBijective φ hφbij with hτdef
  have hτ : ∀ x, τ x = wd b₁ b₂ b₃ x 0 := fun _ => rfl
  have hconj : ∀ k, τ⁻¹ * wd b₁ b₂ b₃ k * τ = xt k := by
    intro k
    apply Equiv.ext
    intro x
    rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq, xt_apply, hτ, hτ, ← hwm k x,
      Perm.mul_apply]
  have hword : ∀ σ ∈ B, ∃ k, σ = wd b₁ b₂ b₃ k := by
    intro σ hσ
    obtain ⟨k, hk⟩ := hφbij.2 (σ 0)
    exact ⟨k, hsr _ hσ _ (hwB k) hk.symm⟩
  refine ⟨τ, fun σ => ⟨fun hσ => ?_, fun hσ => ?_⟩⟩
  · obtain ⟨k, rfl⟩ := hword σ hσ
    rw [hconj]
    exact xt_mem k
  · obtain ⟨k, hk⟩ := hσ
    have h1 : τ⁻¹ * σ * τ = τ⁻¹ * wd b₁ b₂ b₃ k * τ := by rw [hk, hconj]
    have h2 : σ = wd b₁ b₂ b₃ k := mul_left_cancel (mul_right_cancel h1)
    rw [h2]
    exact hwB k

@[expose] def FixB0 (x : Fin 8 → ZMod 2) : Prop := ∀ k i : Fin 8, x (i ^^^ k) + x k = x i

instance : DecidablePred FixB0 := fun x => by
  unfold FixB0
  infer_instance

theorem iota_dAct_xt (k : Fin 8) (y : D8) (i : Fin 8) :
    Multiplicative.toAdd (iota (dAct (xt k) y)) i =
      Multiplicative.toAdd (iota y) (i ^^^ k) + Multiplicative.toAdd (iota y) k := by
  rw [iota_dAct, xt_inv, xt_apply, xt_apply_zero]

theorem fixB0_of_mem {y : D8} (hy : y ∈ fixD B0) : FixB0 (Multiplicative.toAdd (iota y)) := by
  intro k i
  rw [← iota_dAct_xt, (mem_fixD.1 hy) (xt k) (xt_mem k)]

theorem mem_of_fixB0 {y : D8} (hy : FixB0 (Multiplicative.toAdd (iota y))) : y ∈ fixD B0 := by
  rw [mem_fixD]
  rintro _ ⟨k, rfl⟩
  apply iota_inj
  apply Multiplicative.toAdd.injective
  funext i
  rw [iota_dAct_xt]
  exact hy k i

@[expose] noncomputable def cls (x : Fin 8 → ZMod 2) (h : ∑ i, x i = 0) : D8 :=
  QuotientGroup.mk ⟨Multiplicative.ofAdd x, (mem_coreMod).2 h⟩

theorem iota_cls (x : Fin 8 → ZMod 2) (h : ∑ i, x i = 0) (h0 : x 0 = 0) :
    Multiplicative.toAdd (iota (cls x h)) = x := by
  funext i
  change Multiplicative.toAdd (nrm (Multiplicative.ofAdd x)) i = x i
  rw [nrm_apply, toAdd_ofAdd, h0, add_zero]

theorem comm_chk : ∀ z : Fin 6 → ZMod 2, FixB0 (emb z) → ∃ k : Fin 8, ∃ w : Fin 6 → ZMod 2,
    ∀ i, emb z i = emb w i + (emb w (i ^^^ k) + emb w k) := by
  decide +kernel

theorem mem_comm_of_fixD {y : D8} (hy : y ∈ fixD B0) :
    ∃ k : Fin 8, ∃ x : D8, y = x * dAct (xt k) x := by
  have hz : FixB0 (emb (cmp (Multiplicative.toAdd (iota y)))) := by
    rw [emb_iota]
    exact fixB0_of_mem hy
  obtain ⟨k, w, hw⟩ := comm_chk _ hz
  refine ⟨k, cls (emb w) (sum_emb w),
    iota_inj (Multiplicative.toAdd.injective (funext fun i => ?_))⟩
  rw [S126L20.toAdd_iota_mul, Pi.add_apply, iota_dAct_xt, iota_cls _ _ (emb_zero w), ← hw,
    emb_iota]

@[expose] def cv0 : Fin 8 → ZMod 2 := ![0, 1, 0, 1, 0, 1, 0, 1]

@[expose] def cv1 : Fin 8 → ZMod 2 := ![0, 0, 1, 1, 0, 0, 1, 1]

@[expose] def cv2 : Fin 8 → ZMod 2 := ![0, 0, 0, 0, 1, 1, 1, 1]

theorem cv_facts : FixB0 cv0 ∧ FixB0 cv1 ∧ FixB0 cv2 ∧ ∑ i, cv0 i = 0 ∧ ∑ i, cv1 i = 0 ∧
    ∑ i, cv2 i = 0 ∧ cv0 0 = 0 ∧ cv1 0 = 0 ∧ cv2 0 = 0 := by
  decide

theorem cv_sep : ∀ p q : Fin 8, cv0 p = cv0 q → cv1 p = cv1 q → cv2 p = cv2 q → p = q := by
  decide

theorem fix_cv {τ : Perm (Fin 8)} (h0 : τ 0 = 0) (x : Fin 8 → ZMod 2) (hs : ∑ i, x i = 0)
    (hx0 : x 0 = 0) (h : dAct τ (cls x hs) = cls x hs) (i : Fin 8) :
    x (τ⁻¹ i) = x i := by
  have hinv0 : τ⁻¹ 0 = 0 := by rw [Perm.inv_eq_iff_eq, h0]
  have h1 := cond_of_fix h i
  rwa [iota_cls x hs hx0, hinv0, hx0, add_zero] at h1

theorem mem_B0_of_fix {σ : Perm (Fin 8)} (h : ∀ y ∈ fixD B0, dAct σ y = y) : σ ∈ B0 := by
  obtain ⟨f0, f1, f2, s0, s1, s2, z0, z1, z2⟩ := cv_facts
  set k := σ 0 with hk
  set τ := xt k * σ with hτ
  have h0 : τ 0 = 0 := by rw [hτ, Perm.mul_apply, ← hk, xt_apply, xor_self']
  have hfix : ∀ y ∈ fixD B0, dAct τ y = y := fun y hy => by
    rw [hτ, dAct_mul, h y hy, (mem_fixD.1 hy) _ (xt_mem k)]
  have hc : ∀ x (hx : FixB0 x) (hs : ∑ i, x i = 0), x 0 = 0 → ∀ i, x (τ⁻¹ i) = x i :=
    fun x hx hs hx0 => fix_cv h0 x hs hx0 (hfix _ (mem_of_fixB0 (by rwa [iota_cls x hs hx0])))
  have hid : τ⁻¹ = 1 := Equiv.ext fun i => cv_sep _ _ (hc _ f0 s0 z0 i) (hc _ f1 s1 z1 i)
    (hc _ f2 s2 z2 i)
  have hτ1 : τ = 1 := inv_eq_one.1 hid
  refine ⟨k, ?_⟩
  calc σ = (xt k)⁻¹ * τ := by rw [hτ, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = xt k := by rw [hτ1, mul_one, xt_inv]

@[expose] def rho0 : Perm (Fin 8) where
  toFun := ![0, 2, 4, 6, 3, 1, 7, 5]
  invFun := ![0, 5, 1, 4, 2, 7, 3, 6]
  left_inv := by decide
  right_inv := by decide

theorem sign_rho0 : Perm.sign rho0 = 1 := by
  decide

theorem rho0_mem_A8 : rho0 ∈ alternatingGroup (Fin 8) :=
  Perm.mem_alternatingGroup.2 sign_rho0

theorem rho0_conj : ∀ k : Fin 8, rho0 * xt k * rho0⁻¹ = xt (rho0 k) := by
  decide

theorem rho0_zero : rho0 0 = 0 := rfl

theorem orbit_chk : ∀ z : Fin 6 → ZMod 2, FixB0 (emb z) → z ≠ 0 →
    ∀ z' : Fin 6 → ZMod 2, FixB0 (emb z') → z' ≠ 0 →
      ∃ n : Fin 7, ∀ i, emb z' i = emb z ((rho0 ^ n.val)⁻¹ i) := by
  decide +kernel

theorem cmp_ne_zero {y : D8} (hy : y ≠ 1) : cmp (Multiplicative.toAdd (iota y)) ≠ 0 := by
  intro h
  apply hy
  apply iota_inj
  apply Multiplicative.toAdd.injective
  rw [← emb_iota y, h, map_one, toAdd_one]
  funext i
  revert i
  decide

theorem exists_pow_rho0 {y y' : D8} (hy : y ∈ fixD B0) (hy' : y' ∈ fixD B0) (h1 : y ≠ 1)
    (h1' : y' ≠ 1) : ∃ n : ℕ, dAct (rho0 ^ n) y = y' := by
  have hz : FixB0 (emb (cmp (Multiplicative.toAdd (iota y)))) := by
    rw [emb_iota]
    exact fixB0_of_mem hy
  have hz' : FixB0 (emb (cmp (Multiplicative.toAdd (iota y')))) := by
    rw [emb_iota]
    exact fixB0_of_mem hy'
  obtain ⟨n, hn⟩ := orbit_chk _ hz (cmp_ne_zero h1) _ hz' (cmp_ne_zero h1')
  refine ⟨n.val, iota_inj (Multiplicative.toAdd.injective (funext fun i => ?_))⟩
  have hp0 : (rho0 ^ n.val)⁻¹ 0 = 0 := by
    rw [Perm.inv_eq_iff_eq]
    exact (Perm.pow_apply_eq_self_of_apply_eq_self rho0_zero _).symm
  rw [iota_dAct, hp0, iota_zero, add_zero, ← emb_iota y, ← emb_iota y', hn i]

theorem mem_fixD_iff {B : Subgroup (Perm (Fin 8))} {τ : Perm (Fin 8)}
    (hB : ∀ σ, σ ∈ B ↔ τ⁻¹ * σ * τ ∈ B0) {y : D8} :
    y ∈ fixD B ↔ dAct τ⁻¹ y ∈ fixD B0 := by
  constructor
  · intro hy
    rw [mem_fixD]
    intro b hb
    have hb' : τ * b * τ⁻¹ ∈ B := (hB _).2 (by
      rw [show τ⁻¹ * (τ * b * τ⁻¹) * τ = b by group]
      exact hb)
    have h1 := (mem_fixD.1 hy) _ hb'
    rw [dAct_mul, dAct_mul] at h1
    have h2 := congrArg (dAct τ⁻¹) h1
    rwa [dAct_inv_dAct] at h2
  · intro hy
    rw [mem_fixD]
    intro b hb
    have h1 := (mem_fixD.1 hy) _ ((hB b).1 hb)
    rw [dAct_mul, dAct_mul, dAct_dAct_inv] at h1
    have h2 := congrArg (dAct τ) h1
    rwa [dAct_dAct_inv, dAct_dAct_inv] at h2

end S126L20b

end CFSG.Quasithin.H13
