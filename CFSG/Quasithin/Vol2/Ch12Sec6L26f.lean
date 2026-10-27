module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt

public section

namespace CFSG.Quasithin.H13.S126W

abbrev E25 : Type := Multiplicative (ZMod 5 × ZMod 5)

def memB (i : Fin 8) (x : ZMod 5 × ZMod 5) : Bool :=
  if i.val < 5 then decide (x.2 = (i.val : ZMod 5) * x.1)
  else if i.val = 5 then decide (x.1 = 0)
  else if i.val = 6 then true else decide (x = 0)

theorem memB_zero : ∀ i : Fin 8, memB i 0 = true := by decide

theorem memB_add : ∀ (i : Fin 8) (a b : ZMod 5 × ZMod 5), memB i a = true → memB i b = true →
    memB i (a + b) = true := by decide

theorem memB_neg : ∀ (i : Fin 8) (a : ZMod 5 × ZMod 5), memB i a = true → memB i (-a) = true := by
  decide

def AE (i : Fin 8) : Subgroup E25 where
  carrier := {g | memB i (Multiplicative.toAdd g) = true}
  one_mem' := memB_zero i
  mul_mem' := fun ha hb => memB_add i _ _ ha hb
  inv_mem' := fun ha => memB_neg i _ ha

instance (g : E25) (i : Fin 8) : Decidable (g ∈ AE i) :=
  inferInstanceAs (Decidable (memB i (Multiplicative.toAdd g) = true))

def mE : Fin 8 → ℕ := ![1, 1, 1, 1, 1, 1, 0, 0]

def nE : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 1, 5]

theorem coeff_chk : ∀ g : ZMod 5 × ZMod 5,
    ((if memB 0 g then 1 else 0) + (if memB 1 g then 1 else 0) + (if memB 2 g then 1 else 0) +
      (if memB 3 g then 1 else 0) + (if memB 4 g then 1 else 0) + (if memB 5 g then 1 else 0) +
      (if memB 6 g then 0 else 0) + (if memB 7 g then 0 else 0) : ℕ) =
    (if memB 0 g then 0 else 0) + (if memB 1 g then 0 else 0) + (if memB 2 g then 0 else 0) +
      (if memB 3 g then 0 else 0) + (if memB 4 g then 0 else 0) + (if memB 5 g then 0 else 0) +
      (if memB 6 g then 1 else 0) + (if memB 7 g then 5 else 0) := by decide

theorem hcoeff (g : E25) :
    (∑ i : Fin 8, if g ∈ AE i then mE i else 0) = ∑ i : Fin 8, if g ∈ AE i then nE i else 0 := by
  have := coeff_chk (Multiplicative.toAdd g)
  simpa [Fin.sum_univ_eight, AE, mE, nE] using this

theorem card_AE_chk : ∀ i : Fin 8, Fintype.card ↥(AE i) =
    if i.val < 6 then 5 else if i.val = 6 then 25 else 1 := by decide

theorem card_AE (i : Fin 8) : Nat.card ↥(AE i) =
    if i.val < 6 then 5 else if i.val = 6 then 25 else 1 := by
  rw [Nat.card_eq_fintype_card]
  exact card_AE_chk i

def dir (i : Fin 8) : ZMod 5 × ZMod 5 :=
  if i.val < 5 then (1, (i.val : ZMod 5)) else (0, 1)

theorem dir_mem : ∀ i : Fin 8, i.val < 6 → memB i (dir i) = true := by decide

theorem mem_pow_dir : ∀ i : Fin 8, i.val < 6 → ∀ x : ZMod 5 × ZMod 5, memB i x = true →
    ∃ n : Fin 5, x = (n.val : ℕ) • dir i := by decide

theorem dir_ne : ∀ i : Fin 8, dir i ≠ 0 := by decide

theorem eq_bot_seven : ∀ x : ZMod 5 × ZMod 5, memB 7 x = true → x = 0 := by decide

theorem memB_six : ∀ x : ZMod 5 × ZMod 5, memB 6 x = true := by decide

section Action

variable {M : Type} [Group M] [Finite M] [MulDistribMulAction E25 M]

def fixAE (M : Type) [Group M] [MulDistribMulAction E25 M] (i : Fin 8) : Subgroup M :=
  @fixedPointSubgroup (↥(AE i)) M _ _ (MulDistribMulAction.compHom M (AE i).subtype)

omit [Finite M] in
theorem mem_fixAE {i : Fin 8} {x : M} : x ∈ fixAE M i ↔ ∀ a : ↥(AE i), (a : E25) • x = x :=
  Iff.rfl

omit [Finite M] in
theorem pow_smul_eq {g : E25} {x : M} (hx : g • x = x) (n : ℕ) : (g ^ n) • x = x := by
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n ih => rw [pow_succ, mul_smul, hx, ih]

omit [Finite M] in
theorem card_fix_lt (i : Fin 8) (hi : i.val < 6) :
    Nat.card (fixAE M i) = Nat.card {x : M // Multiplicative.ofAdd (dir i) • x = x} := by
  let _ : MulDistribMulAction (↥(AE i)) M := MulDistribMulAction.compHom M (AE i).subtype
  refine Nat.card_congr
    { toFun := fun x => ⟨x, ?_⟩
      invFun := fun x => ⟨x.1, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · exact mem_fixAE.1 x.2 ⟨Multiplicative.ofAdd (dir i), dir_mem i hi⟩
  · refine mem_fixAE.2 ?_
    rintro ⟨k, hk⟩
    obtain ⟨n, hn⟩ := mem_pow_dir i hi _ hk
    have hk' : k = Multiplicative.ofAdd (dir i) ^ n.val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_ofAdd, ← hn]
    show k • (x : M) = x
    rw [hk']
    exact pow_smul_eq x.2 _

omit [Finite M] in
theorem card_fix_seven : Nat.card (fixAE M 7) = Nat.card M := by
  let _ : MulDistribMulAction (↥(AE 7)) M := MulDistribMulAction.compHom M (AE 7).subtype
  have htop : fixAE M 7 = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    refine mem_fixAE.2 ?_
    rintro ⟨k, hk⟩
    have : k = 1 := Multiplicative.toAdd.injective (eq_bot_seven _ hk)
    subst this
    exact one_smul _ x
  rw [htop, Subgroup.card_top]

end Action

theorem two_pow_of_dvd {n k : ℕ} (h : k ∣ 2 ^ n) : ∃ m ≤ n, k = 2 ^ m :=
  (Nat.dvd_prime_pow Nat.prime_two).mp h

section Count

variable {M : Type} [Group M] [Finite M] [MulDistribMulAction E25 M]

theorem card_E25 : Nat.card E25 = 25 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem wielandt (hM : IsPGroup 2 M) :
    (Nat.card (fixAE M 0) * Nat.card (fixAE M 1) * Nat.card (fixAE M 2) *
      Nat.card (fixAE M 3) * Nat.card (fixAE M 4) * Nat.card (fixAE M 5)) ^ 5 =
      Nat.card (fixAE M 6) ^ 25 * Nat.card M ^ 5 := by
  have hcop : Nat.Coprime (Nat.card M) (Nat.card E25) := by
    obtain ⟨n, hn⟩ := hM.exists_card_eq
    rw [hn, card_E25]
    exact Nat.Coprime.pow_left n (by norm_num)
  have hsolv : Group.IsSolvable M := by
    have := hM.isNilpotent
    infer_instance
  have hW := CFSG.Wielandt.fixedPointSubgroup_product_card_eq_of_coeff_sum_eq (G := E25) (V := M)
    (ι := Fin 8) hcop hsolv AE mE nE hcoeff
  simp only [Fin.prod_univ_eight] at hW
  have hW' : Nat.card (fixAE M 0) ^ (mE 0 * Nat.card (AE 0)) *
      Nat.card (fixAE M 1) ^ (mE 1 * Nat.card (AE 1)) *
      Nat.card (fixAE M 2) ^ (mE 2 * Nat.card (AE 2)) *
      Nat.card (fixAE M 3) ^ (mE 3 * Nat.card (AE 3)) *
      Nat.card (fixAE M 4) ^ (mE 4 * Nat.card (AE 4)) *
      Nat.card (fixAE M 5) ^ (mE 5 * Nat.card (AE 5)) *
      Nat.card (fixAE M 6) ^ (mE 6 * Nat.card (AE 6)) *
      Nat.card (fixAE M 7) ^ (mE 7 * Nat.card (AE 7)) =
      Nat.card (fixAE M 0) ^ (nE 0 * Nat.card (AE 0)) *
      Nat.card (fixAE M 1) ^ (nE 1 * Nat.card (AE 1)) *
      Nat.card (fixAE M 2) ^ (nE 2 * Nat.card (AE 2)) *
      Nat.card (fixAE M 3) ^ (nE 3 * Nat.card (AE 3)) *
      Nat.card (fixAE M 4) ^ (nE 4 * Nat.card (AE 4)) *
      Nat.card (fixAE M 5) ^ (nE 5 * Nat.card (AE 5)) *
      Nat.card (fixAE M 6) ^ (nE 6 * Nat.card (AE 6)) *
      Nat.card (fixAE M 7) ^ (nE 7 * Nat.card (AE 7)) := hW
  simp only [card_AE, mE, nE, card_fix_seven] at hW'
  norm_num at hW'
  rw [← hW']
  ring

omit [MulDistribMulAction E25 M] in
theorem card_eq_two_pow (hM : IsPGroup 2 M) (K : Subgroup M) : ∃ k, Nat.card K = 2 ^ k := by
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  obtain ⟨k, -, hk⟩ := two_pow_of_dvd (hn ▸ Subgroup.card_subgroup_dvd_card K)
  exact ⟨k, hk⟩

omit [Finite M] in
theorem card_fix_lt_of (i : Fin 8) (hi : i.val < 6) {n : ℕ} (hn : Nat.card M = 2 ^ n)
    (h8 : Nat.card {x : M // Multiplicative.ofAdd (dir i) • x = x} * 2 ^ 8 = Nat.card M) :
    8 ≤ n ∧ Nat.card (fixAE M i) = 2 ^ (n - 8) := by
  rw [← card_fix_lt i hi, hn] at h8
  have h8n : 8 ≤ n := by
    by_contra hlt
    have h1 : 2 ^ 8 ∣ 2 ^ n := Dvd.intro_left _ h8
    have h2 := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.mp h1
    omega
  refine ⟨h8n, ?_⟩
  have e : 2 ^ n = 2 ^ (n - 8) * 2 ^ 8 := by rw [← pow_add, Nat.sub_add_cancel h8n]
  rw [e] at h8
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h8

theorem false_of_all_eight (hM : IsPGroup 2 M)
    (h8 : ∀ g : E25, g ≠ 1 → Nat.card {x : M // g • x = x} * 2 ^ 8 = Nat.card M) : False := by
  have hW := wielandt hM
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  have hg : ∀ i : Fin 8, Multiplicative.ofAdd (dir i) ≠ (1 : E25) := fun i h =>
    dir_ne i (Multiplicative.ofAdd.injective h)
  obtain ⟨-, h0⟩ := card_fix_lt_of 0 (by decide) hn (h8 _ (hg 0))
  obtain ⟨-, h1⟩ := card_fix_lt_of 1 (by decide) hn (h8 _ (hg 1))
  obtain ⟨-, h2⟩ := card_fix_lt_of 2 (by decide) hn (h8 _ (hg 2))
  obtain ⟨-, h3⟩ := card_fix_lt_of 3 (by decide) hn (h8 _ (hg 3))
  obtain ⟨-, h4⟩ := card_fix_lt_of 4 (by decide) hn (h8 _ (hg 4))
  obtain ⟨hn8, h5⟩ := card_fix_lt_of 5 (by decide) hn (h8 _ (hg 5))
  obtain ⟨c, hc⟩ := card_eq_two_pow hM (fixAE M 6)
  rw [h0, h1, h2, h3, h4, h5, hc, hn] at hW
  have e : ((2 : ℕ) ^ (n - 8) * 2 ^ (n - 8) * 2 ^ (n - 8) * 2 ^ (n - 8) * 2 ^ (n - 8) *
      2 ^ (n - 8)) ^ 5 = 2 ^ (30 * (n - 8)) := by ring
  have e2 : ((2 : ℕ) ^ c) ^ 25 * (2 ^ n) ^ 5 = 2 ^ (25 * c + 5 * n) := by ring
  rw [e, e2] at hW
  have := Nat.pow_right_injective (le_refl 2) hW
  omega

theorem four_dvd_of_pow_modEq {k : ℕ} (h : 2 ^ k % 5 = 1) : k % 4 = 0 := by
  have e : 2 ^ k = 2 ^ (k % 4) * 16 ^ (k / 4) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [e, Nat.mul_mod, Nat.pow_mod 16, show (16 : ℕ) % 5 = 1 by norm_num, one_pow,
    Nat.one_mod, mul_one, Nat.mod_mod] at h
  have hk : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hk' : k % 4 <;> simp_all

theorem false_of_five_eight (hM : IsPGroup 2 M)
    (h8 : ∀ g : E25, (Multiplicative.toAdd g).1 ≠ 0 →
      Nat.card {x : M // g • x = x} * 2 ^ 8 = Nat.card M)
    (hz : ∃ x : M, Multiplicative.ofAdd ((0, 1) : ZMod 5 × ZMod 5) • x ≠ x) : False := by
  have hW := wielandt hM
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  have hg : ∀ i : Fin 8, i.val < 5 →
      (Multiplicative.toAdd (Multiplicative.ofAdd (dir i))).1 ≠ 0 := by
    decide
  obtain ⟨-, k0⟩ := card_fix_lt_of 0 (by decide) hn (h8 _ (hg 0 (by decide)))
  obtain ⟨-, k1⟩ := card_fix_lt_of 1 (by decide) hn (h8 _ (hg 1 (by decide)))
  obtain ⟨-, k2⟩ := card_fix_lt_of 2 (by decide) hn (h8 _ (hg 2 (by decide)))
  obtain ⟨-, k3⟩ := card_fix_lt_of 3 (by decide) hn (h8 _ (hg 3 (by decide)))
  obtain ⟨hn8, k4⟩ := card_fix_lt_of 4 (by decide) hn (h8 _ (hg 4 (by decide)))
  obtain ⟨d, hd⟩ := card_eq_two_pow hM (fixAE M 5)
  obtain ⟨c, hc⟩ := card_eq_two_pow hM (fixAE M 6)
  have hcd : c ≤ d := by
    have hle : fixAE M 6 ≤ fixAE M 5 := by
      intro x hx
      refine mem_fixAE.2 fun k => ?_
      exact mem_fixAE.1 hx ⟨k.1, memB_six _⟩
    have := Subgroup.card_le_of_le hle
    rw [hc, hd] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hdn : d < n := by
    obtain ⟨x, hx⟩ := hz
    by_contra hnd
    push Not at hnd
    have htop : fixAE M 5 = ⊤ := by
      refine Subgroup.eq_top_of_le_card _ ?_
      rw [hd, hn]
      exact Nat.pow_le_pow_right (by norm_num) hnd
    have hxm : x ∈ fixAE M 5 := htop ▸ Subgroup.mem_top x
    exact hx (mem_fixAE.1 hxm ⟨Multiplicative.ofAdd ((0, 1) : ZMod 5 × ZMod 5), by decide⟩)
  have hmod : 2 ^ (n - d) % 5 = 1 := by
    let _ : MulDistribMulAction (↥(AE 5)) M := MulDistribMulAction.compHom M (AE 5).subtype
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hp5 : IsPGroup 5 ↥(AE 5) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [card_AE]
      rfl
    have h1 := hp5.card_modEq_card_fixedPoints M
    have h2 : Nat.card (MulAction.fixedPoints (↥(AE 5)) M) = Nat.card (fixAE M 5) := rfl
    rw [h2, hd, hn] at h1
    have e : 2 ^ n = 2 ^ d * 2 ^ (n - d) := by rw [← pow_add, Nat.add_sub_cancel' hdn.le]
    rw [e] at h1
    have h3 : 2 ^ d * 2 ^ (n - d) ≡ 2 ^ d * 1 [MOD 5] := by rw [mul_one]; exact h1
    have h4 := Nat.ModEq.cancel_left_of_coprime
      (Nat.Coprime.pow_right d (by norm_num : Nat.Coprime 5 2)) h3
    exact h4
  have h4 := four_dvd_of_pow_modEq hmod
  rw [k0, k1, k2, k3, k4, hd, hc, hn] at hW
  have e : ((2 : ℕ) ^ (n - 8) * 2 ^ (n - 8) * 2 ^ (n - 8) * 2 ^ (n - 8) * 2 ^ (n - 8) *
      2 ^ d) ^ 5 = 2 ^ (25 * (n - 8) + 5 * d) := by ring
  have e2 : ((2 : ℕ) ^ c) ^ 25 * (2 ^ n) ^ 5 = 2 ^ (25 * c + 5 * n) := by ring
  rw [e, e2] at hW
  have := Nat.pow_right_injective (le_refl 2) hW
  omega

end Count

end CFSG.Quasithin.H13.S126W
