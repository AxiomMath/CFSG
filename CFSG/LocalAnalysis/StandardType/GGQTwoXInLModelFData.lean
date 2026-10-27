module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def q3f_one (n : ℕ) : Fin n → ZMod 3 := fun _ => 1

@[expose] def q3f_e (n : ℕ) (m : ℕ) : Fin n → ZMod 3 := fun j => if j.val = m then 1 else 0

@[expose] noncomputable def q3f_dotE (n m : ℕ) :
    Module.Dual (ZMod 3) (Fin n → ZMod 3) where
  toFun w := ∑ k : Fin n, (if k.val = m then (1 : ZMod 3) else 0) * w k
  map_add' a b := by
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

lemma q3f_dotE_apply_of_lt (n m : ℕ) (hm : m < n) (w : Fin n → ZMod 3) :
    q3f_dotE n m w = w ⟨m, hm⟩ := by
  change (∑ k : Fin n, (if k.val = m then (1 : ZMod 3) else 0) * w k) = w ⟨m, hm⟩
  rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin n)
    (fun b _ hb => by
      have hbm : b.val ≠ m := fun h => hb (Fin.ext h)
      simp [hbm])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

@[expose] noncomputable def q3f_coroot (n : ℕ) (i : Fin n) : Fin n → ZMod 3 :=
  if i.val = n - 2 then - q3f_e n 0 - q3f_e n 1
  else if i.val = n - 1 then q3f_e n 0 - q3f_e n 1
  else q3f_e n (n - 2 - i.val) - q3f_e n (n - 1 - i.val)

@[expose] noncomputable def q3f_root (n : ℕ) (i : Fin n) :
    Module.Dual (ZMod 3) (Fin n → ZMod 3) :=
  if i.val = n - 2 then - q3f_dotE n 0 - q3f_dotE n 1
  else if i.val = n - 1 then q3f_dotE n 0 - q3f_dotE n 1
  else q3f_dotE n (n - 2 - i.val) - q3f_dotE n (n - 1 - i.val)

@[expose] noncomputable def q3f_permLin (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun v := v ∘ σ
  invFun v := v ∘ σ.symm
  map_add' a b := by ext i; rfl
  map_smul' c a := by ext i; rfl
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp

lemma q3f_permLin_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n → ZMod 3) (i : Fin n) :
    q3f_permLin n σ v i = v (σ i) := rfl

@[expose] noncomputable def q3f_P (n : ℕ) :
    Equiv.Perm (Fin n) →* ((Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) where
  toFun σ := q3f_permLin n σ.symm
  map_one' := by ext v i; rfl
  map_mul' σ π := by
    ext v i
    show v ((σ * π).symm i) = v (π.symm (σ.symm i))
    have hsym : (σ * π).symm = π.symm * σ.symm := by
      ext x
      rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.Perm.mul_apply]
    rw [hsym, Equiv.Perm.mul_apply]

lemma q3f_P_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n → ZMod 3) (i : Fin n) :
    q3f_P n σ v i = v (σ.symm i) := rfl

lemma q3f_P_one (n : ℕ) (σ : Equiv.Perm (Fin n)) : q3f_P n σ (q3f_one n) = q3f_one n := by
  funext i
  simp only [q3f_P_apply, q3f_one]

@[expose] noncomputable def q3f_dLin (n : ℕ) :
    (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun v := fun i => (if i.val = 0 then (-1 : ZMod 3) else 1) * v i
  invFun v := fun i => (if i.val = 0 then (-1 : ZMod 3) else 1) * v i
  map_add' a b := by funext i; simp only [Pi.add_apply, mul_add]
  map_smul' c a := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv v := by
    funext i; by_cases h : i.val = 0 <;> simp [h]
  right_inv v := by
    funext i; by_cases h : i.val = 0 <;> simp [h]

lemma q3f_dLin_apply (n : ℕ) (v : Fin n → ZMod 3) (i : Fin n) :
    q3f_dLin n v i = (if i.val = 0 then (-1 : ZMod 3) else 1) * v i := rfl

lemma q3f_dLin_mul_self (n : ℕ) : q3f_dLin n * q3f_dLin n = 1 := by
  apply LinearEquiv.ext
  intro v
  funext i
  by_cases h : i.val = 0 <;> simp [q3f_dLin, LinearEquiv.mul_apply, h]

lemma q3f_dLin_involutive (n : ℕ) (x : Fin n → ZMod 3) :
    q3f_dLin n (q3f_dLin n x) = x := by
  rw [← LinearEquiv.mul_apply, q3f_dLin_mul_self]
  rfl

@[expose] noncomputable def q3f_conjD (n : ℕ) :
    ((Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) ≃*
      ((Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :=
  MulAut.conj (q3f_dLin n)

lemma q3f_conjD_apply (n : ℕ)
    (X : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    q3f_conjD n X = q3f_dLin n * X * q3f_dLin n := by
  rw [q3f_conjD, MulAut.conj_apply]
  rw [show (q3f_dLin n)⁻¹ = q3f_dLin n from
    (eq_inv_of_mul_eq_one_right (q3f_dLin_mul_self n)).symm]

@[expose] noncomputable def q3f_tau (n : ℕ) (hn : 2 ≤ n) (i : Fin n) : Equiv.Perm (Fin n) :=
  if hi : i.val = n - 1 ∨ i.val = n - 2 then Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  else Equiv.swap ⟨n - 2 - i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩

lemma q3f_tau_first (n : ℕ) (hn : 2 ≤ n) {i : Fin n}
    (h : i.val = n - 1 ∨ i.val = n - 2) :
    q3f_tau n hn i = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  rw [q3f_tau, dif_pos h]

lemma q3f_tau_chain (n : ℕ) (hn : 2 ≤ n) {i : Fin n}
    (h : ¬ (i.val = n - 1 ∨ i.val = n - 2)) :
    q3f_tau n hn i = Equiv.swap ⟨n - 2 - i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ := by
  rw [q3f_tau, dif_neg h]

@[expose] noncomputable def q3f_r (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
  if i.val = n - 2 then q3f_conjD n (q3f_P n (q3f_tau n hn i))
  else q3f_P n (q3f_tau n hn i)

lemma q3f_root_a (n : ℕ) (hn : 2 ≤ n) {i : Fin n} (h : i.val = n - 2)
    (w : Fin n → ZMod 3) :
    q3f_root n i w = - w ⟨0, by omega⟩ - w ⟨1, by omega⟩ := by
  rw [q3f_root, if_pos h]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply]
  rw [q3f_dotE_apply_of_lt n 0 (by omega), q3f_dotE_apply_of_lt n 1 (by omega)]

lemma q3f_root_b (n : ℕ) (hn : 2 ≤ n) {i : Fin n} (h2 : i.val ≠ n - 2)
    (h : i.val = n - 1) (w : Fin n → ZMod 3) :
    q3f_root n i w = w ⟨0, by omega⟩ - w ⟨1, by omega⟩ := by
  rw [q3f_root, if_neg h2, if_pos h]
  simp only [LinearMap.sub_apply]
  rw [q3f_dotE_apply_of_lt n 0 (by omega), q3f_dotE_apply_of_lt n 1 (by omega)]

lemma q3f_root_c (n : ℕ) (hn : 3 ≤ n) {i : Fin n} (h2 : i.val ≠ n - 2)
    (h1 : i.val ≠ n - 1) (w : Fin n → ZMod 3) :
    q3f_root n i w = w ⟨n - 2 - i.val, by omega⟩ - w ⟨n - 1 - i.val, by omega⟩ := by
  rw [q3f_root, if_neg h2, if_neg h1]
  simp only [LinearMap.sub_apply]
  rw [q3f_dotE_apply_of_lt n (n - 2 - i.val) (by omega),
    q3f_dotE_apply_of_lt n (n - 1 - i.val) (by omega)]

lemma q3f_coroot_a (n : ℕ) (hn : 2 ≤ n) {j : Fin n} (h : j.val = n - 2)
    (m : ℕ) (hm : m < n) :
    q3f_coroot n j ⟨m, hm⟩ =
      if m = 0 then (-1 : ZMod 3) else if m = 1 then -1 else 0 := by
  rw [q3f_coroot, if_pos h]
  simp only [Pi.sub_apply, Pi.neg_apply, q3f_e, Fin.val_mk]
  split_ifs <;> (try norm_num) <;> omega

lemma q3f_coroot_b (n : ℕ) (hn : 2 ≤ n) {j : Fin n} (h2 : j.val ≠ n - 2)
    (h : j.val = n - 1) (m : ℕ) (hm : m < n) :
    q3f_coroot n j ⟨m, hm⟩ = if m = 0 then (1 : ZMod 3) else if m = 1 then -1 else 0 := by
  rw [q3f_coroot, if_neg h2, if_pos h]
  simp only [Pi.sub_apply, q3f_e, Fin.val_mk]
  split_ifs <;> (try norm_num) <;> omega

lemma q3f_coroot_c (n : ℕ) (hn : 2 ≤ n) {j : Fin n} (h2 : j.val ≠ n - 2)
    (h1 : j.val ≠ n - 1) (m : ℕ) (hm : m < n) :
    q3f_coroot n j ⟨m, hm⟩ =
      if m = n - 2 - j.val then (1 : ZMod 3) else if m = n - 1 - j.val then -1 else 0 := by
  rw [q3f_coroot, if_neg h2, if_neg h1]
  simp only [Pi.sub_apply, q3f_e, Fin.val_mk]
  split_ifs <;> (try norm_num) <;> omega

lemma q3f_dLin_of_ne_zero (n m : ℕ) (hm : m ≠ 0) :
    q3f_dLin n (q3f_e n m) = q3f_e n m := by
  funext k
  simp only [q3f_dLin_apply, q3f_e]
  by_cases hk : k.val = m
  · have hk0 : k.val ≠ 0 := by rw [hk]; exact hm
    simp [hk0]
  · simp [hk]

lemma q3f_dLin_of_zero (n : ℕ) (hn : 1 ≤ n) :
    q3f_dLin n (q3f_e n 0) = - q3f_e n 0 := by
  funext k
  simp only [q3f_dLin_apply, q3f_e, Pi.neg_apply]
  by_cases hk : k.val = 0 <;> simp [hk]

lemma q3f_dLin_e_sub (n : ℕ) (hn : 1 ≤ n) :
    q3f_dLin n (q3f_e n 0 - q3f_e n 1) = - q3f_e n 0 - q3f_e n 1 := by
  rw [map_sub, q3f_dLin_of_zero n hn, q3f_dLin_of_ne_zero n 1 (by norm_num)]

lemma q3f_P_swap (n : ℕ) (p q : Fin n) (hpq : p ≠ q) (v : Fin n → ZMod 3) :
    q3f_P n (Equiv.swap p q) v =
      v - (v p - v q) • (q3f_e n p.val - q3f_e n q.val) := by
  funext k
  rw [q3f_P_apply, Equiv.symm_swap]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hkp : k = p
  · subst k
    rw [Equiv.swap_apply_left]
    have hp : q3f_e n p.val p = 1 := by simp [q3f_e]
    have hq : q3f_e n q.val p = 0 := by
      simp only [q3f_e]
      rw [if_neg]
      exact fun h => hpq (Fin.ext h)
    rw [hp, hq]; ring
  · by_cases hkq : k = q
    · subst k
      rw [Equiv.swap_apply_right]
      have hp : q3f_e n p.val q = 0 := by
        simp only [q3f_e]
        rw [if_neg]
        exact fun h => hkp (Fin.ext h)
      have hq : q3f_e n q.val q = 1 := by simp [q3f_e]
      rw [hp, hq]; ring
    · rw [Equiv.swap_apply_of_ne_of_ne hkp hkq]
      have hp : q3f_e n p.val k = 0 := by
        simp only [q3f_e]
        rw [if_neg]
        exact fun h => hkp (Fin.ext h)
      have hq : q3f_e n q.val k = 0 := by
        simp only [q3f_e]
        rw [if_neg]
        exact fun h => hkq (Fin.ext h)
      rw [hp, hq]; ring

lemma q3f_conjD_P_swap (n : ℕ) (p q : Fin n) (hpq : p ≠ q)
    (hp : p.val ≠ 0) (hq : q.val ≠ 0) :
    q3f_conjD n (q3f_P n (Equiv.swap p q)) = q3f_P n (Equiv.swap p q) := by
  have hcomm : q3f_dLin n * q3f_P n (Equiv.swap p q) =
      q3f_P n (Equiv.swap p q) * q3f_dLin n := by
    apply LinearEquiv.ext; intro v; funext k
    simp only [LinearEquiv.mul_apply, q3f_P_apply, q3f_dLin_apply, Equiv.symm_swap]
    congr 1
    by_cases hk : k.val = 0
    · have hfix : Equiv.swap p q k = k :=
        Equiv.swap_apply_of_ne_of_ne
          (by intro h; exact hp (by rw [← h]; exact hk))
          (by intro h; exact hq (by rw [← h]; exact hk))
      rw [hfix]
    · have hk' : (Equiv.swap p q k).val ≠ 0 := by
        intro h
        have h' : Equiv.swap p q k = ⟨0, by omega⟩ := Fin.ext h
        rw [Equiv.swap_apply_eq_iff] at h'
        rw [Equiv.swap_apply_of_ne_of_ne
          (by intro hh; exact hp (congrArg Fin.val hh).symm)
          (by intro hh; exact hq (congrArg Fin.val hh).symm)] at h'
        exact hk (congrArg Fin.val h')
      simp only [hk, hk', if_false, if_true]
  rw [q3f_conjD_apply, hcomm, mul_assoc, q3f_dLin_mul_self, mul_one]

lemma q3f_conjD_P_swap01 (n : ℕ) (hn0 : 0 < n) (hn1 : 1 < n) (v : Fin n → ZMod 3) :
    q3f_conjD n (q3f_P n (Equiv.swap ⟨0, hn0⟩ ⟨1, hn1⟩)) v =
      v - (- v ⟨0, hn0⟩ - v ⟨1, hn1⟩) • (- q3f_e n 0 - q3f_e n 1) := by
  rw [q3f_conjD_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [q3f_P_swap n ⟨0, hn0⟩ ⟨1, hn1⟩
    (by intro h; exact Nat.zero_ne_one (congrArg Fin.val h)) (q3f_dLin n v)]
  rw [map_sub, map_smul, q3f_dLin_involutive, q3f_dLin_e_sub n (by omega)]
  have hd0 : q3f_dLin n v ⟨0, hn0⟩ = - v ⟨0, hn0⟩ := by
    rw [q3f_dLin_apply]; simp
  have hd1 : q3f_dLin n v ⟨1, hn1⟩ = v ⟨1, hn1⟩ := by
    rw [q3f_dLin_apply]; simp [show (1 : ℕ) ≠ 0 by norm_num]
  rw [hd0, hd1]

def q3f_dval (n : ℕ) (i j : Fin n) : ZMod 3 :=
  if i = j then 2
  else if i.val + 1 = j.val ∧ j.val + 2 < n then -1
  else if j.val + 1 = i.val ∧ i.val + 2 < n then -1
  else if i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n) then -1
  else if j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n) then -1
  else 0

lemma q3f_D_eq (n : ℕ) (hn : 2 < n) (i j : Fin n) :
    (CartanMatrix.D n i j : ZMod 3) = q3f_dval n i j := by
  rw [q3f_dval, CartanMatrix.D, Matrix.of_apply]
  push_cast
  by_cases hij : i = j
  · simp [hij]
  · rw [if_neg hij, if_neg (show ¬ (n ≤ 2) by omega)]
    split_ifs <;> norm_num

private lemma q3f_pairing_ia (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) (hia : i.val = n - 2) :
    q3f_root n i (q3f_coroot n j) = q3f_dval n i j := by
  rw [q3f_dval]
  simp only [Fin.ext_iff]
  rw [q3f_root_a n (by omega) hia]
  by_cases hja : j.val = n - 2
  · rw [q3f_coroot_a n (by omega) hja 0 (by omega),
      q3f_coroot_a n (by omega) hja 1 (by omega)]
    split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide
  · by_cases hjb : j.val = n - 1
    · rw [q3f_coroot_b n (by omega) hja hjb 0 (by omega),
        q3f_coroot_b n (by omega) hja hjb 1 (by omega)]
      split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide
    · rw [q3f_coroot_c n (by omega) hja hjb 0 (by omega),
        q3f_coroot_c n (by omega) hja hjb 1 (by omega)]
      split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide

private lemma q3f_pairing_ib (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) (hia : ¬ i.val = n - 2)
    (hib : i.val = n - 1) :
    q3f_root n i (q3f_coroot n j) = q3f_dval n i j := by
  rw [q3f_dval]
  simp only [Fin.ext_iff]
  rw [q3f_root_b n (by omega) hia hib]
  by_cases hja : j.val = n - 2
  · rw [q3f_coroot_a n (by omega) hja 0 (by omega),
      q3f_coroot_a n (by omega) hja 1 (by omega)]
    split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide
  · by_cases hjb : j.val = n - 1
    · rw [q3f_coroot_b n (by omega) hja hjb 0 (by omega),
        q3f_coroot_b n (by omega) hja hjb 1 (by omega)]
      split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide
    · rw [q3f_coroot_c n (by omega) hja hjb 0 (by omega),
        q3f_coroot_c n (by omega) hja hjb 1 (by omega)]
      split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide

private lemma q3f_pairing_ica (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) (hia : ¬ i.val = n - 2)
    (hib : ¬ i.val = n - 1) (hja : j.val = n - 2) :
    q3f_root n i (q3f_coroot n j) = q3f_dval n i j := by
  rw [q3f_dval]
  simp only [Fin.ext_iff]
  rw [q3f_root_c n (by omega) hia hib,
    q3f_coroot_a n (by omega) hja (n - 2 - i.val) (by omega),
    q3f_coroot_a n (by omega) hja (n - 1 - i.val) (by omega)]
  split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide

private lemma q3f_pairing_icb (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) (hia : ¬ i.val = n - 2)
    (hib : ¬ i.val = n - 1) (hja : ¬ j.val = n - 2) (hjb : j.val = n - 1) :
    q3f_root n i (q3f_coroot n j) = q3f_dval n i j := by
  rw [q3f_dval]
  simp only [Fin.ext_iff]
  rw [q3f_root_c n (by omega) hia hib,
    q3f_coroot_b n (by omega) hja hjb (n - 2 - i.val) (by omega),
    q3f_coroot_b n (by omega) hja hjb (n - 1 - i.val) (by omega)]
  split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide

private lemma q3f_pairing_icc (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) (hia : ¬ i.val = n - 2)
    (hib : ¬ i.val = n - 1) (hja : ¬ j.val = n - 2) (hjb : ¬ j.val = n - 1) :
    q3f_root n i (q3f_coroot n j) = q3f_dval n i j := by
  rw [q3f_dval]
  simp only [Fin.ext_iff]
  rw [q3f_root_c n (by omega) hia hib,
    q3f_coroot_c n (by omega) hja hjb (n - 2 - i.val) (by omega),
    q3f_coroot_c n (by omega) hja hjb (n - 1 - i.val) (by omega)]
  split_ifs <;> (try norm_num) <;> first | omega | contradiction | decide

private lemma q3f_pairing_ic (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) (hia : ¬ i.val = n - 2)
    (hib : ¬ i.val = n - 1) :
    q3f_root n i (q3f_coroot n j) = q3f_dval n i j := by
  by_cases hja : j.val = n - 2
  · exact q3f_pairing_ica n hn i j hia hib hja
  · by_cases hjb : j.val = n - 1
    · exact q3f_pairing_icb n hn i j hia hib hja hjb
    · exact q3f_pairing_icc n hn i j hia hib hja hjb

lemma q3f_pairing_aux (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) :
    q3f_root n i (q3f_coroot n j) = q3f_dval n i j := by
  by_cases hia : i.val = n - 2
  · exact q3f_pairing_ia n hn i j hia
  · by_cases hib : i.val = n - 1
    · exact q3f_pairing_ib n hn i j hia hib
    · exact q3f_pairing_ic n hn i j hia hib

lemma q3f_pairing (n : ℕ) (hn : 6 ≤ n) (i j : Fin n) :
    q3f_root n i (q3f_coroot n j) = (CartanMatrix.D n i j : ZMod 3) := by
  rw [q3f_pairing_aux n hn i j, q3f_D_eq n (by omega) i j]

lemma q3f_r_apply (n : ℕ) (hn : 2 ≤ n) (i : Fin n) (w : Fin n → ZMod 3) :
    q3f_r n hn i w = w - q3f_root n i w • q3f_coroot n i := by
  by_cases hia : i.val = n - 2
  · have htau : q3f_tau n hn i = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ :=
      q3f_tau_first n hn (Or.inr hia)
    rw [q3f_r, if_pos hia, htau, q3f_root_a n (by omega) hia]
    have hcor : q3f_coroot n i = - q3f_e n 0 - q3f_e n 1 := by
      rw [q3f_coroot, if_pos hia]
    rw [hcor]
    exact q3f_conjD_P_swap01 n (by omega) (by omega) w
  · by_cases hib : i.val = n - 1
    · have htau : q3f_tau n hn i = Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ :=
        q3f_tau_first n hn (Or.inl hib)
      rw [q3f_r, if_neg hia, htau, q3f_root_b n (by omega) hia hib]
      have hcor : q3f_coroot n i = q3f_e n 0 - q3f_e n 1 := by
        rw [q3f_coroot, if_neg hia, if_pos hib]
      rw [hcor]
      exact q3f_P_swap n ⟨0, by omega⟩ ⟨1, by omega⟩
        (by intro h; exact Nat.zero_ne_one (congrArg Fin.val h)) w
    · have hne : ¬ (i.val = n - 1 ∨ i.val = n - 2) := by omega
      have htau : q3f_tau n hn i =
          Equiv.swap ⟨n - 2 - i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩ :=
        q3f_tau_chain n hn hne
      rw [q3f_r, if_neg hia, htau, q3f_root_c n (by omega) hia hib]
      have hcor : q3f_coroot n i = q3f_e n (n - 2 - i.val) - q3f_e n (n - 1 - i.val) := by
        rw [q3f_coroot, if_neg hia, if_neg hib]
      rw [hcor]
      exact q3f_P_swap n ⟨n - 2 - i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩
        (by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_mk] at hh; omega) w

lemma q3f_mem_fixed_range_P (n : ℕ) (hn : 1 ≤ n) (v : Fin n → ZMod 3) :
    (∀ σ : Equiv.Perm (Fin n), q3f_P n σ v = v) ↔ ∃ c : ZMod 3, v = c • q3f_one n := by
  constructor
  · intro h
    refine ⟨v ⟨0, by omega⟩, ?_⟩
    funext j
    have hswap := congrFun (h (Equiv.swap ⟨0, by omega⟩ j)) ⟨0, by omega⟩
    simp only [q3f_P_apply, q3f_permLin_apply, Function.comp_apply, Equiv.symm_swap,
      Equiv.swap_apply_left] at hswap
    simp only [q3f_one, Pi.smul_apply, smul_eq_mul, mul_one]
    exact hswap
  · rintro ⟨c, rfl⟩ σ
    funext i
    simp only [q3f_P_apply, q3f_permLin_apply, Function.comp_apply, Pi.smul_apply, q3f_one,
      smul_eq_mul, mul_one]

lemma q3f_conjD_chain (n : ℕ) (hn : 2 ≤ n) {i : Fin n} (h2 : i.val ≠ n - 2)
    (h1 : i.val ≠ n - 1) :
    q3f_conjD n (q3f_P n (q3f_tau n hn i)) = q3f_P n (q3f_tau n hn i) := by
  have hne : ¬ (i.val = n - 1 ∨ i.val = n - 2) := by omega
  rw [q3f_tau_chain n hn hne]
  exact q3f_conjD_P_swap n ⟨n - 2 - i.val, by omega⟩ ⟨n - 1 - i.val, by omega⟩
    (by intro h; have hh := congrArg Fin.val h; simp only [Fin.val_mk] at hh; omega)
    (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)

lemma q3f_r_eq_conjD (n : ℕ) (hn : 2 ≤ n) (i : Fin n) (hi : i.val ≠ n - 1) :
    q3f_r n hn i = q3f_conjD n (q3f_P n (q3f_tau n hn i)) := by
  by_cases hia : i.val = n - 2
  · rw [q3f_r, if_pos hia]
  · rw [q3f_r, if_neg hia, q3f_conjD_chain n hn hia hi]

@[expose] def q3f_av (m : ℕ) : Fin (m + 1) := ⟨m - 1, by omega⟩

@[expose] def q3f_bv (m : ℕ) : Fin (m + 1) := ⟨m, by omega⟩

lemma q3f_ne_av {m : ℕ} (i : Fin (m + 1)) (hi : i ≠ q3f_av m) : ¬ i.val = m + 1 - 2 := by
  intro hh
  apply hi
  apply Fin.ext
  simp only [q3f_av, Fin.val_mk]
  omega

lemma q3f_ne_bv {m : ℕ} (i : Fin (m + 1)) (hi : i ≠ q3f_bv m) : ¬ i.val = m + 1 - 1 := by
  intro hh
  apply hi
  apply Fin.ext
  simp only [q3f_bv, Fin.val_mk]
  omega

@[expose] noncomputable def q3f_index (m : ℕ) (l : Fin m) :
    {i : Fin (m + 1) // i ≠ q3f_av m} :=
  if hl : l.val = 0 then
    ⟨q3f_bv m, by
      intro h
      have h1 := congrArg Fin.val h
      simp [q3f_av, q3f_bv] at h1
      have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt
      omega⟩
  else
    ⟨⟨m - 1 - l.val, by omega⟩, by
      intro h
      have h1 := congrArg Fin.val h
      simp [q3f_av] at h1
      have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt
      have hlt : l.val < m := l.isLt
      omega⟩

@[expose] noncomputable def q3f_indexK (m : ℕ) (l : Fin m) :
    {i : Fin (m + 1) // i ≠ q3f_bv m} :=
  if hl : l.val = 0 then
    ⟨q3f_av m, by
      intro h
      have h1 := congrArg Fin.val h
      simp [q3f_av, q3f_bv] at h1
      have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt
      omega⟩
  else
    ⟨⟨m - 1 - l.val, by omega⟩, by
      intro h
      have h1 := congrArg Fin.val h
      simp [q3f_bv] at h1
      have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt
      have hlt : l.val < m := l.isLt
      omega⟩

lemma q3f_tau_index (m : ℕ) (l : Fin m) :
    q3f_tau (m + 1)
        (by have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt; omega)
        (q3f_index m l).1 =
      Equiv.swap l.castSucc l.succ := by
  have hm2 : 2 ≤ m + 1 := by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt
    omega
  unfold q3f_index
  split_ifs with hl
  · rw [q3f_tau_first (m + 1) hm2 (Or.inl (show (q3f_bv m).val = m from rfl))]
    congr 1 <;> apply Fin.ext <;> simp [q3f_bv, hl]
  · rw [q3f_tau_chain (m + 1) hm2 (by
      show ¬ (m - 1 - l.val = m + 1 - 1 ∨ m - 1 - l.val = m + 1 - 2)
      have hlt : l.val < m := l.isLt
      omega)]
    congr 1 <;> apply Fin.ext <;> simp <;> omega

lemma q3f_tau_indexK (m : ℕ) (l : Fin m) :
    q3f_tau (m + 1)
        (by have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt; omega)
        (q3f_indexK m l).1 =
      Equiv.swap l.castSucc l.succ := by
  have hm2 : 2 ≤ m + 1 := by
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) l.isLt
    omega
  unfold q3f_indexK
  split_ifs with hl
  · rw [q3f_tau_first (m + 1) hm2 (Or.inr (show (q3f_av m).val = m - 1 from rfl))]
    congr 1 <;> apply Fin.ext <;> simp [q3f_av, hl]
  · rw [q3f_tau_chain (m + 1) hm2 (by
      show ¬ (m - 1 - l.val = m + 1 - 1 ∨ m - 1 - l.val = m + 1 - 2)
      have hlt : l.val < m := l.isLt
      omega)]
    congr 1 <;> apply Fin.ext <;> simp <;> omega

lemma q3f_D_av (m : ℕ) (hm : 5 ≤ m) (c : Fin (m + 1)) (hc : c ≠ q3f_av m) :
    CartanMatrix.D (m + 1) (q3f_av m) c ≠ 0 ↔ c = ⟨m - 2, by omega⟩ := by
  rw [CartanMatrix.D, Matrix.of_apply]
  simp only [q3f_av, Fin.val_mk]
  split_ifs <;> simp_all [q3f_av, Fin.ext_iff] <;> omega

end CFSG.StandardType

end
