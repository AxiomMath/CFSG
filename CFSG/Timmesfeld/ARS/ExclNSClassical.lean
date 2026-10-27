module

public import CFSG.Timmesfeld.ARS.ExclNSForm

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg Matrix

variable {n : ℕ}

@[expose] def ev (n : ℕ) (j : ℕ) : Fin n → ℤ := fun a => if a.val = j then 1 else 0

@[expose] def swapN (k j : ℕ) : ℕ := if j = k then k + 1 else if j = k + 1 then k else j

theorem stdReflB_add (k : Fin n) (e e' : Fin n → ℤ) :
    Spin.stdReflB n k (e + e') = Spin.stdReflB n k e + Spin.stdReflB n k e' := by
  by_cases h : k.val + 1 < n
  · simp only [Spin.stdReflB_of_lt n h]
    rfl
  · simp only [Spin.stdReflB_of_not_lt n h]
    funext a
    simp [mul_add]

theorem stdReflB_neg (k : Fin n) (e : Fin n → ℤ) :
    Spin.stdReflB n k (-e) = -Spin.stdReflB n k e := by
  by_cases h : k.val + 1 < n
  · simp only [Spin.stdReflB_of_lt n h]
    rfl
  · simp only [Spin.stdReflB_of_not_lt n h]
    funext a
    simp

theorem stdReflB_ev_of_lt {k : Fin n} (h : k.val + 1 < n) (j : ℕ) :
    Spin.stdReflB n k (ev n j) = ev n (swapN k.val j) := by
  rw [Spin.stdReflB_of_lt n h]
  funext a
  simp only [Function.comp_apply, ev, swapN, Equiv.swap_apply_def, Fin.ext_iff,
    apply_ite Fin.val]
  split_ifs <;> omega

theorem stdReflB_ev_of_not_lt {k : Fin n} (h : ¬ k.val + 1 < n) (j : ℕ) :
    Spin.stdReflB n k (ev n j) = if j = k.val then -ev n j else ev n j := by
  rw [Spin.stdReflB_of_not_lt n h]
  funext a
  by_cases hj : j = k.val
  · subst hj
    by_cases ha : a = k
    · subst ha
      simp [ev]
    · have ha' : a.val ≠ k.val := fun e => ha (Fin.ext e)
      simp [ev, ha, ha']
  · rw [ite_eq_right hj]
    by_cases ha : a = k
    · subst ha
      have hj' : ¬ a.val = j := fun e => hj e.symm
      simp [ev, hj']
    · simp [ha]

theorem dotProduct_stdReflB (k : Fin n) (e e' : Fin n → ℤ) :
    Spin.stdReflB n k e ⬝ᵥ Spin.stdReflB n k e' = e ⬝ᵥ e' := by
  by_cases h : k.val + 1 < n
  · rw [Spin.stdReflB_of_lt n h, Spin.stdReflB_of_lt n h]
    exact comp_equiv_dotProduct_comp_equiv (x := e) (y := e') _
  · rw [Spin.stdReflB_of_not_lt n h, Spin.stdReflB_of_not_lt n h]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring

theorem ev_eq_single {j : ℕ} (hj : j < n) : ev n j = Pi.single (⟨j, hj⟩ : Fin n) 1 := by
  funext a
  simp only [ev, Pi.single_apply, Fin.ext_iff]

theorem dotProduct_ev (e : Fin n → ℤ) {j : ℕ} (hj : j < n) : e ⬝ᵥ ev n j = e ⟨j, hj⟩ := by
  rw [ev_eq_single hj, dotProduct_single, mul_one]

theorem ev_dotProduct (e : Fin n → ℤ) {j : ℕ} (hj : j < n) : ev n j ⬝ᵥ e = e ⟨j, hj⟩ := by
  rw [dotProduct_comm, dotProduct_ev e hj]

theorem ev_dotProduct_ev (a b : ℕ) : ev n a ⬝ᵥ ev n b = if a = b ∧ a < n then 1 else 0 := by
  by_cases ha : a < n
  · rw [ev_dotProduct _ ha]
    simp only [ev]
    by_cases hab : a = b
    · subst hab
      simp [ha]
    · simp [hab]
  · have h0 : ev n a = 0 := by
      funext c
      have : c.val ≠ a := by omega
      simp [ev, this]
    rw [h0, zero_dotProduct]
    simp [ha]

theorem stdReflB_smul (k : Fin n) (x : ℤ) (e : Fin n → ℤ) :
    Spin.stdReflB n k (x • e) = x • Spin.stdReflB n k e := by
  by_cases h : k.val + 1 < n
  · simp only [Spin.stdReflB_of_lt n h]
    rfl
  · simp only [Spin.stdReflB_of_not_lt n h]
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem comp_swap_eq_self_iff (e : Fin n → ℤ) (a b : Fin n) :
    e ∘ Equiv.swap a b = e ↔ e a = e b := by
  constructor
  · intro h
    have := congrFun h a
    simp only [Function.comp_apply, Equiv.swap_apply_left] at this
    exact this.symm
  · intro h
    funext c
    simp only [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl

theorem reflection_eq_self_iff (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) (v : Fin n → ℤ) :
    reflection A k v = v ↔ coroot A k v = 0 := by
  rw [reflection_apply_coroot, sub_eq_self]
  constructor
  · intro h
    have := congrFun h k
    simpa using this
  · intro h
    rw [h, zero_smul]

structure EpsCoords (A : Matrix (Fin n) (Fin n) ℤ) where
  E : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)
  inj : Function.Injective E
  refl : ∀ k v, E (reflection A k v) = Spin.stdReflB n k (E v)
  single : ∀ (k : Fin n), k.val + 1 < n → E (Pi.single k 1) = ev n k.val - ev n (k.val + 1)
  c : ℤ
  c_pos : 0 < c
  c_le : c ≤ 2
  last : ∀ (k : Fin n), ¬ k.val + 1 < n → E (Pi.single k 1) = c • ev n k.val

namespace EpsCoords

variable {A : Matrix (Fin n) (Fin n) ℤ} (P : EpsCoords A)

@[expose] def invForm : InvForm A where
  Q := LinearMap.mk₂ ℤ (fun x y => P.E x ⬝ᵥ P.E y)
    (fun x x' y => by rw [map_add, add_dotProduct])
    (fun c x y => by rw [map_smul, smul_dotProduct])
    (fun x y y' => by rw [map_add, dotProduct_add])
    (fun c x y => by rw [map_smul, dotProduct_smul])
  symm x y := by
    simp only [LinearMap.mk₂_apply]
    exact dotProduct_comm _ _
  refl k x y := by
    simp only [LinearMap.mk₂_apply, P.refl, dotProduct_stdReflB]
  coroot_iff k x := by
    simp only [LinearMap.mk₂_apply]
    rw [← reflection_eq_self_iff, ← P.inj.eq_iff, P.refl]
    by_cases h : k.val + 1 < n
    · rw [P.single k h, Spin.stdReflB_of_lt n h, comp_swap_eq_self_iff, dotProduct_sub,
        dotProduct_ev _ k.isLt, dotProduct_ev _ h, sub_eq_zero]
    · rw [P.last k h, dotProduct_smul, dotProduct_ev _ k.isLt, smul_eq_mul,
        Spin.stdReflB_of_not_lt n h]
      have hc := P.c_pos.ne'
      constructor
      · intro h0
        have h1 : P.E x k = 0 := (mul_eq_zero.1 h0).resolve_left hc
        funext a
        by_cases ha : a = k
        · subst ha
          simp [h1]
        · simp [ha]
      · intro h0
        have := congrFun h0 k
        simp only [ite_true] at this
        have h1 : P.E x k = 0 := by linarith
        rw [h1, mul_zero]

theorem invForm_apply (x y : Fin n → ℤ) : P.invForm.Q x y = P.E x ⬝ᵥ P.E y := rfl

theorem invForm_single_le (k : Fin n) : P.invForm.Q (Pi.single k 1) (Pi.single k 1) ≤ 4 := by
  rw [invForm_apply]
  by_cases h : k.val + 1 < n
  · rw [P.single k h]
    simp only [sub_dotProduct, dotProduct_sub, ev_dotProduct_ev, true_and]
    split_ifs <;> omega
  · rw [P.last k h]
    simp only [smul_dotProduct, dotProduct_smul, ev_dotProduct_ev, k.isLt, and_self, ite_true,
      smul_eq_mul, mul_one]
    nlinarith [P.c_pos, P.c_le]

theorem invForm_single_of_lt {k : Fin n} (h : k.val + 1 < n) :
    P.invForm.Q (Pi.single k 1) (Pi.single k 1) = 2 := by
  rw [invForm_apply, P.single k h]
  simp only [sub_dotProduct, dotProduct_sub, ev_dotProduct_ev, true_and]
  split_ifs <;> omega

theorem invForm_single_ne_of_not_lt {k : Fin n} (h : ¬ k.val + 1 < n) :
    P.invForm.Q (Pi.single k 1) (Pi.single k 1) ≠ 2 := by
  rw [invForm_apply, P.last k h]
  simp only [smul_dotProduct, dotProduct_smul, ev_dotProduct_ev, k.isLt, and_self, ite_true,
    smul_eq_mul, mul_one]
  have h1 := P.c_pos
  have h2 := P.c_le
  intro he
  have : P.c = 1 ∨ P.c = 2 := by omega
  rcases this with h3 | h3 <;> rw [h3] at he <;> omega

end EpsCoords

section Comb

variable {A : Matrix (Fin n) (Fin n) ℤ} (P : EpsCoords A) {S : Set (Fin n → ℤ)}

@[expose] def epsSet (P : EpsCoords A) (S : Set (Fin n → ℤ)) : Set (Fin n → ℤ) := P.E '' S

include P in
theorem epsSet_step (hinv : ∀ t, -Pi.single t 1 ∉ S → ∀ β ∈ S, reflection A t β ∈ S)
    {e : Fin n → ℤ} (he : e ∈ epsSet P S) {t : Fin n} (ht : -Pi.single t 1 ∉ S) :
    Spin.stdReflB n t e ∈ epsSet P S := by
  obtain ⟨β, hβ, rfl⟩ := he
  exact ⟨_, hinv t ht β hβ, P.refl t β⟩

theorem E_neg_single {k : Fin n} (h : k.val + 1 < n) :
    P.E (-Pi.single k 1) = -ev n k.val + ev n (k.val + 1) := by
  rw [map_neg, P.single k h]
  abel

theorem val_eq_zero_of_neg_single_mem
    (hnorm : ∀ β ∈ S, P.invForm.Q β β = 2)
    (hinv : ∀ t, -Pi.single t 1 ∉ S → ∀ β ∈ S, reflection A t β ∈ S)
    (hobt : ∀ β ∈ S, ∀ β' ∈ S, 0 ≤ P.invForm.Q β' β) {s : Fin n}
    (hs : -Pi.single s 1 ∈ S) : s.val = 0 := by
  have hob : ∀ e ∈ epsSet P S, ∀ e' ∈ epsSet P S, 0 ≤ e' ⬝ᵥ e := by
    rintro _ ⟨β, hβ, rfl⟩ _ ⟨β', hβ', rfl⟩
    exact hobt β hβ β' hβ'
  have hshort : ∀ t : Fin n, -Pi.single t 1 ∈ S → t.val + 1 < n := by
    intro t ht
    by_contra h
    apply P.invForm_single_ne_of_not_lt h
    have := hnorm _ ht
    simpa using this
  have hs1 := hshort s hs
  by_contra hs0
  have hs'1 : (s.val - 1) + 1 < n := by omega
  have hβ0 : -ev n s.val + ev n (s.val + 1) ∈ epsSet P S := ⟨_, hs, E_neg_single P hs1⟩
  by_cases h1 : -Pi.single (⟨s.val - 1, by omega⟩ : Fin n) 1 ∈ S
  ·
    have h2 : -ev n (s.val - 1) + ev n (s.val - 1 + 1) ∈ epsSet P S :=
      ⟨_, h1, E_neg_single P (k := ⟨s.val - 1, by omega⟩) hs'1⟩
    have h3 := hob _ hβ0 _ h2
    simp only [neg_dotProduct, add_dotProduct, dotProduct_neg, dotProduct_add,
      ev_dotProduct_ev] at h3
    split_ifs at h3 <;> omega
  have hswap : ∀ (u : ℕ) (hu : u + 1 < n), -Pi.single (⟨u, by omega⟩ : Fin n) 1 ∉ S →
      ∀ a b : ℕ, ∀ x y : ℤ, x • ev n a + y • ev n b ∈ epsSet P S →
        x • ev n (swapN u a) + y • ev n (swapN u b) ∈ epsSet P S := by
    intro u hu hnot a b x y he
    have := epsSet_step P hinv he hnot
    rwa [stdReflB_add, stdReflB_smul, stdReflB_smul, stdReflB_ev_of_lt (k := ⟨u, by omega⟩) hu,
      stdReflB_ev_of_lt (k := ⟨u, by omega⟩) hu] at this
  have hβ0' : (-1 : ℤ) • ev n s.val + (1 : ℤ) • ev n (s.val + 1) ∈ epsSet P S := by
    simpa [neg_one_smul, one_smul] using hβ0
  have hcontra : ∀ a b : ℕ, ∀ x y : ℤ, x • ev n a + y • ev n b ∈ epsSet P S →
      a < n → b < n → (x • ev n a + y • ev n b) ⬝ᵥ (-ev n s.val + ev n (s.val + 1)) < 0 →
      False := by
    intro a b x y he ha hb hneg
    have := hob _ hβ0 _ he
    linarith
  by_cases hB1 : ∃ j, ∃ hj : j < n, s.val < j ∧ -Pi.single (⟨j, hj⟩ : Fin n) 1 ∈ S
  ·
    classical
    set t := Nat.find hB1 with ht
    obtain ⟨htn, hst, htS⟩ := Nat.find_spec hB1
    have hmin : ∀ j (hj : j < n), s.val < j → j < t → -Pi.single (⟨j, hj⟩ : Fin n) 1 ∉ S :=
      fun j hj hsj hjt hjS => Nat.find_min hB1 hjt ⟨hj, hsj, hjS⟩
    have ht1 : t + 1 < n := hshort ⟨t, htn⟩ htS
    have key : ∀ k, k ≤ t - s.val - 1 →
        (-1 : ℤ) • ev n (t - k) + (1 : ℤ) • ev n (t + 1) ∈ epsSet P S := by
      intro k
      induction k with
      | zero =>
        intro _
        have := E_neg_single P (k := ⟨t, htn⟩) ht1
        refine ⟨_, htS, ?_⟩
        rw [this]
        simp
      | succ k ih =>
        intro hk
        have h2 := hswap (t - k - 1) (by omega) (hmin _ _ (by omega) (by omega)) _ _ _ _
          (ih (by omega))
        have e1 : swapN (t - k - 1) (t - k) = t - (k + 1) := by
          simp only [swapN]
          split_ifs <;> omega
        have e2 : swapN (t - k - 1) (t + 1) = t + 1 := by
          simp only [swapN]
          split_ifs <;> omega
        rwa [e1, e2] at h2
    have h3 := key (t - s.val - 1) le_rfl
    refine hcontra _ _ _ _ h3 (by omega) ht1 ?_
    have e : t - (t - s.val - 1) = s.val + 1 := by omega
    rw [e]
    simp only [neg_one_smul, one_smul, neg_dotProduct, add_dotProduct, dotProduct_neg,
      dotProduct_add, ev_dotProduct_ev, true_and]
    split_ifs <;> omega
  · simp only [not_exists, not_and] at hB1
    have hnot : ∀ j (hj : j < n), s.val < j → -Pi.single (⟨j, hj⟩ : Fin n) 1 ∉ S :=
      fun j hj hsj => hB1 j hj hsj
    have up : ∀ k, s.val + 1 + k < n →
        (-1 : ℤ) • ev n s.val + (1 : ℤ) • ev n (s.val + 1 + k) ∈ epsSet P S := by
      intro k
      induction k with
      | zero => intro _; simpa using hβ0'
      | succ k ih =>
        intro hk
        have h2 := hswap (s.val + 1 + k) (by omega) (hnot _ _ (by omega)) _ _ _ _ (ih (by omega))
        have e1 : swapN (s.val + 1 + k) s.val = s.val := by
          simp only [swapN]
          split_ifs <;> omega
        have e2 : swapN (s.val + 1 + k) (s.val + 1 + k) = s.val + 1 + (k + 1) := by
          simp only [swapN]
          split_ifs <;> omega
        rwa [e1, e2] at h2
    have hlast : (-1 : ℤ) • ev n s.val + (-1 : ℤ) • ev n (n - 1) ∈ epsSet P S := by
      have h2 := up (n - 1 - (s.val + 1)) (by omega)
      have e : s.val + 1 + (n - 1 - (s.val + 1)) = n - 1 := by omega
      rw [e] at h2
      have h3 := epsSet_step P hinv h2 (t := ⟨n - 1, by omega⟩) (hnot _ _ (by omega))
      rwa [stdReflB_add, stdReflB_smul, stdReflB_smul,
        stdReflB_ev_of_not_lt (k := ⟨n - 1, by omega⟩) (by simp; omega),
        stdReflB_ev_of_not_lt (k := ⟨n - 1, by omega⟩) (by simp; omega),
        ite_eq_right (by simp; omega), ite_eq_left rfl, smul_neg, ← neg_smul] at h3
    have down : ∀ k, s.val + 1 + k ≤ n - 1 →
        (-1 : ℤ) • ev n s.val + (-1 : ℤ) • ev n (n - 1 - k) ∈ epsSet P S := by
      intro k
      induction k with
      | zero => intro _; simpa using hlast
      | succ k ih =>
        intro hk
        have h2 := hswap (n - 1 - k - 1) (by omega) (hnot _ _ (by omega)) _ _ _ _ (ih (by omega))
        have e1 : swapN (n - 1 - k - 1) s.val = s.val := by
          simp only [swapN]
          split_ifs <;> omega
        have e2 : swapN (n - 1 - k - 1) (n - 1 - k) = n - 1 - (k + 1) := by
          simp only [swapN]
          split_ifs <;> omega
        rwa [e1, e2] at h2
    have h4 := down (n - 1 - (s.val + 1)) (by omega)
    have e : n - 1 - (n - 1 - (s.val + 1)) = s.val + 1 := by omega
    rw [e] at h4
    have h5 := hswap (s.val - 1) (by omega) h1 _ _ _ _ h4
    have e1 : swapN (s.val - 1) s.val = s.val - 1 := by
      simp only [swapN]
      split_ifs <;> omega
    have e2 : swapN (s.val - 1) (s.val + 1) = s.val + 1 := by
      simp only [swapN]
      split_ifs <;> omega
    rw [e1, e2] at h5
    refine hcontra _ _ _ _ h5 (by omega) (by omega) ?_
    simp only [neg_one_smul, neg_dotProduct, add_dotProduct, dotProduct_neg, dotProduct_add,
      ev_dotProduct_ev, true_and]
    split_ifs <;> omega

end Comb

@[expose] def toStdBLin' (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := Spin.toStdB n
  map_add' := Spin.toStdB_add n
  map_smul' c v := Spin.toStdB_smul n c v

@[expose] def epsB (n : ℕ) : EpsCoords (Spin.cartanB n) where
  E := toStdBLin' n
  inj := Spin.toStdB_injective n
  refl k v := Spin.toStdB_reflection n k v
  single k h := by
    change Spin.toStdB n _ = _
    rw [Spin.toStdB_single_of_lt n h, ev_eq_single k.isLt, ev_eq_single h]
  c := 1
  c_pos := one_pos
  c_le := by norm_num
  last k h := by
    change Spin.toStdB n _ = _
    rw [Spin.toStdB_single_of_not_lt n h, ev_eq_single k.isLt, one_smul]

@[expose] def toStdCLin (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := Symplectic.toStd n
  map_add' := Symplectic.SpExtras.toStd_add'
  map_smul' c v := Symplectic.SpExtras.toStd_zsmul' c v

theorem toStdCLin_apply (v : Fin n → ℤ) : toStdCLin n v = Symplectic.toStd n v := rfl

theorem coroot_cartanC_of_lt' {k : Fin n} (h : k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (Symplectic.cartanC n) k v =
      Symplectic.toStd n v k - Symplectic.toStd n v ⟨k.val + 1, h⟩ := by
  have key : coroot (Symplectic.cartanC n) k =
      ((LinearMap.proj k : (Fin n → ℤ) →ₗ[ℤ] ℤ) - LinearMap.proj (⟨k.val + 1, h⟩ : Fin n)).comp
        (toStdCLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdCLin_apply, Symplectic.toStd,
      Symplectic.cartanC, Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

theorem coroot_cartanC_of_not_lt' {k : Fin n} (h : ¬ k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (Symplectic.cartanC n) k v = Symplectic.toStd n v k := by
  have key : coroot (Symplectic.cartanC n) k = (LinearMap.proj k).comp (toStdCLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single, coroot_single,
      toStdCLin_apply, Symplectic.toStd, Symplectic.cartanC, Matrix.of_apply, Pi.single_apply,
      Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

theorem toStd_reflection' (k : Fin n) (v : Fin n → ℤ) :
    Symplectic.toStd n (reflection (Symplectic.cartanC n) k v) =
      Spin.stdReflB n k (Symplectic.toStd n v) := by
  rw [reflection_apply_coroot, ← toStdCLin_apply, map_sub, map_zsmul, toStdCLin_apply,
    toStdCLin_apply]
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanC_of_lt' h, Symplectic.SpExtras.toStd_single_of_lt' h,
      Spin.stdReflB_of_lt n h]
    have hne : (⟨k.val + 1, h⟩ : Fin n) ≠ k := Fin.ne_of_val_ne (by simp)
    funext a
    by_cases ha : a = k
    · subst ha
      simp [Ne.symm hne]
    by_cases ha' : a = ⟨k.val + 1, h⟩
    · subst ha'
      simp [hne]
    · simp [ha, ha', Equiv.swap_apply_of_ne_of_ne ha ha']
  · rw [coroot_cartanC_of_not_lt' h, Symplectic.SpExtras.toStd_single_of_not_lt' h,
      Spin.stdReflB_of_not_lt n h]
    funext a
    by_cases ha : a = k
    · subst ha
      simp only [Pi.sub_apply, Pi.smul_apply, two_nsmul, Pi.add_apply, Pi.single_eq_same,
        smul_eq_mul, ite_true]
      ring
    · simp [ha]

@[expose] def epsC (n : ℕ) : EpsCoords (Symplectic.cartanC n) where
  E := toStdCLin n
  inj := Symplectic.SpExtras.toStd_inj
  refl k v := toStd_reflection' k v
  single k h := by
    rw [toStdCLin_apply, Symplectic.SpExtras.toStd_single_of_lt' h, ev_eq_single k.isLt,
      ev_eq_single h]
  c := 2
  c_pos := two_pos
  c_le := le_rfl
  last k h := by
    rw [toStdCLin_apply, Symplectic.SpExtras.toStd_single_of_not_lt' h, ev_eq_single k.isLt]
    rw [← natCast_zsmul]
    norm_num

end CFSG.Timmesfeld.ARS.ExclNS
