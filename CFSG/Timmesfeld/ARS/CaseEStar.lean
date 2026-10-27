module

public import CFSG.Timmesfeld.ARS.CaseENonSph

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.RootSystem CFSG.LieType.Universal

namespace CaseE

section Basis

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} {J : Type} [Fintype J]

theorem cartanPair_eq_sum_of_basis (L : (I → ℤ) →ₗ[ℤ] (J → ℤ))
    (hL : ∀ k l, A k l = ∑ x, L (Pi.single l 1) x * L (Pi.single k 1) x) (u v : I → ℤ) :
    cartanPair A u v = ∑ x, L u x * L v x := by
  classical
  have hc : ∀ k, coroot A k u = ∑ x, L u x * L (Pi.single k 1) x := fun k => by
    conv_lhs => rw [← sum_smul_single u]
    conv_rhs => rw [← sum_smul_single u]
    simp only [map_sum, map_zsmul, coroot_single, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hL k l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  unfold cartanPair
  conv_rhs => rw [← sum_smul_single v]
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end Basis

theorem sum_single_sub_mul {J : Type} [Fintype J] [DecidableEq J] (a b c d : J) :
    ∑ x, (Pi.single a (1 : ℤ) - Pi.single b 1 : J → ℤ) x *
        (Pi.single c (1 : ℤ) - Pi.single d 1 : J → ℤ) x =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0) +
        (if b = d then 1 else 0) := by
  have key : ∀ (e : J) (g : J → ℤ), ∑ x, (Pi.single e (1 : ℤ) : J → ℤ) x * g x = g e :=
    fun e g => by
      rw [Finset.sum_eq_single e (fun x _ hx => by rw [Pi.single_eq_of_ne hx, zero_mul])
        (fun h => absurd (Finset.mem_univ e) h)]
      simp
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [key a, key b]
  simp only [Pi.single_apply]
  ring

section TypeA

variable (m : ℕ)

@[expose] def toStdLin : (Fin m → ℤ) →ₗ[ℤ] (Fin (m + 1) → ℤ) where
  toFun := SpecialLinear.toStd m
  map_add' v w := by
    funext a
    simp only [SpecialLinear.toStd, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext a
    simp only [SpecialLinear.toStd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem toStdLin_apply (v : Fin m → ℤ) : toStdLin m v = SpecialLinear.toStd m v := rfl

theorem cartanPair_A (u v : Fin m → ℤ) :
    cartanPair (CartanMatrix.A m) u v =
      ∑ x, SpecialLinear.toStd m u x * SpecialLinear.toStd m v x := by
  refine cartanPair_eq_sum_of_basis (toStdLin m) (fun k l => ?_) u v
  simp only [toStdLin_apply, SpecialLinear.toStd_single, sum_single_sub_mul, CartanMatrix.A,
    Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

theorem sum_le_toStd (v : Fin m → ℤ) (j : Fin m) :
    ∑ x : Fin (m + 1), (if x.val ≤ j.val then SpecialLinear.toStd m v x else 0) = v j := by
  classical
  have h1 : ∀ w : Fin m → ℤ, ∑ x : Fin (m + 1), (if x.val ≤ j.val then
      SpecialLinear.toStd m w x else 0) = ∑ l, w l * ∑ x : Fin (m + 1),
        (if x.val ≤ j.val then SpecialLinear.toStd m (Pi.single l 1) x else 0) := fun w => by
    conv_lhs => rw [← sum_smul_single w]
    simp only [← toStdLin_apply, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    simp only [← Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h1]
  have hs : ∀ p : Fin (m + 1), ∑ x : Fin (m + 1),
      (if x.val ≤ j.val then (Pi.single p (1 : ℤ) : Fin (m + 1) → ℤ) x else 0) =
        if p.val ≤ j.val then 1 else 0 := fun p => by
    rw [Finset.sum_eq_single p (fun x _ hx => by rw [Pi.single_eq_of_ne hx, ite_self])
      (fun h => absurd (Finset.mem_univ p) h)]
    simp
  have h2 : ∀ l : Fin m, ∑ x : Fin (m + 1), (if x.val ≤ j.val then
      SpecialLinear.toStd m (Pi.single l 1) x else 0) = if l = j then 1 else 0 := fun l => by
    have e : ∀ x : Fin (m + 1), (if x.val ≤ j.val then
        SpecialLinear.toStd m (Pi.single l 1) x else 0) =
        (if x.val ≤ j.val then (Pi.single l.castSucc (1 : ℤ) : Fin (m + 1) → ℤ) x else 0) -
          (if x.val ≤ j.val then (Pi.single l.succ (1 : ℤ) : Fin (m + 1) → ℤ) x else 0) :=
      fun x => by
        rw [SpecialLinear.toStd_single, Pi.sub_apply]
        split_ifs <;> simp
    simp only [e, Finset.sum_sub_distrib, hs, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
    split_ifs <;> omega
  simp only [h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]



@[expose] def intervalVec (a b : ℕ) : Fin m → ℤ := fun k => if a ≤ k.val ∧ k.val < b then 1 else 0

theorem toStd_intervalVec {a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    SpecialLinear.toStd m (intervalVec m a b) =
      Pi.single (⟨a, by omega⟩ : Fin (m + 1)) 1 - Pi.single (⟨b, by omega⟩ : Fin (m + 1)) 1 := by
  funext x
  simp only [SpecialLinear.toStd, intervalVec, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem sum_le_single (j : ℕ) (p : Fin (m + 1)) :
    ∑ x : Fin (m + 1), (if x.val ≤ j then (Pi.single p (1 : ℤ) : Fin (m + 1) → ℤ) x else 0) =
      if p.val ≤ j then 1 else 0 := by
  rw [Finset.sum_eq_single p (fun x _ hx => by rw [Pi.single_eq_of_ne hx, ite_self])
    (fun h => absurd (Finset.mem_univ p) h)]
  simp

theorem level_of_toStd {j : Fin m} {c d : Fin (m + 1)} {γ : Fin m → ℤ}
    (hγe : SpecialLinear.toStd m γ = Pi.single c 1 - Pi.single d 1) (hγj : γ j = 1) :
    c.val ≤ j.val ∧ j.val < d.val := by
  have h := sum_le_toStd m γ j
  rw [hγj, hγe] at h
  have e : ∀ x : Fin (m + 1), (if x.val ≤ j.val then
      (Pi.single c (1 : ℤ) - Pi.single d 1 : Fin (m + 1) → ℤ) x else 0) =
      (if x.val ≤ j.val then (Pi.single c (1 : ℤ) : Fin (m + 1) → ℤ) x else 0) -
        (if x.val ≤ j.val then (Pi.single d (1 : ℤ) : Fin (m + 1) → ℤ) x else 0) := fun x => by
    rw [Pi.sub_apply]
    split_ifs <;> simp
  simp only [e, Finset.sum_sub_distrib, sum_le_single] at h
  split_ifs at h <;> omega

theorem exists_root_A {j : Fin m} {c d : Fin (m + 1)} {γ : Fin m → ℤ}
    (hγe : SpecialLinear.toStd m γ = Pi.single c 1 - Pi.single d 1) (hcj : c.val ≤ j.val)
    (hdj : j.val < d.val) {a b : ℕ} (ha : a < j.val) (hb1 : j.val + 2 ≤ b) (hb2 : b ≤ m)
    (hac : a ≠ c.val) (hbd : b ≠ d.val) :
    intervalVec m a b ∈ roots (SpecialLinear.isFiniteType_A m) ∅ ∧ intervalVec m a b j = 1 ∧
      coroot (CartanMatrix.A m) j (intervalVec m a b) = 0 ∧
      cartanPair (CartanMatrix.A m) (intervalVec m a b) γ = 0 := by
  have hst := toStd_intervalVec m (a := a) (b := b) (by omega) hb2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [SpecialLinear.roots_eq]
    exact ⟨_, _, fun e => by
      have := congrArg Fin.val e
      simp only at this
      omega, hst⟩
  · simp only [intervalVec]
    split_ifs with h
    · rfl
    · exact absurd ⟨by omega, by omega⟩ h
  · rw [← cartanPair_single, cartanPair_A, hst, SpecialLinear.toStd_single, sum_single_sub_mul]
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · rw [cartanPair_A, hst, hγe, sum_single_sub_mul]
    simp only [Fin.ext_iff]
    split_ifs <;> omega

theorem starAt_A {j : Fin m} (ha : 2 ≤ j.val) (hb : j.val + 3 ≤ m)
    (hab : 3 ≤ j.val ∨ j.val + 4 ≤ m) :
    StarAt (CartanMatrix.A m) (SpecialLinear.isFiniteType_A m) j := by
  intro γ hγ hγj
  rw [SpecialLinear.roots_eq] at hγ
  obtain ⟨c, d, -, hγe⟩ := hγ
  obtain ⟨hcj, hdj⟩ := level_of_toStd m hγe hγj
  obtain ⟨a₁, b₁, a₂, b₂, hne, ⟨h11, h12, h13, h14, h15⟩, ⟨h21, h22, h23, h24, h25⟩⟩ :
      ∃ a₁ b₁ a₂ b₂ : ℕ, (a₁ ≠ a₂ ∨ b₁ ≠ b₂) ∧
        (a₁ < j.val ∧ j.val + 2 ≤ b₁ ∧ b₁ ≤ m ∧ a₁ ≠ c.val ∧ b₁ ≠ d.val) ∧
        (a₂ < j.val ∧ j.val + 2 ≤ b₂ ∧ b₂ ≤ m ∧ a₂ ≠ c.val ∧ b₂ ≠ d.val) := by
    rcases hab with h3 | h4
    · obtain ⟨b, hb1, hb2, hb3⟩ : ∃ b, j.val + 2 ≤ b ∧ b ≤ m ∧ b ≠ d.val := by
        by_cases hd : d.val = j.val + 2
        · exact ⟨j.val + 3, by omega, by omega, by omega⟩
        · exact ⟨j.val + 2, le_rfl, by omega, fun h => hd h.symm⟩
      by_cases hc0 : c.val = 0
      · exact ⟨1, b, 2, b, Or.inl (by omega), ⟨by omega, hb1, hb2, by omega, hb3⟩,
          ⟨by omega, hb1, hb2, by omega, hb3⟩⟩
      · by_cases hc1 : c.val = 1
        · exact ⟨0, b, 2, b, Or.inl (by omega), ⟨by omega, hb1, hb2, by omega, hb3⟩,
            ⟨by omega, hb1, hb2, by omega, hb3⟩⟩
        · exact ⟨0, b, 1, b, Or.inl (by omega), ⟨by omega, hb1, hb2, by omega, hb3⟩,
            ⟨by omega, hb1, hb2, by omega, hb3⟩⟩
    · obtain ⟨a, ha1, ha2⟩ : ∃ a, a < j.val ∧ a ≠ c.val := by
        by_cases hc : c.val = 0
        · exact ⟨1, by omega, by omega⟩
        · exact ⟨0, by omega, fun h => hc h.symm⟩
      by_cases hd2 : d.val = j.val + 2
      · exact ⟨a, j.val + 3, a, j.val + 4, Or.inr (by omega),
          ⟨ha1, by omega, by omega, ha2, by omega⟩, ⟨ha1, by omega, by omega, ha2, by omega⟩⟩
      · by_cases hd3 : d.val = j.val + 3
        · exact ⟨a, j.val + 2, a, j.val + 4, Or.inr (by omega),
            ⟨ha1, by omega, by omega, ha2, by omega⟩, ⟨ha1, by omega, by omega, ha2, by omega⟩⟩
        · exact ⟨a, j.val + 2, a, j.val + 3, Or.inr (by omega),
            ⟨ha1, by omega, by omega, ha2, by omega⟩, ⟨ha1, by omega, by omega, ha2, by omega⟩⟩
  obtain ⟨r1, l1, c1, p1⟩ := exists_root_A m hγe hcj hdj h11 h12 h13 h14 h15
  obtain ⟨r2, l2, c2, p2⟩ := exists_root_A m hγe hcj hdj h21 h22 h23 h24 h25
  refine ⟨intervalVec m a₁ b₁, intervalVec m a₂ b₂, fun e => ?_, ?_⟩
  · have h := congrArg (SpecialLinear.toStd m) e
    rw [toStd_intervalVec m (by omega) h13, toStd_intervalVec m (by omega) h23] at h
    rcases hne with hne | hne
    · have h' := congrFun h ⟨a₁, by omega⟩
      simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff] at h'
      split_ifs at h' <;> omega
    · have h' := congrFun h ⟨b₁, by omega⟩
      simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff] at h'
      split_ifs at h' <;> omega
  · rintro β (rfl | rfl)
    · exact ⟨r1, l1, c1, p1⟩
    · exact ⟨r2, l2, c2, p2⟩

end TypeA

section TypeD

variable (n : ℕ)


@[expose] def toStdDLin : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := Spin.toStdD n
  map_add' := Spin.toStdD_add n
  map_smul' := Spin.toStdD_smul n

theorem sum_single_add_mul {J : Type} [Fintype J] [DecidableEq J] (a b : J) (s t : ℤ)
    (w : J → ℤ) :
    ∑ x, (Pi.single a s + Pi.single b t : J → ℤ) x * w x = s * w a + t * w b := by
  have key : ∀ (e : J) (r : ℤ), ∑ x, (Pi.single e r : J → ℤ) x * w x = r * w e := fun e r => by
    rw [Finset.sum_eq_single e (fun x _ hx => by rw [Pi.single_eq_of_ne hx, zero_mul])
      (fun h => absurd (Finset.mem_univ e) h)]
    simp
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, key]

theorem sum_mul_single_sub {J : Type} [Fintype J] [DecidableEq J] (w : J → ℤ) (a b : J) :
    ∑ x, w x * (Pi.single a 1 - Pi.single b 1 : J → ℤ) x = w a - w b := by
  have e : (Pi.single a 1 - Pi.single b 1 : J → ℤ) = Pi.single a 1 + Pi.single b (-1) := by
    funext x
    by_cases hx : x = b <;> simp [Pi.single_apply, hx, sub_eq_add_neg]
  simp only [mul_comm (w _), e, sum_single_add_mul]
  ring

theorem sum_mul_single_add {J : Type} [Fintype J] [DecidableEq J] (w : J → ℤ) (a b : J) :
    ∑ x, w x * (Pi.single a 1 + Pi.single b 1 : J → ℤ) x = w a + w b := by
  simp only [mul_comm (w _), sum_single_add_mul]
  ring

variable {n}

theorem coroot_D_eq_sum (hn : 2 ≤ n) (k : Fin n) (v : Fin n → ℤ) :
    coroot (Spin.cartanD n) k v = ∑ x, Spin.toStdD n v x * Spin.toStdD n (Pi.single k 1) x := by
  by_cases h : k.val + 1 < n
  · rw [Spin.coroot_cartanD_of_lt n h, Spin.toStdD_single_of_lt n h, sum_mul_single_sub]
  · rw [Spin.coroot_cartanD_of_not_lt n h, Spin.toStdD_single_of_not_lt n h hn,
      sum_mul_single_add]
    congr 2
    exact Fin.ext (by simp only; omega)

theorem cartanPair_D (hn : 2 ≤ n) (u v : Fin n → ℤ) :
    cartanPair (Spin.cartanD n) u v = ∑ x, Spin.toStdD n u x * Spin.toStdD n v x :=
  cartanPair_eq_sum_of_basis (toStdDLin n) (fun k l => by
    rw [← coroot_single (Spin.cartanD n) k l, coroot_D_eq_sum hn]
    rfl) u v

theorem sum_toStdD (hn : 2 ≤ n) (v : Fin n → ℤ) :
    ∑ x, Spin.toStdD n v x = 2 * v ⟨n - 1, by omega⟩ := by
  let f : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ x, Spin.toStdD n v x
      map_zero' := by simp [Spin.toStdD_zero]
      map_add' := fun v w => by simp [Spin.toStdD_add, Finset.sum_add_distrib] }
  let g : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => 2 * v ⟨n - 1, by omega⟩
      map_zero' := by simp
      map_add' := fun v w => by simp only [Pi.add_apply]; ring }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun l x => ?_
    have hs : (Pi.single l x : Fin n → ℤ) = x • Pi.single l 1 := by
      funext i
      simp [Pi.single_apply]
    have hone : ∀ w : Fin n → ℤ, ∑ y, w y = ∑ y, (fun _ => (1 : ℤ)) y * w y := fun w => by
      simp
    simp only [f, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hs, Spin.toStdD_smul, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum]
    rw [hone]
    by_cases h : l.val + 1 < n
    · rw [Spin.toStdD_single_of_lt n h, sum_mul_single_sub]
      simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    · rw [Spin.toStdD_single_of_not_lt n h hn, sum_mul_single_add]
      simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  exact congrArg (fun φ : (Fin n → ℤ) →+ ℤ => φ v) hfg

theorem sum_sign_toStdD (hn : 2 ≤ n) (v : Fin n → ℤ) :
    ∑ x, (if x.val + 1 = n then -1 else 1) * Spin.toStdD n v x = 2 * v ⟨n - 2, by omega⟩ := by
  let f : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ x, (if x.val + 1 = n then -1 else 1) * Spin.toStdD n v x
      map_zero' := by simp [Spin.toStdD_zero]
      map_add' := fun v w => by simp [Spin.toStdD_add, Finset.sum_add_distrib, mul_add] }
  let g : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => 2 * v ⟨n - 2, by omega⟩
      map_zero' := by simp
      map_add' := fun v w => by simp only [Pi.add_apply]; ring }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun l x => ?_
    have hs : (Pi.single l x : Fin n → ℤ) = x • Pi.single l 1 := by
      funext i
      simp [Pi.single_apply]
    simp only [f, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hs, Spin.toStdD_smul, Pi.smul_apply,
      smul_eq_mul, mul_left_comm _ x, ← Finset.mul_sum]
    by_cases h : l.val + 1 < n
    · rw [Spin.toStdD_single_of_lt n h,
        sum_mul_single_sub (fun y : Fin n => if y.val + 1 = n then (-1 : ℤ) else 1)]
      simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    · rw [Spin.toStdD_single_of_not_lt n h hn,
        sum_mul_single_add (fun y : Fin n => if y.val + 1 = n then (-1 : ℤ) else 1)]
      simp only [Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  exact congrArg (fun φ : (Fin n → ℤ) →+ ℤ => φ v) hfg

theorem sum_sign_mul_single_add (a b : Fin n) :
    ∑ z : Fin n, (if z.val + 1 = n then (-1 : ℤ) else 1) * (Pi.single a 1 + Pi.single b 1 :
      Fin n → ℤ) z = (if a.val + 1 = n then -1 else 1) + (if b.val + 1 = n then -1 else 1) :=
  sum_mul_single_add (fun z : Fin n => if z.val + 1 = n then (-1 : ℤ) else 1) a b

theorem starAt_D (hn : 7 ≤ n) {j : Fin n} (hj : j.val + 2 = n ∨ j.val + 1 = n) :
    StarAt (Spin.cartanD n) (Spin.isFiniteType_cartanD n) j := by
  intro γ hγ hγj
  obtain ⟨c, d, s, t, -, -, -, hγe⟩ :=
    (Set.ext_iff.1 (Spin.rootsD_eq (n := n) (by omega)) γ).1 hγ
  have hcard : 2 < ((Finset.range 5).filter (fun x => x ≠ c.val ∧ x ≠ d.val)).card := by
    have h1 : (Finset.range 5).filter (fun x => ¬(x ≠ c.val ∧ x ≠ d.val)) ⊆
        {c.val, d.val} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h : x = c.val
      · exact Or.inl h
      · exact Or.inr (hx.2 h)
    have h2 := Finset.card_le_card h1
    have h3 := Finset.card_filter_add_card_filter_not
      (s := Finset.range 5) (fun x => x ≠ c.val ∧ x ≠ d.val)
    have h4 : ({c.val, d.val} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_range] at h3
    omega
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.1 hcard
  simp only [Finset.mem_filter, Finset.mem_range] at hp hq hr
  have hroot : ∀ (x y : ℕ) (hx : x < 5) (hy : y < 5), x ≠ y → x ≠ c.val → x ≠ d.val →
      y ≠ c.val → y ≠ d.val → ∃ β ∈ roots (Spin.isFiniteType_cartanD n) ∅,
        Spin.toStdD n β = Pi.single (⟨x, by omega⟩ : Fin n) 1 + Pi.single ⟨y, by omega⟩ 1 ∧
        β j = 1 ∧ coroot (Spin.cartanD n) j β = 0 ∧ cartanPair (Spin.cartanD n) β γ = 0 := by
    intro x y hx hy hxy hxc hxd hyc hyd
    have hne : (⟨x, by omega⟩ : Fin n) ≠ ⟨y, by omega⟩ := fun e => hxy (congrArg Fin.val e)
    obtain ⟨β, hβ, hβe⟩ := Spin.exists_mem_rootsD_toStdD_eq n hne (Or.inl rfl) (Or.inl rfl)
    refine ⟨β, hβ, hβe, ?_, ?_, ?_⟩
    · rcases hj with hj | hj
      · have h1 := sum_sign_toStdD (by omega) β
        rw [hβe, sum_sign_mul_single_add] at h1
        have h2 : j = ⟨n - 2, by omega⟩ := Fin.ext (by simp only; omega)
        rw [h2]
        simp only at h1
        split_ifs at h1 <;> omega
      · have h1 := sum_toStdD (by omega) β
        have h3 : ∑ z : Fin n, Spin.toStdD n β z = 2 := by
          rw [hβe]
          simp [Finset.sum_add_distrib]
        have h2 : j = ⟨n - 1, by omega⟩ := Fin.ext (by simp only; omega)
        rw [h2]
        omega
    · rw [coroot_D_eq_sum (by omega), hβe, sum_single_add_mul]
      rcases hj with hj | hj
      · rw [Spin.toStdD_single_of_lt n (by omega)]
        simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> omega
      · rw [Spin.toStdD_single_of_not_lt n (by omega) (by omega)]
        simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> omega
    · rw [cartanPair_D (by omega), hβe, hγe, sum_single_add_mul]
      simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  obtain ⟨β₁, h1r, h1e, h1j, h1c, h1p⟩ :=
    hroot p q hp.1 hq.1 hpq hp.2.1 hp.2.2 hq.2.1 hq.2.2
  obtain ⟨β₂, h2r, h2e, h2j, h2c, h2p⟩ :=
    hroot p r hp.1 hr.1 hpr hp.2.1 hp.2.2 hr.2.1 hr.2.2
  refine ⟨β₁, β₂, fun e => ?_, ?_⟩
  · have h := congrFun (congrArg (Spin.toStdD n) e) ⟨r, by omega⟩
    rw [h1e, h2e] at h
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff] at h
    split_ifs at h <;> omega
  · rintro β (rfl | rfl)
    · exact ⟨h1r, h1j, h1c, h1p⟩
    · exact ⟨h2r, h2j, h2c, h2p⟩

end TypeD

end CaseE

end CFSG.Timmesfeld.ARS
