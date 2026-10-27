module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Cfg
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {L : Type} [Group L] {m : ℕ}

private def nine3_base (k l : Fin m) (w : L) : Fin m → L :=
  fun x => if x = k then w else if x = l then w⁻¹ else 1

private def nine3_single (k : Fin m) (y : L) : Fin m → L :=
  fun x => if x = k then y else 1

@[simp] private theorem nine3_base_apply (k l : Fin m) (w : L) (n : Fin m) :
    nine3_base k l w n = if n = k then w else if n = l then w⁻¹ else 1 := rfl

@[simp] private theorem nine3_single_apply (k : Fin m) (y : L) (n : Fin m) :
    nine3_single k y n = if n = k then y else 1 := rfl

@[simp] private theorem nine3_wreathAct_apply (σ : Equiv.Perm (Fin m)) (f : Fin m → L)
    (n : Fin m) : wreathAct L m σ f n = f (σ.symm n) := rfl

private def nine3_wr (k l : Fin m) (y : L) : WreathSym L m :=
  ⟨nine3_base k l y, Equiv.swap k l⟩

@[simp] private theorem nine3_wr_left (k l : Fin m) (y : L) :
    (nine3_wr k l y).left = nine3_base k l y := rfl

@[simp] private theorem nine3_wr_right (k l : Fin m) (y : L) :
    (nine3_wr k l y).right = Equiv.swap k l := rfl

private theorem nine3_wr_mul {k l : Fin m} (hkl : k ≠ l) (y z : L) :
    nine3_wr k l y * nine3_wr k l z =
      ⟨fun n => if n = k then y * z⁻¹ else if n = l then y⁻¹ * z else 1, 1⟩ := by
  apply SemidirectProduct.ext
  · funext n
    by_cases hk : n = k
    · simp [hk, hkl, Ne.symm hkl]
    · by_cases hl : n = l
      · simp [hl, hk, hkl, Ne.symm hkl]
      · simp [hk, hl, Equiv.swap_apply_of_ne_of_ne hk hl]
  · simp

private theorem nine3_inv_mul_eq_of_sq {y z : L} (h : (y * z⁻¹) * (y * z⁻¹) = 1) :
    y⁻¹ * z = z⁻¹ * y := by
  have hw : (y * z⁻¹)⁻¹ = y * z⁻¹ := (inv_eq_iff_mul_eq_one).2 h
  calc y⁻¹ * z = ((y * z⁻¹) * z)⁻¹ * z := by group
    _ = (z⁻¹ * (y * z⁻¹)⁻¹) * z := by rw [mul_inv_rev]
    _ = (z⁻¹ * (y * z⁻¹)) * z := by rw [hw]
    _ = z⁻¹ * y := by group

private theorem nine3_wr_comm_iff {k l : Fin m} (hkl : k ≠ l) (y z : L) :
    nine3_wr k l y * nine3_wr k l z = nine3_wr k l z * nine3_wr k l y ↔
      (y * z⁻¹) * (y * z⁻¹) = 1 := by
  rw [nine3_wr_mul hkl y z, nine3_wr_mul hkl z y]
  constructor
  · intro h
    have hk := congrFun (congrArg SemidirectProduct.left h) k
    simp [hkl] at hk
    have hw : y * z⁻¹ = (y * z⁻¹)⁻¹ := by
      rw [mul_inv_rev]; simpa using hk
    nth_rewrite 1 [hw]
    exact inv_mul_cancel _
  · intro h
    apply SemidirectProduct.ext
    · funext n
      by_cases hk : n = k
      · simp [hk, hkl, Ne.symm hkl]
        have hw : y * z⁻¹ = (y * z⁻¹)⁻¹ := (eq_inv_iff_mul_eq_one).2 h
        rw [hw, mul_inv_rev]
        simp
      · by_cases hl : n = l
        · simp [hl, hk, hkl, Ne.symm hkl]
          exact nine3_inv_mul_eq_of_sq h
        · simp [hk, hl, Equiv.swap_apply_of_ne_of_ne hk hl]
    · simp

private theorem nine3_conj_inr (g : WreathSym L m) (ρ : Equiv.Perm (Fin m)) :
    g * SemidirectProduct.inr ρ * g⁻¹ =
      ⟨fun n => g.left n * (g.left ((g.right * ρ * g.right⁻¹).symm n))⁻¹,
        g.right * ρ * g.right⁻¹⟩ := by
  obtain ⟨f, σ⟩ := g
  apply SemidirectProduct.ext
  · funext n
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply, one_mul, mul_one,
      nine3_wreathAct_apply, Pi.mul_apply, Pi.inv_apply, map_mul, MulAut.mul_apply]
    congr 1
  · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right]

private theorem nine3_wr_of_conj_swap {k l : Fin m} (hkl : k ≠ l) {x : WreathSym L m}
    (hx : IsConj (SemidirectProduct.inr (Equiv.swap k l)) x)
    (hr : x.right = Equiv.swap k l) :
    ∃ y : L, x = nine3_wr k l y := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  refine ⟨g.left k * (g.left l)⁻¹, ?_⟩
  have hright : g.right * Equiv.swap k l * g.right⁻¹ = Equiv.swap k l := by
    simpa using hr
  rw [nine3_conj_inr g (Equiv.swap k l), hright]
  apply SemidirectProduct.ext
  · funext n
    by_cases hk : n = k
    · simp [hk, hkl, Ne.symm hkl]
    · by_cases hl : n = l
      · simp [hl, hk, hkl, Ne.symm hkl]
      · simp [hk, hl, Equiv.swap_apply_of_ne_of_ne hk hl]
  · simp

private theorem nine3_isConj_wr_swap {k l : Fin m} (hkl : k ≠ l) (y : L) :
    IsConj (SemidirectProduct.inr (Equiv.swap k l)) (nine3_wr k l y) := by
  refine isConj_iff.2 ⟨SemidirectProduct.inl (nine3_single k y), ?_⟩
  apply SemidirectProduct.ext
  · funext n
    simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, MulAut.one_apply, mul_one,
      SemidirectProduct.left_inr, SemidirectProduct.inv_right, nine3_wreathAct_apply,
      nine3_single_apply, Pi.inv_apply]
    by_cases hk : n = k
    · simp [hk, hkl, Ne.symm hkl]
    · by_cases hl : n = l
      · simp [hl, hk, hkl, Ne.symm hkl]
      · simp [hk, hl, Equiv.swap_apply_of_ne_of_ne hk hl]
  · simp

private theorem nine3_isConj_wr_of_swap {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l)
    (y : L) :
    IsConj (SemidirectProduct.inr (Equiv.swap i j)) (nine3_wr k l y) :=
  (MonoidHom.map_isConj SemidirectProduct.inr (Equiv.Perm.isConj_swap hij hkl)).trans
    (nine3_isConj_wr_swap hkl y)

private theorem nine3_isSwap_right {i j : Fin m} (hij : i ≠ j) {c x : WreathSym L m}
    (hc : IsConj c (SemidirectProduct.inr (Equiv.swap i j))) (hx : IsConj c x) :
    x.right.IsSwap := by
  have h1 : IsConj (SemidirectProduct.inr (Equiv.swap i j)) x := hc.symm.trans hx
  have h2 : IsConj (Equiv.swap i j) x.right :=
    MonoidHom.map_isConj SemidirectProduct.rightHom h1
  obtain ⟨g, hg⟩ := isConj_iff.1 h2
  refine ⟨g i, g j, fun h => hij (g.injective h), ?_⟩
  rw [← hg, Equiv.mul_swap_eq_swap_mul, mul_assoc, mul_inv_cancel, mul_one]

private theorem nine3_isConj_inr_swap_of_conj_c {i j k l : Fin m} {c x : WreathSym L m}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hc : IsConj c (SemidirectProduct.inr (Equiv.swap i j))) (hx : IsConj c x) :
    IsConj (SemidirectProduct.inr (Equiv.swap k l)) x :=
  (MonoidHom.map_isConj SemidirectProduct.inr (Equiv.Perm.isConj_swap hij hkl)).symm.trans
    (hc.symm.trans hx)

private theorem nine3_swap_commute_apply_eq_self {x y k l : Fin m}
    (hxy : x ≠ y) (hkl : k ≠ l)
    (hcomm : Equiv.swap k l * Equiv.swap x y = Equiv.swap x y * Equiv.swap k l)
    (hne : Equiv.swap k l ≠ Equiv.swap x y) :
    Equiv.swap k l x = x := by
  by_contra hx
  have hxor : x = k ∨ x = l :=
    ((Equiv.swap_apply_ne_self_iff (a := k) (b := l) (x := x)).mp hx).2
  have h2 : (Equiv.swap k l * Equiv.swap x y) ^ 2 = 1 := by
    rw [pow_two]
    calc Equiv.swap k l * Equiv.swap x y * (Equiv.swap k l * Equiv.swap x y)
        = Equiv.swap k l * (Equiv.swap x y * Equiv.swap k l) * Equiv.swap x y := by group
      _ = Equiv.swap k l * (Equiv.swap k l * Equiv.swap x y) * Equiv.swap x y := by rw [hcomm]
      _ = (Equiv.swap k l * Equiv.swap k l) * (Equiv.swap x y * Equiv.swap x y) := by group
      _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  rcases hxor with hk | hl
  · have hky : k ≠ y := fun h => hxy (hk.trans h)
    have hly : l ≠ y := fun h => hne (by rw [hk, h])
    have h3 : Equiv.Perm.IsThreeCycle (Equiv.swap k l * Equiv.swap k y) :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same hkl hky hly
    have h4 : (Equiv.swap k l * Equiv.swap k y) ^ 2 = 1 := by simpa [hk] using h2
    have hdvd : orderOf (Equiv.swap k l * Equiv.swap k y) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h4
    rw [Equiv.Perm.IsThreeCycle.orderOf h3] at hdvd
    norm_num at hdvd
  · have hly : l ≠ y := fun h => hxy (hl.trans h)
    have hky : k ≠ y := fun h => hne (by rw [hl, h, Equiv.swap_comm])
    have h3 : Equiv.Perm.IsThreeCycle (Equiv.swap k l * Equiv.swap l y) := by
      rw [Equiv.swap_comm]
      exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hkl.symm hly hky
    have h4 : (Equiv.swap k l * Equiv.swap l y) ^ 2 = 1 := by simpa [hl] using h2
    have hdvd : orderOf (Equiv.swap k l * Equiv.swap l y) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h4
    rw [Equiv.Perm.IsThreeCycle.orderOf h3] at hdvd
    norm_num at hdvd

private theorem nine3_eq_of_comm_of_pow_three_swap {σ τ : Equiv.Perm (Fin m)}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap) (hcomm : σ * τ = τ * σ) (h3 : (σ * τ) ^ 3 = 1) :
    σ = τ := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  obtain ⟨u, w, huw, rfl⟩ := hτ
  have h2 : (Equiv.swap x y * Equiv.swap u w) ^ 2 = 1 := by
    rw [pow_two]
    calc Equiv.swap x y * Equiv.swap u w * (Equiv.swap x y * Equiv.swap u w)
        = Equiv.swap x y * (Equiv.swap u w * Equiv.swap x y) * Equiv.swap u w := by group
      _ = Equiv.swap x y * (Equiv.swap x y * Equiv.swap u w) * Equiv.swap u w := by rw [hcomm]
      _ = (Equiv.swap x y * Equiv.swap x y) * (Equiv.swap u w * Equiv.swap u w) := by group
      _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  have h1 : Equiv.swap x y * Equiv.swap u w = 1 := by
    calc Equiv.swap x y * Equiv.swap u w = Equiv.swap x y * Equiv.swap u w * 1 := by rw [mul_one]
      _ = Equiv.swap x y * Equiv.swap u w * (Equiv.swap x y * Equiv.swap u w) ^ 2 := by
            rw [h2, mul_one]
      _ = (Equiv.swap x y * Equiv.swap u w) ^ 3 := by group
      _ = 1 := h3
  calc Equiv.swap x y = Equiv.swap x y * (Equiv.swap u w * Equiv.swap u w) := by
        rw [Equiv.swap_mul_self, mul_one]
    _ = (Equiv.swap x y * Equiv.swap u w) * Equiv.swap u w := by group
    _ = Equiv.swap u w := by rw [h1, one_mul]

private theorem nine3_sl2_exists_ne_one (F : Type) [Field F] :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) F, x ≠ 1 := by
  refine ⟨⟨!![1, 1; 0, 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    simp
  · intro h
    have h01 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) F =>
      (m : Matrix (Fin 2) (Fin 2) F) 0 1) h
    have h10 : (1 : F) = 0 := by simpa using h01
    exact one_ne_zero h10

private theorem nine3_swap_fixed_four {k l n : Fin m} (hkl : k ≠ l)
    (h : Equiv.swap k l n = n) : n ≠ k ∧ n ≠ l := by
  constructor
  · intro hnk
    rw [hnk, Equiv.swap_apply_left] at h
    exact hkl h.symm
  · intro hnl
    rw [hnl, Equiv.swap_apply_right] at h
    exact hkl h

private theorem nine3_swap_mul_comm_of_disjoint {k l k' l' : Fin m}
    (hk1 : k ≠ k') (hk2 : k ≠ l') (hl1 : l ≠ k') (hl2 : l ≠ l') :
    Equiv.swap k l * Equiv.swap k' l' = Equiv.swap k' l' * Equiv.swap k l := by
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases hx1 : x = k <;> by_cases hx2 : x = l <;>
    by_cases hx3 : x = k' <;> by_cases hx4 : x = l' <;>
    simp_all [Equiv.swap_apply_def, hk1.symm, hk2.symm, hl1.symm, hl2.symm]

private theorem nine3_wr_comm_of_disjoint {k l k' l' : Fin m} (hkl : k ≠ l) (hk'l' : k' ≠ l')
    (hk1 : k ≠ k') (hk2 : k ≠ l') (hl1 : l ≠ k') (hl2 : l ≠ l') (y y' : L) :
    nine3_wr k l y * nine3_wr k' l' y' = nine3_wr k' l' y' * nine3_wr k l y := by
  apply SemidirectProduct.ext
  · funext n
    simp only [nine3_wr_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      nine3_wreathAct_apply, nine3_base_apply, Pi.mul_apply]
    by_cases h1 : n = k
    · simp [h1, hk1, hk2, hl1, hl2, hkl, hk'l', hk1.symm, hk2.symm, hl1.symm, hl2.symm,
        Equiv.swap_apply_of_ne_of_ne hk1 hk2, Equiv.swap_apply_of_ne_of_ne hk1.symm hl1.symm,
        Equiv.swap_apply_of_ne_of_ne hl1 hl2, Equiv.swap_apply_of_ne_of_ne hk2.symm hl2.symm,
        hk'l'.symm]
    · by_cases h2 : n = l
      · simp [h2, hk1, hk2, hl1, hl2, hkl, hk'l', hk1.symm, hk2.symm, hl1.symm, hl2.symm,
          Equiv.swap_apply_of_ne_of_ne hk1 hk2, Equiv.swap_apply_of_ne_of_ne hk1.symm hl1.symm,
          Equiv.swap_apply_of_ne_of_ne hl1 hl2, Equiv.swap_apply_of_ne_of_ne hk2.symm hl2.symm,
          hk'l'.symm]
      · by_cases h3 : n = k'
        · simp [h3, hk1, hk2, hl1, hl2, hkl, hk'l', hk1.symm, hk2.symm, hl1.symm, hl2.symm,
            Equiv.swap_apply_of_ne_of_ne hk1 hk2, Equiv.swap_apply_of_ne_of_ne hk1.symm hl1.symm,
            Equiv.swap_apply_of_ne_of_ne hl1 hl2, Equiv.swap_apply_of_ne_of_ne hk2.symm hl2.symm,
            hk'l'.symm]
        · by_cases h4 : n = l'
          · simp [h4, hk1, hk2, hl1, hl2, hkl, hk'l', hk1.symm, hk2.symm, hl1.symm, hl2.symm,
              Equiv.swap_apply_of_ne_of_ne hk1 hk2, Equiv.swap_apply_of_ne_of_ne hk1.symm hl1.symm,
              Equiv.swap_apply_of_ne_of_ne hl1 hl2, Equiv.swap_apply_of_ne_of_ne hk2.symm hl2.symm,
              hk'l'.symm]
          · simp [h1, h2, h3, h4, Equiv.swap_apply_of_ne_of_ne h1 h2,
              Equiv.swap_apply_of_ne_of_ne h3 h4]
  · exact nine3_swap_mul_comm_of_disjoint hk1 hk2 hl1 hl2

theorem nine3_prop710_wreath {n m : ℕ} (hn : 1 < n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    {c a e a' v : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m} {i j : Fin m} (hij : i ≠ j)
    (hc : IsConj c (SemidirectProduct.inr (Equiv.swap i j))) (h : Nine3Config c a e a' v) :
    ∃ d, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  obtain ⟨k_a, l_a, hkla, hra⟩ := nine3_isSwap_right hij hc h.conj_a
  obtain ⟨k_e, l_e, hkle, hre⟩ := nine3_isSwap_right hij hc h.conj_e
  obtain ⟨k_v, l_v, hklv, hrv⟩ := nine3_isSwap_right hij hc h.conj_v
  obtain ⟨y_a, ha_eq⟩ := nine3_wr_of_conj_swap hkla
    (nine3_isConj_inr_swap_of_conj_c hij hkla hc h.conj_a) hra
  obtain ⟨y_e, he_eq⟩ := nine3_wr_of_conj_swap hkle
    (nine3_isConj_inr_swap_of_conj_c hij hkle hc h.conj_e) hre
  obtain ⟨y_v, hv_eq⟩ := nine3_wr_of_conj_swap hklv
    (nine3_isConj_inr_swap_of_conj_c hij hklv hc h.conj_v) hrv
  have h3_ae : (a.right * e.right) ^ 3 = 1 := by
    have hp := MonoidHom.map_pow SemidirectProduct.rightHom (a * e) 3
    rw [h.pow_ae, map_one] at hp
    simpa [map_mul] using hp.symm
  by_cases h_ae : a.right = e.right
  · by_cases h_av : a.right = v.right
    ·
      have hcomm_ae : a.right * e.right = e.right * a.right := by
        have := congrArg SemidirectProduct.right h.comm_ve
        simpa only [SemidirectProduct.mul_right, ← h_av] using this
      have h_ev : e.right = a.right :=
        nine3_eq_of_comm_of_pow_three_swap ⟨k_e, l_e, hkle, hre⟩
          ⟨k_a, l_a, hkla, hra⟩ hcomm_ae.symm
          (by rw [show e.right * a.right = a.right * e.right from hcomm_ae.symm]; exact h3_ae)
      have he_right : e.right = Equiv.swap k_a l_a := h_ev.trans hra
      have hv_right : v.right = Equiv.swap k_a l_a := h_av.symm.trans hra
      obtain ⟨y_e', he_eq'⟩ := nine3_wr_of_conj_swap hkla
        (nine3_isConj_inr_swap_of_conj_c hij hkla hc h.conj_e) he_right
      obtain ⟨y_v', hv_eq'⟩ := nine3_wr_of_conj_swap hkla
        (nine3_isConj_inr_swap_of_conj_c hij hkla hc h.conj_v) hv_right
      let w' : Matrix.SpecialLinearGroup (Fin 2) F := y_e' * y_a⁻¹
      let t_v : Matrix.SpecialLinearGroup (Fin 2) F := y_a * y_v'⁻¹
      let t_1 : Matrix.SpecialLinearGroup (Fin 2) F := t_v * w'
      let z_1 : Matrix.SpecialLinearGroup (Fin 2) F := t_1 * y_a
      have hcomm_av' : a * v = v * a := h.comm_va.symm
      rw [ha_eq, hv_eq'] at hcomm_av'
      have htv2 : t_v * t_v = 1 := by
        have := (nine3_wr_comm_iff hkla y_a y_v').1 hcomm_av'
        simpa only [t_v] using this
      have hcomm_ev' : e * v = v * e := h.comm_ve.symm
      rw [he_eq', hv_eq'] at hcomm_ev'
      have hsq_ev : (y_e' * y_v'⁻¹) * (y_e' * y_v'⁻¹) = 1 :=
        (nine3_wr_comm_iff hkla y_e' y_v').1 hcomm_ev'
      have hwe : y_v'⁻¹ * y_e' * y_v'⁻¹ = y_e'⁻¹ := by
        calc y_v'⁻¹ * y_e' * y_v'⁻¹
            = y_e'⁻¹ * ((y_e' * y_v'⁻¹) * (y_e' * y_v'⁻¹)) := by group
          _ = y_e'⁻¹ * 1 := by rw [hsq_ev]
          _ = y_e'⁻¹ := by group
      have ht1w : t_v * w' * t_v = w'⁻¹ := by
        show (y_a * y_v'⁻¹) * (y_e' * y_a⁻¹) * (y_a * y_v'⁻¹) = (y_e' * y_a⁻¹)⁻¹
        calc (y_a * y_v'⁻¹) * (y_e' * y_a⁻¹) * (y_a * y_v'⁻¹)
            = y_a * (y_v'⁻¹ * y_e' * y_v'⁻¹) := by
                simp only [mul_assoc]
                group
          _ = y_a * y_e'⁻¹ := by rw [hwe]
          _ = (y_e' * y_a⁻¹)⁻¹ := by group
      have hwt : w' * t_v * w' = t_v := by
        have h1 : w' * t_v * w' * t_v = 1 := by
          rw [show w' * t_v * w' * t_v = w' * (t_v * w' * t_v) by group,
            ht1w, mul_inv_cancel]
        calc w' * t_v * w' = w' * t_v * w' * (t_v * t_v) := by rw [htv2, mul_one]
          _ = (w' * t_v * w' * t_v) * t_v := by group
          _ = 1 * t_v := by rw [h1]
          _ = t_v := by group
      have ht12 : t_1 * t_1 = 1 := by
        show (t_v * w') * (t_v * w') = 1
        calc (t_v * w') * (t_v * w') = (t_v * w' * t_v) * w' := by group
          _ = w'⁻¹ * w' := by rw [ht1w]
          _ = 1 := by group
      have ht1w' : t_1 * w' * t_1 = w'⁻¹ := by
        show (t_v * w') * w' * (t_v * w') = w'⁻¹
        calc (t_v * w') * w' * (t_v * w')
            = t_v * w' * (w' * t_v * w') := by group
          _ = t_v * w' * t_v := by rw [hwt]
          _ = w'⁻¹ := ht1w
      have hwt' : t_1 * w'⁻¹ = w' * t_1 := by
        calc t_1 * w'⁻¹ = t_1 * (t_1 * w' * t_1) := by rw [ht1w']
          _ = (t_1 * t_1) * (w' * t_1) := by group
          _ = 1 * (w' * t_1) := by rw [ht12]
          _ = w' * t_1 := by group
      have hyv'_eq : t_v * y_a = y_v' := by
        show (y_a * y_v'⁻¹) * y_a = y_v'
        calc (y_a * y_v'⁻¹) * y_a
            = (y_a * y_v'⁻¹) * y_a * (y_v'⁻¹ * y_v') := by group
          _ = ((y_a * y_v'⁻¹) * (y_a * y_v'⁻¹)) * y_v' := by group
          _ = 1 * y_v' := by rw [htv2]
          _ = y_v' := by group
      have hz1_ne : z_1 ≠ y_v' := by
        intro hz
        have ht1_eq : t_1 = t_v := by
          have h := hz
          rw [show z_1 = t_1 * y_a from rfl, ← hyv'_eq] at h
          exact mul_right_cancel h
        have hw'_eq : w' = 1 := by
          have h := ht1_eq
          rw [show t_1 = t_v * w' from rfl] at h
          exact mul_left_cancel (a := t_v) (by simpa using h)
        have hye_eq : y_e' = y_a := by
          have h := hw'_eq
          rw [show w' = y_e' * y_a⁻¹ from rfl] at h
          calc y_e' = y_e' * y_a⁻¹ * y_a := by group
            _ = 1 * y_a := by rw [h]
            _ = y_a := by group
        have he_a : e = a := by rw [he_eq', ha_eq, hye_eq]
        exact h.not_comm_ae (by rw [he_a])
      refine ⟨nine3_wr k_a l_a z_1,
        hc.trans (nine3_isConj_wr_of_swap hij hkla z_1), ?_, ?_, ?_⟩
      · rw [hv_eq']
        intro hd
        apply hz1_ne
        have := congrFun (congrArg SemidirectProduct.left hd) k_a
        simpa [hkla] using this
      · rw [ha_eq]
        exact (nine3_wr_comm_iff hkla z_1 y_a).2 (by
          show (z_1 * y_a⁻¹) * (z_1 * y_a⁻¹) = 1
          rw [show z_1 * y_a⁻¹ = t_1 by rw [show z_1 = t_1 * y_a from rfl]; group]
          exact ht12)
      · rw [he_eq']
        exact (nine3_wr_comm_iff hkla z_1 y_e').2 (by
          show (z_1 * y_e'⁻¹) * (z_1 * y_e'⁻¹) = 1
          have h1 : z_1 * y_e'⁻¹ = t_1 * w'⁻¹ := by
            show (t_1 * y_a) * y_e'⁻¹ = t_1 * (y_e' * y_a⁻¹)⁻¹
            group
          rw [h1]
          calc (t_1 * w'⁻¹) * (t_1 * w'⁻¹) = (w' * t_1) * (w' * t_1) := by rw [hwt']
            _ = w' * (t_1 * w' * t_1) := by group
            _ = w' * w'⁻¹ := by rw [ht1w']
            _ = 1 := by group)
    ·
      have hcomm_av : Equiv.swap k_a l_a * Equiv.swap k_v l_v =
          Equiv.swap k_v l_v * Equiv.swap k_a l_a := by
        have := congrArg SemidirectProduct.right h.comm_va
        simp only [SemidirectProduct.mul_right] at this
        rw [hra, hrv] at this
        exact this.symm
      have hcomm_ev : Equiv.swap k_e l_e * Equiv.swap k_v l_v =
          Equiv.swap k_v l_v * Equiv.swap k_e l_e := by
        have := congrArg SemidirectProduct.right h.comm_ve
        simp only [SemidirectProduct.mul_right] at this
        rw [hre, hrv] at this
        exact this.symm
      have hav_ne : Equiv.swap k_a l_a ≠ Equiv.swap k_v l_v := by
        intro h; exact h_av (hra.trans (h.trans hrv.symm))
      have hev_ne : Equiv.swap k_e l_e ≠ Equiv.swap k_v l_v := by
        intro h; exact h_av (h_ae.trans (hre.trans (h.trans hrv.symm)))
      have hfix_ak : Equiv.swap k_a l_a k_v = k_v :=
        nine3_swap_commute_apply_eq_self hklv hkla hcomm_av hav_ne
      have hfix_al : Equiv.swap k_a l_a l_v = l_v :=
        nine3_swap_commute_apply_eq_self hklv.symm hkla
          (by simpa [Equiv.swap_comm] using hcomm_av)
          (by simpa [Equiv.swap_comm] using hav_ne)
      have hfix_ek : Equiv.swap k_e l_e k_v = k_v :=
        nine3_swap_commute_apply_eq_self hklv hkle hcomm_ev hev_ne
      have hfix_el : Equiv.swap k_e l_e l_v = l_v :=
        nine3_swap_commute_apply_eq_self hklv.symm hkle
          (by simpa [Equiv.swap_comm] using hcomm_ev)
          (by simpa [Equiv.swap_comm] using hev_ne)
      obtain ⟨hk1, hk2⟩ := nine3_swap_fixed_four hkla hfix_ak
      obtain ⟨hl1, hl2⟩ := nine3_swap_fixed_four hkla hfix_al
      obtain ⟨hk1', hk2'⟩ := nine3_swap_fixed_four hkle hfix_ek
      obtain ⟨hl1', hl2'⟩ := nine3_swap_fixed_four hkle hfix_el
      obtain ⟨x, hx⟩ := nine3_sl2_exists_ne_one F
      refine ⟨nine3_wr k_v l_v (y_v * x),
        hc.trans (nine3_isConj_wr_of_swap hij hklv (y_v * x)), ?_, ?_, ?_⟩
      · rw [hv_eq]
        intro hd
        have hthis := congrFun (congrArg SemidirectProduct.left hd) k_v
        simp [nine3_wr_left, nine3_base_apply, hklv] at hthis
        exact hx hthis
      · rw [ha_eq]
        exact nine3_wr_comm_of_disjoint hklv hkla hk1 hk2 hl1 hl2 (y_v * x) y_a
      · rw [he_eq]
        exact nine3_wr_comm_of_disjoint hklv hkle hk1' hk2' hl1' hl2' (y_v * x) y_e
  ·
    have hcomm_av : Equiv.swap k_a l_a * Equiv.swap k_v l_v =
        Equiv.swap k_v l_v * Equiv.swap k_a l_a := by
      have := congrArg SemidirectProduct.right h.comm_va
      simp only [SemidirectProduct.mul_right] at this
      rw [hra, hrv] at this
      exact this.symm
    have hcomm_ev : Equiv.swap k_e l_e * Equiv.swap k_v l_v =
        Equiv.swap k_v l_v * Equiv.swap k_e l_e := by
      have := congrArg SemidirectProduct.right h.comm_ve
      simp only [SemidirectProduct.mul_right] at this
      rw [hre, hrv] at this
      exact this.symm
    have hav_ne : Equiv.swap k_a l_a ≠ Equiv.swap k_v l_v := by
      intro hswap
      apply h_ae
      have hv_eq_a : v.right = a.right := by rw [hrv, ← hswap, ← hra]
      have hcomm : a.right * e.right = e.right * a.right := by
        have := congrArg SemidirectProduct.right h.comm_ve
        simp only [SemidirectProduct.mul_right] at this
        simpa [hv_eq_a] using this
      exact nine3_eq_of_comm_of_pow_three_swap ⟨k_a, l_a, hkla, hra⟩
        ⟨k_e, l_e, hkle, hre⟩ hcomm h3_ae
    have hev_ne : Equiv.swap k_e l_e ≠ Equiv.swap k_v l_v := by
      intro hswap
      apply h_ae
      have hv_eq_e : v.right = e.right := by rw [hrv, ← hswap, ← hre]
      have hcomm : e.right * a.right = a.right * e.right := by
        have := congrArg SemidirectProduct.right h.comm_va
        simp only [SemidirectProduct.mul_right] at this
        simpa [hv_eq_e] using this
      have h3 : (e.right * a.right) ^ 3 = 1 := by
        rw [show e.right * a.right = a.right * e.right from hcomm]
        exact h3_ae
      exact (nine3_eq_of_comm_of_pow_three_swap ⟨k_e, l_e, hkle, hre⟩
        ⟨k_a, l_a, hkla, hra⟩ hcomm h3).symm
    have hfix_ak : Equiv.swap k_a l_a k_v = k_v :=
      nine3_swap_commute_apply_eq_self hklv hkla hcomm_av hav_ne
    have hfix_al : Equiv.swap k_a l_a l_v = l_v :=
      nine3_swap_commute_apply_eq_self hklv.symm hkla
        (by simpa [Equiv.swap_comm] using hcomm_av)
        (by simpa [Equiv.swap_comm] using hav_ne)
    have hfix_ek : Equiv.swap k_e l_e k_v = k_v :=
      nine3_swap_commute_apply_eq_self hklv hkle hcomm_ev hev_ne
    have hfix_el : Equiv.swap k_e l_e l_v = l_v :=
      nine3_swap_commute_apply_eq_self hklv.symm hkle
        (by simpa [Equiv.swap_comm] using hcomm_ev)
        (by simpa [Equiv.swap_comm] using hev_ne)
    obtain ⟨hk1, hk2⟩ := nine3_swap_fixed_four hkla hfix_ak
    obtain ⟨hl1, hl2⟩ := nine3_swap_fixed_four hkla hfix_al
    obtain ⟨hk1', hk2'⟩ := nine3_swap_fixed_four hkle hfix_ek
    obtain ⟨hl1', hl2'⟩ := nine3_swap_fixed_four hkle hfix_el
    obtain ⟨x, hx⟩ := nine3_sl2_exists_ne_one F
    refine ⟨nine3_wr k_v l_v (y_v * x),
      hc.trans (nine3_isConj_wr_of_swap hij hklv (y_v * x)), ?_, ?_, ?_⟩
    · rw [hv_eq]
      intro hd
      have hthis := congrFun (congrArg SemidirectProduct.left hd) k_v
      simp [nine3_wr_left, nine3_base_apply, hklv] at hthis
      exact hx hthis
    · rw [ha_eq]
      exact nine3_wr_comm_of_disjoint hklv hkla hk1 hk2 hl1 hl2 (y_v * x) y_a
    · rw [he_eq]
      exact nine3_wr_comm_of_disjoint hklv hkle hk1' hk2' hl1' hl2' (y_v * x) y_e

end CFSG.LocalAnalysis.WeakClosure81
