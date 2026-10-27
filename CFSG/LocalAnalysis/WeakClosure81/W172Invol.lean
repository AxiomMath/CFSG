module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

structure W172InvSys (L : Subgroup (LGL 2 W)) (D : Set (LGL 2 W))
    (Vd : LGL 2 W → Submodule (ZMod 2) W) : Prop where
  mem : ∀ e ∈ D, e ∈ L
  sq : ∀ e ∈ D, e * e = 1
  ne_one : ∀ e ∈ D, e ≠ 1
  conj_mem : ∀ e ∈ D, ∀ h ∈ L, h * e * h⁻¹ ∈ D
  comm_le : ∀ e ∈ D, ∀ w : W, e w - w ∈ Vd e
  fix : ∀ e ∈ D, ∀ v ∈ Vd e, e v = v
  ne_bot : ∀ e ∈ D, Vd e ≠ ⊥
  disjoint : ∀ e ∈ D, ∀ f ∈ D, e ≠ f → Vd e ⊓ Vd f = ⊥
  equivariant : ∀ e ∈ D, ∀ h ∈ L,
    Vd (h * e * h⁻¹) = (Vd e).map (h : W →ₗ[ZMod 2] W)
  cent_iff_stab : ∀ e ∈ D, ∀ h ∈ L,
    h * e = e * h ↔ (Vd e).map (h : W →ₗ[ZMod 2] W) = Vd e
  fix_le_cent : ∀ e ∈ D, ∀ w ∈ Vd e, w ≠ 0 → ∀ h ∈ L, h w = w → h * e = e * h

variable {L : Subgroup (LGL 2 W)} {D : Set (LGL 2 W)} {Vd : LGL 2 W → Submodule (ZMod 2) W}

private lemma w172_inv_eq_self (h : W172InvSys L D Vd) {e : LGL 2 W} (he : e ∈ D) :
    e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (h.sq e he)

private lemma w172_cent_of_comm (h : W172InvSys L D Vd) {a b : LGL 2 W} (ha : a ∈ D)
    (hb : b ∈ D) (hne : a ≠ b) (hcomm : a * b = b * a) : ∀ v ∈ Vd a, b v = v := by
  intro v hv
  have hbL : b ∈ L := h.mem b hb
  have hstab : (Vd a).map (b : W →ₗ[ZMod 2] W) = Vd a :=
    (h.cent_iff_stab a ha b hbL).mp hcomm.symm
  have hbv : b v ∈ Vd a := by
    rw [← hstab]
    exact Submodule.mem_map_of_mem hv
  have hsub : b v - v ∈ Vd b := h.comm_le b hb v
  have hmem : b v - v ∈ Vd a ⊓ Vd b :=
    Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hbv hv, hsub⟩
  rw [h.disjoint a ha b hb hne, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

private lemma w172_conj_inv (h : W172InvSys L D Vd) {e f : LGL 2 W} (he : e ∈ D)
    (hf : f ∈ D) : e * (e * f) * e = (e * f)⁻¹ := by
  have he' : e⁻¹ = e := w172_inv_eq_self h he
  have hf' : f⁻¹ = f := w172_inv_eq_self h hf
  rw [mul_inv_rev, he', hf']
  calc e * (e * f) * e = (e * e) * f * e := by rw [← mul_assoc e e f]
    _ = f * e := by rw [h.sq e he, one_mul]

private lemma w172_conj_inv' (h : W172InvSys L D Vd) {e f : LGL 2 W} (he : e ∈ D)
    (hf : f ∈ D) : e * (e * f)⁻¹ * e = e * f := by
  have he' : e⁻¹ = e := w172_inv_eq_self h he
  have hf' : f⁻¹ = f := w172_inv_eq_self h hf
  rw [mul_inv_rev, he', hf']
  calc e * (f * e) * e = e * (f * (e * e)) := by simp only [mul_assoc]
    _ = e * f := by rw [h.sq e he, mul_one]

private lemma w172_dihedral_mem (h : W172InvSys L D Vd) {e f : LGL 2 W} (he : e ∈ D)
    (hf : f ∈ D) : ∀ j : ℕ, (e * f) ^ j * e ∈ D := by
  have htL : e * f ∈ L := L.mul_mem (h.mem e he) (h.mem f hf)
  have het : e * (e * f)⁻¹ = (e * f) * e := by
    apply mul_right_cancel (b := e)
    rw [w172_conj_inv' h he hf, mul_assoc, h.sq e he, mul_one]
  intro j
  induction j using Nat.twoStepInduction with
  | zero => simpa using he
  | one => simpa [w172_inv_eq_self h he] using h.conj_mem f hf e (h.mem e he)
  | more n ih _ =>
      have hstep : (e * f) ^ (n + 2) * e
          = (e * f) * ((e * f) ^ n * e) * (e * f)⁻¹ := by
        calc (e * f) ^ (n + 2) * e = (e * f) ^ (n + 1) * ((e * f) * e) := by
              rw [pow_succ]; group
          _ = (e * f) ^ (n + 1) * (e * (e * f)⁻¹) := by rw [het]
          _ = (e * f) * ((e * f) ^ n * e) * (e * f)⁻¹ := by
              rw [pow_succ']; group
      rw [hstep]
      exact h.conj_mem ((e * f) ^ n * e) ih (e * f) htL

theorem w172_comm_or_odd (h : W172InvSys L D Vd) {e f : LGL 2 W} (he : e ∈ D) (hf : f ∈ D) :
    e * f = f * e ∨ Odd (orderOf (e * f)) := by
  by_cases hcomm : e * f = f * e
  · exact Or.inl hcomm
  · right
    by_contra hodd
    have heven : Even (orderOf (e * f)) := Nat.not_odd_iff_even.mp hodd
    obtain ⟨k, hk⟩ := heven
    have hkpos : 0 < k := by
      have hpos : 0 < orderOf (e * f) := orderOf_pos _
      omega
    have hklt : k < orderOf (e * f) := by omega
    have hz_ne : (e * f) ^ k ≠ 1 :=
      pow_ne_one_of_lt_orderOf (Nat.ne_of_gt hkpos) hklt
    have hzz : (e * f) ^ k * (e * f) ^ k = 1 := by
      rw [← pow_add, ← hk, pow_orderOf_eq_one]
    have hz_inv : ((e * f) ^ k)⁻¹ = (e * f) ^ k := inv_eq_of_mul_eq_one_right hzz
    have he_inv : e⁻¹ = e := w172_inv_eq_self h he
    have hf_inv : f⁻¹ = f := w172_inv_eq_self h hf
    have het : e * (e * f) * e = (e * f)⁻¹ := w172_conj_inv h he hf
    have het' : e * (e * f)⁻¹ * e = e * f := w172_conj_inv' h he hf
    have hetinv : e * (e * f)⁻¹ = (e * f) * e := by
      apply mul_right_cancel (b := e)
      rw [het', mul_assoc, h.sq e he, mul_one]
    have hez : e * (e * f) ^ k * e = ((e * f) ^ k)⁻¹ := by
      have h1 : e * (e * f) ^ k * e⁻¹ = ((e * f) ^ k)⁻¹ := by
        rw [← conj_pow, he_inv, het, inv_pow]
      rwa [he_inv] at h1
    have hez_comm : e * (e * f) ^ k = (e * f) ^ k * e := by
      apply mul_right_cancel (b := e)
      rw [hez, hz_inv, mul_assoc, h.sq e he, mul_one]
    have hfconj : f * (e * f) * f = (e * f)⁻¹ := by
      rw [mul_inv_rev, hf_inv, he_inv]
      calc f * (e * f) * f = f * (e * (f * f)) := by simp only [mul_assoc]
        _ = f * e := by rw [h.sq f hf, mul_one]
    have hfz : f * (e * f) ^ k * f = (e * f) ^ k := by
      have h1 : f * (e * f) ^ k * f⁻¹ = ((e * f) ^ k)⁻¹ := by
        rw [← conj_pow, hf_inv, hfconj, inv_pow]
      have h2 : f * (e * f) ^ k * f = ((e * f) ^ k)⁻¹ := by
        rwa [hf_inv] at h1
      rw [h2, hz_inv]
    have hfz_comm : f * (e * f) ^ k = (e * f) ^ k * f := by
      apply mul_right_cancel (b := f)
      rw [hfz, mul_assoc, h.sq f hf, mul_one]
    have hq : e * (e * f) ^ k ∈ D := by
      rw [hez_comm]
      exact w172_dihedral_mem h he hf k
    have hq_ne : e * (e * f) ^ k ≠ e := fun hqe =>
      hz_ne (mul_left_cancel (a := e) (by simpa using hqe))
    have hfe : f * e = (e * f)⁻¹ := by
      rw [mul_inv_rev, hf_inv, he_inv]
    have hfe_pow : (f * e) ^ k = (e * f) ^ k := by
      rw [hfe, inv_pow, hz_inv]
    have hr : f * (e * f) ^ k ∈ D := by
      have hmem : (f * e) ^ k * f ∈ D := w172_dihedral_mem h hf he k
      rw [hfe_pow, ← hfz_comm] at hmem
      exact hmem
    have hr_ne : f * (e * f) ^ k ≠ f := fun hrf =>
      hz_ne (mul_left_cancel (a := f) (by simpa using hrf))
    have hqe_comm : e * (e * (e * f) ^ k) = (e * (e * f) ^ k) * e := by
      rw [← mul_assoc, h.sq e he, one_mul, hez_comm, mul_assoc, h.sq e he, mul_one]
    have hrf_comm : f * (f * (e * f) ^ k) = (f * (e * f) ^ k) * f := by
      rw [← mul_assoc, h.sq f hf, one_mul, hfz_comm, mul_assoc, h.sq f hf, mul_one]
    have he_fixes_q : ∀ v ∈ Vd (e * (e * f) ^ k), e v = v :=
      w172_cent_of_comm h hq he hq_ne hqe_comm.symm
    have hq_fixes_e : ∀ v ∈ Vd e, (e * (e * f) ^ k) v = v :=
      w172_cent_of_comm h he hq (Ne.symm hq_ne) hqe_comm
    have hf_fixes_r : ∀ v ∈ Vd (f * (e * f) ^ k), f v = v :=
      w172_cent_of_comm h hr hf hr_ne hrf_comm.symm
    have hr_fixes_f : ∀ v ∈ Vd f, (f * (e * f) ^ k) v = v :=
      w172_cent_of_comm h hf hr (Ne.symm hr_ne) hrf_comm
    have hz_fix_e : ∀ v ∈ Vd e, ((e * f) ^ k) v = v := by
      intro v hv
      have h3 : (e * (e * (e * f) ^ k)) v = v := by
        rw [LinearEquiv.mul_apply, hq_fixes_e v hv, h.fix e he v hv]
      rwa [show e * (e * (e * f) ^ k) = (e * f) ^ k by
        rw [← mul_assoc, h.sq e he, one_mul]] at h3
    have hz_fix_f : ∀ v ∈ Vd f, ((e * f) ^ k) v = v := by
      intro v hv
      have h3 : (f * (f * (e * f) ^ k)) v = v := by
        rw [LinearEquiv.mul_apply, hr_fixes_f v hv, h.fix f hf v hv]
      rwa [show f * (f * (e * f) ^ k) = (e * f) ^ k by
        rw [← mul_assoc, h.sq f hf, one_mul]] at h3
    have hfixVf : ∀ w ∈ Vd f, e w = w := by
      intro w hw
      have hq_w : e ((e * (e * f) ^ k) w) = w := by
        have h3 : (e * (e * (e * f) ^ k)) w = w := by
          rw [show e * (e * (e * f) ^ k) = (e * f) ^ k by
            rw [← mul_assoc, h.sq e he, one_mul]]
          exact hz_fix_f w hw
        rwa [LinearEquiv.mul_apply] at h3
      have h2 : e ((e * (e * f) ^ k) w - w) = (e * (e * f) ^ k) w - w :=
        he_fixes_q _ (h.comm_le (e * (e * f) ^ k) hq w)
      have hms : e (w - (e * (e * f) ^ k) w) = e w - e ((e * (e * f) ^ k) w) :=
        (e : W →ₗ[ZMod 2] W).map_sub w ((e * (e * f) ^ k) w)
      have hmn : e (-((e * (e * f) ^ k) w - w)) = -e ((e * (e * f) ^ k) w - w) :=
        (e : W →ₗ[ZMod 2] W).map_neg ((e * (e * f) ^ k) w - w)
      have hww : e w - w = e w - e ((e * (e * f) ^ k) w) := by rw [hq_w]
      have h1 : e w - w = -((e * (e * f) ^ k) w - w) := by
        rw [hww, ← hms, show w - (e * (e * f) ^ k) w
              = -((e * (e * f) ^ k) w - w) by abel, hmn, h2]
      have hmemq : e w - w ∈ Vd (e * (e * f) ^ k) := by
        rw [h1]
        exact Submodule.neg_mem _ (h.comm_le (e * (e * f) ^ k) hq w)
      have hmeminf : e w - w ∈ Vd e ⊓ Vd (e * (e * f) ^ k) :=
        Submodule.mem_inf.mpr ⟨h.comm_le e he w, hmemq⟩
      rw [h.disjoint e he (e * (e * f) ^ k) hq (Ne.symm hq_ne), Submodule.mem_bot] at hmeminf
      exact sub_eq_zero.mp hmeminf
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff (Vd f)).mp (h.ne_bot f hf)
    exact hcomm (h.fix_le_cent f hf w hw hw0 e (h.mem e he) (hfixVf w hw))

theorem w172_eq_one_of_inverted (h : W172InvSys L D Vd) {e f : LGL 2 W} (he : e ∈ D)
    (hf : f ∈ D) (hne : e ≠ f) (hcomm : e * f = f * e) {x : LGL 2 W} (hx : x ∈ L)
    (hodd : Odd (orderOf x)) (hex : e * x * e⁻¹ = x⁻¹) (hfx : f * x * f⁻¹ = x⁻¹) : x = 1 := by
  have he_inv : e⁻¹ = e := w172_inv_eq_self h he
  have hf_inv : f⁻¹ = f := w172_inv_eq_self h hf
  obtain ⟨k, hk⟩ := hodd
  let y : LGL 2 W := x ^ (k + 1)
  have hyL : y ∈ L := L.pow_mem hx (k + 1)
  have hyy : y * y = x := by
    change x ^ (k + 1) * x ^ (k + 1) = x
    rw [← pow_add, show k + 1 + (k + 1) = orderOf x + 1 by omega,
        pow_succ, pow_orderOf_eq_one, one_mul]
  have hey : e * y * e⁻¹ = y⁻¹ := by
    change e * x ^ (k + 1) * e⁻¹ = (x ^ (k + 1))⁻¹
    rw [← conj_pow, hex, inv_pow]
  have hey_e : e * y * e = y⁻¹ := by simpa [he_inv] using hey
  have hey_eq : e * y = y⁻¹ * e := by
    apply mul_right_cancel (b := e)
    rw [hey_e, mul_assoc, h.sq e he, mul_one]
  have hxinv : x⁻¹ * e = e * x := by
    rw [← hex, mul_assoc, he_inv, h.sq e he, mul_one]
  have hyey : y⁻¹ * e * y = e * x := by
    rw [mul_assoc, hey_eq, ← mul_assoc, ← mul_inv_rev, hyy, hxinv]
  have hexD : e * x ∈ D := by
    rw [← hyey]
    simpa using h.conj_mem e he y⁻¹ (L.inv_mem hyL)
  have hc_sq : (f * e) * (f * e) = 1 := by
    calc (f * e) * (f * e) = f * (e * f) * e := by group
      _ = f * (f * e) * e := by rw [hcomm]
      _ = (f * f) * (e * e) := by group
      _ = 1 := by rw [h.sq f hf, h.sq e he, one_mul]
  have hc_ne : f * e ≠ 1 := by
    intro hc1
    apply hne
    rw [← hf_inv]
    exact (inv_eq_of_mul_eq_one_right hc1).symm
  have hc_sq2 : (f * e) ^ 2 = 1 := by rw [pow_two]; exact hc_sq
  have horder_c : orderOf (f * e) = 2 := orderOf_eq_prime (p := 2) hc_sq2 hc_ne
  have hc_comm_x : Commute (f * e) x := by
    show (f * e) * x = x * (f * e)
    have hcx : (f * e) * x * (f * e)⁻¹ = x := by
      calc (f * e) * x * (f * e)⁻¹ = f * (e * x * e⁻¹) * f⁻¹ := by group
        _ = f * x⁻¹ * f⁻¹ := by rw [hex]
        _ = (f * x * f⁻¹)⁻¹ := by group
        _ = x := by rw [hfx, inv_inv]
    apply mul_right_cancel (b := (f * e)⁻¹)
    rw [hcx, mul_assoc, mul_inv_cancel, mul_one]
  have hgm : (f * (e * x)) ^ (orderOf x) = f * e := by
    have h1 : f * (e * x) = (f * e) * x := by group
    rw [h1, hc_comm_x.mul_pow (orderOf x), pow_orderOf_eq_one, mul_one]
    rw [hk, pow_succ, pow_mul, pow_two, hc_sq, one_pow, one_mul]
  have hdvd : orderOf ((f * (e * x)) ^ (orderOf x)) ∣ orderOf (f * (e * x)) :=
    orderOf_pow_dvd (x := f * (e * x)) (orderOf x)
  have h2dvd : 2 ∣ orderOf (f * (e * x)) := by
    rw [hgm, horder_c] at hdvd
    exact hdvd
  have hnot_odd_g : ¬ Odd (orderOf (f * (e * x))) := fun hoddg =>
    (Nat.not_even_iff_odd.mpr hoddg) (even_iff_two_dvd.mpr h2dvd)
  have hcommg : f * (e * x) = (e * x) * f := by
    rcases w172_comm_or_odd h hf hexD with hc | ho
    · exact hc
    · exact absurd ho hnot_odd_g
  have hfx_eq : f * (e * x) * f⁻¹ = e * x := by
    rw [hcommg, mul_assoc, mul_inv_cancel, mul_one]
  have hfe : f * e * f⁻¹ = e := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hL : f * (e * x) * f⁻¹ = e * x⁻¹ := by
    calc f * (e * x) * f⁻¹ = (f * e * f⁻¹) * (f * x * f⁻¹) := by group
      _ = e * x⁻¹ := by rw [hfe, hfx]
  have hex_eq : e * x = e * x⁻¹ := by
    rw [← hfx_eq, hL]
  have hxx : x = x⁻¹ := mul_left_cancel hex_eq
  have hxx1 : x * x = 1 := by
    nth_rewrite 2 [hxx]
    rw [mul_inv_cancel]
  have hdvd2 : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx1)
  have horder1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact h1
    · exfalso
      rw [h2] at hk
      omega
  exact orderOf_eq_one_iff.mp horder1

end CFSG.LocalAnalysis.WeakClosure81

end
