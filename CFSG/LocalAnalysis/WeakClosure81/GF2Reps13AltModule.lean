module

public import CFSG.Quasithin.H13.A5Semilinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

open CFSG.Quasithin Equiv
open scoped commutatorElement

section Module

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_card_eq_four_pow (hW : ∀ w : W, w ^ 2 = 1) {z : MulAut W} (hz : z ^ 3 = 1)
    {U : Subgroup W} (hU : ∀ u ∈ U, z u ∈ U) (hfix : ∀ u ∈ U, z u = u → u = 1) :
    ∃ k : ℕ, Nat.card U = 4 ^ k := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hP : IsPGroup 2 U := fun u => ⟨1, Subtype.ext (by simp [hW u.1])⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hz3 : ∀ w : W, z (z (z w)) = w := fun w => by
    have h := congrArg (fun e : MulAut W => e w) hz
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at h
    exact h
  let f : Function.End U := fun u => ⟨z u, hU u u.2⟩
  have hf : f ^ (3 ^ 1) = 1 := by
    show f ^ 3 = 1
    rw [pow_three]
    funext u
    exact Subtype.ext (hz3 u)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have h1 : (1 : U) ∈ f.fixedPoints := show f 1 = 1 from Subtype.ext (map_one z)
  have key : ∀ u : U, u ∈ f.fixedPoints → u = 1 := fun u hu =>
    Subtype.ext (hfix u u.2 (congrArg Subtype.val (show f u = u from hu)))
  have hfp : Nat.card f.fixedPoints = 1 :=
    Nat.card_eq_one_iff_exists.2 ⟨⟨1, h1⟩, fun y => Subtype.ext (key y.1 y.2)⟩
  have hmod' : Nat.card U ≡ Nat.card f.fixedPoints [MOD 3] := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hmod
  rw [hfp, hm] at hmod'
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
  · exact ⟨j, by rw [hm, hj, pow_mul]; norm_num⟩
  · exfalso
    rw [hj] at hmod'
    unfold Nat.ModEq at hmod'
    have h4 : 4 ^ j % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have h2 : 2 ^ (2 * j + 1) = 4 ^ j * 2 := by rw [pow_succ, pow_mul]; norm_num
    rw [h2] at hmod'
    omega

omit [Finite W] in
theorem index_fixV_of_inv_fpf (hW : ∀ w : W, w ^ 2 = 1) {z t : MulAut W} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (ht : t * t = 1) (htz : t * z * t⁻¹ = z⁻¹) {k : ℕ}
    (hk : Nat.card W = 4 ^ k) : (fixV (Subgroup.zpowers t)).index = 2 ^ k := by
  have hinvw : ∀ w : W, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW w)
  have hz3 : ∀ w : W, z (z (z w)) = w := fun w => by
    have h := congrArg (fun e : MulAut W => e w) hz
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at h
    exact h
  have hzi : z⁻¹ = z * z := inv_eq_of_mul_eq_one_right ((pow_three z).symm.trans hz)
  have hkey : ∀ y : W, z (z y) = z y * y := by
    intro y
    have hmem : y * z y * z (z y) ∈ fixV (Subgroup.zpowers z) := by
      rw [mem_fixV_zpowers_iff_apply, map_mul, map_mul, hz3]
      ac_rfl
    rw [hfix, Subgroup.mem_bot] at hmem
    calc z (z y) = (y * z y)⁻¹ := eq_inv_of_mul_eq_one_right hmem
      _ = z y * y := by rw [mul_inv, hinvw, hinvw, mul_comm]
  have hcomm : t * z = z⁻¹ * t := by
    rw [← htz, inv_mul_cancel_right]
  have hθ : ∀ w : W, t (z w) = z (t w) * t w := by
    intro w
    have h1 : t (z w) = z⁻¹ (t w) := by
      have h := congrArg (fun e : MulAut W => e w) hcomm
      simpa only [MulAut.mul_apply] using h
    rw [h1, hzi, MulAut.mul_apply, hkey]
  have hcard : Nat.card W = 2 ^ (2 * k) := by
    rw [hk, pow_mul]
    norm_num
  exact CFSG.Quasithin.H13.A5.index_fixV_of_semilinear hW z.toMonoidHom t ht hθ hcard

omit [Finite W] in
theorem card_fixV_zpowers_conj (g x : MulAut W) :
    Nat.card ↥(fixV (Subgroup.zpowers (g * x * g⁻¹))) =
      Nat.card ↥(fixV (Subgroup.zpowers x)) := by
  have hgg : ∀ a : W, g⁻¹ (g a) = a := fun a => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hgg' : ∀ a : W, g (g⁻¹ a) = a := fun a => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hto : ∀ v : W, v ∈ fixV (Subgroup.zpowers (g * x * g⁻¹)) →
      g⁻¹ v ∈ fixV (Subgroup.zpowers x) := by
    intro v hv
    rw [mem_fixV_zpowers_iff_apply, MulAut.mul_apply, MulAut.mul_apply] at hv
    rw [mem_fixV_zpowers_iff_apply]
    calc x (g⁻¹ v) = g⁻¹ (g (x (g⁻¹ v))) := (hgg _).symm
      _ = g⁻¹ v := by rw [hv]
  have hfrom : ∀ w : W, w ∈ fixV (Subgroup.zpowers x) →
      g w ∈ fixV (Subgroup.zpowers (g * x * g⁻¹)) := by
    intro w hw
    rw [mem_fixV_zpowers_iff_apply] at hw
    rw [mem_fixV_zpowers_iff_apply, MulAut.mul_apply, MulAut.mul_apply, hgg, hw]
  exact Nat.card_congr
    { toFun := fun v => ⟨g⁻¹ v.1, hto v.1 v.2⟩
      invFun := fun w => ⟨g w.1, hfrom w.1 w.2⟩
      left_inv := fun v => Subtype.ext (hgg' v.1)
      right_inv := fun w => Subtype.ext (hgg w.1) }

omit [Finite W] in
private theorem comm_apply {g h : MulAut W} (hgh : g * h = h * g) (v : W) :
    g (h v) = h (g v) := by
  have := congrArg (fun m : MulAut W => m v) hgh
  simpa only [MulAut.mul_apply] using this

omit [Finite W] in
private theorem cube_apply {g : MulAut W} (hg : g ^ 3 = 1) (w : W) : g (g (g w)) = w := by
  have h : g * (g * g) = 1 := by rw [← pow_three]; exact hg
  have h2 := congrArg (fun m : MulAut W => m w) h
  simpa only [MulAut.mul_apply, MulAut.one_apply] using h2

omit [Finite W] in
private theorem apply_mem_fixV {g h : MulAut W} (hgh : g * h = h * g) {v : W}
    (hv : v ∈ fixV (Subgroup.zpowers g)) : h v ∈ fixV (Subgroup.zpowers g) := by
  rw [mem_fixV_zpowers_iff_apply] at hv ⊢
  rw [comm_apply hgh, hv]

omit [Finite W] in
private theorem apply_trace3 {g : MulAut W} (hg : g ^ 3 = 1) (w : W) :
    g (w * g w * g (g w)) = w * g w * g (g w) := by
  rw [map_mul, map_mul, cube_apply hg]
  ac_rfl

omit [Finite W] in
private theorem trace3_of_fixed (hW : ∀ w : W, w ^ 2 = 1) {g : MulAut W} {w : W}
    (hw : g w = w) : w * g w * g (g w) = w := by
  rw [hw, hw, ← pow_two, hW, one_mul]

omit [Finite W] in
private theorem trace3_eq_one {z : MulAut W} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (w : W) : w * z w * z (z w) = 1 := by
  have h : w * z w * z (z w) ∈ fixV (Subgroup.zpowers z) :=
    mem_fixV_zpowers_iff_apply.2 (apply_trace3 hz w)
  rw [hfix] at h
  exact Subgroup.mem_bot.1 h

omit [Finite W] in
private theorem trace3_mul (g : MulAut W) (a b c : W) :
    (a * b * c) * g (a * b * c) * g (g (a * b * c)) =
      (a * g a * g (g a)) * (b * g b * g (g b)) * (c * g c * g (g c)) := by
  simp only [map_mul]
  ac_rfl

omit [Finite W] in
private theorem trace3_eq_one_of_apply {g z : MulAut W} (hgz : g * z = z * g) (hg : g ^ 3 = 1)
    (hz : z ^ 3 = 1) (hfix : fixV (Subgroup.zpowers z) = ⊥) {b : W} (hb : g (z b) = b) :
    b * g b * g (g b) = 1 := by
  have hgg : g (g b) = z b := by
    have h := cube_apply hg (z b)
    rwa [hb] at h
  have hgb : g b = z (z b) := by
    have h1 : z (g (g b)) = z (z b) := by rw [hgg]
    rwa [comm_apply hgz.symm, comm_apply hgz.symm, hb] at h1
  calc b * g b * g (g b) = b * z (z b) * z b := by rw [hgg, hgb]
    _ = b * z b * z (z b) := by ac_rfl
    _ = 1 := trace3_eq_one hz hfix b

omit [Finite W] in
private theorem trace3_eq_one_of_apply_apply {g z : MulAut W} (hgz : g * z = z * g)
    (hz : z ^ 3 = 1) (hfix : fixV (Subgroup.zpowers z) = ⊥) {c : W}
    (hc : g (z (z c)) = c) : c * g c * g (g c) = 1 := by
  have hgc : g c = z c := by
    have h1 : z (g (z (z c))) = z c := by rw [hc]
    rwa [comm_apply hgz.symm, cube_apply hz] at h1
  have hggc : g (g c) = z (z c) := by
    rw [hgc, ← comm_apply hgz.symm, hgc]
  calc c * g c * g (g c) = c * z c * z (z c) := by rw [hggc, hgc]
    _ = 1 := trace3_eq_one hz hfix c

omit [Finite W] in
private theorem pow_three_mul_pow {x z : MulAut W} (hxz : x * z = z * x) (hx : x ^ 3 = 1)
    (hz : z ^ 3 = 1) (k : ℕ) : (x * z ^ k) ^ 3 = 1 := by
  have hc : Commute x (z ^ k) := Commute.pow_right (show Commute x z from hxz) k
  rw [hc.mul_pow, hx, ← pow_mul, mul_comm k 3, pow_mul, hz, one_pow, one_mul]

omit [Finite W] in
private theorem trace3_prod_eq (hW : ∀ w : W, w ^ 2 = 1) {x z : MulAut W}
    (hxz : x * z = z * x) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (w : W) :
    (w * x w * x (x w)) * (w * (x * z) w * (x * z) ((x * z) w)) *
      (w * (x * z ^ 2) w * (x * z ^ 2) ((x * z ^ 2) w)) = w := by
  have hzx := comm_apply hxz
  have hz3 := cube_apply hz
  have e1 : z (x (z w)) = x (z (z w)) := (hzx (z w)).symm
  have e2 : z (z (x (z (z w)))) = x (z w) := by
    rw [← hzx (z (z w)), ← hzx (z (z (z w))), hz3 (z w)]
  have h0 := trace3_eq_one hz hfix w
  have h1 : x w * x (z w) * x (z (z w)) = 1 := by
    calc x w * x (z w) * x (z (z w)) = x (w * z w * z (z w)) := by simp only [map_mul]
      _ = 1 := by rw [h0, map_one]
  have h2 : x (x w) * x (x (z (z w))) * x (x (z w)) = 1 := by
    calc x (x w) * x (x (z (z w))) * x (x (z w)) = x (x (w * z (z w) * z w)) := by
          simp only [map_mul]
      _ = 1 := by rw [mul_right_comm, h0, map_one, map_one]
  simp only [MulAut.mul_apply, pow_two]
  rw [e1, e2]
  calc _ = (w * w * w) * (x w * x (z w) * x (z (z w))) *
          (x (x w) * x (x (z (z w))) * x (x (z w))) := by ac_rfl
    _ = w := by rw [h1, h2, mul_one, mul_one, ← pow_two, hW, one_mul]

omit [Finite W] in
private theorem proj_fst (hW : ∀ w : W, w ^ 2 = 1) {x z : MulAut W}
    (hxz : x * z = z * x) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) {a b c : W}
    (ha : a ∈ fixV (Subgroup.zpowers x)) (hb : b ∈ fixV (Subgroup.zpowers (x * z)))
    (hc : c ∈ fixV (Subgroup.zpowers (x * z ^ 2))) :
    (a * b * c) * x (a * b * c) * x (x (a * b * c)) = a := by
  have hb' : x (z b) = b := by
    simpa only [MulAut.mul_apply] using mem_fixV_zpowers_iff_apply.1 hb
  have hc' : x (z (z c)) = c := by
    simpa only [MulAut.mul_apply, pow_two] using mem_fixV_zpowers_iff_apply.1 hc
  rw [trace3_mul x a b c, trace3_of_fixed hW (mem_fixV_zpowers_iff_apply.1 ha),
    trace3_eq_one_of_apply hxz hx hz hfix hb',
    trace3_eq_one_of_apply_apply hxz hz hfix hc', mul_one, mul_one]

omit [Finite W] in
private theorem proj_snd (hW : ∀ w : W, w ^ 2 = 1) {x z : MulAut W}
    (hxz : x * z = z * x) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) {a b c : W}
    (ha : a ∈ fixV (Subgroup.zpowers x)) (hb : b ∈ fixV (Subgroup.zpowers (x * z)))
    (hc : c ∈ fixV (Subgroup.zpowers (x * z ^ 2))) :
    (a * b * c) * (x * z) (a * b * c) * (x * z) ((x * z) (a * b * c)) = b := by
  have hxz3 : (x * z) ^ 3 = 1 := by
    have := pow_three_mul_pow hxz hx hz 1
    rwa [pow_one] at this
  have hgz : (x * z) * z = z * (x * z) := by rw [← mul_assoc, ← hxz]
  have ha' : x a = a := mem_fixV_zpowers_iff_apply.1 ha
  have ha2 : (x * z) (z (z a)) = a := by
    rw [MulAut.mul_apply, cube_apply hz, ha']
  have hb' : (x * z) b = b := mem_fixV_zpowers_iff_apply.1 hb
  have hc2 : (x * z) (z c) = c := by
    simpa only [MulAut.mul_apply, pow_two] using mem_fixV_zpowers_iff_apply.1 hc
  rw [trace3_mul (x * z) a b c,
    trace3_eq_one_of_apply_apply hgz hz hfix ha2, trace3_of_fixed hW hb',
    trace3_eq_one_of_apply hgz hxz3 hz hfix hc2, one_mul, mul_one]

omit [Finite W] in
private theorem proj_thd (hW : ∀ w : W, w ^ 2 = 1) {x z : MulAut W}
    (hxz : x * z = z * x) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) {a b c : W}
    (ha : a ∈ fixV (Subgroup.zpowers x)) (hb : b ∈ fixV (Subgroup.zpowers (x * z)))
    (hc : c ∈ fixV (Subgroup.zpowers (x * z ^ 2))) :
    (a * b * c) * (x * z ^ 2) (a * b * c) * (x * z ^ 2) ((x * z ^ 2) (a * b * c)) = c := by
  have hxz23 : (x * z ^ 2) ^ 3 = 1 := pow_three_mul_pow hxz hx hz 2
  have hgz : (x * z ^ 2) * z = z * (x * z ^ 2) :=
    ((show Commute x z from hxz).mul_left ((Commute.refl z).pow_left 2)).eq
  have ha' : x a = a := mem_fixV_zpowers_iff_apply.1 ha
  have ha2 : (x * z ^ 2) (z a) = a := by
    simp only [MulAut.mul_apply, pow_two]
    rw [cube_apply hz, ha']
  have hb' : x (z b) = b := by
    simpa only [MulAut.mul_apply] using mem_fixV_zpowers_iff_apply.1 hb
  have hb2 : (x * z ^ 2) (z (z b)) = b := by
    simp only [MulAut.mul_apply, pow_two]
    rw [cube_apply hz (z b), hb']
  have hc' : (x * z ^ 2) c = c := mem_fixV_zpowers_iff_apply.1 hc
  rw [trace3_mul (x * z ^ 2) a b c, trace3_eq_one_of_apply hgz hxz23 hz hfix ha2,
    trace3_eq_one_of_apply_apply hgz hz hfix hb2, trace3_of_fixed hW hc', one_mul, one_mul]

omit [Finite W] in
theorem bijective_mul_fixV_of_fpf (hW : ∀ w : W, w ^ 2 = 1) {x z : MulAut W}
    (hxz : x * z = z * x) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) :
    Function.Bijective fun p : ↥(fixV (Subgroup.zpowers x)) ×
        ↥(fixV (Subgroup.zpowers (x * z))) × ↥(fixV (Subgroup.zpowers (x * z ^ 2))) =>
      (p.1 : W) * (p.2.1 : W) * (p.2.2 : W) := by
  have hxz3 : (x * z) ^ 3 = 1 := by
    have := pow_three_mul_pow hxz hx hz 1
    rwa [pow_one] at this
  have hxz23 : (x * z ^ 2) ^ 3 = 1 := pow_three_mul_pow hxz hx hz 2
  have hE : ∀ (g : MulAut W) (p q : W), p = q → p * g p * g (g p) = q * g q * g (g q) :=
    fun g p q hpq => by rw [hpq]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩⟩ h
    have h : a * b * c = a' * b' * c' := h
    have e1 : a = a' := (proj_fst hW hxz hx hz hfix ha hb hc).symm.trans
      ((hE x _ _ h).trans (proj_fst hW hxz hx hz hfix ha' hb' hc'))
    have e2 : b = b' := (proj_snd hW hxz hx hz hfix ha hb hc).symm.trans
      ((hE (x * z) _ _ h).trans (proj_snd hW hxz hx hz hfix ha' hb' hc'))
    have e3 : c = c' := (proj_thd hW hxz hx hz hfix ha hb hc).symm.trans
      ((hE (x * z ^ 2) _ _ h).trans (proj_thd hW hxz hx hz hfix ha' hb' hc'))
    subst e1 e2 e3
    rfl
  · intro w
    exact ⟨(⟨w * x w * x (x w), mem_fixV_zpowers_iff_apply.2 (apply_trace3 hx w)⟩,
      ⟨w * (x * z) w * (x * z) ((x * z) w), mem_fixV_zpowers_iff_apply.2 (apply_trace3 hxz3 w)⟩,
      ⟨w * (x * z ^ 2) w * (x * z ^ 2) ((x * z ^ 2) w),
        mem_fixV_zpowers_iff_apply.2 (apply_trace3 hxz23 w)⟩), trace3_prod_eq hW hxz hz hfix w⟩

omit [Finite W] in
theorem card_eq_mul_mul_of_fpf (hW : ∀ w : W, w ^ 2 = 1) {x z : MulAut W}
    (hxz : x * z = z * x) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) :
    Nat.card W = Nat.card ↥(fixV (Subgroup.zpowers x)) *
      Nat.card ↥(fixV (Subgroup.zpowers (x * z))) *
        Nat.card ↥(fixV (Subgroup.zpowers (x * z ^ 2))) := by
  have h := Nat.card_congr (Equiv.ofBijective _ (bijective_mul_fixV_of_fpf hW hxz hx hz hfix))
  rw [Nat.card_prod, Nat.card_prod] at h
  rw [← h, mul_assoc]

theorem card_fixV_le_index_of_inv (hW : ∀ w : W, w ^ 2 = 1) {x z t : MulAut W}
    (hxz : x * z = z * x) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (ht : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹)
    (htz : t * z = z * t) :
    Nat.card ↥(fixV (Subgroup.zpowers (x * z))) ≤ (fixV (Subgroup.zpowers t)).index := by
  have hww : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hzt : ∀ v : W, z (t v) = t (z v) := comm_apply htz.symm
  have hzx : ∀ v : W, x (z v) = z (x v) := comm_apply hxz
  have hxt : ∀ v : W, x (t v) = t (x (x v)) := by
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hxinv : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hx)
    rw [htinv, hxinv] at htx
    have hxt_eq : x * t = t * (x * x) := by
      calc x * t = (t * t) * x * t := by rw [ht, one_mul]
        _ = t * (t * x * t) := by simp only [mul_assoc]
        _ = t * (x * x) := by rw [htx]
    intro v
    have := congrArg (fun m : MulAut W => m v) hxt_eq
    simpa only [MulAut.mul_apply] using this
  have hmap : ∀ b : W, b ∈ fixV (Subgroup.zpowers (x * z)) →
      t b ∈ fixV (Subgroup.zpowers (x * z ^ 2)) := by
    intro b hb
    have hb' : x (z b) = b := by
      simpa only [MulAut.mul_apply] using mem_fixV_zpowers_iff_apply.1 hb
    have h1 : x (z (z b)) = z b := by rw [hzx (z b), hb']
    have h2 : x (x (z (z b))) = b := by rw [h1, hb']
    rw [mem_fixV_zpowers_iff_apply]
    calc (x * z ^ 2) (t b) = x (z (z (t b))) := by simp only [MulAut.mul_apply, pow_two]
      _ = x (t (z (z b))) := by rw [hzt, hzt]
      _ = t (x (x (z (z b)))) := hxt _
      _ = t b := by rw [h2]
  obtain ⟨φ, hφ⟩ : ∃ φ : W →* W, ∀ w, φ w = w * t w :=
    ⟨MonoidHom.mk' (fun w => w * t w) (fun a b => by simp only [map_mul]; ac_rfl),
      fun w => rfl⟩
  have hker : φ.ker = fixV (Subgroup.zpowers t) := by
    ext w
    rw [MonoidHom.mem_ker, hφ, mem_fixV_zpowers_iff_apply]
    constructor
    · intro h
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_eq_of_mul_eq_one_right (hww w)
    · intro h
      rw [h]
      exact hww w
  have hgz1 : (x * z) * z = z * (x * z) :=
    ((show Commute x z from hxz).mul_left (Commute.refl z)).eq
  have hxz3 : (x * z) ^ 3 = 1 := by
    have := pow_three_mul_pow hxz hx hz 1
    rwa [pow_one] at this
  have hkill : ∀ c : W, c ∈ fixV (Subgroup.zpowers (x * z)) →
      c ∈ fixV (Subgroup.zpowers (x * z ^ 2)) → c = 1 := by
    intro c hc1 hc2
    have h1 : (x * z) c = c := mem_fixV_zpowers_iff_apply.1 hc1
    have h2 : (x * z) (z c) = c := by
      simpa only [MulAut.mul_apply, pow_two] using mem_fixV_zpowers_iff_apply.1 hc2
    exact (trace3_of_fixed hW h1).symm.trans (trace3_eq_one_of_apply hgz1 hxz3 hz hfix h2)
  have hinj : Function.Injective (fun b : ↥(fixV (Subgroup.zpowers (x * z))) =>
      (⟨φ (b : W), (b : W), rfl⟩ : φ.range)) := by
    intro b b' h
    have h' : φ (b : W) = φ (b' : W) := congrArg Subtype.val h
    have hc : (b : W) * (b' : W) ∈ fixV (Subgroup.zpowers (x * z)) :=
      Subgroup.mul_mem _ b.2 b'.2
    have hcφ : φ ((b : W) * (b' : W)) = 1 := by
      rw [map_mul, h']
      exact hww _
    have htc : t ((b : W) * (b' : W)) = (b : W) * (b' : W) := by
      have hmem : (b : W) * (b' : W) ∈ φ.ker := MonoidHom.mem_ker.2 hcφ
      rw [hker] at hmem
      exact mem_fixV_zpowers_iff_apply.1 hmem
    have hc2 : (b : W) * (b' : W) ∈ fixV (Subgroup.zpowers (x * z ^ 2)) := by
      have := hmap _ hc
      rwa [htc] at this
    have h1 : (b : W) * (b' : W) = 1 := hkill _ hc hc2
    exact Subtype.ext ((mul_eq_one_iff_eq_inv.1 h1).trans (inv_eq_of_mul_eq_one_right (hww _)))
  calc Nat.card ↥(fixV (Subgroup.zpowers (x * z)))
      ≤ Nat.card φ.range := Nat.card_le_card_of_injective _ hinj
    _ = φ.ker.index := (Subgroup.index_ker φ).symm
    _ = (fixV (Subgroup.zpowers t)).index := by rw [hker]

private theorem fixes_of_card_four {z u : MulAut W} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (huz : u * z = z * u) (hu : u * u = 1)
    {U : Subgroup W} (hzU : ∀ w ∈ U, z w ∈ U) (huU : ∀ w ∈ U, u w ∈ U)
    (hU : Nat.card U = 4) {a : W} (ha : a ∈ U) : u a = a := by
  classical
  by_cases ha1 : a = 1
  · rw [ha1, map_one]
  have hz1 : ∀ v : W, z v = v → v = 1 := fun v hv => by
    have h : v ∈ fixV (Subgroup.zpowers z) := mem_fixV_zpowers_iff_apply.2 hv
    rw [hfix] at h
    exact Subgroup.mem_bot.1 h
  have hz3 := cube_apply hz
  have huu : ∀ v : W, u (u v) = v := fun v => by
    have := congrArg (fun m : MulAut W => m v) hu
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have huzc : ∀ v : W, u (z v) = z (u v) := comm_apply huz
  have hzinj : ∀ p q : W, z p = z q → p = q := fun p q h => EquivLike.injective z h
  have h_za : z a ≠ a := fun h => ha1 (hz1 a h)
  have h_zza : z (z a) ≠ a := fun h => h_za (by
    have h2 : z (z (z a)) = z a := by rw [h]
    rw [hz3] at h2
    exact h2.symm)
  have n01 : (1 : W) ≠ a := Ne.symm ha1
  have n02 : (1 : W) ≠ z a := fun h =>
    ha1 (hzinj a 1 (by rw [map_one]; exact h.symm))
  have n03 : (1 : W) ≠ z (z a) := fun h =>
    n02 (hzinj (z a) 1 (by rw [map_one]; exact h.symm)).symm
  have n12 : a ≠ z a := h_za.symm
  have n13 : a ≠ z (z a) := h_zza.symm
  have n23 : z a ≠ z (z a) := fun h => h_za (hzinj (z a) a h.symm)
  have : Fintype U := Fintype.ofFinite U
  have hcard : Fintype.card U = 4 := by rw [← Nat.card_eq_fintype_card]; exact hU
  obtain ⟨e0, he0⟩ : ∃ e : U, (e : W) = 1 := ⟨⟨1, U.one_mem⟩, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ e : U, (e : W) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e : U, (e : W) = z a := ⟨⟨z a, hzU a ha⟩, rfl⟩
  obtain ⟨e3, he3⟩ : ∃ e : U, (e : W) = z (z a) := ⟨⟨z (z a), hzU _ (hzU a ha)⟩, rfl⟩
  have d01 : e0 ≠ e1 := fun h => n01 (by
    have := congrArg Subtype.val h
    rwa [he0, he1] at this)
  have d02 : e0 ≠ e2 := fun h => n02 (by
    have := congrArg Subtype.val h
    rwa [he0, he2] at this)
  have d03 : e0 ≠ e3 := fun h => n03 (by
    have := congrArg Subtype.val h
    rwa [he0, he3] at this)
  have d12 : e1 ≠ e2 := fun h => n12 (by
    have := congrArg Subtype.val h
    rwa [he1, he2] at this)
  have d13 : e1 ≠ e3 := fun h => n13 (by
    have := congrArg Subtype.val h
    rwa [he1, he3] at this)
  have d23 : e2 ≠ e3 := fun h => n23 (by
    have := congrArg Subtype.val h
    rwa [he2, he3] at this)
  have hs : ({e0, e1, e2, e3} : Finset U).card = Fintype.card U := by
    rw [hcard, Finset.card_insert_of_notMem (by simp [d01, d02, d03]),
      Finset.card_insert_of_notMem (by simp [d12, d13]),
      Finset.card_insert_of_notMem (by simp [d23]), Finset.card_singleton]
  have huniv := Finset.eq_univ_of_card _ hs
  have key : ∀ y ∈ U, y = 1 ∨ y = a ∨ y = z a ∨ y = z (z a) := by
    intro y hy
    have hmem : (⟨y, hy⟩ : U) ∈ ({e0, e1, e2, e3} : Finset U) := by
      rw [huniv]
      exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl ((congrArg Subtype.val h).trans he0)
    · exact Or.inr (Or.inl ((congrArg Subtype.val h).trans he1))
    · exact Or.inr (Or.inr (Or.inl ((congrArg Subtype.val h).trans he2)))
    · exact Or.inr (Or.inr (Or.inr ((congrArg Subtype.val h).trans he3)))
  have hua : u a ∈ U := huU a ha
  rcases key (u a) hua with h | h | h | h
  · exfalso
    apply ha1
    calc a = u (u a) := (huu a).symm
      _ = u 1 := by rw [h]
      _ = 1 := map_one u
  · exact h
  · exfalso
    apply h_zza
    calc z (z a) = z (u a) := by rw [h]
      _ = u (z a) := (huzc a).symm
      _ = u (u a) := by rw [h]
      _ = a := huu a
  · exfalso
    apply h_za
    calc z a = z (z (z (z a))) := (hz3 (z a)).symm
      _ = z (z (u a)) := by rw [h]
      _ = z (u (z a)) := by rw [huzc]
      _ = u (z (z a)) := (huzc _).symm
      _ = u (u a) := by rw [h]
      _ = a := huu a

theorem eq_one_of_card_fixV_eq_four (hW : ∀ w : W, w ^ 2 = 1) {x z u : MulAut W}
    (hxz : x * z = z * x) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (hux : u * x = x * u) (huz : u * z = z * u)
    (hu : u * u = 1) (h1 : Nat.card ↥(fixV (Subgroup.zpowers x)) = 4)
    (h2 : Nat.card ↥(fixV (Subgroup.zpowers (x * z))) = 4)
    (h3 : Nat.card ↥(fixV (Subgroup.zpowers (x * z ^ 2))) = 4) : u = 1 := by
  have cxz : Commute x z := hxz
  have cuz : Commute u z := huz
  have cux : Commute u x := hux
  have cz1 : (x * z) * z = z * (x * z) := (cxz.mul_left (Commute.refl z)).eq
  have cz2 : (x * z ^ 2) * z = z * (x * z ^ 2) :=
    (cxz.mul_left ((Commute.refl z).pow_left 2)).eq
  have cu1 : (x * z) * u = u * (x * z) := (cux.symm.mul_left cuz.symm).eq
  have cu2 : (x * z ^ 2) * u = u * (x * z ^ 2) :=
    (cux.symm.mul_left (cuz.symm.pow_left 2)).eq
  have f1 : ∀ w ∈ fixV (Subgroup.zpowers x), u w = w := fun w hw =>
    fixes_of_card_four hz hfix huz hu (U := fixV (Subgroup.zpowers x))
      (fun v hv => apply_mem_fixV hxz hv) (fun v hv => apply_mem_fixV hux.symm hv) h1 hw
  have f2 : ∀ w ∈ fixV (Subgroup.zpowers (x * z)), u w = w := fun w hw =>
    fixes_of_card_four hz hfix huz hu (U := fixV (Subgroup.zpowers (x * z)))
      (fun v hv => apply_mem_fixV cz1 hv) (fun v hv => apply_mem_fixV cu1 hv) h2 hw
  have f3 : ∀ w ∈ fixV (Subgroup.zpowers (x * z ^ 2)), u w = w := fun w hw =>
    fixes_of_card_four hz hfix huz hu (U := fixV (Subgroup.zpowers (x * z ^ 2)))
      (fun v hv => apply_mem_fixV cz2 hv) (fun v hv => apply_mem_fixV cu2 hv) h3 hw
  have hsurj := (bijective_mul_fixV_of_fpf hW hxz hx hz hfix).2
  refine MulEquiv.ext fun w => ?_
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩, hw⟩ := hsurj w
  have hw' : a * b * c = w := hw
  rw [← hw', MulAut.one_apply, map_mul, map_mul, f1 a ha, f2 b hb, f3 c hc]

end Module

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt

end
