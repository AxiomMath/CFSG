module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
public import CFSG.LocalAnalysis.WeakClosure81.W172ModDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

omit [Finite W] in
private lemma w172_fixSub_zpowers (a : LGL 2 W) :
    fixSub (Subgroup.zpowers a) = LinearMap.ker ((a : W →ₗ[ZMod 2] W) - LinearMap.id) := by
  ext v
  rw [LinearMap.mem_ker, mem_fixSub]
  constructor
  · intro h
    have h1 := h a (Subgroup.mem_zpowers a)
    change a v - v = 0
    rw [h1, sub_self]
  · intro h g hg
    have hav : a v = v := by simpa using sub_eq_zero.mp h
    have hmem : a ∈ MulAction.stabilizer (LGL 2 W) v := hav
    exact (Subgroup.zpowers_le.mpr hmem) hg

private lemma w172_exists_mul_modEq_one {p : ℕ} (hp : p.Prime) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) : ∃ r : ℕ, (p : ℤ) ∣ (r : ℤ) * k - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk0 : (k : ZMod p) ≠ 0 := fun h =>
    hk ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h)
  refine ⟨(((k : ZMod p)⁻¹).val), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hval : ((((k : ZMod p)⁻¹).val : ℕ) : ZMod p) = (k : ZMod p)⁻¹ :=
    ZMod.natCast_zmod_val _
  push_cast
  rw [hval, inv_mul_cancel₀ hk0, sub_self]

private lemma w172_exists_dvd_sub_mul {p : ℕ} (hp : p.Prime) {i : ℤ}
    (hi : ¬ (p : ℤ) ∣ i) (m : ℤ) : ∃ k : ℕ, (p : ℤ) ∣ m - (k : ℤ) * i := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hi0 : (i : ZMod p) ≠ 0 := fun h =>
    hi ((ZMod.intCast_zmod_eq_zero_iff_dvd i p).mp h)
  refine ⟨((m : ZMod p) * (i : ZMod p)⁻¹).val, ?_⟩
  have hval : ((((m : ZMod p) * (i : ZMod p)⁻¹).val : ℕ) : ZMod p) =
      (m : ZMod p) * (i : ZMod p)⁻¹ := ZMod.natCast_zmod_val _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hval, mul_assoc, inv_mul_cancel₀ hi0, mul_one, sub_self]

omit [Finite W] in
private lemma w172_pow_mem {U : Submodule (ZMod 2) W} {z : LGL 2 W}
    (hUz : ∀ u ∈ U, z u ∈ U) : ∀ (n : ℕ) (u : W), u ∈ U → (z ^ n) u ∈ U := by
  intro n
  induction n with
  | zero => intro u hu; simpa using hu
  | succ n ih => intro u hu; rw [pow_succ']; exact hUz _ (ih u hu)

omit [Finite W] in
private lemma w172_zpow_mem {U : Submodule (ZMod 2) W} {z : LGL 2 W} {p : ℕ} (hp : p.Prime)
    (hz : z ^ p = 1) (hUz : ∀ u ∈ U, z u ∈ U) :
    ∀ (m : ℤ) (u : W), u ∈ U → (z ^ m) u ∈ U := by
  have hinv : ∀ u ∈ U, z⁻¹ u ∈ U := by
    have hz1 : z⁻¹ = z ^ (p - 1) := inv_eq_of_mul_eq_one_left (by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hz])
    intro u hu
    rw [hz1]
    exact w172_pow_mem hUz (p - 1) u hu
  have hinvpow : ∀ (n : ℕ) (u : W), u ∈ U → ((z⁻¹) ^ n) u ∈ U := w172_pow_mem hinv
  intro m u hu
  obtain ⟨n, hm | hm⟩ := Int.eq_nat_or_neg m
  · rw [hm, zpow_natCast]; exact w172_pow_mem hUz n u hu
  · rw [hm, zpow_neg, zpow_natCast, ← inv_pow]; exact hinvpow n u hu

omit [Finite W] in
private lemma w172_zpow_comm {U : Submodule (ZMod 2) W} {g z : LGL 2 W} {p : ℕ} (hp : p.Prime)
    (hz : z ^ p = 1) (hUz : ∀ u ∈ U, z u ∈ U)
    (hcomm : ∀ u ∈ U, z (g u) = g (z u)) :
    ∀ (m : ℤ) (u : W), u ∈ U → (z ^ m) (g u) = g ((z ^ m) u) := by
  have hnat : ∀ (n : ℕ) (u : W), u ∈ U → (z ^ n) (g u) = g ((z ^ n) u) := by
    intro n
    induction n with
    | zero => intro u _; rfl
    | succ n ih =>
      intro u hu
      rw [pow_succ']
      change z ((z ^ n) (g u)) = g (z ((z ^ n) u))
      rw [ih u hu, hcomm ((z ^ n) u) (w172_pow_mem hUz n u hu)]
  intro m u hu
  obtain ⟨n, hm | hm⟩ := Int.eq_nat_or_neg m
  · rw [hm, zpow_natCast]; exact hnat n u hu
  · rw [hm]
    have hu' : (z ^ (-(n : ℤ))) u ∈ U := w172_zpow_mem hp hz hUz (-(n : ℤ)) u hu
    have h1 : (z ^ (n : ℤ)) (g ((z ^ (-(n : ℤ))) u)) = g u := by
      have hn := hnat n ((z ^ (-(n : ℤ))) u) hu'
      rw [← zpow_natCast] at hn
      have h2 : (z ^ (n : ℤ)) ((z ^ (-(n : ℤ))) u) = u := by
        rw [← LinearEquiv.mul_apply]
        have : (z ^ (n : ℤ)) * (z ^ (-(n : ℤ))) = 1 := by
          rw [← zpow_add, add_neg_cancel, zpow_zero]
        rw [this]; rfl
      rw [h2] at hn
      exact hn
    have h3 := congrArg (fun w => (z ^ (-(n : ℤ))) w) h1
    have h4 : (z ^ (-(n : ℤ))) ((z ^ (n : ℤ)) (g ((z ^ (-(n : ℤ))) u))) =
        g ((z ^ (-(n : ℤ))) u) := by
      rw [← LinearEquiv.mul_apply]
      have : (z ^ (-(n : ℤ))) * (z ^ (n : ℤ)) = 1 := by
        rw [← zpow_add, neg_add_cancel, zpow_zero]
      rw [this]; rfl
    rw [h4] at h3
    exact h3.symm

private lemma w172_inv_mem {U : Submodule (ZMod 2) W} {x : LGL 2 W}
    (hUx : ∀ u ∈ U, x u ∈ U) : ∀ u ∈ U, x⁻¹ u ∈ U := by
  classical
  intro u hu
  have hinj : Function.Injective (fun v : U => (⟨x v, hUx v v.2⟩ : U)) :=
    fun a b h => Subtype.ext (x.injective (Subtype.ext_iff.mp h))
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective
    (f := fun v : U => (⟨x v, hUx v v.2⟩ : U)) hinj ⟨u, hu⟩
  have hxw : x (w : W) = u := congrArg Subtype.val hw
  have hxu : x⁻¹ u = w := by rw [← hxw]; exact x.symm_apply_apply (w : W)
  rw [hxu]; exact w.2

private def w172Eig (U : Submodule (ZMod 2) W) (y z : LGL 2 W) (m : ℤ) :
    Submodule (ZMod 2) W :=
  U ⊓ LinearMap.ker ((y : W →ₗ[ZMod 2] W) - ((z ^ m : LGL 2 W) : W →ₗ[ZMod 2] W))

omit [Finite W] in
private lemma w172_mem_eig {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {m : ℤ} {u : W} :
    u ∈ w172Eig U y z m ↔ u ∈ U ∧ y u = (z ^ m) u := by
  simp only [w172Eig, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  exact Iff.rfl

omit [Finite W] in
private lemma w172_eig_zero {U : Submodule (ZMod 2) W} (y z : LGL 2 W) :
    w172Eig U y z 0 = U ⊓ fixSub (Subgroup.zpowers y) := by
  rw [w172Eig, w172_fixSub_zpowers]
  simp

omit [Finite W] in
private lemma w172_eig_fix_eq_zero {U : Submodule (ZMod 2) W} {z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hz : z ^ p = 1) (hfix : ∀ u ∈ U, z u = u → u = 0)
    {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) {u : W} (hu : u ∈ U) (h : (z ^ k) u = u) : u = 0 := by
  obtain ⟨r, hr⟩ := w172_exists_mul_modEq_one hp hk
  obtain ⟨t, ht⟩ := hr
  have hzpt : (z : LGL 2 W) ^ ((p : ℤ) * t) = 1 := by
    rw [zpow_mul, zpow_natCast, hz, one_zpow]
  have hzr : (z ^ k) ^ r = z := by
    rw [← zpow_natCast, ← zpow_mul]
    have hkr : k * (r : ℤ) = (r : ℤ) * k := by ring
    rw [hkr]
    have h1 : (r : ℤ) * k = 1 + (p : ℤ) * t := by linarith
    rw [h1, zpow_add, hzpt, mul_one, zpow_one]
  have hpow : ∀ n : ℕ, ((z ^ k) ^ n) u = u := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ']; change (z ^ k) (((z ^ k) ^ n) u) = u; rw [ih, h]
  exact hfix u hu (by rw [← hzr]; exact hpow r)

omit [Finite W] in
private lemma w172_eig_T_maps {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ} (hp : p.Prime)
    (hz : z ^ p = 1) (hUy : ∀ u ∈ U, y u ∈ U) (hUz : ∀ u ∈ U, z u ∈ U)
    (hzy : ∀ u ∈ U, z (y u) = y (z u)) {i j : ℤ} {w : W} (hw : w ∈ w172Eig U y z i) :
    ((y : W →ₗ[ZMod 2] W) - ((z ^ j : LGL 2 W) : W →ₗ[ZMod 2] W)) w ∈
      w172Eig U y z i := by
  obtain ⟨hwU, hwy⟩ := w172_mem_eig.mp hw
  have hTm : ((y : W →ₗ[ZMod 2] W) - ((z ^ j : LGL 2 W) : W →ₗ[ZMod 2] W)) w =
      y w - (z ^ j) w := rfl
  rw [w172_mem_eig]
  refine ⟨?_, ?_⟩
  · rw [hTm]
    exact U.sub_mem (hUy w hwU) (w172_zpow_mem hp hz hUz j w hwU)
  · rw [hTm, map_sub, map_sub]
    have hcomm_i := w172_zpow_comm hp hz hUz hzy i w hwU
    have hcomm_j := w172_zpow_comm hp hz hUz hzy j w hwU
    have hL : y (y w) = (z ^ (i + i)) w := by
      calc y (y w) = y ((z ^ i) w) := by rw [hwy]
        _ = (z ^ i) (y w) := hcomm_i.symm
        _ = (z ^ i) ((z ^ i) w) := by rw [hwy]
        _ = (z ^ (i + i)) w := by rw [← LinearEquiv.mul_apply, ← zpow_add]
    have hR : y ((z ^ j) w) = (z ^ (i + j)) w := by
      calc y ((z ^ j) w) = (z ^ j) (y w) := hcomm_j.symm
        _ = (z ^ j) ((z ^ i) w) := by rw [hwy]
        _ = (z ^ (j + i)) w := by rw [← LinearEquiv.mul_apply, ← zpow_add]
        _ = (z ^ (i + j)) w := by congr 1; ring
    have hL2 : (z ^ i) (y w) = (z ^ (i + i)) w := by
      rw [hwy, ← LinearEquiv.mul_apply, ← zpow_add]
    have hR2 : (z ^ i) ((z ^ j) w) = (z ^ (i + j)) w := by
      rw [← LinearEquiv.mul_apply, ← zpow_add]
    rw [hL, hR, hL2, hR2]

omit [Finite W] in
private lemma w172_eig_x_maps {U : Submodule (ZMod 2) W} {x y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hz : z ^ p = 1) (hUx : ∀ u ∈ U, x u ∈ U) (hUz : ∀ u ∈ U, z u ∈ U)
    (hzx : ∀ u ∈ U, z (x u) = x (z u)) {i : ℤ}
    (hxy : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) {m : ℤ} {u : W}
    (hu : u ∈ w172Eig U y z m) : x u ∈ w172Eig U y z (m - i) := by
  obtain ⟨huU, huy⟩ := w172_mem_eig.mp hu
  rw [w172_mem_eig]
  refine ⟨hUx u huU, ?_⟩
  have hcomm := w172_zpow_comm hp hz hUz hzx m u huU
  have h1 : (z ^ m) (x u) = (z ^ i) (y (x u)) := by
    rw [hcomm, ← hxy u huU, huy]
  have h2 : (z ^ (-i)) ((z ^ m) (x u)) = y (x u) := by
    rw [h1, ← LinearEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero]
    rfl
  rw [← h2, ← LinearEquiv.mul_apply, ← zpow_add]
  congr 1
  ring

private lemma w172_eig_inv_x_maps {U : Submodule (ZMod 2) W} {x y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hUx : ∀ u ∈ U, x u ∈ U) (hUz : ∀ u ∈ U, z u ∈ U) (hz : z ^ p = 1)
    (hzx : ∀ u ∈ U, z (x u) = x (z u)) (hzy : ∀ u ∈ U, z (y u) = y (z u)) {i : ℤ}
    (hxy : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) {m : ℤ} {v : W}
    (hv : v ∈ w172Eig U y z (m - i)) : x⁻¹ v ∈ w172Eig U y z m := by
  obtain ⟨hvU, hvy⟩ := w172_mem_eig.mp hv
  have hxinv : ∀ u ∈ U, x⁻¹ u ∈ U := w172_inv_mem hUx
  rw [w172_mem_eig]
  refine ⟨hxinv v hvU, ?_⟩
  apply x.injective
  have h1 : x (y (x⁻¹ v)) = (z ^ i) (y v) := by
    rw [hxy (x⁻¹ v) (hxinv v hvU)]
    exact congrArg (fun w => (z ^ i) (y w)) (x.apply_symm_apply v)
  have h2 : x ((z ^ m) (x⁻¹ v)) = (z ^ m) v := by
    rw [← w172_zpow_comm hp hz hUz hzx m (x⁻¹ v) (hxinv v hvU)]
    exact congrArg (fun w => (z ^ m) w) (x.apply_symm_apply v)
  rw [h1, h2, hvy, ← LinearEquiv.mul_apply, ← zpow_add]
  congr 1
  ring

private lemma w172_eig_finrank_step {U : Submodule (ZMod 2) W} {x y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hUx : ∀ u ∈ U, x u ∈ U) (hUy : ∀ u ∈ U, y u ∈ U)
    (hUz : ∀ u ∈ U, z u ∈ U) (hz : z ^ p = 1) (hzx : ∀ u ∈ U, z (x u) = x (z u))
    (hzy : ∀ u ∈ U, z (y u) = y (z u)) {i : ℤ}
    (hxy : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) (m : ℤ) :
    Module.finrank (ZMod 2) ↥(w172Eig U y z m) =
      Module.finrank (ZMod 2) ↥(w172Eig U y z (m - i)) := by
  apply le_antisymm
  · let f : (w172Eig U y z m) →ₗ[ZMod 2] (w172Eig U y z (m - i)) :=
      { toFun := fun u => ⟨x (u : W), w172_eig_x_maps hp hz hUx hUz hzx hxy u.2⟩
        map_add' := fun a b =>
          Subtype.ext (map_add (x : W →ₗ[ZMod 2] W) (a : W) (b : W))
        map_smul' := fun c a =>
          Subtype.ext (map_smul (x : W →ₗ[ZMod 2] W) c (a : W)) }
    have hinj : Function.Injective f := by
      intro a b h
      have h' : x (a : W) = x (b : W) :=
        congrArg (fun v : w172Eig U y z (m - i) => (v : W)) h
      exact Subtype.ext (x.injective h')
    exact LinearMap.finrank_le_finrank_of_injective (f := f) hinj
  · let f : (w172Eig U y z (m - i)) →ₗ[ZMod 2] (w172Eig U y z m) :=
      { toFun := fun v => ⟨x⁻¹ (v : W), w172_eig_inv_x_maps hp hUx hUz hz hzx hzy hxy v.2⟩
        map_add' := fun a b =>
          Subtype.ext (map_add ((x⁻¹ : LGL 2 W) : W →ₗ[ZMod 2] W) (a : W) (b : W))
        map_smul' := fun c a =>
          Subtype.ext (map_smul ((x⁻¹ : LGL 2 W) : W →ₗ[ZMod 2] W) c (a : W)) }
    have hinj : Function.Injective f := by
      intro a b h
      have h' : x⁻¹ (a : W) = x⁻¹ (b : W) :=
        congrArg (fun v : w172Eig U y z m => (v : W)) h
      exact Subtype.ext (x⁻¹.injective h')
    exact LinearMap.finrank_le_finrank_of_injective (f := f) hinj

private lemma w172_eig_eq_zero_of_dvd {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ}
    (hz : z ^ p = 1) {j : ℤ} (hj : (p : ℤ) ∣ j) : w172Eig U y z j = w172Eig U y z 0 := by
  obtain ⟨t, ht⟩ := hj
  have h : (z : LGL 2 W) ^ j = 1 := by
    rw [ht, zpow_mul, zpow_natCast, hz, one_zpow]
  simp only [w172Eig, h, zpow_zero]

private lemma w172_eig_dim_eq {U : Submodule (ZMod 2) W} {x y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hUx : ∀ u ∈ U, x u ∈ U) (hUy : ∀ u ∈ U, y u ∈ U)
    (hUz : ∀ u ∈ U, z u ∈ U) (hz : z ^ p = 1) (hzx : ∀ u ∈ U, z (x u) = x (z u))
    (hzy : ∀ u ∈ U, z (y u) = y (z u)) {i : ℤ} (hi : ¬ (p : ℤ) ∣ i)
    (hxy : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) (m : ℤ) :
    Module.finrank (ZMod 2) ↥(w172Eig U y z m) =
      Module.finrank (ZMod 2) ↥(w172Eig U y z 0) := by
  obtain ⟨k, hk⟩ := w172_exists_dvd_sub_mul hp hi m
  have hiter : ∀ k : ℕ, Module.finrank (ZMod 2) ↥(w172Eig U y z m) =
      Module.finrank (ZMod 2) ↥(w172Eig U y z (m - (k : ℤ) * i)) := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, zero_mul, sub_zero]
    | succ k ih =>
      rw [ih, w172_eig_finrank_step hp hUx hUy hUz hz hzx hzy hxy (m - (k : ℤ) * i)]
      rw [show m - (k : ℤ) * i - i = m - ((k + 1 : ℕ) : ℤ) * i by push_cast; ring]
  rw [hiter k, w172_eig_eq_zero_of_dvd hz hk]

omit [Finite W] in
private lemma w172_eig_indep {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hz : z ^ p = 1) (hUy : ∀ u ∈ U, y u ∈ U) (hUz : ∀ u ∈ U, z u ∈ U)
    (hzy : ∀ u ∈ U, z (y u) = y (z u)) (hfix : ∀ u ∈ U, z u = u → u = 0) :
    iSupIndep (fun j : Fin p => w172Eig U y z (j : ℤ)) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro S
  induction S using Finset.induction with
  | empty => intro v _ _ i hi; simp at hi
  | insert j0 S hj0S ih =>
    intro v hv h0 i hi
    rw [Finset.sum_insert hj0S] at h0
    have hvj0 : v j0 ∈ w172Eig U y z (j0 : ℤ) := hv j0 (Finset.mem_insert_self _ _)
    have hvS : ∀ j ∈ S, v j ∈ w172Eig U y z (j : ℤ) :=
      fun j hj => hv j (Finset.mem_insert_of_mem hj)
    let T : W →ₗ[ZMod 2] W :=
      (y : W →ₗ[ZMod 2] W) - ((z ^ (j0 : ℤ) : LGL 2 W) : W →ₗ[ZMod 2] W)
    have hTj0 : T (v j0) = 0 := by
      obtain ⟨_, hvy⟩ := w172_mem_eig.mp hvj0
      simp only [T, LinearMap.sub_apply]
      exact sub_eq_zero.mpr hvy
    have hTsum : ∑ j ∈ S, T (v j) = 0 := by
      have h := congrArg (fun w => T w) h0
      simp only [map_add, map_sum, hTj0, zero_add, map_zero] at h
      exact h
    have hTS : ∀ j ∈ S, T (v j) ∈ w172Eig U y z (j : ℤ) :=
      fun j hj => w172_eig_T_maps hp hz hUy hUz hzy (hvS j hj)
    have hTzero : ∀ j ∈ S, T (v j) = 0 := ih (fun j => T (v j)) hTS hTsum
    have hzeroS : ∀ j ∈ S, v j = 0 := by
      intro j hj
      have hTj := hTzero j hj
      obtain ⟨hvjU, hvjy⟩ := w172_mem_eig.mp (hvS j hj)
      simp only [T, LinearMap.sub_apply] at hTj
      have hjj : (z ^ (j : ℤ)) (v j) = (z ^ (j0 : ℤ)) (v j) := by
        rw [← hvjy]
        simpa using sub_eq_zero.mp hTj
      have hjne : j ≠ j0 := fun h => hj0S (h ▸ hj)
      have hk : ¬ (p : ℤ) ∣ (j : ℤ) - (j0 : ℤ) := by
        intro hdvd
        have habs : |(j : ℤ) - (j0 : ℤ)| < (p : ℤ) := by
          have h1 : (j : ℤ) < (p : ℤ) := by exact_mod_cast j.isLt
          have h2 : (j0 : ℤ) < (p : ℤ) := by exact_mod_cast j0.isLt
          have h3 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
          have h4 : (0 : ℤ) ≤ (j0 : ℤ) := Int.natCast_nonneg _
          rw [abs_lt]; constructor <;> omega
        have hze := Int.eq_zero_of_abs_lt_dvd hdvd habs
        exact hjne (Fin.ext (by omega))
      have heq : (z ^ ((j : ℤ) - (j0 : ℤ))) (v j) = v j := by
        have h2 := congrArg (fun w => (z ^ (-(j0 : ℤ))) w) hjj
        rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← zpow_add, ← zpow_add] at h2
        rw [show -(j0 : ℤ) + (j : ℤ) = (j : ℤ) - (j0 : ℤ) by ring,
          show -(j0 : ℤ) + (j0 : ℤ) = 0 by ring, zpow_zero] at h2
        simpa using h2
      exact w172_eig_fix_eq_zero hp hz hfix hk hvjU heq
    rw [Finset.mem_insert] at hi
    rcases hi with h | hiS
    · rw [h]
      have h0' : v j0 = -∑ j ∈ S, v j := by
        rw [← add_eq_zero_iff_eq_neg]; exact h0
      rw [h0', Finset.sum_eq_zero hzeroS, neg_zero]
    · exact hzeroS i hiS

private lemma w172_eig_finrank_sum {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ}
    (h : iSupIndep (fun j : Fin p => w172Eig U y z (j : ℤ))) (S : Finset (Fin p)) :
    ∀ T ⊆ S, Module.finrank (ZMod 2) ↥(T.sup fun j : Fin p => w172Eig U y z (j : ℤ)) =
      ∑ j ∈ T, Module.finrank (ZMod 2) ↥(w172Eig U y z (j : ℤ)) := by
  intro T
  induction T using Finset.induction with
  | empty => intro _; simp
  | insert j0 T hj0T ih =>
    intro hTS
    have hTS' : T ⊆ S := fun _ hj => hTS (Finset.mem_insert_of_mem hj)
    have hmem : j0 ∈ S := hTS (Finset.mem_insert_self _ _)
    have hdisj : Disjoint (w172Eig U y z (j0 : ℤ))
        (T.sup fun j : Fin p => w172Eig U y z (j : ℤ)) :=
      (iSupIndep_iff_supIndep.mp h S) hTS' hmem hj0T
    rw [Finset.sup_insert, Finset.sum_insert hj0T]
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq (w172Eig U y z (j0 : ℤ))
      (T.sup fun j : Fin p => w172Eig U y z (j : ℤ))
    rw [hdisj.eq_bot, finrank_bot, add_zero] at hfin
    rw [hfin, ih hTS']

theorem w172_heis_eigen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Submodule (ZMod 2) W}
    {x y z : LGL 2 W} (hUx : ∀ u ∈ U, x u ∈ U) (hUy : ∀ u ∈ U, y u ∈ U)
    (hUz : ∀ u ∈ U, z u ∈ U) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hzx : ∀ u ∈ U, z (x u) = x (z u)) (hzy : ∀ u ∈ U, z (y u) = y (z u))
    (hfix : ∀ u ∈ U, z u = u → u = 0) {i : ℕ} (hi : ¬ p ∣ i)
    (hxy : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) :
    p * Module.finrank (ZMod 2) ↥(U ⊓ fixSub (zpowers y)) ≤ Module.finrank (ZMod 2) ↥U := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hi' : ¬ (p : ℤ) ∣ (i : ℤ) := fun h => hi (Int.natCast_dvd_natCast.mp h)
  have hxy' : ∀ u ∈ U, x (y u) = (z ^ (i : ℤ)) (y (x u)) := by
    intro u hu; rw [hxy u hu, zpow_natCast]
  let E' : Fin p → Submodule (ZMod 2) W := fun j => w172Eig U y z (j : ℤ)
  have hindep : iSupIndep E' := w172_eig_indep hp hz hUy hUz hzy hfix
  have hsum := w172_eig_finrank_sum hindep (Finset.univ : Finset (Fin p))
    (Finset.univ : Finset (Fin p)) Finset.Subset.rfl
  have hle : Module.finrank (ZMod 2) ↥(Finset.univ.sup E') ≤ Module.finrank (ZMod 2) ↥U :=
    Submodule.finrank_mono (Finset.sup_le fun j _ => inf_le_left)
  have hall : ∀ j : Fin p, Module.finrank (ZMod 2) ↥(E' j) =
      Module.finrank (ZMod 2) ↥(E' 0) :=
    fun j => w172_eig_dim_eq hp hUx hUy hUz hz hzx hzy hi' hxy' (j : ℤ)
  have hcard : ∑ j : Fin p, Module.finrank (ZMod 2) ↥(E' j) =
      p * Module.finrank (ZMod 2) ↥(E' 0) := by
    rw [Finset.sum_congr rfl (fun j _ => hall j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    simp [Nat.nsmul_eq_mul]
  have hzero : E' 0 = U ⊓ fixSub (Subgroup.zpowers y) := w172_eig_zero y z
  rw [hzero] at hcard
  calc p * Module.finrank (ZMod 2) ↥(U ⊓ fixSub (Subgroup.zpowers y))
      = ∑ j : Fin p, Module.finrank (ZMod 2) ↥(E' j) := hcard.symm
    _ = Module.finrank (ZMod 2) ↥(Finset.univ.sup E') := hsum.symm
    _ ≤ Module.finrank (ZMod 2) ↥U := hle

private noncomputable def w172SubMap (U : Submodule (ZMod 2) W) (y : LGL 2 W)
    (hUy : ∀ u ∈ U, y u ∈ U) : ↥U →ₗ[ZMod 2] ↥U where
  toFun u := ⟨y (u : W) - (u : W), U.sub_mem (hUy u u.2) u.2⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    abel
  map_smul' c a := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul]
    rw [smul_sub]
    simp

private lemma w172_ker_subMap {U : Submodule (ZMod 2) W} {y : LGL 2 W}
    (hUy : ∀ u ∈ U, y u ∈ U) :
    LinearMap.ker (w172SubMap U y hUy) =
      (U ⊓ fixSub (Subgroup.zpowers y)).comap U.subtype := by
  ext u
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf, w172_fixSub_zpowers,
    LinearMap.mem_ker]
  constructor
  · intro h
    have h' : (w172SubMap U y hUy u : W) = 0 :=
      congrArg (fun v : ↥U => (v : W)) h
    exact ⟨u.2, by simpa [w172SubMap] using h'⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext (by simpa [w172SubMap] using h)

private noncomputable def w172ComapEquiv (U S : Submodule (ZMod 2) W) (hSU : S ≤ U) :
    ↥(S.comap U.subtype) ≃ₗ[ZMod 2] ↥S where
  toFun x := ⟨(x.1 : W), x.2⟩
  invFun s := ⟨⟨(s : W), hSU s.2⟩, s.2⟩
  map_add' x y := Subtype.ext rfl
  map_smul' c x := Subtype.ext rfl
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

private lemma w172_finrank_ker_subMap {U : Submodule (ZMod 2) W} {y : LGL 2 W}
    (hUy : ∀ u ∈ U, y u ∈ U) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (w172SubMap U y hUy)) =
      Module.finrank (ZMod 2) ↥(U ⊓ fixSub (Subgroup.zpowers y)) := by
  rw [w172_ker_subMap hUy]
  exact LinearEquiv.finrank_eq (w172ComapEquiv U (U ⊓ fixSub (Subgroup.zpowers y)) inf_le_left)

private lemma w172_finrank_range_subMap_le {U : Submodule (ZMod 2) W} {y : LGL 2 W}
    (hUy : ∀ u ∈ U, y u ∈ U) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (w172SubMap U y hUy)) ≤
      Module.finrank (ZMod 2) ↥(U ⊓ commSub (Subgroup.zpowers y)) := by
  let f : ↥(LinearMap.range (w172SubMap U y hUy)) →ₗ[ZMod 2]
      ↥(U ⊓ commSub (Subgroup.zpowers y)) :=
    { toFun := fun w => ⟨(w.1 : W), w.1.2, by
        rw [← w.2.choose_spec]
        simpa [w172SubMap] using
          sub_mem_commSub (Subgroup.zpowers y) (Subgroup.mem_zpowers y) (w.2.choose : W)⟩
      map_add' a b := Subtype.ext rfl
      map_smul' c a := Subtype.ext rfl }
  have hinj : Function.Injective f := by
    intro a b h
    have h' : (a.1 : W) = (b.1 : W) :=
      congrArg (fun v : ↥(U ⊓ commSub (Subgroup.zpowers y)) => (v.1 : W)) h
    exact Subtype.ext (Subtype.ext h')
  exact LinearMap.finrank_le_finrank_of_injective (f := f) hinj

theorem w172_heis_moves {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Submodule (ZMod 2) W}
    {x y z : LGL 2 W} (hUx : ∀ u ∈ U, x u ∈ U) (hUy : ∀ u ∈ U, y u ∈ U)
    (hUz : ∀ u ∈ U, z u ∈ U) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hzx : ∀ u ∈ U, z (x u) = x (z u)) (hzy : ∀ u ∈ U, z (y u) = y (z u))
    (hfix : ∀ u ∈ U, z u = u → u = 0) {i : ℕ} (hi : ¬ p ∣ i)
    (hxy : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) :
    (p - 1) * Module.finrank (ZMod 2) ↥U ≤
      p * Module.finrank (ZMod 2) ↥(U ⊓ commSub (zpowers y)) := by
  have heigen := w172_heis_eigen hp hp2 hUx hUy hUz hy hz hzx hzy hfix hi hxy
  set a : ℕ := Module.finrank (ZMod 2) ↥(U ⊓ fixSub (Subgroup.zpowers y)) with ha
  set c : ℕ := Module.finrank (ZMod 2) ↥(U ⊓ commSub (Subgroup.zpowers y)) with hc
  set d : ℕ := Module.finrank (ZMod 2) ↥U with hd
  have hrn := LinearMap.finrank_range_add_finrank_ker (w172SubMap U y hUy)
  have hker := w172_finrank_ker_subMap hUy
  have hrange := w172_finrank_range_subMap_le hUy
  have hdca : d ≤ c + a := by
    have h1 : Module.finrank (ZMod 2) ↥(LinearMap.range (w172SubMap U y hUy)) +
        Module.finrank (ZMod 2) ↥(LinearMap.ker (w172SubMap U y hUy)) = d := by
      rw [hrn, ← hd]
    rw [hker, ← ha] at h1
    have h2 : Module.finrank (ZMod 2) ↥(LinearMap.range (w172SubMap U y hUy)) ≤ c := by
      rw [hc]; exact hrange
    omega
  have hpa : p * a ≤ d := by rw [ha, hd]; exact heigen
  have hpd : p * d ≤ p * c + d := by
    calc p * d ≤ p * (c + a) := Nat.mul_le_mul_left p hdca
      _ = p * c + p * a := Nat.mul_add p c a
      _ ≤ p * c + d := Nat.add_le_add_left hpa (p * c)
  have hp1 : 1 ≤ p := hp.one_le
  have hsplit : p * d = (p - 1) * d + d := by
    conv_lhs => rw [← Nat.sub_add_cancel hp1, add_mul, one_mul]
  have hfinal : (p - 1) * d + d ≤ p * c + d := hsplit ▸ hpd
  exact Nat.add_le_add_iff_right.mp hfinal

@[expose] def w172Cent (Y : Subgroup (LGL 2 W)) (U : Submodule (ZMod 2) W)
    (hU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) : Subgroup (LGL 2 W) where
  carrier := {y | y ∈ Y ∧ ∀ x ∈ Y, ∀ u ∈ U, y (x u) = x (y u)}
  one_mem' := ⟨Y.one_mem, fun _ _ _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
    refine ⟨Y.mul_mem haY hbY, fun x hx u hu => ?_⟩
    show a (b (x u)) = x (a (b u))
    rw [hb x hx u hu, ha x hx (b u) (hU b hbY u hu)]
  inv_mem' := by
    rintro a ⟨haY, ha⟩
    refine ⟨Y.inv_mem haY, fun x hx u hu => ?_⟩
    have hv : a⁻¹ u ∈ U := hU a⁻¹ (Y.inv_mem haY) u hu
    have h2 : a (a⁻¹ u) = u := a.apply_symm_apply u
    have h1 : a (x (a⁻¹ u)) = x u := by rw [ha x hx (a⁻¹ u) hv, h2]
    calc a⁻¹ (x u) = a⁻¹ (a (x (a⁻¹ u))) := by rw [h1]
      _ = x (a⁻¹ u) := a.symm_apply_apply _

private lemma w172_heis_pair {p : ℕ} (hp : p.Prime) {Y : Subgroup (LGL 2 W)}
    (hY : ∀ y ∈ Y, y ^ p = 1) {U : Submodule (ZMod 2) W}
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) {z : LGL 2 W} (hzY : z ∈ Y)
    (hzc : ∀ y ∈ Y, ∀ u ∈ U, z (y u) = y (z u))
    (hcls : ∀ y ∈ Y, ∀ x ∈ Y, ∃ i : ℕ, ∀ u ∈ U, (y * x * y⁻¹ * x⁻¹) u = (z ^ i) u)
    {y : LGL 2 W} (hyY : y ∈ Y) (hyC : y ∉ w172Cent Y U hUY) :
    ∃ x ∈ Y, ∃ i : ℕ, ¬ p ∣ i ∧ (∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) ∧
      ∃ u ∈ U, y (x u) ≠ x (y u) := by
  have hnot : ¬ ∀ x ∈ Y, ∀ u ∈ U, y (x u) = x (y u) := fun h => hyC ⟨hyY, h⟩
  obtain ⟨x, hx⟩ : ∃ x, ¬ (x ∈ Y → ∀ u ∈ U, y (x u) = x (y u)) := not_forall.mp hnot
  obtain ⟨hxY, hxnot⟩ := not_imp.mp hx
  obtain ⟨u0, hu0⟩ : ∃ u0, ¬ (u0 ∈ U → y (x u0) = x (y u0)) := not_forall.mp hxnot
  obtain ⟨hu0U, hu0ne⟩ := not_imp.mp hu0
  obtain ⟨i, hi_rel⟩ := hcls x hxY y hyY
  have hxy_i : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u)) := by
    intro u hu
    have hyxu : y (x u) ∈ U := hUY y hyY (x u) (hUY x hxY u hu)
    have h := hi_rel (y (x u)) hyxu
    have hL : (x * y * x⁻¹ * y⁻¹) (y (x u)) = x (y u) := by
      simp [LinearEquiv.mul_apply]
    rw [hL] at h
    exact h
  refine ⟨x, hxY, i, ?_, hxy_i, u0, hu0U, hu0ne⟩
  have hz : z ^ p = 1 := hY z hzY
  have hzi_ne : (z ^ i) (y (x u0)) ≠ y (x u0) := by
    intro h
    have hxyeq : x (y u0) = y (x u0) := by rw [hxy_i u0 hu0U, h]
    exact hu0ne hxyeq.symm
  intro hpi
  obtain ⟨t, ht⟩ := hpi
  have hz1 : (z : LGL 2 W) ^ i = 1 := by rw [ht, pow_mul, hz, one_pow]
  exact hzi_ne (by rw [hz1]; rfl)

theorem w172_heis_moves_of_not_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (LGL 2 W)} (hY : ∀ y ∈ Y, y ^ p = 1) {U : Submodule (ZMod 2) W} (hU : U ≠ ⊥)
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) {z : LGL 2 W} (hzY : z ∈ Y)
    (hzc : ∀ y ∈ Y, ∀ u ∈ U, z (y u) = y (z u)) (hfix : ∀ u ∈ U, z u = u → u = 0)
    (hcls : ∀ y ∈ Y, ∀ x ∈ Y, ∃ i : ℕ, ∀ u ∈ U, (y * x * y⁻¹ * x⁻¹) u = (z ^ i) u)
    {y : LGL 2 W} (hyY : y ∈ Y) (hyC : y ∉ w172Cent Y U hUY) :
    (p - 1) * Module.finrank (ZMod 2) ↥U ≤
      p * Module.finrank (ZMod 2) ↥(U ⊓ commSub (zpowers y)) := by
  obtain ⟨x, hxY, i, hpi, hxy, -⟩ := w172_heis_pair hp hY hUY hzY hzc hcls hyY hyC
  exact w172_heis_moves hp hp2 (hUY x hxY) (hUY y hyY) (hUY z hzY) (hY y hyY) (hY z hzY)
    (hzc x hxY) (hzc y hyY) hfix hpi hxy

open scoped commutatorElement

private lemma w172_map_eq_self {U : Submodule (ZMod 2) W} {g : LGL 2 W}
    (hg : ∀ u ∈ U, g u ∈ U) : U.map (g : W →ₗ[ZMod 2] W) = U := by
  have hle : U.map (g : W →ₗ[ZMod 2] W) ≤ U := by
    rw [Submodule.map_le_iff_le_comap]
    exact fun u hu => hg u hu
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact (LinearEquiv.finrank_eq (g.submoduleMap U)).symm

private noncomputable def w172Restrict {U : Submodule (ZMod 2) W} {g : LGL 2 W}
    (hg : ∀ u ∈ U, g u ∈ U) : LGL 2 ↥U :=
  LinearEquiv.ofSubmodules g U U (w172_map_eq_self hg)

@[simp] private lemma w172Restrict_apply {U : Submodule (ZMod 2) W} {g : LGL 2 W}
    (hg : ∀ u ∈ U, g u ∈ U) (u : ↥U) :
    ((w172Restrict hg u : ↥U) : W) = g (u : W) :=
  LinearEquiv.ofSubmodules_apply g (w172_map_eq_self hg) u

private noncomputable def w172RestrictHom (Y : Subgroup (LGL 2 W)) (U : Submodule (ZMod 2) W)
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) : ↥Y →* LGL 2 ↥U where
  toFun g := w172Restrict (hUY g g.2)
  map_one' := by
    apply LinearEquiv.ext; intro u; apply Subtype.ext; simp
  map_mul' g h := by
    apply LinearEquiv.ext; intro u; apply Subtype.ext; simp

@[simp] private lemma w172RestrictHom_apply {Y : Subgroup (LGL 2 W)}
    {U : Submodule (ZMod 2) W} (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) (g : ↥Y) (u : ↥U) :
    ((w172RestrictHom Y U hUY g) u : W) = (g : LGL 2 W) (u : W) :=
  w172Restrict_apply (hUY g g.2) u

private lemma w172_commutatorElement_mul {G Q : Type} [Group G] [Group Q] (ρ : G →* Q)
    {A : Subgroup Q} (hAc : ∀ a ∈ A, ∀ q ∈ ρ.range, a * q = q * a)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {qc : Q}
    (hmem : ∀ g : G, ⁅ρ g, qc⁆ ∈ A) (a b : G) :
    ⁅ρ (a * b), qc⁆ = ⁅ρ a, qc⁆ * ⁅ρ b, qc⁆ := by
  have hB : ∀ q ∈ ρ.range, ⁅ρ b, qc⁆ * q = q * ⁅ρ b, qc⁆ := hAc _ (hmem b)
  have hbc : ρ b * qc * (ρ b)⁻¹ = ⁅ρ b, qc⁆ * qc := by
    rw [commutatorElement_def]; group
  have hcomm : ⁅ρ b, qc⁆ * ⁅ρ a, qc⁆ = ⁅ρ a, qc⁆ * ⁅ρ b, qc⁆ :=
    hAab _ (hmem b) _ (hmem a)
  calc ⁅ρ (a * b), qc⁆ = ρ a * (ρ b * qc * (ρ b)⁻¹) * (ρ a)⁻¹ * qc⁻¹ := by
        rw [map_mul, commutatorElement_def]; group
    _ = ρ a * (⁅ρ b, qc⁆ * qc) * (ρ a)⁻¹ * qc⁻¹ := by rw [hbc]
    _ = ⁅ρ b, qc⁆ * ⁅ρ a, qc⁆ := by
        conv_rhs => rw [commutatorElement_def]
        have h := hB (ρ a) (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
        calc ρ a * (⁅ρ b, qc⁆ * qc) * (ρ a)⁻¹ * qc⁻¹
            = (ρ a * ⁅ρ b, qc⁆) * qc * (ρ a)⁻¹ * qc⁻¹ := by group
          _ = (⁅ρ b, qc⁆ * ρ a) * qc * (ρ a)⁻¹ * qc⁻¹ := by rw [← h]
          _ = ⁅ρ b, qc⁆ * (ρ a * qc * (ρ a)⁻¹ * qc⁻¹) := by group
    _ = ⁅ρ a, qc⁆ * ⁅ρ b, qc⁆ := hcomm

private noncomputable def w172CommutatorHom {G Q : Type} [Group G] [Group Q]
    (ρ : G →* Q) {A : Subgroup Q} (hAc : ∀ a ∈ A, ∀ q ∈ ρ.range, a * q = q * a)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {qc : Q}
    (hmem : ∀ g : G, ⁅ρ g, qc⁆ ∈ A) : G →* A where
  toFun g := ⟨⁅ρ g, qc⁆, hmem g⟩
  map_one' := by
    apply Subtype.ext
    show ⁅ρ 1, qc⁆ = (1 : Q)
    rw [commutatorElement_def, map_one]
    group
  map_mul' a b := by
    apply Subtype.ext
    exact w172_commutatorElement_mul ρ hAc hAab hmem a b

private def w172CenY (Y : Subgroup (LGL 2 W)) (U : Submodule (ZMod 2) W)
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) (c : LGL 2 W) : Subgroup (LGL 2 W) where
  carrier := {g | g ∈ Y ∧ ∀ u ∈ U, g (c u) = c (g u)}
  one_mem' := ⟨Y.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
    refine ⟨Y.mul_mem haY hbY, fun u hu => ?_⟩
    show a (b (c u)) = c (a (b u))
    rw [hb u hu, ha (b u) (hUY b hbY u hu)]
  inv_mem' := by
    rintro a ⟨haY, ha⟩
    refine ⟨Y.inv_mem haY, fun u hu => ?_⟩
    have hainv : a⁻¹ u ∈ U := w172_inv_mem (hUY a haY) u hu
    have h1 : a (c (a⁻¹ u)) = c u := by
      rw [ha (a⁻¹ u) hainv]
      exact congrArg c (a.apply_symm_apply u)
    calc a⁻¹ (c u) = a⁻¹ (a (c (a⁻¹ u))) := by rw [h1]
      _ = c (a⁻¹ u) := a.symm_apply_apply _

private def w172Y1 (Y : Subgroup (LGL 2 W)) (U : Submodule (ZMod 2) W)
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) (x y : LGL 2 W) : Subgroup (LGL 2 W) :=
  w172CenY Y U hUY x ⊓ w172CenY Y U hUY y

private lemma w172_index_cenY {p : ℕ} (hp : p.Prime) {Y : Subgroup (LGL 2 W)}
    (hY : ∀ y ∈ Y, y ^ p = 1) {U : Submodule (ZMod 2) W}
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) {z : LGL 2 W} (hzY : z ∈ Y)
    (hzc : ∀ y ∈ Y, ∀ u ∈ U, z (y u) = y (z u))
    (hfix : ∀ u ∈ U, z u = u → u = 0) (hU : U ≠ ⊥)
    (hcls : ∀ y ∈ Y, ∀ x ∈ Y, ∃ i : ℕ, ∀ u ∈ U, (y * x * y⁻¹ * x⁻¹) u = (z ^ i) u)
    {H : Subgroup (LGL 2 W)} (hHY : H ≤ Y) {c : LGL 2 W} (hcY : c ∈ Y)
    {g0 : LGL 2 W} (hg0H : g0 ∈ H) (hg0 : ∃ u ∈ U, g0 (c u) ≠ c (g0 u)) :
    Nat.card H = p * Nat.card (w172CenY H U (fun y hy => hUY y (hHY hy)) c) := by
  classical
  let ρH := w172RestrictHom H U (fun y hy => hUY y (hHY hy))
  let ρ := w172RestrictHom Y U hUY
  let Zc : Subgroup (LGL 2 ↥U) := Subgroup.zpowers (ρ ⟨z, hzY⟩)
  have hZcCard : Nat.card Zc = p := by
    have hρz_ne : ρ ⟨z, hzY⟩ ≠ 1 := by
      intro h
      apply hU
      rw [eq_bot_iff]
      intro u hu
      have h1 : (ρ ⟨z, hzY⟩) ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [h]; rfl
      have h2 : z u = u := by
        have := congrArg (fun x : ↥U => (x : W)) h1
        simpa [ρ] using this
      exact hfix u hu h2
    have hzYp : (⟨z, hzY⟩ : ↥Y) ^ p = 1 := Subtype.ext (by simpa using hY z hzY)
    have hρzp : (ρ ⟨z, hzY⟩) ^ p = 1 := by rw [← map_pow, hzYp, map_one]
    have hord : orderOf (ρ ⟨z, hzY⟩) = p := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hρzp) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hρz_ne
      · exact h
    rw [Nat.card_zpowers, hord]
  have hAc : ∀ a ∈ Zc, ∀ q ∈ ρ.range, a * q = q * a := by
    intro a ha q hq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
    have hcomm : Commute (ρ ⟨z, hzY⟩) (ρ g) := by
      change (ρ ⟨z, hzY⟩) * (ρ g) = (ρ g) * (ρ ⟨z, hzY⟩)
      apply LinearEquiv.ext; intro u; apply Subtype.ext
      simpa [ρ, w172RestrictHom_apply] using hzc g g.2 (u : W) u.2
    rw [← hk]
    exact (hcomm.zpow_left k).eq
  have hAab : ∀ a ∈ Zc, ∀ b ∈ Zc, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hi, ← hj, ← zpow_add, add_comm, zpow_add]
  have hAcH : ∀ a ∈ Zc, ∀ q ∈ ρH.range, a * q = q * a := by
    intro a ha q hq
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
    exact hAc a ha (ρH g) (MonoidHom.mem_range.mpr ⟨⟨g.1, hHY g.2⟩, rfl⟩)
  have hmem : ∀ g : ↥H, ⁅ρH g, ρ ⟨c, hcY⟩⁆ ∈ Zc := by
    intro g
    obtain ⟨i, hi⟩ := hcls g.1 (hHY g.2) c hcY
    have h1 : ρ (⟨g.1, hHY g.2⟩ * ⟨c, hcY⟩ * ⟨g.1, hHY g.2⟩⁻¹ * ⟨c, hcY⟩⁻¹) =
        ⁅ρH g, ρ ⟨c, hcY⟩⁆ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, commutatorElement_def]
      rfl
    have h2 : ρ (⟨g.1, hHY g.2⟩ * ⟨c, hcY⟩ * ⟨g.1, hHY g.2⟩⁻¹ * ⟨c, hcY⟩⁻¹) =
        (ρ ⟨z, hzY⟩) ^ i := by
      rw [← map_pow]
      apply LinearEquiv.ext; intro u; apply Subtype.ext
      have hi' := hi (u : W) u.2
      simpa only [ρ, w172RestrictHom_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_pow] using hi'
    rw [← h1, h2]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(i : ℤ), by rw [zpow_natCast]⟩
  let φ := w172CommutatorHom ρH hAcH hAab (qc := ρ ⟨c, hcY⟩) hmem
  have hφg0 : φ ⟨g0, hg0H⟩ ≠ 1 := by
    intro h
    have hc1 : ⁅ρH ⟨g0, hg0H⟩, ρ ⟨c, hcY⟩⁆ = 1 := by
      have := congrArg Subtype.val h
      simpa [φ, w172CommutatorHom] using this
    have hcomm := commutatorElement_eq_one_iff_commute.mp hc1
    obtain ⟨u, hu, hne⟩ := hg0
    exact hne (Subtype.ext_iff.mp (congrArg (fun e : LGL 2 ↥U => e ⟨u, hu⟩) hcomm.eq))
  have hrange : Nat.card φ.range = p := by
    have hnt : Nontrivial φ.range := by
      refine ⟨⟨φ ⟨g0, hg0H⟩, ⟨⟨g0, hg0H⟩, rfl⟩⟩, ⟨1, φ.range.one_mem⟩, ?_⟩
      intro h
      exact hφg0 (Subtype.ext_iff.mp h)
    have h1 : 1 < Nat.card φ.range := Finite.one_lt_card_iff_nontrivial.mpr hnt
    have hdvd : Nat.card φ.range ∣ p := by
      have := Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)
      simpa [Subgroup.card_top, hZcCard] using this
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · omega
    · exact h
  have hkerEq : w172CenY H U (fun y hy => hUY y (hHY hy)) c = φ.ker.map H.subtype := by
    ext g
    constructor
    · intro hg
      refine ⟨⟨g, hg.1⟩, ?_, rfl⟩
      apply Subtype.ext
      apply commutatorElement_eq_one_iff_commute.mpr
      change (ρH ⟨g, hg.1⟩) * (ρ ⟨c, hcY⟩) = (ρ ⟨c, hcY⟩) * (ρH ⟨g, hg.1⟩)
      apply LinearEquiv.ext; intro u; apply Subtype.ext
      simpa [ρH, ρ, w172RestrictHom_apply] using hg.2 (u : W) u.2
    · rintro ⟨y, hy, rfl⟩
      change φ y = 1 at hy
      have hy1 : ⁅ρH y, ρ ⟨c, hcY⟩⁆ = 1 := by
        have := congrArg Subtype.val hy
        simpa [φ, w172CommutatorHom] using this
      have hcomm := commutatorElement_eq_one_iff_commute.mp hy1
      refine ⟨y.2, fun u hu => ?_⟩
      have := congrArg (fun e : LGL 2 ↥U => e ⟨u, hu⟩) hcomm.eq
      exact Subtype.ext_iff.mp this
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hkerCard : Nat.card φ.ker =
      Nat.card (w172CenY H U (fun y hy => hUY y (hHY hy)) c) := by
    rw [hkerEq, Subgroup.card_map_of_injective H.subtype_injective]
  rw [hrange, hkerCard, mul_comm] at hcard
  exact hcard.symm

private noncomputable def w172NormOf (A : LGL 2 W) (p : ℕ) : W →ₗ[ZMod 2] W :=
  ∑ k ∈ Finset.range p, ((A ^ k : LGL 2 W) : W →ₗ[ZMod 2] W)

private lemma w172_coe_pow (A : LGL 2 W) (n : ℕ) :
    ((A ^ n : LGL 2 W) : W →ₗ[ZMod 2] W) = (A : W →ₗ[ZMod 2] W) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change (A : W →ₗ[ZMod 2] W) * ((A ^ n : LGL 2 W) : W →ₗ[ZMod 2] W) =
      (A : W →ₗ[ZMod 2] W) * (A : W →ₗ[ZMod 2] W) ^ n
    rw [ih]

private lemma w172_coe_pow_apply (A : LGL 2 W) (n : ℕ) (u : W) :
    ((A : W →ₗ[ZMod 2] W) ^ n) u = (A ^ n) u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih]
    rfl

@[simp] private lemma w172NormOf_apply (A : LGL 2 W) (p : ℕ) (u : W) :
    w172NormOf A p u = ∑ k ∈ Finset.range p, (A ^ k) u := by
  rw [w172NormOf]
  induction (Finset.range p) using Finset.induction_on with
  | empty => rfl
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    change ((A ^ a : LGL 2 W) : W →ₗ[ZMod 2] W) u +
        (∑ k ∈ s, ((A ^ k : LGL 2 W) : W →ₗ[ZMod 2] W)) u = (A ^ a) u + ∑ k ∈ s, (A ^ k) u
    rw [ih]
    rfl

private lemma w172_commute_pow_apply {g h : LGL 2 W} {U : Submodule (ZMod 2) W}
    (hg : ∀ u ∈ U, g u ∈ U) (hcomm : ∀ u ∈ U, g (h u) = h (g u)) :
    ∀ (k : ℕ) (u : W), u ∈ U → h ((g ^ k) u) = (g ^ k) (h u) := by
  intro k
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    have hgu : (g ^ k) u ∈ U := w172_pow_mem hg k u hu
    rw [pow_succ']
    change h (g ((g ^ k) u)) = g ((g ^ k) (h u))
    rw [(hcomm ((g ^ k) u) hgu).symm, ih u hu]

private lemma w172_mul_pow_apply {g h : LGL 2 W} {U : Submodule (ZMod 2) W}
    (hg : ∀ u ∈ U, g u ∈ U) (hh : ∀ u ∈ U, h u ∈ U)
    (hcomm : ∀ u ∈ U, g (h u) = h (g u)) :
    ∀ (k : ℕ) (u : W), u ∈ U → ((g * h) ^ k) u = (g ^ k) ((h ^ k) u) := by
  intro k
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    have hhku : (h ^ k) u ∈ U := w172_pow_mem hh k u hu
    rw [pow_succ', pow_succ', pow_succ']
    change g (h (((g * h) ^ k) u)) = g ((g ^ k) (h ((h ^ k) u)))
    rw [ih u hu, w172_commute_pow_apply hg hcomm k ((h ^ k) u) hhku]

private lemma w172_norm_pow_apply {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hy : y ^ p = 1) (hz : z ^ p = 1) (hUy : ∀ u ∈ U, y u ∈ U)
    (hUz : ∀ u ∈ U, z u ∈ U) (hzy : ∀ u ∈ U, z (y u) = y (z u))
    (m : ℕ) : ∀ u ∈ U, ((y * z ^ (-(m : ℤ))) ^ p) u = u := by
  intro u hu
  have hzU : ∀ v ∈ U, (z ^ (-(m : ℤ)) : LGL 2 W) v ∈ U :=
    fun v hv => w172_zpow_mem hp hz hUz (-(m : ℤ)) v hv
  have hcomm : ∀ v ∈ U, y ((z ^ (-(m : ℤ)) : LGL 2 W) v) =
      (z ^ (-(m : ℤ)) : LGL 2 W) (y v) :=
    fun v hv => (w172_zpow_comm hp hz hUz hzy (-(m : ℤ)) v hv).symm
  rw [w172_mul_pow_apply hUy hzU hcomm p u hu, hy]
  change ((z ^ (-(m : ℤ)) : LGL 2 W) ^ p) u = u
  have hzmp : (z : LGL 2 W) ^ ((m : ℤ) * (p : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, zpow_natCast, zpow_natCast, hz, one_pow]
  have hzneg : (z : LGL 2 W) ^ ((-(m : ℤ)) * (p : ℤ)) = 1 := by
    rw [show (-(m : ℤ)) * (p : ℤ) = -((m : ℤ) * (p : ℤ)) by ring, zpow_neg, hzmp, inv_one]
  have hzp : ((z ^ (-(m : ℤ)) : LGL 2 W) ^ p) u = ((z : LGL 2 W) ^ ((-(m : ℤ)) * (p : ℤ))) u := by
    congr 1
    rw [← zpow_natCast, ← zpow_mul]
  rw [hzp, hzneg]; rfl

private lemma w172NormOf_fixed {U : Submodule (ZMod 2) W} {A : LGL 2 W} {p : ℕ}
    (hAU : ∀ u ∈ U, A u ∈ U) (hAp : ∀ u ∈ U, (A ^ p) u = u) :
    ∀ u ∈ U, A (w172NormOf A p u) = w172NormOf A p u := by
  intro u hu
  have hcoe : w172NormOf A p = ∑ k ∈ Finset.range p, (A : W →ₗ[ZMod 2] W) ^ k := by
    rw [w172NormOf]
    exact Finset.sum_congr rfl fun k _ => w172_coe_pow A k
  have hgeom : ((A : W →ₗ[ZMod 2] W) - 1) * w172NormOf A p =
      (A : W →ₗ[ZMod 2] W) ^ p - 1 := by
    rw [hcoe]
    exact mul_geom_sum (A : W →ₗ[ZMod 2] W) p
  have h0 : (A : W →ₗ[ZMod 2] W) (w172NormOf A p u) - w172NormOf A p u = 0 := by
    have h1 := congrArg (fun f : W →ₗ[ZMod 2] W => f u) hgeom
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at h1
    rw [w172_coe_pow_apply A p u, hAp u hu, sub_self] at h1
    exact h1
  exact sub_eq_zero.mp h0

private lemma w172Norm_eig {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hy : y ^ p = 1) (hz : z ^ p = 1) (hUy : ∀ u ∈ U, y u ∈ U)
    (hUz : ∀ u ∈ U, z u ∈ U) (hzy : ∀ u ∈ U, z (y u) = y (z u)) (m : ℕ)
    {u : W} (hu : u ∈ U) :
    w172NormOf (y * z ^ (-(m : ℤ))) p u ∈ w172Eig U y z (m : ℤ) := by
  have hzU : ∀ v ∈ U, (z ^ (-(m : ℤ)) : LGL 2 W) v ∈ U :=
    fun v hv => w172_zpow_mem hp hz hUz (-(m : ℤ)) v hv
  have hAU : ∀ v ∈ U, (y * z ^ (-(m : ℤ)) : LGL 2 W) v ∈ U :=
    fun v hv => hUy _ (hzU v hv)
  have hfixA := w172NormOf_fixed hAU (w172_norm_pow_apply hp hy hz hUy hUz hzy m) u hu
  have hTU : w172NormOf (y * z ^ (-(m : ℤ))) p u ∈ U := by
    rw [w172NormOf_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact w172_pow_mem hAU k u hu
  rw [w172_mem_eig]
  refine ⟨hTU, ?_⟩
  have hfixA' : y ((z ^ (-(m : ℤ)) : LGL 2 W) (w172NormOf (y * z ^ (-(m : ℤ))) p u)) =
      w172NormOf (y * z ^ (-(m : ℤ))) p u := hfixA
  have h3 := congrArg (fun w => (z ^ (m : ℤ) : LGL 2 W) w) hfixA'
  rw [w172_zpow_comm hp hz hUz hzy (m : ℤ) _
    (w172_zpow_mem hp hz hUz (-(m : ℤ)) _ hTU)] at h3
  simpa [← LinearEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero] using h3

private lemma w172_zpow_pow_apply {U : Submodule (ZMod 2) W} {z : LGL 2 W} {p : ℕ}
    (hz : z ^ p = 1) (k : ℕ) : ∀ u ∈ U, ((z ^ (-(k : ℤ)) : LGL 2 W) ^ p) u = u := by
  intro u _
  rw [← zpow_natCast, ← zpow_mul]
  have hzmp : (z : LGL 2 W) ^ ((k : ℤ) * (p : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, zpow_natCast, zpow_natCast, hz, one_pow]
  have hzneg : (z : LGL 2 W) ^ ((-(k : ℤ)) * (p : ℤ)) = 1 := by
    rw [show (-(k : ℤ)) * (p : ℤ) = -((k : ℤ) * (p : ℤ)) by ring, zpow_neg, hzmp, inv_one]
  rw [hzneg]; rfl

private lemma w172_sum_norm {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hUy : ∀ u ∈ U, y u ∈ U) (hUz : ∀ u ∈ U, z u ∈ U)
    (hzy : ∀ u ∈ U, z (y u) = y (z u)) (hfix : ∀ u ∈ U, z u = u → u = 0)
    {u : W} (hu : u ∈ U) :
    ∑ m ∈ Finset.range p, w172NormOf (y * z ^ (-(m : ℤ))) p u = u := by
  have hzU : ∀ (m : ℕ) (v : W), v ∈ U → (z ^ (-(m : ℤ)) : LGL 2 W) v ∈ U :=
    fun m v hv => w172_zpow_mem hp hz hUz (-(m : ℤ)) v hv
  have hstep : ∀ k ∈ Finset.range p,
      (∑ m ∈ Finset.range p, ((y * z ^ (-(m : ℤ))) ^ k) u) =
        (y ^ k) (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ k) u) := by
    intro k _
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact w172_mul_pow_apply hUy (hzU m) (fun v hv =>
      (w172_zpow_comm hp hz hUz hzy (-(m : ℤ)) v hv).symm) k u hu
  have hzero : ∀ k ∈ Finset.range p, k ≠ 0 →
      (y ^ k) (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ k) u) = 0 := by
    intro k hk hk0
    have hklt : k < p := Finset.mem_range.mp hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkndvd : ¬ p ∣ k := fun h => by
      have := Nat.le_of_dvd hkpos h
      omega
    have hv : (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ k) u) =
        w172NormOf (z ^ (-(k : ℤ))) p u := by
      rw [w172NormOf_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      congr 1; ring
    have hw := w172NormOf_fixed (hzU k) (w172_zpow_pow_apply hz k) u hu
    have hzk : (z ^ (k : ℤ) : LGL 2 W) (w172NormOf (z ^ (-(k : ℤ))) p u) =
        w172NormOf (z ^ (-(k : ℤ))) p u := by
      calc (z ^ (k : ℤ) : LGL 2 W) (w172NormOf (z ^ (-(k : ℤ))) p u)
          = (z ^ (k : ℤ) : LGL 2 W) ((z ^ (-(k : ℤ)) : LGL 2 W)
              (w172NormOf (z ^ (-(k : ℤ))) p u)) := by rw [hw]
        _ = ((z ^ (k : ℤ) : LGL 2 W) * (z ^ (-(k : ℤ)) : LGL 2 W))
              (w172NormOf (z ^ (-(k : ℤ))) p u) := by rw [LinearEquiv.mul_apply]
        _ = w172NormOf (z ^ (-(k : ℤ))) p u := by
            rw [show (z ^ (k : ℤ) : LGL 2 W) * (z ^ (-(k : ℤ)) : LGL 2 W) = 1 by
              rw [← zpow_add, add_neg_cancel, zpow_zero]]
            rfl
    have hTU : w172NormOf (z ^ (-(k : ℤ))) p u ∈ U := by
      rw [w172NormOf_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact w172_pow_mem (hzU k) j u hu
    rw [hv]
    have hzero' : w172NormOf (z ^ (-(k : ℤ))) p u = 0 :=
      w172_eig_fix_eq_zero hp hz hfix (k := (k : ℤ))
        (by exact_mod_cast hkndvd) hTU hzk
    rw [hzero', map_zero]
  calc ∑ m ∈ Finset.range p, w172NormOf (y * z ^ (-(m : ℤ))) p u
      = ∑ m ∈ Finset.range p, ∑ k ∈ Finset.range p, ((y * z ^ (-(m : ℤ))) ^ k) u := by
        simp only [w172NormOf_apply]
    _ = ∑ k ∈ Finset.range p, (y ^ k) (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ k) u) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl hstep
    _ = u := by
        have h0 : (y ^ 0)
            (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ 0) u) = u := by
          rw [pow_zero]
          change (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ 0) u) = u
          rw [show (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ 0) u) =
              ∑ _m ∈ Finset.range p, u by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [pow_zero]; rfl]
          rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul (ZMod 2),
            ZMod.natCast_eq_one_iff_odd.mpr (hp.odd_of_ne_two hp2), one_smul]
        have hsum : (∑ k ∈ Finset.range p,
            (y ^ k) (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ k) u)) =
            (y ^ 0) (∑ m ∈ Finset.range p, ((z ^ (-(m : ℤ))) ^ 0) u) :=
          Finset.sum_eq_single 0 (fun k hk hk0 => hzero k hk hk0)
            (fun h => absurd (Finset.mem_range.mpr hp.pos) h)
        rw [hsum, h0]

private lemma w172_iSup_eig_eq_top {U : Submodule (ZMod 2) W} {y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hUy : ∀ u ∈ U, y u ∈ U) (hUz : ∀ u ∈ U, z u ∈ U)
    (hzy : ∀ u ∈ U, z (y u) = y (z u)) (hfix : ∀ u ∈ U, z u = u → u = 0) :
    (⨆ m : Fin p, w172Eig U y z (m : ℤ)) = U := by
  apply le_antisymm
  · exact iSup_le fun m => inf_le_left
  · intro u hu
    rw [← w172_sum_norm hp hp2 hy hz hUy hUz hzy hfix hu]
    refine Submodule.sum_mem _ fun m hm => ?_
    exact Submodule.mem_iSup_of_mem ⟨m, Finset.mem_range.mp hm⟩
      (w172Norm_eig hp hy hz hUy hUz hzy m hu)

private lemma w172_eq_or_eq_of_relIndex_prime {G : Type*} [Group G] {A B C : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A.relIndex C = p) :
    B = A ∨ B = C := by
  have h := Subgroup.relIndex_mul_relIndex (H := A) (K := B) (L := C) hAB hBC
  rw [hAC] at h
  have hdvd : A.relIndex B ∣ p := ⟨B.relIndex C, h.symm⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAB
  · right
    rw [h1] at h
    have h2 : B.relIndex C = 1 := by
      have hh : p * B.relIndex C = p * 1 := by rw [h, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hp.pos hh
    exact le_antisymm hBC (Subgroup.relIndex_eq_one.mp h2)

private lemma w172_eig_zero_finrank {U : Submodule (ZMod 2) W} {x y z : LGL 2 W} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hUx : ∀ u ∈ U, x u ∈ U) (hUy : ∀ u ∈ U, y u ∈ U) (hUz : ∀ u ∈ U, z u ∈ U)
    (hzx : ∀ u ∈ U, z (x u) = x (z u)) (hzy : ∀ u ∈ U, z (y u) = y (z u))
    (hfix : ∀ u ∈ U, z u = u → u = 0) {i : ℕ} (hpi : ¬ p ∣ i)
    (hxy : ∀ u ∈ U, x (y u) = (z ^ i) (y (x u))) :
    Module.finrank (ZMod 2) ↥U = p * Module.finrank (ZMod 2) ↥(w172Eig U y z 0) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let E' : Fin p → Submodule (ZMod 2) W := fun m => w172Eig U y z (m : ℤ)
  have hUeq : (⨆ m : Fin p, E' m) = U := w172_iSup_eig_eq_top hp hp2 hy hz hUy hUz hzy hfix
  have hIndep : iSupIndep E' := w172_eig_indep hp hz hUy hUz hzy hfix
  have hSum := w172_eig_finrank_sum hIndep (Finset.univ : Finset (Fin p))
    (Finset.univ : Finset (Fin p)) Finset.Subset.rfl
  have hi' : ¬ (p : ℤ) ∣ (i : ℤ) := fun h => hpi (Int.natCast_dvd_natCast.mp h)
  have hxy' : ∀ u ∈ U, x (y u) = (z ^ (i : ℤ)) (y (x u)) := by
    intro u hu; rw [hxy u hu, zpow_natCast]
  have hdim : ∀ m : Fin p, Module.finrank (ZMod 2) ↥(E' m) =
      Module.finrank (ZMod 2) ↥(w172Eig U y z 0) := by
    intro m
    have := w172_eig_dim_eq hp hUx hUy hUz hz hzx hzy hi' hxy' (m : ℤ)
    simpa [E'] using this
  have hdim0 : ∀ m : Fin p, Module.finrank (ZMod 2) ↥(E' m) =
      Module.finrank (ZMod 2) ↥(E' 0) := fun m => (hdim m).trans (hdim 0).symm
  have hcard : ∑ m : Fin p, Module.finrank (ZMod 2) ↥(E' m) =
      p * Module.finrank (ZMod 2) ↥(E' 0) := by
    rw [Finset.sum_congr rfl (fun m _ => hdim0 m), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    simp [Nat.nsmul_eq_mul]
  have hsup : Finset.univ.sup E' = ⨆ m : Fin p, E' m := by
    rw [Finset.sup_eq_iSup]; simp
  have hE0 : E' 0 = w172Eig U y z 0 := rfl
  calc Module.finrank (ZMod 2) ↥U
      = Module.finrank (ZMod 2) ↥(⨆ m : Fin p, E' m) := by rw [hUeq]
    _ = Module.finrank (ZMod 2) ↥(Finset.univ.sup E') := by rw [hsup]
    _ = ∑ m : Fin p, Module.finrank (ZMod 2) ↥(E' m) := hSum
    _ = p * Module.finrank (ZMod 2) ↥(E' 0) := hcard
    _ = p * Module.finrank (ZMod 2) ↥(w172Eig U y z 0) := by rw [hE0]

theorem w172_heis_dim {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup (LGL 2 W)}
    (hY : ∀ y ∈ Y, y ^ p = 1) {U : Submodule (ZMod 2) W} (hU : U ≠ ⊥)
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) {z : LGL 2 W} (hzY : z ∈ Y)
    (hzc : ∀ y ∈ Y, ∀ u ∈ U, z (y u) = y (z u)) (hfix : ∀ u ∈ U, z u = u → u = 0)
    (hcls : ∀ y ∈ Y, ∀ x ∈ Y, ∃ i : ℕ, ∀ u ∈ U, (y * x * y⁻¹ * x⁻¹) u = (z ^ i) u) :
    ∃ w : ℕ, Nat.card Y = p ^ (2 * w) * Nat.card (w172Cent Y U hUY) ∧
      orderOf (2 : ZMod p) * p ^ w ≤ Module.finrank (ZMod 2) ↥U := by
  have H : ∀ n : ℕ, ∀ (Y : Subgroup (LGL 2 W)) (U : Submodule (ZMod 2) W),
      Nat.card Y = n → (hY : ∀ y ∈ Y, y ^ p = 1) → (hU : U ≠ ⊥) →
      (hUY : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U) → (hzY : z ∈ Y) →
      (hzc : ∀ y ∈ Y, ∀ u ∈ U, z (y u) = y (z u)) →
      (hfix : ∀ u ∈ U, z u = u → u = 0) →
      (hcls : ∀ y ∈ Y, ∀ x ∈ Y, ∃ i : ℕ, ∀ u ∈ U, (y * x * y⁻¹ * x⁻¹) u = (z ^ i) u) →
      ∃ w : ℕ, Nat.card Y = p ^ (2 * w) * Nat.card (w172Cent Y U hUY) ∧
        orderOf (2 : ZMod p) * p ^ w ≤ Module.finrank (ZMod 2) ↥U := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y U hcard hY hU hUY hzY hzc hfix hcls
      by_cases hcent : w172Cent Y U hUY = Y
      · refine ⟨0, ?_, ?_⟩
        · rw [pow_zero, one_mul, hcent]
        · rw [pow_zero, mul_one]
          have hz1 : z ^ p = 1 := hY z hzY
          have hdvd := w172_orderOf_two_dvd_finrank_sub hp hp2 hz1 U (hUY z hzY) hfix
          have hpos : 0 < Module.finrank (ZMod 2) ↥U := by
            rw [Nat.pos_iff_ne_zero]
            intro h0
            exact hU (Submodule.finrank_eq_zero.mp h0)
          exact Nat.le_of_dvd hpos hdvd
      · have hYle : w172Cent Y U hUY ≤ Y := fun g hg => hg.1
        have hlt : ¬ Y ≤ w172Cent Y U hUY := fun h => hcent (le_antisymm hYle h)
        obtain ⟨y, hyY, hyC⟩ := Set.not_subset.mp hlt
        obtain ⟨x, hxY, i, hpi, hxy, u0, hu0U, hu0ne⟩ :=
          w172_heis_pair hp hY hUY hzY hzc hcls hyY hyC
        have hz1 : z ^ p = 1 := hY z hzY
        have hUx : ∀ u ∈ U, x u ∈ U := hUY x hxY
        have hUy : ∀ u ∈ U, y u ∈ U := hUY y hyY
        have hUz : ∀ u ∈ U, z u ∈ U := hUY z hzY
        have hzx : ∀ u ∈ U, z (x u) = x (z u) := hzc x hxY
        have hzy : ∀ u ∈ U, z (y u) = y (z u) := hzc y hyY
        let U1 : Submodule (ZMod 2) W := w172Eig U y z 0
        have hdim : Module.finrank (ZMod 2) ↥U = p * Module.finrank (ZMod 2) ↥U1 := by
          exact w172_eig_zero_finrank hp hp2 (hY y hyY) hz1 hUx hUy hUz hzx hzy hfix hpi hxy
        have hU1 : U1 ≠ ⊥ := by
          intro hbot
          have h0 : Module.finrank (ZMod 2) ↥U1 = 0 := by rw [hbot, finrank_bot]
          rw [h0, mul_zero] at hdim
          have hpos : 0 < Module.finrank (ZMod 2) ↥U := by
            rw [Nat.pos_iff_ne_zero]
            intro hh
            exact hU (Submodule.finrank_eq_zero.mp hh)
          omega
        let Cx : Subgroup (LGL 2 W) := w172CenY Y U hUY x
        let Cy : Subgroup (LGL 2 W) := w172CenY Y U hUY y
        let Y1 : Subgroup (LGL 2 W) := w172Y1 Y U hUY x y
        have hCx_le : Cx ≤ Y := fun g hg => hg.1
        have hY1_le_Cx : Y1 ≤ Cx := inf_le_left
        have hY1_le_Y : Y1 ≤ Y := hY1_le_Cx.trans hCx_le
        have hzY1 : z ∈ Y1 := ⟨⟨hzY, fun u hu => hzx u hu⟩, hzY, fun u hu => hzy u hu⟩
        have hU1inv : ∀ g ∈ Y1, ∀ u ∈ U1, g u ∈ U1 := by
          intro g hg u hu
          obtain ⟨huU, huy⟩ := w172_mem_eig.mp hu
          refine w172_mem_eig.mpr ⟨hUY g (hY1_le_Y hg) u huU, ?_⟩
          have hgy : g (y u) = y (g u) := hg.2.2 u huU
          simpa [zpow_zero, huy] using hgy.symm
        have hY1_eq_cen : w172CenY Cx U (fun g hg => hUY g (hCx_le hg)) y = Y1 := by
          ext g
          constructor
          · rintro ⟨hgCx, hgy⟩
            exact ⟨hgCx, hCx_le hgCx, hgy⟩
          · rintro ⟨hgCx, hgy⟩
            exact ⟨hgCx, hgy.2⟩
        have hcardCx : Nat.card Y = p * Nat.card Cx :=
          w172_index_cenY hp hY hUY hzY hzc hfix hU hcls le_rfl hxY hyY
            ⟨u0, hu0U, hu0ne⟩
        have hcardY1 : Nat.card Cx = p * Nat.card Y1 := by
          have h := w172_index_cenY hp hY hUY hzY hzc hfix hU hcls hCx_le hyY
            (g0 := x) ⟨hxY, fun u hu => rfl⟩ ⟨u0, hu0U, fun hh => hu0ne hh.symm⟩
          rwa [hY1_eq_cen] at h
        have hcardY : Nat.card Y = p ^ 2 * Nat.card Y1 := by
          rw [hcardCx, hcardY1, pow_two, mul_assoc]
        have hCxRel : Cx.relIndex Y = p := by
          have h := Subgroup.relIndex_mul_card (H := Cx) (K := Y)
          rw [inf_eq_left.mpr hCx_le, hcardCx] at h
          exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
        have hY1Rel : Y1.relIndex Cx = p := by
          have h := Subgroup.relIndex_mul_card (H := Y1) (K := Cx)
          rw [inf_eq_left.mpr hY1_le_Cx, hcardY1] at h
          exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
        have hxCy : x ∉ Cy := by
          intro hxCy'
          have hcomm : x (y u0) = y (x u0) := hxCy'.2 u0 hu0U
          rw [hxy u0 hu0U] at hcomm
          have hyx0 : y (x u0) = 0 :=
            w172_eig_fix_eq_zero hp hz1 hfix (k := (i : ℤ))
              (by exact_mod_cast hpi) (hUy (x u0) (hUx u0 hu0U)) hcomm
          have hzero : x (y u0) = 0 := by rw [hxy u0 hu0U, hyx0, map_zero]
          exact hu0ne (hzero.trans hyx0.symm).symm
        have hyCx : y ∉ Cx := fun hyCx' => hu0ne (hyCx'.2 u0 hu0U)
        have hcenteq : w172Cent Y1 U1 hU1inv = w172Cent Y U hUY := by
          apply le_antisymm
          · intro g hg
            have hgY1 : g ∈ Y1 := hg.1
            have hgcomm : ∀ h ∈ Y1, ∀ u ∈ U1, g (h u) = h (g u) := hg.2
            have hS1 : Y1 ≤ w172CenY Y U hUY g := by
              intro h hh
              refine ⟨hY1_le_Y hh, ?_⟩
              obtain ⟨e, he⟩ := hcls g (hY1_le_Y hgY1) h (hY1_le_Y hh)
              have htriv : ∀ u ∈ U1, ((z : LGL 2 W) ^ e) u = u := by
                intro u hu
                have huU : u ∈ U := (w172_mem_eig.mp hu).1
                have hgu : g⁻¹ (h⁻¹ u) ∈ U1 :=
                  hU1inv g⁻¹ (Y1.inv_mem hgY1) _ (hU1inv h⁻¹ (Y1.inv_mem hh) u hu)
                have hcommgh : g (h (g⁻¹ (h⁻¹ u))) = h (g (g⁻¹ (h⁻¹ u))) :=
                  hgcomm h hh (g⁻¹ (h⁻¹ u)) hgu
                have hval : (g * h * g⁻¹ * h⁻¹) u = u := by
                  change g (h (g⁻¹ (h⁻¹ u))) = u
                  rw [hcommgh]
                  exact (congrArg h (g.apply_symm_apply (h⁻¹ u))).trans
                    (h.apply_symm_apply u)
                rw [← he u huU]
                exact hval
              have hpe : p ∣ e := by
                by_contra hpe
                obtain ⟨v, hvU1, hv0⟩ := (Submodule.ne_bot_iff U1).1 hU1
                refine hv0 (w172_eig_fix_eq_zero hp hz1 hfix (k := (e : ℤ))
                  (by exact_mod_cast hpe) (w172_mem_eig.mp hvU1).1 ?_)
                rw [zpow_natCast]
                exact htriv v hvU1
              have hze : (z : LGL 2 W) ^ e = 1 := by
                obtain ⟨t, ht⟩ := hpe
                rw [ht, pow_mul, hz1, one_pow]
              intro u hu
              have h1 : (g * h * g⁻¹ * h⁻¹) (h (g u)) = h (g u) := by
                rw [he (h (g u)) (hUY h (hY1_le_Y hh) (g u) (hUY g (hY1_le_Y hgY1) u hu)), hze]
                rfl
              have h2 : g (h u) = h (g u) := by
                simpa [LinearEquiv.mul_apply, h.apply_symm_apply, g.apply_symm_apply] using h1
              exact h2.symm
            have hxS : x ∈ w172CenY Y U hUY g ⊓ Cx := by
              refine ⟨⟨hxY, fun u hu => ?_⟩, ⟨hxY, fun u hu => rfl⟩⟩
              exact (hgY1.1.2 u hu).symm
            have hxY1 : x ∉ Y1 := fun h => hxCy h.2
            have hle1 : Cx ≤ w172CenY Y U hUY g := by
              rcases w172_eq_or_eq_of_relIndex_prime hp (le_inf hS1 hY1_le_Cx) inf_le_right
                hY1Rel with h | h
              · exact absurd (h ▸ hxS) hxY1
              · exact (le_of_eq h.symm).trans inf_le_left
            have hyS : y ∈ w172CenY Y U hUY g :=
              ⟨hyY, fun u hu => (hgY1.2.2 u hu).symm⟩
            have hEqY : w172CenY Y U hUY g = Y := by
              rcases w172_eq_or_eq_of_relIndex_prime hp hle1 (fun h hh => hh.1) hCxRel with h | h
              · exact absurd (h ▸ hyS) hyCx
              · exact h
            refine ⟨hY1_le_Y hgY1, fun h hh u hu => ?_⟩
            exact ((hEqY.symm ▸ hh : h ∈ w172CenY Y U hUY g).2 u hu).symm
          · intro g hg
            refine ⟨⟨⟨hg.1, hg.2 x hxY⟩, hg.1, hg.2 y hyY⟩, ?_⟩
            intro h hh u hu
            exact hg.2 h (hY1_le_Y hh) u (w172_mem_eig.mp hu).1
        have hY1lt : Nat.card Y1 < n := by
          rw [← hcard, hcardY]
          have h2 : 1 < p ^ 2 := by nlinarith [hp.two_le]
          calc Nat.card Y1 = Nat.card Y1 * 1 := (mul_one _).symm
            _ < Nat.card Y1 * p ^ 2 := (Nat.mul_lt_mul_left Nat.card_pos).mpr h2
            _ = p ^ 2 * Nat.card Y1 := mul_comm _ _
        obtain ⟨w1, hw1card, hw1dim⟩ := ih (Nat.card Y1) hY1lt Y1 U1 rfl
          (fun g hg => hY g (hY1_le_Y hg)) hU1 hU1inv hzY1
          (fun g hg u hu => hzc g (hY1_le_Y hg) u (w172_mem_eig.mp hu).1)
          (fun u hu => hfix u (w172_mem_eig.mp hu).1)
          (fun g hg x hx => by
            obtain ⟨j, hj⟩ := hcls g (hY1_le_Y hg) x (hY1_le_Y hx)
            exact ⟨j, fun u hu => hj u (w172_mem_eig.mp hu).1⟩)
        refine ⟨w1 + 1, ?_, ?_⟩
        · have hpow : p ^ (2 * (w1 + 1)) = p ^ 2 * p ^ (2 * w1) := by
            rw [show 2 * (w1 + 1) = 2 + 2 * w1 by ring, pow_add]
          rw [hcardY, hw1card, hcenteq, hpow, mul_assoc]
        · have hstep : orderOf (2 : ZMod p) * p ^ (w1 + 1) =
              p * (orderOf (2 : ZMod p) * p ^ w1) := by
            rw [pow_succ]; ring
          rw [hstep]
          calc p * (orderOf (2 : ZMod p) * p ^ w1)
              ≤ p * Module.finrank (ZMod 2) ↥U1 := Nat.mul_le_mul_left p hw1dim
            _ = Module.finrank (ZMod 2) ↥U := hdim.symm
  exact H (Nat.card Y) Y U rfl hY hU hUY hzY hzc hfix hcls

end CFSG.LocalAnalysis.WeakClosure81

end
