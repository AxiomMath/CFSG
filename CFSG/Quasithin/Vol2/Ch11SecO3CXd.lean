module

public import CFSG.Quasithin.Vol2.Ch11SecO3CXc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
public import Mathlib.Algebra.GroupWithZero.Units.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

variable {G : Type} [Group G] {W W' C : Subgroup G}

theorem fix_eq_one_of_two {M : Type*} [Group M] (hcomm : ∀ u v : M, u * v = v * u)
    (hsq : ∀ u : M, u * u = 1) (P Z X : M →* M) (hX : ∀ v, X v = P (Z v))
    (hZP : ∀ v, Z (P v) = P (Z v)) {k : ℕ} (hk : ∀ v, (⇑Z)^[2 ^ k] v = v)
    (hP : ∀ v, P v = v → v = 1) (v : M) (hv : X v = v) : v = 1 := by
  set δ : M → M := fun u => Z u * u with hδ
  have hδ_mul : ∀ u w, δ (u * w) = δ u * δ w := fun u w => by
    simp only [hδ, map_mul]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, hcomm (Z w) u, mul_assoc]
  have hZiter : ∀ n u w, (⇑Z)^[n] (u * w) = (⇑Z)^[n] u * (⇑Z)^[n] w := fun n => by
    induction n with
    | zero => intro u w; rfl
    | succ n ih =>
      intro u w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, map_mul]
  have hpow : ∀ m u, δ^[2 ^ m] u = (⇑Z)^[2 ^ m] u * u := by
    intro m
    induction m with
    | zero => intro u; rfl
    | succ m ih =>
      intro u
      rw [pow_succ, mul_two, Function.iterate_add_apply, ih, ih, hZiter,
        ← Function.iterate_add_apply]
      simp only [mul_assoc]
      rw [← mul_assoc ((⇑Z)^[2 ^ m] u) ((⇑Z)^[2 ^ m] u) u, hsq, one_mul]
  have hXZ : ∀ u, X (Z u) = Z (X u) := fun u => by rw [hX, hX, hZP]
  have hδX : ∀ u, X u = u → X (δ u) = δ u := fun u hu => by
    simp only [hδ, map_mul, hXZ, hu]
  have hiterX : ∀ n u, X u = u → X (δ^[n] u) = δ^[n] u := fun n => by
    induction n with
    | zero => intro u hu; exact hu
    | succ n ih =>
      intro u hu
      rw [Function.iterate_succ_apply']
      exact hδX _ (ih u hu)
  by_contra hne
  have hex : ∃ n, δ^[n] v = 1 := ⟨2 ^ k, by rw [hpow, hk, hsq]⟩
  classical
  let n₀ := Nat.find hex
  have hn₀ : δ^[n₀] v = 1 := Nat.find_spec hex
  have hn₀pos : n₀ ≠ 0 := fun h0 => hne (by rw [← hn₀, h0]; rfl)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn₀pos
  have hm1 : δ^[m] v ≠ 1 := Nat.find_min hex (by omega)
  have hδm : δ (δ^[m] v) = 1 := by
    have h1 : δ^[m.succ] v = 1 := hm ▸ hn₀
    rwa [Function.iterate_succ_apply'] at h1
  set u := δ^[m] v
  have hZu : Z u = u := by
    have h1 : Z u * u = 1 := hδm
    calc Z u = Z u * (u * u) := by rw [hsq, mul_one]
      _ = (Z u * u) * u := by rw [mul_assoc]
      _ = u := by rw [h1, one_mul]
  have hXu : X u = u := hiterX m v hv
  apply hm1
  apply hP
  calc P u = P (Z u) := by rw [hZu]
    _ = X u := (hX u).symm
    _ = u := hXu

theorem dual_param {K : Type} [Field K] {β c : K} (hβ : β ≠ 0) (hc : c ≠ 0) :
    c * (c * β ^ 2)⁻¹ * β ^ 2 = 1 := by
  field_simp

variable [(dQ W W' C).Normal]

namespace Frame

variable (hF : Frame W W' C)
include hF

theorem qA_cm_eq_one {w : G} (hw : w ∈ W) {b : G} (hb : b ∈ W' ⊓ C) (h : qB W W' C b hb = 1) :
    qA W W' C (cm w b) (hF.comm_W_B hw hb) = 1 := by
  rw [hF.qc_cm_W hw hb (W' ⊓ C).one_mem (h.trans qB_one.symm)]
  exact (qc_eq_one_iff _).mpr (by simp [cm])

theorem qB_cm_eq_one {w : G} (hw : w ∈ W') {a : G} (ha : a ∈ W ⊓ C) (h : qA W W' C a ha = 1) :
    qB W W' C (cm w a) (hF.comm_W'_A hw ha) = 1 := by
  rw [hF.qc_cm_W' hw ha (W ⊓ C).one_mem (h.trans qA_one.symm)]
  exact (qc_eq_one_iff _).mpr (by simp [cm])

end Frame

namespace Roots

variable {K : Type} [Field K] {β : K} {wf wf' : K → G} (hF : Frame W W' C)
  (hR : Roots W W' C β wf wf')
include hF hR

theorem qc_cm_add_of {c c₁ c₂ : K} (h : c = c₁ + c₂) {b : G} (hb : b ∈ W' ⊓ C) :
    qA W W' C (cm (wf c) b) (hF.comm_W_B (hR.mem c) hb) =
      qA W W' C (cm (wf c₁) b) (hF.comm_W_B (hR.mem c₁) hb) *
        qA W W' C (cm (wf c₂) b) (hF.comm_W_B (hR.mem c₂) hb) := by
  subst h
  exact hR.qc_cm_add hF c₁ c₂ hb

theorem qc_cm_add'_of {d d₁ d₂ : K} (h : d = d₁ + d₂) {a : G} (ha : a ∈ W ⊓ C) :
    qB W W' C (cm (wf' d) a) (hF.comm_W'_A (hR.mem' d) ha) =
      qB W W' C (cm (wf' d₁) a) (hF.comm_W'_A (hR.mem' d₁) ha) *
        qB W W' C (cm (wf' d₂) a) (hF.comm_W'_A (hR.mem' d₂) ha) := by
  subst h
  exact hR.qc_cm_add' hF d₁ d₂ ha

theorem qB_eq_one_of (hβ : β ≠ 0) {e : K} (he : e ≠ 0) {b : G} (hb : b ∈ W' ⊓ C)
    (h : qA W W' C (cm (wf e) b) (hF.comm_W_B (hR.mem e) hb) = 1) : qB W W' C b hb = 1 := by
  rw [← (hR.weyl_B hF (dual_param hβ he) hb).1]
  exact hF.qB_cm_eq_one (hR.mem' _) _ h

theorem qA_eq_one_of (hβ : β ≠ 0) {e : K} (he : e ≠ 0) {a : G} (ha : a ∈ W ⊓ C)
    (h : qB W W' C (cm (wf' e) a) (hF.comm_W'_A (hR.mem' e) ha) = 1) : qA W W' C a ha = 1 := by
  have hd : (e * β ^ 2)⁻¹ * e * β ^ 2 = 1 := by field_simp
  rw [← (hR.weyl_A hF hd ha).1]
  exact hF.qA_cm_eq_one (hR.mem _) _ h

theorem fix_eq_one (hβ : β ≠ 0) {c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0) (hcc : c ≠ c')
    (v : QS W W' C)
    (hv : act (norm_mul (hR.norm_s hF c' (c' * β ^ 2)⁻¹) (hR.norm_s hF c (c * β ^ 2)⁻¹)) v = v) :
    v = 1 := by
  have hcd := dual_param hβ hc
  have hcd' := dual_param hβ hc'
  obtain ⟨a, ha, b, hb, rfl⟩ := hF.exists_qc_eq v
  have hα := hF.comm_W_B (hR.mem c) hb
  have hβ₁ := hF.comm_W'_A (hR.mem' (c * β ^ 2)⁻¹) ha
  rw [act_mul (hR.norm_s hF c' (c' * β ^ 2)⁻¹) (hR.norm_s hF c (c * β ^ 2)⁻¹), map_mul, map_mul,
    (hR.weyl_A hF hcd ha).2, (hR.weyl_B hF hcd hb).2, (hR.weyl_B hF hcd' hβ₁).2,
    (hR.weyl_A hF hcd' hα).2] at hv
  obtain ⟨hA, hB⟩ := Frame.eq_of_mul_eq _ ha _ hb hv
  have hdd : (c * β ^ 2)⁻¹ ≠ (c' * β ^ 2)⁻¹ := by
    intro h
    exact hcc (mul_right_cancel₀ (pow_ne_zero 2 hβ) (inv_inj.mp h))
  have hB1 : qB W W' C (cm (wf' ((c' * β ^ 2)⁻¹ - (c * β ^ 2)⁻¹)) (cm (wf c) b))
      (hF.comm_W'_A (hR.mem' _) hα) = 1 := by
    have h1 := hR.qc_cm_add'_of hF
      (show (c' * β ^ 2)⁻¹ = (c * β ^ 2)⁻¹ + ((c' * β ^ 2)⁻¹ - (c * β ^ 2)⁻¹) by ring) hα
    rw [hB, ← (hR.weyl_B hF hcd hb).1] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
  have hα1 := hR.qA_eq_one_of hF hβ (sub_ne_zero.mpr hdd.symm) hα hB1
  have hb1 : qB W W' C b hb = 1 := by
    rw [← (hR.weyl_B hF hcd hb).1]
    exact hF.qB_cm_eq_one (hR.mem' _) hα hα1
  have hA1 : qA W W' C (cm (wf (c' - c)) (cm (wf' (c * β ^ 2)⁻¹) a))
      (hF.comm_W_B (hR.mem _) hβ₁) = 1 := by
    have h1 := hR.qc_cm_add_of hF (show c' = c + (c' - c) by ring) hβ₁
    rw [hA, ← (hR.weyl_A hF hcd ha).1] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
  have hβ1 := hR.qB_eq_one_of hF hβ (sub_ne_zero.mpr (Ne.symm hcc)) hβ₁ hA1
  have ha1 : qA W W' C a ha = 1 := by
    rw [← (hR.weyl_A hF hcd ha).1]
    exact hF.qA_cm_eq_one (hR.mem c) hβ₁ hβ1
  rw [ha1, hb1, one_mul]

end Roots

omit [(dQ W W' C).Normal] in
theorem norm_one : Norm W W' C (1 : G) :=
  ⟨fun q hq => by simpa using hq, fun d hd => by simpa using hd⟩

omit [(dQ W W' C).Normal] in
theorem norm_pow {z : G} (hz : Norm W W' C z) : ∀ n : ℕ, Norm W W' C (z ^ n)
  | 0 => by rw [pow_zero]; exact norm_one
  | n + 1 => by rw [pow_succ]; exact norm_mul (norm_pow hz n) hz

theorem act_one (v : QS W W' C) : act (norm_one (W := W) (W' := W') (C := C)) v = v := by
  induction v using QuotientGroup.induction_on with
  | H q =>
    change act norm_one (qc (W := W) (W' := W') (C := C) q q.2) =
      qc (W := W) (W' := W') (C := C) q q.2
    rw [act_qc]
    congr 1
    group

theorem act_iterate {z : G} (hz : Norm W W' C z) (n : ℕ) (v : QS W W' C) :
    (⇑(act hz))^[n] v = act (norm_pow hz n) v := by
  induction n with
  | zero =>
    rw [Function.iterate_zero, id]
    exact ((act_congr (norm_pow hz 0) norm_one (pow_zero z) v).trans (act_one v)).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, act_congr (norm_pow hz (n + 1))
      (norm_mul hz (norm_pow hz n)) (by rw [pow_succ']) v, act_mul]

namespace Roots

variable {K : Type} [Field K] {β : K} {wf wf' : K → G} (hF : Frame W W' C)
  (hR : Roots W W' C β wf wf')
include hF hR

theorem act_comm_s {z : G} (hz : z ∈ C) (hzn : Norm W W' C z) (c d : K) (v : QS W W' C) :
    act hzn (act (hR.norm_s hF c d) v) = act (hR.norm_s hF c d) (act hzn v) := by
  rw [hR.act_s hF, hR.act_s hF, hF.act_comm_C_W hz hzn (hR.mem c),
    hF.act_comm_C_W' hz hzn (hR.mem' d), hF.act_comm_C_W hz hzn (hR.mem c)]

theorem mem_D_of_comm (hβ : β ≠ 0) {c c' : K} (hc : c ≠ 0) (hc' : c' ≠ 0) (hcc : c ≠ c')
    {x z : G} (hz : z ∈ C) (hzn : Norm W W' C z) {k : ℕ} (hzk : z ^ (2 ^ k) = 1)
    (hxz : x = (wf c' * wf' (c' * β ^ 2)⁻¹ * wf c') * (wf c * wf' (c * β ^ 2)⁻¹ * wf c) * z)
    (hxn : Norm W W' C x) {q : G} (hq : q ∈ qQ W W' C) (hxq : x * q * x⁻¹ = q) :
    q ∈ W ⊓ W' := by
  have hs' := hR.norm_s hF c' (c' * β ^ 2)⁻¹
  have hs := hR.norm_s hF c (c * β ^ 2)⁻¹
  have hfix := fix_eq_one_of_two hF.comm hF.sq_eq_one (act (norm_mul hs' hs)) (act hzn)
    (act hxn) (fun v => by rw [act_congr hxn (norm_mul (norm_mul hs' hs) hzn) hxz v,
      act_mul (norm_mul hs' hs) hzn])
    (fun v => by
      rw [act_mul hs' hs, act_mul hs' hs, hR.act_comm_s hF hz hzn c', hR.act_comm_s hF hz hzn c])
    (k := k) (fun v => by
      rw [act_iterate, act_congr (norm_pow hzn (2 ^ k)) norm_one hzk v, act_one])
    (fun v hv => hR.fix_eq_one hF hβ hc hc' hcc v hv) (qc (W := W) (W' := W') (C := C) q hq)
    (by rw [act_qc]; congr 1)
  exact (qc_eq_one_iff hq).mp hfix

end Roots

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
