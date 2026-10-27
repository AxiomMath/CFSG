module

public import CFSG.Quasithin.Vol2.Ch11SecO3CXb
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

variable {G : Type} [Group G] {W W' C : Subgroup G}

structure Roots (W W' C : Subgroup G) {K : Type} [Field K] (β : K) (wf wf' : K → G) : Prop where
  mem : ∀ c, wf c ∈ W
  mem' : ∀ d, wf' d ∈ W'
  add : ∀ c c', (wf c * wf c')⁻¹ * wf (c + c') ∈ W ⊓ C
  add' : ∀ d d', (wf' d * wf' d')⁻¹ * wf' (d + d') ∈ W' ⊓ C
  weylA : ∀ c d, c * d * β ^ 2 = 1 → ∀ a ∈ W ⊓ C,
    (wf c * wf' d * wf c) * a * (wf c * wf' d * wf c)⁻¹ ∈ W' ⊓ C
  weylB : ∀ c d, c * d * β ^ 2 = 1 → ∀ b ∈ W' ⊓ C,
    (wf c * wf' d * wf c) * b * (wf c * wf' d * wf c)⁻¹ ∈ W ⊓ C

variable [(dQ W W' C).Normal]

namespace Frame

variable (hF : Frame W W' C)
include hF

theorem act_eq_of_mem {g h : G} (hg : Norm W W' C g) (hh : Norm W W' C h)
    (hgh : g⁻¹ * h ∈ qQ W W' C) (v : QS W W' C) : act hh v = act hg v :=
  calc act hh v = act (norm_mul hg (hF.norm_Q hgh)) v := act_congr _ _ (by group) v
    _ = act hg (act (hF.norm_Q hgh) v) := act_mul _ _ v
    _ = act hg v := by rw [hF.act_Q hgh]

theorem qc_cm_W {w : G} (hw : w ∈ W) {b₁ b₂ : G} (hb₁ : b₁ ∈ W' ⊓ C) (hb₂ : b₂ ∈ W' ⊓ C)
    (h : qB W W' C b₁ hb₁ = qB W W' C b₂ hb₂) :
    qA W W' C (cm w b₁) (hF.comm_W_B hw hb₁) = qA W W' C (cm w b₂) (hF.comm_W_B hw hb₂) := by
  have h1 := hF.act_W_B hw hb₁
  have h2 := hF.act_W_B hw hb₂
  rw [h] at h1
  rw [h1] at h2
  exact mul_right_cancel h2

theorem qc_cm_W' {w : G} (hw : w ∈ W') {a₁ a₂ : G} (ha₁ : a₁ ∈ W ⊓ C) (ha₂ : a₂ ∈ W ⊓ C)
    (h : qA W W' C a₁ ha₁ = qA W W' C a₂ ha₂) :
    qB W W' C (cm w a₁) (hF.comm_W'_A hw ha₁) = qB W W' C (cm w a₂) (hF.comm_W'_A hw ha₂) := by
  have h1 := hF.act_W'_A hw ha₁
  have h2 := hF.act_W'_A hw ha₂
  rw [h] at h1
  rw [h1] at h2
  exact mul_right_cancel h2

theorem eq_of_mul_eq_one {x y : QS W W' C} (h : x * y = 1) : x = y := by
  have h2 := hF.sq_eq_one y
  calc x = x * (y * y) := by rw [h2, mul_one]
    _ = (x * y) * y := by rw [mul_assoc]
    _ = y := by rw [h, one_mul]

omit hF in
theorem qB_one : qB W W' C 1 (W' ⊓ C).one_mem = 1 :=
  (qc_eq_one_iff _).mpr ⟨W.one_mem, W'.one_mem⟩

omit hF in
theorem qA_one : qA W W' C 1 (W ⊓ C).one_mem = 1 :=
  (qc_eq_one_iff _).mpr ⟨W.one_mem, W'.one_mem⟩

end Frame

namespace Roots

variable {K : Type} [Field K] {β : K} {wf wf' : K → G} (hF : Frame W W' C)
  (hR : Roots W W' C β wf wf')
include hF hR

omit [(dQ W W' C).Normal] in
theorem norm_s (c d : K) : Norm W W' C (wf c * wf' d * wf c) :=
  norm_mul (norm_mul (hF.norm_W (hR.mem c)) (hF.norm_W' (hR.mem' d))) (hF.norm_W (hR.mem c))

theorem qc_cm_add (c c' : K) {b : G} (hb : b ∈ W' ⊓ C) :
    qA W W' C (cm (wf (c + c')) b) (hF.comm_W_B (hR.mem (c + c')) hb) =
      qA W W' C (cm (wf c) b) (hF.comm_W_B (hR.mem c) hb) *
        qA W W' C (cm (wf c') b) (hF.comm_W_B (hR.mem c') hb) := by
  have h1 := hF.act_eq_of_mem (norm_mul (hF.norm_W (hR.mem c)) (hF.norm_W (hR.mem c')))
    (hF.norm_W (hR.mem (c + c')))
    (Subgroup.mem_sup_left (hR.add c c')) (qB W W' C b hb)
  rw [act_mul (hF.norm_W (hR.mem c)) (hF.norm_W (hR.mem c')), hF.act_W_B (hR.mem c') hb,
    map_mul, hF.act_W_A (hR.mem c) (hF.comm_W_B (hR.mem c') hb), hF.act_W_B (hR.mem c) hb,
    hF.act_W_B (hR.mem (c + c')) hb] at h1
  generalize qA W W' C (cm (wf (c + c')) b) _ = X at h1 ⊢
  generalize qA W W' C (cm (wf c) b) _ = Y at h1 ⊢
  generalize qA W W' C (cm (wf c') b) _ = Z at h1 ⊢
  generalize qB W W' C b hb = P at h1
  have h2 : X * P = (Y * Z) * P := by rw [h1, ← mul_assoc, hF.comm Z Y]
  exact mul_right_cancel h2

theorem qc_cm_add' (d d' : K) {a : G} (ha : a ∈ W ⊓ C) :
    qB W W' C (cm (wf' (d + d')) a) (hF.comm_W'_A (hR.mem' (d + d')) ha) =
      qB W W' C (cm (wf' d) a) (hF.comm_W'_A (hR.mem' d) ha) *
        qB W W' C (cm (wf' d') a) (hF.comm_W'_A (hR.mem' d') ha) := by
  have h1 := hF.act_eq_of_mem (norm_mul (hF.norm_W' (hR.mem' d)) (hF.norm_W' (hR.mem' d')))
    (hF.norm_W' (hR.mem' (d + d')))
    (Subgroup.mem_sup_right (hR.add' d d')) (qA W W' C a ha)
  rw [act_mul (hF.norm_W' (hR.mem' d)) (hF.norm_W' (hR.mem' d')), hF.act_W'_A (hR.mem' d') ha,
    map_mul, hF.act_W'_B (hR.mem' d)
    (hF.comm_W'_A (hR.mem' d') ha), hF.act_W'_A (hR.mem' d) ha,
    hF.act_W'_A (hR.mem' (d + d')) ha] at h1
  generalize qB W W' C (cm (wf' (d + d')) a) _ = X at h1 ⊢
  generalize qB W W' C (cm (wf' d) a) _ = Y at h1 ⊢
  generalize qB W W' C (cm (wf' d') a) _ = Z at h1 ⊢
  generalize qA W W' C a ha = P at h1
  have h2 : X * P = (Y * Z) * P := by rw [h1, ← mul_assoc, hF.comm Z Y]
  exact mul_right_cancel h2

theorem act_s (c d : K) (v : QS W W' C) :
    act (hR.norm_s hF c d) v = act (hF.norm_W (hR.mem c))
      (act (hF.norm_W' (hR.mem' d)) (act (hF.norm_W (hR.mem c)) v)) := by
  rw [act_congr (hR.norm_s hF c d) (norm_mul (norm_mul (hF.norm_W (hR.mem c))
      (hF.norm_W' (hR.mem' d))) (hF.norm_W (hR.mem c))) rfl v,
    act_mul (norm_mul (hF.norm_W (hR.mem c)) (hF.norm_W' (hR.mem' d))) (hF.norm_W (hR.mem c)),
    act_mul (hF.norm_W (hR.mem c)) (hF.norm_W' (hR.mem' d))]

theorem weyl_B {c d : K} (hcd : c * d * β ^ 2 = 1) {b : G} (hb : b ∈ W' ⊓ C) :
    qB W W' C (cm (wf' d) (cm (wf c) b))
        (hF.comm_W'_A (hR.mem' d) (hF.comm_W_B (hR.mem c) hb)) = qB W W' C b hb ∧
      act (hR.norm_s hF c d) (qB W W' C b hb) =
        qA W W' C (cm (wf c) b) (hF.comm_W_B (hR.mem c) hb) := by
  have hα := hF.comm_W_B (hR.mem c) hb
  have hγ := hF.comm_W'_A (hR.mem' d) hα
  have hδ := hF.comm_W_B (hR.mem c) hγ
  have hs := hR.weylB c d hcd b hb
  have e1 : act (hR.norm_s hF c d) (qB W W' C b hb) =
      qA W W' C _ hs * qB W W' C 1 (W' ⊓ C).one_mem := by
    rw [Frame.qB_one, mul_one]
    rfl
  have e2 : act (hR.norm_s hF c d) (qB W W' C b hb) =
      qA W W' C _ hδ * qB W W' C _ ((W' ⊓ C).mul_mem hγ hb) := by
    rw [hR.act_s hF, hF.act_W_B (hR.mem c) hb, map_mul, hF.act_W'_A (hR.mem' d) hα,
      hF.act_W'_B (hR.mem' d) hb, map_mul, map_mul, hF.act_W_B (hR.mem c) hγ,
      hF.act_W_A (hR.mem c) hα, hF.act_W_B (hR.mem c) hb]
    rw [show qB W W' C _ ((W' ⊓ C).mul_mem hγ hb) = qB W W' C _ hγ * qB W W' C b hb from rfl]
    generalize qA W W' C (cm (wf c) (cm (wf' d) (cm (wf c) b))) _ = X
    generalize qB W W' C (cm (wf' d) (cm (wf c) b)) _ = Y
    generalize qA W W' C (cm (wf c) b) _ = Z
    generalize qB W W' C b hb = P
    have hZ := hF.sq_eq_one Z
    calc X * Y * Z * (Z * P) = X * Y * (Z * Z) * P := by simp only [mul_assoc]
      _ = X * (Y * P) := by rw [hZ, mul_one, mul_assoc]
  rw [e1] at e2
  obtain ⟨hA, hB⟩ := Frame.eq_of_mul_eq hs hδ (W' ⊓ C).one_mem ((W' ⊓ C).mul_mem hγ hb) e2
  have hγb : qB W W' C _ hγ = qB W W' C b hb := by
    have h1 : qB W W' C _ hγ * qB W W' C b hb = 1 := by
      rw [show qB W W' C _ hγ * qB W W' C b hb = qB W W' C _ ((W' ⊓ C).mul_mem hγ hb) from rfl,
        ← hB, Frame.qB_one]
    exact hF.eq_of_mul_eq_one h1
  refine ⟨hγb, ?_⟩
  rw [e1, Frame.qB_one, mul_one, hA]
  exact hF.qc_cm_W (hR.mem c) hγ hb hγb

theorem weyl_A {c d : K} (hcd : c * d * β ^ 2 = 1) {a : G} (ha : a ∈ W ⊓ C) :
    qA W W' C (cm (wf c) (cm (wf' d) a))
        (hF.comm_W_B (hR.mem c) (hF.comm_W'_A (hR.mem' d) ha)) = qA W W' C a ha ∧
      act (hR.norm_s hF c d) (qA W W' C a ha) =
        qB W W' C (cm (wf' d) a) (hF.comm_W'_A (hR.mem' d) ha) := by
  have hβ₁ := hF.comm_W'_A (hR.mem' d) ha
  have hδ := hF.comm_W_B (hR.mem c) hβ₁
  have hs := hR.weylA c d hcd a ha
  have e1 : act (hR.norm_s hF c d) (qA W W' C a ha) =
      qA W W' C 1 (W ⊓ C).one_mem * qB W W' C _ hs := by
    rw [Frame.qA_one, one_mul]
    rfl
  have e2 : act (hR.norm_s hF c d) (qA W W' C a ha) =
      qA W W' C _ ((W ⊓ C).mul_mem hδ ha) * qB W W' C _ hβ₁ := by
    rw [hR.act_s hF, hF.act_W_A (hR.mem c) ha, hF.act_W'_A (hR.mem' d) ha, map_mul,
      hF.act_W_B (hR.mem c) hβ₁, hF.act_W_A (hR.mem c) ha]
    rw [show qA W W' C _ ((W ⊓ C).mul_mem hδ ha) = qA W W' C _ hδ * qA W W' C a ha from rfl]
    generalize qA W W' C (cm (wf c) (cm (wf' d) a)) _ = X
    generalize qB W W' C (cm (wf' d) a) _ = Y
    generalize qA W W' C a ha = P
    rw [mul_assoc, hF.comm Y P, ← mul_assoc]
  rw [e1] at e2
  obtain ⟨hA, hB⟩ := Frame.eq_of_mul_eq (W ⊓ C).one_mem ((W ⊓ C).mul_mem hδ ha) hs hβ₁ e2
  have hδa : qA W W' C _ hδ = qA W W' C a ha := by
    have h1 : qA W W' C _ hδ * qA W W' C a ha = 1 := by
      rw [show qA W W' C _ hδ * qA W W' C a ha = qA W W' C _ ((W ⊓ C).mul_mem hδ ha) from rfl,
        ← hA, Frame.qA_one]
    exact hF.eq_of_mul_eq_one h1
  refine ⟨hδa, ?_⟩
  rw [e1, Frame.qA_one, one_mul, hB]

end Roots

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
