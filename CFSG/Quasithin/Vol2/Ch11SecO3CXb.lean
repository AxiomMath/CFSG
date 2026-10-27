module

public import CFSG.Quasithin.Vol2.Ch11SecO3CXa
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

open scoped Pointwise

variable {G : Type} [Group G] {W W' C : Subgroup G}

theorem conj_mem_sup {H K M : Subgroup G} {g : G} (hH : ∀ h ∈ H, g * h * g⁻¹ ∈ M)
    (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ M) : ∀ x ∈ H ⊔ K, g * x * g⁻¹ ∈ M := by
  have hle : H ⊔ K ≤ M.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun h hh => hH h hh) (fun k hk => hK k hk)
  exact fun x hx => hle hx

theorem conj_mem_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {h : G} (hh : h ∈ H) : g * h * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg h).mp hh

theorem norm_of {g : G} (h1 : g ∈ Subgroup.normalizer (W : Set G))
    (h2 : g ∈ Subgroup.normalizer (W' : Set G)) (h3 : g ∈ Subgroup.normalizer (C : Set G)) :
    Norm W W' C g :=
  ⟨conj_mem_sup (fun _ ha => Subgroup.mem_sup_left ⟨conj_mem_of_mem_normalizer h1 ha.1,
      conj_mem_of_mem_normalizer h3 ha.2⟩)
    (fun _ hb => Subgroup.mem_sup_right ⟨conj_mem_of_mem_normalizer h2 hb.1,
      conj_mem_of_mem_normalizer h3 hb.2⟩),
    fun _ hd => ⟨conj_mem_of_mem_normalizer h1 hd.1, conj_mem_of_mem_normalizer h2 hd.2⟩⟩

namespace Frame

variable (hF : Frame W W' C)
include hF

theorem comm_W_B {w : G} (hw : w ∈ W) {b : G} (hb : b ∈ W' ⊓ C) :
    cm w b ∈ W ⊓ C := by
  refine ⟨?_, ?_⟩
  · have h1 : b * w⁻¹ * b⁻¹ ∈ W := conj_mem_of_mem_normalizer (hF.cW hb.2) (W.inv_mem hw)
    have h2 := W.mul_mem hw h1
    simpa [mul_assoc] using h2
  · have h1 : w * b * w⁻¹ ∈ C := conj_mem_of_mem_normalizer (hF.wC hw) hb.2
    exact C.mul_mem h1 (C.inv_mem hb.2)

theorem comm_W'_A {w : G} (hw : w ∈ W') {a : G} (ha : a ∈ W ⊓ C) :
    cm w a ∈ W' ⊓ C := by
  refine ⟨?_, ?_⟩
  · have h1 : a * w⁻¹ * a⁻¹ ∈ W' := conj_mem_of_mem_normalizer (hF.cW' ha.2) (W'.inv_mem hw)
    have h2 := W'.mul_mem hw h1
    simpa [mul_assoc] using h2
  · have h1 : w * a * w⁻¹ ∈ C := conj_mem_of_mem_normalizer (hF.w'C hw) ha.2
    exact C.mul_mem h1 (C.inv_mem ha.2)

theorem norm_W {w : G} (hw : w ∈ W) : Norm W W' C w := by
  refine ⟨conj_mem_sup (fun a ha => Subgroup.mem_sup_left ⟨?_, ?_⟩) (fun b hb => ?_),
    fun d hd => ⟨?_, ?_⟩⟩
  · exact W.mul_mem (W.mul_mem hw ha.1) (W.inv_mem hw)
  · exact conj_mem_of_mem_normalizer (hF.wC hw) ha.2
  · have : w * b * w⁻¹ = (w * b * w⁻¹ * b⁻¹) * b := by group
    rw [this]
    exact (qQ W W' C).mul_mem (Subgroup.mem_sup_left (hF.comm_W_B hw hb))
      (Subgroup.mem_sup_right hb)
  · exact W.mul_mem (W.mul_mem hw hd.1) (W.inv_mem hw)
  · have : w * d * w⁻¹ = (w * d * w⁻¹ * d⁻¹) * d := by group
    rw [this]
    exact W'.mul_mem (hF.ww w hw d hd.1) hd.2

theorem norm_W' {w : G} (hw : w ∈ W') : Norm W W' C w := by
  refine ⟨conj_mem_sup (fun a ha => ?_) (fun b hb => Subgroup.mem_sup_right ⟨?_, ?_⟩),
    fun d hd => ⟨?_, ?_⟩⟩
  · have : w * a * w⁻¹ = (w * a * w⁻¹ * a⁻¹) * a := by group
    rw [this]
    exact (qQ W W' C).mul_mem (Subgroup.mem_sup_right (hF.comm_W'_A hw ha))
      (Subgroup.mem_sup_left ha)
  · exact W'.mul_mem (W'.mul_mem hw hb.1) (W'.inv_mem hw)
  · exact conj_mem_of_mem_normalizer (hF.w'C hw) hb.2
  · have : w * d * w⁻¹ = (w * d * w⁻¹ * d⁻¹) * d := by group
    rw [this]
    exact W.mul_mem (hF.w'w' w hw d hd.2) hd.1
  · exact W'.mul_mem (W'.mul_mem hw hd.2) (W'.inv_mem hw)

theorem norm_Q {q : G} (hq : q ∈ qQ W W' C) : Norm W W' C q :=
  ⟨fun _ hp => (qQ W W' C).mul_mem ((qQ W W' C).mul_mem hq hp) ((qQ W W' C).inv_mem hq),
    fun _ hd => hF.conj_mem_D hq hd⟩

theorem a_le_normalizer_b : W ⊓ C ≤ Subgroup.normalizer ((W' ⊓ C : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have h1 := Subgroup.mem_normalizer_iff.mp (hF.cW' ha.2) b
  have h2 := Subgroup.mem_normalizer_iff.mp (hF.wC ha.1) b
  simp only [Subgroup.mem_inf]
  rw [h1, h2]

end Frame

section Act

variable [(dQ W W' C).Normal]

namespace Frame

variable (hF : Frame W W' C)
include hF

theorem act_Q {q : G} (hq : q ∈ qQ W W' C) (hn : Norm W W' C q) (v : QS W W' C) :
    act hn v = v := by
  induction v using QuotientGroup.induction_on with
  | H p =>
    change act hn (qc (W := W) (W' := W') (C := C) p p.2) = qc (W := W) (W' := W') (C := C) p p.2
    rw [act_qc, qc_eq_qc_iff]
    have h := hF.qq q hq p⁻¹ ((qQ W W' C).inv_mem p.2)
    simpa [mul_assoc] using h

theorem act_W_A {w : G} (hw : w ∈ W) {a : G} (ha : a ∈ W ⊓ C) :
    act (hF.norm_W hw) (qA W W' C a ha) = qA W W' C a ha := by
  rw [act_qc, qc_eq_qc_iff]
  refine ⟨?_, ?_⟩
  · have h := W.mul_mem (W.mul_mem (W.mul_mem hw (W.inv_mem ha.1)) (W.inv_mem hw)) ha.1
    simpa [mul_assoc] using h
  · have h := hF.ww w hw a⁻¹ (W.inv_mem ha.1)
    simpa [mul_assoc] using h

theorem act_W'_B {w : G} (hw : w ∈ W') {b : G} (hb : b ∈ W' ⊓ C) :
    act (hF.norm_W' hw) (qB W W' C b hb) =
      qB W W' C b hb := by
  rw [act_qc, qc_eq_qc_iff]
  refine ⟨?_, ?_⟩
  · have h := hF.w'w' w hw b⁻¹ (W'.inv_mem hb.1)
    simpa [mul_assoc] using h
  · have h := W'.mul_mem (W'.mul_mem (W'.mul_mem hw (W'.inv_mem hb.1)) (W'.inv_mem hw)) hb.1
    simpa [mul_assoc] using h

theorem act_W_B {w : G} (hw : w ∈ W) {b : G} (hb : b ∈ W' ⊓ C) :
    act (hF.norm_W hw) (qB W W' C b hb) =
      qA W W' C (cm w b) (hF.comm_W_B hw hb) *
        qB W W' C b hb := by
  rw [act_qc, qc_mul]
  congr 1
  simp only [cm]
  group

theorem act_W'_A {w : G} (hw : w ∈ W') {a : G} (ha : a ∈ W ⊓ C) :
    act (hF.norm_W' hw) (qA W W' C a ha) =
      qB W W' C (cm w a) (hF.comm_W'_A hw ha) *
        qA W W' C a ha := by
  rw [act_qc, qc_mul]
  congr 1
  simp only [cm]
  group

theorem qc_sq {q : G} (hq : q ∈ qQ W W' C) : qc q hq * qc q hq = 1 := by
  rw [qc_mul, qc_eq_one_iff]
  exact hF.sqq q hq

theorem qc_comm {p q : G} (hp : p ∈ qQ W W' C) (hq : q ∈ qQ W W' C) :
    qc p hp * qc q hq = qc q hq * qc p hp := by
  rw [qc_mul, qc_mul, qc_eq_qc_iff]
  have h := hF.qq q⁻¹ ((qQ W W' C).inv_mem hq) p⁻¹ ((qQ W W' C).inv_mem hp)
  simpa [mul_assoc] using h

theorem comm (u v : QS W W' C) : u * v = v * u := by
  induction u using QuotientGroup.induction_on with
  | H p =>
    induction v using QuotientGroup.induction_on with
    | H q => exact hF.qc_comm p.2 q.2

theorem sq_eq_one (u : QS W W' C) : u * u = 1 := by
  induction u using QuotientGroup.induction_on with
  | H p => exact hF.qc_sq p.2

omit hF in
theorem mem_D_of_qc_eq {a b : G} (ha : a ∈ W ⊓ C) (hb : b ∈ W' ⊓ C)
    (h : qA W W' C a ha = qB W W' C b hb) : a ∈ W ⊓ W' := by
  rw [qc_eq_qc_iff] at h
  refine ⟨ha.1, ?_⟩
  have : a = b * (a⁻¹ * b)⁻¹ := by group
  rw [this]
  exact W'.mul_mem hb.1 (W'.inv_mem h.2)

omit hF in
theorem eq_of_mul_eq {a a' b b' : G} (ha : a ∈ W ⊓ C) (ha' : a' ∈ W ⊓ C) (hb : b ∈ W' ⊓ C)
    (hb' : b' ∈ W' ⊓ C)
    (h : qA W W' C a ha * qB W W' C b hb = qA W W' C a' ha' * qB W W' C b' hb') :
    qA W W' C a ha = qA W W' C a' ha' ∧ qB W W' C b hb = qB W W' C b' hb' := by
  have h1 : (qA W W' C a' ha')⁻¹ * qA W W' C a ha =
      qB W W' C b' hb' * (qB W W' C b hb)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h2 : qA W W' C (a'⁻¹ * a) ((W ⊓ C).mul_mem ((W ⊓ C).inv_mem ha') ha) =
      qB W W' C (b' * b⁻¹) ((W' ⊓ C).mul_mem hb' ((W' ⊓ C).inv_mem hb)) := h1
  have hD := mem_D_of_qc_eq _ _ h2
  have hA : qA W W' C a ha = qA W W' C a' ha' := by
    rw [qc_eq_qc_iff]
    have := (W ⊓ W').inv_mem hD
    simpa using this
  refine ⟨hA, ?_⟩
  rw [hA] at h
  exact mul_left_cancel h

theorem exists_qc_eq (v : QS W W' C) :
    ∃ a, ∃ ha : a ∈ W ⊓ C, ∃ b, ∃ hb : b ∈ W' ⊓ C,
      v = qA W W' C a ha * qB W W' C b hb := by
  induction v using QuotientGroup.induction_on with
  | H q =>
    have hq : (q : G) ∈ ((W ⊓ C : Subgroup G) : Set G) * ((W' ⊓ C : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hF.a_le_normalizer_b]
      exact q.2
    obtain ⟨a, ha, b, hb, hab⟩ := hq
    refine ⟨a, ha, b, hb, ?_⟩
    rw [qc_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext hab.symm)

theorem act_comm_C_W {z : G} (hz : z ∈ C) (hzn : Norm W W' C z) {w : G} (hw : w ∈ W)
    (v : QS W W' C) : act hzn (act (hF.norm_W hw) v) = act (hF.norm_W hw) (act hzn v) := by
  have hzw : z * w * z⁻¹ * w⁻¹ ∈ W ⊓ C := by
    refine ⟨W.mul_mem (conj_mem_of_mem_normalizer (hF.cW hz) hw) (W.inv_mem hw), ?_⟩
    have h1 : w * z⁻¹ * w⁻¹ ∈ C := conj_mem_of_mem_normalizer (hF.wC hw) (C.inv_mem hz)
    have h2 := C.mul_mem hz h1
    simpa [mul_assoc] using h2
  have hq : z * w * z⁻¹ * w⁻¹ ∈ qQ W W' C := Subgroup.mem_sup_left hzw
  calc act hzn (act (hF.norm_W hw) v) = act (norm_mul hzn (hF.norm_W hw)) v :=
        (act_mul _ _ v).symm
    _ = act (norm_mul (hF.norm_Q hq) (norm_mul (hF.norm_W hw) hzn)) v :=
        act_congr _ _ (by group) v
    _ = act (hF.norm_Q hq) (act (norm_mul (hF.norm_W hw) hzn) v) := act_mul _ _ v
    _ = act (norm_mul (hF.norm_W hw) hzn) v := hF.act_Q hq _ _
    _ = act (hF.norm_W hw) (act hzn v) := act_mul _ _ v

theorem act_comm_C_W' {z : G} (hz : z ∈ C) (hzn : Norm W W' C z) {w : G} (hw : w ∈ W')
    (v : QS W W' C) : act hzn (act (hF.norm_W' hw) v) = act (hF.norm_W' hw) (act hzn v) := by
  have hzw : z * w * z⁻¹ * w⁻¹ ∈ W' ⊓ C := by
    refine ⟨W'.mul_mem (conj_mem_of_mem_normalizer (hF.cW' hz) hw) (W'.inv_mem hw), ?_⟩
    have h1 : w * z⁻¹ * w⁻¹ ∈ C := conj_mem_of_mem_normalizer (hF.w'C hw) (C.inv_mem hz)
    have h2 := C.mul_mem hz h1
    simpa [mul_assoc] using h2
  have hq : z * w * z⁻¹ * w⁻¹ ∈ qQ W W' C := Subgroup.mem_sup_right hzw
  calc act hzn (act (hF.norm_W' hw) v) = act (norm_mul hzn (hF.norm_W' hw)) v :=
        (act_mul _ _ v).symm
    _ = act (norm_mul (hF.norm_Q hq) (norm_mul (hF.norm_W' hw) hzn)) v :=
        act_congr _ _ (by group) v
    _ = act (hF.norm_Q hq) (act (norm_mul (hF.norm_W' hw) hzn) v) := act_mul _ _ v
    _ = act (norm_mul (hF.norm_W' hw) hzn) v := hF.act_Q hq _ _
    _ = act (hF.norm_W' hw) (act hzn v) := act_mul _ _ v

end Frame

end Act

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
