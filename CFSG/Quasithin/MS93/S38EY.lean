module

public import CFSG.Quasithin.MS93.S38EMod
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin
open scoped commutatorElement

variable {U₀ : Type*} [Group U₀] {V : Subgroup U₀}

theorem commutator_mem_vv (v w : ↥V) : ⁅(v : U₀), (w : U₀)⁆ ∈ ⁅V, V⁆ :=
  Subgroup.commutator_mem_commutator v.2 w.2

@[expose] def vComm (v w : ↥V) : ↥⁅V, V⁆ := ⟨⁅(v : U₀), (w : U₀)⁆, commutator_mem_vv v w⟩

section ClassTwo

variable (hV : ⁅V, V⁆ ≤ Subgroup.centralizer (V : Set U₀))
include hV

theorem comm_central {c : U₀} (hc : c ∈ ⁅V, V⁆) {v : U₀} (hv : v ∈ V) : v * c * v⁻¹ = c := by
  have := Subgroup.mem_centralizer_iff.mp (hV hc) v hv
  rw [this, mul_inv_cancel_right]

theorem vComm_mul_left (v₁ v₂ w : ↥V) : vComm (v₁ * v₂) w = vComm v₂ w * vComm v₁ w := by
  apply Subtype.ext
  show ⁅(v₁ : U₀) * v₂, (w : U₀)⁆ = ⁅(v₂ : U₀), (w : U₀)⁆ * ⁅(v₁ : U₀), (w : U₀)⁆
  have e : ⁅(v₁ : U₀) * v₂, (w : U₀)⁆ =
      ((v₁ : U₀) * ⁅(v₂ : U₀), (w : U₀)⁆ * (v₁ : U₀)⁻¹) * ⁅(v₁ : U₀), (w : U₀)⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, comm_central hV (commutator_mem_vv v₂ w) v₁.2]

theorem vComm_mul_right (v w₁ w₂ : ↥V) : vComm v (w₁ * w₂) = vComm v w₁ * vComm v w₂ := by
  apply Subtype.ext
  show ⁅(v : U₀), (w₁ : U₀) * w₂⁆ = ⁅(v : U₀), (w₁ : U₀)⁆ * ⁅(v : U₀), (w₂ : U₀)⁆
  have e : ⁅(v : U₀), (w₁ : U₀) * w₂⁆ =
      ⁅(v : U₀), (w₁ : U₀)⁆ * ((w₁ : U₀) * ⁅(v : U₀), (w₂ : U₀)⁆ * (w₁ : U₀)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, comm_central hV (commutator_mem_vv v w₂) w₁.2]

variable (lam : ↥⁅V, V⁆ →* ℂˣ)

@[expose] def vPair (v w : ↥V) : ℂˣ := lam (vComm v w)

omit hV in
theorem vPair_self (v : ↥V) : vPair lam v v = 1 := by
  have : vComm v v = 1 := Subtype.ext (by simp [vComm])
  rw [vPair, this, map_one]

theorem vPair_mul_left (v₁ v₂ w : ↥V) :
    vPair lam (v₁ * v₂) w = vPair lam v₁ w * vPair lam v₂ w := by
  rw [vPair, vComm_mul_left hV, map_mul, mul_comm]
  rfl

theorem vPair_mul_right (v w₁ w₂ : ↥V) :
    vPair lam v (w₁ * w₂) = vPair lam v w₁ * vPair lam v w₂ := by
  rw [vPair, vComm_mul_right hV, map_mul]
  rfl

@[expose] def zLam : Subgroup ↥V where
  carrier := {v | ∀ w, vPair lam v w = 1}
  one_mem' := fun w => by
    have h := vPair_mul_left hV lam 1 1 w
    rw [one_mul] at h
    exact left_eq_mul.mp h
  mul_mem' := fun ha hb w => by rw [vPair_mul_left hV, ha w, hb w, one_mul]
  inv_mem' := fun {a} ha w => by
    have h := vPair_mul_left hV lam a a⁻¹ w
    rw [mul_inv_cancel, ha w, one_mul] at h
    have h1 := vPair_mul_left hV lam 1 1 w
    rw [one_mul] at h1
    rw [← h, ← left_eq_mul.mp h1]

theorem commutator_le_zLam : ⁅(⊤ : Subgroup ↥V), ⊤⁆ ≤ zLam hV lam := by
  rw [Subgroup.commutator_le]
  intro a _ b _ w
  have hab : ((⁅a, b⁆ : ↥V) : U₀) = ⁅(a : U₀), (b : U₀)⁆ := by
    simp [commutatorElement_def]
  have hc : ((⁅a, b⁆ : ↥V) : U₀) ∈ ⁅V, V⁆ := by
    rw [hab]
    exact commutator_mem_vv a b
  have this : vComm ⁅a, b⁆ w = 1 := by
    apply Subtype.ext
    show ⁅((⁅a, b⁆ : ↥V) : U₀), (w : U₀)⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    have h1 := comm_central hV hc w.2
    calc ((⁅a, b⁆ : ↥V) : U₀) * w = ((w : U₀) * ((⁅a, b⁆ : ↥V) : U₀) * (w : U₀)⁻¹) * w := by
          rw [h1]
      _ = w * ((⁅a, b⁆ : ↥V) : U₀) := by group
  rw [vPair, this, map_one]

theorem zLam_normal : (zLam hV lam).Normal := by
  refine ⟨fun z hz v => ?_⟩
  have e : v * z * v⁻¹ = ⁅v, z⁆ * z := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (zLam hV lam).mul_mem (commutator_le_zLam hV lam
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top v) (Subgroup.mem_top z))) hz

instance zLam_normal' : (zLam hV lam).Normal := zLam_normal hV lam

theorem vPair_swap (v w : ↥V) : vPair lam w v = (vPair lam v w)⁻¹ := by
  have h := vPair_self lam (v * w)
  rw [vPair_mul_left hV, vPair_mul_right hV, vPair_mul_right hV, vPair_self, vPair_self,
    one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem vPair_right_eq_one {v z : ↥V} (hz : z ∈ zLam hV lam) : vPair lam v z = 1 := by
  rw [vPair_swap hV, hz v, inv_one]

instance yCommGroup : CommGroup (↥V ⧸ zLam hV lam) :=
  { (QuotientGroup.Quotient.group (zLam hV lam)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have h := commutator_le_zLam hV lam (Subgroup.commutator_mem_commutator
            (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
          have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact h }

@[expose] noncomputable def yPairLeft (w : ↥V) : (↥V ⧸ zLam hV lam) →* ℂˣ :=
  QuotientGroup.lift (zLam hV lam)
    { toFun := fun v => vPair lam v w
      map_one' := by
        have h := vPair_mul_left hV lam 1 1 w
        rw [one_mul] at h
        exact left_eq_mul.mp h
      map_mul' := fun a b => vPair_mul_left hV lam a b w }
    (fun z hz => hz w)

@[expose] noncomputable def yPairHom : (↥V ⧸ zLam hV lam) →* ((↥V ⧸ zLam hV lam) →* ℂˣ) :=
  QuotientGroup.lift (zLam hV lam)
    { toFun := fun w => yPairLeft hV lam w
      map_one' := by
        ext v
        show ((vPair lam v 1 : ℂˣ) : ℂ) = 1
        have h := vPair_mul_right hV lam v 1 1
        rw [one_mul] at h
        rw [left_eq_mul.mp h]
        rfl
      map_mul' := fun a b => by
        ext v
        show ((vPair lam v (a * b) : ℂˣ) : ℂ) = ((vPair lam v a * vPair lam v b : ℂˣ) : ℂ)
        rw [vPair_mul_right hV] }
    (fun z hz => by
      ext v
      show ((vPair lam v z : ℂˣ) : ℂ) = 1
      rw [vPair_right_eq_one hV lam hz]
      rfl)

@[expose] noncomputable def yPairing : Pairing (↥V ⧸ zLam hV lam) ℂˣ where
  f a b := yPairHom hV lam b a
  map_mul_left a b c := map_mul _ a b
  map_mul_right a b c := by rw [map_mul, MonoidHom.mul_apply]
  self a := by
    induction a using QuotientGroup.induction_on with
    | H a => exact vPair_self lam a
  nondeg a ha := by
    induction a using QuotientGroup.induction_on with
    | H a =>
      rw [QuotientGroup.eq_one_iff]
      intro w
      exact ha (QuotientGroup.mk w)

theorem yPairing_f_mk (v w : ↥V) :
    (yPairing hV lam).f (QuotientGroup.mk v) (QuotientGroup.mk w) = vPair lam v w := rfl

end ClassTwo

section Action

variable {G₀ : Subgroup U₀} (hG₀ : G₀ ≤ Subgroup.normalizer (V : Set U₀))
include hG₀

theorem conj_mem_of_le_normalizer {g : U₀} (hg : g ∈ G₀) {v : U₀} (hv : v ∈ V) :
    g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hG₀ hg) v).mp hv

@[expose] def conjV (g : ↥G₀) : ↥V ≃* ↥V where
  toFun v := ⟨(g : U₀) * v * (g : U₀)⁻¹, conj_mem_of_le_normalizer hG₀ g.2 v.2⟩
  invFun v := ⟨(g : U₀)⁻¹ * v * (g : U₀)⁻¹⁻¹, conj_mem_of_le_normalizer hG₀ (G₀.inv_mem g.2) v.2⟩
  left_inv v := Subtype.ext (by simp [mul_assoc])
  right_inv v := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjV_apply_coe (g : ↥G₀) (v : ↥V) :
    ((conjV hG₀ g v : ↥V) : U₀) = (g : U₀) * v * (g : U₀)⁻¹ := rfl

variable (hV : ⁅V, V⁆ ≤ Subgroup.centralizer (V : Set U₀)) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam : ∀ g : ↥G₀, ∀ v w : ↥V, vPair lam (conjV hG₀ g v) (conjV hG₀ g w) = vPair lam v w)
include hlam

theorem conjV_mem_zLam (g : ↥G₀) {z : ↥V} (hz : z ∈ zLam hV lam) :
    conjV hG₀ g z ∈ zLam hV lam := by
  intro w
  have hw : w = conjV hG₀ g ((conjV hG₀ g).symm w) := by simp
  rw [hw, hlam]
  exact hz _

theorem map_conjV_zLam (g : ↥G₀) :
    (zLam hV lam).map (conjV hG₀ g).toMonoidHom = zLam hV lam := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact conjV_mem_zLam hG₀ hV lam hlam g hz
  · intro hw
    refine ⟨(conjV hG₀ g).symm w, ?_, by simp⟩
    have h := conjV_mem_zLam hG₀ hV lam hlam g⁻¹ hw
    have e : conjV hG₀ g⁻¹ w = (conjV hG₀ g).symm w := Subtype.ext (by
      simp [conjV])
    rwa [e] at h

@[expose] noncomputable def yAct : ↥G₀ →* MulAut (↥V ⧸ zLam hV lam) where
  toFun g := QuotientGroup.congr _ _ (conjV hG₀ g) (map_conjV_zLam hG₀ hV lam hlam g)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H v =>
      apply congrArg (QuotientGroup.mk (s := zLam hV lam))
      exact Subtype.ext (by simp [conjV])
  map_mul' g h := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H v =>
      apply congrArg (QuotientGroup.mk (s := zLam hV lam))
      exact Subtype.ext (by simp [conjV, mul_assoc])

theorem yAct_mk (g : ↥G₀) (v : ↥V) :
    yAct hG₀ hV lam hlam g (QuotientGroup.mk v) = QuotientGroup.mk (conjV hG₀ g v) := rfl

theorem yPairing_isInv : (yPairing hV lam).IsInv (yAct hG₀ hV lam hlam).range := by
  rintro _ ⟨g, rfl⟩ a b
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [yAct_mk, yAct_mk, yPairing_f_mk, yPairing_f_mk, hlam]

end Action

end CFSG.Quasithin.MS93.S38E
