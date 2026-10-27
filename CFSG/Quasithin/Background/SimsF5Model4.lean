module

public import CFSG.Quasithin.Background.SimsF5Ai
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Quasithin.Background.SimsF5Main

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open CFSG.ASVolI.ChF
open scoped Pointwise commutatorElement

local notation "M6" => Matrix (Fin 6) (Fin 6) (ZMod 3)

@[expose] def rhoMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 1, 0, 0, 0, -1; 1, 1, 0, 0, 0, 1; 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0;
    -1, 1, 0, 0, 0, 0]

theorem m4_rhoMat_mul_pow : rhoMat * rhoMat ^ 3 = 1 := by decide

theorem m4_rhoMat_pow_mul : rhoMat ^ 3 * rhoMat = 1 := by decide

@[expose] def rhoDot : GL6 := ⟨rhoMat, rhoMat ^ 3, m4_rhoMat_mul_pow, m4_rhoMat_pow_mul⟩

theorem m4_rhoDot_val : ((rhoDot : GL6) : M6) = rhoMat := rfl

theorem rhoDot_mem_MDot : rhoDot ∈ MDot :=
  quat_mem_MDot_of_refl [quatRV ![1, 1, 0, 0, 0, 0], quatRV ![0, 0, 1, 0, 0, 0],
    quatRV ![0, 0, 0, 1, 0, 0], quatRV ![0, 0, 0, 0, 1, 0], quatRV ![1, 2, 0, 0, 0, 0],
    quatRV ![1, 2, 0, 0, 0, 2]] rhoDot (by decide) (by decide) (by decide)

theorem rhoDot_mul_self : rhoDot * rhoDot = fDot := Units.ext (by decide)

theorem orderOf_rhoDot : orderOf rhoDot = 4 := by
  have h4 : rhoDot ^ 4 = 1 := by
    have : rhoDot ^ 4 = fDot * fDot := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, rhoDot_mul_self]
    rw [this, mono_fDot_mul_self]
  have h2 : rhoDot ^ 2 ≠ 1 := by
    rw [sq, rhoDot_mul_self]; exact mono_fDot_ne_one
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one]) (by simpa using h4)
  simpa using this

theorem m4_mulVec_comm {A B : M6} (h : A * B = B * A) (v : V6) :
    B *ᵥ (A *ᵥ v) = A *ᵥ (B *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem m4_V2_form : ∀ v : V6, fMat *ᵥ v = -v → ∃ s t : ZMod 3, v = ![s, -s, 0, 0, 0, t] := by
  decide +kernel

theorem m4_ext_basis {A B : M6} (h0 : A *ᵥ (x1 + x2) = B *ᵥ (x1 + x2))
    (h1 : A *ᵥ (x1 - x2) = B *ᵥ (x1 - x2)) (h2 : A *ᵥ x3 = B *ᵥ x3) (h3 : A *ᵥ x4 = B *ᵥ x4)
    (h4 : A *ᵥ x5 = B *ᵥ x5) (h5 : A *ᵥ x6 = B *ᵥ x6) : A = B := by
  apply mono_mat_ext
  intro i
  have e0 : xvec 0 = (2 : ZMod 3) • (x1 + x2) + (2 : ZMod 3) • (x1 - x2) := by decide
  have e1 : xvec 1 = (2 : ZMod 3) • (x1 + x2) - (2 : ZMod 3) • (x1 - x2) := by decide
  fin_cases i
  · show A *ᵥ xvec 0 = B *ᵥ xvec 0
    rw [e0, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, h0, h1]
  · show A *ᵥ xvec 1 = B *ᵥ xvec 1
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, h0, h1]
  · exact h2
  · exact h3
  · exact h4
  · exact h5

@[expose] def m4Mat (e s t s' t' : ZMod 3) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![2 * e + 2 * s, 2 * e - 2 * s, 0, 0, 0, s'; 2 * e - 2 * s, 2 * e + 2 * s, 0, 0, 0, -s';
    0, 0, e, 0, 0, 0; 0, 0, 0, e, 0, 0; 0, 0, 0, 0, e, 0; 2 * t, -2 * t, 0, 0, 0, t']

theorem m4Mat_s : ∀ e s t s' t' : ZMod 3, m4Mat e s t s' t' *ᵥ (x1 + x2) = e • (x1 + x2) ∧
    m4Mat e s t s' t' *ᵥ (x1 - x2) = ![s, -s, 0, 0, 0, t] ∧
    m4Mat e s t s' t' *ᵥ x3 = e • x3 ∧ m4Mat e s t s' t' *ᵥ x4 = e • x4 ∧
    m4Mat e s t s' t' *ᵥ x5 = e • x5 ∧ m4Mat e s t s' t' *ᵥ x6 = ![s', -s', 0, 0, 0, t'] := by
  decide +kernel

theorem m4_key : ∀ e s t s' t' : ZMod 3, e ≠ 0 →
    qV ![s, -s, 0, 0, 0, t] = -1 → qV ![s', -s', 0, 0, 0, t'] = -1 →
    bil ![s, -s, 0, 0, 0, t] ![s', -s', 0, 0, 0, t'] = 0 →
    (m4Mat e s t s' t').det = 1 →
    m4Mat e s t s' t' = 1 ∨ m4Mat e s t s' t' = fMat ∨ m4Mat e s t s' t' = rhoMat ∨
      m4Mat e s t s' t' = rhoMat ^ 3 ∨ m4Mat e s t s' t' = -1 ∨ m4Mat e s t s' t' = -fMat ∨
      m4Mat e s t s' t' = -rhoMat ∨ m4Mat e s t s' t' = -(rhoMat ^ 3) := by
  decide +kernel

theorem m4_rho_sq : rhoDot ^ 2 = fDot := by
  rw [sq]
  exact rhoDot_mul_self

theorem m4_rho_pow_four : rhoDot ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, m4_rho_sq, mono_fDot_mul_self]

theorem m4_mem_Y_iff {x : GL6} :
    x ∈ Subgroup.zpowers rhoDot ↔ x = 1 ∨ x = rhoDot ∨ x = fDot ∨ x = rhoDot ^ 3 := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hk : rhoDot ^ k = rhoDot ^ (k % 4) := by
      have := zpow_mod_orderOf rhoDot k
      rw [orderOf_rhoDot] at this
      exact this.symm
    have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rw [hk]
    rcases h4 with h | h | h | h <;> rw [h]
    · exact Or.inl (zpow_zero _)
    · exact Or.inr (Or.inl (zpow_one _))
    · exact Or.inr (Or.inr (Or.inl (by rw [zpow_two]; exact rhoDot_mul_self)))
    · exact Or.inr (Or.inr (Or.inr (zpow_ofNat rhoDot 3)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · rw [← m4_rho_sq]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3

theorem m4_Y_le_MDot : Subgroup.zpowers rhoDot ≤ MDot :=
  Subgroup.zpowers_le.2 rhoDot_mem_MDot

theorem m4_rho_comm_f : rhoDot * fDot = fDot * rhoDot := by
  rw [← m4_rho_sq, ← pow_succ, ← pow_succ']

theorem m4_Y_comm_f {y : GL6} (hy : y ∈ Subgroup.zpowers rhoDot) : y * fDot = fDot * y := by
  rcases m4_mem_Y_iff.1 hy with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact m4_rho_comm_f
  · rfl
  · rw [← m4_rho_sq, ← pow_add, ← pow_add, add_comm]

theorem m4_rho_neg : ∀ w : V6, fMat *ᵥ w = w → rhoMat *ᵥ w = -w := by decide +kernel

theorem m4_conj_rho {g : GL6} (hg : g * fDot = fDot * g) {v : V6} (hv : fMat *ᵥ v = v) :
    ((g * rhoDot * g⁻¹ : GL6) : M6) *ᵥ v = -v := by
  have hg' : (g : M6) * fMat = fMat * (g : M6) := congrArg Units.val hg
  have hgi : ((g⁻¹ : GL6) : M6) * fMat = fMat * ((g⁻¹ : GL6) : M6) := by
    have h : (g⁻¹ : GL6) * fDot = fDot * g⁻¹ :=
      (Commute.inv_left (show Commute g fDot from hg)).eq
    exact congrArg Units.val h
  have h1 : fMat *ᵥ (((g⁻¹ : GL6) : M6) *ᵥ v) = ((g⁻¹ : GL6) : M6) *ᵥ v := by
    rw [m4_mulVec_comm hgi, hv]
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, m4_rhoDot_val,
    m4_rho_neg _ h1, Matrix.mulVec_neg, mono_mulVec_inv]

theorem m4_mem_Y {h : GL6} (hM : h ∈ MDot) (hf : h * fDot = fDot * h) {e : ZMod 3} (he : e ≠ 0)
    (h0 : (h : M6) *ᵥ (x1 + x2) = e • (x1 + x2)) (h3 : (h : M6) *ᵥ x3 = e • x3)
    (h4 : (h : M6) *ᵥ x4 = e • x4) (h5 : (h : M6) *ᵥ x5 = e • x5) :
    h ∈ Subgroup.zpowers rhoDot := by
  have hO : h ∈ OVq := MDot_le_OVq hM
  have hdet := det_of_mem_MDot hM
  have hf' : (h : M6) * fMat = fMat * (h : M6) := congrArg Units.val hf
  have hu : fMat *ᵥ ((h : M6) *ᵥ (x1 - x2)) = -((h : M6) *ᵥ (x1 - x2)) := by
    rw [m4_mulVec_comm hf', show fMat *ᵥ (x1 - x2) = -(x1 - x2) by decide, Matrix.mulVec_neg]
  have hw : fMat *ᵥ ((h : M6) *ᵥ x6) = -((h : M6) *ᵥ x6) := by
    rw [m4_mulVec_comm hf', show fMat *ᵥ x6 = -x6 by decide, Matrix.mulVec_neg]
  obtain ⟨s, t, hs⟩ := m4_V2_form _ hu
  obtain ⟨s', t', hs'⟩ := m4_V2_form _ hw
  have hq1 : qV ((h : M6) *ᵥ (x1 - x2)) = -1 := by
    rw [qV_mulVec_of_mem_OVq hO]; exact qV_x1_sub_x2
  have hq2 : qV ((h : M6) *ᵥ x6) = -1 := by
    rw [qV_mulVec_of_mem_OVq hO]; exact qV_x6
  have hb : bil ((h : M6) *ᵥ (x1 - x2)) ((h : M6) *ᵥ x6) = 0 := by
    rw [bil_mulVec_of_mem_OVq hO]; decide
  rw [hs] at hq1 hb
  rw [hs'] at hq2 hb
  have hA : (h : M6) = m4Mat e s t s' t' := by
    obtain ⟨c0, c1, c2, c3, c4, c5⟩ := m4Mat_s e s t s' t'
    exact m4_ext_basis (by rw [h0, c0]) (by rw [hs, c1]) (by rw [h3, c2]) (by rw [h4, c3])
      (by rw [h5, c4]) (by rw [hs', c5])
  rw [hA] at hdet
  have key := m4_key e s t s' t' he hq1 hq2 hb hdet
  have hneg : ∀ x : GL6, x ∈ MDot → (h : M6) = -(x : M6) → False := by
    intro x hx hxx
    have h1 : (-1 : GL6) = h * x⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, hxx, Units.val_neg, Units.val_one, neg_mul, Units.mul_inv]
    exact neg_one_not_mem_MDot (h1 ▸ MDot.mul_mem hM (MDot.inv_mem hx))
  rw [← hA] at key
  rcases key with k | k | k | k | k | k | k | k
  · exact (m4_mem_Y_iff).2 (Or.inl (Units.ext k))
  · exact (m4_mem_Y_iff).2 (Or.inr (Or.inr (Or.inl (Units.ext k))))
  · exact (m4_mem_Y_iff).2 (Or.inr (Or.inl (Units.ext k)))
  · exact (m4_mem_Y_iff).2 (Or.inr (Or.inr (Or.inr
      (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact k)))))
  · exact (hneg 1 MDot.one_mem (by rw [k]; simp)).elim
  · exact (hneg fDot fDot_mem_MDot k).elim
  · exact (hneg rhoDot rhoDot_mem_MDot k).elim
  · exact (hneg (rhoDot ^ 3) (MDot.pow_mem rhoDot_mem_MDot 3)
      (by rw [Units.val_pow_eq_pow_val]; exact k)).elim

theorem m4_val_comm {a b : GL6} (h : a * b = b * a) :
    (a : M6) * (b : M6) = (b : M6) * (a : M6) := by
  have := congrArg Units.val h
  simpa [Units.val_mul] using this

theorem m4_Y_conj {g : GL6} (hg : g ∈ MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) :
    g * rhoDot * g⁻¹ ∈ Subgroup.zpowers rhoDot := by
  have hgf : g * fDot = fDot * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
  refine m4_mem_Y (e := -1) ?_ ?_ (by decide) ?_ ?_ ?_ ?_
  · exact MDot.mul_mem (MDot.mul_mem hg.1 rhoDot_mem_MDot) (MDot.inv_mem hg.1)
  · exact ((Commute.mul_left (show Commute g fDot from hgf)
      (show Commute rhoDot fDot from m4_rho_comm_f)).mul_left
      (Commute.inv_left (show Commute g fDot from hgf))).eq
  · rw [m4_conj_rho hgf (by decide), neg_one_smul]
  · rw [m4_conj_rho hgf (by decide), neg_one_smul]
  · rw [m4_conj_rho hgf (by decide), neg_one_smul]
  · rw [m4_conj_rho hgf (by decide), neg_one_smul]

theorem m4_Y_normal {g : GL6} (hg : g ∈ MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6))
    {y : GL6} (hy : y ∈ Subgroup.zpowers rhoDot) : g * y * g⁻¹ ∈ Subgroup.zpowers rhoDot := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ (m4_Y_conj hg) k

theorem m4_mem_CGDot12 {g : GL6} (hM : g ∈ MDot) (h6 : (g : M6) *ᵥ x6 = x6)
    (h12 : (g : M6) *ᵥ (x1 - x2) = x1 - x2) : g ∈ CGDot12 :=
  ⟨mem_GDot_iff.2 ⟨hM, h6⟩, MulAction.mem_stabilizer_iff.2 ((quat_smul_def g _).trans h12)⟩

theorem m4_E23_mem : eJ {2, 3} ∈ CGDot12 :=
  m4_mem_CGDot12 (eJ_mem_MDot _ (by decide) (by decide)) (eJ_mulVec_x6 _ (by decide)) (by decide)

theorem m4_E24_mem : eJ {2, 4} ∈ CGDot12 :=
  m4_mem_CGDot12 (eJ_mem_MDot _ (by decide) (by decide)) (eJ_mulVec_x6 _ (by decide)) (by decide)

theorem m4_E34_mem : eJ {3, 4} ∈ CGDot12 :=
  m4_mem_CGDot12 (eJ_mem_MDot _ (by decide) (by decide)) (eJ_mulVec_x6 _ (by decide)) (by decide)

@[expose] def m4G1Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 2, 1, 1, 0; 0, 1, 2, 1, 1, 0; 1, 1, 0, 1, 1, 0; 2, 2, 1, 0, 2, 0; 2, 2, 1, 2, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def m4G1InvMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 1, 2, 2, 0; 0, 1, 1, 2, 2, 0; 2, 2, 0, 1, 1, 0; 1, 1, 1, 0, 2, 0; 1, 1, 1, 2, 0, 0;
    0, 0, 0, 0, 0, 1]

theorem m4G1Mat_mul : m4G1Mat * m4G1InvMat = 1 := by decide

theorem m4G1Mat_mul' : m4G1InvMat * m4G1Mat = 1 := by decide

@[expose] def m4G1 : GL6 := ⟨m4G1Mat, m4G1InvMat, m4G1Mat_mul, m4G1Mat_mul'⟩

theorem m4G1_mem : m4G1 ∈ CGDot12 :=
  m4_mem_CGDot12 (quat_mem_MDot_of_refl [quatRV ![1, 1, 0, 0, 0, 0], quatRV ![2, 2, 1, 2, 2, 0]]
    m4G1 (by decide) (by decide) (by decide)) (by decide) (by decide)

theorem m4_L3 : ∀ v : V6, ((eJ {2, 3} : GL6) : M6) *ᵥ v = -v →
    ((eJ {2, 4} : GL6) : M6) *ᵥ v = -v → ∃ c : ZMod 3, v = c • x3 := by decide +kernel

theorem m4_L4 : ∀ v : V6, ((eJ {2, 3} : GL6) : M6) *ᵥ v = -v →
    ((eJ {3, 4} : GL6) : M6) *ᵥ v = -v → ∃ c : ZMod 3, v = c • x4 := by decide +kernel

theorem m4_L5 : ∀ v : V6, ((eJ {2, 4} : GL6) : M6) *ᵥ v = -v →
    ((eJ {3, 4} : GL6) : M6) *ᵥ v = -v → ∃ c : ZMod 3, v = c • x5 := by decide +kernel

theorem m4_L0 : ∀ v : V6, ((eJ {2, 3} : GL6) : M6) *ᵥ v = v → ((eJ {2, 4} : GL6) : M6) *ᵥ v = v →
    ((eJ {3, 4} : GL6) : M6) *ᵥ v = v → fMat *ᵥ v = v → ∃ c : ZMod 3, v = c • (x1 + x2) := by
  decide +kernel

theorem m4_L6 : ∀ c0 c3 c4 c5 : ZMod 3,
    -(c0 • (x1 + x2)) + c4 • x4 + c5 • x5 = c3 • (-(x1 + x2) + x4 + x5) →
    c0 = c3 ∧ c4 = c3 ∧ c5 = c3 := by decide +kernel

theorem m4_cen_scalar {h : GL6} (hf : h * fDot = fDot * h)
    (hc : ∀ g ∈ CGDot12, h * g = g * h) :
    ∃ e : ZMod 3, (h : M6) *ᵥ (x1 + x2) = e • (x1 + x2) ∧ (h : M6) *ᵥ x3 = e • x3 ∧
      (h : M6) *ᵥ x4 = e • x4 ∧ (h : M6) *ᵥ x5 = e • x5 := by
  have c23 := m4_val_comm (hc _ m4_E23_mem)
  have c24 := m4_val_comm (hc _ m4_E24_mem)
  have c34 := m4_val_comm (hc _ m4_E34_mem)
  have cg := m4_val_comm (hc _ m4G1_mem)
  have cf : (h : M6) * fMat = fMat * (h : M6) := m4_val_comm hf
  obtain ⟨c3, h3⟩ := m4_L3 ((h : M6) *ᵥ x3)
    (by rw [m4_mulVec_comm c23, show ((eJ {2, 3} : GL6) : M6) *ᵥ x3 = -x3 by decide,
      Matrix.mulVec_neg])
    (by rw [m4_mulVec_comm c24, show ((eJ {2, 4} : GL6) : M6) *ᵥ x3 = -x3 by decide,
      Matrix.mulVec_neg])
  obtain ⟨c4, h4⟩ := m4_L4 ((h : M6) *ᵥ x4)
    (by rw [m4_mulVec_comm c23, show ((eJ {2, 3} : GL6) : M6) *ᵥ x4 = -x4 by decide,
      Matrix.mulVec_neg])
    (by rw [m4_mulVec_comm c34, show ((eJ {3, 4} : GL6) : M6) *ᵥ x4 = -x4 by decide,
      Matrix.mulVec_neg])
  obtain ⟨c5, h5⟩ := m4_L5 ((h : M6) *ᵥ x5)
    (by rw [m4_mulVec_comm c24, show ((eJ {2, 4} : GL6) : M6) *ᵥ x5 = -x5 by decide,
      Matrix.mulVec_neg])
    (by rw [m4_mulVec_comm c34, show ((eJ {3, 4} : GL6) : M6) *ᵥ x5 = -x5 by decide,
      Matrix.mulVec_neg])
  obtain ⟨c0, h0⟩ := m4_L0 ((h : M6) *ᵥ (x1 + x2))
    (by rw [m4_mulVec_comm c23, show ((eJ {2, 3} : GL6) : M6) *ᵥ (x1 + x2) = x1 + x2 by decide])
    (by rw [m4_mulVec_comm c24, show ((eJ {2, 4} : GL6) : M6) *ᵥ (x1 + x2) = x1 + x2 by decide])
    (by rw [m4_mulVec_comm c34, show ((eJ {3, 4} : GL6) : M6) *ᵥ (x1 + x2) = x1 + x2 by decide])
    (by rw [m4_mulVec_comm cf, show fMat *ᵥ (x1 + x2) = x1 + x2 by decide])
  have hg : ((m4G1 : GL6) : M6) *ᵥ x3 = -(x1 + x2) + x4 + x5 := by decide
  have hcon : (h : M6) *ᵥ (((m4G1 : GL6) : M6) *ᵥ x3) =
      ((m4G1 : GL6) : M6) *ᵥ ((h : M6) *ᵥ x3) := m4_mulVec_comm cg.symm x3
  rw [hg, h3, Matrix.mulVec_smul, hg, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_neg,
    h0, h4, h5] at hcon
  obtain ⟨e0, e4, e5⟩ := m4_L6 c0 c3 c4 c5 hcon
  exact ⟨c3, by rw [h0, e0], h3, by rw [h4, e4], by rw [h5, e5]⟩

theorem m4_cen_mem_Y {h : GL6} (hM : h ∈ MDot) (hf : h * fDot = fDot * h)
    (hc : ∀ g ∈ CGDot12, h * g = g * h) : h ∈ Subgroup.zpowers rhoDot := by
  obtain ⟨e, h0, h3, h4, h5⟩ := m4_cen_scalar hf hc
  exact m4_mem_Y hM hf (ai_scalar_ne_zero h3 (by decide)) h0 h3 h4 h5

theorem m4_two_mul_card_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hHK : H ≤ K)
    (hne : H ≠ K) : 2 * Nat.card H ≤ Nat.card K := by
  have h := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.2 hHK] at h
  have h1 : H.relIndex K ≠ 1 := fun h' => hne (le_antisymm hHK (Subgroup.relIndex_eq_one.1 h'))
  have h0 : H.relIndex K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := ↥K)).ne' h.symm
  have h2 : 2 ≤ H.relIndex K := by omega
  calc 2 * Nat.card H ≤ H.relIndex K * Nat.card H := Nat.mul_le_mul_right _ h2
    _ = Nat.card K := h

@[expose] def m4D4Fun {G : Type*} [Group G] (A C : G) : DihedralGroup 4 → G
  | .r k => quatZpow A k
  | .sr k => C * quatZpow A k

@[expose] def m4D4Lift {G : Type*} [Group G] (A C : G) (hA : A ^ 4 = 1) (hC : C ^ 2 = 1)
    (hCA : C * A * C⁻¹ = A⁻¹) : DihedralGroup 4 →* G where
  toFun := m4D4Fun A C
  map_one' := by
    rw [← DihedralGroup.r_zero]
    simp [m4D4Fun, quatZpow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · simp only [DihedralGroup.r_mul_r, m4D4Fun]
      exact quatZpow_add hA i j
    · simp only [DihedralGroup.r_mul_sr, m4D4Fun]
      rw [← mul_assoc, quatZpow_mul_B hA hCA, mul_assoc, ← quatZpow_add hA, neg_add_eq_sub]
    · simp only [DihedralGroup.sr_mul_r, m4D4Fun, quatZpow_add hA, mul_assoc]
    · simp only [DihedralGroup.sr_mul_sr, m4D4Fun]
      symm
      calc C * quatZpow A i * (C * quatZpow A j)
          = C * (quatZpow A i * C) * quatZpow A j := by simp only [mul_assoc]
        _ = C * (C * quatZpow A (-i)) * quatZpow A j := by rw [quatZpow_mul_B hA hCA]
        _ = (C * C) * (quatZpow A (-i) * quatZpow A j) := by simp only [mul_assoc]
        _ = quatZpow A (j - i) := by
          rw [← quatZpow_add hA, ← sq, hC, one_mul, neg_add_eq_sub]

theorem m4D4Lift_mem {G : Type*} [Group G] {A C : G} {hA : A ^ 4 = 1} {hC : C ^ 2 = 1}
    {hCA : C * A * C⁻¹ = A⁻¹} {H : Subgroup G} (hAH : A ∈ H) (hCH : C ∈ H) (x : DihedralGroup 4) :
    m4D4Lift A C hA hC hCA x ∈ H := by
  rcases x with k | k
  · exact H.pow_mem hAH _
  · exact H.mul_mem hCH (H.pow_mem hAH _)

theorem m4_eJ_mem_TDot {J : Finset (Fin 6)} (hJ : J ⊆ Iset) (he : Even J.card) :
    eJ J ∈ TDot := by
  have hS : eJ J ∈ SDot := by
    rw [SDot_eq]
    exact Subgroup.mem_sup_left (mono_eJ_mem_Q2Dot hJ he)
  exact Subgroup.mem_sup_left hS

theorem m4_f_mem_TDot : fDot ∈ TDot := Subgroup.mem_sup_right (Subgroup.mem_zpowers fDot)

@[expose] def m4Kap1Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def m4Kap2Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem m4Kap1Mat_sq : m4Kap1Mat * m4Kap1Mat = 1 := by decide

theorem m4Kap2Mat_sq : m4Kap2Mat * m4Kap2Mat = 1 := by decide

@[expose] def m4Kap1 : GL6 := ⟨m4Kap1Mat, m4Kap1Mat, m4Kap1Mat_sq, m4Kap1Mat_sq⟩

@[expose] def m4Kap2 : GL6 := ⟨m4Kap2Mat, m4Kap2Mat, m4Kap2Mat_sq, m4Kap2Mat_sq⟩

theorem m4_sgn_swap_mul_swap (a b c d : Fin 5) (hab : a ≠ b) (hcd : c ≠ d) :
    monoSgn (Equiv.swap a b * Equiv.swap c d) = 1 := by
  unfold monoSgn
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
  decide

theorem m4Kap1_eq : m4Kap1 = s5Hom (Equiv.swap 0 1 * Equiv.swap 2 3) := by
  apply mono_gl_ext
  intro i
  rw [s5Hom_mulVec_xvec]
  rcases mono_fin_cases i with rfl | ⟨c, rfl⟩
  · rw [mono_scal_five, mono_ext_five, m4_sgn_swap_mul_swap 0 1 2 3 (by decide) (by decide)]
    decide
  · rw [mono_scal_castSucc, mono_ext_castSucc, one_smul]
    revert c
    decide

theorem m4Kap2_eq : m4Kap2 = s5Hom (Equiv.swap 0 2 * Equiv.swap 1 3) := by
  apply mono_gl_ext
  intro i
  rw [s5Hom_mulVec_xvec]
  rcases mono_fin_cases i with rfl | ⟨c, rfl⟩
  · rw [mono_scal_five, mono_ext_five, m4_sgn_swap_mul_swap 0 2 1 3 (by decide) (by decide)]
    decide
  · rw [mono_scal_castSucc, mono_ext_castSucc, one_smul]
    revert c
    decide

theorem m4_Kap1_mem_TDot : m4Kap1 ∈ TDot := by
  have hS : m4Kap1 ∈ SDot := by
    rw [SDot_eq, m4Kap1_eq]
    exact Subgroup.mem_sup_right ⟨_, mem_monoKlein4.2 (Or.inr (Or.inl rfl)), rfl⟩
  exact Subgroup.mem_sup_left hS

theorem m4_Kap2_mem_TDot : m4Kap2 ∈ TDot := by
  have hS : m4Kap2 ∈ SDot := by
    rw [SDot_eq, m4Kap2_eq]
    exact Subgroup.mem_sup_right ⟨_, mem_monoKlein4.2 (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  exact Subgroup.mem_sup_left hS

@[expose] def m4A1Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, -1]

@[expose] def m4B1Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, -1]

@[expose] def m4A2Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![-1, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, -1]

@[expose] def m4B2Mat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, -1]

theorem m4A1Mat_inv : m4A1Mat * m4A1Mat ^ 3 = 1 := by decide
theorem m4A1Mat_inv' : m4A1Mat ^ 3 * m4A1Mat = 1 := by decide
theorem m4A2Mat_inv : m4A2Mat * m4A2Mat ^ 3 = 1 := by decide
theorem m4A2Mat_inv' : m4A2Mat ^ 3 * m4A2Mat = 1 := by decide
theorem m4B1Mat_sq : m4B1Mat * m4B1Mat = 1 := by decide
theorem m4B2Mat_sq : m4B2Mat * m4B2Mat = 1 := by decide

@[expose] def m4A1 : GL6 := ⟨m4A1Mat, m4A1Mat ^ 3, m4A1Mat_inv, m4A1Mat_inv'⟩
@[expose] def m4A2 : GL6 := ⟨m4A2Mat, m4A2Mat ^ 3, m4A2Mat_inv, m4A2Mat_inv'⟩
@[expose] def m4B1 : GL6 := ⟨m4B1Mat, m4B1Mat, m4B1Mat_sq, m4B1Mat_sq⟩
@[expose] def m4B2 : GL6 := ⟨m4B2Mat, m4B2Mat, m4B2Mat_sq, m4B2Mat_sq⟩

theorem m4_A1_pow : m4A1 ^ 4 = 1 := by decide
theorem m4_A2_pow : m4A2 ^ 4 = 1 := by decide
theorem m4_B1_sq : m4B1 ^ 2 = 1 := by decide
theorem m4_B2_sq : m4B2 ^ 2 = 1 := by decide
theorem m4_B1A1 : m4B1 * m4A1 * m4B1⁻¹ = m4A1⁻¹ := by decide
theorem m4_B2A2 : m4B2 * m4A2 * m4B2⁻¹ = m4A2⁻¹ := by decide

@[expose] def m4Phi1 : DihedralGroup 4 →* GL6 := m4D4Lift m4A1 m4B1 m4_A1_pow m4_B1_sq m4_B1A1

@[expose] def m4Phi2 : DihedralGroup 4 →* GL6 := m4D4Lift m4A2 m4B2 m4_A2_pow m4_B2_sq m4_B2A2

theorem m4_phi_comm : ∀ x y : DihedralGroup 4, m4Phi1 x * m4Phi2 y = m4Phi2 y * m4Phi1 x := by
  decide +kernel

@[expose] def m4Phi : DihedralGroup 4 × DihedralGroup 4 →* GL6 :=
  MonoidHom.noncommCoprod m4Phi1 m4Phi2 fun x y => m4_phi_comm x y

theorem m4Phi_apply (p : DihedralGroup 4 × DihedralGroup 4) : m4Phi p = m4Phi1 p.1 * m4Phi2 p.2 :=
  rfl

theorem m4Phi_injective : Function.Injective m4Phi := by
  rw [injective_iff_map_eq_one]
  have key : ∀ p : DihedralGroup 4 × DihedralGroup 4, m4Phi1 p.1 * m4Phi2 p.2 = 1 → p = 1 := by
    decide +kernel
  intro p hp
  exact key p hp

theorem m4_mem_Tt {g : GL6} (hT : g ∈ TDot) (hc : g * tDot = tDot * g) :
    g ∈ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) :=
  ⟨hT, Subgroup.mem_centralizer_singleton_iff.2 hc⟩

theorem m4_A1_mem : m4A1 ∈ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
  have h : m4A1 = eJ {1, 2, 3, 4} * fDot := Units.ext (by decide)
  refine m4_mem_Tt ?_ (by decide)
  rw [h]
  exact TDot.mul_mem (m4_eJ_mem_TDot (by decide) (by decide)) m4_f_mem_TDot

theorem m4_B1_mem : m4B1 ∈ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
  have h : m4B1 = eJ {2, 3} * fDot := Units.ext (by decide)
  refine m4_mem_Tt ?_ (by decide)
  rw [h]
  exact TDot.mul_mem (m4_eJ_mem_TDot (by decide) (by decide)) m4_f_mem_TDot

theorem m4_B2_mem : m4B2 ∈ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
  have h : m4B2 = m4Kap1 * fDot := Units.ext (by decide)
  refine m4_mem_Tt ?_ (by decide)
  rw [h]
  exact TDot.mul_mem m4_Kap1_mem_TDot m4_f_mem_TDot

theorem m4_A2_mem : m4A2 ∈ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
  have h : m4A2 = eJ {0, 1, 3, 4} * m4B2 := Units.ext (by decide)
  refine m4_mem_Tt ?_ (by decide)
  rw [h]
  exact TDot.mul_mem (m4_eJ_mem_TDot (by decide) (by decide)) m4_B2_mem.1

theorem m4_range_le : m4Phi.range ≤ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
  rintro _ ⟨p, rfl⟩
  rw [m4Phi_apply]
  exact Subgroup.mul_mem _ (m4D4Lift_mem m4_A1_mem m4_B1_mem p.1)
    (m4D4Lift_mem m4_A2_mem m4_B2_mem p.2)

theorem m4_Tt_card_le :
    Nat.card ↥(TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6)) ≤ 64 := by
  have hne : TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) ≠ TDot := by
    intro h
    have h2 : m4Kap2 ∈ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
      rw [h]
      exact m4_Kap2_mem_TDot
    have h3 := Subgroup.mem_centralizer_singleton_iff.1 h2.2
    revert h3
    decide
  have := m4_two_mul_card_le (inf_le_left : TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) ≤ TDot)
    hne
  rw [card_TDot] at this
  omega

theorem m4_card_D4 : Nat.card (DihedralGroup 4 × DihedralGroup 4) = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem m4_range_eq : m4Phi.range = TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6) := by
  apply Subgroup.eq_of_le_of_card_ge m4_range_le
  have h : Nat.card ↥m4Phi.range = 64 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective m4Phi_injective).toEquiv, m4_card_D4]
  rw [h]
  exact m4_Tt_card_le

theorem TDot_inf_cen_tDot :
    Nonempty (↥(TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6)) ≃*
      DihedralGroup 4 × DihedralGroup 4) :=
  ⟨((MonoidHom.ofInjective m4Phi_injective).trans (MulEquiv.subgroupCongr m4_range_eq)).symm⟩

@[expose] def m4P0 : DihedralGroup 4 × DihedralGroup 4 := (DihedralGroup.sr 0, DihedralGroup.r 2)

theorem m4Phi_P0 : m4Phi m4P0 = fDot := by
  rw [m4Phi_apply]
  decide

theorem m4_Tf_eq : TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) =
    (Subgroup.centralizer ({m4P0} : Set (DihedralGroup 4 × DihedralGroup 4))).map m4Phi := by
  ext g
  constructor
  · rintro ⟨hT, hc⟩
    have hcf : g * fDot = fDot * g := Subgroup.mem_centralizer_singleton_iff.1 hc
    have hM2 : g ∈ M2Dot := (TDot_le_M12 hT).2
    have hct : g * tDot = tDot * g := ai_tDot_central hM2 hcf
    have hg : g ∈ m4Phi.range := by
      rw [m4_range_eq]
      exact m4_mem_Tt hT hct
    obtain ⟨x, rfl⟩ := hg
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply m4Phi_injective
    rw [map_mul, map_mul, m4Phi_P0]
    exact hcf
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨(m4_range_le ⟨x, rfl⟩).1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := congrArg m4Phi hx
    rwa [map_mul, map_mul, m4Phi_P0] at this

theorem m4_card_cen_P0 :
    Nat.card ↥(Subgroup.centralizer ({m4P0} : Set (DihedralGroup 4 × DihedralGroup 4))) = 32 := by
  have : Nat.card ↥(Subgroup.centralizer ({m4P0} : Set (DihedralGroup 4 × DihedralGroup 4))) =
      Nat.card {x : DihedralGroup 4 × DihedralGroup 4 // x * m4P0 = m4P0 * x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Subgroup.mem_centralizer_singleton_iff)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem m4_card_Tf : Nat.card ↥(TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = 32 := by
  rw [m4_Tf_eq, Subgroup.card_map_of_injective m4Phi_injective, m4_card_cen_P0]

@[expose] noncomputable def RDot : Subgroup GL6 :=
  (TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ⊔ Subgroup.zpowers rhoDot

theorem m4_Tf_le_C : TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≤
    MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  fun _ hg => ⟨(TDot_le_M12 hg.1).1.1, hg.2⟩

theorem m4_Y_le_C : Subgroup.zpowers rhoDot ≤ MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  Subgroup.zpowers_le.2 ⟨rhoDot_mem_MDot, Subgroup.mem_centralizer_singleton_iff.2 m4_rho_comm_f⟩

theorem RDot_le : RDot ≤ MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  sup_le m4_Tf_le_C m4_Y_le_C

theorem m4_Tf_le_R : TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≤ RDot := le_sup_left

theorem m4_Y_le_R : Subgroup.zpowers rhoDot ≤ RDot := le_sup_right

theorem m4_rho_mem_R : rhoDot ∈ RDot := m4_Y_le_R (Subgroup.mem_zpowers _)

theorem m4_f_mem_Tf : fDot ∈ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  ⟨m4_f_mem_TDot, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem m4_Tf_le_normalizer_Y :
    TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≤
      Subgroup.normalizer (Subgroup.zpowers rhoDot : Set GL6) := by
  intro t ht
  have ht' := m4_Tf_le_C ht
  refine mono_mem_normalizer_of_conj (fun s hs => m4_Y_normal ht' hs) (fun s hs => ?_)
  have := m4_Y_normal ((MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)).inv_mem ht') hs
  rwa [inv_inv] at this

theorem m4_mem_RDot_iff {x : GL6} : x ∈ RDot ↔
    ∃ t ∈ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6), ∃ y ∈ Subgroup.zpowers rhoDot,
      x = t * y := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right
    (TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) (Subgroup.zpowers rhoDot)
    m4_Tf_le_normalizer_Y
  constructor
  · intro hx
    have hx' : x ∈ (↑RDot : Set GL6) := hx
    rw [show (RDot : Set GL6) = ↑((TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ⊔
      Subgroup.zpowers rhoDot) from rfl, h] at hx'
    obtain ⟨t, ht, y, hy, rfl⟩ := hx'
    exact ⟨t, ht, y, hy, rfl⟩
  · rintro ⟨t, ht, y, hy, rfl⟩
    exact RDot.mul_mem (m4_Tf_le_R ht) (m4_Y_le_R hy)

theorem m4_rho_not_mem_M0 : rhoDot ∉ M0Dot := by
  intro h
  have := M0Dot_mulVec_x6 h
  revert this
  rw [m4_rhoDot_val]
  decide

theorem m4_rho_not_mem_Tf : rhoDot ∉ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  fun h => m4_rho_not_mem_M0 (M2Dot_le_M0Dot (TDot_le_M12 h.1).2)

theorem m4_rho3_not_mem_Tf : rhoDot ^ 3 ∉ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  intro h
  apply m4_rho_not_mem_Tf
  have h2 := (TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)).mul_mem h m4_f_mem_Tf
  have : rhoDot ^ 3 * fDot = rhoDot := by
    rw [← m4_rho_sq, ← pow_add]
    have := m4_rho_pow_four
    calc rhoDot ^ (3 + 2) = rhoDot ^ 4 * rhoDot := by rw [← pow_succ]
      _ = rhoDot := by rw [this, one_mul]
  rwa [this] at h2

theorem m4_xor_aux {b : GL6} (hb : b ∈ RDot) :
    Xor' (b * rhoDot ∈ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6))
      (b ∈ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) := by
  obtain ⟨t, ht, y, hy, rfl⟩ := m4_mem_RDot_iff.1 hb
  have hr4 := m4_rho_pow_four
  have hρ := m4_rho_not_mem_Tf
  have hρ3 := m4_rho3_not_mem_Tf
  have hf := m4_f_mem_Tf
  have e1 : ∀ z : GL6, t * z ∈ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) →
      z ∈ TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := fun z hz => by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hz
    rwa [inv_mul_cancel_left] at this
  rcases m4_mem_Y_iff.1 hy with rfl | rfl | rfl | rfl
  · exact Or.inr ⟨by simpa using ht, fun h => hρ (e1 _ (by simpa using h))⟩
  · refine Or.inl ⟨?_, fun h => hρ (e1 _ h)⟩
    rw [mul_assoc, ← sq, m4_rho_sq]
    exact Subgroup.mul_mem _ ht hf
  · refine Or.inr ⟨Subgroup.mul_mem _ ht hf, fun h => hρ ?_⟩
    rw [mul_assoc] at h
    have h1 := e1 _ h
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hf) h1
    rwa [inv_mul_cancel_left] at h2
  · refine Or.inl ⟨?_, fun h => hρ3 (e1 _ h)⟩
    rw [mul_assoc, ← pow_succ, show (3 + 1 : ℕ) = 4 from rfl, hr4, mul_one]
    exact ht

theorem m4_index_Tf_R :
    ((TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)).subgroupOf RDot).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨rhoDot, m4_rho_mem_R⟩, fun b => ?_⟩
  rcases m4_xor_aux b.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Subgroup.mem_subgroupOf.2 h1, fun h => h2 (Subgroup.mem_subgroupOf.1 h)⟩
  · exact Or.inr ⟨Subgroup.mem_subgroupOf.2 h1, fun h => h2 (Subgroup.mem_subgroupOf.1 h)⟩

theorem card_RDot : Nat.card ↥RDot = 64 := by
  have h := Subgroup.card_mul_index
    ((TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)).subgroupOf RDot)
  rw [m4_index_Tf_R, Nat.card_congr (Subgroup.subgroupOfEquivOfLe m4_Tf_le_R).toEquiv,
    m4_card_Tf] at h
  omega

theorem RDot_inf_M0Dot : RDot ⊓ M0Dot = TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  have hle : TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≤ RDot ⊓ M0Dot :=
    le_inf m4_Tf_le_R fun g hg => M2Dot_le_M0Dot (TDot_le_M12 hg.1).2
  have hne : RDot ⊓ M0Dot ≠ RDot := by
    intro h
    have h1 : rhoDot ∈ RDot ⊓ M0Dot := by
      rw [h]
      exact m4_rho_mem_R
    exact m4_rho_not_mem_M0 h1.2
  have h2 := m4_two_mul_card_le (inf_le_left : RDot ⊓ M0Dot ≤ RDot) hne
  rw [card_RDot] at h2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [m4_card_Tf]; omega)).symm

theorem zpowers_rhoDot_equiv :
    Nonempty (↥(Subgroup.zpowers rhoDot) ≃* Multiplicative (ZMod 4)) := by
  have hc : Nat.card ↥(Subgroup.zpowers rhoDot) = 4 := by
    rw [Nat.card_zpowers, orderOf_rhoDot]
  exact ⟨((AddEquiv.toMultiplicative (ZMod.ringEquivCongr hc.symm).toAddEquiv).trans
    (zmodCyclicMulEquiv (Subgroup.isCyclic_zpowers rhoDot))).symm⟩

theorem eq_RDot (R : Subgroup GL6)
    (hcard : Nat.card ↥(MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = 2880)
    (hR : IsSylowOf 2 R (MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)))
    (hTR : TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≤ R) : R = RDot := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRC, hRp, hRidx⟩ := hR
  set C := MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) with hC
  have hR64 : Nat.card ↥R = 64 := by
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    have h := Subgroup.relIndex_mul_card R C
    rw [inf_eq_left.2 hRC, hk, hcard] at h
    have hk11 : k < 12 := by
      by_contra hk12
      have h1 : 2 ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hk12)
      have h2 : R.relIndex C ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h
        omega
      have h3 : 2 ^ k ≤ 2880 := by
        have : 1 * 2 ^ k ≤ R.relIndex C * 2 ^ k :=
          Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.2 h2)
        omega
      omega
    have hodd : ¬ 2 ∣ R.relIndex C := hRidx
    rw [hk]
    interval_cases k <;> omega
  have hYC : Subgroup.zpowers rhoDot ≤ C := m4_Y_le_C
  have hYle : Subgroup.zpowers rhoDot ≤ R := by
    let N : Subgroup ↥C := (Subgroup.zpowers rhoDot).subgroupOf C
    haveI hN : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using m4_Y_normal g.2 hn⟩
    have hNcard : Nat.card ↥N = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv, Nat.card_zpowers,
        orderOf_rhoDot]
    have hNp : IsPGroup 2 ↥N := IsPGroup.of_card (n := 2) (by rw [hNcard]; norm_num)
    let S : Subgroup ↥C := R.subgroupOf C
    have hScard : Nat.card ↥S = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hR64]
    have hSp : IsPGroup 2 ↥S := IsPGroup.of_card (n := 6) (by rw [hScard]; norm_num)
    have hSidx : ¬ 2 ∣ S.index := hRidx
    have hle := hNp.le_sylow_of_normal (hSp.toSylow hSidx)
    intro y hy
    have hyN : (⟨y, hYC hy⟩ : ↥C) ∈ N := Subgroup.mem_subgroupOf.2 hy
    exact Subgroup.mem_subgroupOf.1 (hle hyN)
  have hRle : RDot ≤ R := sup_le hTR hYle
  exact (Subgroup.eq_of_le_of_card_ge hRle (by rw [hR64, card_RDot])).symm

theorem m4_rho_sub : rhoMat *ᵥ (x1 - x2) = x6 := by decide

theorem m4_rho_x6 : rhoMat *ᵥ x6 = -(x1 - x2) := by decide

theorem m4_rho_comm_CGDot12 {g : GL6} (hg : g ∈ CGDot12) : g * rhoDot = rhoDot * g := by
  have hgf : g * fDot = fDot * g :=
    Subgroup.mem_centralizer_singleton_iff.1 (s6_CGDot12_le_DDot hg).2
  have hA : (g : M6) * fMat = fMat * (g : M6) := m4_val_comm hgf
  have h6 : (g : M6) *ᵥ x6 = x6 := (mem_GDot_iff.1 hg.1).2
  have h12 : (g : M6) *ᵥ (x1 - x2) = x1 - x2 :=
    (quat_smul_def g _).symm.trans (MulAction.mem_stabilizer_iff.1 hg.2)
  have key : ∀ v : V6, fMat *ᵥ v = v →
      (g : M6) *ᵥ (rhoMat *ᵥ v) = rhoMat *ᵥ ((g : M6) *ᵥ v) := by
    intro v hv
    have h1 : fMat *ᵥ ((g : M6) *ᵥ v) = (g : M6) *ᵥ v := by rw [m4_mulVec_comm hA, hv]
    rw [m4_rho_neg v hv, m4_rho_neg _ h1, Matrix.mulVec_neg]
  apply Units.ext
  show (g : M6) * rhoMat = rhoMat * (g : M6)
  apply m4_ext_basis
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact key _ (by decide)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h12, m4_rho_sub, h6]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact key _ (by decide)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact key _ (by decide)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact key _ (by decide)
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h6, m4_rho_x6, Matrix.mulVec_neg, h12]

theorem RDot_inf_cen : RDot ⊓ Subgroup.centralizer ((CGDot12 : Subgroup GL6) : Set GL6) =
    Subgroup.zpowers rhoDot := by
  apply le_antisymm
  · rintro r ⟨hr, hcen⟩
    have hrC := RDot_le hr
    exact m4_cen_mem_Y hrC.1 (Subgroup.mem_centralizer_singleton_iff.1 hrC.2) fun g hg =>
      (Subgroup.mem_centralizer_iff.1 hcen g hg).symm
  · refine le_inf m4_Y_le_R (Subgroup.zpowers_le.2 ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact m4_rho_comm_CGDot12 hg

theorem m4_DDot_le_C : DDot ≤ MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
  fun _ hd => ⟨(mem_GDot_iff.1 hd.1).1, hd.2⟩

theorem m4_orbit_w : ∀ v : V6, fMat *ᵥ v = -v → qV v = -1 →
    v = x1 - x2 ∨ v = -(x1 - x2) ∨ v = x6 ∨ v = -x6 := by decide +kernel

theorem RDot_mul_DDot
    (hcard : Nat.card ↥(MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = 2880) :
    (RDot : Set GL6) * (DDot : Set GL6) =
      ((MDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) : Set GL6) := by
  have _ := hcard
  ext g
  constructor
  · rintro ⟨r, hr, d, hd, rfl⟩
    exact Subgroup.mul_mem _ (RDot_le hr) (m4_DDot_le_C hd)
  · intro hg
    have hgM : g ∈ MDot := hg.1
    have hgf : g * fDot = fDot * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
    have key : ∀ y ∈ Subgroup.zpowers rhoDot, ((y : GL6) : M6) *ᵥ x6 = (g : M6) *ᵥ x6 →
        g ∈ (RDot : Set GL6) * (DDot : Set GL6) := by
      intro y hy hyg
      refine ⟨y, m4_Y_le_R hy, y⁻¹ * g, ?_, by simp⟩
      refine ⟨mem_GDot_iff.2 ⟨MDot.mul_mem (MDot.inv_mem (m4_Y_le_MDot hy)) hgM, ?_⟩,
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hyg, mono_inv_mulVec]
      · exact (((Commute.inv_left (show Commute y fDot from m4_Y_comm_f hy)).mul_left
          (show Commute g fDot from hgf)) : Commute (y⁻¹ * g) fDot).eq
    have hv : fMat *ᵥ ((g : M6) *ᵥ x6) = -((g : M6) *ᵥ x6) := by
      have hA : (g : M6) * fMat = fMat * (g : M6) := m4_val_comm hgf
      rw [m4_mulVec_comm hA, show fMat *ᵥ x6 = -x6 by decide, Matrix.mulVec_neg]
    have hq : qV ((g : M6) *ᵥ x6) = -1 := by
      rw [qV_mulVec_of_mem_OVq (MDot_le_OVq hgM)]
      exact qV_x6
    rcases m4_orbit_w _ hv hq with h | h | h | h
    · exact key (rhoDot ^ 3) (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3) (by
        rw [h, Units.val_pow_eq_pow_val, m4_rhoDot_val]; decide)
    · exact key rhoDot (Subgroup.mem_zpowers _) (by rw [h, m4_rhoDot_val, m4_rho_x6])
    · exact key 1 (Subgroup.one_mem _) (by rw [h]; simp)
    · exact key fDot (by rw [← m4_rho_sq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)
        (by rw [h]; decide)

theorem m4_card_Z2S4 : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) = 48 := by
  have h24 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
    simp [Nat.card_zmod]
  rw [Nat.card_prod, h2, h24]

@[expose] def m4Z (a : GL6) : Subgroup GL6 := Subgroup.zpowers a ⊔ Subgroup.zpowers fDot

structure M4Data (Mi : Subgroup GL6) (a g1 g2 g3 : GL6) : Prop where
  card : Nat.card ↥(EDot Mi) = 96
  Mi_le : Mi ≤ MDot
  T_le : TDot ≤ Mi
  f_mem : fDot ∈ EDot Mi
  a_mem : a ∈ EDot Mi
  g1_mem : g1 ∈ EDot Mi
  g2_mem : g2 ∈ EDot Mi
  g3_mem : g3 ∈ EDot Mi
  a_cen : ∀ x ∈ EDot Mi, x * a = a * x
  a_sq : a * a = 1
  a_ne : a ≠ 1
  a_ne_f : a ≠ fDot
  cox : CFSG.Permutation.SymmetricCoxeter.IsCoxeterA 3 (aiGen (a * g1) (a * g2) (a * g3))
  ne : (a * g1) * (a * g3) ≠ 1
  a_x6 : (a : M6) *ᵥ x6 = x6
  x1' : ((a * g1 : GL6) : M6) *ᵥ x6 = x6
  x2' : ((a * g2 : GL6) : M6) *ᵥ x6 = x6
  x3' : ((a * g3 : GL6) : M6) *ᵥ x6 = x6
  rho1 : rhoDot * (a * g1) = (a * g1) * rhoDot
  rho2 : rhoDot * (a * g2) = (a * g2) * rhoDot
  rho3 : rhoDot * (a * g3) = (a * g3) * rhoDot
  rho_a : rhoDot * a * rhoDot⁻¹ = a * fDot
  rho_inv_a : rhoDot⁻¹ * a * (rhoDot⁻¹)⁻¹ = a * fDot
  a_rho : a * rhoDot * a⁻¹ = rhoDot⁻¹
  delta_inj : ∀ d : DihedralGroup 4, m4D4Fun rhoDot a d = 1 → d = 1

namespace M4Data

variable {Mi : Subgroup GL6} {a g1 g2 g3 : GL6} (D : M4Data Mi a g1 g2 g3)

include D

theorem a_comm_f : a * fDot = fDot * a :=
  Subgroup.mem_centralizer_singleton_iff.1 D.a_mem.2

@[expose] def psi : Equiv.Perm (Fin 4) →* GL6 := aiPsi D.cox

theorem psi_injective : Function.Injective D.psi := aiPsi_injective D.cox D.ne

theorem mem_E : ∀ σ, D.psi σ ∈ EDot Mi := aiPsi_mem D.cox
  ((EDot Mi).mul_mem D.a_mem D.g1_mem) ((EDot Mi).mul_mem D.a_mem D.g2_mem)
    ((EDot Mi).mul_mem D.a_mem D.g3_mem)

theorem psi_rho (σ : Equiv.Perm (Fin 4)) : rhoDot * D.psi σ = D.psi σ * rhoDot := by
  have := aiPsi_mem D.cox (E := Subgroup.centralizer ({rhoDot} : Set GL6))
    (Subgroup.mem_centralizer_singleton_iff.2 D.rho1.symm)
    (Subgroup.mem_centralizer_singleton_iff.2 D.rho2.symm)
    (Subgroup.mem_centralizer_singleton_iff.2 D.rho3.symm) σ
  exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm

theorem psi_x6 (σ : Equiv.Perm (Fin 4)) : ((D.psi σ : GL6) : M6) *ᵥ x6 = x6 := by
  have hst : ∀ g : GL6, ((g : GL6) : M6) *ᵥ x6 = x6 → g ∈ MulAction.stabilizer GL6 x6 :=
    fun g hg => MulAction.mem_stabilizer_iff.2 ((quat_smul_def g _).trans hg)
  have := aiPsi_mem D.cox (E := MulAction.stabilizer GL6 x6) (hst _ D.x1') (hst _ D.x2')
    (hst _ D.x3') σ
  rw [← quat_smul_def]
  exact MulAction.mem_stabilizer_iff.1 this

theorem Z_le : m4Z a ≤ EDot Mi :=
  sup_le (Subgroup.zpowers_le.2 D.a_mem) (Subgroup.zpowers_le.2 D.f_mem)

theorem Z_central : ∀ z ∈ m4Z a, ∀ x ∈ EDot Mi, x * z = z * x := by
  have hC : m4Z a ≤ Subgroup.centralizer (EDot Mi : Set GL6) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun x hx => D.a_cen x hx
    · exact Subgroup.mem_centralizer_iff.2 fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.1 hx.2
  intro z hz x hx
  exact (Subgroup.mem_centralizer_iff.1 (hC hz)) x hx

theorem card_Z : Nat.card ↥(m4Z a) = 4 := by
  have hf2 : fDot * fDot = 1 := mono_fDot_mul_self
  have hAB : Subgroup.zpowers a ⊓ Subgroup.zpowers fDot = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    rcases mono_mem_zpowers_involution D.a_sq hxa with rfl | rfl
    · exact Subgroup.one_mem _
    · rcases mono_mem_zpowers_involution hf2 hxb with h | h
      · exact absurd h D.a_ne
      · exact absurd h D.a_ne_f
  have hnorm : Subgroup.zpowers fDot ≤ Subgroup.normalizer (Subgroup.zpowers a : Set GL6) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_)
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute a fDot from D.a_comm_f) k).eq
  unfold m4Z
  rw [mono_card_sup_of_le_normalizer _ _ hAB hnorm, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact D.a_sq) D.a_ne,
    orderOf_eq_prime (by rw [pow_two]; exact hf2) mono_fDot_ne_one]

theorem Z_inf_K : m4Z a ⊓ D.psi.range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxZ, ⟨σ, rfl⟩⟩
  have hσ : σ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    apply D.psi_injective
    rw [map_mul, map_mul]
    exact (D.Z_central _ hxZ _ (D.mem_E τ)).symm
  rw [hσ, map_one]
  exact Subgroup.one_mem _

theorem card_K : Nat.card ↥D.psi.range = 24 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective D.psi_injective).toEquiv, Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem K_le_E : D.psi.range ≤ EDot Mi := by
  rintro _ ⟨σ, rfl⟩
  exact D.mem_E σ

theorem Z_sup_K : m4Z a ⊔ D.psi.range = EDot Mi := by
  have hle : m4Z a ⊔ D.psi.range ≤ EDot Mi := sup_le D.Z_le D.K_le_E
  apply Subgroup.eq_of_le_of_card_ge hle
  have hnorm : D.psi.range ≤ Subgroup.normalizer (m4Z a : Set GL6) := by
    rintro _ ⟨σ, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz => ?_)
    exact (D.Z_central z hz _ (D.mem_E σ)).symm
  rw [mono_card_sup_of_le_normalizer _ _ D.Z_inf_K hnorm, D.card_Z, D.card_K, D.card]

theorem rho_normalizer : rhoDot ∈ Subgroup.normalizer (EDot Mi : Set GL6) := by
  rw [← D.Z_sup_K]
  have conj : ∀ g : GL6, g * a * g⁻¹ = a * fDot → g * fDot * g⁻¹ = fDot →
      (∀ σ, g * D.psi σ = D.psi σ * g) →
      ∀ s ∈ m4Z a ⊔ D.psi.range, g * s * g⁻¹ ∈ m4Z a ⊔ D.psi.range := by
    intro g hga hgf hgK
    apply mono_conj_mem_sup
    · intro x hx
      apply Subgroup.mem_sup_left
      refine mono_conj_mem_sup (X := Subgroup.zpowers a) (Y := Subgroup.zpowers fDot) ?_ ?_ x hx
      · intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        rw [← conj_zpow, hga]
        exact Subgroup.zpow_mem _ (Subgroup.mul_mem_sup (Subgroup.mem_zpowers a)
          (Subgroup.mem_zpowers fDot)) k
      · intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        rw [← conj_zpow, hgf]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩)
    · intro y hy
      obtain ⟨σ, rfl⟩ := hy
      apply Subgroup.mem_sup_right
      refine ⟨σ, ?_⟩
      rw [hgK σ, mul_inv_cancel_right]
  have hfc : Commute rhoDot fDot := m4_rho_comm_f
  refine mono_mem_normalizer_of_conj
    (conj rhoDot D.rho_a (by rw [hfc.eq, mul_inv_cancel_right]) D.psi_rho) (fun s hs => ?_)
  have := conj rhoDot⁻¹ D.rho_inv_a (by rw [hfc.inv_left.eq, mul_inv_cancel_right])
    (fun σ => (Commute.inv_left (show Commute rhoDot (D.psi σ) from D.psi_rho σ)).eq) s hs
  rwa [inv_inv] at this

theorem a_comm_psi (σ : Equiv.Perm (Fin 4)) : a * D.psi σ = D.psi σ * a :=
  (D.a_cen _ (D.mem_E σ)).symm

@[expose] def delta : DihedralGroup 4 →* GL6 :=
  m4D4Lift rhoDot a m4_rho_pow_four (by rw [pow_two]; exact D.a_sq) D.a_rho

theorem delta_comm (d : DihedralGroup 4) (σ : Equiv.Perm (Fin 4)) :
    Commute (D.delta d) (D.psi σ) := by
  have hmem : D.delta d ∈ Subgroup.centralizer (D.psi.range : Set GL6) := by
    refine m4D4Lift_mem (H := Subgroup.centralizer (D.psi.range : Set GL6)) ?_ ?_ d
    · refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨τ, rfl⟩
      exact (D.psi_rho τ).symm
    · refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨τ, rfl⟩
      exact D.a_cen _ (D.mem_E τ)
  exact (Subgroup.mem_centralizer_iff.1 hmem (D.psi σ) ⟨σ, rfl⟩).symm

@[expose] def Phi : DihedralGroup 4 × Equiv.Perm (Fin 4) →* GL6 :=
  MonoidHom.noncommCoprod D.delta D.psi fun d σ => D.delta_comm d σ

theorem Phi_injective : Function.Injective D.Phi := by
  rw [injective_iff_map_eq_one]
  rintro ⟨d, σ⟩ h
  have h1 : D.delta d * D.psi σ = 1 := h
  have h2 : D.psi σ = (D.delta d)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hσ : σ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    apply D.psi_injective
    rw [map_mul, map_mul, h2]
    exact (Commute.inv_left (D.delta_comm d τ)).eq
  subst hσ
  rw [map_one, mul_one] at h1
  have := D.delta_inj d h1
  rw [this]
  rfl

theorem Z_le_delta : m4Z a ≤ D.delta.range := by
  refine sup_le (Subgroup.zpowers_le.2 ⟨DihedralGroup.sr 0, ?_⟩)
    (Subgroup.zpowers_le.2 ⟨DihedralGroup.r 2, ?_⟩)
  · show a * quatZpow rhoDot (0 : ZMod 4) = a
    rw [quatZpow_zero, mul_one]
  · show rhoDot ^ ((2 : ZMod 4).val) = fDot
    rw [show (2 : ZMod 4).val = 2 from rfl, m4_rho_sq]

theorem Y_le_delta : Subgroup.zpowers rhoDot ≤ D.delta.range := by
  refine Subgroup.zpowers_le.2 ⟨DihedralGroup.r 1, ?_⟩
  show rhoDot ^ ((1 : ZMod 4).val) = rhoDot
  rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]

theorem Tf_le_E : TDot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≤ EDot Mi :=
  fun _ hg => ⟨D.T_le hg.1, hg.2⟩

theorem E_le_range : EDot Mi ≤ D.delta.range ⊔ D.psi.range := by
  rw [← D.Z_sup_K]
  exact sup_le_sup_right D.Z_le_delta _

theorem Phi_range : D.Phi.range = EDot Mi ⊔ RDot := by
  rw [Phi, MonoidHom.noncommCoprod_range]
  apply le_antisymm
  · refine sup_le ?_ (D.K_le_E.trans le_sup_left)
    rintro _ ⟨d, rfl⟩
    exact m4D4Lift_mem (H := EDot Mi ⊔ RDot) (Subgroup.mem_sup_right m4_rho_mem_R)
      (Subgroup.mem_sup_left D.a_mem) d
  · refine sup_le D.E_le_range (sup_le ?_ ?_)
    · exact D.Tf_le_E.trans D.E_le_range
    · exact D.Y_le_delta.trans le_sup_left

theorem EDot_sup_RDot_iso :
    Nonempty (↥(EDot Mi ⊔ RDot) ≃* DihedralGroup 4 × Equiv.Perm (Fin 4)) :=
  ⟨((MonoidHom.ofInjective D.Phi_injective).trans (MulEquiv.subgroupCongr D.Phi_range)).symm⟩

theorem R_normalizer : RDot ≤ Subgroup.normalizer (EDot Mi : Set GL6) := by
  refine sup_le ?_ (Subgroup.zpowers_le.2 D.rho_normalizer)
  exact D.Tf_le_E.trans Subgroup.le_normalizer

theorem card_a : Nat.card ↥(Subgroup.zpowers a) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact D.a_sq) D.a_ne]

@[expose] def eA : Multiplicative (ZMod 2) ≃* ↥(Subgroup.zpowers a) :=
  (AddEquiv.toMultiplicative (ZMod.ringEquivCongr D.card_a.symm).toAddEquiv).trans
    (zmodCyclicMulEquiv (Subgroup.isCyclic_zpowers a))

@[expose] def ha : Multiplicative (ZMod 2) →* GL6 :=
  (Subgroup.zpowers a).subtype.comp D.eA.toMonoidHom

theorem ha_injective : Function.Injective D.ha := Subtype.val_injective.comp D.eA.injective

theorem ha_mem (u : Multiplicative (ZMod 2)) : D.ha u ∈ Subgroup.zpowers a := (D.eA u).2

theorem ha_range : D.ha.range = Subgroup.zpowers a := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact D.ha_mem u
  · refine Subgroup.zpowers_le.2 ?_
    obtain ⟨u, hu⟩ := D.eA.surjective ⟨a, Subgroup.mem_zpowers a⟩
    exact ⟨u, congrArg Subtype.val hu⟩

theorem ha_comm (u : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 4)) :
    Commute (D.ha u) (D.psi σ) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (D.ha_mem u)
  rw [← hk]
  exact Commute.zpow_left (show Commute a (D.psi σ) from D.a_comm_psi σ) k

@[expose] def PhiD : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) →* GL6 :=
  MonoidHom.noncommCoprod D.ha D.psi fun u σ => D.ha_comm u σ

theorem PhiD_injective : Function.Injective D.PhiD := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, σ⟩ h
  have h1 : D.ha u * D.psi σ = 1 := h
  have h2 : D.psi σ = (D.ha u)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hσ : σ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro τ
    apply D.psi_injective
    rw [map_mul, map_mul, h2]
    exact (Commute.inv_left (D.ha_comm u τ)).eq
  subst hσ
  rw [map_one, mul_one] at h1
  have := D.ha_injective (h1.trans (map_one D.ha).symm)
  rw [this]
  rfl

theorem PhiD_range : D.PhiD.range = GDot ⊓ Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  have hle : D.PhiD.range ≤ GDot ⊓ Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
    rw [PhiD, MonoidHom.noncommCoprod_range, D.ha_range]
    refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
    · exact ⟨⟨mem_GDot_iff.2 ⟨D.Mi_le D.a_mem.1, D.a_x6⟩, D.a_mem.1⟩, D.a_mem.2⟩
    · rintro _ ⟨σ, rfl⟩
      exact ⟨⟨mem_GDot_iff.2 ⟨D.Mi_le (D.mem_E σ).1, D.psi_x6 σ⟩, (D.mem_E σ).1⟩,
        (D.mem_E σ).2⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  have hD : GDot ⊓ Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≤ EDot Mi :=
    fun _ hg => ⟨hg.1.2, hg.2⟩
  have hne : GDot ⊓ Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6) ≠ EDot Mi := by
    intro h
    have hf : fDot ∈ GDot ⊓ Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
      rw [h]
      exact D.f_mem
    have := (mem_GDot_iff.1 hf.1.1).2
    revert this
    decide
  have h2 := m4_two_mul_card_le hD hne
  rw [D.card] at h2
  have h3 : Nat.card ↥D.PhiD.range = 48 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective D.PhiD_injective).toEquiv, m4_card_Z2S4]
  omega

theorem DDot_iso : Nonempty (↥(GDot ⊓ Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ≃*
    Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :=
  ⟨((MonoidHom.ofInjective D.PhiD_injective).trans (MulEquiv.subgroupCongr D.PhiD_range)).symm⟩

end M4Data

theorem m4Data1 : M4Data M1Dot zDot aiT1 aiT2 aiT3 where
  card := ai_card_E1
  Mi_le := fun _ hg => hg.1
  T_le := fun _ hg => (TDot_le_M12 hg).1
  f_mem := ai_fDot_mem_E1
  a_mem := ai_zDot_mem_E1
  g1_mem := aiT1_mem_E1
  g2_mem := aiT2_mem_E1
  g3_mem := aiT3_mem_E1
  a_cen := fun _ hg => Subgroup.mem_centralizer_singleton_iff.1 hg.1.2
  a_sq := zDot_mul_self
  a_ne := by decide +kernel
  a_ne_f := by decide +kernel
  cox := ai_isCoxeterA_gen (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  ne := by decide +kernel
  a_x6 := by decide +kernel
  x1' := by decide +kernel
  x2' := by decide +kernel
  x3' := by decide +kernel
  rho1 := by decide +kernel
  rho2 := by decide +kernel
  rho3 := by decide +kernel
  rho_a := by decide +kernel
  rho_inv_a := by decide +kernel
  a_rho := by decide +kernel
  delta_inj := by decide +kernel

theorem m4Data2 : M4Data M2Dot tDot aiU1 aiU2 aiU3 where
  card := ai_card_E2
  Mi_le := fun _ hg => hg.1
  T_le := fun _ hg => (TDot_le_M12 hg).2
  f_mem := ai_fDot_mem_E2
  a_mem := ai_tDot_mem_E2
  g1_mem := aiU1_mem_E2
  g2_mem := aiU2_mem_E2
  g3_mem := aiU3_mem_E2
  a_cen := fun _ hg => ai_tDot_central hg.1 (ai_comm_of_mem_EDot hg)
  a_sq := tDot_mul_self
  a_ne := tDot_ne_one
  a_ne_f := by decide +kernel
  cox := ai_isCoxeterA_gen (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  ne := by decide +kernel
  a_x6 := by decide +kernel
  x1' := by decide +kernel
  x2' := by decide +kernel
  x3' := by decide +kernel
  rho1 := by decide +kernel
  rho2 := by decide +kernel
  rho3 := by decide +kernel
  rho_a := by decide +kernel
  rho_inv_a := by decide +kernel
  a_rho := by decide +kernel
  delta_inj := by decide +kernel

theorem m4_data (Mi : Subgroup GL6) (hMi : Mi = M1Dot ∨ Mi = M2Dot) :
    ∃ a g1 g2 g3 : GL6, M4Data Mi a g1 g2 g3 := by
  rcases hMi with rfl | rfl
  · exact ⟨_, _, _, _, m4Data1⟩
  · exact ⟨_, _, _, _, m4Data2⟩

theorem RDot_le_normalizer_EDot (Mi : Subgroup GL6) (hMi : Mi = M1Dot ∨ Mi = M2Dot) :
    RDot ≤ Subgroup.normalizer (EDot Mi : Set GL6) := by
  obtain ⟨a, g1, g2, g3, D⟩ := m4_data Mi hMi
  exact D.R_normalizer

theorem EDot_sup_RDot (Mi : Subgroup GL6) (hMi : Mi = M1Dot ∨ Mi = M2Dot) :
    Nonempty (↥(EDot Mi ⊔ RDot) ≃* DihedralGroup 4 × Equiv.Perm (Fin 4)) := by
  obtain ⟨a, g1, g2, g3, D⟩ := m4_data Mi hMi
  exact D.EDot_sup_RDot_iso

theorem DDot1_equiv : Nonempty (↥(GDot ⊓ M1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ≃*
    Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :=
  m4Data1.DDot_iso

theorem DDot2_equiv : Nonempty (↥(GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ≃*
    Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :=
  m4Data2.DDot_iso

theorem m4_s6_mem_D2 (j : ℕ) (τ : Equiv.Perm (Fin 6)) (hj : j < 5)
    (h : ∀ i : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧
      ((s6Gen j : GL6) : M6) *ᵥ xvec i = c • xvec (τ i)) :
    s6Gen j ∈ GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  have hD := s6Gen_mem_DDot j hj
  exact ⟨⟨hD.1, (mem_GDot_iff.1 hD.1).1, mono_mem_stabilizer_Lambda τ h⟩, hD.2⟩

@[expose] def m4X : GL6 :=
  s6Gen 1 * s6Gen 3 * s6Gen 2 * s6Gen 1 * s6Gen 4 * s6Gen 3

theorem m4X_mem_D1 : m4X ∈ GDot ⊓ M1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  have hX : m4X ∈ DDot := by
    unfold m4X
    exact DDot.mul_mem (DDot.mul_mem (DDot.mul_mem (DDot.mul_mem (DDot.mul_mem
      (s6Gen_mem_DDot 1 (by norm_num)) (s6Gen_mem_DDot 3 (by norm_num)))
      (s6Gen_mem_DDot 2 (by norm_num))) (s6Gen_mem_DDot 1 (by norm_num)))
      (s6Gen_mem_DDot 4 (by norm_num))) (s6Gen_mem_DDot 3 (by norm_num))
  exact ⟨⟨hX.1, quat_mem_M1Dot (mem_GDot_iff.1 hX.1).1 (by decide +kernel)⟩, hX.2⟩

theorem m4_s3_eq : s6Gen 3 = s6Gen 2 * (m4X * s6Gen 1 * m4X⁻¹) * s6Gen 2 := by decide +kernel

theorem DDot1_sup_DDot2 : (GDot ⊓ M1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ⊔
    (GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = DDot := by
  apply le_antisymm
  · exact sup_le (fun _ hg => ⟨hg.1.1, hg.2⟩) (fun _ hg => ⟨hg.1.1, hg.2⟩)
  · rw [← s6Hom_range_eq, MonoidHom.range_eq_map,
      ← CFSG.Permutation.SymmetricCoxeter.closure_adjSwap 5, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hi' : i < 5 := hi
    rw [s6Hom_adjSwap hi']
    have h0 : s6Gen 0 ∈ GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
      m4_s6_mem_D2 0 (Equiv.swap 0 1 * Equiv.swap 3 4) (by norm_num) (by decide +kernel)
    have h1 : s6Gen 1 ∈ GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
      m4_s6_mem_D2 1 (Equiv.swap 0 1 * Equiv.swap 2 4) (by norm_num) (by decide +kernel)
    have h2 : s6Gen 2 ∈ GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
      m4_s6_mem_D2 2 (Equiv.swap 0 1 * Equiv.swap 3 4) (by norm_num) (by decide +kernel)
    have h4 : s6Gen 4 ∈ GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) :=
      m4_s6_mem_D2 4 1 (by norm_num) (by decide +kernel)
    have hJ : ∀ x ∈ GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6),
        x ∈ (GDot ⊓ M1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ⊔
          (GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) :=
      fun x hx => Subgroup.mem_sup_right hx
    have hX : m4X ∈ (GDot ⊓ M1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ⊔
          (GDot ⊓ M2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) :=
      Subgroup.mem_sup_left m4X_mem_D1
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact hJ _ h0
    · exact hJ _ h1
    · exact hJ _ h2
    · rw [m4_s3_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hJ _ h2)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hX (hJ _ h1)) (Subgroup.inv_mem _ hX)))
        (hJ _ h2)
    · exact hJ _ h4

theorem m4_pow_mulVec_neg {x : GL6} {v : V6} (hx : (x : M6) *ᵥ v = -v) (n : ℕ) :
    ((x ^ n : GL6) : M6) *ᵥ v = ((-1 : ZMod 3) ^ n) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_neg, ih, pow_succ,
      mul_neg_one, neg_smul]

theorem oTwoRes_DDot : oTwoRes DDot = CGDot12 := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxD, m, hm, hxm⟩
    rcases s6_DDot_mulVec hxD with h | h
    · exact ⟨hxD.1, MulAction.mem_stabilizer_iff.2 ((quat_smul_def x _).trans h)⟩
    · exfalso
      have h1 := m4_pow_mulVec_neg (x := x) (v := x1 - x2) h m
      rw [hxm, Units.val_one, Matrix.one_mulVec, hm.neg_one_pow] at h1
      revert h1
      decide
  · rw [s6_CGDot12_eq_map_alternatingGroup, ← Equiv.Perm.closure_three_cycles_eq_alternating,
      MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨σ, hσ, rfl⟩
    have h3 : σ ^ 3 = 1 := by
      have := pow_orderOf_eq_one σ
      rwa [hσ.orderOf] at this
    refine ⟨s6Hom_range_le ⟨σ, rfl⟩, 3, by decide, ?_⟩
    rw [← map_pow, h3, map_one]

@[expose] def m4GMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 1, 0, 0, 0, 1; 2, 2, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    1, 2, 0, 0, 0, 0]

@[expose] def m4GInvMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 2, 0, 0, 0, 2; 1, 2, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    2, 2, 0, 0, 0, 0]

theorem m4GMat_mul : m4GMat * m4GInvMat = 1 := by decide

theorem m4GMat_mul' : m4GInvMat * m4GMat = 1 := by decide

@[expose] def m4G : GL6 := ⟨m4GMat, m4GInvMat, m4GMat_mul, m4GMat_mul'⟩

theorem m4G_mem : m4G ∈ MDot :=
  quat_mem_MDot_of_refl [quatRV ![1, 0, 0, 0, 0, 0], quatRV ![1, 2, 0, 0, 0, 1]] m4G
    (by decide) (by decide) (by decide)

theorem conj_zDot_fDot_tDot_zDot : ∃ g ∈ MDot, g * zDot * g⁻¹ = fDot * tDot * zDot :=
  ⟨m4G, m4G_mem, by decide +kernel⟩

theorem m4_mem_sup_f {CQ : Subgroup GL6} (hf : ∀ x ∈ CQ, x * fDot = fDot * x) {x : GL6}
    (hx : x ∈ Subgroup.zpowers fDot ⊔ CQ) : ∃ q ∈ CQ, x = q ∨ x = q * fDot := by
  have hnorm : Subgroup.zpowers fDot ≤ Subgroup.normalizer (CQ : Set GL6) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => hf x hx)
  have hx2 : x ∈ ((CQ ⊔ Subgroup.zpowers fDot : Subgroup GL6) : Set GL6) := by
    rw [SetLike.mem_coe, sup_comm]
    exact hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hx2
  obtain ⟨q, hq, y, hy, rfl⟩ := hx2
  rcases mono_mem_zpowers_involution mono_fDot_mul_self hy with rfl | rfl
  · exact ⟨q, hq, Or.inl (mul_one q)⟩
  · exact ⟨q, hq, Or.inr rfl⟩

theorem m4_normalizes {Mi : Subgroup GL6} (hT : TDot ≤ Mi) {g : GL6} (hgT : g ∈ TDot)
    (hgf : g * fDot = fDot * g) : g ∈ Subgroup.normalizer (ADot Mi : Set GL6) := by
  have hgE : g ∈ EDot Mi := ⟨hT hgT, Subgroup.mem_centralizer_singleton_iff.2 hgf⟩
  have hgiE : g⁻¹ ∈ EDot Mi := (EDot Mi).inv_mem hgE
  refine mono_mem_normalizer_of_conj (fun s hs => mono_pCoreOf_conj _ hgE hs) (fun s hs => ?_)
  have := mono_pCoreOf_conj _ hgiE hs
  rwa [inv_inv] at this

theorem m4_comm_A2 : ∀ J : Finset (Fin 6), J ⊆ Iset → Even J.card →
    ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) →
    ((m4A2 * eJ J * m4A2⁻¹ * (eJ J)⁻¹ = 1 ∨ m4A2 * eJ J * m4A2⁻¹ * (eJ J)⁻¹ = eJ {2, 3}) ∧
      (m4A2 * (eJ J * fDot) * m4A2⁻¹ * (eJ J * fDot)⁻¹ = 1 ∨
        m4A2 * (eJ J * fDot) * m4A2⁻¹ * (eJ J * fDot)⁻¹ = eJ {2, 3})) := by
  decide +kernel

theorem m4_comm_A1 : ∀ k : Fin 8,
    ((m4A2 * aiE k * m4A2⁻¹ * (aiE k)⁻¹ = 1 ∨ m4A2 * aiE k * m4A2⁻¹ * (aiE k)⁻¹ = eJ {2, 3}) ∧
      (m4A2 * (aiE k * fDot) * m4A2⁻¹ * (aiE k * fDot)⁻¹ = 1 ∨
        m4A2 * (aiE k * fDot) * m4A2⁻¹ * (aiE k * fDot)⁻¹ = eJ {2, 3})) := by
  decide +kernel

theorem m4_exists_A1 : ∃ k : Fin 8, m4A2 * aiE k * m4A2⁻¹ * (aiE k)⁻¹ = eJ {2, 3} := by
  decide +kernel

theorem exists_transvection (Mi : Subgroup GL6) (hMi : Mi = M1Dot ∨ Mi = M2Dot) :
    ∃ g ∈ TDot ⊓ Subgroup.centralizer ({tDot} : Set GL6),
      g ∈ Subgroup.normalizer (ADot Mi : Set GL6) ∧
      ∃ w : GL6, w ≠ 1 ∧ (∃ a ∈ ADot Mi, g * a * g⁻¹ * a⁻¹ = w) ∧
        ∀ a ∈ ADot Mi, g * a * g⁻¹ * a⁻¹ = 1 ∨ g * a * g⁻¹ * a⁻¹ = w := by
  have hgf : m4A2 * fDot = fDot * m4A2 := by decide +kernel
  rcases hMi with rfl | rfl
  · refine ⟨m4A2, m4_A2_mem, m4_normalizes (fun _ hg => (TDot_le_M12 hg).1) m4_A2_mem.1 hgf,
      eJ {2, 3}, by decide +kernel, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := m4_exists_A1
      refine ⟨aiE k, ?_, hk⟩
      rw [ADot_M1Dot_eq]
      exact Subgroup.mem_sup_right (ai_mem_CQ1_iff.2 ⟨k, rfl⟩)
    · intro x hx
      rw [ADot_M1Dot_eq] at hx
      obtain ⟨q, hq, hxq⟩ := m4_mem_sup_f
        (CQ := Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx.2) hx
      obtain ⟨k, rfl⟩ := ai_mem_CQ1_iff.1 hq
      rcases hxq with rfl | rfl
      · exact (m4_comm_A1 k).1
      · exact (m4_comm_A1 k).2
  · refine ⟨m4A2, m4_A2_mem, m4_normalizes (fun _ hg => (TDot_le_M12 hg).2) m4_A2_mem.1 hgf,
      eJ {2, 3}, by decide +kernel, ?_, ?_⟩
    · refine ⟨eJ {2, 4}, ai_eJ_mem_A (by decide) (by decide) (by decide), by decide +kernel⟩
    · intro x hx
      rw [ADot_M2Dot_eq] at hx
      obtain ⟨q, hq, hxq⟩ := m4_mem_sup_f
        (CQ := Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.1 hx.2) hx
      have hq' : q ∈ ((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) :
          Set GL6) := hq
      rw [Q2Dot_inf_centralizer_coe] at hq'
      obtain ⟨J, hJ, hev, h01, rfl⟩ := hq'
      rcases hxq with rfl | rfl
      · exact (m4_comm_A2 J hJ hev h01).1
      · exact (m4_comm_A2 J hJ hev h01).2

end

end CFSG.Quasithin.SimsF5
