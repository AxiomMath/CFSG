module

public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.He

open Native Matrix
open CFSG.Sporadic.Th (Rep idx idx_of_lt idx_lt allIn_eq_true orbit_eq_image orbitEquiv)
open CFSG.Sporadic.Th.Native (Table ap)

noncomputable instance vecAction :
    MulAction J (Fin 50 → ZMod 7) where
  smul g v := mat g *ᵥ v
  one_smul v := by
    show mat 1 *ᵥ v = v
    rw [mat_one, Matrix.one_mulVec]
  mul_smul g h v := by
    show mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v)
    rw [mat_mul, Matrix.mulVec_mulVec]

theorem vec_smul_def
    (g : J) (v : Fin 50 → ZMod 7) : g • v = mat g *ᵥ v := rfl

@[expose] noncomputable def pt (k : ℕ) : Fin 50 → ZMod 7 := toVec 7 50 orb.keys[k]!

theorem a_smul_pt
    {i : ℕ} (hi : i < orb.keys.size) : a • pt i = pt (ap orb.alpha i) := by
  rw [vec_smul_def, mat_a, pt, pt, ← toMat_matA, (vecFacts.alpha i hi).2]

theorem b_smul_pt
    {i : ℕ} (hi : i < orb.keys.size) : b • pt i = pt (ap orb.beta i) := by
  rw [vec_smul_def, mat_b, pt, pt, ← toMat_matB, (vecFacts.beta i hi).2]

theorem pt_inj
    {i j : ℕ} (hi : i < orb.keys.size) (hj : j < orb.keys.size) (h : pt i = pt j) :
    i = j :=
  vecFacts.inj i hi j hj h

theorem orbit_hyps :
    (∀ i < orb.keys.size, ap orb.alpha i < orb.keys.size ∧ a • pt i = pt (ap orb.alpha i)) ∧
    (∀ i < orb.keys.size, ap orb.beta i < orb.keys.size ∧ b • pt i = pt (ap orb.beta i)) :=
  ⟨fun i hi => ⟨(vecFacts.alpha i hi).1, a_smul_pt hi⟩,
    fun i hi => ⟨(vecFacts.beta i hi).1, b_smul_pt hi⟩⟩

theorem orbit_eq :
    MulAction.orbit J (pt 0) = pt '' Set.Iio orb.keys.size :=
  orbit_eq_image closure_ab vecFacts.size_pos pt orbit_hyps.1 orbit_hyps.2 (ap orb.par)
    (ap orb.lab) vecFacts.tree

@[expose] noncomputable def ptEquiv :
    Fin 8330 ≃ MulAction.orbit J (pt 0) :=
  (Fin.castOrderIso orb_size.symm).toEquiv.trans
    (orbitEquiv closure_ab vecFacts.size_pos pt (fun _ hi _ hj h => pt_inj hi hj h)
      orbit_hyps.1 orbit_hyps.2 (ap orb.par) (ap orb.lab) vecFacts.tree)

theorem ptEquiv_apply (i : Fin 8330) : (ptEquiv i : Fin 50 → ZMod 7) = pt i.val := rfl

noncomputable instance idxInst :
    MulAction J (Fin 8330) := ptEquiv.mulAction J

theorem smul_def
    (g : J) (i : Fin 8330) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem ptEquiv_smul
    (g : J) (i : Fin 8330) : ptEquiv (g • i) = g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem pt_smul
    (g : J) (i : Fin 8330) : pt (g • i : Fin 8330).val = g • pt i.val := by
  have := congrArg Subtype.val (ptEquiv_smul g i)
  rw [ptEquiv_apply] at this
  rw [this]
  rfl

theorem smul_eq_iff
    (g : J) (i j : Fin 8330) : g • i = j ↔ g • pt i.val = pt j.val := by
  constructor
  · rintro rfl; exact (pt_smul g i).symm
  · intro h
    apply Fin.ext
    apply pt_inj (by rw [orb_size]; exact (g • i).isLt) (by rw [orb_size]; exact j.isLt)
    rw [pt_smul, h]

theorem idx_eq_iff
    {g : J} {i j : ℕ} (hi : i < 8330) (hj : j < 8330) :
    idx 8330 g i = j ↔ g • pt i = pt j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    exact (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 8330 orb.alpha a := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.alpha i < 8330 := by rw [← orb_size]; exact (vecFacts.alpha i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (a_smul_pt hi')

theorem rep_beta : Rep 8330 orb.beta b := by
  intro i hi
  have hi' : i < orb.keys.size := by rw [orb_size]; exact hi
  have hlt : ap orb.beta i < 8330 := by rw [← orb_size]; exact (vecFacts.beta i hi').1
  symm
  exact (idx_eq_iff hi hlt).2 (b_smul_pt hi')

noncomputable abbrev basisM : Matrix (Fin 50) (Fin 50) (ZMod 7) := toMat 7 50 (colsMat 50 orb.keys)

theorem basisM_mul_inv :
    basisM * toMat 7 50 (invM 7 50 (colsMat 50 orb.keys)) = 1 := by
  have h := actionFacts.basis
  unfold basisCheck at h
  have e := toMat_eq_of_beq (p := 7) (d := 50) h
  rwa [toMat_mulM, toMat_idM] at e

theorem chainQ_getElem {t : ℕ} (ht : t < 50) : chainQ[t]! = t := by
  unfold chainQ
  rw [getElem!_pos (Array.range 50) t (by simpa using ht), Array.getElem_range]

theorem chainQ_size : chainQ.size = 50 := by unfold chainQ; simp

theorem sep
    (g : J) (hg : ∀ t < chainQ.size, idx 8330 g chainQ[t]! = chainQ[t]!) : g = 1 := by
  have hfix : ∀ t : Fin 50, mat g *ᵥ pt t.val = pt t.val := by
    intro t
    have h := hg t.val (by rw [chainQ_size]; exact t.isLt)
    rw [chainQ_getElem t.isLt] at h
    exact (idx_eq_iff (by omega) (by omega)).1 h
  have hM : mat g * basisM = basisM := by
    ext i t
    have := congrFun (hfix t) i
    rw [Matrix.mulVec, dotProduct] at this
    unfold pt at this
    rw [Matrix.mul_apply, basisM, toMat_colsMat, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [toMat_colsMat]
  apply mat_injective
  rw [mat_one]
  calc mat g = mat g * (basisM * toMat 7 50 (invM 7 50 (colsMat 50 orb.keys))) := by
        rw [basisM_mul_inv, mul_one]
    _ = (mat g * basisM) * toMat 7 50 (invM 7 50 (colsMat 50 orb.keys)) := by rw [mul_assoc]
    _ = 1 := by rw [hM, basisM_mul_inv]

theorem chainQ_lt {t : ℕ} (ht : t < chainQ.size) : chainQ[t]! < 8330 := by
  rw [chainQ_size] at ht
  rw [chainQ_getElem ht]
  omega

theorem eq_one_of_fix_all
    {g : J} (h : ∀ i : Fin 8330, g • i = i) : g = 1 := by
  apply sep
  intro t ht
  rw [idx_of_lt g (chainQ_lt ht), h]

instance faithful : FaithfulSMul J (Fin 8330) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := eq_one_of_fix_all fun i => by rw [mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem eq_one_of_isIdT
    {T : Table} {g : J} (hT : Rep 8330 T g) (h : isIdT T = true) : g = 1 := by
  apply eq_one_of_fix_all
  intro i
  apply Fin.ext
  have := (allIn_eq_true.1 h) i.val (Nat.zero_le _) i.isLt
  rw [beq_iff_eq, hT i.val i.isLt, idx_of_lt g i.isLt] at this
  exact this

theorem ne_one_of_isIdT
    {T : Table} {g : J} (hT : Rep 8330 T g) (h : isIdT T = false) :
    g ≠ 1 := by
  rintro rfl
  unfold isIdT at h
  rw [← Bool.not_eq_true, allIn_eq_true] at h
  apply h
  intro i _ hi
  rw [beq_iff_eq, hT i hi, CFSG.Sporadic.Th.idx_one]

end CFSG.Sporadic.He
