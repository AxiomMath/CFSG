
module

public import CFSG.Sporadic.Fi24.OrbitBase
import all CFSG.Sporadic.Fi24.OrbitBase

public import CFSG.Sporadic.Fi24.Setup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

noncomputable instance subAction : MulAction J Sub781 where
  smul g S := ⟨S.sp.map (Matrix.mulVecLin (mat g))⟩
  one_smul S := by
    apply Sub781.ext'
    show S.sp.map (Matrix.mulVecLin (mat 1)) = S.sp
    rw [mat_one, Matrix.mulVecLin_one, Submodule.map_id]
  mul_smul g h S := by
    apply Sub781.ext'
    show S.sp.map (Matrix.mulVecLin (mat g * mat h)) =
      (S.sp.map (Matrix.mulVecLin (mat h))).map (Matrix.mulVecLin (mat g))
    rw [Matrix.mulVecLin_mul, Submodule.map_comp]

theorem smul_sp
    (g : J) (S : Sub781) : (g • S).sp = S.sp.map (Matrix.mulVecLin (mat g)) := rfl

theorem pt_step_one {k : ℕ} (hk : k < nPts) :
    (⟨rowSpan 253 (stepForm ((gensT ()).get 1) (form k).rows).rows⟩ : Sub781) = a • pt k := by
  obtain ⟨hs, hw⟩ := form_facts hk
  apply Sub781.ext'
  rw [smul_sp, gensT_get_one, rowSpan_stepForm rowsWF_matAT matAT_size hw hs, matW_matAT_T, mat_a]
  rfl

theorem pt_step_two {k : ℕ} (hk : k < nPts) :
    (⟨rowSpan 253 (stepForm ((gensT ()).get 2) (form k).rows).rows⟩ : Sub781) = b • pt k := by
  obtain ⟨hs, hw⟩ := form_facts hk
  apply Sub781.ext'
  rw [smul_sp, gensT_get_two, rowSpan_stepForm rowsWF_matBT matBT_size hw hs, matW_matBT_T, mat_b]
  rfl

theorem alpha_lt
    {k : ℕ} (hk : k < nPts) : ap orb.alpha k < nPts := (core_facts.alpha k hk).1

theorem beta_lt
    {k : ℕ} (hk : k < nPts) : ap orb.beta k < nPts := (core_facts.beta k hk).1

theorem edges :
    ∀ k < nPts, a • pt k = pt (ap orb.alpha k) ∧ b • pt k = pt (ap orb.beta k) := by
  intro k hk
  constructor
  · apply Sub781.ext'
    rw [smul_sp, mat_a]
    exact (core_facts.alpha k hk).2
  · apply Sub781.ext'
    rw [smul_sp, mat_b]
    exact (core_facts.beta k hk).2

theorem form_rows_inj
    {i j : ℕ} (hi : i < nPts) (hj : j < nPts) (h : pt i = pt j) : i = j :=
  core_facts.inj i hi j hj (congrArg Sub781.sp h)

theorem pt_inj
    {i j : ℕ} (hi : i < nPts) (hj : j < nPts) (h : pt i = pt j) : i = j :=
  form_rows_inj hi hj h

theorem tree_facts : ∀ i < nPts, 0 < i → ap orb.par i < i ∧
    ((ap orb.lab i = 1 ∧ ap orb.alpha (ap orb.par i) = i) ∨
      (ap orb.lab i = 2 ∧ ap orb.beta (ap orb.par i) = i)) :=
  fun _ hi h0 => core_facts.tree _ hi h0

theorem orbit_hyps :
    (∀ i < nPts, ap orb.alpha i < nPts ∧ a • pt i = pt (ap orb.alpha i)) ∧
    (∀ i < nPts, ap orb.beta i < nPts ∧ b • pt i = pt (ap orb.beta i)) :=
  ⟨fun i hi => ⟨alpha_lt hi, (edges i hi).1⟩, fun i hi => ⟨beta_lt hi, (edges i hi).2⟩⟩

theorem orbit_eq : MulAction.orbit J (pt 0) = pt '' Set.Iio nPts :=
  orbit_eq_image closure_ab (by rw [nPts_eq]; norm_num) pt orbit_hyps.1 orbit_hyps.2
    (ap orb.par) (ap orb.lab) tree_facts

@[expose] noncomputable def ptEquiv :
    Fin 306936 ≃ MulAction.orbit J (pt 0) :=
  orbitEquiv closure_ab (by norm_num) pt (fun i hi j hj h => pt_inj hi hj h)
    orbit_hyps.1 orbit_hyps.2 (ap orb.par) (ap orb.lab) tree_facts

theorem ptEquiv_apply (i : Fin 306936) : (ptEquiv i : Sub781) = pt i.val := rfl

noncomputable instance idxInst :
    MulAction J (Fin 306936) := ptEquiv.mulAction J

theorem smul_def
    (g : J) (i : Fin 306936) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem ptEquiv_smul
    (g : J) (i : Fin 306936) : ptEquiv (g • i) = g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem pt_smul
    (g : J) (i : Fin 306936) : pt (g • i : Fin 306936).val = g • pt i.val := by
  have := congrArg Subtype.val (ptEquiv_smul g i)
  rw [ptEquiv_apply] at this
  rw [this]
  rfl

theorem smul_eq_iff
    (g : J) (i j : Fin 306936) : g • i = j ↔ g • pt i.val = pt j.val := by
  constructor
  · rintro rfl; exact (pt_smul g i).symm
  · intro h
    apply Fin.ext
    apply pt_inj (by rw [nPts_eq]; exact (g • i).isLt) (by rw [nPts_eq]; exact j.isLt)
    rw [pt_smul, h]

theorem idx_eq_iff
    {g : J} {i j : ℕ} (hi : i < 306936) (hj : j < 306936) :
    idx 306936 g i = j ↔ g • pt i = pt j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    exact (smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
  · intro h
    exact congrArg Fin.val ((smul_eq_iff g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep 306936 orb.alpha a := by
  intro i hi
  have hlt : ap orb.alpha i < 306936 := alpha_lt hi
  symm
  exact (idx_eq_iff hi hlt).2 (edges i hi).1

theorem rep_beta : Rep 306936 orb.beta b := by
  intro i hi
  have hlt : ap orb.beta i < 306936 := beta_lt hi
  symm
  exact (idx_eq_iff hi hlt).2 (edges i hi).2

end CFSG.Sporadic.Fi24
