module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarSts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarFanoA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private theorem s16t3_gl3_ext {M M' : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)}
    (h : ∀ x : {v : Fin 3 → ZMod 2 // v ≠ 0},
      ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (x : Fin 3 → ZMod 2)) =
      ((M' : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (x : Fin 3 → ZMod 2))) :
    M = M' := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  have hne : (Pi.single i (1 : ZMod 2) : Fin 3 → ZMod 2) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 i
    simp at h1
  exact h ⟨Pi.single i (1 : ZMod 2), hne⟩

theorem ThreeNat.exists_fano_rep (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    ∃ r : ↥A →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      (∀ a : ↥A, r a = 1 ↔ ∀ J ∈ irrSet L, J.map (a : MulAut W).toMonoidHom = J) ∧
      ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
        ∃ a : ↥A, ((r a : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = v := by
  classical
  obtain ⟨third, ptAct, hmap, h1, h2, h3, heq⟩ := s16t3_exists_fano_structure h h7
  haveI : Fintype ↥(irrSet L) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(irrSet L) = 7 := by
    rw [← Nat.card_eq_fintype_card]
    exact h7
  obtain ⟨e, he⟩ := s16t3_sts7_coordinates hcard third h1 h2 h3
  let π : ↥A → Equiv.Perm {v : Fin 3 → ZMod 2 // v ≠ 0} :=
    fun a => e.symm.trans ((ptAct a).trans e)
  have hπ : ∀ (a : ↥A) (x : {v : Fin 3 → ZMod 2 // v ≠ 0}),
      π a x = e (ptAct a (e.symm x)) := fun _ _ => rfl
  have hπone : ∀ x : {v : Fin 3 → ZMod 2 // v ≠ 0}, π 1 x = x := by
    intro x
    simp only [hπ, map_one, Equiv.Perm.one_apply, Equiv.apply_symm_apply]
  have hπmul : ∀ (a b : ↥A) (x : {v : Fin 3 → ZMod 2 // v ≠ 0}),
      π (a * b) x = π a (π b x) := by
    intro a b x
    simp only [hπ, map_mul, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  have hgl : ∀ a : ↥A, ∃ M : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      ∀ x : {v : Fin 3 → ZMod 2 // v ≠ 0},
      ((M : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x =
        ((π a x : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) := by
    intro a
    apply s16t3_gl3_of_perm (π a)
    intro x y hxy hxy'
    have hJJ' : e.symm x ≠ e.symm y := by
      intro hh
      exact hxy (by rw [← e.apply_symm_apply x, hh, e.apply_symm_apply y])
    have hsymm : e.symm ⟨(x : Fin 3 → ZMod 2) + (y : Fin 3 → ZMod 2), hxy'⟩ =
        third (e.symm x) (e.symm y) := by
      have hJ : e (third (e.symm x) (e.symm y)) =
          ⟨(x : Fin 3 → ZMod 2) + (y : Fin 3 → ZMod 2), hxy'⟩ := by
        apply Subtype.ext
        simpa using he (e.symm x) (e.symm y) hJJ'
      rw [← hJ, Equiv.symm_apply_apply]
    have hne : ptAct a (e.symm x) ≠ ptAct a (e.symm y) :=
      fun hh => hJJ' ((ptAct a).injective hh)
    simp only [hπ, hsymm, heq]
    exact he (ptAct a (e.symm x)) (ptAct a (e.symm y)) hne
  let rf : ↥A → Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := fun a => Classical.choose (hgl a)
  have hrf : ∀ (a : ↥A) (x : {v : Fin 3 → ZMod 2 // v ≠ 0}),
      ((rf a : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x =
        ((π a x : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) :=
    fun a => Classical.choose_spec (hgl a)
  let r : ↥A →* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    { toFun := rf
      map_one' := by
        apply s16t3_gl3_ext
        intro x
        rw [hrf 1 x, hπone x, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      map_mul' := fun a b => by
        apply s16t3_gl3_ext
        intro x
        rw [hrf (a * b) x, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hrf b x,
          hrf a (π b x)]
        exact congrArg Subtype.val (hπmul a b x) }
  have hrf' : ∀ (a : ↥A) (x : {v : Fin 3 → ZMod 2 // v ≠ 0}),
      ((r a : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x =
        ((π a x : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) :=
    fun a => hrf a
  refine ⟨r, ?_, ?_⟩
  · intro a
    constructor
    · intro ha J hJ
      have hπid : ∀ x : {v : Fin 3 → ZMod 2 // v ≠ 0}, π a x = x := by
        intro x
        have h1 := hrf' a x
        rw [ha, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h1
        exact Subtype.ext h1.symm
      have hpt : ptAct a (⟨J, hJ⟩ : ↥(irrSet L)) = ⟨J, hJ⟩ := by
        apply e.injective
        have h1 := hπid (e ⟨J, hJ⟩)
        simpa only [hπ, Equiv.symm_apply_apply] using h1
      have hm := hmap a (⟨J, hJ⟩ : ↥(irrSet L))
      rw [hpt] at hm
      exact hm.symm
    · intro hfix
      apply s16t3_gl3_ext
      intro x
      have hx : π a x = x := by
        have hpt : ptAct a (e.symm x) = e.symm x := by
          apply Subtype.ext
          rw [hmap a (e.symm x), hfix (e.symm x) (e.symm x).2]
        rw [hπ, hpt, Equiv.apply_symm_apply]
      rw [hrf' a x, hx, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  · intro u v hu hv
    obtain ⟨g, hg, hJ'⟩ := h.trans (e.symm ⟨u, hu⟩) (e.symm ⟨u, hu⟩).2
      (e.symm ⟨v, hv⟩) (e.symm ⟨v, hv⟩).2
    refine ⟨⟨g, hg.1⟩, ?_⟩
    have hpt : ptAct ⟨g, hg.1⟩ (e.symm ⟨u, hu⟩) = e.symm ⟨v, hv⟩ := by
      apply Subtype.ext
      rw [hmap ⟨g, hg.1⟩ (e.symm ⟨u, hu⟩)]
      exact hJ'.symm
    calc ((r ⟨g, hg.1⟩ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u
        = ((r ⟨g, hg.1⟩ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
              (⟨u, hu⟩ : {v : Fin 3 → ZMod 2 // v ≠ 0}) := rfl
      _ = ((π ⟨g, hg.1⟩ (⟨u, hu⟩ : {v : Fin 3 → ZMod 2 // v ≠ 0}) :
            {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) := hrf' ⟨g, hg.1⟩ (⟨u, hu⟩ : _)
      _ = ((e (ptAct ⟨g, hg.1⟩ (e.symm ⟨u, hu⟩)) :
            {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) := by
            rw [hπ]
      _ = ((e (e.symm ⟨v, hv⟩) : {v : Fin 3 → ZMod 2 // v ≠ 0}) : Fin 3 → ZMod 2) := by rw [hpt]
      _ = v := by simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
