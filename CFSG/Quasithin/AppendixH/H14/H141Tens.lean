module

public import CFSG.Quasithin.AppendixH.H14.H141Coord
public import CFSG.Quasithin.AppendixH.H14.H141TInst
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Matrix Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H158T CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Open

@[expose] def codeOfMat (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) : ℕ :=
  (X 0 0).val + 2 * (X 1 0).val + 4 * (X 2 0).val + 8 * (X 0 1).val + 16 * (X 1 1).val +
    32 * (X 2 1).val

@[expose] def matOfCode (n : ℕ) : Matrix (Fin 3) (Fin 2) (ZMod 2) :=
  !![((n % 2 : ℕ) : ZMod 2), ((n / 8 % 2 : ℕ) : ZMod 2);
     ((n / 2 % 2 : ℕ) : ZMod 2), ((n / 16 % 2 : ℕ) : ZMod 2);
     ((n / 4 % 2 : ℕ) : ZMod 2), ((n / 32 % 2 : ℕ) : ZMod 2)]

theorem codeOfMat_lt (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) : codeOfMat X < 64 := by
  revert X; decide +kernel

theorem codeOfMat_matOfCode : ∀ n < 64, codeOfMat (matOfCode n) = n := by
  decide +kernel

theorem matOfCode_codeOfMat (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    matOfCode (codeOfMat X) = X := by
  revert X; decide +kernel

theorem codeOfMat_add (X Y : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    codeOfMat (X + Y) = codeOfMat X ^^^ codeOfMat Y := by
  revert X Y; decide +kernel

@[expose] def coordMat : Coord64 (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) where
  code X := codeOfMat (Multiplicative.toAdd X)
  ofCode n := Multiplicative.ofAdd (matOfCode n)
  code_lt X := codeOfMat_lt _
  ofCode_code X := by
    show Multiplicative.ofAdd (matOfCode (codeOfMat (Multiplicative.toAdd X))) = X
    rw [matOfCode_codeOfMat, ofAdd_toAdd]
  code_ofCode n hn := by
    simpa using codeOfMat_matOfCode n hn
  code_mul a b := by
    rw [toAdd_mul]
    exact codeOfMat_add _ _

@[expose] noncomputable def actT :
    ↥(MY M24g labTrio) →* MulAut (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) :=
  actHom engine_T.normal (tab64Equiv tabT_ok coordMat)

theorem exists_state_T (g : ↥(MY M24g labTrio)) :
    ∃ st, StReach gmT st ∧ ∀ n < 64,
      (g : S24) * tab64Perm tabT n * (g : S24)⁻¹ = tab64Perm tabT (linAct st n) := by
  obtain ⟨st, hst, hact⟩ := engine_T.action g g.2
  obtain ⟨e, he, he1⟩ := List.mem_map.mp hst
  refine ⟨st, ?_, hact⟩
  rw [← he1]
  exact (sbfsOK_sound bfsT_ok).2.2 e he

theorem actT_apply_state (g : ↥(MY M24g labTrio)) {st : ℕ}
    (hst : ∀ n < 64, (g : S24) * tab64Perm tabT n * (g : S24)⁻¹ = tab64Perm tabT (linAct st n))
    (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    actT g (Multiplicative.ofAdd X) =
      Multiplicative.ofAdd (matOfCode (linAct st (codeOfMat X))) := by
  have h := actHom_tab64Equiv_state tabT_ok coordMat engine_T.normal g hst (codeOfMat_lt X)
  have hx : (Multiplicative.ofAdd X : Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) =
      coordMat.ofCode (codeOfMat X) := by
    rw [show coordMat.ofCode (codeOfMat X) =
        Multiplicative.ofAdd (matOfCode (codeOfMat X)) from rfl, matOfCode_codeOfMat]
  rw [hx]
  exact h

@[expose] def TensorSt (st : ℕ) : Prop :=
  ∃ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : Matrix (Fin 2) (Fin 2) (ZMod 2)),
    IsUnit g.det ∧ IsUnit h.det ∧ ∀ X : Matrix (Fin 3) (Fin 2) (ZMod 2),
      matOfCode (linAct st (codeOfMat X)) = g * X * hᵀ

theorem gen0_act (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    matOfCode (linAct 30059803077 (codeOfMat X)) =
      (!![1, 1, 1; 0, 1, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X *
        (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ := by
  revert X; decide +kernel

theorem gen1_act (X : Matrix (Fin 3) (Fin 2) (ZMod 2)) :
    matOfCode (linAct 29151560224 (codeOfMat X)) =
      (!![0, 1, 1; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X *
        (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ := by
  revert X; decide +kernel

theorem tensorSt_gens : ∀ j < 2, TensorSt (gmT.getD j 0) := by
  intro j hj
  interval_cases j
  · refine ⟨!![1, 1, 1; 0, 1, 1; 1, 1, 0], !![1, 1; 0, 1], ?_, ?_, ?_⟩
    · have h : (!![1, 1, 1; 0, 1, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
        decide +kernel
      rw [h]; exact isUnit_one
    · have h : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)).det = 1 := by
        decide +kernel
      rw [h]; exact isUnit_one
    · intro X
      rw [show gmT.getD 0 0 = 30059803077 by decide +kernel]
      exact gen0_act X
  · refine ⟨!![0, 1, 1; 0, 0, 1; 1, 0, 0], !![0, 1; 1, 1], ?_, ?_, ?_⟩
    · have h : (!![0, 1, 1; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
        decide +kernel
      rw [h]; exact isUnit_one
    · have h : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)).det = 1 := by
        decide +kernel
      rw [h]; exact isUnit_one
    · intro X
      rw [show gmT.getD 1 0 = 29151560224 by decide +kernel]
      exact gen1_act X

theorem tensorSt_of_reach {st : ℕ} (h : StReach gmT st) : TensorSt st := by
  refine StReach.rec (motive := fun st _ => TensorSt st) ?_ ?_ h
  · refine ⟨1, 1, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro X
      rw [linAct_idSt (codeOfMat_lt X), matOfCode_codeOfMat]
      simp
  · intro j s hj hs ih
    have hj2 : j < 2 := by simpa [gmT] using hj
    obtain ⟨g₀, h₀, hg₀, hh₀, hact₀⟩ := tensorSt_gens j hj2
    obtain ⟨g₁, h₁, hg₁, hh₁, hact₁⟩ := ih
    refine ⟨g₀ * g₁, h₀ * h₁, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul]; exact hg₀.mul hg₁
    · rw [Matrix.det_mul]; exact hh₀.mul hh₁
    · intro X
      rw [linAct_compSt]
      have hcode : linAct s (codeOfMat X) =
          codeOfMat (matOfCode (linAct s (codeOfMat X))) :=
        (codeOfMat_matOfCode _ (linAct_lt s _)).symm
      rw [hcode, hact₀ (matOfCode (linAct s (codeOfMat X))), hact₁ X, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]

theorem actT_mem (g : ↥(MY M24g labTrio)) :
    actT g ∈ tensorSet32 := by
  obtain ⟨st, hreach, hst⟩ := exists_state_T g
  obtain ⟨g₀, h₀, hg₀, hh₀, hact₀⟩ := tensorSt_of_reach hreach
  refine ⟨Matrix.GeneralLinearGroup.mk'' g₀ hg₀, Matrix.GeneralLinearGroup.mk'' h₀ hh₀, ?_⟩
  intro X
  rw [actT_apply_state g hst X, toAdd_ofAdd, hact₀ X]
  rfl

@[expose] def TensorPairOK (γ : MulAut (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))))
    (p : GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2)) : Prop :=
  ∀ X : Matrix (Fin 3) (Fin 2) (ZMod 2),
    Multiplicative.toAdd (γ (Multiplicative.ofAdd X)) =
      (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X * (p.2 : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ

theorem ncard_tensorSet32_le : tensorSet32.ncard ≤ 1008 := by
  classical
  have hcard3 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three]; norm_num [ZMod.card]
  have hcard2 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two]; norm_num [ZMod.card]
  let f : MulAut (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) →
      GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2) := fun γ =>
    if h : ∃ p : GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2), TensorPairOK γ p then
      Classical.choose h
    else (1, 1)
  have hf_mem : ∀ γ ∈ tensorSet32,
      f γ ∈ (Set.univ : Set (GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2))) :=
    fun γ _ => Set.mem_univ _
  have hf_inj : Set.InjOn f tensorSet32 := by
    intro γ hγ γ' hγ' heq
    have hgood : ∃ p : GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2), TensorPairOK γ p := by
      obtain ⟨g, h, hgh⟩ := hγ
      exact ⟨(g, h), hgh⟩
    have hgood' : ∃ p : GL (Fin 3) (ZMod 2) × GL (Fin 2) (ZMod 2), TensorPairOK γ' p := by
      obtain ⟨g, h, hgh⟩ := hγ'
      exact ⟨(g, h), hgh⟩
    have h1 : Classical.choose hgood = Classical.choose hgood' := by
      have := heq
      simp only [f, dif_pos hgood, dif_pos hgood'] at this
      exact this
    have hm1 := congrArg Prod.fst h1
    have hm2 := congrArg Prod.snd h1
    have hspec : ∀ X, Multiplicative.toAdd (γ (Multiplicative.ofAdd X)) =
        Multiplicative.toAdd (γ' (Multiplicative.ofAdd X)) := by
      intro X
      have hs := Classical.choose_spec hgood X
      have hs' := Classical.choose_spec hgood' X
      rw [hm1, hm2] at hs
      rw [hs, hs']
    exact MulEquiv.ext (fun x => by
      have hx := congrArg Multiplicative.ofAdd (hspec x.toAdd)
      simpa only [ofAdd_toAdd] using hx)
  have hle := Set.ncard_le_ncard_of_injOn f hf_mem hf_inj
  rw [Set.ncard_univ, Nat.card_prod, hcard3, hcard2] at hle
  norm_num at hle
  exact hle

theorem le_ncard_range_actT :
    1008 ≤ (Set.range actT).ncard := by
  classical
  let S : Set ℕ := {st | st ∈ bfsT.map Prod.fst}
  let f : ℕ → MulAut (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) := fun st =>
    if h : st ∈ bfsT.map Prod.fst then
      actT ⟨Classical.choose (engine_T.realize st h),
            (Classical.choose_spec (engine_T.realize st h)).1⟩
    else 1
  have hf_mem : ∀ st ∈ S, f st ∈ Set.range actT := by
    intro st hst
    have hstm : st ∈ bfsT.map Prod.fst := hst
    exact ⟨_, by
      simp only [f, dif_pos hstm]
      rfl⟩
  have hf_inj : Set.InjOn f S := by
    intro st hst st' hst' heq
    have hstm : st ∈ bfsT.map Prod.fst := hst
    have hst'm : st' ∈ bfsT.map Prod.fst := hst'
    let x : ↥(MY M24g labTrio) :=
      ⟨Classical.choose (engine_T.realize st hstm),
       (Classical.choose_spec (engine_T.realize st hstm)).1⟩
    let x' : ↥(MY M24g labTrio) :=
      ⟨Classical.choose (engine_T.realize st' hst'm),
       (Classical.choose_spec (engine_T.realize st' hst'm)).1⟩
    have hfst : f st = actT x := by simp only [f, dif_pos hstm, x]
    have hfst' : f st' = actT x' := by simp only [f, dif_pos hst'm, x']
    have hreal_st : ∀ n < 64,
        (x : S24) * tab64Perm tabT n * (x : S24)⁻¹ = tab64Perm tabT (linAct st n) :=
      (Classical.choose_spec (engine_T.realize st hstm)).2
    have hreal_st' : ∀ n < 64,
        (x' : S24) * tab64Perm tabT n * (x' : S24)⁻¹ = tab64Perm tabT (linAct st' n) :=
      (Classical.choose_spec (engine_T.realize st' hst'm)).2
    have hmat : ∀ n < 64, matOfCode (linAct st n) = matOfCode (linAct st' n) := by
      intro n hn
      have h3 : actT x (Multiplicative.ofAdd (matOfCode n)) =
          actT x' (Multiplicative.ofAdd (matOfCode n)) := by
        rw [← hfst, ← hfst', heq]
      rw [actT_apply_state x hreal_st (matOfCode n),
        actT_apply_state x' hreal_st' (matOfCode n), codeOfMat_matOfCode n hn] at h3
      have := congrArg Multiplicative.toAdd h3
      simpa only [toAdd_ofAdd] using this
    have hlin : ∀ n < 64, linAct st n = linAct st' n := by
      intro n hn
      have h := congrArg codeOfMat (hmat n hn)
      rwa [codeOfMat_matOfCode _ (linAct_lt st n),
        codeOfMat_matOfCode _ (linAct_lt st' n)] at h
    have hcol : ∀ i < 6, col st i = col st' i := by
      intro i hi
      have h2i : 2 ^ i < 64 := by interval_cases i <;> norm_num
      rw [← linAct_two_pow st hi, ← linAct_two_pow st' hi]
      exact hlin (2 ^ i) h2i
    have hreach_st : StReach gmT st := by
      obtain ⟨e, he, he1⟩ := List.mem_map.mp hstm
      rw [← he1]
      exact (sbfsOK_sound bfsT_ok).2.2 e he
    have hreach_st' : StReach gmT st' := by
      obtain ⟨e, he, he1⟩ := List.mem_map.mp hst'm
      rw [← he1]
      exact (sbfsOK_sound bfsT_ok).2.2 e he
    exact eq_of_col_eq (StReach.lt hreach_st) (StReach.lt hreach_st') hcol
  have hS_ncard : S.ncard = 1008 := by
    have hS_eq : S = ↑((bfsT.map Prod.fst).toFinset) := by
      ext st; simp [S]
    rw [hS_eq, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup (sbfsOK_sound bfsT_ok).2.1]
    simp [bfsT_length]
  have hle := Set.ncard_le_ncard_of_injOn f hf_mem hf_inj
  rw [hS_ncard] at hle
  exact hle

theorem actT_surj :
    ∀ γ ∈ tensorSet32, ∃ g : ↥(MY M24g labTrio), actT g = γ := by
  intro γ hγ
  have hsub : Set.range actT ⊆ tensorSet32 := by
    rintro γ ⟨g, rfl⟩
    exact actT_mem g
  have hle : tensorSet32.ncard ≤ (Set.range actT).ncard :=
    le_trans ncard_tensorSet32_le le_ncard_range_actT
  have heq : Set.range actT = tensorSet32 := Set.eq_of_subset_of_ncard_le hsub hle
  rw [← heq] at hγ
  obtain ⟨g, hg⟩ := hγ
  exact ⟨g, hg⟩

theorem stdMT_conjIso :
    ConjIso (MY M24g labTrio) (tab64Sub tabT tabT_ok)
      (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) tensorSet32
      (tab64Equiv tabT_ok coordMat) actT := by
  exact conjIso_of_actHom engine_T.le engine_T.normal (tab64Equiv tabT_ok coordMat)
    tensorSet32 actT_mem actT_surj engine_T.selfCentralizing

theorem stdMT_conjIsoModel :
    ConjIsoModel (MY M24g labTrio) (KY M24g labTrio)
      (Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))) tensorSet32 := by
  rw [pCore_T]
  exact ⟨tab64Equiv tabT_ok coordMat, actT, stdMT_conjIso⟩

end CFSG.Quasithin.AppendixH.H14
