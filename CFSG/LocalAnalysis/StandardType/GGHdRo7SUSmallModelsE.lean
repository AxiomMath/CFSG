module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
import CFSG.LocalAnalysis.StandardType.GGWAutCommon

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def hdRo7SmEAux_H : Fin 7 → SMV 7 :=
  ![![1,2,0,0,0,0,0],
    ![0,0,0,1,1,1,1],
    ![0,1,2,0,0,0,0],
    ![0,0,1,2,0,0,0],
    ![0,0,0,1,2,0,0],
    ![0,0,0,0,1,2,0],
    ![0,0,0,0,0,1,2]]

private def hdRo7SmEAux_W : Fin 7 → SMV 7 :=
  ![![1,2,0,0,0,0,0],
    ![1,1,1,2,2,2,2],
    ![0,1,2,0,0,0,0],
    ![0,0,1,2,0,0,0],
    ![0,0,0,1,2,0,0],
    ![0,0,0,0,1,2,0],
    ![0,0,0,0,0,1,2]]

private noncomputable def hdRo7SmEAux_A (i : Fin 7) : Module.Dual (ZMod 3) (SMV 7) := smDual (hdRo7SmEAux_W i)

private lemma hdRo7SmEAux_pairing (i j : Fin 7) :
    hdRo7SmEAux_A i (hdRo7SmEAux_H j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma hdRo7SmEAux_hα (i : Fin 7) : hdRo7SmEAux_A i (hdRo7SmEAux_H i) = 2 := by
  rw [hdRo7SmEAux_pairing]; fin_cases i <;> decide

private noncomputable def hdRo7SmEAux_Phi (i : Fin 7) : SMGL 7 :=
  Module.reflection (hdRo7SmEAux_hα i)

private def hdRo7SmEAux_C : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  (CartanMatrix.E 7).map (Int.castRingHom (ZMod 3))

private def hdRo7SmEAux_Cinv : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![![2,2,0,1,0,2,1],
    ![2,2,1,0,0,0,0],
    ![0,1,0,2,0,1,2],
    ![1,0,2,0,0,0,0],
    ![0,0,0,0,0,2,1],
    ![2,0,1,0,2,1,2],
    ![1,0,2,0,1,2,0]]

private lemma hdRo7SmEAux_Cinv_mul : hdRo7SmEAux_Cinv * hdRo7SmEAux_C = 1 := by decide

private lemma hdRo7SmEAux_linIndep : LinearIndependent (ZMod 3) hdRo7SmEAux_H := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hC : hdRo7SmEAux_C.mulVec g = 0 := by
    ext i
    have h := congrArg (hdRo7SmEAux_A i) hg
    rw [map_sum, map_zero] at h
    have h' : ∑ j, g j * hdRo7SmEAux_A i (hdRo7SmEAux_H j) = 0 := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul]
    have h'' : ∑ j, g j * ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) = 0 := by
      rw [← h']
      apply Finset.sum_congr rfl
      intro j _
      rw [hdRo7SmEAux_pairing]
    rw [Matrix.mulVec_apply, dotProduct]
    simpa [hdRo7SmEAux_C, Matrix.map_apply, mul_comm] using h''
  have h1 : hdRo7SmEAux_Cinv.mulVec (hdRo7SmEAux_C.mulVec g) = 0 := by rw [hC, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, hdRo7SmEAux_Cinv_mul, Matrix.one_mulVec] at h1
  exact congrFun h1 i

private lemma hdRo7SmEAux_φ_isRefl (i : Fin 7) : ZS.IsRefl 3 (hdRo7SmEAux_Phi i) := by
  have h : IsReflLin (hdRo7SmEAux_Phi i) := ⟨hdRo7SmEAux_H i, hdRo7SmEAux_A i, hdRo7SmEAux_hα i, rfl⟩
  exact (ggLinRefl_iff_isReflLin _).mpr h

private lemma hdRo7SmEAux_F_inj :
    Function.Injective (CoxeterMatrix.E₇.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hdRo7SmEAux_hα i),
        isLiftable_reflection_of_intCartan ggIntCartan_E₇ hdRo7SmEAux_H hdRo7SmEAux_A
          hdRo7SmEAux_hα hdRo7SmEAux_pairing⟩) := by
  have hFT : TauCeti.IsFiniteType (CartanMatrix.E 7) := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
    rwa [TauCeti.DynkinType.cartanMatrix_E7] at h
  exact ggCartanFaithful_of_isFiniteType (p := 3) (hα := hdRo7SmEAux_hα) (hP := hdRo7SmEAux_pairing)
    (by decide) hFT ggIntCartan_E₇ hdRo7SmEAux_linIndep

private noncomputable def hdRo7SmEAux_PermToGL (σ : Equiv.Perm (Fin 7)) : SMGL 7 where
  toFun v := fun i => v (σ.symm i)
  invFun v := fun i => v (σ i)
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

private noncomputable def hdRo7SmEAux_PermToGLHom : Equiv.Perm (Fin 7) →* SMGL 7 where
  toFun := hdRo7SmEAux_PermToGL
  map_one' := by ext v i; rfl
  map_mul' σ τ := by ext v i; rfl

private lemma hdRo7SmEAux_PermToGL_eq_iff (g : SMGL 7) :
    SMIsPerm g ↔ ∃ σ : Equiv.Perm (Fin 7), g = hdRo7SmEAux_PermToGL σ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, by ext v i; simp [hdRo7SmEAux_PermToGL, hσ]⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, fun v i => rfl⟩

private def hdRo7SmEAux_AdjIdx : Fin 6 → Fin 7 := ![0,2,3,4,5,6]

private lemma hdRo7SmEAux_PermToGL_adjSwap (i : Fin 6) :
    hdRo7SmEAux_PermToGL (Equiv.swap i.castSucc i.succ) = hdRo7SmEAux_Phi (hdRo7SmEAux_AdjIdx i) := by
  fin_cases i
  all_goals
    apply Module.Basis.ext' (Pi.basisFun (ZMod 3) (Fin 7))
    intro k
    rw [Pi.basisFun_apply]
    fin_cases k <;> decide

private lemma hdRo7SmEAux_perm_mem (g : SMGL 7) (hg : SMIsPerm g) :
    g ∈ Subgroup.closure (Set.range hdRo7SmEAux_Phi) := by
  obtain ⟨σ, rfl⟩ := (hdRo7SmEAux_PermToGL_eq_iff g).mp hg
  have hσ : σ ∈ Subgroup.closure
      (Set.range (fun i : Fin 6 => Equiv.swap i.castSucc i.succ)) := by
    have hsub : (Submonoid.closure
        (Set.range (fun i : Fin 6 => Equiv.swap i.castSucc i.succ)) : Set (Equiv.Perm (Fin 7))) ⊆
        (Subgroup.closure (Set.range (fun i : Fin 6 => Equiv.swap i.castSucc i.succ)) :
          Set (Equiv.Perm (Fin 7))) :=
      Submonoid.closure_le.mpr (fun x hx => Subgroup.subset_closure hx)
    have htop : Subgroup.closure (Set.range (fun i : Fin 6 => Equiv.swap i.castSucc i.succ)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hsub (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)
    rw [htop]; trivial
  have hmem : hdRo7SmEAux_PermToGL σ ∈ (Subgroup.closure
      (Set.range (fun i : Fin 6 => Equiv.swap i.castSucc i.succ))).map hdRo7SmEAux_PermToGLHom :=
    Subgroup.mem_map_of_mem _ hσ
  rw [MonoidHom.map_closure] at hmem
  exact Subgroup.closure_mono (by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := hx
    exact ⟨hdRo7SmEAux_AdjIdx i, (hdRo7SmEAux_PermToGL_adjSwap i).symm⟩) hmem

private lemma hdRo7SmEAux_PermToGL_mem_A (σ : Equiv.Perm (Fin 7)) :
    hdRo7SmEAux_PermToGL σ ∈ smGroup 7 [sm7E7b, sm7A7a] := by
  refine Subgroup.subset_closure (Or.inl ?_)
  exact ⟨σ, fun v i => rfl⟩

private lemma hdRo7SmEAux_Phi_one_eq : hdRo7SmEAux_Phi 1 =
    Module.reflection (show smDual sm7E7b.2 sm7E7b.1 = 2 from by decide) := by
  apply Module.Basis.ext' (Pi.basisFun (ZMod 3) (Fin 7))
  intro k
  rw [Pi.basisFun_apply]
  fin_cases k <;> decide

private lemma hdRo7SmEAux_Phi_one_mem_A : hdRo7SmEAux_Phi 1 ∈ smGroup 7 [sm7E7b, sm7A7a] := by
  rw [hdRo7SmEAux_Phi_one_eq]
  refine Subgroup.subset_closure (Or.inr ?_)
  refine ⟨sm7E7b, by simp, ?_⟩
  exact ⟨by decide, fun v => Module.reflection_apply v (by decide)⟩

private lemma hdRo7SmEAux_Phi_adjIdx_mem_A (j : Fin 6) :
    hdRo7SmEAux_Phi (hdRo7SmEAux_AdjIdx j) ∈ smGroup 7 [sm7E7b, sm7A7a] := by
  rw [← hdRo7SmEAux_PermToGL_adjSwap j]
  exact hdRo7SmEAux_PermToGL_mem_A _

private lemma hdRo7SmEAux_Phi_mem_A_ne (i : Fin 7) (hi : i ≠ 1) :
    hdRo7SmEAux_Phi i ∈ smGroup 7 [sm7E7b, sm7A7a] := by
  have h : ∃ j : Fin 6, hdRo7SmEAux_AdjIdx j = i := by
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact absurd rfl hi
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  obtain ⟨j, rfl⟩ := h
  exact hdRo7SmEAux_Phi_adjIdx_mem_A j

private lemma hdRo7SmEAux_Phi_mem_A (i : Fin 7) : hdRo7SmEAux_Phi i ∈ smGroup 7 [sm7E7b, sm7A7a] := by
  by_cases hi : i = 1
  · subst hi; exact hdRo7SmEAux_Phi_one_mem_A
  · exact hdRo7SmEAux_Phi_mem_A_ne i hi

private noncomputable def hdRo7SmEAux_A7a : SMGL 7 :=
  Module.reflection (show smDual sm7A7a.2 sm7A7a.1 = 2 from by decide)

private def hdRo7SmEAux_Word : List (Fin 7) :=
  [0,2,3,4,5,1,3,4,2,3,0,2,1,3,4,5,6,5,4,3,2,1,3,4,5,0,2,3,4,1,3,2,0]

private lemma hdRo7SmEAux_Word_prod : (hdRo7SmEAux_Word.map hdRo7SmEAux_Phi).prod = hdRo7SmEAux_A7a := by
  apply Module.Basis.ext' (Pi.basisFun (ZMod 3) (Fin 7))
  intro k
  rw [Pi.basisFun_apply]
  fin_cases k <;> decide +kernel

private lemma hdRo7SmEAux_A7a_mem : hdRo7SmEAux_A7a ∈ Subgroup.closure (Set.range hdRo7SmEAux_Phi) := by
  rw [← hdRo7SmEAux_Word_prod]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨i, rfl⟩

private noncomputable def hdRo7SmEAux_L : CoxeterMatrix.E₇.Group →* SMGL 7 :=
  CoxeterMatrix.E₇.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hdRo7SmEAux_hα i),
      isLiftable_reflection_of_intCartan ggIntCartan_E₇ hdRo7SmEAux_H hdRo7SmEAux_A hdRo7SmEAux_hα hdRo7SmEAux_pairing⟩

private lemma hdRo7SmEAux_L_simple (i : Fin 7) : hdRo7SmEAux_L (CoxeterMatrix.E₇.simple i) = hdRo7SmEAux_Phi i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, hdRo7SmEAux_L, CoxeterSystem.lift_apply_simple]
  rfl

private lemma hdRo7SmEAux_L_range : hdRo7SmEAux_L.range = Subgroup.closure (Set.range hdRo7SmEAux_Phi) := by
  rw [MonoidHom.range_eq_map, ← CoxeterMatrix.E₇.toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1

private lemma hdRo7SmEAux_L_inj : Function.Injective hdRo7SmEAux_L := hdRo7SmEAux_F_inj

private lemma hdRo7SmEAux_range_eq_A : hdRo7SmEAux_L.range = smGroup 7 [sm7E7b, sm7A7a] := by
  apply le_antisymm
  · rw [hdRo7SmEAux_L_range]
    exact (Subgroup.closure_le _).mpr (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact hdRo7SmEAux_Phi_mem_A i)
  · rw [hdRo7SmEAux_L_range, smGroup, Subgroup.closure_le]
    rintro y (hy | hy)
    · exact hdRo7SmEAux_perm_mem y hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      obtain ⟨q, hq, hrfl⟩ := hy
      rcases hq with rfl | rfl
      · have hy_eq : y = Module.reflection
            (show smDual sm7E7b.2 sm7E7b.1 = 2 from hrfl.1) := by
          ext v
          rw [hrfl.2 v, Module.reflection_apply]
        rw [hy_eq, ← hdRo7SmEAux_Phi_one_eq]
        exact Subgroup.subset_closure ⟨1, rfl⟩
      · have hy_eq : y = hdRo7SmEAux_A7a := by
          ext v
          rw [hrfl.2 v, hdRo7SmEAux_A7a, Module.reflection_apply]
        rw [hy_eq]
        exact hdRo7SmEAux_A7a_mem

private lemma hdRo7SmEAux_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

theorem smModelsE_holds : SMModelsELeaf := by
  let A := smGroup 7 [sm7E7b, sm7A7a]
  let F : CoxeterMatrix.E₇.Group →* ↥A :=
    { toFun := fun x => ⟨hdRo7SmEAux_L x, by
        rw [show A = hdRo7SmEAux_L.range from hdRo7SmEAux_range_eq_A.symm]; exact ⟨x, rfl⟩⟩
      map_one' := by ext; simp [hdRo7SmEAux_L]
      map_mul' x y := by ext; simp [hdRo7SmEAux_L] }
  have hF_inj : Function.Injective F := by
    intro x y h
    exact hdRo7SmEAux_L_inj (congrArg Subtype.val h)
  have hF_surj : Function.Surjective F := by
    intro a
    have ha : (a : SMGL 7) ∈ hdRo7SmEAux_L.range := by rw [hdRo7SmEAux_range_eq_A]; exact a.2
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨Fin 7, CoxeterMatrix.E₇, ?_, ?_⟩
  · exact GGIsWeylMatrixE.isWeylMatrix
      (Or.inr (Or.inl ⟨Equiv.refl _, (hdRo7SmEAux_reindex_refl CoxeterMatrix.E₇).symm⟩))
  · have hF_bij : Function.Bijective F := ⟨hF_inj, hF_surj⟩
    refine ⟨MulEquiv.ofBijective F hF_bij, ?_⟩
    intro i
    rw [MulEquiv.ofBijective_apply]
    have hcoe : ((F (CoxeterMatrix.E₇.simple i) : ↥A) : SMGL 7) = hdRo7SmEAux_Phi i := by
      change hdRo7SmEAux_L (CoxeterMatrix.E₇.simple i) = hdRo7SmEAux_Phi i
      exact hdRo7SmEAux_L_simple i
    rw [hcoe]
    exact hdRo7SmEAux_φ_isRefl i

end CFSG.StandardType.HdRo7SU.Small
