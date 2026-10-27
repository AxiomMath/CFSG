module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Graph

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LangTwistedProof Matrix
open scoped MatrixGroups

variable {L : Type} [Field L] [CharP L 2]

theorem exists_secGraph_of_mem_secM {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {m : ModGL TwistTag.D4.tag L} (hm : m ∈ secM μ) : ∃ P : PGL(3, L), (m, P) ∈ secGraph μ := by
  suffices h : secM μ ≤ (secGraph μ).map (MonoidHom.fst _ _) by
    obtain ⟨p, hp, rfl⟩ := h hm
    exact ⟨p.2, hp⟩
  refine iSup_le fun o => ?_
  rcases o with _ | ⟨j, _ | _⟩
  · rintro t ⟨htT, htP⟩
    obtain ⟨a, ha1, ha3, rfl⟩ := exists_rootDiagUnit_of_mem_torus_fixed htT htP
    exact ⟨_, mem_secGraph (mem_secM_of_mem_torus μ htT htP) (adRel_rootDiagUnit μ ha1 ha3), rfl⟩
  · rintro _ ⟨c, rfl⟩
    have hmem := secOrbitY_mem_secM μ j (Multiplicative.toAdd c)
    fin_cases j
    · exact ⟨_, mem_secGraph hmem (adRel_secOrbitY_zero μ hμ _), rfl⟩
    · exact ⟨_, mem_secGraph hmem (adRel_secOrbitY_one μ hμ _), rfl⟩
    · exact ⟨_, mem_secGraph hmem (adRel_secOrbitY_two μ hμ _), rfl⟩
  · rintro _ ⟨c, rfl⟩
    have hmem := secOrbitX_mem_secM μ j (Multiplicative.toAdd c)
    fin_cases j
    · exact ⟨_, mem_secGraph hmem (adRel_secOrbitX_zero μ hμ _), rfl⟩
    · exact ⟨_, mem_secGraph hmem (adRel_secOrbitX_one μ hμ _), rfl⟩
    · exact ⟨_, mem_secGraph hmem (adRel_secOrbitX_two μ hμ _), rfl⟩

theorem mem_snd_secGraph_tvGL {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {i j : Fin 3}
    (hij : i ≠ j) (c : L) :
    ProjGenLinGroup.mk (tvGL hij c) ∈ (secGraph μ).map (MonoidHom.snd _ _) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨_, mem_secGraph (secOrbitX_mem_secM μ 0 c) (adRel_secOrbitX_zero μ hμ c), rfl⟩
  · exact ⟨_, mem_secGraph (secOrbitX_mem_secM μ 2 c) (adRel_secOrbitX_two μ hμ c), rfl⟩
  · exact ⟨_, mem_secGraph (secOrbitY_mem_secM μ 0 c) (adRel_secOrbitY_zero μ hμ c), rfl⟩
  · exact absurd rfl hij
  · exact ⟨_, mem_secGraph (secOrbitX_mem_secM μ 1 c) (adRel_secOrbitX_one μ hμ c), rfl⟩
  · exact ⟨_, mem_secGraph (secOrbitY_mem_secM μ 2 c) (adRel_secOrbitY_two μ hμ c), rfl⟩
  · exact ⟨_, mem_secGraph (secOrbitY_mem_secM μ 1 c) (adRel_secOrbitY_one μ hμ c), rfl⟩
  · exact absurd rfl hij

@[expose] def secTorTuple (s u : Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  ![s, s, u, s]

theorem mem_snd_secGraph_diagonal [IsAlgClosed L] {μ : Lˣ} (g : GL (Fin 3) L)
    {d : Fin 3 → L} (hg : (g : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) :
    ProjGenLinGroup.mk g ∈ (secGraph μ).map (MonoidHom.snd _ _) := by
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hg]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero
  rw [Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have hd0 : d 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hd1 : d 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hd2 : d 2 ≠ 0 := fun h => hdet (by rw [h]; ring)
  set s : Lˣ := Units.mk0 (d 0 / d 1) (div_ne_zero hd0 hd1)
  set u : Lˣ := Units.mk0 (d 1 ^ 2 / (d 0 * d 2)) (div_ne_zero (pow_ne_zero 2 hd1)
    (mul_ne_zero hd0 hd2))
  set a := secTorTuple s u with ha
  have ha1 : a 1 = a 0 := rfl
  have ha3 : a 3 = a 0 := rfl
  have hT : rootDiagUnit TwistTag.D4.tag a ∈ torusGroup TwistTag.D4.tag L :=
    rootDiagUnit_mem_torusGroup a
  have hP : rootDiagUnit TwistTag.D4.tag a ∈
      graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) := by
    have hTG : torusGroup TwistTag.D4.tag L ≤ adjointGroup TwistTag.D4.tag L :=
      (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
    refine Subgroup.mem_inf.2 ⟨hTG hT, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine (rootDiagUnit_commute_diagramMap_iff a).2 ?_
    funext i
    fin_cases i <;> rfl
  refine ⟨_, mem_secGraph (mem_secM_of_mem_torus μ hT hP) (adRel_rootDiagUnit μ ha1 ha3), ?_⟩
  simp only [MonoidHom.coe_snd]
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 (d 2) hd2, Units.ext ?_⟩
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hg]
  simp only [dgGL, secTorD, ha, secTorTuple, Units.val_mk0, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal]
  have hs : (s : L) = d 0 / d 1 := rfl
  have hu : (u : L) = d 1 ^ 2 / (d 0 * d 2) := rfl
  congr 1
  funext k
  fin_cases k <;> simp [hs, hu] <;> field_simp

theorem exists_secGraph_of_pgl [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    (P : PGL(3, L)) : ∃ m, (m, P) ∈ secGraph μ := by
  suffices h : ∀ g : GL (Fin 3) L,
      ProjGenLinGroup.mk g ∈ (secGraph μ).map (MonoidHom.snd _ _) by
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective P
    obtain ⟨p, hp, hpg⟩ := h g
    exact ⟨p.1, by rw [← hpg]; exact hp⟩
  intro g
  have key : ∀ M : Matrix (Fin 3) (Fin 3) L, M.det ≠ 0 → ∀ g : GL (Fin 3) L,
      (g : Matrix (Fin 3) (Fin 3) L) = M →
        ProjGenLinGroup.mk g ∈ (secGraph μ).map (MonoidHom.snd _ _) := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => ∀ g : GL (Fin 3) L,
      (g : Matrix (Fin 3) (Fin 3) L) = M →
        ProjGenLinGroup.mk g ∈ (secGraph μ).map (MonoidHom.snd _ _)) M hM ?_ ?_ ?_
    · intro D _ g hg
      exact mem_snd_secGraph_diagonal g hg
    · intro t g hg
      have : g = tvGL t.hij t.c := Units.ext hg
      rw [this]
      exact mem_snd_secGraph_tvGL hμ t.hij t.c
    · intro A B hA hB hPA hPB g hg
      set gA : GL (Fin 3) L := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
      set gB : GL (Fin 3) L := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
      have hgAB : g = gA * gB := Units.ext (by rw [hg]; rfl)
      rw [hgAB, map_mul]
      exact mul_mem (hPA gA rfl) (hPB gB rfl)
  exact key _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero g rfl

@[expose] def secGraphFst (μ : Lˣ) : secGraph μ →* secM μ where
  toFun p := ⟨p.1.1, p.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def secGraphSnd (μ : Lˣ) : secGraph μ →* PGL(3, L) where
  toFun p := p.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem secGraphFst_bijective {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) :
    Function.Bijective (secGraphFst (L := L) μ) := by
  refine ⟨fun p q hpq => ?_, fun m => ?_⟩
  · have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hpq
    have hq : (p.1.1, q.1.2) ∈ secGraph μ := by rw [h1]; exact q.2
    have h2 := secGraph_snd_eq p.2 hq
    exact Subtype.ext (Prod.ext h1 h2)
  · obtain ⟨P, hP⟩ := exists_secGraph_of_mem_secM hμ m.2
    exact ⟨⟨(m.1, P), hP⟩, rfl⟩

theorem secGraphSnd_bijective [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) :
    Function.Bijective (secGraphSnd (L := L) μ) := by
  refine ⟨fun p q hpq => ?_, fun P => ?_⟩
  · have h2 : p.1.2 = q.1.2 := hpq
    have hq := (secGraph μ).mul_mem ((secGraph μ).inv_mem p.2) q.2
    have hq' : ((p.1.1)⁻¹ * q.1.1, (1 : PGL(3, L))) ∈ secGraph μ := by
      have e : ((p.1 : ModGL TwistTag.D4.tag L × PGL(3, L))⁻¹ * q.1) =
          ((p.1.1)⁻¹ * q.1.1, (1 : PGL(3, L))) := by
        refine Prod.ext rfl ?_
        change (p.1.2)⁻¹ * q.1.2 = 1
        rw [h2, inv_mul_cancel]
      rw [← e]
      exact hq
    have h1 := eq_one_of_mem_secGraph hμ hq'
    exact Subtype.ext (Prod.ext (inv_mul_eq_one.1 h1) h2)
  · obtain ⟨m, hm⟩ := exists_secGraph_of_pgl hμ P
    exact ⟨⟨(m, P), hm⟩, rfl⟩

@[expose] def secPhi [IsAlgClosed L] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) :
    secM μ ≃* PGL(3, L) :=
  (MulEquiv.ofBijective _ (secGraphFst_bijective hμ)).symm.trans
    (MulEquiv.ofBijective _ (secGraphSnd_bijective hμ))

theorem secPhi_mem [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) (m : secM μ) :
    ((m : ModGL TwistTag.D4.tag L), secPhi μ hμ m) ∈ secGraph μ := by
  set p := (MulEquiv.ofBijective _ (secGraphFst_bijective (L := L) hμ)).symm m with hp
  have h1 : secGraphFst μ p = m :=
    (MulEquiv.ofBijective _ (secGraphFst_bijective (L := L) hμ)).apply_symm_apply m
  have e : ((m : ModGL TwistTag.D4.tag L), secPhi μ hμ m) = p.1 := by
    refine Prod.ext ?_ rfl
    rw [← h1]
    rfl
  rw [e]
  exact p.2

end CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof
