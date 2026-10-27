module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamGen
public import CFSG.LocalAnalysis.StandardType.PhanEResFrame
public import CFSG.LocalAnalysis.StandardType.PhanEStdSetting

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.AGLEmbeddingD2.ParabLevi

open scoped commutatorElement

section Matrices

variable {Fld : Type} [Field Fld] {m : ℕ}

private theorem hmbSM_Vsub_eq_flagSpace (F : Type) [Field F] (n c : ℕ) :
    Vsub (K := F) n c = LinearFlag.flagSpace n F c := by
  apply Submodule.ext
  intro v
  rw [LinearFlag.mem_flagSpace]
  rfl

private theorem hmbSM_glLin_mul {F : Type} [Field F] {n : ℕ} (g h : GL (Fin n) F) :
    glLin (g * h) = (glLin h).trans (glLin g) := by
  ext v
  rw [glLin_apply, LinearEquiv.trans_apply, glLin_apply, glLin_apply]
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

private theorem hmbSM_glLin_one {F : Type} [Field F] {n : ℕ} :
    glLin (1 : GL (Fin n) F) = LinearEquiv.refl F (Fin n → F) := by
  ext v
  rw [glLin_apply]
  simp

private theorem hmbSM_glLin_inv {F : Type} [Field F] {n : ℕ} (g : GL (Fin n) F) :
    glLin g⁻¹ = (glLin g).symm := by
  apply LinearEquiv.ext
  intro v
  apply (glLin g).injective
  rw [LinearEquiv.apply_symm_apply, glLin_apply, glLin_apply, Matrix.mulVec_mulVec,
    ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

private theorem hmbSM_map_Vsub_upper {F : Type} [Field F] {m : ℕ} (k : Fin m) (c : F)
    (c₀ : ℕ) :
    (Vsub (m + 1) c₀).map
        (glLin (SpecialLinearGroup.toGL (tv F k.castSucc k.succ c))).toLinearMap =
      Vsub (m + 1) c₀ := by
  have hne : k.castSucc ≠ k.succ := k.castSucc_lt_succ.ne
  refine Submodule.eq_of_le_of_finrank_eq ?_
    (LinearEquiv.finrank_map_eq (glLin (SpecialLinearGroup.toGL (tv F k.castSucc k.succ c)))
      (Vsub (m + 1) c₀))
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  change (glLin (SpecialLinearGroup.toGL (tv F k.castSucc k.succ c))) v ∈
    Vsub (m + 1) c₀
  rw [hmbSM_Vsub_eq_flagSpace F (m + 1) c₀] at hv ⊢
  rw [LinearFlag.mem_flagSpace] at hv ⊢
  intro j hj
  rw [glLin_apply, SpecialLinearGroup.coe_GL_coe_matrix, tv_of_ne hne,
    SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  by_cases hjc : j = k.castSucc
  · subst hjc
    have h1 : v k.castSucc = 0 := hv k.castSucc hj
    have h2 : v k.succ = 0 :=
      hv k.succ (le_trans hj (by rw [Fin.val_succ, Fin.val_castSucc]; exact Nat.le_succ _))
    simp [h1, h2]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hjc, smul_eq_mul, mul_zero,
      add_zero]
    exact hv j hj

private theorem hmbSM_map_Vsub_lower {F : Type} [Field F] {m : ℕ} (k : Fin m) (c : F)
    {c₀ : ℕ} (hc₀ : c₀ ≠ k.val + 1) :
    (Vsub (m + 1) c₀).map
        (glLin (SpecialLinearGroup.toGL (tv F k.succ k.castSucc c))).toLinearMap =
      Vsub (m + 1) c₀ := by
  have hne : k.succ ≠ k.castSucc := k.castSucc_lt_succ.ne.symm
  refine Submodule.eq_of_le_of_finrank_eq ?_
    (LinearEquiv.finrank_map_eq (glLin (SpecialLinearGroup.toGL (tv F k.succ k.castSucc c)))
      (Vsub (m + 1) c₀))
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  change (glLin (SpecialLinearGroup.toGL (tv F k.succ k.castSucc c))) v ∈
    Vsub (m + 1) c₀
  rw [hmbSM_Vsub_eq_flagSpace F (m + 1) c₀] at hv ⊢
  rw [LinearFlag.mem_flagSpace] at hv ⊢
  intro j hj
  rw [glLin_apply, SpecialLinearGroup.coe_GL_coe_matrix, tv_of_ne hne,
    SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  by_cases hjc : j = k.succ
  · subst hjc
    have hj' : c₀ ≤ k.val + 1 := by simpa [Fin.val_succ] using hj
    have hlt : c₀ ≤ k.val := by omega
    have h1 : v k.castSucc = 0 := hv k.castSucc (by simpa [Fin.val_castSucc] using hlt)
    have h2 : v k.succ = 0 := hv k.succ (by simpa [Fin.val_succ] using hj')
    simp [h1, h2]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hjc, smul_eq_mul, mul_zero,
      add_zero]
    exact hv j hj

private theorem hmbSM_map_Vsub_diagonal {F : Type} [Field F] {n : ℕ} {D : GL (Fin n) F}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) F) i j = 0) (c : ℕ) :
    (Vsub n c).map (glLin D).toLinearMap = Vsub n c := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq (glLin D) (Vsub n c))
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  change (glLin D) v ∈ Vsub n c
  rw [hmbSM_Vsub_eq_flagSpace F n c] at hv ⊢
  rw [LinearFlag.mem_flagSpace] at hv ⊢
  intro j hj
  rw [glLin_apply, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = j
  · rw [hk, hv j hj, mul_zero]
  · rw [hD j k (Ne.symm hk), zero_mul]

private theorem hmbSM_map_Vsub_of_mem_blockSL {F : Type} [Field F] {m : ℕ}
    (d : List ℕ) (A : SpecialLinearGroup (Fin (m + 1)) F) (hA : A ∈ blockSL F m d)
    (b : ℕ) (hb : b < d.length) :
    (Vsub (m + 1) (d.getD b 0)).map
        (glLin (SpecialLinearGroup.toGL A)).toLinearMap =
      Vsub (m + 1) (d.getD b 0) := by
  let P : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    { carrier := {A | (Vsub (m + 1) (d.getD b 0)).map
          (glLin (SpecialLinearGroup.toGL A)).toLinearMap = Vsub (m + 1) (d.getD b 0)}
      one_mem' := by
        show (Vsub (m + 1) (d.getD b 0)).map
          (glLin (SpecialLinearGroup.toGL (1 : SpecialLinearGroup (Fin (m + 1)) F))).toLinearMap
            = Vsub (m + 1) (d.getD b 0)
        rw [map_one]
        show (Vsub (m + 1) (d.getD b 0)).map
          (glLin (1 : GL (Fin (m + 1)) F)).toLinearMap = Vsub (m + 1) (d.getD b 0)
        rw [hmbSM_glLin_one]
        change (Vsub (m + 1) (d.getD b 0)).map
          (LinearMap.id : (Fin (m + 1) → F) →ₗ[F] (Fin (m + 1) → F)) =
            Vsub (m + 1) (d.getD b 0)
        rw [Submodule.map_id]
      mul_mem' := by
        intro A B hA hB
        show (Vsub (m + 1) (d.getD b 0)).map
          (glLin (SpecialLinearGroup.toGL (A * B))).toLinearMap = Vsub (m + 1) (d.getD b 0)
        rw [map_mul, hmbSM_glLin_mul]
        change (Vsub (m + 1) (d.getD b 0)).map
          ((glLin (SpecialLinearGroup.toGL A)).toLinearMap.comp
            (glLin (SpecialLinearGroup.toGL B)).toLinearMap) = Vsub (m + 1) (d.getD b 0)
        rw [Submodule.map_comp, hB, hA]
      inv_mem' := by
        intro A hA
        have hcomp : (glLin (SpecialLinearGroup.toGL A⁻¹)).toLinearMap.comp
            (glLin (SpecialLinearGroup.toGL A)).toLinearMap = LinearMap.id := by
          rw [map_inv, hmbSM_glLin_inv]
          ext v
          simp
        have h' := congrArg (fun q => q.map
          (glLin (SpecialLinearGroup.toGL A⁻¹)).toLinearMap) hA
        rw [← Submodule.map_comp, hcomp, Submodule.map_id] at h'
        exact h'.symm }
  have hgen : ∀ A ∈ ({A | ∃ k : Fin m, k ∈ cutTypes m d ∧ ∃ c : F,
      A = tv F k.castSucc k.succ c ∨ A = tv F k.succ k.castSucc c} : Set _), A ∈ P := by
    rintro A ⟨k, hk, c, h | h⟩
    · rw [h]
      exact hmbSM_map_Vsub_upper k c (d.getD b 0)
    · rw [h]
      exact hmbSM_map_Vsub_lower k c (hk b hb)
  rw [blockSL] at hA
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact P.one_mem
  | mul x y hx hy ihx ihy => exact P.mul_mem ihx ihy
  | inv x hx ih => exact P.inv_mem ih

private theorem hmbSM_map_Vsub_mul {F : Type} [Field F] {n : ℕ} {A B : GL (Fin n) F} {c : ℕ}
    (hA : (Vsub n c).map (glLin A).toLinearMap = Vsub n c)
    (hB : (Vsub n c).map (glLin B).toLinearMap = Vsub n c) :
    (Vsub n c).map (glLin (A * B)).toLinearMap = Vsub n c := by
  rw [hmbSM_glLin_mul]
  change (Vsub n c).map
    ((glLin A).toLinearMap.comp (glLin B).toLinearMap) = Vsub n c
  rw [Submodule.map_comp, hB, hA]

end Matrices

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable {M : ChevModel2 D n H Fld} {m : ℕ}

theorem map_blockSL (L : SLPath M m) (d : List ℕ) :
    (blockSL Fld m d).map L.ε = leviM D (L.e '' cutTypes m d) := by
  have hCT := isCTRootSystem D.isFiniteType D.divisible
  have hpos : ∀ i : Fin D.rank, Pi.single i 1 ∈ D.roots := fun i => hCT.single_mem i
  have hneg : ∀ i : Fin D.rank, -Pi.single i 1 ∈ D.roots := fun i => by
    have h := hCT.smul_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i)
      (Pi.single i 1) (hCT.single_mem i)
    rwa [hCT.simple_single] at h
  rw [blockSL, MonoidHom.map_closure L.ε]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨A, ⟨k, hk, c, h | h⟩, rfl⟩
    · rw [h, L.tv_eq k.castSucc k.succ (hmbSM_castSucc_ne_succ k) c,
        pathRoot_castSucc_succ]
      refine rankOne_le_leviM (i := L.e k) (I := L.e '' cutTypes m d) ⟨k, hk, rfl⟩ ?_
      exact Subgroup.mem_sup_left
        ((M.x_mem (Pi.single (L.e k) 1) (hpos (L.e k)) _).mpr ⟨c, rfl⟩)
    · rw [h, L.tv_eq k.succ k.castSucc (hmbSM_castSucc_ne_succ k).symm c,
        pathRoot_succ_castSucc]
      refine rankOne_le_leviM (i := L.e k) (I := L.e '' cutTypes m d) ⟨k, hk, rfl⟩ ?_
      exact Subgroup.mem_sup_right
        ((M.x_mem (-Pi.single (L.e k) 1) (hneg (L.e k)) _).mpr ⟨c, rfl⟩)
  · rw [leviM]
    refine iSup₂_le ?_
    rintro i ⟨k, hk, rfl⟩
    rw [show rankOne D.rootGroup (L.e k) =
        D.rootGroup (Pi.single (L.e k) 1) ⊔ D.rootGroup (-Pi.single (L.e k) 1) from rfl]
    refine sup_le ?_ ?_
    · rintro y hy
      obtain ⟨c, rfl⟩ := (M.x_mem (Pi.single (L.e k) 1) (hpos (L.e k)) y).mp hy
      refine Subgroup.subset_closure ⟨tv Fld k.castSucc k.succ c, ⟨k, hk, c, Or.inl rfl⟩, ?_⟩
      rw [L.tv_eq k.castSucc k.succ (hmbSM_castSucc_ne_succ k) c, pathRoot_castSucc_succ]
    · rintro y hy
      obtain ⟨c, rfl⟩ := (M.x_mem (-Pi.single (L.e k) 1) (hneg (L.e k)) y).mp hy
      refine Subgroup.subset_closure ⟨tv Fld k.succ k.castSucc c, ⟨k, hk, c, Or.inr rfl⟩, ?_⟩
      rw [L.tv_eq k.succ k.castSucc (hmbSM_castSucc_ne_succ k).symm c, pathRoot_succ_castSucc]

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

include hext hw₀ hsq in
theorem exists_seam [CharP Fld 2] (L : SLPath M m) {J : Set (Fin D.rank)} (hJ : Set.range L.e = J)
    {a : K ⧸ borel D H} {g : K} {v : W} {I : Set (Fin D.rank)} {t₀ l₀ : K} (hIJ : I ⊆ J)
    (hR : residue (cs) (stdδ hct) J a = residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))
    (hcore : Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a =
      residue (cs) (stdδ hct) I ((g : K) : K ⧸ borel D H))
    (ht₀ : t₀ ∈ ⨆ k, H k) (hl₀ : l₀ ∈ leviM D I)
    (hψ : ∀ l ∈ leviM D I,
      Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a ((g * l : K) : K ⧸ borel D H) =
        ((g * t₀ * l₀ * (nrep hct v * F.φ l * (nrep hct v)⁻¹) : K) : K ⧸ borel D H))
    {d : List ℕ} (hd : IsCut (m + 1) d) (hI : ∀ k, L.e k ∈ I ↔ k ∈ cutTypes m d)
    (θ : Fld →+* Fld) (P : SpecialLinearGroup (Fin (m + 1)) Fld) (pol : Bool)
    (hPu : ∀ k ∈ cutTypes m d, ∀ c : Fld,
      nrep hct v * F.φ (L.ε (tv Fld k.castSucc k.succ c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol P (tv Fld k.castSucc k.succ c)))
    (hPl : ∀ k ∈ cutTypes m d, ∀ c : Fld,
      nrep hct v * F.φ (L.ε (tv Fld k.succ k.castSucc c)) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol P (tv Fld k.succ k.castSucc c))) :
    ∃ (Θ₀ : ChamberIso ((buildingOver (cs) (stdδ hct) J).restrict (residue (cs) (stdδ hct) J a))
        (flagSys Fld m)) (N : GL (Fin (m + 1)) Fld),
      (∀ b, b < d.length → (Vsub (m + 1) (d.getD b 0)).map (glLin N).toLinearMap =
        Vsub (m + 1) (d.getD b 0)) ∧
      (∀ c : ↥(residue (cs) (stdδ hct) J a),
        (c : K ⧸ borel D H) ∈ Gate.flipCore (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a ↔
          Θ₀.Φ c ∈ refSet Fld (m + 1) d) ∧
      ∀ A ∈ blockSL Fld m d, ∀ c c' : ↥(residue (cs) (stdδ hct) J a),
        Θ₀.Φ c = flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)) →
        (c' : K ⧸ borel D H) =
          Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a (c : K ⧸ borel D H) →
        Θ₀.Φ c' = flagAct N
          (flagAct (SpecialLinearGroup.toGL (kapMat θ pol P A)) (stdFlag Fld (m + 1))) := by
  classical
  have hIeq : I = L.e '' cutTypes m d := by
    ext x
    constructor
    · intro hx
      have hxJ : x ∈ Set.range L.e := by rw [hJ]; exact hIJ hx
      obtain ⟨k, hk⟩ := hxJ
      subst hk
      exact ⟨k, (hI k).mp hx, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact (hI k).mpr hk
  have hlevi : leviM D I = (blockSL Fld m d).map L.ε := by
    rw [hIeq, ← map_blockSL L d]
  obtain ⟨A₀, hA₀, hA₀eq⟩ : ∃ A₀ ∈ blockSL Fld m d, L.ε A₀ = l₀ := by
    have hl : l₀ ∈ (blockSL Fld m d).map L.ε := by
      rw [← hlevi]
      exact hl₀
    exact Subgroup.mem_map.mp hl
  have hcap : ∀ A ∈ blockSL Fld m d,
      nrep hct v * F.φ (L.ε A) * (nrep hct v)⁻¹ = L.ε (kapMat θ pol P A) := by
    intro A hA
    let fHom : SpecialLinearGroup (Fin (m + 1)) Fld →* K :=
      (MulAut.conj (nrep hct v)).toMonoidHom.comp (F.φ.comp L.ε)
    let gHom : SpecialLinearGroup (Fin (m + 1)) Fld →* K := L.ε.comp (kapMat θ pol P)
    have hfg : ∀ A ∈ blockSL Fld m d, fHom A = gHom A := by
      intro A hA
      rw [blockSL] at hA
      induction hA using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with ⟨k, hk, c, h | h⟩
        · rw [h]
          simpa [fHom, gHom, MonoidHom.comp_apply, MulAut.conj_apply] using hPu k hk c
        · rw [h]
          simpa [fHom, gHom, MonoidHom.comp_apply, MulAut.conj_apply] using hPl k hk c
      | one => simp [fHom, gHom]
      | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy]
      | inv x hx ih => rw [map_inv, map_inv, ih]
    have h := hfg A hA
    simpa [fHom, gHom, MonoidHom.comp_apply, MulAut.conj_apply] using h
  let Θ₀ : ChamberIso
      ((buildingOver (cs) (stdδ hct) J).restrict (residue (cs) (stdδ hct) J a))
      (flagSys Fld m) :=
    (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).trans
      (slChart hct hext L hJ g)
  obtain ⟨Dt, hDt_diag, hDt_prop⟩ := slChart_coord_torus hct hext L hJ g ht₀
  refine ⟨Θ₀, Dt * SpecialLinearGroup.toGL A₀, ?_, ?_, ?_⟩
  ·
    intro b hb
    have hDs := hmbSM_map_Vsub_diagonal hDt_diag (d.getD b 0)
    have hAs := hmbSM_map_Vsub_of_mem_blockSL d A₀ hA₀ b hb
    simpa using hmbSM_map_Vsub_mul hDs hAs
  ·
    intro c
    have hg_mem : ((g : K) : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) J a :=
      hR.symm ▸ self_mem_residue J ((g : K) : K ⧸ borel D H)
    let x : ↥(residue (cs) (stdδ hct) J a) := ⟨((g : K) : K ⧸ borel D H), hg_mem⟩
    have hxΦ : Θ₀.Φ x = stdFlag Fld (m + 1) := by
      have h1 : (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).Φ x =
          ⟨((g * L.ε (1 : SpecialLinearGroup (Fin (m + 1)) Fld) : K) : K ⧸ borel D H),
            mk_mul_ε_mem_residue hct hext L hJ g 1⟩ := by
        apply Subtype.ext
        change (x : K ⧸ borel D H) =
          ((g * L.ε (1 : SpecialLinearGroup (Fin (m + 1)) Fld) : K) : K ⧸ borel D H)
        simp [x]
      rw [ChamberIso.trans_Φ_apply, h1, slChart_apply hct hext L hJ g 1, map_one, flagAct_one]
    have hΘe : Θ₀.e = (slChart hct hext L hJ g).e := by
      simp [Θ₀, ChamberIso.trans, ChamberIso.restrictCongr]
    have hchar : ∀ j : ↥J, (slChart hct hext L hJ g).e j ∈ cutTypes m d ↔
        (j : Fin D.rank) ∈ I := by
      intro j
      have hjJ : (j : Fin D.rank) ∈ Set.range L.e := by rw [hJ]; exact j.2
      obtain ⟨k, hk⟩ := hjJ
      have hxJ : L.e k ∈ J := by rw [hk]; exact j.2
      have hjk : j = (⟨L.e k, hxJ⟩ : ↥J) := by
        apply Subtype.ext
        exact hk.symm
      rw [hjk, slChart_e_apply hct hext L hJ g k hxJ]
      exact (hI k).symm
    have htype : Θ₀.e '' {j : ↥J | (j : Fin D.rank) ∈ I} = cutTypes m d := by
      rw [hΘe]
      ext k
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact (hchar j).mpr hj
      · intro hk
        refine ⟨(slChart hct hext L hJ g).e.symm k, ?_, ?_⟩
        · exact (hchar _).mp (by rw [Equiv.apply_symm_apply]; exact hk)
        · exact Equiv.apply_symm_apply _ _
    have hresid : (flagSys Fld m).residue (cutTypes m d) (stdFlag Fld (m + 1)) =
        refSet Fld (m + 1) d := by
      rw [← residue_flagδ_eq (K := Fld) (cutTypes m d) (stdFlag Fld (m + 1)),
        residue_cutTypes_eq hd (stdFlag_mem_refSet (K := Fld) hd)]
    have hmem := mem_residue_iff_of_chamberIso (stdBuilding hct hext) Θ₀ hIJ x c
    rw [htype, hxΦ, hresid] at hmem
    rw [hcore]
    exact hmem
  ·
    intro A hA c c' hc hc'
    have hAlevi : L.ε A ∈ leviM D I := by
      rw [hlevi]
      exact Subgroup.mem_map_of_mem L.ε hA
    have hΦ : Θ₀.Φ c = (slChart hct hext L hJ g).Φ
        ((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).Φ c) :=
      ChamberIso.trans_Φ_apply _ _ c
    have h1 : (ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).Φ c =
        (slChart hct hext L hJ g).Φ.symm
          (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))) := by
      apply (Equiv.eq_symm_apply (slChart hct hext L hJ g).Φ).mpr
      rw [← hc]
      exact hΦ.symm
    have hcl : (c : K ⧸ borel D H) = ((g * L.ε A : K) : K ⧸ borel D H) := by
      calc (c : K ⧸ borel D H)
          = (((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).Φ c :
              ↥(residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))) : K ⧸ borel D H) := rfl
        _ = (((slChart hct hext L hJ g).Φ.symm
              (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))) :
              ↥(residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))) : K ⧸ borel D H) :=
            congrArg Subtype.val h1
        _ = ((g * L.ε A : K) : K ⧸ borel D H) := slChart_symm_apply hct hext L hJ g A
    have hκ : nrep hct v * F.φ (L.ε A) * (nrep hct v)⁻¹ =
        L.ε (kapMat θ pol P A) := hcap A hA
    have hmain : (c' : K ⧸ borel D H) =
        ((g * t₀ * L.ε (A₀ * kapMat θ pol P A) : K) : K ⧸ borel D H) := by
      have hK : g * t₀ * l₀ * (nrep hct v * F.φ (L.ε A) * (nrep hct v)⁻¹) =
          g * t₀ * L.ε (A₀ * kapMat θ pol P A) := by
        rw [hκ, map_mul, hA₀eq]
        group
      calc (c' : K ⧸ borel D H)
          = Gate.flipPsi (cs) (stdδ hct) (stdFlip F (nrep hct w₀)) J a
              (c : K ⧸ borel D H) := hc'
        _ = ((g * t₀ * l₀ * (nrep hct v * F.φ (L.ε A) * (nrep hct v)⁻¹) : K) :
              K ⧸ borel D H) := by
              rw [hcl]
              exact hψ (L.ε A) hAlevi
        _ = ((g * t₀ * L.ε (A₀ * kapMat θ pol P A) : K) : K ⧸ borel D H) := by
              rw [hK]
    have hxg : (((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).Φ c' :
        ↥(residue (cs) (stdδ hct) J ((g : K) : K ⧸ borel D H))) : K ⧸ borel D H) =
        ((g * t₀ * L.ε (A₀ * kapMat θ pol P A) : K) : K ⧸ borel D H) := by
      change (c' : K ⧸ borel D H) = _
      rw [hmain]
    have hDt_c' := hDt_prop (A₀ * kapMat θ pol P A)
      ((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).Φ c') hxg
    calc Θ₀.Φ c' = (slChart hct hext L hJ g).Φ
          ((ChamberIso.restrictCongr (buildingOver (cs) (stdδ hct) J) hR).Φ c') :=
            ChamberIso.trans_Φ_apply _ _ c'
      _ = flagAct Dt (flagAct (SpecialLinearGroup.toGL (A₀ * kapMat θ pol P A))
            (stdFlag Fld (m + 1))) := hDt_c'
      _ = flagAct Dt (flagAct (SpecialLinearGroup.toGL A₀ *
            SpecialLinearGroup.toGL (kapMat θ pol P A)) (stdFlag Fld (m + 1))) := by
            rw [map_mul]
      _ = flagAct Dt (flagAct (SpecialLinearGroup.toGL A₀)
            (flagAct (SpecialLinearGroup.toGL (kapMat θ pol P A)) (stdFlag Fld (m + 1)))) := by
            rw [flagAct_mul]
      _ = flagAct (Dt * SpecialLinearGroup.toGL A₀)
            (flagAct (SpecialLinearGroup.toGL (kapMat θ pol P A)) (stdFlag Fld (m + 1))) := by
            rw [← flagAct_mul]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end