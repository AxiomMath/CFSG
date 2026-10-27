module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProdAux

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.AGLEmbeddingD2.ParabLevi

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable {M : ChevModel2 D n H Fld}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {w₀ : W} (F : FrobData D n H w₀)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

section ProdResidue

variable {ι₁ ι₂ C₁ C₂ : Type}

private theorem hmbSP_prod_gallery_fst (X : ChamberSystem ι₁ C₁) (Y : ChamberSystem ι₂ C₂)
    {S₁ : Set ι₁} {S₂ : Set ι₂} {x : C₁} {y : C₂} {γ : List ((ι₁ ⊕ ι₂) × (C₁ × C₂))}
    (hγ : (X.prod Y).IsGallery (x, y) γ)
    (hJ : ∀ i ∈ galleryType γ, i ∈ Sum.inl '' S₁ ∪ Sum.inr '' S₂) :
    (galleryEnd (x, y) γ).1 ∈ X.residue S₁ x := by
  induction γ generalizing x y with
  | nil => exact X.self_mem_residue S₁ x
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨i, c, d⟩ := p
    have htail : (galleryEnd (c, d) γ).1 ∈ X.residue S₁ c :=
      ih h2 (fun k hk => hJ k (by simp [hk]))
    have hp := hJ i (by simp)
    rw [galleryEnd_cons]
    cases i with
    | inl i₁ =>
      have hx : X.adj i₁ x c := h1.1
      have hi₁ : i₁ ∈ S₁ := by
        rcases hp with ⟨k, hk, hk'⟩ | ⟨k, hk, hk'⟩
        · exact (Sum.inl.inj hk') ▸ hk
        · exact absurd hk' (by simp)
      exact X.mem_residue_trans (X.residue_mono (Set.singleton_subset_iff.mpr hi₁) x
        (X.mem_residue_singleton.mpr hx)) htail
    | inr i₂ =>
      have hx : x = c := h1.1
      rw [hx]
      exact htail

private theorem hmbSP_prod_gallery_snd (X : ChamberSystem ι₁ C₁) (Y : ChamberSystem ι₂ C₂)
    {S₁ : Set ι₁} {S₂ : Set ι₂} {x : C₁} {y : C₂} {γ : List ((ι₁ ⊕ ι₂) × (C₁ × C₂))}
    (hγ : (X.prod Y).IsGallery (x, y) γ)
    (hJ : ∀ i ∈ galleryType γ, i ∈ Sum.inl '' S₁ ∪ Sum.inr '' S₂) :
    (galleryEnd (x, y) γ).2 ∈ Y.residue S₂ y := by
  induction γ generalizing x y with
  | nil => exact Y.self_mem_residue S₂ y
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨i, c, d⟩ := p
    have htail : (galleryEnd (c, d) γ).2 ∈ Y.residue S₂ d :=
      ih h2 (fun k hk => hJ k (by simp [hk]))
    have hp := hJ i (by simp)
    rw [galleryEnd_cons]
    cases i with
    | inl i₁ =>
      have hy : y = d := h1.2
      rw [hy]
      exact htail
    | inr i₂ =>
      have hy : Y.adj i₂ y d := h1.2
      have hi₂ : i₂ ∈ S₂ := by
        rcases hp with ⟨k, hk, hk'⟩ | ⟨k, hk, hk'⟩
        · exact absurd hk' (by simp)
        · exact (Sum.inr.inj hk') ▸ hk
      exact Y.mem_residue_trans (Y.residue_mono (Set.singleton_subset_iff.mpr hi₂) y
        (Y.mem_residue_singleton.mpr hy)) htail

private theorem hmbSP_prod_gallery_inl (X : ChamberSystem ι₁ C₁) (Y : ChamberSystem ι₂ C₂)
    {x : C₁} {y : C₂} {γ₁ : List (ι₁ × C₁)} (hγ₁ : X.IsGallery x γ₁) :
    (X.prod Y).IsGallery (x, y)
        (γ₁.map (fun p => ((Sum.inl p.1 : ι₁ ⊕ ι₂), (p.2, y)))) ∧
      galleryEnd (x, y) (γ₁.map (fun p => ((Sum.inl p.1 : ι₁ ⊕ ι₂), (p.2, y)))) =
        (galleryEnd x γ₁, y) := by
  induction γ₁ generalizing x with
  | nil => exact ⟨trivial, rfl⟩
  | cons p γ₁ ih =>
    obtain ⟨h1, h2⟩ := hγ₁
    obtain ⟨h1', h2'⟩ := ih h2
    exact ⟨⟨⟨h1, rfl⟩, h1'⟩, by simpa using h2'⟩

private theorem hmbSP_prod_gallery_inr (X : ChamberSystem ι₁ C₁) (Y : ChamberSystem ι₂ C₂)
    {x : C₁} {y : C₂} {γ₂ : List (ι₂ × C₂)} (hγ₂ : Y.IsGallery y γ₂) :
    (X.prod Y).IsGallery (x, y)
        (γ₂.map (fun p => ((Sum.inr p.1 : ι₁ ⊕ ι₂), (x, p.2)))) ∧
      galleryEnd (x, y) (γ₂.map (fun p => ((Sum.inr p.1 : ι₁ ⊕ ι₂), (x, p.2)))) =
        (x, galleryEnd y γ₂) := by
  induction γ₂ generalizing y with
  | nil => exact ⟨trivial, rfl⟩
  | cons p γ₂ ih =>
    obtain ⟨h1, h2⟩ := hγ₂
    obtain ⟨h1', h2'⟩ := ih h2
    exact ⟨⟨⟨rfl, h1⟩, h1'⟩, by simpa using h2'⟩

theorem hmbSP_prod_residue (X : ChamberSystem ι₁ C₁) (Y : ChamberSystem ι₂ C₂)
    (S₁ : Set ι₁) (S₂ : Set ι₂) (x : C₁) (y : C₂) :
    (X.prod Y).residue (Sum.inl '' S₁ ∪ Sum.inr '' S₂) (x, y) =
      X.residue S₁ x ×ˢ Y.residue S₂ y := by
  ext p
  obtain ⟨a, b⟩ := p
  constructor
  · rintro ⟨γ, hγ, hJ, hend⟩
    refine ⟨?_, ?_⟩
    · have h := hmbSP_prod_gallery_fst X Y hγ hJ
      rwa [hend] at h
    · have h := hmbSP_prod_gallery_snd X Y hγ hJ
      rwa [hend] at h
  · rintro ⟨ha, hb⟩
    obtain ⟨γ₁, hγ₁, hJ₁, hend₁⟩ := ha
    obtain ⟨γ₂, hγ₂, hJ₂, hend₂⟩ := hb
    refine ⟨(γ₁.map fun p => ((Sum.inl p.1 : ι₁ ⊕ ι₂), (p.2, y))) ++
      (γ₂.map fun p => ((Sum.inr p.1 : ι₁ ⊕ ι₂), (a, p.2))), ?_, ?_, ?_⟩
    · rw [ChamberSystem.isGallery_append]
      obtain ⟨h1a, h1b⟩ := hmbSP_prod_gallery_inl X Y hγ₁
      obtain ⟨h2a, h2b⟩ := hmbSP_prod_gallery_inr X Y (x := a) hγ₂
      rw [h1b, hend₁]
      exact ⟨h1a, h2a⟩
    · intro i hi
      rw [galleryType_append, List.mem_append] at hi
      rcases hi with hi | hi
      · rw [galleryType, List.map_map, List.mem_map] at hi
        obtain ⟨q, hq, hq'⟩ := hi
        exact Or.inl ⟨q.1, hJ₁ q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩), hq'⟩
      · rw [galleryType, List.map_map, List.mem_map] at hi
        obtain ⟨q, hq, hq'⟩ := hi
        exact Or.inr ⟨q.1, hJ₂ q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩), hq'⟩
    · obtain ⟨h1a, h1b⟩ := hmbSP_prod_gallery_inl X Y hγ₁
      obtain ⟨h2a, h2b⟩ := hmbSP_prod_gallery_inr X Y (x := a) hγ₂
      rw [galleryEnd_append, h1b, hend₁, h2b, hend₂]

end ProdResidue

section StabV

private theorem hmbSP_glLin_one {n : ℕ} :
    glLin (1 : GL (Fin n) Fld) = LinearEquiv.refl Fld (Fin n → Fld) := by
  ext v
  rw [glLin_apply]
  simp

private theorem hmbSP_glLin_mul {n : ℕ} (g h : GL (Fin n) Fld) :
    glLin (g * h) = (glLin h).trans (glLin g) := by
  ext v
  rw [glLin_apply, LinearEquiv.trans_apply, glLin_apply, glLin_apply,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

private theorem hmbSP_glLin_inv {n : ℕ} (g : GL (Fin n) Fld) :
    glLin g⁻¹ = (glLin g).symm := by
  have h : (glLin g).trans (glLin g⁻¹) = LinearEquiv.refl Fld (Fin n → Fld) := by
    rw [← hmbSP_glLin_mul, inv_mul_cancel, hmbSP_glLin_one]
  have hv : ∀ w, glLin g⁻¹ (glLin g w) = w := by
    intro w
    simpa [LinearEquiv.trans_apply] using
      congrArg (fun e : (Fin n → Fld) ≃ₗ[Fld] (Fin n → Fld) => e w) h
  apply LinearEquiv.ext
  intro v
  calc glLin g⁻¹ v = glLin g⁻¹ (glLin g ((glLin g).symm v)) := by
        rw [(glLin g).apply_symm_apply]
    _ = (glLin g).symm v := hv _

private theorem hmbSP_glLin_toGL {n : ℕ} (A : SpecialLinearGroup (Fin n) Fld) :
    (glLin (SpecialLinearGroup.toGL A)).toLinearMap = Matrix.mulVecLin A :=
  LinearMap.ext fun v => by
    change glLin (SpecialLinearGroup.toGL A) v = (A : Matrix (Fin n) (Fin n) Fld).mulVec v
    rw [glLin_apply]
    rfl

private theorem hmbSP_stabV_one {n : ℕ} (e : ℕ) :
    (Vsub n e).map (glLin (1 : GL (Fin n) Fld)).toLinearMap = Vsub n e := by
  rw [hmbSP_glLin_one]
  simp

theorem hmbSP_stabV_mul {n : ℕ} {g h : GL (Fin n) Fld} {e : ℕ}
    (hg : (Vsub n e).map (glLin g).toLinearMap = Vsub n e)
    (hh : (Vsub n e).map (glLin h).toLinearMap = Vsub n e) :
    (Vsub n e).map (glLin (g * h)).toLinearMap = Vsub n e := by
  rw [hmbSP_glLin_mul]
  change (Vsub n e).map ((glLin g).toLinearMap.comp (glLin h).toLinearMap) = Vsub n e
  rw [Submodule.map_comp, hh, hg]

private theorem hmbSP_stabV_inv {n : ℕ} {g : GL (Fin n) Fld} {e : ℕ}
    (hg : (Vsub n e).map (glLin g).toLinearMap = Vsub n e) :
    (Vsub n e).map (glLin g⁻¹).toLinearMap = Vsub n e := by
  rw [hmbSP_glLin_inv]
  have h := congrArg (Submodule.map (glLin g).symm.toLinearMap) hg
  rw [← Submodule.map_comp] at h
  have hcomp : ((glLin g).symm.toLinearMap.comp (glLin g).toLinearMap :
      (Fin n → Fld) →ₗ[Fld] (Fin n → Fld)) = LinearMap.id := by
    ext v; simp
  rw [hcomp, Submodule.map_id] at h
  exact h.symm

private theorem hmbSP_transvection_stabV {n : ℕ} (p q : Fin n) (c : Fld) (e : ℕ)
    (hpq : p ≠ q) (hcond : ¬ (q.val < e ∧ e ≤ p.val)) :
    (Vsub n e).map (Matrix.mulVecLin (Matrix.transvection p q c)) = Vsub n e := by
  have hle : ∀ c' : Fld,
      (Vsub n e).map (Matrix.mulVecLin (Matrix.transvection p q c')) ≤ Vsub n e := by
    intro c' w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    intro j hj
    rw [Matrix.mulVecLin_apply, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec_eq, Pi.add_apply, hv j hj]
    by_cases hjp : j = p
    · subst hjp
      have hqe : e ≤ q.val := by
        by_contra hlt
        rw [not_le] at hlt
        exact hcond ⟨hlt, hj⟩
      simp [Pi.smul_apply, Pi.single_eq_same, hv q hqe]
    · simp [Pi.smul_apply, Pi.single_eq_of_ne, hjp]
  apply le_antisymm (hle c)
  intro v hv
  refine ⟨Matrix.mulVecLin (Matrix.transvection p q (-c)) v,
    hle (-c) (Submodule.mem_map_of_mem hv), ?_⟩
  have hcomp : (Matrix.mulVecLin (Matrix.transvection p q c)).comp
      (Matrix.mulVecLin (Matrix.transvection p q (-c))) = LinearMap.id := by
    rw [← Matrix.mulVecLin_mul, Matrix.transvection_mul_transvection_same p q hpq c (-c),
      add_neg_cancel, Matrix.transvection_zero, Matrix.mulVecLin_one]
  exact congrFun (congrArg DFunLike.coe hcomp) v

theorem hmbSP_blockSL_stabV {m : ℕ} (d : List ℕ) :
    ∀ A ∈ blockSL Fld m d, ∀ b, b < d.length →
      (Vsub (m + 1) (d.getD b 0)).map
        (glLin (SpecialLinearGroup.toGL A)).toLinearMap = Vsub (m + 1) (d.getD b 0) := by
  let T : Subgroup (SpecialLinearGroup (Fin (m + 1)) Fld) :=
    { carrier := {A | ∀ b, b < d.length →
        (Vsub (m + 1) (d.getD b 0)).map
          (glLin (SpecialLinearGroup.toGL A)).toLinearMap = Vsub (m + 1) (d.getD b 0)}
      one_mem' := by intro b _; rw [map_one]; exact hmbSP_stabV_one _
      mul_mem' := by
        intro A B hA hB b hb
        rw [map_mul]
        exact hmbSP_stabV_mul (hA b hb) (hB b hb)
      inv_mem' := by
        intro A hA b hb
        rw [map_inv]
        exact hmbSP_stabV_inv (hA b hb) }
  have hle : blockSL Fld m d ≤ T := by
    rw [blockSL, Subgroup.closure_le]
    rintro A ⟨k, hk, c, h | h⟩
    · rw [h, tv_of_ne k.castSucc_lt_succ.ne]
      intro b _
      rw [hmbSP_glLin_toGL]
      exact hmbSP_transvection_stabV k.castSucc k.succ c (d.getD b 0)
        k.castSucc_lt_succ.ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    · rw [h, tv_of_ne k.castSucc_lt_succ.ne.symm]
      intro b hb
      rw [hmbSP_glLin_toGL]
      refine hmbSP_transvection_stabV k.succ k.castSucc c (d.getD b 0)
        k.castSucc_lt_succ.ne.symm ?_
      rintro ⟨h1, h2⟩
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      exact hk b hb (by omega)
  exact hle

theorem hmbSP_diag_stabV {n : ℕ} {g : GL (Fin n) Fld}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) Fld) i j = 0) (c : ℕ) :
    (Vsub n c).map (glLin g).toLinearMap = Vsub n c := by
  have hbt : (g : Matrix (Fin n) (Fin n) Fld).BlockTriangular id := by
    intro i j hij
    exact hg i j (ne_of_gt hij)
  have h := congrArg (fun x : FlagK Fld n => x.E c) (flagAct_stdFlag g hbt)
  rw [flagAct, flagMap_E] at h
  exact h

end StabV

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
