module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3Geom14
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoMatrices
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3Geom
public import CFSG.Quasithin.Vol2.KGNatSL3Line

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Quasithin.Vol2.KGNat
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
open CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped Matrix Pointwise

variable {K : Type} [Field K] [CharP K 2]

private def swap23 : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by
    have h : (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).det = -1 := by
      rw [Matrix.det_fin_three]
      simp [Matrix.of_apply]
    rw [h, CharTwo.neg_eq]⟩

private def lowerSL (t : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, t, 1], by
    rw [Matrix.det_fin_three]
    simp [Matrix.of_apply]⟩

private theorem swap23_mulVec (x : Fin 3 → K) :
    ((swap23 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![x 0, x 2, x 1] := by
  change (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) *ᵥ x = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

private theorem lowerSL_mulVec (t : K) (x : Fin 3 → K) :
    ((lowerSL t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![x 0, x 1, x 2 + t * x 1] := by
  change (!![1, 0, 0; 0, 1, 0; 0, t, 1] : Matrix (Fin 3) (Fin 3) K) *ᵥ x = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

private theorem swap23_mulVec_e0 :
    ((swap23 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![1, 0, 0] = ![1, 0, 0] := by
  rw [swap23_mulVec]
  exact vec3_eq (by simp) (by simp) (by simp)

private theorem swap23_mulVec_e1 :
    ((swap23 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![0, 1, 0] = ![0, 0, 1] := by
  rw [swap23_mulVec]
  exact vec3_eq (by simp) (by simp) (by simp)

private theorem lowerSL_mulVec_e1 (t : K) :
    ((lowerSL t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![0, 1, 0] = ![0, 1, t] := by
  rw [lowerSL_mulVec]
  exact vec3_eq (by simp) (by simp) (by simp)

private theorem unitriangular_le_Usl : unitriangular 3 K ≤ Usl K := by
  rintro B ⟨hlt, hd⟩
  refine ⟨(B : Matrix (Fin 3) (Fin 3) K) 0 1, (B : Matrix (Fin 3) (Fin 3) K) 0 2,
    (B : Matrix (Fin 3) (Fin 3) K) 1 2, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  have h10 := hlt 1 0 (by decide)
  have h20 := hlt 2 0 (by decide)
  have h21 := hlt 2 1 (by decide)
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  fin_cases i <;> fin_cases j <;> simp_all [coe_uSL, uMat]

section Stabilizer

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}

@[expose] noncomputable def setStab (H : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup ↥H :=
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  MulAction.stabilizer ↥H (U : Set W)

private theorem smul_set_eq_iff_mem_stabW {U : Subgroup W} (x : ↥H) :
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    x • (U : Set W) = (U : Set W) ↔ (x : MulAut W) ∈ Ch11.SecA.stabW U := by
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  rw [Ch11.SecA.mem_stabW]
  constructor
  · intro h u
    constructor
    · intro hu
      exact Eq.mp (congrArg (fun S : Set W => (x : MulAut W) u ∈ S) h)
        (Set.mem_smul_set.mpr ⟨u, hu, rfl⟩)
    · intro hu
      obtain ⟨v, hv, hvx⟩ := Set.mem_smul_set.mp
        (Eq.mp (congrArg (fun S : Set W => (x : MulAut W) u ∈ S) h.symm) hu)
      have h1 : ((x : MulAut W)⁻¹) (x • v) = u := by
        rw [hvx]
        exact MulAut.inv_apply_self W (x : MulAut W) u
      have h2 : ((x : MulAut W)⁻¹) (x • v) = v := by
        show ((x : MulAut W)⁻¹) ((x : MulAut W) v) = v
        exact MulAut.inv_apply_self W (x : MulAut W) v
      rw [← h1, h2]
      exact hv
  · intro h
    ext u
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (h v).mp hv
    · intro hu
      exact ⟨((x : MulAut W)⁻¹) u, (h _).mpr (by simpa using hu),
        MulAut.apply_inv_self W (x : MulAut W) u⟩

theorem setStab_eq (H : Subgroup (MulAut W)) (U : Subgroup W) :
    setStab H U = (H ⊓ Ch11.SecA.stabW U).subgroupOf H := by
  unfold setStab
  ext x
  rw [MulAction.mem_stabilizer_iff, smul_set_eq_iff_mem_stabW x, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

end Stabilizer





section Conjugate

variable [Finite K]
variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}

private theorem mem_stabW_pre_iff
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (S : Submodule K (Fin 3 → K))
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((rho3 ρ A : ↥H) : MulAut W) ∈
        Ch11.SecA.stabW (hf.pre (gmap g S).toAddSubgroup) ↔
      ∀ y : Fin 3 → K, y ∈ gmap g S ↔
        (A : Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ gmap g S := by
  rw [IsCoord.rho3_mem_stabW_iff hf (hf.le_pre _) A, hf.img_pre]
  rfl

end Conjugate

section Coordinates

variable [Finite K] {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
  {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}

@[expose] noncomputable def preLine
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) : Subgroup W :=
  hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup

private noncomputable def prePlane
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) : Subgroup W :=
  hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup

private noncomputable def sigma (ρ : ↥(StatedSL 3 K) →* ↥H)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix.SpecialLinearGroup (Fin 3) K →* ↥H :=
  (rho3 ρ).comp (MulAut.conj g).toMonoidHom

private theorem sigma_apply (ρ : ↥(StatedSL 3 K) →* ↥H)
    (g A : Matrix.SpecialLinearGroup (Fin 3) K) :
    sigma ρ g A = rho3 ρ (g * A * g⁻¹) := by
  simp [sigma, MulAut.conj_apply]

theorem fixedPointSubgroup_eq_preLine
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {S : Subgroup ↥H} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ S.map H.subtype ↔
      ∃ u ∈ Usl K, x = ((rho3 ρ (g * u * g⁻¹) : ↥H) : MulAut W)) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp S.subtype)
    fixedPointSubgroup ↥S W = preLine hf g := by
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp S.subtype)
  ext w
  change (w ∈ FixedPoints.subgroup ↥S W) ↔ w ∈ preLine hf g
  rw [FixedPoints.mem_subgroup]
  have hiff : (∀ s : ↥S, s • w = w) ↔
      ∀ x ∈ S.map H.subtype, x w * w⁻¹ ∈ (⊥ : Subgroup W) := by
    constructor
    · rintro h x ⟨s, hs, rfl⟩
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      exact h ⟨s, hs⟩
    · intro h s
      have h1 := h _ (Subgroup.mem_map_of_mem H.subtype s.2)
      rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
  refine hiff.trans ?_
  rw [fixedW_iff hf hg w]
  change f w ∈ gmap g (stdLine K) ↔ f w ∈ gmap g (flagSpace 3 K 1)
  rw [stdLine_eq_flagSpace]

private theorem map_stabilizer_eq_setStab
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (d : ℕ) :
    (stabilizer (flagSpace 3 K d)).map (sigma ρ g) =
      setStab H (hf.pre (gmap g (flagSpace 3 K d)).toAddSubgroup) := by
  rw [setStab_eq]
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨(rho3 ρ (g * A * g⁻¹)).2, ?_⟩
    rw [sigma_apply]
    rw [mem_stabW_pre_iff hf g (flagSpace 3 K d) (g * A * g⁻¹)]
    intro y
    rw [mem_gmap, mem_gmap, conj_mulVec]
    simpa only [Matrix.SpecialLinearGroup.coe_inv] using
      mem_iff_of_mem_stabilizer hA ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) *ᵥ y)
  · rintro ⟨-, hx⟩
    obtain ⟨A, hA⟩ := (rho3_bijective hf).2 x
    rw [← hA] at hx
    have hxs := (mem_stabW_pre_iff hf g (flagSpace 3 K d) A).mp hx
    have hB : g⁻¹ * A * g ∈ stabilizer (flagSpace 3 K d) := by
      refine mem_stabilizer_of_iff fun y => ?_
      have h1 := hxs ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y)
      rw [mem_gmap, mem_gmap, ginv_g_mulVec, mulVec_gconj] at h1
      exact h1
    refine ⟨g⁻¹ * A * g, hB, ?_⟩
    rw [sigma_apply, show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]

private theorem map_unitriangular_le
    {S : Subgroup ↥H} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ S.map H.subtype ↔
      ∃ u ∈ Usl K, x = ((rho3 ρ (g * u * g⁻¹) : ↥H) : MulAut W)) :
    (unitriangular 3 K).map (sigma ρ g) ≤ S := by
  rintro _ ⟨u, hu, rfl⟩
  rw [← Subgroup.mem_map_iff_mem H.subtype_injective]
  refine (hg _).mpr ⟨u, unitriangular_le_Usl hu, ?_⟩
  simp [sigma_apply]

private theorem coatom_eq_setStab {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K)
    {C : Subgroup ↥H} (hUC : (unitriangular 3 K).map (sigma ρ g) ≤ C) (hC : IsCoatom C) :
    C = setStab H (preLine hf g) ∨ C = setStab H (prePlane hf g) := by
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hinj : Function.Injective (sigma ρ g) := by
    simpa [sigma] using (rho3_bijective hf).1.comp (MulAut.conj g).injective
  have hsurj : Function.Surjective (sigma ρ g) := by
    simpa [sigma] using (rho3_bijective hf).2.comp (MulAut.conj g).surjective
  have hker : (sigma ρ g).ker ≤ scalars 3 K := by
    rw [(MonoidHom.ker_eq_bot_iff (sigma ρ g)).mpr hinj]
    exact bot_le
  obtain ⟨-, -, hmax, -, -, -⟩ :=
    linear_three_residual_of_cover ⟨n, hK⟩ (sigma ρ g) hsurj hker
  obtain ⟨j, hj⟩ := (hmax C hUC).mp (covBy_top_iff.mpr hC)
  have key : C = setStab H
      (hf.pre (gmap g (flagSpace 3 K ((j : ℕ) + 1))).toAddSubgroup) :=
    hj.trans (map_stabilizer_eq_setStab hf g ((j : ℕ) + 1))
  fin_cases j
  · exact Or.inl (by simpa [preLine] using key)
  · exact Or.inr (by simpa [prePlane] using key)

private theorem eq_setStab_plane {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K)
    {P' : Subgroup ↥H} (hUP : (unitriangular 3 K).map (sigma ρ g) ≤ P')
    (hco : IsCoatom P') (hne : P' ≠ setStab H (preLine hf g)) :
    P' = setStab H (prePlane hf g) :=
  (coatom_eq_setStab hK hf g hUP hco).resolve_left hne

private theorem apply_mem_of_mem_setStab {U : Subgroup W} {p : ↥H}
    (hp : p ∈ setStab H U) {w : W} (hw : w ∈ U) : (p : MulAut W) w ∈ U := by
  rw [setStab_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hp
  exact (Ch11.SecA.mem_stabW.mp hp.2 w).mp hw

private theorem preLine_le_prePlane
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) : preLine hf g ≤ prePlane hf g := by
  intro w hw
  exact Submodule.map_mono (flagSpace_mono (by norm_num : 1 ≤ 2)) hw

private theorem rho3_blockSL_mem_setStab
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    rho3 ρ (g * blockSL A * g⁻¹) ∈ setStab H (prePlane hf g) := by
  rw [setStab_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  refine ⟨(rho3 ρ (g * blockSL A * g⁻¹)).2, ?_⟩
  have hx := perfectCore_le _ ((mem_perfectCore_HU2_iff hSL hf g _).mpr
    ⟨blockSL A, blockSL_mem A, rfl⟩)
  exact (Subgroup.mem_inf.mp hx).2

private theorem exists_blockSL_apply_eq
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {w : W} (hw : w ∈ prePlane hf g) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, ∃ w₀ ∈ preLine hf g,
      ((rho3 ρ (g * blockSL A * g⁻¹) : ↥H) : MulAut W) w₀ = w := by
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  let y : Fin 3 → K :=
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w
  have hy2 : y 2 = 0 := (mem_pre_plane_iff hf g w).mp hw
  have hy : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ y = f w := g_ginv_mulVec g (f w)
  by_cases hv : (![y 0, y 1] : Fin 2 → K) = 0
  · have hy0 : y = 0 := by
      have h0 := congrFun hv 0
      have h1 := congrFun hv 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
      exact vec3_eq (by simpa using h0) (by simpa using h1) (by simpa using hy2)
    have hw1 : w = 1 := by
      have hf0 : f w = 0 := by rw [← hy, hy0, Matrix.mulVec_zero]
      exact Subgroup.mem_bot.mp ((hf.ker w).mp hf0)
    refine ⟨1, 1, (preLine hf g).one_mem, ?_⟩
    rw [hw1]
    simp
  · obtain ⟨A, hA⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq hv
    obtain ⟨w₀, hw₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
    have hw₀U : w₀ ∈ preLine hf g :=
      (mem_pre_line_iff hf g w₀).mpr ⟨1, by rw [hw₀, one_smul]⟩
    have hA0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = y 0 := by
      have := congrFun hA 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have hA1 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = y 1 := by
      have := congrFun hA 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    have hblock : (![((A : Matrix (Fin 2) (Fin 2) K)) 0 0 * ![1, 0, 0] 0 +
        ((A : Matrix (Fin 2) (Fin 2) K)) 0 1 * ![1, 0, 0] 1,
        ((A : Matrix (Fin 2) (Fin 2) K)) 1 0 * ![1, 0, 0] 0 +
          ((A : Matrix (Fin 2) (Fin 2) K)) 1 1 * ![1, 0, 0] 1,
        (![1, 0, 0] : Fin 3 → K) 2] : Fin 3 → K) = ![y 0, y 1, 0] := by
      refine vec3_eq ?_ ?_ ?_ <;> simp [hA0, hA1]
    refine ⟨A, w₀, hw₀U, hinj _ _ ?_⟩
    rw [hf.act3, gconj_mulVec, hw₀, ginv_g_mulVec, blockSL_mulVec, hblock]
    conv_rhs => rw [← hy]
    congr 1
    exact vec3_eq rfl rfl hy2.symm

private theorem closure_iUnion_smul_eq
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    Subgroup.closure (⋃ p ∈ setStab H (prePlane hf g),
      p • ((preLine hf g : Subgroup W) : Set W)) = prePlane hf g := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).2 ?_
    intro w hw
    rw [Set.mem_iUnion] at hw
    obtain ⟨p, hw⟩ := hw
    rw [Set.mem_iUnion] at hw
    obtain ⟨hp, hw⟩ := hw
    rw [Set.mem_smul_set] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    exact apply_mem_of_mem_setStab hp (preLine_le_prePlane hf g hw₀)
  · intro w hw
    obtain ⟨A, w₀, hw₀, rfl⟩ := exists_blockSL_apply_eq hf g hw
    refine Subgroup.subset_closure ?_
    rw [Set.mem_iUnion]
    refine ⟨_, Set.mem_iUnion.mpr ⟨rho3_blockSL_mem_setStab hSL hf g A, ?_⟩⟩
    rw [Set.mem_smul_set]
    exact ⟨w₀, hw₀, rfl⟩

private theorem neg_add_uMat_mulVec_mem_stdLine (a b c : K) {y : Fin 3 → K} (hy : y 2 = 0) :
    -y + uMat a b c *ᵥ y ∈ stdLine K := by
  rw [mem_stdLine, uMat_mulVec]
  constructor <;> simp [hy]

private theorem inv_mul_apply_mem_preLine
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {S : Subgroup ↥H} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ S.map H.subtype ↔
      ∃ u ∈ Usl K, x = ((rho3 ρ (g * u * g⁻¹) : ↥H) : MulAut W))
    {s : ↥H} (hs : s ∈ S) {w : W} (hw : w ∈ prePlane hf g) :
    w⁻¹ * (s : MulAut W) w ∈ preLine hf g := by
  obtain ⟨u, hu, hsu⟩ := (hg (s : MulAut W)).mp (Subgroup.mem_map_of_mem H.subtype hs)
  obtain ⟨a, b, c, rfl⟩ := mem_Usl.mp hu
  have h2 : (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ f w) 2 = 0 := (mem_pre_plane_iff hf g w).mp hw
  change f (w⁻¹ * (s : MulAut W) w) ∈ gmap g (flagSpace 3 K 1)
  rw [← stdLine_eq_flagSpace, mem_gmap, hf.map_mul, hf.map_inv, hsu, hf.act3,
    Matrix.mulVec_add, Matrix.mulVec_neg, gconj_mulVec, ginv_g_mulVec, coe_uSL]
  exact neg_add_uMat_mulVec_mem_stdLine a b c h2

private theorem line_conclusion
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {S : Subgroup ↥H} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ S.map H.subtype ↔
      ∃ u ∈ Usl K, x = ((rho3 ρ (g * u * g⁻¹) : ↥H) : MulAut W))
    {ℓ : Subgroup W} {P' : Subgroup ↥H}
    (hℓ : ℓ = preLine hf g) (hP' : P' = setStab H (prePlane hf g)) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    let π : Subgroup W := Subgroup.closure (⋃ p ∈ P', p • (ℓ : Set W))
    (∀ w ∈ π, ∃ p ∈ P', w ∈ p • (ℓ : Set W)) ∧
      ∀ s ∈ S, ∀ w ∈ π, w⁻¹ * (s • w) ∈ ℓ := by
  subst hℓ hP'
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro π
  have hπ : π = prePlane hf g := closure_iUnion_smul_eq hSL hf g
  constructor
  · intro w hw
    rw [hπ] at hw
    obtain ⟨A, w₀, hw₀, rfl⟩ := exists_blockSL_apply_eq hf g hw
    exact ⟨_, rho3_blockSL_mem_setStab hSL hf g A,
      Set.mem_smul_set.mpr ⟨w₀, hw₀, rfl⟩⟩
  · intro s hs w hw
    rw [hπ] at hw
    exact inv_mul_apply_mem_preLine hf hg hs hw

theorem mem_Hinf_subgroupOf_iff {G : Type} [Group G] [Finite G] {H A : Subgroup G}
    (hAH : A ≤ H) (k : ↥H) :
    k ∈ Hinf (A.subgroupOf H) ↔ (k : G) ∈ CFSG.Quasithin.perfectCore A := by
  have hcore : Hinf (A.subgroupOf H) = CFSG.Quasithin.perfectCore (A.subgroupOf H) := by
    unfold Hinf CFSG.inSubgroup
    rw [perfectCore_eq_map_perfectResidual]
  rw [hcore, ← Subgroup.mem_map_iff_mem H.subtype_injective,
    ← perfectCore_map H.subtype H.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hAH]
  rfl

private theorem rho3_mem_Hinf_setStab_line
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {B : Matrix.SpecialLinearGroup (Fin 3) K}
    (hB : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0]) :
    rho3 ρ (g * B * g⁻¹) ∈ Hinf (setStab H (preLine hf g)) := by
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  rw [setStab_eq, mem_Hinf_subgroupOf_iff inf_le_left]
  exact (mem_perfectCore_HU1_iff hSL hf g _).mpr ⟨B, hB, rfl⟩

private theorem eq_top_of_coords
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {C : Subgroup W}
    (h0 : ∀ t : K, ∃ c ∈ C, f c = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![t, 0, 0])
    (h1 : ∀ t : K, ∃ c ∈ C, f c = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, t, 0])
    (h2 : ∀ t : K, ∃ c ∈ C, f c = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, t]) :
    C = ⊤ := by
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  refine eq_top_iff.2 fun w _ => ?_
  let y : Fin 3 → K :=
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w
  obtain ⟨c0, hc0, hc0f⟩ := h0 (y 0)
  obtain ⟨c1, hc1, hc1f⟩ := h1 (y 1)
  obtain ⟨c2, hc2, hc2f⟩ := h2 (y 2)
  have hvec : (![y 0, 0, 0] + ![0, y 1, 0] + ![0, 0, y 2] : Fin 3 → K) = y :=
    vec3_eq (by simp) (by simp) (by simp)
  have hy : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ y = f w := g_ginv_mulVec g (f w)
  have hw : w = c0 * c1 * c2 := by
    refine hinj _ _ ?_
    rw [hf.map_mul, hf.map_mul, hc0f, hc1f, hc2f, ← Matrix.mulVec_add, ← Matrix.mulVec_add,
      hvec, hy]
  rw [hw]
  exact C.mul_mem (C.mul_mem hc0 hc1) hc2

private theorem exists_coord_comm
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g B : Matrix.SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K) :
    ∃ w : W, f (w⁻¹ * ((rho3 ρ (g * B * g⁻¹) : ↥H) : MulAut W) w) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (-x + (B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) := by
  obtain ⟨w, hw⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
  refine ⟨w, ?_⟩
  rw [hf.map_mul, hf.map_inv, hf.act3, gconj_mulVec, hw, ginv_g_mulVec, ← Matrix.mulVec_neg,
    ← Matrix.mulVec_add]

private theorem comm_closure_eq_top
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {Ks : Subgroup ↥H}
    (hKs : ∀ B : Matrix.SpecialLinearGroup (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        rho3 ρ (g * B * g⁻¹) ∈ Ks) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    Subgroup.closure {w : W | ∃ k ∈ Ks, ∃ x : W, w = x⁻¹ * (k • x)} = ⊤ := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  refine eq_top_of_coords hf g (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · obtain ⟨w, hw⟩ := exists_coord_comm hf g (uSL t 0 0) ![0, 1, 0]
    have hk : rho3 ρ (g * uSL t 0 0 * g⁻¹) ∈ Ks :=
      hKs _ (by rw [coe_uSL, uMat_mulVec_e0])
    refine ⟨w⁻¹ * (((rho3 ρ (g * uSL t 0 0 * g⁻¹) : ↥H) : MulAut W) w), ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨_, hk, w, rfl⟩
    · rw [hw]
      congr 1
      rw [coe_uSL, uMat_mulVec]
      exact vec3_eq (by simp) (by simp) (by simp)
  · obtain ⟨w, hw⟩ := exists_coord_comm hf g (uSL 0 0 t) ![0, 0, 1]
    have hk : rho3 ρ (g * uSL 0 0 t * g⁻¹) ∈ Ks :=
      hKs _ (by rw [coe_uSL, uMat_mulVec_e0])
    refine ⟨w⁻¹ * (((rho3 ρ (g * uSL 0 0 t * g⁻¹) : ↥H) : MulAut W) w), ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨_, hk, w, rfl⟩
    · rw [hw]
      congr 1
      rw [coe_uSL, uMat_mulVec]
      exact vec3_eq (by simp) (by simp) (by simp)
  · obtain ⟨w, hw⟩ := exists_coord_comm hf g (lowerSL t) ![0, 1, 0]
    have hk : rho3 ρ (g * lowerSL t * g⁻¹) ∈ Ks :=
      hKs _ (by rw [lowerSL_mulVec]; exact vec3_eq (by simp) (by simp) (by simp))
    refine ⟨w⁻¹ * (((rho3 ρ (g * lowerSL t * g⁻¹) : ↥H) : MulAut W) w), ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨_, hk, w, rfl⟩
    · rw [hw]
      congr 1
      rw [lowerSL_mulVec]
      exact vec3_eq (by simp) (by simp) (by simp)

private theorem mem_prePlane_of_mulVec_eq
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {x : Fin 3 → K} (hx : x 2 = 0) {w : W}
    (hw : f w = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) : w ∈ prePlane hf g := by
  rw [prePlane, mem_pre_plane_iff hf g w, hw, ginv_g_mulVec]
  exact hx

private theorem exists_mem_prePlane_of_mulVec_eq
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {x : Fin 3 → K} (hx : x 2 = 0) :
    ∃ w : W, f w = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∧ w ∈ prePlane hf g := by
  obtain ⟨w, hw⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
  exact ⟨w, hw, mem_prePlane_of_mulVec_eq hf g hx hw⟩

private theorem span_conclusion
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) {Ks P' : Subgroup ↥H} {ℓ : Subgroup W}
    (hℓ : ℓ = preLine hf g) (hP' : P' = setStab H (prePlane hf g))
    (hKs : ∀ B : Matrix.SpecialLinearGroup (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        rho3 ρ (g * B * g⁻¹) ∈ Ks) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    Subgroup.closure (⋃ k ∈ Ks,
      k • ((Subgroup.closure (⋃ p ∈ P', p • (ℓ : Set W)) : Subgroup W) : Set W)) = ⊤ := by
  subst hℓ hP'
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  rw [closure_iUnion_smul_eq hSL hf g]
  refine eq_top_of_coords hf g (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · obtain ⟨w, hw, hwU⟩ := exists_mem_prePlane_of_mulVec_eq hf g (x := ![t, 0, 0]) (by simp)
    refine ⟨w, ?_, hw⟩
    refine Subgroup.subset_closure ?_
    rw [Set.mem_iUnion]
    refine ⟨1, Set.mem_iUnion.mpr ⟨Ks.one_mem, ?_⟩⟩
    rw [Set.mem_smul_set]
    exact ⟨w, hwU, one_smul _ w⟩
  · obtain ⟨w, hw, hwU⟩ := exists_mem_prePlane_of_mulVec_eq hf g (x := ![0, t, 0]) (by simp)
    refine ⟨w, ?_, hw⟩
    refine Subgroup.subset_closure ?_
    rw [Set.mem_iUnion]
    refine ⟨1, Set.mem_iUnion.mpr ⟨Ks.one_mem, ?_⟩⟩
    rw [Set.mem_smul_set]
    exact ⟨w, hwU, one_smul _ w⟩
  · obtain ⟨w, hw, hwU⟩ := exists_mem_prePlane_of_mulVec_eq hf g (x := ![0, t, 0]) (by simp)
    refine ⟨((rho3 ρ (g * swap23 * g⁻¹) : ↥H) : MulAut W) w, ?_, ?_⟩
    · refine Subgroup.subset_closure ?_
      rw [Set.mem_iUnion]
      refine ⟨rho3 ρ (g * swap23 * g⁻¹),
        Set.mem_iUnion.mpr ⟨hKs _ swap23_mulVec_e0, ?_⟩⟩
      rw [Set.mem_smul_set]
      exact ⟨w, hwU, rfl⟩
    · rw [hf.act3, gconj_mulVec, hw, ginv_g_mulVec, swap23_mulVec] <;>
        exact congrArg (fun v => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
          (vec3_eq (by simp) (by simp) (by simp))

end Coordinates

theorem kSL3Line_holds : KSL3Line := by
  intro W _ _ H n _ hnat hn S ℓ Pℓ P' hNP' hco hne
  obtain ⟨K, hfield, hfinite, hK, ρ, hρ⟩ := hnat
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : CharP K 2 := charP_two_of_card (by omega) hK
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
    commutator_SL2_eq_top (four_le_card (by omega) hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 3 K)) hρ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
    (CFSG.Quasithin.A4.isSylowTwoOf_map H S)
  have hℓ : ℓ = preLine hf g := fixedPointSubgroup_eq_preLine hf hg
  have hPℓ : Pℓ = setStab H (preLine hf g) := by rw [← hℓ]; rfl
  have hP' : P' = setStab H (prePlane hf g) :=
    eq_setStab_plane hK hf g
      ((map_unitriangular_le hg).trans (Subgroup.le_normalizer.trans hNP')) hco
      (fun h => hne (h.trans hPℓ.symm))
  exact line_conclusion hSL hf hg hℓ hP'

theorem kSL3Span_holds : KSL3Span := by
  intro W _ _ H n _ hnat hn S ℓ Pℓ Kstar
  obtain ⟨K, hfield, hfinite, hK, ρ, hρ⟩ := hnat
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : CharP K 2 := charP_two_of_card (by omega) hK
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
    commutator_SL2_eq_top (four_le_card (by omega) hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 3 K)) hρ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
    (CFSG.Quasithin.A4.isSylowTwoOf_map H S)
  have hℓ : ℓ = preLine hf g := fixedPointSubgroup_eq_preLine hf hg
  have hPℓ : Pℓ = setStab H (preLine hf g) := by rw [← hℓ]; rfl
  have hKs : ∀ B : Matrix.SpecialLinearGroup (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
        rho3 ρ (g * B * g⁻¹) ∈ Kstar := by
    intro B hB
    show rho3 ρ (g * B * g⁻¹) ∈ Hinf Pℓ
    rw [hPℓ]
    exact rho3_mem_Hinf_setStab_line hSL hf g hB
  refine ⟨comm_closure_eq_top hSL hf g hKs, fun P' hNP' hco hne => ?_⟩
  exact span_conclusion hSL hf g hℓ
    (eq_setStab_plane hK hf g
      ((map_unitriangular_le hg).trans (Subgroup.le_normalizer.trans hNP')) hco
      (fun h => hne (h.trans hPℓ.symm))) hKs

section Geom14

variable [Finite K] {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
  {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}

private theorem overgroup_sylow_le {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {S : Subgroup ↥H} {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ S.map H.subtype ↔
      ∃ u ∈ Usl K, x = ((rho3 ρ (g * u * g⁻¹) : ↥H) : MulAut W))
    {Y : Subgroup ↥H} (hSY : S ≤ Y) (hY : Y ≠ ⊤) :
    Y ≤ setStab H (preLine hf g) ∨ Y ≤ setStab H (prePlane hf g) := by
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨C, hC, hYC⟩ := (IsCoatomic.eq_top_or_exists_le_coatom Y).resolve_left hY
  rcases coatom_eq_setStab hK hf g
    ((map_unitriangular_le hg).trans (hSY.trans hYC)) hC with h | h
  · exact Or.inl (h ▸ hYC)
  · exact Or.inr (h ▸ hYC)

private theorem sq_eq_one_of_fix_e0_e1 {B : Matrix.SpecialLinearGroup (Fin 3) K}
    (h0 : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0])
    (h1 : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] = ![0, 1, 0]) :
    B ^ 2 = 1 := by
  have h00 : (B : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    have := congrFun h0 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h10 : (B : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := congrFun h0 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h20 : (B : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := congrFun h0 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h01 : (B : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    have := congrFun h1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h11 : (B : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    have := congrFun h1 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h21 : (B : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have := congrFun h1 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h22 : (B : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have hdet : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := B.2
    rw [Matrix.det_fin_three] at hdet
    simpa [h00, h01, h10, h11, h20, h21] using hdet
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h01, h10, h11, h20, h21, h22,
      CharTwo.add_self_eq_zero]

private theorem sq_eq_one_of_fix_line
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (h : ↥H)
    (hfix : ∀ w ∈ prePlane hf g, (h : MulAut W) w = w) : h ^ 2 = 1 := by
  obtain ⟨A, rfl⟩ := (rho3_bijective hf).2 h
  obtain ⟨w0, hw0⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  obtain ⟨w1, hw1⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0])
  have hw0U : w0 ∈ prePlane hf g :=
    mem_prePlane_of_mulVec_eq hf g (x := ![1, 0, 0]) (by simp) hw0
  have hw1U : w1 ∈ prePlane hf g :=
    mem_prePlane_of_mulVec_eq hf g (x := ![0, 1, 0]) (by simp) hw1
  have hA0 : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] := by
    have h := congrArg f (hfix w0 hw0U)
    rwa [hf.act3, hw0] at h
  have hA1 : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0]) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] := by
    have h := congrArg f (hfix w1 hw1U)
    rwa [hf.act3, hw1] at h
  let B : Matrix.SpecialLinearGroup (Fin 3) K := g⁻¹ * A * g
  have hB0 : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
    have h := congrArg (fun v => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) hA0
    rwa [mulVec_gconj, ginv_g_mulVec] at h
  have hB1 : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] = ![0, 1, 0] := by
    have h := congrArg (fun v => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) hA1
    rwa [mulVec_gconj, ginv_g_mulVec] at h
  have hB2 : B ^ 2 = 1 := sq_eq_one_of_fix_e0_e1 hB0 hB1
  have hconj : ((MulAut.conj g).toMonoidHom) B = A := by
    change (MulAut.conj g) B = A
    rw [MulAut.conj_apply]
    show g * (g⁻¹ * A * g) * g⁻¹ = A; group
  have hA2 : A ^ 2 = 1 := by
    have hmap := map_pow ((MulAut.conj g).toMonoidHom) B 2
    rw [hB2, map_one, hconj] at hmap
    exact hmap.symm
  rw [← map_pow, hA2, map_one]

private theorem map_rho3_pre
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g A : Matrix.SpecialLinearGroup (Fin 3) K) (S : Submodule K (Fin 3 → K)) :
    (hf.pre (gmap g S).toAddSubgroup).map
        ((rho3 ρ A : ↥H) : MulAut W).toMonoidHom =
      hf.pre (gmap (A * g) S).toAddSubgroup := by
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    change f (((rho3 ρ A : ↥H) : MulAut W) u) ∈ gmap (A * g) S
    rw [hf.act3, mem_gmap]
    have hu' : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f u ∈ S := mem_gmap.mp hu
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one]
    exact hu'
  · intro hw
    refine ⟨((rho3 ρ A⁻¹ : ↥H) : MulAut W) w, ?_, ?_⟩
    · change f (((rho3 ρ A⁻¹ : ↥H) : MulAut W) w) ∈ gmap g S
      rw [hf.act3, mem_gmap]
      have hw' : (((A * g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ f w ∈ S := mem_gmap.mp hw
      rwa [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec] at hw'
    · show ((rho3 ρ A : ↥H) : MulAut W) (((rho3 ρ A⁻¹ : ↥H) : MulAut W) w) = w
      rw [← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
      simp

private theorem crossProduct_ne_zero_of_ne
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {D₁ D₂ : Matrix.SpecialLinearGroup (Fin 3) K} (hne : preLine hf D₁ ≠ preLine hf D₂) :
    crossProduct ((D₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
      ((D₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) ≠ 0 := by
  intro h0
  set a : Fin 3 → K := (D₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] with ha
  set b : Fin 3 → K := (D₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] with hb
  have hni : ¬ LinearIndependent K ![a, b] := fun hli =>
    (crossProduct_ne_zero_iff_linearIndependent.mpr hli) h0
  have ha0 : a ≠ 0 := by
    intro hzero
    have h := congrArg (fun v => ((D₁⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) hzero
    rw [ha, ginv_g_mulVec, Matrix.mulVec_zero] at h
    have h1 : (1 : K) = 0 := by simpa using congrFun h 0
    exact one_ne_zero h1
  have hb0 : b ≠ 0 := by
    intro hzero
    have h := congrArg (fun v => ((D₂⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) hzero
    rw [hb, ginv_g_mulVec, Matrix.mulVec_zero] at h
    have h1 : (1 : K) = 0 := by simpa using congrFun h 0
    exact one_ne_zero h1
  rw [LinearIndependent.pair_iff' ha0] at hni
  push Not at hni
  obtain ⟨c, hc⟩ := hni
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hb0 hc.symm
  apply hne
  ext w
  rw [preLine, preLine, mem_pre_line_iff hf D₁ w, mem_pre_line_iff hf D₂ w]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t * c⁻¹, ?_⟩
    rw [ht, ← ha, ← hb, ← hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  · rintro ⟨t, ht⟩
    refine ⟨t * c, ?_⟩
    rw [ht, ← hb, ← ha, ← hc, smul_smul]

private theorem pre_line_sup_eq_pre_plane
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {D₁ D₂ C : Matrix.SpecialLinearGroup (Fin 3) K}
    (h₁ : (C : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] =
      (D₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
    (h₂ : (C : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] =
      (D₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) :
    preLine hf D₁ ⊔ preLine hf D₂ = prePlane hf C := by
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro w hw
    rw [preLine] at hw; rw [prePlane, mem_pre_plane_iff hf C w]
    obtain ⟨t, ht⟩ := (mem_pre_line_iff hf D₁ w).mp hw
    rw [ht, ← h₁, Matrix.mulVec_smul, ginv_g_mulVec]
    simp
  · intro w hw
    rw [preLine] at hw; rw [prePlane, mem_pre_plane_iff hf C w]
    obtain ⟨t, ht⟩ := (mem_pre_line_iff hf D₂ w).mp hw
    rw [ht, ← h₂, Matrix.mulVec_smul, ginv_g_mulVec]
    simp
  · intro w hw
    rw [prePlane, mem_pre_plane_iff hf C w] at hw
    let y : Fin 3 → K := ((C⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f w
    have hy2 : y 2 = 0 := hw
    have hy : (C : Matrix (Fin 3) (Fin 3) K) *ᵥ y = f w := g_ginv_mulVec C (f w)
    obtain ⟨w₁, hw₁⟩ := hf.surj (y 0 • ((D₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]))
    obtain ⟨w₂, hw₂⟩ := hf.surj (y 1 • ((D₂ : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]))
    have hw₁U : w₁ ∈ preLine hf D₁ := by
      rw [preLine]
      exact (mem_pre_line_iff hf D₁ w₁).mpr ⟨y 0, hw₁⟩
    have hw₂U : w₂ ∈ preLine hf D₂ := by
      rw [preLine]
      exact (mem_pre_line_iff hf D₂ w₂).mpr ⟨y 1, hw₂⟩
    have hsum : f (w₁ * w₂) = f w := by
      rw [hf.map_mul, hw₁, hw₂, ← h₁, ← h₂, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
        ← Matrix.mulVec_add, ← hy]
      congr 1
      exact vec3_eq (by simp) (by simp) (by simp [hy2])
    rw [show w = w₁ * w₂ from (hinj _ _ hsum).symm]
    exact Subgroup.mul_mem_sup hw₁U hw₂U

private theorem exists_sup_eq_map_plane
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (x₁ x₂ : ↥H)
    (hne : (preLine hf g).map (x₁ : MulAut W).toMonoidHom ≠
      (preLine hf g).map (x₂ : MulAut W).toMonoidHom) :
    ∃ y : ↥H, (preLine hf g).map (x₁ : MulAut W).toMonoidHom ⊔
        (preLine hf g).map (x₂ : MulAut W).toMonoidHom =
      (prePlane hf g).map (y : MulAut W).toMonoidHom := by
  obtain ⟨A₁, rfl⟩ := (rho3_bijective hf).2 x₁
  obtain ⟨A₂, rfl⟩ := (rho3_bijective hf).2 x₂
  simp only [preLine, prePlane] at hne ⊢
  rw [map_rho3_pre hf g A₁ (flagSpace 3 K 1),
    map_rho3_pre hf g A₂ (flagSpace 3 K 1)] at hne
  rw [map_rho3_pre hf g A₁ (flagSpace 3 K 1),
    map_rho3_pre hf g A₂ (flagSpace 3 K 1)]
  obtain ⟨C, hC₁, hC₂⟩ := UnitarySixFieldTwo.exists_SL_mulVec_pair
    (crossProduct_ne_zero_of_ne hf hne)
  have hs0 : (Pi.single 0 1 : Fin 3 → K) = ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp
  have hs1 : (Pi.single 1 1 : Fin 3 → K) = ![0, 1, 0] := by
    ext i
    fin_cases i <;> simp
  rw [hs0] at hC₁
  rw [hs1] at hC₂
  refine ⟨rho3 ρ (C * g⁻¹), ?_⟩
  rw [map_rho3_pre hf g (C * g⁻¹) (flagSpace 3 K 2),
    show (C * g⁻¹) * g = C by group]
  exact pre_line_sup_eq_pre_plane hf hC₁ hC₂

end Geom14

theorem kSL3Geom14_holds : KSL3Geom14 := by
  intro W _ _ H n _ hnat hn S ℓ Pℓ P' hNP' hco hne π
  obtain ⟨K, hfield, hfinite, hK, ρ, hρ⟩ := hnat
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : CharP K 2 := charP_two_of_card (by omega) hK
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
    commutator_SL2_eq_top (four_le_card (by omega) hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 3 K)) hρ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
    (CFSG.Quasithin.A4.isSylowTwoOf_map H S)
  have hℓ : ℓ = preLine hf g := fixedPointSubgroup_eq_preLine hf hg
  have hPℓ : Pℓ = setStab H (preLine hf g) := by rw [← hℓ]; rfl
  have hP' : P' = setStab H (prePlane hf g) :=
    eq_setStab_plane hK hf g
      ((map_unitriangular_le hg).trans (Subgroup.le_normalizer.trans hNP')) hco
      (fun h => hne (h.trans hPℓ.symm))
  have hπ : π = prePlane hf g := by
    show Subgroup.closure (⋃ p ∈ P', p • (ℓ : Set W)) = prePlane hf g
    rw [hℓ, hP']
    exact closure_iUnion_smul_eq hSL hf g
  refine ⟨fun Y hSY hY => ?_, fun h hfix => ?_, fun x₁ x₂ hx => ?_⟩
  · rw [hPℓ, hP']
    exact overgroup_sylow_le hK hf hg hSY hY
  · exact sq_eq_one_of_fix_line hf g h (fun w hw => hfix w (hπ ▸ hw))
  · rw [hπ, hℓ]
    rw [hℓ] at hx
    exact exists_sup_eq_map_plane hf g x₁ x₂ hx

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
