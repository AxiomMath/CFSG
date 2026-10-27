module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSL3Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3PointTorus
public import CFSG.Quasithin.Vol2.Ch11SecAKB1
public import CFSG.Quasithin.Background.C41PfV
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLevi
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Quasithin.Vol2.KGNat
open CFSG.Quasithin.Vol2.KGNat.PointStab
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped Matrix Pointwise

variable {K : Type} [Field K] [CharP K 2]

variable [Finite K]

theorem mem_hinf_stabilizer_iff {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) (z : ↥H) :
    z ∈ Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)) ↔
      (z : MulAut W) ∈ CFSG.Quasithin.perfectCore
        (H ⊓ Ch11.SecA.stabW (preLine hf h)) := by
  have hP : MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W) =
      (H ⊓ Ch11.SecA.stabW (preLine hf h)).subgroupOf H := by
    rw [← setStab_eq H (preLine hf h)]
    rfl
  rw [hP, mem_Hinf_subgroupOf_iff inf_le_left]

private theorem mem_pCore_hinf_iff {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) (z : ↥H) :
    z ∈ CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))) ↔
      (z : MulAut W) ∈ CFSG.Open.pCoreOf 2
        (CFSG.Quasithin.perfectCore (H ⊓ Ch11.SecA.stabW (preLine hf h))) := by
  set A : Subgroup (MulAut W) := H ⊓ Ch11.SecA.stabW (preLine hf h) with hA
  have hP : MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W) = A.subgroupOf H := by
    change setStab H (preLine hf h) = A.subgroupOf H
    rw [hA]
    exact setStab_eq H (preLine hf h)
  have hHinf : Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)) =
      CFSG.Quasithin.perfectCore (A.subgroupOf H) := by
    rw [hP]
    unfold Hinf CFSG.inSubgroup
    rw [perfectCore_eq_map_perfectResidual]
  have hmapK : (CFSG.Quasithin.perfectCore (A.subgroupOf H)).map H.subtype =
      CFSG.Quasithin.perfectCore A :=
    perfectCore_map_subgroupOf inf_le_left
  have hmap : (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore (A.subgroupOf H))).map
        H.subtype = CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore A) := by
    rw [← CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 H.subtype H.subtype_injective
      (CFSG.Quasithin.perfectCore (A.subgroupOf H)), hmapK]
  rw [hHinf, ← Subgroup.mem_map_iff_mem H.subtype_injective, hmap]
  rfl

private theorem exists_uSL_of_quot_trivial {B : Matrix.SpecialLinearGroup (Fin 3) K}
    (hBquot : ∀ v : Fin 3 → K, ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 = v 1 ∧
      ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = v 2) :
    ∃ a b : K, B = uSL a b 0 := by
  have hB10 : (B : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := (hBquot ![1, 0, 0]).1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hB20 : (B : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := (hBquot ![1, 0, 0]).2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hB11 : (B : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    have := (hBquot ![0, 1, 0]).1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hB21 : (B : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have := (hBquot ![0, 1, 0]).2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hB12 : (B : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    have := (hBquot ![0, 0, 1]).1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hB22 : (B : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have := (hBquot ![0, 0, 1]).2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hB00 : (B : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    have hdet : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := B.2
    rw [Matrix.det_fin_three] at hdet
    simpa [hB10, hB20, hB11, hB12, hB21, hB22] using hdet
  have hB0 : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hB00, hB10, hB20]
  have hBstab : B ∈ stabE0 K := mem_stabE0.mpr hB0
  have hlev : leviHom K ⟨B, hBstab⟩ = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [leviHom_coe]
    fin_cases i <;> fin_cases j <;> simp [lev, hB11, hB12, hB21, hB22]
  refine ⟨(B : Matrix (Fin 3) (Fin 3) K) 0 1, (B : Matrix (Fin 3) (Fin 3) K) 0 2, ?_⟩
  simpa using eq_uSL_of_mem_ker (B := ⟨B, hBstab⟩) hlev

private theorem exists_uSL_of_mem_pCore_hinf {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) {z : ↥H}
    (hz : z ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)))) :
    ∃ a b : K, z = rho3 ρ (h * uSL a b 0 * h⁻¹) := by
  have hz' : (z : MulAut W) ∈ CFSG.Open.pCoreOf 2
      (CFSG.Quasithin.perfectCore (H ⊓ Ch11.SecA.stabW (preLine hf h))) :=
    (mem_pCore_hinf_iff hf h z).mp hz
  obtain ⟨B, hBquot, hBz⟩ := levi_of_mem_pCoreOf_HU1 hSL hf h hz'
  obtain ⟨a, b, hBeq⟩ := exists_uSL_of_quot_trivial hBquot
  refine ⟨a, b, ?_⟩
  apply Subtype.ext
  conv_lhs => rw [hBz, hBeq]

private theorem mem_pCore_hinf_of_eq_uSL {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) (a b : K) :
    rho3 ρ (h * uSL a b 0 * h⁻¹) ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))) := by
  have hx : ((rho3 ρ (h * uSL a b 0 * h⁻¹) : ↥H) : MulAut W) ∈ CFSG.Open.pCoreOf 2
      (CFSG.Quasithin.perfectCore (H ⊓ Ch11.SecA.stabW (preLine hf h))) := by
    obtain ⟨y, hy, hyeq⟩ := radical_mem_pCore hSL hf h a b
    have hyU : (y : MulAut W) ∈ CFSG.Open.pCoreOf 2
        (CFSG.Quasithin.perfectCore (H ⊓ Ch11.SecA.stabW (preLine hf h))) :=
      Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rwa [hyeq] at hyU
  exact (mem_pCore_hinf_iff hf h _).mpr hx

theorem mem_pCore_hinf_iff_exists_uSL {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) (z : ↥H) :
    z ∈ CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))) ↔
      ∃ a b : K, z = rho3 ρ (h * uSL a b 0 * h⁻¹) :=
  ⟨fun hz => exists_uSL_of_mem_pCore_hinf hSL hf h hz, by
    rintro ⟨a, b, rfl⟩
    exact mem_pCore_hinf_of_eq_uSL hSL hf h a b⟩

theorem apply_eq_of_mem_pCore_hinf {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) {z : ↥H}
    (hz : z ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))))
    {w : W} (hw : w ∈ preLine hf h) : (z : MulAut W) w = w := by
  obtain ⟨a, b, rfl⟩ := (mem_pCore_hinf_iff_exists_uSL hSL hf h z).mp hz
  have hw' : w ∈ hf.pre (gmap h (flagSpace 3 K 1)).toAddSubgroup := by
    rwa [preLine] at hw
  obtain ⟨t, ht⟩ := (mem_pre_line_iff hf h w).mp hw'
  have hinj : ∀ x y : W, f x = f y → x = y := fun x y hxy =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff x y).mp hxy))
  refine hinj _ _ ?_
  rw [hf.act3, gconj_mulVec, ht, Matrix.mulVec_smul, ginv_g_mulVec, Matrix.mulVec_smul,
    coe_uSL, uMat_mulVec_e0, Matrix.mulVec_smul]

theorem mem_preLine_of_forall_pCore_fix {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) {w : W}
    (hw : ∀ z ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))),
      (z : MulAut W) w = w) : w ∈ preLine hf h := by
  set y : Fin 3 → K := ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ f w with hy
  have hz1 : rho3 ρ (h * uSL 1 0 0 * h⁻¹) ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))) :=
    mem_pCore_hinf_of_eq_uSL hSL hf h 1 0
  have hz2 : rho3 ρ (h * uSL 0 1 0 * h⁻¹) ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))) :=
    mem_pCore_hinf_of_eq_uSL hSL hf h 0 1
  have h1 : (((uSL (1 : K) 0 0 : Matrix.SpecialLinearGroup (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ y = y := by
    have h := congrArg (fun v => ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) (congrArg f (hw _ hz1))
    rw [hf.act3, gconj_mulVec, ginv_g_mulVec] at h
    exact h
  have h2 : (((uSL (0 : K) 1 0 : Matrix.SpecialLinearGroup (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ y = y := by
    have h := congrArg (fun v => ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) (congrArg f (hw _ hz2))
    rw [hf.act3, gconj_mulVec, ginv_g_mulVec] at h
    exact h
  rw [coe_uSL, uMat_mulVec] at h1
  rw [coe_uSL, uMat_mulVec] at h2
  have hy1 : y 1 = 0 := by
    have h := congrFun h1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have hy2 : y 2 = 0 := by
    have h := congrFun h2 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  rw [preLine]
  change f w ∈ gmap h (flagSpace 3 K 1)
  rw [← stdLine_eq_flagSpace, mem_gmap]
  change y ∈ stdLine K
  rw [mem_stdLine]
  exact ⟨hy1, hy2⟩

private theorem map_conj_eq_self_of_commutator {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {U : Subgroup ↥H} {g : ↥H}
    (hcomm : ∀ k ∈ U, g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 U) :
    U.map (MulAut.conj g).toMonoidHom = U := by
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro x ⟨k, hk, rfl⟩
    change (MulAut.conj g) k ∈ U
    rw [MulAut.conj_apply]
    have hUle : CFSG.Open.pCoreOf 2 U ≤ U := Subgroup.map_subtype_le _
    rw [show g * k * g⁻¹ = (g * k * g⁻¹ * k⁻¹) * k from by group]
    exact U.mul_mem (hUle (hcomm k hk)) hk
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem map_conj_pCore_eq_self {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {U : Subgroup ↥H} {g : ↥H}
    (hU : U.map (MulAut.conj g).toMonoidHom = U) :
    (CFSG.Open.pCoreOf 2 U).map (MulAut.conj g).toMonoidHom = CFSG.Open.pCoreOf 2 U := by
  rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) U, hU]

private theorem mem_pCore_conj_iff {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {U : Subgroup ↥H} {g : ↥H}
    (hU : (CFSG.Open.pCoreOf 2 U).map (MulAut.conj g).toMonoidHom =
      CFSG.Open.pCoreOf 2 U) (u : ↥H) :
    u ∈ CFSG.Open.pCoreOf 2 U ↔ g * u * g⁻¹ ∈ CFSG.Open.pCoreOf 2 U := by
  have h := (Subgroup.mem_map_iff_mem (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective (K := CFSG.Open.pCoreOf 2 U) (x := u))
  rw [hU] at h
  change (MulAut.conj g) u ∈ CFSG.Open.pCoreOf 2 U ↔ u ∈ CFSG.Open.pCoreOf 2 U at h
  rw [MulAut.conj_apply] at h
  exact h.symm

private theorem forall_smul_eq_iff_conj {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {P : Subgroup ↥H} {g : ↥H}
    (hP : ∀ u : ↥H, u ∈ P ↔ g * u * g⁻¹ ∈ P) {w : W} :
    (∀ u ∈ P, (u : MulAut W) w = w) ↔
      (∀ u ∈ P, (u : MulAut W) ((g : MulAut W) w) = (g : MulAut W) w) := by
  constructor
  · intro hw u hu
    have hgu : g⁻¹ * u * g ∈ P := by
      rw [hP (g⁻¹ * u * g)]
      rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u from by group]
    calc (u : MulAut W) ((g : MulAut W) w)
        = ((u * g : ↥H) : MulAut W) w := by
            rw [Subgroup.coe_mul, MulAut.mul_apply]
      _ = ((g * (g⁻¹ * u * g) : ↥H) : MulAut W) w := by
          rw [show u * g = g * (g⁻¹ * u * g) by group]
      _ = (g : MulAut W) (((g⁻¹ * u * g : ↥H) : MulAut W) w) := by
          rw [Subgroup.coe_mul, MulAut.mul_apply]
      _ = (g : MulAut W) w := by rw [hw _ hgu]
  · intro hw u hu
    have hgu : g * u * g⁻¹ ∈ P := (hP u).mp hu
    have h1 := hw _ hgu
    have h2 := congrArg (fun x => ((g : MulAut W)⁻¹) x) h1
    simpa [MulAut.mul_apply] using h2

private theorem mem_stabilizer_of_pCore_fix {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {P : Subgroup ↥H} {g : ↥H} {ℓ : Subgroup W}
    (hfix : ∀ w : W, w ∈ ℓ ↔ ∀ u ∈ P, (u : MulAut W) w = w)
    (hP : ∀ u : ↥H, u ∈ P ↔ g * u * g⁻¹ ∈ P) :
    g ∈ MulAction.stabilizer ↥H (ℓ : Set W) := by
  have hPinv : ∀ u : ↥H, u ∈ P ↔ g⁻¹ * u * g ∈ P := by
    intro u
    have h := hP (g⁻¹ * u * g)
    rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at h
    exact h.symm
  rw [MulAction.mem_stabilizer_iff]
  ext w
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ ℓ at hx
    change (g : MulAut W) x ∈ ℓ
    rw [hfix x] at hx
    rw [hfix ((g : MulAut W) x)]
    exact (forall_smul_eq_iff_conj hP).mp hx
  · intro hw
    have hw' : ∀ u ∈ P, (u : MulAut W) w = w := (hfix w).mp hw
    refine ⟨((g : MulAut W)⁻¹) w, ?_, ?_⟩
    · change ((g : MulAut W)⁻¹) w ∈ ℓ
      rw [hfix (((g : MulAut W)⁻¹) w)]
      exact (forall_smul_eq_iff_conj hPinv).mp hw'
    · exact MulAut.apply_inv_self W (g : MulAut W) w

theorem exists_smul_e0_of_mem_stabW {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h M : Matrix.SpecialLinearGroup (Fin 3) K) {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : D = h⁻¹ * M * h)
    (hg : ((rho3 ρ M : ↥H) : MulAut W) ∈ Ch11.SecA.stabW (preLine hf h)) :
    ∃ μ : K, μ ≠ 0 ∧ (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0] := by
  have hD' : h * D * h⁻¹ = M := by rw [hD]; group
  have hg' : ((rho3 ρ (h * D * h⁻¹) : ↥H) : MulAut W) ∈
      Ch11.SecA.stabW (preLine hf h) := by rw [hD']; exact hg
  have hstab := (hf.rho3_mem_stabW_iff (hf.le_pre _) (h * D * h⁻¹)).mp hg'
  have h1 := hstab ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  rw [hf.img_pre, ← stdLine_eq_flagSpace] at h1
  simp only [Submodule.mem_toAddSubgroup, mem_gmap, ginv_g_mulVec, gconj_mulVec] at h1
  have hDmem : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] ∈ stdLine K :=
    h1.mp (mem_stdLine.mpr ⟨by simp, by simp⟩)
  refine ⟨((D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) 0, ?_, ?_⟩
  · intro h0
    have hzero : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = 0 := by
      rw [mem_stdLine] at hDmem
      exact vec3_eq (by simpa using h0) (by simpa using hDmem.1) (by simpa using hDmem.2)
    have h2 := congrArg (fun v => ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) hzero
    rw [ginv_g_mulVec, Matrix.mulVec_zero] at h2
    have h10 : (1 : K) = 0 := by simpa using congrFun h2 0
    exact one_ne_zero h10
  · rw [mem_stdLine] at hDmem
    exact vec3_eq (by simp) (by simpa using hDmem.1) (by simpa using hDmem.2)

private theorem exists_quot_trivial_of_commutator {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h M : Matrix.SpecialLinearGroup (Fin 3) K)
    (hcomm : ∀ k ∈ Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)),
      rho3 ρ M * k * (rho3 ρ M)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))))
    {B : Matrix.SpecialLinearGroup (Fin 3) K} (hB : B ∈ stabE0 K) :
    ∃ C : Matrix.SpecialLinearGroup (Fin 3) K,
      (∀ v : Fin 3 → K, ((C : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 = v 1 ∧
        ((C : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = v 2) ∧
      (h⁻¹ * M * h) * B * (h⁻¹ * M * h)⁻¹ * B⁻¹ = C := by
  let D : Matrix.SpecialLinearGroup (Fin 3) K := h⁻¹ * M * h
  let kB : ↥H := rho3 ρ (h * B * h⁻¹)
  have hB0 : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := mem_stabE0.mp hB
  have hkB : kB ∈ Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)) := by
    rw [mem_hinf_stabilizer_iff hf h kB]
    change ((rho3 ρ (h * B * h⁻¹) : ↥H) : MulAut W) ∈
      CFSG.Quasithin.perfectCore (H ⊓ Ch11.SecA.stabW (preLine hf h))
    exact (mem_perfectCore_HU1_iff hSL hf h _).mpr ⟨B, hB0, rfl⟩
  have hz : (rho3 ρ M * kB * (rho3 ρ M)⁻¹ * kB⁻¹ : ↥H) ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))) :=
    hcomm kB hkB
  have hz' : ((rho3 ρ M * kB * (rho3 ρ M)⁻¹ * kB⁻¹ : ↥H) : MulAut W) ∈
      CFSG.Open.pCoreOf 2 (CFSG.Quasithin.perfectCore
        (H ⊓ Ch11.SecA.stabW (preLine hf h))) :=
    (mem_pCore_hinf_iff hf h _).mp hz
  obtain ⟨C, hCquot, hCz⟩ := levi_of_mem_pCoreOf_HU1 hSL hf h hz'
  refine ⟨C, hCquot, ?_⟩
  have hzD : ((rho3 ρ M * kB * (rho3 ρ M)⁻¹ * kB⁻¹ : ↥H) : MulAut W) =
      ((rho3 ρ (h * (D * B * D⁻¹ * B⁻¹) * h⁻¹) : ↥H) : MulAut W) := by
    simp only [kB, D, map_mul, map_inv]
    congr 1
    group
  have hH : rho3 ρ (h * C * h⁻¹) = rho3 ρ (h * (D * B * D⁻¹ * B⁻¹) * h⁻¹) := by
    apply Subtype.ext
    exact hCz.symm.trans hzD
  have hmat : C = D * B * D⁻¹ * B⁻¹ := by
    have h1 := (rho3_bijective hf).1 hH
    exact mul_left_cancel (mul_right_cancel h1)
  change D * B * D⁻¹ * B⁻¹ = C
  exact hmat.symm

private theorem lev_mul_of_mem_stdLine {A B : Matrix (Fin 3) (Fin 3) K}
    (hA : A *ᵥ ![1, 0, 0] ∈ stdLine K) : lev (A * B) = lev A * lev B := by
  have h10 : A 1 0 = 0 := by
    have h := (mem_stdLine.mp hA).1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have h20 : A 2 0 = 0 := by
    have h := (mem_stdLine.mp hA).2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  exact lev_mul h10 h20

private theorem mem_stdLine_mul {A B : Matrix (Fin 3) (Fin 3) K}
    (hA : A *ᵥ ![1, 0, 0] ∈ stdLine K) (hB : B *ᵥ ![1, 0, 0] ∈ stdLine K) :
    (A * B) *ᵥ ![1, 0, 0] ∈ stdLine K := by
  have h1 : (A * B) *ᵥ ![1, 0, 0] = A *ᵥ (B *ᵥ ![1, 0, 0]) :=
    (Matrix.mulVec_mulVec ![1, 0, 0] A B).symm
  rw [h1, mem_stdLine]
  have hA10 : A 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (mem_stdLine.mp hA).1
  have hA20 : A 2 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (mem_stdLine.mp hA).2
  have hB1 : (B *ᵥ ![1, 0, 0]) 1 = 0 := (mem_stdLine.mp hB).1
  have hB2 : (B *ᵥ ![1, 0, 0]) 2 = 0 := (mem_stdLine.mp hB).2
  constructor
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp [hA10, hB1, hB2]
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp [hA20, hB1, hB2]

private theorem inv_mulVec_e0 {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0]) (hμ : μ ≠ 0) :
    ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![1, 0, 0] = μ⁻¹ • ![1, 0, 0] := by
  have h := congrArg (fun v => ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ v) hD
  rw [ginv_g_mulVec, Matrix.mulVec_smul] at h
  have h' := congrArg (fun v => μ⁻¹ • v) h
  rw [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h'
  exact h'.symm

private theorem lev_conj_commutator {D B : Matrix.SpecialLinearGroup (Fin 3) K} {μ : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0]) (hμ : μ ≠ 0)
    (hB : B ∈ stabE0 K) :
    lev (((D * B * D⁻¹ * B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) =
      lev (D : Matrix (Fin 3) (Fin 3) K) * lev (B : Matrix (Fin 3) (Fin 3) K) *
        lev ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          lev ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hDmem : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] ∈ stdLine K := by
    rw [hD]; exact mem_stdLine.mpr ⟨by simp, by simp⟩
  have hDimem : ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] ∈ stdLine K := by
    rw [inv_mulVec_e0 hD hμ]; exact mem_stdLine.mpr ⟨by simp, by simp⟩
  have hBmem : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] ∈ stdLine K := by
    rw [mem_stabE0.mp hB]; exact mem_stdLine.mpr ⟨by simp, by simp⟩
  have hDBmem : ((D : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *ᵥ
      ![1, 0, 0] ∈ stdLine K := mem_stdLine_mul hDmem hBmem
  have hDBDimem : (((D : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
      ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
        ![1, 0, 0] ∈ stdLine K := mem_stdLine_mul hDBmem hDimem
  have hcoe : (((D * B * D⁻¹ * B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) =
      (((D : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
        ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
          ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe]
  calc lev ((((D : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
        ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
          ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      = lev (((D : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
          ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            lev ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
        lev_mul_of_mem_stdLine hDBDimem
    _ = (lev ((D : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
          lev ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            lev ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [lev_mul_of_mem_stdLine hDBmem]
    _ = ((lev (D : Matrix (Fin 3) (Fin 3) K) * lev (B : Matrix (Fin 3) (Fin 3) K)) *
          lev ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            lev ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [lev_mul_of_mem_stdLine hDmem]

private theorem lev_eq_one_of_quot_trivial {C : Matrix.SpecialLinearGroup (Fin 3) K}
    (hC : ∀ v : Fin 3 → K, ((C : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 = v 1 ∧
      ((C : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = v 2) :
    lev (C : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [lev, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (hC ![0, 1, 0]).1
  · simpa [lev, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (hC ![0, 0, 1]).1
  · simpa [lev, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (hC ![0, 1, 0]).2
  · simpa [lev, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (hC ![0, 0, 1]).2

private theorem lev_commutator_eq_one {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h M : Matrix.SpecialLinearGroup (Fin 3) K)
    (hcomm : ∀ k ∈ Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)),
      rho3 ρ M * k * (rho3 ρ M)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))))
    {B : Matrix.SpecialLinearGroup (Fin 3) K} (hB : B ∈ stabE0 K) :
    lev ((((h⁻¹ * M * h) * B * (h⁻¹ * M * h)⁻¹ * B⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 1 := by
  obtain ⟨C, hCquot, hCeq⟩ := exists_quot_trivial_of_commutator hSL hf h M hcomm hB
  have hClev : lev (C : Matrix (Fin 3) (Fin 3) K) = 1 := lev_eq_one_of_quot_trivial hCquot
  rw [hCeq]
  exact hClev

private theorem lev_inv_mul_eq_one {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hDmem : ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ![1, 0, 0] ∈ stdLine K) :
    lev ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      lev (D : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← lev_mul_of_mem_stdLine hDmem]
  rw [show ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (D : Matrix (Fin 3) (Fin 3) K) = (1 : Matrix (Fin 3) (Fin 3) K) by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lev]

private theorem commute_of_mul_eq_one {L A Linv Ainv : Matrix (Fin 2) (Fin 2) K}
    (hprod : L * A * Linv * Ainv = 1) (hAinvA : Ainv * A = 1) (hLinvL : Linv * L = 1) :
    L * A = A * L := by
  have h : L * A * Linv = A := by
    have h := congrArg (fun X => X * A) hprod
    rw [mul_assoc, hAinvA, mul_one, one_mul] at h
    exact h
  have h' := congrArg (fun X => X * L) h
  rw [mul_assoc, hLinvL, mul_one] at h'
  exact h'

private theorem lev_conj_commute {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h M : Matrix.SpecialLinearGroup (Fin 3) K)
    (hcomm : ∀ k ∈ Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)),
      rho3 ρ M * k * (rho3 ρ M)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))))
    {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0]) (hμ : μ ≠ 0)
    (hDdef : D = h⁻¹ * M * h) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    lev (D : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * lev (D : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨B, hBlev⟩ := leviHom_surjective A
  have hB : (B : Matrix.SpecialLinearGroup (Fin 3) K) ∈ stabE0 K := B.2
  have h1 := lev_commutator_eq_one hSL hf h M hcomm hB
  have h1' : lev (((D * (B : Matrix.SpecialLinearGroup (Fin 3) K) * D⁻¹ *
      (B : Matrix.SpecialLinearGroup (Fin 3) K)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) = 1 := by
    rw [hDdef]; exact h1
  have hDimem : ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] ∈ stdLine K := by
    rw [inv_mulVec_e0 hD hμ]; exact mem_stdLine.mpr ⟨by simp, by simp⟩
  have hAeq : lev ((B : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hBlev, leviHom_coe]
  have h2 := lev_conj_commutator (D := D) (B := (B : Matrix.SpecialLinearGroup (Fin 3) K))
    hD hμ hB
  rw [hAeq] at h2
  set Linv : Matrix (Fin 2) (Fin 2) K :=
    lev ((D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hLinv
  have hprod : lev (D : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 2) (Fin 2) K) *
      Linv * lev (((B : Matrix.SpecialLinearGroup (Fin 3) K)⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← h2]
    simpa [hLinv] using h1'
  have hBimem : (((B : Matrix.SpecialLinearGroup (Fin 3) K)⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ![1, 0, 0] ∈ stdLine K := by
    rw [mem_stabE0.mp ((stabE0 K).inv_mem hB)]
    exact mem_stdLine.mpr ⟨by simp, by simp⟩
  have hAinvA : lev (((B : Matrix.SpecialLinearGroup (Fin 3) K)⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← hAeq]; exact lev_inv_mul_eq_one hBimem
  have hLinvL : Linv * lev (D : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hLinv]; exact lev_inv_mul_eq_one hDimem
  exact commute_of_mul_eq_one hprod hAinvA hLinvL

private theorem matrix_eq_smul_one_of_mulVec {L : Matrix (Fin 2) (Fin 2) K} {c : K}
    (hL : ∀ x : Fin 2 → K, L *ᵥ x = c • x) : L = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using
      congrFun (hL ![1, 0]) 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using
      congrFun (hL ![0, 1]) 0
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using
      congrFun (hL ![1, 0]) 1
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply] using
      congrFun (hL ![0, 1]) 1

theorem exists_smul_one_lev {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h M : Matrix.SpecialLinearGroup (Fin 3) K)
    (hcomm : ∀ k ∈ Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W)),
      rho3 ρ M * k * (rho3 ρ M)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))))
    {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0]) (hμ : μ ≠ 0)
    (hDdef : D = h⁻¹ * M * h) :
    ∃ c : K, lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  let L : Matrix (Fin 2) (Fin 2) K := lev (D : Matrix (Fin 3) (Fin 3) K)
  have hLcomm : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      L * (A : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) * L :=
    fun A => lev_conj_commute hSL hf h M hcomm hD hμ hDdef A
  have hf : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) K) (x : Fin 2 → K),
      (Matrix.toLin' L) ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x) =
        (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (Matrix.toLin' L) x := by
    intro A x
    calc (Matrix.toLin' L) ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x)
        = L *ᵥ ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x) := Matrix.toLin'_apply L _
      _ = (L * (A : Matrix (Fin 2) (Fin 2) K)) *ᵥ x :=
          Matrix.mulVec_mulVec x L (A : Matrix (Fin 2) (Fin 2) K)
      _ = ((A : Matrix (Fin 2) (Fin 2) K) * L) *ᵥ x := by rw [hLcomm A]
      _ = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (L *ᵥ x) :=
          (Matrix.mulVec_mulVec x (A : Matrix (Fin 2) (Fin 2) K) L).symm
      _ = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (Matrix.toLin' L) x := by
          rw [Matrix.toLin'_apply]
  obtain ⟨c, hc⟩ := CFSG.Quasithin.C41Pf.SL3N.exists_scalar_of_commute
    (Matrix.toLin' L).toAddMonoidHom hf
  refine ⟨c, ?_⟩
  change L = c • (1 : Matrix (Fin 2) (Fin 2) K)
  exact matrix_eq_smul_one_of_mulVec fun x => by
    have h := hc x
    simpa using h

theorem eq_tSL_mul_uSL {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0])
    (hlev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hμc : μ * c ^ 2 = 1) (hc0 : c ≠ 0) :
    ∃ a b : K, D = tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹,
      Units.mk0 c hc0) * uSL a b 0 := by
  have hμ : μ = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hμc
  have h00 : (D : Matrix (Fin 3) (Fin 3) K) 0 0 = μ := by
    have := congrFun hD 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h10 : (D : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := congrFun hD 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h20 : (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := congrFun hD 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h11 : (D : Matrix (Fin 3) (Fin 3) K) 1 1 = c := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h12 : (D : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h21 : (D : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h22 : (D : Matrix (Fin 3) (Fin 3) K) 2 2 = c := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  refine ⟨c ^ 2 * (D : Matrix (Fin 3) (Fin 3) K) 0 1,
    c ^ 2 * (D : Matrix (Fin 3) (Fin 3) K) 0 2, ?_⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.SpecialLinearGroup.coe_mul] <;>
    simp [tSL, tFun, tMat, coe_uSL, uMat, Matrix.mul_apply, Fin.sum_univ_three,
      h00, h10, h20, h11, h12, h21, h22, hμ] <;>
    field_simp [hc0]

private theorem eq_zero_of_fixed_of_scalar {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0])
    (hlev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hμ1 : μ ≠ 1) (hc1 : c ≠ 1) {y : Fin 3 → K}
    (hy : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ y = y) : y = 0 := by
  have h00 : (D : Matrix (Fin 3) (Fin 3) K) 0 0 = μ := by
    have := congrFun hD 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h10 : (D : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := congrFun hD 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h20 : (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := congrFun hD 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h11 : (D : Matrix (Fin 3) (Fin 3) K) 1 1 = c := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h12 : (D : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h21 : (D : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h22 : (D : Matrix (Fin 3) (Fin 3) K) 2 2 = c := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h1 : y 1 = 0 := by
    have h := congrFun hy 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h11, h12] at h
    have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
    have hz : (c - 1) * y 1 = 0 := by rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left hc
  have h2 : y 2 = 0 := by
    have h := congrFun hy 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, h22] at h
    have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
    have hz : (c - 1) * y 2 = 0 := by rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left hc
  have h0 : y 0 = 0 := by
    have h := congrFun hy 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, h1, h2] at h
    have hμ : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ1
    have hz : (μ - 1) * y 0 = 0 := by rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left hμ
  exact vec3_eq h0 h1 h2

private theorem uSL_eq_one_of_conj_fixed {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0])
    (hlev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hμc : μ * c ^ 2 = 1) (hc0 : c ≠ 0) (hc3 : c ^ 3 ≠ 1) {a b : K}
    (hfix : (((D * uSL a b 0 * D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = (uSL a b 0 : Matrix (Fin 3) (Fin 3) K)) :
    uSL a b 0 = 1 := by
  obtain ⟨a', b', hD_eq⟩ := eq_tSL_mul_uSL hD hlev hμc hc0
  let T : Matrix.SpecialLinearGroup (Fin 3) K :=
    tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0)
  let N : Matrix.SpecialLinearGroup (Fin 3) K := uSL a' b' 0
  let B : Matrix.SpecialLinearGroup (Fin 3) K := uSL a b 0
  have hD_eq' : D = T * N := by simpa only [T, N] using hD_eq
  have hNB : N * B * N⁻¹ = B := by
    have hcomm : N * B = B * N := by
      simp only [N, B, uSL_mul]
      congr 1 <;> simp [add_comm, add_left_comm, mul_zero]
    rw [hcomm]
    group
  have hTconj : T * B * T⁻¹ = uSL ((c ^ 3)⁻¹ * a) ((c ^ 3)⁻¹ * b) 0 := by
    simp only [T, B, tSL_conj_uSL, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    congr 2 <;> field_simp [hc0] <;> ring
  have hDB : D * B * D⁻¹ = T * B * T⁻¹ := by
    calc D * B * D⁻¹ = (T * N) * B * (T * N)⁻¹ := by rw [hD_eq']
      _ = T * (N * B * N⁻¹) * T⁻¹ := by group
      _ = T * B * T⁻¹ := by rw [hNB]
  have hfixSL : D * B * D⁻¹ = B := Subtype.ext hfix
  rw [hDB, hTconj] at hfixSL
  obtain ⟨ha, hb, -⟩ := uSL_injective hfixSL
  have hc3inv1 : (c ^ 3)⁻¹ ≠ 1 := by
    intro h
    apply hc3
    rw [← inv_inv (c ^ 3), h, inv_one]
  have ha0 : a = 0 := by
    have hz : ((c ^ 3)⁻¹ - 1) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc3inv1)
  have hb0 : b = 0 := by
    have hz : ((c ^ 3)⁻¹ - 1) * b = 0 := by rw [sub_mul, one_mul, hb, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc3inv1)
  rw [ha0, hb0, uSL_zero]

theorem mu_mul_sq_of_line_lev {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0])
    (hlev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    μ * c ^ 2 = 1 := by
  have h00 : (D : Matrix (Fin 3) (Fin 3) K) 0 0 = μ := by
    have := congrFun hD 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h10 : (D : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := congrFun hD 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h20 : (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := congrFun hD 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h11 : (D : Matrix (Fin 3) (Fin 3) K) 1 1 = c := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h12 : (D : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h21 : (D : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have h22 : (D : Matrix (Fin 3) (Fin 3) K) 2 2 = c := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hlev
    simpa [lev_apply, Matrix.smul_apply, Matrix.one_apply] using this
  have hdet : (D : Matrix (Fin 3) (Fin 3) K).det = 1 := D.2
  rw [Matrix.det_fin_three] at hdet
  simpa [h00, h10, h20, h11, h12, h21, h22, pow_two, mul_assoc] using hdet

private theorem uSL_sq_eq_one (a b : K) : (uSL a b 0) ^ 2 = 1 := by
  rw [sq, uSL_mul]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha : a + a = 0 := by rw [← two_mul, h2, zero_mul]
  have hb : b + b + a * 0 = 0 := by rw [mul_zero, add_zero, ← two_mul, h2, zero_mul]
  rw [ha, hb, zero_add, uSL_zero]

private theorem eq_one_of_lev_eq_one_of_odd {E : Matrix.SpecialLinearGroup (Fin 3) K} {ν : K}
    (hE : (E : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ν • ![1, 0, 0])
    (hlev : lev (E : Matrix (Fin 3) (Fin 3) K) = 1) (hodd : Odd (orderOf E)) : E = 1 := by
  have h00 : (E : Matrix (Fin 3) (Fin 3) K) 0 0 = ν := by
    have := congrFun hE 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h10 : (E : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := congrFun hE 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h20 : (E : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := congrFun hE 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have h11 : (E : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hlev
    simpa [lev_apply, Matrix.one_apply] using this
  have h12 : (E : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hlev
    simpa [lev_apply, Matrix.one_apply] using this
  have h21 : (E : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hlev
    simpa [lev_apply, Matrix.one_apply] using this
  have h22 : (E : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hlev
    simpa [lev_apply, Matrix.one_apply] using this
  have hν : ν = 1 := by
    have hdet : (E : Matrix (Fin 3) (Fin 3) K).det = 1 := E.2
    rw [Matrix.det_fin_three] at hdet
    simpa [h00, h10, h20, h11, h12, h21, h22] using hdet
  have hE0 : (E : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
    rw [hE, hν, one_smul]
  have hEstab : E ∈ stabE0 K := mem_stabE0.mpr hE0
  have hlevHom : leviHom K ⟨E, hEstab⟩ = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [leviHom_coe]
    fin_cases i <;> fin_cases j <;> simp [lev, h11, h12, h21, h22]
  have hEeq : E = uSL ((E : Matrix (Fin 3) (Fin 3) K) 0 1)
      ((E : Matrix (Fin 3) (Fin 3) K) 0 2) 0 := by
    simpa using eq_uSL_of_mem_ker (B := ⟨E, hEstab⟩) hlevHom
  have hsq : E ^ 2 = 1 := by rw [hEeq, uSL_sq_eq_one]
  have hdvd : orderOf E ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · rw [h2] at hodd
    exact absurd hodd (by norm_num)

private theorem lev_pow_three {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0]) :
    lev (((D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      lev (D : Matrix (Fin 3) (Fin 3) K) ^ 3 := by
  have hD10 : (D : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := congrFun hD 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hD20 : (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := congrFun hD 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hDD10 : ((D : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K)) 1 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp [hD10, hD20]
  have hDD20 : ((D : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K)) 2 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp [hD10, hD20]
  have hcube : (((D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = (((D * D : Matrix.SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K) := by
    rw [show (D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) =
      (D * D) * D by rw [pow_succ, pow_two], Matrix.SpecialLinearGroup.coe_mul]
  rw [hcube, Matrix.SpecialLinearGroup.coe_mul, lev_mul hDD10 hDD20, lev_mul hD10 hD20]
  rw [show lev (D : Matrix (Fin 3) (Fin 3) K) ^ 3 =
    lev (D : Matrix (Fin 3) (Fin 3) K) * lev (D : Matrix (Fin 3) (Fin 3) K) *
      lev (D : Matrix (Fin 3) (Fin 3) K) by rw [pow_succ, pow_two]]

private theorem pow_three_eq_one_of_scalar {D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0])
    (hlev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hc3 : c ^ 3 = 1) (hodd : Odd (orderOf D)) : D ^ 3 = 1 := by
  have hlevD3 : lev (((D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = 1 := by
    rw [lev_pow_three hD, hlev, smul_pow, one_pow, hc3, one_smul]
  have hD10 : (D : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have := congrFun hD 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hD20 : (D : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have := congrFun hD 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hDD10 : ((D : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K)) 1 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp [hD10, hD20]
  have hDD20 : ((D : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K)) 2 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp [hD10, hD20]
  have hcube : (((D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = (((D * D : Matrix.SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K) := by
    rw [show (D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) =
      (D * D) * D by rw [pow_succ, pow_two], Matrix.SpecialLinearGroup.coe_mul]
  have hD3_10 : ((D : Matrix (Fin 3) (Fin 3) K) ^ 3) 1 0 = 0 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hcube, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_three]
    simp [hDD10, hD10, hD20]
  have hD3_20 : ((D : Matrix (Fin 3) (Fin 3) K) ^ 3) 2 0 = 0 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hcube, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_three]
    simp [hDD20, hD10, hD20]
  have hD3e0 : (((D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) *ᵥ ![1, 0, 0] =
        ((((D ^ 3 : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)) 0 0) • ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.SpecialLinearGroup.coe_pow, hD3_10, hD3_20]
  exact eq_one_of_lev_eq_one_of_odd hD3e0 hlevD3 (hodd.of_dvd_nat (orderOf_pow_dvd 3))

private theorem g_cube_eq_one_of_D_cube {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H}
    {h M D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hDdef : D = h⁻¹ * M * h) (hD3 : D ^ 3 = 1) : (rho3 ρ M) ^ 3 = 1 := by
  have hM3 : M ^ 3 = 1 := by
    rw [show M = h * D * h⁻¹ by rw [hDdef]; group]
    rw [conj_pow, hD3]
    group
  rw [← map_pow, hM3, map_one]

private theorem pointTorus_fixed_W {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    {h M D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (hDdef : D = h⁻¹ * M * h)
    (hDe0 : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0])
    (hclev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hμ1 : μ ≠ 1) (hc1 : c ≠ 1) :
    ∀ w : W, ((rho3 ρ M : ↥H) : MulAut W) w = w → w = 1 := by
  intro w hw
  have hMw : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ f w = f w := by
    have h := congrArg f hw
    rwa [hf.act3] at h
  let y : Fin 3 → K :=
    ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w
  have hcoord : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ y = y := by
    have h1 : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ y =
        ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ y)) := by
      rw [hDdef]
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [(Matrix.mulVec_mulVec y (((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) * (M : Matrix (Fin 3) (Fin 3) K))
            (h : Matrix (Fin 3) (Fin 3) K)).symm,
          (Matrix.mulVec_mulVec ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ y)
            ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
            (M : Matrix (Fin 3) (Fin 3) K)).symm]
    calc (D : Matrix (Fin 3) (Fin 3) K) *ᵥ y
        = ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ
              ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ y)) := h1
      _ = ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) := by rw [g_ginv_mulVec]
      _ = y := by rw [hMw]
  have hy : y = 0 := eq_zero_of_fixed_of_scalar hDe0 hclev hμ1 hc1 hcoord
  have hfw0 : f w = 0 := by
    have hginv := g_ginv_mulVec h (f w)
    rw [show ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f w = 0 from hy, Matrix.mulVec_zero] at hginv
    exact hginv.symm
  have hmem : w * 1⁻¹ ∈ (⊥ : Subgroup W) :=
    (hf.eq_iff w 1).mp (by rw [hfw0, hf.map_one])
  simpa using hmem

private theorem pointTorus_fixed_U {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    {h M D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (hDdef : D = h⁻¹ * M * h)
    (hDe0 : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = μ • ![1, 0, 0])
    (hclev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hμc : μ * c ^ 2 = 1) (hc0 : c ≠ 0) (hc3 : c ^ 3 ≠ 1) :
    ∀ u ∈ CFSG.Open.pCoreOf 2
      (Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))),
      (rho3 ρ M : ↥H) * u * (rho3 ρ M : ↥H)⁻¹ = u → u = 1 := by
  intro u hu hfix
  obtain ⟨a, b, rfl⟩ := (mem_pCore_hinf_iff_exists_uSL hSL hf h u).mp hu
  let B : Matrix.SpecialLinearGroup (Fin 3) K := uSL a b 0
  have hfixSL : M * (h * B * h⁻¹) * M⁻¹ = h * B * h⁻¹ := by
    apply (rho3_bijective hf).1
    apply Subtype.ext
    have hfix' := congrArg (fun x : ↥H => (x : MulAut W)) hfix
    simpa [B, map_mul, map_inv] using hfix'
  have hDconj : D * B * D⁻¹ = B := by
    calc D * B * D⁻¹ = h⁻¹ * (M * (h * B * h⁻¹) * M⁻¹) * h := by
          rw [hDdef]; group
      _ = h⁻¹ * (h * B * h⁻¹) * h := by rw [hfixSL]
      _ = B := by group
  have hfixMat : (((D * B * D⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) = (B : Matrix (Fin 3) (Fin 3) K) :=
    congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K))
      hDconj
  have hBone : B = 1 := uSL_eq_one_of_conj_fixed hDe0 hclev hμc hc0 hc3 hfixMat
  rw [show uSL a b 0 = B from rfl, hBone]
  simp

theorem kSL3PointTorus_scalar_properties {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    {h : Matrix.SpecialLinearGroup (Fin 3) K}
    {M D : Matrix.SpecialLinearGroup (Fin 3) K} {μ c : K}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (hDdef : D = h⁻¹ * M * h) (hDe0 : (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] =
      μ • ![1, 0, 0])
    (hclev : lev (D : Matrix (Fin 3) (Fin 3) K) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hodd : Odd (orderOf (rho3 ρ M))) (hg3 : (rho3 ρ M) ^ 3 ≠ 1) :
    Odd (orderOf D) ∧ c ≠ 0 ∧ c ^ 3 ≠ 1 ∧ c ≠ 1 ∧ μ ≠ 1 := by
  have hμc : μ * c ^ 2 = 1 := mu_mul_sq_of_line_lev hDe0 hclev
  have hc0 : c ≠ 0 := by
    intro hc
    have h01 : (0 : K) = 1 := by simpa [hc] using hμc
    exact zero_ne_one h01
  have hoddD : Odd (orderOf D) := by
    have h1 : orderOf (rho3 ρ M) = orderOf M :=
      orderOf_injective (rho3 ρ) (rho3_bijective hf).1 M
    have h2 : orderOf D = orderOf M := by
      rw [hDdef]
      exact SemiconjBy.orderOf_eq h (x := h⁻¹ * M * h) (y := M) (by
        rw [SemiconjBy]; group)
    rw [h2, ← h1]
    exact hodd
  have hc3 : c ^ 3 ≠ 1 := by
    intro hc3eq
    exact hg3 (g_cube_eq_one_of_D_cube hDdef
      (pow_three_eq_one_of_scalar hDe0 hclev hc3eq hoddD))
  have hc1 : c ≠ 1 := by
    intro hc
    exact hc3 (by rw [hc]; norm_num)
  have hμ1 : μ ≠ 1 := by
    intro hμ
    have hc2 : c ^ 2 = 1 := by rw [hμ, one_mul] at hμc; exact hμc
    have hc1' : c = 1 := by
      rcases sq_eq_one_iff.mp hc2 with hc | hc
      · exact hc
      · rw [hc, CharTwo.neg_eq]
    exact hc1 hc1'
  exact ⟨hoddD, hc0, hc3, hc1, hμ1⟩

theorem mem_stabilizer_of_commutator {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    {h : Matrix.SpecialLinearGroup (Fin 3) K} {Kstar' : Subgroup ↥H} {g : ↥H}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (hKstar' : Kstar' = Hinf (MulAction.stabilizer ↥H
      ((preLine hf h : Subgroup W) : Set W)))
    (hcomm : ∀ k ∈ Kstar', g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Kstar') :
    g ∈ MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W) := by
  have hKmap : Kstar'.map (MulAut.conj g).toMonoidHom = Kstar' :=
    map_conj_eq_self_of_commutator hcomm
  have hUmap : (CFSG.Open.pCoreOf 2 Kstar').map (MulAut.conj g).toMonoidHom =
      CFSG.Open.pCoreOf 2 Kstar' := map_conj_pCore_eq_self hKmap
  have hUconj := mem_pCore_conj_iff hUmap
  have hCeq : ∀ w, w ∈ preLine hf h ↔
      ∀ u ∈ CFSG.Open.pCoreOf 2 Kstar', (u : MulAut W) w = w := by
    intro w
    constructor
    · intro hw u hu
      apply apply_eq_of_mem_pCore_hinf hSL hf h _ hw
      rwa [hKstar'] at hu
    · intro hw
      rw [hKstar'] at hw
      exact mem_preLine_of_forall_pCore_fix hSL hf h hw
  exact mem_stabilizer_of_pCore_fix hCeq hUconj

theorem kSL3PointTorus_holds : KSL3PointTorus := by
  intro W _ _ H n hSLn hnat hn S ℓ Pℓ Kstar g hodd hg3 hcomm
  obtain ⟨K, hfield, hfinite, hK, ρ, hρ⟩ := hnat
  letI : Field K := hfield; letI : Finite K := hfinite
  letI : CharP K 2 := charP_two_of_card (by omega) hK
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL := commutator_SL2_eq_top (four_le_card (by omega) hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 3 K)) hρ
  obtain ⟨h, hh⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
    (CFSG.Quasithin.A4.isSylowTwoOf_map H S)
  let Kstar' : Subgroup ↥H := Hinf (MulAction.stabilizer ↥H
    ((preLine hf h : Subgroup W) : Set W))
  have hKstar' : Kstar = Kstar' := by
    show Hinf (MulAction.stabilizer ↥H (ℓ : Set W)) = Kstar'
    rw [show ℓ = preLine hf h from fixedPointSubgroup_eq_preLine hf hh]
  have hcomm' : ∀ k ∈ Kstar', g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Kstar' := by
    simpa [hKstar'] using hcomm
  have hgPℓ' := mem_stabilizer_of_commutator hSL hf rfl hcomm'
  obtain ⟨M, rfl⟩ := (rho3_bijective hf).2 g
  have hgStab : ((rho3 ρ M : ↥H) : MulAut W) ∈ Ch11.SecA.stabW (preLine hf h) := by
    have hG := hgPℓ'
    change (rho3 ρ M : ↥H) ∈ setStab H (preLine hf h) at hG
    rw [setStab_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hG
    exact hG.2
  obtain ⟨μ, hμ0, hDe0⟩ := exists_smul_e0_of_mem_stabW hf h M rfl hgStab
  obtain ⟨c, hclev⟩ := exists_smul_one_lev hSL hf h M hcomm' hDe0 hμ0 rfl
  obtain ⟨hoddD, hc0, hc3, hc1, hμ1⟩ := kSL3PointTorus_scalar_properties hf rfl hDe0 hclev hodd hg3
  refine ⟨?_, ?_⟩
  · intro w hw; exact pointTorus_fixed_W hf rfl hDe0 hclev hμ1 hc1 w hw
  · intro u hu hfix; rw [hKstar'] at hu
    exact pointTorus_fixed_U hSL hf rfl hDe0 hclev (mu_mul_sq_of_line_lev hDe0 hclev)
      hc0 hc3 u hu hfix

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
