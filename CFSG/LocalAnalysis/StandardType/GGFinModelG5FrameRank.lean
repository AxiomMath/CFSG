module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5RankOne
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5LangDatum
public import CFSG.LocalAnalysis.StandardType.GGLangTorusAssembly
public import CFSG.LocalAnalysis.StandardType.GGLatPermExc

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LangRat CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphInvolution

section FrameRank

private theorem g5_sl2Upper_eq_uSL (c : GGL) : sl2Upper GGL c = uSL c := rfl
private theorem g5_sl2Lower_eq_vSL (c : GGL) : sl2Lower GGL c = vSL c := rfl

private theorem g5_HSL_conj_uSL {M : Type*} [Field M] (a : Mˣ) (c : M) :
    (HSL a : SL2 M) * uSL c * (HSL a)⁻¹ = uSL ((a : M) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, uSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

private theorem g5_HSL_conj_vSL {M : Type*} [Field M] (a : Mˣ) (c : M) :
    (HSL a : SL2 M) * vSL c * (HSL a)⁻¹ = vSL (((a⁻¹ : Mˣ) : M) ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

private theorem g5_map_uSL (f : ℕ) (c : GGL) :
    Matrix.SpecialLinearGroup.map (ggFrobT f) (uSL c) = uSL (c ^ 2 ^ f) := by
  apply Subtype.ext
  show (↑(Matrix.SpecialLinearGroup.map (ggFrobT f) (uSL c)) : Matrix (Fin 2) (Fin 2) GGL) =
    (↑(uSL (c ^ 2 ^ f)) : Matrix (Fin 2) (Fin 2) GGL)
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, ggFrobT_apply, uSL]

private theorem g5_map_vSL (f : ℕ) (c : GGL) :
    Matrix.SpecialLinearGroup.map (ggFrobT f) (vSL c) = vSL (c ^ 2 ^ f) := by
  apply Subtype.ext
  show (↑(Matrix.SpecialLinearGroup.map (ggFrobT f) (vSL c)) : Matrix (Fin 2) (Fin 2) GGL) =
    (↑(vSL (c ^ 2 ^ f)) : Matrix (Fin 2) (Fin 2) GGL)
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, Matrix.map_apply, ggFrobT_apply, vSL]

private theorem g5_frobSL2_surjective (f : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (ggFrobT f) :
      SL2 GGL → SL2 GGL) := by
  intro B
  have hgen : B ∈ Subgroup.closure (Set.range (sl2Upper GGL) ∪ Set.range (sl2Lower GGL)) := by
    rw [sl2_closure_upper_lower]
    exact Subgroup.mem_top B
  have hle : Subgroup.closure (Set.range (sl2Upper GGL) ∪ Set.range (sl2Lower GGL)) ≤
      (Matrix.SpecialLinearGroup.map (ggFrobT f) : SL2 GGL →* SL2 GGL).range := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c
        (pow_pos (by norm_num : (0:ℕ) < 2) f)
      refine ⟨uSL c', ?_⟩
      rw [g5_sl2Upper_eq_uSL, g5_map_uSL, hc']
    · obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c
        (pow_pos (by norm_num : (0:ℕ) < 2) f)
      refine ⟨vSL c', ?_⟩
      rw [g5_sl2Lower_eq_vSL, g5_map_vSL, hc']
  exact hle hgen

private theorem g5_eq_one_of_commute_uSL_vSL {L : Type*} [Field L] [CharP L 2] {Y : SL2 L}
    (hu : uSL 1 * Y = Y * uSL 1) (hv : vSL 1 * Y = Y * vSL 1) : Y = 1 := by
  have hum := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L)) hu
  have hvm := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hum hvm
  have hscal := CFSG.RankThree.QuadraticSL2.eq_scalar_of_commute
    (Y : Matrix (Fin 2) (Fin 2) L) hum.symm hvm.symm
  have hdet : (Y : Matrix (Fin 2) (Fin 2) L).det = 1 := Y.2
  have h1 : (Y : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    rw [hscal] at hdet
    simp [Matrix.scalar_apply] at hdet
    rcases hdet with h | h
    · exact h
    · rw [h]
      exact CharTwo.neg_eq (1 : L)
  refine Subtype.ext ?_
  rw [hscal, h1]
  simp

private theorem g5_latGram_gram_eq_iform
    {t : StatedLieTag} (f : ℕ) (ht : GGExcFive t)
    (α β : Fin (ggU (absTag t) 6 f).D.rank → ℤ) :
    latGram (gram t f) α β =
      iform (ggLangReidx (rank_eq_langTag f ht) α) (ggLangReidx (rank_eq_langTag f ht) β) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem g5_reidx_single {R N : ℕ} (h : R = N) (j : Fin R) :
    ggLangReidx h (Pi.single j (1:ℤ)) = Pi.single (Fin.cast h j) (1:ℤ) := by
  funext i
  rw [ggLangReidx, Pi.single_apply, Pi.single_apply]
  by_cases h1 : Fin.cast h.symm i = j
  · have h2 : i = Fin.cast h j := by
      have := congrArg (Fin.cast h) h1
      simpa using this
    rw [if_pos h1, if_pos h2]
  · have h2 : i ≠ Fin.cast h j := by
      intro hc
      apply h1
      have := congrArg (Fin.cast h.symm) hc
      simpa using this
    rw [if_neg h1, if_neg h2]

private theorem g5_corootCoord_eq
    {t : StatedLieTag} {p f : ℕ} [NeZero p] (ht : GGExcFive t)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ}
    (j : Fin (ggU (absTag t) 6 f).D.rank) :
    corootCoord p (gram t f) β j =
      ((corootPair (ggLangReidx (rank_eq_langTag f ht) β)
        (Pi.single (Fin.cast (rank_eq_langTag f ht) j) (1:ℤ)) : ℤ) : ZMod p) := by
  have hsingle := g5_reidx_single (rank_eq_langTag f ht) j
  have hden : latGram (gram t f) β β =
      iform (ggLangReidx (rank_eq_langTag f ht) β) (ggLangReidx (rank_eq_langTag f ht) β) :=
    g5_latGram_gram_eq_iform f ht β β
  rw [corootCoord, g5_latGram_gram_eq_iform f ht, hden, hsingle, corootPair, iform_comm]


private theorem g5_zeta_zpow_congr {p : ℕ} [NeZero p] {ζ : GGLˣ} (hζ : orderOf ζ = p)
    {m n : ℤ} (h : (m : ZMod p) = (n : ZMod p)) : ζ ^ m = ζ ^ n := by
  rw [zpow_eq_zpow_iff_modEq, hζ]
  exact (ZMod.intCast_eq_intCast_iff m n p).mp h

private theorem g5_rootChar_ggParam {τ : Tag} {R p : ℕ} [NeZero p] (hR : R = τ.rank)
    {ζ : GGLˣ} (z : Fin R → ZMod p) (α : Fin R → ℤ) :
    rootChar (ggParam hR ζ z) (ggLangReidx hR α) =
      ζ ^ (∑ i, ((z i).val : ℤ) * α i) := by
  unfold rootChar ggParam ggLangReidx
  have hprod : (∏ j : Fin τ.rank,
      (ζ ^ (z (Fin.cast hR.symm j)).val) ^ (α (Fin.cast hR.symm j))) =
      ∏ j : Fin τ.rank,
        ζ ^ (((z (Fin.cast hR.symm j)).val : ℤ) * α (Fin.cast hR.symm j)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
  rw [hprod, Finset.prod_zpow_eq_zpow_sum]
  congr 1
  rw [← Fintype.sum_equiv (finCongr hR)
    (fun i : Fin R => ((z i).val : ℤ) * α i)
    (fun j : Fin τ.rank =>
      ((z (Fin.cast hR.symm j)).val : ℤ) * α (Fin.cast hR.symm j))]
  intro i
  simp

private theorem g5_rootChar_ggParam_eq_one_iff {τ : Tag} {R p : ℕ} [NeZero p] (hR : R = τ.rank)
    {ζ : GGLˣ} (hζ : orderOf ζ = p) (z : Fin R → ZMod p) (α : Fin R → ℤ) :
    rootChar (ggParam hR ζ z) (ggLangReidx hR α) = 1 ↔ latChar p z α = 0 := by
  rw [g5_rootChar_ggParam, ← orderOf_dvd_iff_zpow_eq_one, hζ,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcast : ((∑ i, ((z i).val : ℤ) * α i : ℤ) : ZMod p) = latChar p z α := by
    simp only [latChar, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [← hcast]

private theorem g5_rootChar_neg {τ : Tag} {E : Type} [Field E] (b : Fin τ.rank → Eˣ)
    (β : Fin τ.rank → ℤ) : rootChar b (-β) = (rootChar b β)⁻¹ := by
  have h := rootChar_sub b 0 β
  rwa [zero_sub, rootChar_zero, one_mul] at h

private theorem g5_rootDiagUnit_conj_rootSL2
    {τ : Tag} {E : Type} [Field E] (h2 : (2 : E) = 0)
    (b : Fin τ.rank → Eˣ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (s : Eˣ)
    (hs : s ^ 2 = rootChar b β) (A : SL2 E) :
    rootDiagUnit τ b * rootSL2 τ E β A * (rootDiagUnit τ b)⁻¹ =
      rootSL2 τ E β (HSL s * A * (HSL s)⁻¹) := by
  let f₁ : SL2 E →* ModGL τ E :=
    (MulAut.conj (rootDiagUnit τ b)).toMonoidHom.comp (rootSL2 τ E β)
  let f₂ : SL2 E →* ModGL τ E :=
    (rootSL2 τ E β).comp (MulAut.conj (HSL s)).toMonoidHom
  have hu : ∀ c, f₁ (uSL c) = f₂ (uSL c) := by
    intro c
    show rootDiagUnit τ b * rootSL2 τ E β (uSL c) * (rootDiagUnit τ b)⁻¹ =
      rootSL2 τ E β (HSL s * uSL c * (HSL s)⁻¹)
    rw [rootSL2_uSL_of_two h2, g5_HSL_conj_uSL, rootSL2_uSL_of_two h2,
      rootDiagUnit_conj_pinnedX b hβ, ← hs]
    simp
  have hv : ∀ c, f₁ (vSL c) = f₂ (vSL c) := by
    intro c
    show rootDiagUnit τ b * rootSL2 τ E β (vSL c) * (rootDiagUnit τ b)⁻¹ =
      rootSL2 τ E β (HSL s * vSL c * (HSL s)⁻¹)
    rw [rootSL2_vSL_of_two h2 hβ, g5_HSL_conj_vSL, rootSL2_vSL_of_two h2 hβ,
      rootDiagUnit_conj_pinnedX b (IsRoot.neg hβ)]
    have hneg : rootChar b (-β) = (s⁻¹) ^ 2 := by
      rw [g5_rootChar_neg, ← hs]
      group
    rw [hneg]
    simp
  have heq : f₁ = f₂ := MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower (by
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hu c
    · exact hv c)
  exact DFunLike.congr_fun heq A

private theorem g5_uMap_conj_rootSL2
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t}
    {C : Type} [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ}
    (F : GGLangFrame t p f ht)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D ι₀ ζ)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : β ∈ F.frame)
    (z : Multiplicative (ggFixAdd p (piB t p f))) (s : GGLˣ)
    (hs : s ^ 2 = rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
      (ggLangReidx (rank_eq_langTag f ht) β))
    (A : SL2 GGL) :
    hT.uMap z * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A *
        (hT.uMap z)⁻¹ =
      rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
        ((F.z * HSL s * F.z⁻¹) * A * (F.z * HSL s * F.z⁻¹)⁻¹) := by
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  have hβroot : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).mp (F.frame_root β hβ)
  set Z := F.z * HSL s * F.z⁻¹
  have hactinv : F.M.D.g0⁻¹ *
      rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A * F.M.D.g0 =
      rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
        (F.z⁻¹ * A * F.z) := by
    have h := F.act β hβ (F.z⁻¹ * A * F.z)
    rw [show F.z * (F.z⁻¹ * A * F.z) * F.z⁻¹ = A by group] at h
    calc F.M.D.g0⁻¹ * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A *
          F.M.D.g0
        = F.M.D.g0⁻¹ * (F.M.D.g0 *
            rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
              (F.z⁻¹ * A * F.z) * F.M.D.g0⁻¹) * F.M.D.g0 := by rw [h]
      _ = rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (F.z⁻¹ * A * F.z) := by
          group
  calc hT.uMap z * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A *
        (hT.uMap z)⁻¹
      = F.M.D.g0 * (rootDiagUnit (langTag t)
            (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1) *
          (F.M.D.g0⁻¹ *
            rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A * F.M.D.g0) *
          (rootDiagUnit (langTag t)
            (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1))⁻¹) *
          F.M.D.g0⁻¹ := by
        rw [hT.uMap_apply]
        group
    _ = F.M.D.g0 * (rootDiagUnit (langTag t)
            (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1) *
          rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (F.z⁻¹ * A * F.z) *
          (rootDiagUnit (langTag t)
            (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1))⁻¹) *
          F.M.D.g0⁻¹ := by rw [hactinv]
    _ = F.M.D.g0 * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
          (HSL s * (F.z⁻¹ * A * F.z) * (HSL s)⁻¹) * F.M.D.g0⁻¹ := by
        rw [g5_rootDiagUnit_conj_rootSL2 h2 _ hβroot s hs]
    _ = rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
          (F.z * (HSL s * (F.z⁻¹ * A * F.z) * (HSL s)⁻¹) * F.z⁻¹) := by
        rw [F.act β hβ]
    _ = rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (Z * A * Z⁻¹) := by
        simp only [Z]
        group

private theorem g5_Z_mem_ratSL2
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t}
    {C : Type} [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ}
    (F : GGLangFrame t p f ht)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D ι₀ ζ)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : β ∈ F.frame)
    (z : Multiplicative (ggFixAdd p (piB t p f))) (s : GGLˣ)
    (hs : s ^ 2 = rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
      (ggLangReidx (rank_eq_langTag f ht) β)) :
    F.z * HSL s * F.z⁻¹ ∈ ratSL2 f := by
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  have hβroot : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).mp (F.frame_root β hβ)
  have hfixg := F.frame_graph β hβ
  have hfixU : ggPhi t f (hT.uMap z) = hT.uMap z := by
    rw [← F.M.hΦ]
    exact ((LangDatum.mem_fix F.M.D).mp (hT.uMap_mem_fix z)).2
  set Z := F.z * HSL s * F.z⁻¹ with hZ
  have hEq : ∀ A : SL2 GGL,
      Z * Matrix.SpecialLinearGroup.map (ggFrobT f) A * Z⁻¹ =
        Matrix.SpecialLinearGroup.map (ggFrobT f) Z *
          Matrix.SpecialLinearGroup.map (ggFrobT f) A *
            (Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ := by
    intro A
    have hphi := congrArg (ggPhi t f) (g5_uMap_conj_rootSL2 F hT hβ z s hs A)
    rw [map_mul, map_mul, map_inv, hfixU,
      ggG5_phi_rootSL2 ht f hβroot hfixg A] at hphi
    rw [ggG5_phi_rootSL2 ht f hβroot hfixg (Z * A * Z⁻¹)] at hphi
    rw [show Matrix.SpecialLinearGroup.map (ggFrobT f) (Z * A * Z⁻¹) =
        Matrix.SpecialLinearGroup.map (ggFrobT f) Z * Matrix.SpecialLinearGroup.map (ggFrobT f) A *
          (Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ by rw [map_mul, map_mul, map_inv]] at hphi
    rw [g5_uMap_conj_rootSL2 F hT hβ z s hs (Matrix.SpecialLinearGroup.map (ggFrobT f) A)] at hphi
    have hphi' := rootSL2_injective_of_two h2 (ggLangReidx (rank_eq_langTag f ht) β) hphi
    simpa only [← hZ] using hphi'
  have hcomm : ∀ B : SL2 GGL, ((Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ * Z) * B =
      B * ((Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ * Z) := by
    intro B
    obtain ⟨A, rfl⟩ := g5_frobSL2_surjective f B
    have h := hEq A
    calc ((Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ * Z) *
          Matrix.SpecialLinearGroup.map (ggFrobT f) A
        = (Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ *
            (Z * Matrix.SpecialLinearGroup.map (ggFrobT f) A) := by group
      _ = (Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ *
            ((Z * Matrix.SpecialLinearGroup.map (ggFrobT f) A * Z⁻¹) * Z) := by group
      _ = (Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ *
            ((Matrix.SpecialLinearGroup.map (ggFrobT f) Z *
              Matrix.SpecialLinearGroup.map (ggFrobT f) A *
              (Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹) * Z) := by rw [h]
      _ = Matrix.SpecialLinearGroup.map (ggFrobT f) A *
            ((Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ * Z) := by group
  have hC1 : (Matrix.SpecialLinearGroup.map (ggFrobT f) Z)⁻¹ * Z = 1 :=
    g5_eq_one_of_commute_uSL_vSL (hcomm (uSL 1)).symm (hcomm (vSL 1)).symm
  have hFrZ : Matrix.SpecialLinearGroup.map (ggFrobT f) Z = Z := inv_mul_eq_one.mp hC1
  rw [ratSL2]
  show Matrix.SpecialLinearGroup.map (ggFrobT f) Z = Z
  exact hFrZ


private theorem g5_HSL_one {M : Type*} [Field M] : (HSL (1 : Mˣ) : SL2 M) = 1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

private theorem g5_HSL_injective {M : Type*} [Field M] :
    Function.Injective (HSL : Mˣ → SL2 M) := by
  intro a b h
  have h' := congrArg (fun g : SL2 M => (g : Matrix (Fin 2) (Fin 2) M) 0 0) h
  exact Units.ext (by simpa [HSL] using h')

private theorem g5_corootCoord_mem_ggFixAdd
    {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : latPerm (piB t p f) β = β) :
    corootCoord p (gram t f) β ∈ ggFixAdd p (piB t p f) := by
  have hGram : ∀ a b : Fin (ggU (absTag t) 6 f).D.rank → ℤ,
      latGram (gram t f) (latPerm (piB t p f) a) (latPerm (piB t p f) b) =
        latGram (gram t f) a b :=
    latGram_latPerm (ggU (absTag t) 6 f).D (gram t f) (isRootGram_gram f ht)
      (piB t p f) (isDiagAut_piB p f ht) (nodesConnected_univ_exc t f ht)
  rw [mem_ggFixAdd]
  intro i
  have hsingle : latPerm (piB t p f) (Pi.single i (1:ℤ)) = Pi.single (piB t p f i) 1 := by
    ext j
    simp only [latPerm, Pi.single_apply, Equiv.symm_apply_eq]
  have h1 := hGram (Pi.single i (1:ℤ)) β
  rw [hsingle, hβ] at h1
  unfold corootCoord
  rw [h1]

private theorem g5_rootDiagUnit_coroot_eq
    {t : StatedLieTag} {p f : ℕ} [NeZero p]
    {ht : GGExcFive t} {C : Type} [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ}
    (F : GGLangFrame t p f ht)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D ι₀ ζ)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : β ∈ F.frame) :
    rootDiagUnit (langTag t) (ggParam (rank_eq_langTag f ht) ζ
        (corootCoord p (gram t f) β)) =
      rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (HSL ζ) := by
  have hβroot : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).mp (F.frame_root β hβ)
  have hb : ∀ j : Fin (langTag t).rank,
      ggParam (rank_eq_langTag f ht) ζ (corootCoord p (gram t f) β) j =
        ζ ^ corootPair (ggLangReidx (rank_eq_langTag f ht) β) (Pi.single j 1) := by
    intro j
    have hjj : Fin.cast (rank_eq_langTag f ht) (Fin.cast (rank_eq_langTag f ht).symm j) = j := by
      simp
    show ζ ^ (corootCoord p (gram t f) β (Fin.cast (rank_eq_langTag f ht).symm j)).val =
      ζ ^ corootPair (ggLangReidx (rank_eq_langTag f ht) β) (Pi.single j 1)
    rw [g5_corootCoord_eq ht (j := Fin.cast (rank_eq_langTag f ht).symm j), hjj, ← zpow_natCast]
    exact g5_zeta_zpow_congr hT.ζ_order (by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val])
  have hbridge :=
    rootDiagUnit_eq_prod_rootSL2_HSL (τ := langTag t) (L := GGL) [ggLangReidx (rank_eq_langTag f ht) β]
      (by intro γ hγ; simp at hγ; subst hγ; exact hβroot)
      (fun _ => ζ) (b := ggParam (rank_eq_langTag f ht) ζ (corootCoord p (gram t f) β))
      (by intro j; simpa using hb j)
  simpa using hbridge


private theorem g5_HSL_mul {M : Type*} [Field M] (a b : Mˣ) :
    (HSL a : SL2 M) * HSL b = HSL (a * b) := by
  refine Subtype.ext ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private def g5_HSL_hom (M : Type*) [Field M] : Mˣ →* SL2 M where
  toFun := HSL
  map_one' := g5_HSL_one
  map_mul' := fun a b => (g5_HSL_mul a b).symm

private theorem g5_orderOf_HSL {M : Type*} [Field M] (a : Mˣ) :
    orderOf (HSL a : SL2 M) = orderOf a :=
  orderOf_injective (g5_HSL_hom M) (fun x y h => by
    apply g5_HSL_injective
    simpa [g5_HSL_hom] using h) a

theorem ggG5_frame_normalizer
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t} {C : Type}
    [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ} (F : GGLangFrame t p f ht)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D ι₀ ζ)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : β ∈ F.frame)
    (z : Multiplicative (ggFixAdd p (piB t p f))) :
    hT.uMap z ∈ Subgroup.normalizer
      ((ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β) :
        Subgroup (ModGL (langTag t) GGL)) : Set (ModGL (langTag t) GGL)) := by
  have hβroot : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).mp (F.frame_root β hβ)
  have hfixg := F.frame_graph β hβ
  obtain ⟨s0, hs0⟩ := IsAlgClosed.exists_pow_nat_eq
    ((rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
      (ggLangReidx (rank_eq_langTag f ht) β) : GGL))
    (by norm_num : (0:ℕ) < 2)
  have hsne : s0 ≠ 0 := by
    intro h0
    rw [h0] at hs0
    simpa using hs0.symm
  let s : GGLˣ := Units.mk0 s0 hsne
  have hs : s ^ 2 = rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
      (ggLangReidx (rank_eq_langTag f ht) β) := by
    apply Units.ext
    show (s0 : GGL) ^ 2 = (rootChar (ggParam (rank_eq_langTag f ht) ζ
      (Multiplicative.toAdd z).1) (ggLangReidx (rank_eq_langTag f ht) β) : GGL)
    simpa using hs0
  have hZ : F.z * HSL s * F.z⁻¹ ∈ ratSL2 f := g5_Z_mem_ratSL2 F hT hβ z s hs
  rw [ggG5_ratRankOne_eq ht f hβroot hfixg]
  apply (Subgroup.mem_normalizer_iff_map_conj_eq).mpr
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨B, hB, hBA⟩ := hA
    subst hBA
    change hT.uMap z * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) B *
        (hT.uMap z)⁻¹ ∈
      Subgroup.map (rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)) (ratSL2 f)
    rw [g5_uMap_conj_rootSL2 F hT hβ z s hs B]
    exact Subgroup.mem_map.mpr ⟨(F.z * HSL s * F.z⁻¹) * B * (F.z * HSL s * F.z⁻¹)⁻¹,
      (ratSL2 f).mul_mem ((ratSL2 f).mul_mem hZ hB) ((ratSL2 f).inv_mem hZ), rfl⟩
  · rintro ⟨A, hA, rfl⟩
    refine ⟨rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
        ((F.z * HSL s * F.z⁻¹)⁻¹ * A * (F.z * HSL s * F.z⁻¹)), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(F.z * HSL s * F.z⁻¹)⁻¹ * A * (F.z * HSL s * F.z⁻¹),
        (ratSL2 f).mul_mem ((ratSL2 f).mul_mem ((ratSL2 f).inv_mem hZ) hA) hZ, rfl⟩
    · change hT.uMap z * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
          ((F.z * HSL s * F.z⁻¹)⁻¹ * A * (F.z * HSL s * F.z⁻¹)) * (hT.uMap z)⁻¹ =
        rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A
      rw [g5_uMap_conj_rootSL2 F hT hβ z s hs
        ((F.z * HSL s * F.z⁻¹)⁻¹ * A * (F.z * HSL s * F.z⁻¹))]
      congr 1
      group


theorem ggG5_frame_centralizer_iff
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t}
    {C : Type} [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ} (F : GGLangFrame t p f ht)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D ι₀ ζ)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : β ∈ F.frame)
    (z : Multiplicative (ggFixAdd p (piB t p f))) :
    hT.uMap z ∈ Subgroup.centralizer
      ((ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β) :
        Subgroup (ModGL (langTag t) GGL)) : Set (ModGL (langTag t) GGL)) ↔
      latChar p (Multiplicative.toAdd z).1 β = 0 := by
  have hβroot : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).mp (F.frame_root β hβ)
  have hfixg := F.frame_graph β hβ
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  obtain ⟨s0, hs0⟩ := IsAlgClosed.exists_pow_nat_eq
    ((rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
      (ggLangReidx (rank_eq_langTag f ht) β) : GGL))
    (by norm_num : (0:ℕ) < 2)
  have hsne : s0 ≠ 0 := by
    intro h0
    rw [h0] at hs0
    simpa using hs0.symm
  let s : GGLˣ := Units.mk0 s0 hsne
  have hs : s ^ 2 = rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
      (ggLangReidx (rank_eq_langTag f ht) β) := by
    apply Units.ext
    show (s0 : GGL) ^ 2 = (rootChar (ggParam (rank_eq_langTag f ht) ζ
      (Multiplicative.toAdd z).1) (ggLangReidx (rank_eq_langTag f ht) β) : GGL)
    simpa using hs0
  have hZ : F.z * HSL s * F.z⁻¹ ∈ ratSL2 f := g5_Z_mem_ratSL2 F hT hβ z s hs
  have huSL1 : uSL 1 ∈ ratSL2 f := by
    rw [ratSL2]
    show Matrix.SpecialLinearGroup.map (ggFrobT f) (uSL 1) = uSL 1
    rw [g5_map_uSL]
    norm_num
  have hvSL1 : vSL 1 ∈ ratSL2 f := by
    rw [ratSL2]
    show Matrix.SpecialLinearGroup.map (ggFrobT f) (vSL 1) = vSL 1
    rw [g5_map_vSL]
    norm_num
  rw [Subgroup.mem_centralizer_iff, ggG5_ratRankOne_eq ht f hβroot hfixg]
  constructor
  · intro hc
    have hconj (A : SL2 GGL) (hA : A ∈ ratSL2 f) :
        hT.uMap z * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A *
          (hT.uMap z)⁻¹ =
          rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A := by
      have hm : rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A ∈
          Subgroup.map (rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β))
            (ratSL2 f) :=
        Subgroup.mem_map.mpr ⟨A, hA, rfl⟩
      have h := hc _ hm
      rw [← h]
      group
    have hZu : F.z * HSL s * F.z⁻¹ * uSL 1 * (F.z * HSL s * F.z⁻¹)⁻¹ = uSL 1 := by
      have hphi : rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
          (F.z * HSL s * F.z⁻¹ * uSL 1 * (F.z * HSL s * F.z⁻¹)⁻¹) =
          rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (uSL 1) := by
        rw [← g5_uMap_conj_rootSL2 F hT hβ z s hs (uSL 1)]
        exact hconj (uSL 1) huSL1
      exact rootSL2_injective_of_two h2 _ hphi
    have hZv : F.z * HSL s * F.z⁻¹ * vSL 1 * (F.z * HSL s * F.z⁻¹)⁻¹ = vSL 1 := by
      have hphi : rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
          (F.z * HSL s * F.z⁻¹ * vSL 1 * (F.z * HSL s * F.z⁻¹)⁻¹) =
          rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (vSL 1) := by
        rw [← g5_uMap_conj_rootSL2 F hT hβ z s hs (vSL 1)]
        exact hconj (vSL 1) hvSL1
      exact rootSL2_injective_of_two h2 _ hphi
    have hcommu : uSL 1 * (F.z * HSL s * F.z⁻¹) =
        (F.z * HSL s * F.z⁻¹) * uSL 1 := by
      calc uSL 1 * (F.z * HSL s * F.z⁻¹) =
          (F.z * HSL s * F.z⁻¹ * uSL 1 * (F.z * HSL s * F.z⁻¹)⁻¹) *
            (F.z * HSL s * F.z⁻¹) := by rw [hZu]
        _ = (F.z * HSL s * F.z⁻¹) * uSL 1 := by group
    have hcommv : vSL 1 * (F.z * HSL s * F.z⁻¹) =
        (F.z * HSL s * F.z⁻¹) * vSL 1 := by
      calc vSL 1 * (F.z * HSL s * F.z⁻¹) =
          (F.z * HSL s * F.z⁻¹ * vSL 1 * (F.z * HSL s * F.z⁻¹)⁻¹) *
            (F.z * HSL s * F.z⁻¹) := by rw [hZv]
        _ = (F.z * HSL s * F.z⁻¹) * vSL 1 := by group
    have hZ1 : F.z * HSL s * F.z⁻¹ = 1 :=
      g5_eq_one_of_commute_uSL_vSL hcommu hcommv
    have hHs : HSL s = 1 := by
      have h := hZ1
      calc HSL s = F.z⁻¹ * (F.z * HSL s * F.z⁻¹) * F.z := by group
        _ = F.z⁻¹ * 1 * F.z := by rw [h]
        _ = 1 := by group
    have hs1 : s = 1 := g5_HSL_injective (by rw [hHs, g5_HSL_one])
    have hrc : rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
        (ggLangReidx (rank_eq_langTag f ht) β) = 1 := by
      rw [← hs, hs1]
      simp
    exact (g5_rootChar_ggParam_eq_one_iff (rank_eq_langTag f ht) hT.ζ_order
      (Multiplicative.toAdd z).1 β).mp hrc
  · intro hlat
    have hrc : rootChar (ggParam (rank_eq_langTag f ht) ζ (Multiplicative.toAdd z).1)
        (ggLangReidx (rank_eq_langTag f ht) β) = 1 :=
      (g5_rootChar_ggParam_eq_one_iff (rank_eq_langTag f ht) hT.ζ_order
        (Multiplicative.toAdd z).1 β).mpr hlat
    have hs2 : (s : GGL) * s = 1 := by
      have h : s ^ 2 = 1 := by rw [hs, hrc]
      have hv := congrArg (fun u : GGLˣ => (u : GGL)) h
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two] at hv
      exact hv
    have hs1 : s = 1 := Units.ext
      (eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hs2)
    have hZ1 : F.z * HSL s * F.z⁻¹ = 1 := by
      rw [hs1]
      simp [g5_HSL_one]
    intro y hy
    obtain ⟨A, hA, hxy⟩ := hy
    subst hxy
    have hZA : hT.uMap z * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A *
        (hT.uMap z)⁻¹ =
        rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A := by
      rw [g5_uMap_conj_rootSL2 F hT hβ z s hs A, hZ1]
      congr 1
      group
    calc rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A * hT.uMap z
        = ((hT.uMap z) * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A *
            (hT.uMap z)⁻¹) * hT.uMap z := by rw [hZA]
      _ = hT.uMap z * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A := by
          group


theorem ggG5_frame_pelt
    {t : StatedLieTag} {p f : ℕ} [NeZero p] {ht : GGExcFive t} {C : Type}
    [Group C] {ι₀ : C →* ModGL (langTag t) GGL} {ζ : GGLˣ} (F : GGLangFrame t p f ht)
    (hT : GGTorusData (rank_eq_langTag f ht) p (piB t p f) F.M.D ι₀ ζ)
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hβ : β ∈ F.frame) :
    ∃ z : Multiplicative (ggFixAdd p (piB t p f)),
      (Multiplicative.toAdd z).1 = corootCoord p (gram t f) β ∧
      hT.uMap z ∈ ratRankOne t f (ggLangReidx (rank_eq_langTag f ht) β) ∧
      orderOf (hT.uMap z) = p := by
  have hβroot : IsRoot (langTag t) (ggLangReidx (rank_eq_langTag f ht) β) :=
    (mem_roots_iff_isRoot f ht β).mp (F.frame_root β hβ)
  have hfixg := F.frame_graph β hβ
  have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
  have hmem : corootCoord p (gram t f) β ∈ ggFixAdd p (piB t p f) :=
    g5_corootCoord_mem_ggFixAdd ht (F.frame_fixed β hβ)
  let z : Multiplicative (ggFixAdd p (piB t p f)) :=
    Multiplicative.ofAdd ⟨corootCoord p (gram t f) β, hmem⟩
  have hz : (Multiplicative.toAdd z).1 = corootCoord p (gram t f) β := rfl
  have hbridge := g5_rootDiagUnit_coroot_eq F hT hβ
  have hu : hT.uMap z = rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
      (F.z * HSL ζ * F.z⁻¹) := by
    rw [hT.uMap_apply]
    change F.M.D.g0 * rootDiagUnit (langTag t)
        (ggParam (rank_eq_langTag f ht) ζ (corootCoord p (gram t f) β)) * F.M.D.g0⁻¹ =
      rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (F.z * HSL ζ * F.z⁻¹)
    rw [hbridge, F.act β hβ]
  refine ⟨z, hz, ?_, ?_⟩
  · rw [ggG5_ratRankOne_eq ht f hβroot hfixg]
    have hfixU : ggPhi t f (hT.uMap z) = hT.uMap z := by
      rw [← F.M.hΦ]
      exact ((LangDatum.mem_fix F.M.D).mp (hT.uMap_mem_fix z)).2
    have hZ : F.z * HSL ζ * F.z⁻¹ ∈ ratSL2 f := by
      have hphi : rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
          (F.z * HSL ζ * F.z⁻¹) =
          rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
            (Matrix.SpecialLinearGroup.map (ggFrobT f) (F.z * HSL ζ * F.z⁻¹)) := by
        calc rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
              (F.z * HSL ζ * F.z⁻¹) = hT.uMap z := hu.symm
          _ = ggPhi t f (hT.uMap z) := hfixU.symm
          _ = ggPhi t f (rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
                (F.z * HSL ζ * F.z⁻¹)) := by rw [hu]
          _ = rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β)
                (Matrix.SpecialLinearGroup.map (ggFrobT f) (F.z * HSL ζ * F.z⁻¹)) :=
              ggG5_phi_rootSL2 ht f hβroot hfixg (F.z * HSL ζ * F.z⁻¹)
      have h := rootSL2_injective_of_two h2 (ggLangReidx (rank_eq_langTag f ht) β) hphi
      rw [ratSL2]
      show Matrix.SpecialLinearGroup.map (ggFrobT f) (F.z * HSL ζ * F.z⁻¹) =
        F.z * HSL ζ * F.z⁻¹
      exact h.symm
    exact Subgroup.mem_map.mpr ⟨F.z * HSL ζ * F.z⁻¹, hZ, hu.symm⟩
  · rw [hu]
    rw [orderOf_injective (rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β))
      (rootSL2_injective_of_two h2 (ggLangReidx (rank_eq_langTag f ht) β))]
    have hconj : SemiconjBy F.z (HSL ζ : SL2 GGL) (F.z * HSL ζ * F.z⁻¹) := by
      show F.z * HSL ζ = (F.z * HSL ζ * F.z⁻¹) * F.z
      group
    rw [(hconj.orderOf_eq F.z).symm, g5_orderOf_HSL, hT.ζ_order]


end FrameRank

end CFSG.StandardType.GGFinModel.G5
