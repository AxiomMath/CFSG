module

public import CFSG.RankThree.PartOne.S13K.Sp6Lin
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG.RankThree.PartOne.KFQ CFSG.GroupTheory.WeirSylow Module
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj StatedSL)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev Sp1 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (Qext K ≃ₗ[K] Qext K) :=
  formIsometryGroup K (fun x y : Qext K => qForm x y)

noncomputable abbrev sp1Space (K : Type) [Field K] [Finite K] [CharP K 2] : FormSpace K K :=
  ⟨Qext K, fun x y => qForm x y⟩

theorem isSymplecticSpace_sp1 : IsSymplecticSpace (sp1Space K) :=
  ⟨qForm, fun _ _ => rfl, qForm_isAlt, qForm_nondegenerate⟩

theorem finrank_sp1 : finrank K (sp1Space K).V = 2 * 1 := by
  change finrank K (Qext K) = 2 * 1
  rw [finrank_qext]

theorem nonempty_sp1Equiv : Nonempty (↥(Sp1 K) ≃* ↥(StatedSp 1 K)) := by
  obtain ⟨B, hBF, hBa, hBn⟩ := isSymplecticSpace_sp1 (K := K)
  obtain ⟨ι⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_form_isometry B
    (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K 1) hBa hBn
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [finrank_sp1, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard])
  let e₁ : (sp1Space K).isom ≃* (stdSympSpace K 1).isom :=
    formIsometryGroupCongr ι.toLinearEquiv fun x y => by
      rw [hBF]
      exact ι.map_app y x
  let M := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun K (Fin 1 ⊕ Fin 1))
  have hmem : ∀ g : (stdSympSpace K 1).isom, M g.1 ∈ StatedSp 1 K := fun g => by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp]
    exact Subgroup.mem_map_of_mem _ (TauCeti.BilinForm.mem_isometryGroup_iff.2 g.2)
  let ψ₀ : (stdSympSpace K 1).isom →* StatedSp 1 K :=
    { toFun := fun g => ⟨M g.1, hmem g⟩
      map_one' := Subtype.ext (map_one M)
      map_mul' := fun g h => Subtype.ext (map_mul M g.1 h.1) }
  have hinj : Function.Injective ψ₀ := fun g h hgh =>
    Subtype.ext (M.injective (congrArg Subtype.val hgh))
  have hsurj : Function.Surjective ψ₀ := by
    rintro ⟨A, hA⟩
    have hA' := hA
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp] at hA'
    obtain ⟨g, hg, hgA⟩ := hA'
    refine ⟨⟨g, ?_⟩, Subtype.ext hgA⟩
    intro x y
    exact TauCeti.BilinForm.mem_isometryGroup_iff.1 hg x y
  have hbij : Function.Bijective (ψ₀.comp e₁.toMonoidHom) :=
    ⟨hinj.comp e₁.injective, hsurj.comp e₁.surjective⟩
  exact ⟨MulEquiv.ofBijective _ hbij⟩

@[expose] noncomputable def liftZero (h : Qext K ≃ₗ[K] Qext K) : AutV K :=
  LinearEquiv.piCongrRight fun j : Fin 3 => if j = 0 then h else LinearEquiv.refl K (Qext K)

theorem liftZero_apply (h : Qext K ≃ₗ[K] Qext K) (v : QV K (Fin 3)) (j : Fin 3) :
    liftZero h v j = if j = 0 then h (v 0) else v j := by
  by_cases hj : j = 0
  · subst hj
    simp [liftZero]
  · simp [liftZero, hj]

theorem liftZero_one : liftZero (1 : Qext K ≃ₗ[K] Qext K) = 1 := by
  refine LinearEquiv.ext fun v => ?_
  funext j
  rw [liftZero_apply]
  by_cases hj : j = 0
  · subst hj
    simp
  · simp [hj]

theorem liftZero_mul (h h' : Qext K ≃ₗ[K] Qext K) : liftZero (h * h') = liftZero h * liftZero h' := by
  refine LinearEquiv.ext fun v => ?_
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [LinearEquiv.mul_apply, liftZero_apply]
  · simp [LinearEquiv.mul_apply, liftZero_apply, hj]

theorem liftZero_mem_M10 {h : Qext K ≃ₗ[K] Qext K} (hh : h ∈ Sp1 K) : liftZero h ∈ M10 K := by
  rw [mem_M10_iff']
  intro x y
  simp only [liftZero_apply, ite_true, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, ite_false]
  rw [show qForm (h (x 0)) (h (y 0)) = qForm (x 0) (y 0) from hh _ _]

@[expose] noncomputable def ρS : ↥(Sp1 K) →* ↥(M10 K) where
  toFun h := ⟨liftZero h.1, liftZero_mem_M10 h.2⟩
  map_one' := Subtype.ext liftZero_one
  map_mul' h h' := Subtype.ext (liftZero_mul h.1 h'.1)

theorem ρS_apply (h : ↥(Sp1 K)) : (ρS h : ↥(M10 K)).1 = liftZero h.1 := rfl

theorem ρS_injective : Function.Injective (ρS : ↥(Sp1 K) →* ↥(M10 K)) := by
  intro h h' hh
  have h1 : liftZero h.1 = liftZero h'.1 := by
    have := congrArg (fun g : ↥(M10 K) => g.1) hh
    simpa [ρS_apply] using this
  apply Subtype.ext
  refine LinearEquiv.ext fun a => ?_
  have := congrArg (fun g : AutV K => g (sg 0 a) 0) h1
  simpa [liftZero_apply] using this

theorem ρS_mem_sBlk (h : ↥(Sp1 K)) : ρS h ∈ sBlk K := by
  intro a
  refine ⟨?_, ?_⟩
  · funext j
    rw [ρS_apply, liftZero_apply]
    by_cases hj : j = 0
    · subst hj
      simp
    · simp [hj]
  · funext j
    rw [ρS_apply, liftZero_apply]
    by_cases hj : j = 0
    · subst hj
      simp
    · simp [hj]

@[expose] noncomputable def resZeroLin (g : ↥(M10 K)) : Qext K →ₗ[K] Qext K :=
  (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => Qext K) 0).comp
    (g.1.toLinearMap.comp (LinearMap.single K (fun _ : Fin 3 => Qext K) 0))

theorem resZeroLin_apply (g : ↥(M10 K)) (a : Qext K) : resZeroLin g a = g.1 (sg 0 a) 0 := rfl

theorem sg_zero_of_sBlk {g : ↥(M10 K)} (hg : g ∈ sBlk K) (a : Qext K) :
    g.1 (sg 0 a) = sg 0 (resZeroLin g a) := by
  obtain ⟨h1, h2⟩ := sBlk_sg_zero hg a
  funext j
  fin_cases j
  · simp [resZeroLin_apply]
  · simpa using h1
  · simpa using h2

theorem resZeroLin_mul {g h : ↥(M10 K)} (hh : h ∈ sBlk K) (a : Qext K) :
    resZeroLin (g * h) a = resZeroLin g (resZeroLin h a) := by
  rw [resZeroLin_apply, resZeroLin_apply]
  change g.1 (h.1 (sg 0 a)) 0 = g.1 (sg 0 (resZeroLin h a)) 0
  rw [sg_zero_of_sBlk hh a]

theorem resZeroLin_one (a : Qext K) : resZeroLin (1 : ↥(M10 K)) a = a := by
  simp [resZeroLin_apply]

@[expose] noncomputable def resZero (g : ↥(sBlk K)) : Qext K ≃ₗ[K] Qext K :=
  LinearEquiv.ofLinearMap (resZeroLin g.1) (resZeroLin g⁻¹.1)
    (LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, ← resZeroLin_mul g⁻¹.2]
      have : g.1 * (g⁻¹ : ↥(sBlk K)).1 = 1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel]
        rfl
      rw [show (g.1 * (g⁻¹ : ↥(sBlk K)).1 : ↥(M10 K)) = 1 from this, resZeroLin_one])
    (LinearMap.ext fun a => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, ← resZeroLin_mul g.2]
      have : (g⁻¹ : ↥(sBlk K)).1 * g.1 = 1 := by
        rw [← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      rw [show ((g⁻¹ : ↥(sBlk K)).1 * g.1 : ↥(M10 K)) = 1 from this, resZeroLin_one])

theorem resZero_apply (g : ↥(sBlk K)) (a : Qext K) : resZero g a = g.1.1 (sg 0 a) 0 := rfl

theorem resZero_mem_Sp1 (g : ↥(sBlk K)) : resZero g ∈ Sp1 K := by
  intro x y
  have h1 := formQ_map g.1.2 (sg 0 x) (sg 0 y)
  rw [sg_zero_of_sBlk g.2 x, sg_zero_of_sBlk g.2 y, formQ_sg_left, formQ_sg_left] at h1
  simpa [resZero_apply, sg_zero_of_sBlk g.2] using h1

@[expose] noncomputable def resHom : ↥(sBlk K) →* ↥(Sp1 K) where
  toFun g := ⟨resZero g, resZero_mem_Sp1 g⟩
  map_one' := by
    apply Subtype.ext
    refine LinearEquiv.ext fun a => ?_
    simp [resZero_apply]
  map_mul' g h := by
    apply Subtype.ext
    refine LinearEquiv.ext fun a => ?_
    change resZeroLin (g.1 * h.1) a = _
    rw [resZeroLin_mul h.2]
    rfl

theorem resHom_apply (g : ↥(sBlk K)) (a : Qext K) : (resHom g : Qext K ≃ₗ[K] Qext K) a =
    g.1.1 (sg 0 a) 0 := rfl

theorem resHom_bijective : Function.Bijective (resHom : ↥(sBlk K) →* ↥(Sp1 K)) := by
  constructor
  · intro g g' hgg
    have h1 : ∀ a, resZeroLin g.1 a = resZeroLin g'.1 a := fun a => by
      have := congrArg (fun h : ↥(Sp1 K) => (h : Qext K ≃ₗ[K] Qext K) a) hgg
      simpa [resHom_apply, resZeroLin_apply] using this
    apply Subtype.ext
    apply Subtype.ext
    refine autV_ext_sg (fun a => ?_) (fun a => ?_) (fun a => ?_)
    · rw [sg_zero_of_sBlk g.2, sg_zero_of_sBlk g'.2, h1]
    · rw [(g.2 a).1, (g'.2 a).1]
    · rw [(g.2 a).2, (g'.2 a).2]
  · intro h
    refine ⟨⟨ρS h, ρS_mem_sBlk h⟩, ?_⟩
    apply Subtype.ext
    refine LinearEquiv.ext fun a => ?_
    simp [resHom_apply, ρS_apply, liftZero_apply]

@[expose] noncomputable def sBlkEquivSp1 : ↥(sBlk K) ≃* ↥(Sp1 K) :=
  MulEquiv.ofBijective resHom resHom_bijective

theorem nonempty_sBlk_mulEquiv_SL2 :
    Nonempty (↥(sBlk K) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨e⟩ := nonempty_sp1Equiv (K := K)
  exact ⟨(sBlkEquivSp1.trans e).trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm⟩

theorem sBlk_model {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    CFSG.IsQuasisimple ↥(sBlk K) ∧ Subgroup.center ↥(sBlk K) = ⊥ ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(sBlk K) .PSL 2 2 f := by
  obtain ⟨e⟩ := nonempty_sBlk_mulEquiv_SL2 (K := K)
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      exact hq
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := K)
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.RankThree.Classical.isQuasisimple_SL2 h4),
    by rw [← Subgroup.map_center_eq e.symm, CFSG.RankThree.PartOne.KFU.center_SL2_eq_bot,
      Subgroup.map_bot], ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance,
    hK, ⟨e.trans e'⟩⟩
  · intro hc
    simp only [Prod.mk.injEq, true_and] at hc
    omega
  · intro hc
    simp only [Prod.mk.injEq, true_and] at hc
    omega

end CFSG.RankThree.PartOne.S13K
