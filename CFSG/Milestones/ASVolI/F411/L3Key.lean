module

public import CFSG.Milestones.ASVolI.F411.SpOdd
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open Matrix Subgroup CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem burnsideF411_l3_marking_parabolic {p f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 p f H) :
    ∃ e : projectiveSL 3 marking.field ≃* H, ∀ b : Bool, marking.parabolic b =
      (projStabilizer (flagSpace 3 marking.field (if b then 2 else 1))).map e.toMonoidHom := by
  set K := marking.field
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let s : Matrix.SpecialLinearGroup (Fin 3) K ≃* StatedSL 3 K :=
    specialLinearGroupEquivStatedSL 3 K
  have keym : ∀ (b : Bool) (x : StatedSL 3 K),
      x ∈ ChF.ClassicalRoots.nativeParabolic .L3 (p ^ f) K marking.basis b ↔
        s.symm x ∈ stabilizer (flagSpace 3 K (if b then 2 else 1)) := by
    intro b x
    rw [hbasis]
    have h1 : x ∈ ChF.ClassicalRoots.nativeParabolic .L3 (p ^ f) K 1 b ↔
        (x : GL (ChF.ClassicalRoots.Coord .L3) K) ∈ ChF.ClassicalRoots.rawStabilizer
          ((fun vector => ((1 : GL (ChF.ClassicalRoots.Coord .L3) K) :
            Matrix (ChF.ClassicalRoots.Coord .L3) (ChF.ClassicalRoots.Coord .L3) K).mulVec
              vector) ''
            ChF.ClassicalRoots.coordinateSpace (if b then ChF.ClassicalRoots.flagTwo .L3
              else ChF.ClassicalRoots.flagOne .L3)) :=
      Iff.rfl
    have hxu : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((s.symm x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      conv_lhs => rw [← s.apply_symm_apply x]
      rfl
    rw [h1, burnsideF4h_cl_mem_rawStabilizer, mem_stabilizer,
      burnsideF4h_cl_map_eq_iff _
        (C := (((s.symm x)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (coe_inv_mul_coe _)
        (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one])]
    simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
    rw [hxu]
    cases b
    · simp only [Bool.false_eq_true, if_false, ChF.ClassicalRoots.flagOne]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sl_coordinateSpace _).1, (burnsideF4h_cl_sl_coordinateSpace _).1]
    · simp only [if_true, ChF.ClassicalRoots.flagTwo]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sl_coordinateSpace _).2, (burnsideF4h_cl_sl_coordinateSpace _).2]
  let φ : projectiveSL 3 K ≃* StatedProj (StatedSL 3 K) :=
    QuotientGroup.congr (scalars 3 K) ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) s
      (by rw [scalars_eq_center]; exact map_center_eq_statedScalars 3 K)
  let e : projectiveSL 3 K ≃* H := φ.trans marking.identification
  have he : ∀ x : StatedSL 3 K, e (proj 3 K (s.symm x)) = marking.transport x := fun x =>
    congrArg marking.transport (s.apply_symm_apply x)
  refine ⟨e, fun b => ?_⟩
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨proj 3 K (s.symm x), ⟨s.symm x, (keym b x).1 hx, rfl⟩, he x⟩
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨s u, (keym b (s u)).2 (by rwa [MulEquiv.symm_apply_apply]), ?_⟩
    have := he (s u)
    rw [MulEquiv.symm_apply_apply] at this
    exact this.symm

theorem burnsideF411_l3_chart {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : projectiveSL 3 K ≃* ↥Gp),
      Nat.card K = p ^ f ∧
      Gp ⊓ M₁ = (projStabilizer (flagSpace 3 K 1)).map (Gp.subtype.comp e.toMonoidHom) ∧
      Gp ⊓ M₂ = (projStabilizer (flagSpace 3 K 2)).map (Gp.subtype.comp e.toMonoidHom) ∧
      IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨chart, hB, hP1, hP2⟩ := hyp.lie_amalgam
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, -, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  rotate_left
  iterate 5 exact absurd hk (by decide)
  have hc : c = .L3 := by cases c <;> first | rfl | exact absurd hk (by decide)
  subst hc
  haveI : Fact p.Prime := ⟨marking.prime⟩
  set K := marking.field
  have hK : Nat.card K = p ^ f := by simpa using marking.field_card
  have hcl := burnsideF4h_cl_L3 p f ↥Gp marking
  have hmap := burnsideF4h_isLieParabolics_map Gp.subtype Gp.subtype_injective hcl
  rw [burnsideF4h_map_subtype_top, ← h1, ← h2, ← h3, ← hB, ← hP1, ← hP2] at hmap
  obtain ⟨e, hpar⟩ := burnsideF411_l3_marking_parabolic marking
  refine ⟨K, inferInstance, inferInstance, e, hK, ?_, ?_, hmap⟩
  · rw [hP1, h2, hpar false]
    exact Subgroup.map_map _ _ _
  · rw [hP2, h3, hpar true]
    exact Subgroup.map_map _ _ _

section Model

variable {K : Type} [Field K]

abbrev burnsideF411_l3e (i : Fin 3) : Fin 3 → K := Pi.single i 1

@[expose] def burnsideF411_l3dt (t : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(t : K), 1, ((t⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp⟩

theorem burnsideF411_coe_l3dt (t : Kˣ) :
    ((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(t : K), 1, ((t⁻¹ : Kˣ) : K)] := rfl

theorem burnsideF411_l3dt_e0 (t : Kˣ) :
    ((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      burnsideF411_l3e 0 = (t : K) • burnsideF411_l3e 0 := by
  rw [burnsideF411_coe_l3dt]
  funext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]

theorem burnsideF411_l3dt_e1 (t : Kˣ) :
    ((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      burnsideF411_l3e 1 = burnsideF411_l3e 1 := by
  rw [burnsideF411_coe_l3dt]
  funext i
  fin_cases i <;> simp [Matrix.mulVec_diagonal]

theorem burnsideF411_l3dt_apply (t : Kˣ) (v : Fin 3 → K) :
    (((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 =
        v 1 ∧
      (((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 =
        ((t⁻¹ : Kˣ) : K) * v 2 := by
  rw [burnsideF411_coe_l3dt]
  simp [Matrix.mulVec_diagonal]

theorem burnsideF411_map_l3dt (σ : K ≃+* K) (t : Kˣ) :
    SpecialLinearGroup.map σ.toRingHom (burnsideF411_l3dt t) =
      burnsideF411_l3dt (Units.map σ.toRingHom.toMonoidHom t) := by
  ext i j
  change ((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map
    σ.toRingHom i j = _
  rw [burnsideF411_coe_l3dt, burnsideF411_coe_l3dt, Matrix.diagonal_map (map_zero _)]
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideF411_unitri_e0 {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K) :
    (u : Matrix (Fin 3) (Fin 3) K) *ᵥ burnsideF411_l3e 0 = burnsideF411_l3e 0 := by
  obtain ⟨h1, h2⟩ := hu
  have h10 : (u : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := h1 1 0 (by decide)
  have h20 : (u : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := h1 2 0 (by decide)
  rw [Matrix.mulVec_single_one]
  funext i
  fin_cases i <;> simp [h10, h20, h2 0]

theorem burnsideF411_unitri_apply_one {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) {v : Fin 3 → K} (hv : v 2 = 0) :
    ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 = v 1 := by
  obtain ⟨h1, h2⟩ := hu
  have h10 : (u : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := h1 1 0 (by decide)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h2 1, hv]

theorem burnsideF411_coordImage_flagSpace (σ : K ≃+* K) (i : ℕ) :
    coordImage σ (flagSpace 3 K i) = flagSpace 3 K i := by
  ext v
  rw [mem_coordImage, mem_flagSpace, mem_flagSpace]
  simp

theorem burnsideF411_l3_vectors :
    burnsideF411_l3e (K := K) 0 ∈ flagSpace 3 K 1 ∧ burnsideF411_l3e (K := K) 1 ∈ flagSpace 3 K 2 ∧
      burnsideF411_l3e (K := K) 1 ∉ flagSpace 3 K 1 ∧
      burnsideF411_l3e (K := K) 0 ∉ dotOrth (flagSpace 3 K 1) ∧
      burnsideF411_l3e (K := K) 0 ∉ dotOrth (flagSpace 3 K 2) ∧
      burnsideF411_l3e (K := K) 1 ∈ dotOrth (flagSpace 3 K 1) ∧
      burnsideF411_l3e (K := K) 2 ∈ dotOrth (flagSpace 3 K 2) ∧
      flagSpace 3 K 1 ≤ flagSpace 3 K 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_flagSpace]
    intro j hj
    fin_cases j <;> simp_all
  · rw [mem_flagSpace]
    intro j hj
    fin_cases j <;> simp_all
  · rw [mem_flagSpace]
    intro h
    have := h 1 le_rfl
    simp at this
  · rw [mem_dotOrth]
    intro h
    have := h _ (by rw [mem_flagSpace]; intro j hj; fin_cases j <;> simp_all :
      burnsideF411_l3e (K := K) 0 ∈ flagSpace 3 K 1)
    simp at this
  · rw [mem_dotOrth]
    intro h
    have := h _ (by rw [mem_flagSpace]; intro j hj; fin_cases j <;> simp_all :
      burnsideF411_l3e (K := K) 0 ∈ flagSpace 3 K 2)
    simp at this
  · rw [mem_dotOrth]
    intro w hw
    have h1 := (mem_flagSpace.mp hw) 1 le_rfl
    have h2 := (mem_flagSpace.mp hw) 2 (by decide)
    simp [dotProduct, Fin.sum_univ_three, h1, h2]
  · rw [mem_dotOrth]
    intro w hw
    have h2 := (mem_flagSpace.mp hw) 2 le_rfl
    simp [dotProduct, Fin.sum_univ_three, h2]
  · intro v hv
    rw [mem_flagSpace] at hv ⊢
    intro j hj
    exact hv j (by omega)

theorem burnsideF411_l3_proper (A : GL (Fin 3) K) (σ : K ≃+* K) {W : Submodule K (Fin 3 → K)}
    {w v : Fin 3 → K} (hw : w ∈ W) (hw0 : w ≠ 0) (hv : v ∉ W) :
    ⊥ < (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) ∧
      (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) < ⊤ := by
  have hAinv : ∀ x, ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨bot_lt_iff_ne_bot.mpr fun hbot => ?_, lt_top_iff_ne_top.mpr fun htop => ?_⟩
  · have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun i => σ (w i)) ∈
        (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) :=
      ⟨_, coord_mem_coordImage hw, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply hw0
    have h1 := hAinv (fun i => σ (w i))
    rw [hmem, Matrix.mulVec_zero] at h1
    funext i
    have := congrFun h1 i
    simpa using this.symm
  · have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ (fun i => σ (v i)) ∈
        (coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨x, hx, hxe⟩ := hmem
    have hx' : x = fun i => σ (v i) := by
      have := congrArg (fun y => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) hxe
      simp only [mulVecLin_apply] at this
      rwa [hAinv, hAinv] at this
    have hx2 : (fun i => σ (v i)) ∈ coordImage σ W := hx' ▸ hx
    rw [mem_coordImage] at hx2
    apply hv
    simpa using hx2

theorem burnsideF411_l3_map_projStab (A : GL (Fin 3) K) (σ : K ≃+* K)
    (W : Submodule K (Fin 3 → K)) :
    (projStabilizer W).map (conjAut 3 K A * fieldAut 3 K σ).toMonoidHom =
        projStabilizer ((coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) ∧
      (projStabilizer W).map (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K).toMonoidHom =
        projStabilizer ((coordImage σ (dotOrth W)).map
          (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) := by
  obtain ⟨-, -, -, -, -, -, hA, hσ, hδ, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  constructor
  · rw [show (conjAut 3 K A * fieldAut 3 K σ).toMonoidHom =
      (conjAut 3 K A).toMonoidHom.comp (fieldAut 3 K σ).toMonoidHom from rfl, ← Subgroup.map_map]
    rw [show (fieldAut 3 K σ).toMonoidHom = ((fieldAut 3 K σ : projectiveSL 3 K →* projectiveSL 3 K))
      from rfl, hσ, show (conjAut 3 K A).toMonoidHom =
        ((conjAut 3 K A : projectiveSL 3 K →* projectiveSL 3 K)) from rfl, hA]
  · rw [show (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K).toMonoidHom =
      (conjAut 3 K A).toMonoidHom.comp ((fieldAut 3 K σ).toMonoidHom.comp
        (dualAut 3 K).toMonoidHom) from rfl, ← Subgroup.map_map, ← Subgroup.map_map]
    rw [show (dualAut 3 K).toMonoidHom = ((dualAut 3 K : projectiveSL 3 K →* projectiveSL 3 K))
      from rfl, hδ, show (fieldAut 3 K σ).toMonoidHom =
        ((fieldAut 3 K σ : projectiveSL 3 K →* projectiveSL 3 K)) from rfl, hσ,
      show (conjAut 3 K A).toMonoidHom = ((conjAut 3 K A : projectiveSL 3 K →* projectiveSL 3 K))
        from rfl, hA]

theorem burnsideF411_l3_projStab_inf :
    projStabilizer (flagSpace 3 K 1) ⊓ projStabilizer (flagSpace 3 K 2) =
      projUpperTriangular 3 K := by
  rw [projStabilizer, projStabilizer, projUpperTriangular,
    ← burnsideF4h_cl_map_inf_of_ker_le _ (by rw [ker_proj]; exact scalars_le_stabilizer _),
    burnsideF4h_cl_sl_stab_inf]

theorem burnsideF411_l3_pCoreOf_projUT [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    pCoreOf p (projUpperTriangular 3 K) = projUnitriangular 3 K := by
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  have hN := normalizer_projUnitriangular (K := K) (n := 3) p
  have hUB : projUnitriangular 3 K ≤ projUpperTriangular 3 K :=
    hN ▸ Subgroup.le_normalizer
  apply le_antisymm
  · have hSB : (SU : Subgroup (projectiveSL 3 K)) ≤ projUpperTriangular 3 K := hSU ▸ hUB
    haveI := CFSG.LieType.BorelTits.pCore_normal p (G := ↥(projUpperTriangular 3 K))
    have hle := (CFSG.LieType.BorelTits.pCore_isPGroup p
      (G := ↥(projUpperTriangular 3 K))).le_sylow_of_normal (SU.subtype hSB)
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hle hx
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf, hSU] at hx'
    exact hx'
  · refine burnsideF411_le_pCoreOf hUB (le_of_eq hN.symm) ?_
    rw [← hSU]
    exact SU.isPGroup'

theorem burnsideF411_l3_proj_dt_mem (t : Kˣ) :
    proj 3 K (burnsideF411_l3dt t) ∈ projUpperTriangular 3 K := by
  refine ⟨burnsideF411_l3dt t, fun i j hij => ?_, rfl⟩
  rw [burnsideF411_coe_l3dt, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]

end Model

section Torus

variable {K : Type} [Field K]

theorem burnsideF411_l3_inner_of_torus [Finite K] {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hK : Nat.card K = p ^ f) (β : MulAut (projectiveSL 3 K)) (k : ℕ) (hβ : β ^ (p ^ k) = 1)
    (h1 : (projStabilizer (flagSpace 3 K 1)).map β.toMonoidHom = projStabilizer (flagSpace 3 K 1))
    (h2 : (projStabilizer (flagSpace 3 K 2)).map β.toMonoidHom = projStabilizer (flagSpace 3 K 2))
    (hT : ∀ t : Kˣ, β (proj 3 K (burnsideF411_l3dt t)) * (proj 3 K (burnsideF411_l3dt t))⁻¹ ∈
      projUnitriangular 3 K) :
    ∃ g, β = MulAut.conj g := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := burnsideF4h_cl_charP hK
  obtain ⟨-, hinj, -⟩ := maximal_parabolics (K := K) p (n := 3) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) (by norm_num)).2 β
  obtain ⟨v0F1, v1F2, v1nF1, v0nO1, v0nO2, v1O1, v2O2, hF12⟩ := burnsideF411_l3_vectors (K := K)
  have hne : ∀ i : Fin 3, burnsideF411_l3e (K := K) i ≠ 0 := fun i h0 => by
    have := congrFun h0 i
    simp at this
  have hF2nt : burnsideF411_l3e (K := K) 2 ∉ flagSpace 3 K 2 := by
    rw [mem_flagSpace]
    intro h
    have := h 2 le_rfl
    simp at this
  have hF1 : flagSpace 3 K 1 ∈ {W : Submodule K (Fin 3 → K) | ⊥ < W ∧ W < ⊤} :=
    ⟨bot_lt_iff_ne_bot.mpr fun h => hne 0 (by rw [h] at v0F1; exact (Submodule.mem_bot K).mp v0F1),
      lt_top_iff_ne_top.mpr fun h => v1nF1 (h ▸ Submodule.mem_top)⟩
  have hF2 : flagSpace 3 K 2 ∈ {W : Submodule K (Fin 3 → K) | ⊥ < W ∧ W < ⊤} :=
    ⟨bot_lt_iff_ne_bot.mpr fun h => hne 1 (by rw [h] at v1F2; exact (Submodule.mem_bot K).mp v1F2),
      lt_top_iff_ne_top.mpr fun h => hF2nt (h ▸ Submodule.mem_top)⟩
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hβ h1 h2 hT ⊢
    set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
    have hA : ∀ i, 1 ≤ i → i ≤ 2 →
        (projStabilizer (flagSpace 3 K i)).map (conjAut 3 K A * fieldAut 3 K σ).toMonoidHom =
          projStabilizer (flagSpace 3 K i) →
        flagSpace 3 K i ∈ {W : Submodule K (Fin 3 → K) | ⊥ < W ∧ W < ⊤} →
        (∃ w ∈ flagSpace 3 K i, w ≠ 0) → (∃ v, v ∉ flagSpace 3 K i) →
        (flagSpace 3 K i).map (mulVecLin M) = flagSpace 3 K i := by
      intro i _ _ hi hFi ⟨w, hw, hw0⟩ ⟨v, hv⟩
      rw [(burnsideF411_l3_map_projStab A σ _).1] at hi
      have hpr := burnsideF411_l3_proper A σ hw hw0 hv
      rw [burnsideF411_coordImage_flagSpace] at hpr hi
      exact hinj hpr hFi hi
    have hA1 := hA 1 le_rfl (by norm_num) h1 hF1 ⟨_, v0F1, hne 0⟩ ⟨_, v1nF1⟩
    have hA2 := hA 2 (by norm_num) le_rfl h2 hF2 ⟨_, v1F2, hne 1⟩ ⟨_, hF2nt⟩
    have hMinv : ∀ x, ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (M *ᵥ x) = x :=
      fun x => by
        rw [Matrix.mulVec_mulVec, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
    have hAe0 : M *ᵥ burnsideF411_l3e 0 ∈ flagSpace 3 K 1 := by
      rw [← hA1]
      exact ⟨_, v0F1, rfl⟩
    set α := (M *ᵥ burnsideF411_l3e 0) 0 with hαdef
    have hα : M *ᵥ burnsideF411_l3e 0 = α • burnsideF411_l3e 0 := by
      funext i
      fin_cases i
      · simp [hαdef]
      · simp [(mem_flagSpace.mp hAe0) 1 le_rfl]
      · simp [(mem_flagSpace.mp hAe0) 2 (by decide)]
    have hα0 : α ≠ 0 := by
      intro h0
      apply hne 0
      have := hMinv (burnsideF411_l3e 0)
      rw [hα, h0, zero_smul, Matrix.mulVec_zero] at this
      exact this.symm
    have hAe1 : M *ᵥ burnsideF411_l3e 1 ∈ flagSpace 3 K 2 := by
      rw [← hA2]
      exact ⟨_, v1F2, rfl⟩
    have hAe1_2 : (M *ᵥ burnsideF411_l3e 1) 2 = 0 := (mem_flagSpace.mp hAe1) 2 le_rfl
    have hγ : (M *ᵥ burnsideF411_l3e 1) 1 ≠ 0 := by
      intro h0
      have hmem : M *ᵥ burnsideF411_l3e 1 ∈ flagSpace 3 K 1 := by
        rw [mem_flagSpace]
        intro j hj
        fin_cases j
        · simp at hj
        · exact h0
        · exact hAe1_2
      rw [← hA1] at hmem
      obtain ⟨w, hw, hwe⟩ := hmem
      have hw' : w = burnsideF411_l3e 1 := by
        have := congrArg (fun y => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y) hwe
        simp only [mulVecLin_apply] at this
        rwa [hMinv, hMinv] at this
      exact v1nF1 (hw' ▸ hw)
    have hσt : ∀ t : Kˣ, σ (t : K) = t := by
      intro t
      have hTt := hT t
      rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj, ← map_inv, ← map_mul] at hTt
      obtain ⟨u, hu, huX⟩ := hTt
      generalize hXdef : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
        (SpecialLinearGroup.map σ.toRingHom (burnsideF411_l3dt t)) = X at huX
      have huX' := (QuotientGroup.eq (s := scalars 3 K)).mp huX
      obtain ⟨c, -, hc⟩ := mem_scalars.mp huX'
      have hXeq : (X : Matrix (Fin 3) (Fin 3) K) = (u : Matrix (Fin 3) (Fin 3) K) *
          Matrix.scalar (Fin 3) (c : K) *
            ((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        obtain ⟨Y, hY, hYc⟩ : ∃ Y : SpecialLinearGroup (Fin 3) K,
            Y = u⁻¹ * (X * (burnsideF411_l3dt t)⁻¹) ∧
              (Y : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (c : K) := ⟨_, rfl, hc⟩
        have e1 : X = u * Y * burnsideF411_l3dt t := by rw [hY]; group
        rw [e1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hYc]
      have hXv : ∀ w, (X : Matrix (Fin 3) (Fin 3) K) *ᵥ (M *ᵥ w) =
          M *ᵥ (((burnsideF411_l3dt (Units.map σ.toRingHom.toMonoidHom t) :
            SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
        intro w
        rw [← hXdef, coe_slConjugation, burnsideF411_map_l3dt, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hMinv]
      have hXu : ∀ w, (X : Matrix (Fin 3) (Fin 3) K) *ᵥ w = (c : K) • ((u : Matrix (Fin 3) (Fin 3) K)
          *ᵥ (((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ w)) := by
        intro w
        have hs : ∀ v : Fin 3 → K, Matrix.scalar (Fin 3) (c : K) *ᵥ v = (c : K) • v := by
          intro v
          funext x
          rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
          rfl
        rw [hXeq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul]
      have e2 := (hXv (burnsideF411_l3e 1)).symm.trans (hXu _)
      rw [burnsideF411_l3dt_e1] at e2
      have e2' := congrFun e2 1
      have hinr : (((burnsideF411_l3dt t : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ (M *ᵥ burnsideF411_l3e 1)) 2 = 0 := by
        rw [(burnsideF411_l3dt_apply t _).2, hAe1_2, mul_zero]
      rw [Pi.smul_apply, smul_eq_mul, burnsideF411_unitri_apply_one hu hinr,
        (burnsideF411_l3dt_apply t _).1] at e2'
      have hc1 : (c : K) = 1 := mul_right_cancel₀ hγ (by rw [one_mul]; exact e2'.symm)
      have e1 := (hXv (burnsideF411_l3e 0)).symm.trans (hXu _)
      rw [burnsideF411_l3dt_e0, Matrix.mulVec_smul, hα, Matrix.mulVec_smul,
        burnsideF411_l3dt_e0, Matrix.mulVec_smul, Matrix.mulVec_smul, burnsideF411_unitri_e0 hu,
        hc1, one_smul, smul_smul] at e1
      have e1' := congrFun e1 0
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, Units.coe_map] at e1'
      have e1'' : σ (t : K) * α = α * t := e1'
      exact mul_right_cancel₀ hα0 (by rw [e1'']; ring)
    have hσ : σ = 1 := by
      refine RingEquiv.ext fun x => ?_
      by_cases hx : x = 0
      · rw [hx, map_zero, map_zero]
      · exact hσt (Units.mk0 x hx)
    rw [hσ, map_one, mul_one] at hβ ⊢
    have hcop : Nat.Coprime (p ^ k) 3 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_three).mpr hp3)
    obtain ⟨g, hg⟩ := mem_range_conj_of_mem_linearAutGroup_of_coprime
      (conjAut_mem_linearAutGroup A) hcop hβ
    exact ⟨g, hg.symm⟩
  ·
    exfalso
    rw [pow_one] at h1 h2
    rw [(burnsideF411_l3_map_projStab A σ _).2] at h1 h2
    have hW1 := hinj (burnsideF411_l3_proper A σ v1O1 (hne 1) v0nO1) hF1 h1
    have hW2 := hinj (burnsideF411_l3_proper A σ v2O2 (hne 2) v0nO2) hF2 h2
    have hle : dotOrth (flagSpace 3 K 2) ≤ dotOrth (flagSpace 3 K 1) := fun v hv =>
      mem_dotOrth.mpr fun w hw => mem_dotOrth.mp hv w (hF12 hw)
    have hle' : (coordImage σ (dotOrth (flagSpace 3 K 2))).map
        (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) ≤
        (coordImage σ (dotOrth (flagSpace 3 K 1))).map
          (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) :=
      Submodule.map_mono fun v hv => mem_coordImage.mpr (hle (mem_coordImage.mp hv))
    rw [hW1, hW2] at hle'
    exact v1nF1 (hle' v1F2)

end Torus

theorem burnsideF411_key_L3 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) (hp3 : p ≠ 3) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ (p ^ k) = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr k hrk hcomm
  haveI : Finite E := hyp.finite
  haveI := hyp.normal
  have hp : p.Prime := hyp.model.1
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, e, hK, hG1, hG2, hP⟩ := burnsideF411_l3_chart hyp
  haveI : CharP K p := burnsideF4h_cl_charP hK
  set Ψ : projectiveSL 3 K →* E := Gp.subtype.comp e.toMonoidHom with hΨdef
  have hΨ : Function.Injective Ψ := Gp.subtype_injective.comp e.injective
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (projUpperTriangular 3 K).map Ψ := by
    rw [← hP.2.2.1, hG1, hG2, ← Subgroup.map_inf_eq _ _ Ψ hΨ, burnsideF411_l3_projStab_inf]
  have hU : pCoreOf p (Gp ⊓ (M₁ ⊓ M₂)) = (projUnitriangular 3 K).map Ψ := by
    rw [hGB, burnsideF411_pCoreOf_map_injective hΨ, burnsideF411_l3_pCoreOf_projUT]
  let β : MulAut (projectiveSL 3 K) := MulAut.congr e.symm (MulAut.conjNormal r)
  have hβΨ : ∀ x, Ψ (β x) = r * Ψ x * r⁻¹ := by
    intro x
    show ((e (e.symm (MulAut.conjNormal r (e x))) : ↥Gp) : E) = r * ((e x : ↥Gp) : E) * r⁻¹
    rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
  have hβcomp : Ψ.comp β.toMonoidHom = (MulAut.conj r).toMonoidHom.comp Ψ :=
    MonoidHom.ext fun x => (hβΨ x).trans (by rw [MonoidHom.comp_apply]; rfl)
  have hβk : β ^ (p ^ k) = 1 := by
    have h1 : (MulAut.conjNormal r : MulAut ↥Gp) ^ (p ^ k) = 1 := by
      rw [← map_pow, hrk, map_one]
    show (MulAut.congr e.symm (MulAut.conjNormal r)) ^ (p ^ k) = 1
    rw [← map_pow, h1, map_one]
  have hmapβ : ∀ X : Subgroup (projectiveSL 3 K), r ∈ Subgroup.normalizer
      ((X.map Ψ : Subgroup E) : Set E) → X.map β.toMonoidHom = X := by
    intro X hX
    apply Subgroup.map_injective hΨ
    rw [Subgroup.map_map, hβcomp, ← Subgroup.map_map, burnsideF411_map_conj_eq hX]
  have hr1 : r ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) := by
    rw [inf_comm]
    exact burnsideF411_le_normalizer_inf hyp.normal M₁ hr.1
  have hr2 : r ∈ Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) := by
    rw [inf_comm]
    exact burnsideF411_le_normalizer_inf hyp.normal M₂ hr.2
  have h1 : (projStabilizer (flagSpace 3 K 1)).map β.toMonoidHom =
      projStabilizer (flagSpace 3 K 1) := by
    refine hmapβ _ ?_
    rw [← hG1]
    exact hr1
  have h2 : (projStabilizer (flagSpace 3 K 2)).map β.toMonoidHom =
      projStabilizer (flagSpace 3 K 2) := by
    refine hmapβ _ ?_
    rw [← hG2]
    exact hr2
  have hT : ∀ t : Kˣ, β (proj 3 K (burnsideF411_l3dt t)) * (proj 3 K (burnsideF411_l3dt t))⁻¹ ∈
      projUnitriangular 3 K := by
    intro t
    set h := proj 3 K (burnsideF411_l3dt t) with hh
    have hb : Ψ h ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hGB]
      exact ⟨h, burnsideF411_l3_proj_dt_mem t, rfl⟩
    have hc := hcomm (Ψ h) hb
    rw [hU] at hc
    have e1 : Ψ (β h * h⁻¹) = r * Ψ h * r⁻¹ * (Ψ h)⁻¹ := by rw [map_mul, map_inv, hβΨ]
    rw [← e1] at hc
    exact (Subgroup.mem_map_iff_mem hΨ).mp hc
  obtain ⟨g, hg⟩ := burnsideF411_l3_inner_of_torus hp hp3 hK β k hβk h1 h2 hT
  have hcent : (Ψ g)⁻¹ * r ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    have hyx : y = Ψ x := by
      show y = ((e x : ↥Gp) : E)
      rw [hx]
    have h3 : Ψ (β x) = Ψ (g * x * g⁻¹) := by rw [hg]; rfl
    rw [hβΨ, map_mul, map_mul, map_inv] at h3
    rw [hyx]
    calc Ψ x * ((Ψ g)⁻¹ * r) = (Ψ g)⁻¹ * (Ψ g * Ψ x * (Ψ g)⁻¹) * r := by group
      _ = (Ψ g)⁻¹ * (r * Ψ x * r⁻¹) * r := by rw [← h3]
      _ = (Ψ g)⁻¹ * r * Ψ x := by group
  rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hcent
  have hrg : r = Ψ g := by
    have := congrArg (fun z => Ψ g * z) hcent
    simpa using this
  rw [hrg]
  exact (e g).2

theorem burnsideF411_l3_pCoreOf_eq {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) (hp3 : p ≠ 3) :
    pCoreOf p M₁ = pCoreOf p (Gp ⊓ M₁) ∧ pCoreOf p M₂ = pCoreOf p (Gp ⊓ M₂) := by
  haveI : Finite E := hyp.finite
  haveI : Fact p.Prime := ⟨hyp.model.1⟩
  obtain ⟨K, _, _, e, hK, hG1, hG2, hP⟩ := burnsideF411_l3_chart hyp
  obtain ⟨T, hTp, hTi, hT⟩ := burnsideF411_exists_sylow_inf hyp.normal hyp.split hP
  exact ⟨burnsideF411_pCoreOf_eq_of_key hyp.normal hTp hTi hT (burnsideF411_key_L3 hyp hp3)
      inf_le_left,
    burnsideF411_pCoreOf_eq_of_key hyp.normal hTp hTi hT (burnsideF411_key_L3 hyp hp3)
      inf_le_right⟩

end CFSG.ASVolI
