module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.LieType.Chevalley.E6GraphRadicalDetector
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Timmesfeld.LieEmbed.SpF4
public import CFSG.LieType.Classical.SteinbergBLSymplectic
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart21
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussBlocks
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.E6GraphRadicalCoords
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.CurtisTits.Symplectic
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.C3Exact

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
    CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld.LieEmbed

noncomputable def f4C3Coeff (α β : Fin (Tag.rank .F4) → ℤ) : ℕ × ℕ → ℤ
  | (1, 1) => (stringNorm (τ := .F4) α β : ℤ)
  | _ => 1

theorem f4C3Coeff_one_one (α β : Fin (Tag.rank .F4) → ℤ) :
    f4C3Coeff α β (1, 1) = (stringNorm (τ := .F4) α β : ℤ) := rfl

theorem f4C3Coeff_one_two (α β : Fin (Tag.rank .F4) → ℤ) : f4C3Coeff α β (1, 2) = 1 := rfl

theorem f4C3Coeff_two_one (α β : Fin (Tag.rank .F4) → ℤ) : f4C3Coeff α β (2, 1) = 1 := rfl

theorem cast_spCommC_eq_f4C3Coeff
    {K : Type} [Field K] [CharP K 2]
    {α β : Fin 3 → ℤ} (hα : α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅)
    (hβ : β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅) (_hne : α ≠ β)
    (hαβ : α + β ≠ 0) {p : ℕ × ℕ} (hp : p ∈ pairs₀)
    (hr : p.1 • α + p.2 • β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅) :
    (Sp.commC α β p : K) = (f4C3Coeff (c3ToF4 α) (c3ToF4 β) p : K) := by
  have hα' : CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 α) := isRoot_c3ToF4 hα
  have hβ' : CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 β) := isRoot_c3ToF4 hβ
  simp only [pairs₀, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp only [one_smul] at hr
    by_cases hd : β - α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅
    · have h4 := (sub_mem_roots_iff hα hβ hr).1 hd
      have hd' : CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 β - c3ToF4 α) := by
        rw [← map_sub]
        exact isRoot_c3ToF4 hd
      refine (intCast_eq_zero_of_natAbs (natAbs_commC_one_one_long hα hβ hαβ hr h4)).trans ?_
      rw [f4C3Coeff_one_one, stringNorm, if_pos hd']
      exact (intCast_eq_zero_of_natAbs (by norm_num)).symm
    · have h2 : toStd 3 (α + β) ⬝ᵥ toStd 3 (α + β) = 2 := by
        obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
        rcases dot_stdVec t with h | h
        · rwa [ht] at h
        · exact absurd ((sub_mem_roots_iff hα hβ hr).2 (by rwa [ht] at h)) hd
      have hd' : ¬CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 β - c3ToF4 α) := by
        rw [← map_sub, isRoot_c3ToF4_iff]
        exact hd
      refine (intCast_eq_one_of_natAbs (Sp.natAbs_commC_one_one hα hβ hαβ hr h2)).trans ?_
      rw [f4C3Coeff_one_one, stringNorm, if_neg hd']
      exact (intCast_eq_one_of_natAbs (by norm_num)).symm
  · have hr' : CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 α + 2 • c3ToF4 β) := by
      rw [← map_nsmul, ← map_add]
      simpa only [one_smul] using isRoot_c3ToF4 hr
    refine (intCast_eq_one_of_natAbs (Sp.natAbs_commC_one_two hα hβ hαβ
        (by simpa only [one_smul] using hr))).trans ?_
    rw [f4C3Coeff_one_two]
    exact (intCast_eq_one_of_natAbs (by norm_num)).symm
  · have hr' : CFSG.Blueprint.Chevalley.IsRoot .F4 (2 • c3ToF4 α + c3ToF4 β) := by
      rw [← map_nsmul, ← map_add]
      simpa only [one_smul] using isRoot_c3ToF4 hr
    refine (intCast_eq_one_of_natAbs (natAbs_commC_two_one hα hβ hαβ
        (by simpa only [one_smul] using hr))).trans ?_
    rw [f4C3Coeff_two_one]
    exact (intCast_eq_one_of_natAbs (by norm_num)).symm

section Embedding

open CFSG.LieType.Steinberg

open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

theorem spF4Par_add
    (γ : Fin 3 → ℤ) (c d : K) :
    spF4Par K γ (c + d) = spF4Par K γ c * spF4Par K γ d := by
  by_cases h : CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 γ)
  · change xPar (rootOperatorFamily .F4) (c3ToF4 γ) (c + d) =
      xPar (rootOperatorFamily .F4) (c3ToF4 γ) c * xPar (rootOperatorFamily .F4) (c3ToF4 γ) d
    rw [xPar, dif_pos h, xPar, dif_pos h, xPar, dif_pos h]
    exact (rootOperatorFamily .F4).eltElement_add ⟨c3ToF4 γ, h⟩ c d
  · change xPar (rootOperatorFamily .F4) (c3ToF4 γ) (c + d) =
      xPar (rootOperatorFamily .F4) (c3ToF4 γ) c * xPar (rootOperatorFamily .F4) (c3ToF4 γ) d
    rw [xPar, dif_neg h, xPar, dif_neg h, xPar, dif_neg h, mul_one]

theorem spF4Par_of_not_exact
    {γ : Fin 3 → ℤ}
    (hγ : γ ∉ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅) (c : K) :
    spF4Par K γ c = 1 := by
  change xPar (rootOperatorFamily .F4) (c3ToF4 γ) c = 1
  rw [xPar, dif_neg]
  exact fun h => hγ (isRoot_c3ToF4_iff.1 h)

theorem f4Par_simple_one_ne_one_exact
    (i : Fin (Tag.rank .F4)) :
    (Adjoint.f4Par K (Pi.single i 1) 1 : ↥(adjointGroup .F4 K)) ≠ 1 := by
  intro h
  have h' : (xUnit .F4 K i 1 : ModGL .F4 K) = 1 := by
    have h1 := congrArg (fun x : ↥(adjointGroup .F4 K) => (x : ModGL .F4 K)) h
    have h2 : (rootOperatorFamily .F4).eltUnit K (simpleRoot .F4 i) 1 = 1 := by
      rw [show ((Adjoint.f4Par K (Pi.single i 1) 1 : ↥(adjointGroup .F4 K)) : ModGL .F4 K) =
          (rootOperatorFamily .F4).eltUnit K (simpleRoot .F4 i) 1 from ?_] at h1
      · exact h1
      · rw [Adjoint.f4Par, xPar, dif_pos (isRoot_single .F4 i)]
        rfl
    rwa [← (rootOperatorFamily .F4).eltUnit_simple i 1]
  have h2 : simpleRootSL2 .F4 K i (uSL 1) = simpleRootSL2 .F4 K i 1 := by
    rw [simpleRootSL2_uSL, h', map_one]
  have hinj := CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two
    (CharP.cast_eq_zero K 2) i
  have h3 : (uSL (1 : K) : SL2 K) = 1 := hinj h2
  have h4 : ((uSL (1 : K) : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 = (0 : K) := by
    rw [h3]
    simp
  have h5 : ((uSL (1 : K) : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 = (1 : K) := by
    simp [uSL]
  rw [h5] at h4
  exact one_ne_zero h4

theorem spF4_rels_exact
    (O : CommOrder (Sp.Φ 3 K))
    (hadd : ∀ γ (c d : K), spF4Par K γ (c + d) = spF4Par K γ c * spF4Par K γ d)
    (hcomm : ∀ {α β : Fin 3 → ℤ},
      α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ →
      β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ → α + β ≠ 0 → ∀ c d,
        ⁅spF4Par K α c, spF4Par K β d⁆ =
          ((O.list α β).map fun p => spF4Par K (p.1 • α + p.2 • β)
            ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2)).prod) :
    ∀ r ∈ relA (Sp.Φ 3 K) K ∪ relB (Sp.Φ 3 K) K O Sp.commC,
      FreeGroup.lift (chevEval (spF4Par K)) r = 1 := by
  have hof : ∀ γ (hγ : γ ∈ (Sp.Φ 3 K).roots) (c : K),
      FreeGroup.lift (chevEval (spF4Par K)) (chevOf (Φ := Sp.Φ 3 K) γ c) = spF4Par K γ c := by
    intro γ hγ c
    rw [chevOf, dite_eq_left hγ, FreeGroup.lift_apply_of]
    rfl
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · rw [map_mul, map_mul, map_inv, hof γ hγ, hof γ hγ, hof γ hγ, mul_inv_eq_one]
    exact (hadd γ c d).symm
  · rw [map_mul, map_inv, map_commutatorElement, hof α hα, hof β hβ, map_list_prod,
      List.map_map, hcomm hα hβ hαβ c d, mul_inv_eq_one]
    refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
    rw [Function.comp_apply, hof _ ((O.mem_iff α hα β hβ hαβ p).1 hp).2.2]

variable [Finite K]

theorem exists_hom_spToF4_exact
    (O : CommOrder (Sp.Φ 3 K))
    (hadd : ∀ γ (c d : K), spF4Par K γ (c + d) = spF4Par K γ c * spF4Par K γ d)
    (hcomm : ∀ {α β : Fin 3 → ℤ},
      α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ →
      β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ → α + β ≠ 0 → ∀ c d,
        ⁅spF4Par K α c, spF4Par K β d⁆ =
          ((O.list α β).map fun p => spF4Par K (p.1 • α + p.2 • β)
            ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2)).prod) :
    ∃ ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K),
      ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c := by
  obtain ⟨hrel, hbij⟩ :=
    (Sp.presentationB (n := 3) (F := K) (by norm_num) O).2 Sp.commC (Sp.commutatorFormula O)
  set e := MulEquiv.ofBijective (PresentedGroup.toGroup hrel) hbij
  refine ⟨(PresentedGroup.toGroup (spF4_rels_exact O hadd hcomm)).comp e.symm.toMonoidHom,
    fun γ c => ?_⟩
  by_cases hγ : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅
  · have he : e.symm (Sp.x 3 K γ c) = PresentedGroup.of (⟨γ, hγ⟩, c) := by
      rw [MulEquiv.symm_apply_eq]
      change Sp.x 3 K γ c = PresentedGroup.toGroup hrel (PresentedGroup.of (⟨γ, hγ⟩, c))
      rw [PresentedGroup.toGroup.of]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, PresentedGroup.toGroup.of]
    rfl
  · rw [Sp.x_of_not (fun ⟨r, hr⟩ => hγ (SpExtras.mem_roots_of_stdVec hr)), map_one]
    exact (spF4Par_of_not_exact hγ c).symm

theorem injective_of_pinned_formula
    {ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K)}
    (_hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c)
    (hnt : ∃ g, ι g ≠ 1) : Function.Injective ι := by
  have hcard : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : CFSG.IsQuasisimple (StatedSp 3 K) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num) (by
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 ∨ 4 ≤ Nat.card K by omega) with h | h | h
    · exact Or.inr (Or.inr ⟨h, le_rfl⟩)
    · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
    · exact Or.inl (Or.inr h))
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc := CurtisTits.ker_le_center_of_isQuasisimple hq hnt hg
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hc
  exact hc

theorem f4C3_exists_pinned_of_comm
    (O : CommOrder (Sp.Φ 3 K))
    (hadd : ∀ γ (c d : K), spF4Par K γ (c + d) = spF4Par K γ c * spF4Par K γ d)
    (hcomm : ∀ {α β : Fin 3 → ℤ},
      α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ →
      β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ → α + β ≠ 0 → ∀ c d,
        ⁅spF4Par K α c, spF4Par K β d⁆ =
          ((O.list α β).map fun p => spF4Par K (p.1 • α + p.2 • β)
            ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2)).prod)
    (hroot : (Adjoint.f4Par K (Pi.single (⟨3, by decide⟩ : Fin (Tag.rank .F4)) 1) 1 :
      ↥(adjointGroup .F4 K)) ≠ 1) :
    ∃ ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K), Function.Injective ι ∧
      ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c := by
  obtain ⟨ι, hι⟩ := exists_hom_spToF4_exact O hadd hcomm
  have hc3 : c3ToF4 (Pi.single 0 1) = Pi.single (⟨3, by decide⟩ : Fin (Tag.rank .F4)) 1 := by
    funext j; fin_cases j <;> rfl
  have hnt : ∃ g, ι g ≠ 1 := ⟨Sp.x 3 K (Pi.single 0 1) 1, by
    rw [hι, hc3]; exact hroot⟩
  exact ⟨ι, injective_of_pinned_formula hι hnt, hι⟩

theorem f4C3_exists_pinned_of_comm_only
    (O : CommOrder (Sp.Φ 3 K))
    (hcomm : ∀ {α β : Fin 3 → ℤ},
      α ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ →
      β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC 3) ∅ → α + β ≠ 0 → ∀ c d,
        ⁅spF4Par K α c, spF4Par K β d⁆ =
          ((O.list α β).map fun p => spF4Par K (p.1 • α + p.2 • β)
            ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2)).prod) :
    ∃ ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K), Function.Injective ι ∧
      ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c :=
  f4C3_exists_pinned_of_comm O (fun γ c d => spF4Par_add γ c d) hcomm
    (f4Par_simple_one_ne_one_exact (⟨3, by decide⟩ : Fin (Tag.rank .F4)))

end Embedding

end CFSG.StandardType.F4ExplicitPos.C3Exact

end

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley IsNilpotent

open scoped Nat

open scoped commutatorElement

variable {τ : Tag}

theorem nsmul_add_nsmul_ne_zero_without117 {α β : Fin τ.rank → ℤ} (h : LinIndepPair α β) {i j : ℕ}
    (hij : i ≠ 0 ∨ j ≠ 0) : i • α + j • β ≠ 0 := by
  intro h0
  have := h i j (by rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h0)
  omega

theorem ne_neg_of_linIndep_without117 {α β : Fin τ.rank → ℤ} (h : LinIndepPair α β) {i j k l : ℕ}
    (hij : i + k ≠ 0 ∨ j + l ≠ 0) : i • α + j • β ≠ -(k • α + l • β) := by
  intro h0
  apply nsmul_add_nsmul_ne_zero_without117 h hij
  rw [add_nsmul, add_nsmul, eq_neg_iff_add_eq_zero] at *
  rw [← h0]
  abel

theorem ne_neg_of_linIndep'_without117 {α β u v : Fin τ.rank → ℤ} (h : LinIndepPair α β)
    {i j k l : ℕ} (hij : i + k ≠ 0 ∨ j + l ≠ 0) (hu : u = i • α + j • β)
    (hv : v = k • α + l • β) : u ≠ -v := by
  rw [hu, hv]
  exact ne_neg_of_linIndep_without117 h hij

namespace RootOperatorFamily'

variable {D : AdjData τ}

open _root_.Classical in
noncomputable def bracketCoeff_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (β γ : Root τ) : ℤ := by
  classical
  exact if h : γ.1 ≠ -β.1 ∧ IsRoot τ (β.1 + γ.1) then
    ((bracket_without117 F hD β γ h.1).1 h.2).choose
  else 0

theorem bracketCoeff_natAbs_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) {β γ : Root τ} (hγ : γ.1 ≠ -β.1)
    (h : IsRoot τ (β.1 + γ.1)) :
    (bracketCoeff_without117 F hD β γ).natAbs = stringNorm β.1 γ.1 := by
  rw [bracketCoeff_without117, dite_eq_left ⟨hγ, h⟩]
  exact ((bracket_without117 F hD β γ hγ).1 h).choose_spec.1

theorem bracket_eq_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) {β γ : Root τ} (hγ : γ.1 ≠ -β.1)
    (h : IsRoot τ (β.1 + γ.1)) (R : Type) [CommRing R] :
    F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 =
      (bracketCoeff_without117 F hD β γ : R) • F.D R ⟨β.1 + γ.1, h⟩ 1 := by
  rw [bracketCoeff_without117, dite_eq_left ⟨hγ, h⟩]
  exact ((bracket_without117 F hD β γ hγ).1 h).choose_spec.2 R

theorem bracket_eq_zero_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) {β γ : Root τ} (hγ : γ.1 ≠ -β.1)
    (h : ¬IsRoot τ (β.1 + γ.1)) (R : Type) [CommRing R] :
    F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 = 0 :=
  (bracket_without117 F hD β γ hγ).2 h R

end RootOperatorFamily'
end CFSG.LieType.Steinberg.Adjoint
end

end
