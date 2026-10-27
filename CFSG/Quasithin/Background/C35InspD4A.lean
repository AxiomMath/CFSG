module

public import CFSG.Quasithin.Background.C35InspG2A
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C35InspL45C
public import CFSG.Quasithin.Background.C35InspNat
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.SmithB51LnAut
public import CFSG.Sporadic.J4.QTOutChar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique Matrix CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

section Gen

variable {F : Type} [Field F]

theorem HSL_eq_uSL_WSL (t : Fˣ) :
    HSL t = uSL (t : F) * (WSL * uSL ((t⁻¹ : Fˣ) : F) * WSL⁻¹) * uSL (t : F) * WSL⁻¹ := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, coe_uSL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

theorem SL2_induction_uW {p : SL2 F → Prop} (hmul : ∀ g g', p g → p g' → p (g * g'))
    (hinv : ∀ g, p g → p g⁻¹) (hu : ∀ s, p (uSL s)) (hW : p WSL) (g : SL2 F) : p g := by
  refine SL2_induction hmul hu (fun t => ?_) hW g
  rw [HSL_eq_uSL_WSL]
  exact hmul _ _ (hmul _ _ (hmul _ _ (hu _) (hmul _ _ (hmul _ _ hW (hu _)) (hinv _ hW))) (hu _))
    (hinv _ hW)

theorem uSL_mulVec (c : F) (w : Fin 2 → F) :
    ((uSL c : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = ![w 0 + c * w 1, w 1] := by
  rw [coe_uSL]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem WSL_mulVec_of_neg (hneg : ∀ x : F, -x = x) (w : Fin 2 → F) :
    ((WSL : SL2 F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = ![w 1, w 0] := by
  rw [coe_WSL]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hneg]

end Gen

section D4

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K
local notation "E₁" => (orbitField TwistTag.D4 K τ₀ fa1)

include hσ3 in
theorem centerQ1_d4
    {z : GL} (hzQ : z ∈ Q1 σ) (hzC : z ∈ Subgroup.centralizer (Q1 σ : Set GL)) :
    ∃ e f : trialityFixedField K τ₀, z = ox₅ σ e * ox₆ σ f := by
  obtain ⟨a, c, d, e, f, rfl⟩ := (mem_radical_a1_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q1 σ,
      ⁅ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hac : ∀ t : K, trialityTrace K τ₀ hσ3 (a * t) = 0 ∧ trialityTrace K τ₀ hσ3 (c * t) = 0 := by
    intro t
    have h1 := hcent _ (ox₄_mem_Q1 σ hσ3 t)
    have e1 : ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * (ox₁ σ a * ox₃ σ c) * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _)] at h1
    have e2 : ⁅ox₁ σ a * ox₃ σ c, ox₄ σ t⁆ =
        ox₁ σ a * ⁅ox₃ σ c, ox₄ σ t⁆ * (ox₁ σ a)⁻¹ * ⁅ox₁ σ a, ox₄ σ t⁆ := by
      simp only [commutatorElement_def]; group
    rw [e2, rel34 σ hσ3, rel14 σ hσ3, (comm16 σ hσ3 a _).eq, mul_inv_cancel_right] at h1
    have h2 : ox₅ σ (trialityTrace K τ₀ hσ3 (a * t)) * ox₆ σ (trialityTrace K τ₀ hσ3 (c * t)) =
        1 := by
      rw [(comm56 σ hσ3 _ _).eq]; exact h1
    obtain ⟨h5, h6⟩ := five_six_eq_one σ hσ3 h2
    exact ⟨h5, h6⟩
  have ha : a = 0 := trace_nondeg σ hσ3 a (fun t => (hac t).1)
  have hc : c = 0 := trace_nondeg σ hσ3 c (fun t => (hac t).2)
  subst ha
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₁_mem_Q1 σ hσ3 s)
    have e1 : ox₁ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by
      rw [ox₁_zero σ hσ3, ox₃_zero σ hσ3]; group
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₁ σ s) :=
      (comm15 σ hσ3 s e).symm.mul_left (comm16 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₁ σ s⁆ = (ox₅ σ (trialityTrace K τ₀ hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel14 σ hσ3]
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), hinv] at h1
    exact ox₅_inj σ hσ3 ((inv_eq_one.1 h1).trans (ox₅_zero σ hσ3).symm)
  subst hd
  exact ⟨e, f, by rw [ox₁_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3]; simp⟩

theorem levi_proj_d4
    (a : Fin TwistTag.D4.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K τ₀))
    (hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ a), s.card = 4) :
    ∃ R : SL2 ↥(orbitField TwistTag.D4 K τ₀ a) →* GL,
      (∀ c, R (uSL c) = orbitX TwistTag.D4 K τ₀ a c) ∧
      R WSL = canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∧
      Function.Injective R ∧
      ∃ g : ↥(CFSG.Quasithin.perfectCore (graphFixedParabolic TwistTag.D4 K τ₀ {a})) →*
          ↥R.range, Function.Surjective g ∧
        ∀ x, ((g x : ↥R.range) : GL)⁻¹ * (x : GL) ∈
          graphFixedSimpleComplement TwistTag.D4 K τ₀ a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite GL := finite_modGL
  obtain ⟨R, hRx, hRy, hRH, hRW, hRn, hrange, -, hker, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K τ₀ a
  obtain ⟨hVU, hVnormal, hmul, -, -, -, -, hnV, -, himage⟩ :=
    fixed_simple_positive_complement TwistTag.D4 K σ a
  have hUnormV : graphFixedPosUnipotent TwistTag.D4 K τ₀ ≤
      Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mp hVnormal
  have hX : ∀ c, (orbitX TwistTag.D4 K τ₀ a c : GL) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
    fun c => orbitX_mem_graphFixedPosUnipotent TwistTag.D4 τ₀ a c
  have hUN := graphFixedPosUnipotent_le_fixedPosWeylGroup (t := TwistTag.D4) (K := K) (σ := τ₀) a
  have hRN : R.range ≤ fixedPosWeylGroup TwistTag.D4 K τ₀ a := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hUN (hX c)
    · exact orbitY_mem_fixedPosWeylGroup a c
  have hRnorm : R.range ≤
      Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL) := by
    rw [hrange]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hUnormV (hX c)
    · have hy : (orbitY TwistTag.D4 K τ₀ a c : GL) ∈
          (fun g => canonicalRep (coxeterSystem TwistTag.D4.tag) K
              (TwistTag.D4.orbitReflection a) * g *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹) ''
            Set.range (fun c : orbitField TwistTag.D4 K τ₀ a =>
              (orbitX TwistTag.D4 K τ₀ a c : GL)) := by
        rw [himage]
        exact ⟨c, rfl⟩
      obtain ⟨_, ⟨c', rfl⟩, hyc⟩ := hy
      show (orbitY TwistTag.D4 K τ₀ a c : GL) ∈
        Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL)
      rw [← hyc]
      exact mul_mem (mul_mem hnV (hUnormV (hX c'))) (inv_mem hnV)
  have hNnorm : fixedPosWeylGroup TwistTag.D4 K τ₀ a ≤
      Subgroup.normalizer (graphFixedSimpleComplement TwistTag.D4 K τ₀ a : Set GL) :=
    sup_le hUnormV ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hnV))
  have hsup : graphFixedSimpleComplement TwistTag.D4 K τ₀ a ⊔ R.range =
      fixedPosWeylGroup TwistTag.D4 K τ₀ a := by
    refine le_antisymm (sup_le (hVU.trans hUN) hRN) ?_
    refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ?_))
    · have hu' : u ∈ (graphFixedPosUnipotent TwistTag.D4 K τ₀ : Set GL) := hu
      rw [hmul] at hu'
      obtain ⟨v, hv, _, ⟨c, rfl⟩, rfl⟩ := hu'
      exact mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨uSL c, hRx c⟩)
    · exact Subgroup.mem_sup_right ⟨WSL, by rw [hRW, hRn]⟩
  have hRinj : Function.Injective R := fixed_rankOne_injective σ a hker
  have hsimpleSL : IsSimpleGroup (SL2 ↥(orbitField TwistTag.D4 K τ₀ a)) := sl2_isSimple hL4
  have hperfSL : Group.IsPerfect (SL2 ↥(orbitField TwistTag.D4 K τ₀ a)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  have hsimpleM : IsSimpleGroup ↥R.range :=
    (MonoidHom.ofInjective hRinj).symm.isSimpleGroup
  have hMperf : ⁅R.range, R.range⁆ = R.range := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range R)
  have hV2 : IsPGroup 2 ↥(graphFixedSimpleComplement TwistTag.D4 K τ₀ a) :=
    IsPGroup.of_injective hU (Subgroup.inclusion hVU) (Subgroup.inclusion_injective hVU)
  have hVM : graphFixedSimpleComplement TwistTag.D4 K τ₀ a ⊓ R.range = ⊥ :=
    inf_eq_bot_of_simple hRnorm hV2 hMperf
  have hMP : R.range ≤ graphFixedParabolic TwistTag.D4 K τ₀ {a} :=
    hRN.trans (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective a)
  obtain ⟨g, hg, hk⟩ := exists_levi_proj (hVU.trans hUN) hNnorm hVM hsup le_rfl hMperf
    (CFSG.Quasithin.perfectCore_le _)
  have hpc : CFSG.Quasithin.perfectCore (graphFixedParabolic TwistTag.D4 K τ₀ {a}) =
      CFSG.Quasithin.perfectCore (fixedPosWeylGroup TwistTag.D4 K τ₀ a) :=
    fixed_perfectCore_eq σ a
  refine ⟨R, hRx, by rw [hRW, hRn], hRinj, g.comp (MulEquiv.subgroupCongr hpc).toMonoidHom,
    hg.comp (MulEquiv.subgroupCongr hpc).surjective, fun x => ?_⟩
  have h2 := hk (MulEquiv.subgroupCongr hpc x)
  rwa [MulEquiv.subgroupCongr_apply] at h2

omit [Finite K] [CharP K 2] in
theorem orbitField_fa1_eq :
    orbitField TwistTag.D4 K τ₀ fa1 = trialityFixedField K τ₀ := by
  ext c
  rw [mem_orbitField, orbit_card_fa1, pow_one, mem_trialityFixedField]

@[expose] def toK
    (c : ↥(orbitField TwistTag.D4 K τ₀ fa1)) : ↥(trialityFixedField K τ₀) :=
  ⟨c, (orbitField_fa1_eq σ).le c.2⟩

include hσ3 in
theorem d4_action
    (R : SL2 ↥(orbitField TwistTag.D4 K τ₀ fa1) →* GL)
    (hu : ∀ c, R (uSL c) = orbitX TwistTag.D4 K τ₀ fa1 c)
    (hW : R WSL = canonicalRep (coxeterSystem TwistTag.D4.tag) K
      (TwistTag.D4.orbitReflection fa1))
    (D : SL2 ↥(orbitField TwistTag.D4 K τ₀ fa1)) (w : Fin 2 → ↥(orbitField TwistTag.D4 K τ₀ fa1)) :
    R D * (ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0))) * (R D)⁻¹ =
      ox₅ σ (toK σ (((D : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w) 1)) *
        ox₆ σ (toK σ (((D : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w) 0)) := by
  revert w
  refine SL2_induction_uW (p := fun D => ∀ w : Fin 2 → ↥(orbitField TwistTag.D4 K τ₀ fa1),
    R D * (ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0))) * (R D)⁻¹ =
      ox₅ σ (toK σ (((D : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w) 1)) *
        ox₆ σ (toK σ (((D : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w) 0))) ?_ ?_ ?_ ?_ D
  · intro g g' hg hg' w
    have e : R (g * g') * (ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0))) * (R (g * g'))⁻¹ =
        R g * (R g' * (ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0))) * (R g')⁻¹) * (R g)⁻¹ := by
      rw [map_mul]
      group
    rw [e, hg', hg]
    have hm : ((g * g' : SL2 E₁) : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w =
        (g : Matrix (Fin 2) (Fin 2) E₁) *ᵥ ((g' : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [hm]
  · intro g hg w
    have h1 := hg (((g⁻¹ : SL2 E₁) : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w)
    have hm : (g : Matrix (Fin 2) (Fin 2) E₁) *ᵥ
        (((g⁻¹ : SL2 E₁) : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec]
      have h : (g : Matrix (Fin 2) (Fin 2) E₁) * ((g⁻¹ : SL2 E₁) : Matrix (Fin 2) (Fin 2) E₁) = 1 :=
        congrArg (fun z : SL2 E₁ => (z : Matrix (Fin 2) (Fin 2) E₁)) (mul_inv_cancel g)
      rw [h, Matrix.one_mulVec]
    rw [hm] at h1
    rw [map_inv, inv_inv, ← h1]
    group
  · intro c w
    rw [hu, orbitX_fa1_eq σ c (toK σ c) rfl]
    have h1 : ox₂ σ (toK σ c) * ox₅ σ (toK σ (w 1)) * (ox₂ σ (toK σ c))⁻¹ =
        ox₆ σ (toK σ c * toK σ (w 1)) * ox₅ σ (toK σ (w 1)) := by
      have h := rel25 σ hσ3 (toK σ c) (toK σ (w 1))
      rw [commutatorElement_def] at h
      rw [← h]
      group
    have h2 : ox₂ σ (toK σ c) * ox₆ σ (toK σ (w 0)) * (ox₂ σ (toK σ c))⁻¹ =
        ox₆ σ (toK σ (w 0)) := by
      rw [(comm26 σ hσ3 _ _).eq, mul_inv_cancel_right]
    have h3 : ((uSL c : SL2 E₁) : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w = ![w 0 + c * w 1, w 1] :=
      uSL_mulVec c w
    rw [h3]
    have e1 : ox₂ σ (toK σ c) * (ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0))) *
        (ox₂ σ (toK σ c))⁻¹ =
          (ox₂ σ (toK σ c) * ox₅ σ (toK σ (w 1)) * (ox₂ σ (toK σ c))⁻¹) *
            (ox₂ σ (toK σ c) * ox₆ σ (toK σ (w 0)) * (ox₂ σ (toK σ c))⁻¹) := by
      group
    have e2 : toK σ (w 0 + c * w 1) = toK σ c * toK σ (w 1) + toK σ (w 0) := by
      apply Subtype.ext
      show ((w 0 : K) + (c : K) * (w 1 : K)) = (c : K) * (w 1 : K) + (w 0 : K)
      ring
    rw [e1, h1, h2, show ![w 0 + c * w 1, w 1] 0 = w 0 + c * w 1 from rfl,
      show ![w 0 + c * w 1, w 1] 1 = w 1 from rfl, e2, ox₆_add σ hσ3,
      ← (comm56 σ hσ3 (toK σ (w 1)) (toK σ c * toK σ (w 1))).eq]
    group
  · intro w
    rw [hW]
    have hroot5 : IsRoot TwistTag.D4.tag (trialityRoot 4) := (isRoot_trialityRoot 4 0).1
    have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
    have hw : TwistTag.D4.orbitWord fa1 = [⟨2, by decide⟩] := by decide
    have hr5 : TwistTag.D4.orbitReflection fa1 • trialityRoot 4 = trialityRoot 5 := by
      unfold TwistTag.orbitReflection
      rw [hw, CoxeterSystem.wordProd_singleton, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have hr6 : TwistTag.D4.orbitReflection fa1 • trialityRoot 5 = trialityRoot 4 := by
      unfold TwistTag.orbitReflection
      rw [hw, CoxeterSystem.wordProd_singleton, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    have h5 : ∀ e : ↥(trialityFixedField K τ₀),
        canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1) *
          ox₅ σ e * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
            (TwistTag.D4.orbitReflection fa1))⁻¹ = ox₆ σ e := by
      intro e
      have := canonicalRep_conj_charTwo' (K := K) (TwistTag.D4.orbitReflection fa1) hroot5 (e : K)
      rw [hr5] at this
      exact this
    have h6 : ∀ e : ↥(trialityFixedField K τ₀),
        canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1) *
          ox₆ σ e * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
            (TwistTag.D4.orbitReflection fa1))⁻¹ = ox₅ σ e := by
      intro e
      have := canonicalRep_conj_charTwo' (K := K) (TwistTag.D4.orbitReflection fa1) hroot6 (e : K)
      rw [hr6] at this
      exact this
    have hneg : ∀ x : ↥(orbitField TwistTag.D4 K τ₀ fa1), -x = x := fun x =>
      Subtype.ext (CharTwo.neg_eq (x : K))
    have h3 : ((WSL : SL2 E₁) : Matrix (Fin 2) (Fin 2) E₁) *ᵥ w = ![w 1, w 0] :=
      WSL_mulVec_of_neg hneg w
    rw [h3]
    have e1 : canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1) *
        (ox₅ σ (toK σ (w 1)) * ox₆ σ (toK σ (w 0))) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1))⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1) *
          ox₅ σ (toK σ (w 1)) * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
            (TwistTag.D4.orbitReflection fa1))⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection fa1) *
          ox₆ σ (toK σ (w 0)) * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
            (TwistTag.D4.orbitReflection fa1))⁻¹) := by
      group
    rw [e1, h5, h6, ← (comm56 σ hσ3 (toK σ (w 0)) (toK σ (w 1))).eq]
    rfl

end D4

end CFSG.Quasithin.C35Pf
