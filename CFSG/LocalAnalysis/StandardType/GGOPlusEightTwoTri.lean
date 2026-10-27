module

public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEnd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp CFSG.StandardType.Triality CFSG.StandardType.D4Rank
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Matrix

namespace OPlusEight

section Transport

variable {G H : Type} [Group G] [Group H]

theorem normalizesTwo_map (φ : G ≃* H) {A : Subgroup G}
    (h : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G)) :
    ∃ U : Subgroup H, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A.map φ.toMonoidHom ≤ Subgroup.normalizer (U : Set H) := by
  obtain ⟨U, hU1, hU2, hAU⟩ := h
  refine ⟨U.map φ.toMonoidHom, fun hbot => hU1 ?_, hU2.map _,
    (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map φ.toMonoidHom)⟩
  rwa [Subgroup.map_eq_bot_iff_of_injective _ φ.injective] at hbot

theorem two_of_map (φ : G ≃* H) {A : Subgroup G} {t : G}
    (h : ∃ U : Subgroup H, U ≤ LargeEvenLayer (Subgroup.centralizer ({φ t} : Set H)) ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ A.map φ.toMonoidHom ≤ Subgroup.normalizer (U : Set H)) :
    ∃ U : Subgroup G, U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set G)) ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨U, hUL, hU1, hU2, hAU⟩ := h
  have hC : Subgroup.centralizer ({φ t} : Set H) =
      (Subgroup.centralizer ({t} : Set G)).map φ.toMonoidHom :=
    (TableBSymp.map_centralizer_singleton φ t).symm
  have hlay : LargeEvenLayer (Subgroup.centralizer ({φ t} : Set H)) =
      (LargeEvenLayer (Subgroup.centralizer ({t} : Set G))).map φ.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective _ φ.injective]
  have hkey : ∀ y : G, y ∈ U.map φ.symm.toMonoidHom ↔ φ y ∈ U := by
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hy
      exact ⟨φ y, hy, by simp⟩
  refine ⟨U.map φ.symm.toMonoidHom, ?_, fun hbot => hU1 ?_, hU2.map _, ?_⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [hlay] at hUL
    obtain ⟨z, hz, hzu⟩ := hUL hu
    have : φ.symm u = z := by rw [← hzu]; exact φ.symm_apply_apply z
    show φ.symm u ∈ _
    rw [this]
    exact hz
  · rw [Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective] at hbot
    exact hbot
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hn := Subgroup.mem_normalizer_iff.mp (hAU ⟨a, ha, rfl⟩) (φ y)
    rw [hkey, hkey, map_mul, map_mul, map_inv]
    exact hn

theorem ggEndNodeRootEltAll_of_mulEquiv {p r : ℕ} (φ : G ≃* H)
    (h : GGEndNodeRootEltAll p r G) : GGEndNodeRootEltAll p r H := by
  intro A hA hr h3 hU
  set A₀ := A.map φ.symm.toMonoidHom with hA₀
  have hcard : Nat.card A₀ = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ φ.symm.injective).toEquiv).symm
  have hid : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id H :=
    MonoidHom.ext fun x => φ.apply_symm_apply x
  have hA' : A₀.map φ.toMonoidHom = A := by
    rw [hA₀, Subgroup.map_map, hid, Subgroup.map_id]
  obtain ⟨hex, hall⟩ := h A₀ (TableB.isElemAbelian_map hA _) (hcard ▸ hr) (hcard ▸ h3)
    (normalizesTwo_map φ.symm hU)
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨t, ht⟩ := hex
    have := ht.map φ
    rw [hA'] at this
    exact ⟨φ t, this⟩
  · have ht' := ht.map φ.symm
    obtain ⟨U, hUL, hU1, hU2, hAU⟩ := hall (φ.symm t) ht'
    refine two_of_map φ.symm ?_
    exact ⟨U, hUL, hU1, hU2, hAU⟩

end Transport

section Dim

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_pow_three_eq_one (hK : Nat.card K = 2) : ∀ c : K, c ^ 3 = 1 → c = 1 :=
  OrthRestOdd.eq_one_of_pow_eq_one_of_dvd (n := 1) (p := 3) (by rw [hK, pow_one])
    Nat.prime_three (by norm_num)

theorem omFixDim_eq_finrank_fixedSpace (t : Om8 K) :
    omFixDim t = Module.finrank K (CFSG.RankThree.PartOne.LIT.fixedSpace
      ((CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus 4 K) t :
        CFSG.RankThree.Classical2.orthDerived (coordinateQuadPlus 4 K)) :
          (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) := by
  refine congrArg (fun W : Submodule K (Fin (2 * 4) → K) => Module.finrank K W) ?_
  ext v
  rw [mem_ker_omRep_sub_one, CFSG.RankThree.PartOne.LIT.mem_fixedSpace]
  rfl

theorem exists_twoSubgroup_of_fixDim_six (hK : Nat.card K = 2) {A : Subgroup (Om8 K)}
    (hA : IsElemAbelian 3 A)
    (hU : ∃ U : Subgroup (Om8 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (Om8 K)))
    {t : Om8 K} (htA : t ∈ A) (ht6 : omFixDim t = 6) :
    ∃ U : Subgroup (Om8 K), U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set (Om8 K))) ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set (Om8 K)) := by
  obtain ⟨hnd, -⟩ := regular_coordinateQuadPlus (K := K) (n := 4) (by norm_num)
  set Q := coordinateQuadPlus 4 K with hQ
  let φ : Om8 K ≃* CFSG.RankThree.Classical2.orthDerived Q :=
    CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q
  refine two_of_map φ ?_
  have hpK : ((3 : ℕ) : K) ≠ 0 := OrthRestOdd.natCast_ne_zero_of_odd Nat.prime_three (by norm_num)
  have htp : (φ t) ^ 3 = 1 := by rw [← map_pow, hA.2 t htA, map_one]
  have hxp : ((φ t : CFSG.RankThree.Classical2.orthDerived Q) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, htp]
    rfl
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hxp
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hfix : Module.finrank K (CFSG.RankThree.PartOne.LIT.fixedSpace
      ((φ t : CFSG.RankThree.Classical2.orthDerived Q) :
        (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) = 6 := by
    rw [← omFixDim_eq_finrank_fixedSpace, ht6]
  have hd : Module.finrank K (CFSG.RankThree.PartOne.LIT.commSpace
      ((φ t : CFSG.RankThree.Classical2.orthDerived Q) :
        (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) = 2 := by
    rw [Module.finrank_fin_fun] at hsum
    omega
  exact exists_twoSubgroup_of_commSpace_two hnd (by rw [Module.finrank_fin_fun])
    (eq_one_of_pow_three_eq_one hK) (TableB.isElemAbelian_map hA _) (normalizesTwo_map φ hU)
    ⟨t, htA, rfl⟩ hd

theorem exists_twoSubgroup_of_fixDim_zero (hK : Nat.card K = 2) {A : Subgroup (Om8 K)}
    (hA : IsElemAbelian 3 A)
    (hU : ∃ U : Subgroup (Om8 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (Om8 K)))
    {t : Om8 K} (htA : t ∈ A) (ht0 : omFixDim t = 0) :
    ∃ U : Subgroup (Om8 K), U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set (Om8 K))) ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set (Om8 K)) := by
  have ht3 : t ^ 3 = 1 := hA.2 t htA
  rcases (ggD4TrialityClassInput_holds K t ht3).2 ht0 with h6 | h6
  · refine two_of_map (theta : Om8 K ≃* Om8 K) ?_
    exact exists_twoSubgroup_of_fixDim_six hK (TableB.isElemAbelian_map hA _)
      (normalizesTwo_map _ hU) ⟨t, htA, rfl⟩ h6
  · refine two_of_map ((theta : MulAut (Om8 K))⁻¹ : Om8 K ≃* Om8 K) ?_
    exact exists_twoSubgroup_of_fixDim_six hK (TableB.isElemAbelian_map hA _)
      (normalizesTwo_map _ hU) ⟨t, htA, rfl⟩ h6

theorem exists_twoSubgroup_of_fixDim (hK : Nat.card K = 2) {A : Subgroup (Om8 K)}
    (hA : IsElemAbelian 3 A)
    (hU : ∃ U : Subgroup (Om8 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (Om8 K)))
    {t : Om8 K} (htA : t ∈ A) (ht : omFixDim t = 0 ∨ omFixDim t = 6) :
    ∃ U : Subgroup (Om8 K), U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set (Om8 K))) ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set (Om8 K)) :=
  ht.elim (exists_twoSubgroup_of_fixDim_zero hK hA hU htA)
    (exists_twoSubgroup_of_fixDim_six hK hA hU htA)

end Dim

section EndNode

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def MidClassInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ t : Om8 K, t ^ 3 = 1 →
    (omFixDim t = 2 ∨ omFixDim t = 4) →
      ¬ IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set (Om8 K))))
        (Subgroup.centralizer ({t} : Set (Om8 K)))

@[expose] def MidClassSolvableInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ t : Om8 K, t ^ 3 = 1 →
    (omFixDim t = 2 ∨ omFixDim t = 4) →
      Group.IsSolvable (Subgroup.centralizer ({t} : Set (Om8 K)))

@[expose] def MidClassCommuteInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ t : Om8 K, t ^ 3 = 1 →
    (omFixDim t = 2 ∨ omFixDim t = 4) → ∀ g : Om8 K, g * t = t * g → ∀ q : ℕ, q.Prime → 3 < q →
      orderOf g ≠ q

theorem midClassSolvableInput_of_commute (h : MidClassCommuteInput) : MidClassSolvableInput :=
  fun K _ _ hK t ht3 hd =>
    LayerCores.OrthRegular.isSolvable_of_no_prime_gt_three' fun g q hq hq3 hg =>
      h K hK t ht3 hd (g : Om8 K)
        (Subgroup.mem_centralizer_singleton_iff.mp g.2) q hq hq3
        (by rw [Subgroup.orderOf_coe]; exact hg)

theorem midClassInput_of_solvable (h : MidClassSolvableInput) : MidClassInput :=
  fun K _ _ hK t ht3 hd hcomp =>
    ClNonsplit.not_isQuasisimple_of_le (h K hK t ht3 hd) hcomp.1
      ((isQuasisimple_iff _).mp hcomp.2.2)

theorem eq_one_of_omFixDim_eq_eight {t : Om8 K} (h : omFixDim t = 8) : t = 1 := by
  have htop : LinearMap.ker (omRep t - 1) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact h
  have hall : ∀ v : Fin (2 * 4) → K, (t : GL (Fin (2 * 4)) K).val *ᵥ v = v := fun v =>
    mem_ker_omRep_sub_one.mp (htop ▸ Submodule.mem_top)
  apply Subtype.ext
  apply Units.ext
  exact Matrix.ext_of_mulVec_single fun j => by
    rw [hall]
    show Pi.single j 1 = (1 : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ Pi.single j 1
    rw [Matrix.one_mulVec]

theorem omFixDim_le_eight (t : Om8 K) : omFixDim t ≤ 8 := by
  have := Submodule.finrank_le (LinearMap.ker (omRep t - 1))
  rwa [Module.finrank_fin_fun] at this

theorem omFixDim_mem_of_isEndNode (hK : Nat.card K = 2) (hmid : MidClassInput)
    {A : Subgroup (Om8 K)} (hA : IsElemAbelian 3 A) {t : Om8 K}
    (ht : TableBOrth.IsEndNode A t) : omFixDim t = 0 ∨ omFixDim t = 6 := by
  have ht3 : t ^ 3 = 1 := hA.2 t ht.1
  obtain ⟨k, hk⟩ := omFixDim_even t ht3
  have hle := omFixDim_le_eight t
  have hne8 : omFixDim t ≠ 8 := fun h8 => ht.2.1 (eq_one_of_omFixDim_eq_eight h8)
  by_contra hcon
  exact hmid K hK t ht3 (by omega) ht.2.2.1

theorem center_om8_eq_bot : Subgroup.center (Om8 K) = ⊥ := by
  obtain ⟨hnd, -⟩ := regular_coordinateQuadPlus (K := K) (n := 4) (by norm_num)
  obtain ⟨-, hc, -⟩ := OrthRestOdd.orthDerived_facts (coordinateQuadPlus 4 K) hnd
    (by rw [Module.finrank_fin_fun]; norm_num)
  let φ : Om8 K ≃* CFSG.RankThree.Classical2.orthDerived (coordinateQuadPlus 4 K) :=
    CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus 4 K)
  rw [eq_bot_iff]
  intro z hz
  have hz' : φ z ∈ Subgroup.center
      (CFSG.RankThree.Classical2.orthDerived (coordinateQuadPlus 4 K)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hc, Subgroup.mem_bot] at hz'
  exact (Subgroup.mem_bot).mpr (φ.injective (by rw [hz', map_one]))

theorem exists_endNode_om8 (hK : Nat.card K = 2) {A : Subgroup (Om8 K)} (hA : IsElemAbelian 3 A)
    (h27 : 3 ^ 3 ≤ Nat.card A)
    (hU : ∃ U : Subgroup (Om8 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (Om8 K))) : ∃ t, TableBOrth.IsEndNode A t := by
  have hadm := OrthRestOdd.ggEndNodeEltAdm_of_mulEquiv
    (RecipeFieldOmega.plusEquiv (K := K) (m := 4) (by norm_num))
    (ggOrthRestEndNodeInput_holds.2 K 4 hK le_rfl)
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  have hZ : Subgroup.center (Om8 K) = ⊥ := center_om8_eq_bot
  have hinj : Function.Injective (MulAut.conj : Om8 K →* MulAut (Om8 K)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center (Om8 K) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := congrArg (fun f : MulAut (Om8 K) => f h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc h * g = (g * h * g⁻¹) * g := by rw [this]
        _ = g * h := by group
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  obtain ⟨t, htA, ht1, hcomp, hcent⟩ := hadm A hA h27 h27
    ⟨U.map (MulAut.conj : Om8 K →* MulAut (Om8 K)),
      fun hbot => hU1 ((Subgroup.map_eq_bot_iff_of_injective U hinj).mp hbot), hU2.map _,
      (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map _)⟩
  exact ⟨t, htA, ht1, hcomp, hcent⟩

theorem ggEndNodeRootEltAll_om8 (hK : Nat.card K = 2) (hmid : MidClassInput) :
    GGEndNodeRootEltAll 3 3 (Om8 K) := by
  intro A hA _ h3 hU
  exact ⟨exists_endNode_om8 hK hA h3 hU, fun t ht =>
    exists_twoSubgroup_of_fixDim hK hA hU ht.1 (omFixDim_mem_of_isEndNode hK hmid hA ht)⟩

end EndNode

end OPlusEight

end CFSG.StandardType

end
