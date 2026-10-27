module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympCent
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LieType.SemisimpleCentralizers.HeldTwoDimUnitaryBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Wreathed.ProjectiveTwoParameterUniqueness
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615
open CFSG.LieType.SemisimpleCentralizers.Held
  (heldGU heldSU mem_heldGU commutatorElement_mem_heldSU SUComponentsTrivial_holds
    isComponentOf_subgroupOf_top_of)open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

noncomputable section

private theorem ltrspb3b_factorization_504 : (504 : ℕ).factorization 2 = 3 := by
  rw [show (504 : ℕ) = 2 ^ 3 * 63 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (p := 2) (n := 3) (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (p := 2) (n := 63) (by norm_num : ¬ 2 ∣ 63), add_zero]

private theorem ltrspb3b_arith {r n : ℕ} (hr : 1 ≤ r)
    (h : n * (r * (r - 1) / 2) = 3) : r = 2 ∨ r = 3 := by
  have ht_le : r * (r - 1) / 2 ≤ 3 := by
    have hn : 1 ≤ n := by
      rcases n with _ | n
      · simp at h
      · omega
    calc r * (r - 1) / 2 = 1 * (r * (r - 1) / 2) := (one_mul _).symm
      _ ≤ n * (r * (r - 1) / 2) := Nat.mul_le_mul_right _ hn
      _ = 3 := h
  have hrle : r ≤ 3 := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    have hprod : 12 ≤ r * (r - 1) := by
      calc 12 = 4 * 3 := by norm_num
        _ ≤ r * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h6 : 6 ≤ r * (r - 1) / 2 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
    omega
  interval_cases r
  · exfalso; norm_num at h
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem ltrspb3b_component_heldSU {r Q : ℕ} {E : Type} [Field E] [Finite E]
    {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x}
    (hcard : Nat.card E = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q)
    {J : Subgroup (GL (Fin r) E)} (hJ : CFSG.Open.IsComponentOf J (heldGU r E τ hτ)) :
    J = heldSU r E τ hτ := by
  have hle : J ≤ heldSU r E τ hτ := by
    have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
    have hcomm : ⁅J, J⁆ ≤ ⁅heldGU r E τ hτ, heldGU r E τ hτ⁆ :=
      Subgroup.commutator_mono hJ.1 hJ.1
    have hGU : ⁅heldGU r E τ hτ, heldGU r E τ hτ⁆ ≤ heldSU r E τ hτ :=
      Subgroup.commutator_le.mpr fun x hx y hy => commutatorElement_mem_heldSU hx hy
    rw [Subgroup.isPerfect_iff.mp hperf] at hcomm
    exact hcomm.trans hGU
  have hsub : CFSG.Open.IsSubnormal J (heldSU r E τ hτ) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hJ.2.1
      (inf_le_left : heldSU r E τ hτ ≤ heldGU r E τ hτ)
    change CFSG.Open.IsSubnormal (J ⊓ heldSU r E τ hτ) (heldSU r E τ hτ) at h
    rwa [inf_eq_left.mpr hle] at h
  have hcomp : CFSG.Open.IsComponentOf J (heldSU r E τ hτ) := ⟨hle, hsub, hJ.2.2⟩
  have htop : (J.subgroupOf (heldSU r E τ hτ)) = ⊤ :=
    SUComponentsTrivial_holds r Q E τ hτ hcard hτQ _
      (isComponentOf_subgroupOf_top_of hcomp)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

private theorem ltrspb3b_isComponentOf_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {L K : Subgroup G} (hL : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hL.1, CFSG.Open.IsSubnormal.map e.toMonoidHom hL.2.1, ?_⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective).symm hL.2.2

private theorem ltrspb3b_heldGU_two_conj_eq_heldSU {E : Type} [Field E] [Finite E] [CharP E 2]
    {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x}
    (hcard : Even (Nat.card E)) (g : ↥(heldGU 2 E τ hτ)) :
    ∃ s : ↥(heldSU 2 E τ hτ), ∀ x : ↥(heldSU 2 E τ hτ),
      (g : GL (Fin 2) E) * (x : GL (Fin 2) E) * (g : GL (Fin 2) E)⁻¹ =
      (s : GL (Fin 2) E) * (x : GL (Fin 2) E) * (s : GL (Fin 2) E)⁻¹ := by
  classical
  have hdetnorm : τ ((Matrix.GeneralLinearGroup.det (g : GL (Fin 2) E) : Eˣ) : E) *
      ((Matrix.GeneralLinearGroup.det (g : GL (Fin 2) E) : Eˣ) : E) = 1 := by
    have hg := mem_heldGU.mp g.2
    have hd := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    change Matrix.det ((Units.val (g : GL (Fin 2) E)).map ⇑τ) *
      Matrix.det (Units.val (g : GL (Fin 2) E)) = 1 at hd
    rw [show (Units.val (g : GL (Fin 2) E)).map ⇑τ =
        τ.mapMatrix (Units.val (g : GL (Fin 2) E)) from rfl,
      ← RingEquiv.map_det τ (Units.val (g : GL (Fin 2) E))] at hd
    exact hd
  obtain ⟨ρ0, hρ0⟩ := FiniteField.isSquare_of_char_two (ringChar.eq E 2)
    ((Matrix.GeneralLinearGroup.det (g : GL (Fin 2) E) : Eˣ) : E)
  have hρ0ne : ρ0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hρ0
    exact (Units.ne_zero (Matrix.GeneralLinearGroup.det (g : GL (Fin 2) E))) hρ0
  let ρ : Eˣ := Units.mk0 ρ0 hρ0ne
  have hρ : (ρ : E) ^ 2 = ((Matrix.GeneralLinearGroup.det (g : GL (Fin 2) E) : Eˣ) : E) := by
    simpa [ρ, pow_two] using hρ0.symm
  have hnorm : τ (ρ : E) * (ρ : E) = 1 := by
    have hsq : (τ (ρ : E) * (ρ : E)) ^ 2 = 1 := by
      rw [mul_pow, ← map_pow, hρ, hdetnorm]
    exact CharTwo.sq_injective (by simpa using hsq)
  let sc : GL (Fin 2) E := Matrix.GeneralLinearGroup.scalar (Fin 2) ρ
  have hM : (sc : Matrix (Fin 2) (Fin 2) E) = Matrix.scalar (Fin 2) (ρ : E) := rfl
  have hsc_mem : sc ∈ heldGU 2 E τ hτ := by
    rw [mem_heldGU, hM]
    rw [show (Matrix.scalar (Fin 2) (↑ρ : E)).map ⇑τ = Matrix.scalar (Fin 2) (τ ↑ρ) from by
      rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero τ), ← Matrix.scalar_apply]]
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.scalar_apply, hnorm,
      Matrix.scalar_apply, Matrix.diagonal_one]
  let s : GL (Fin 2) E := sc⁻¹ * g
  have hgu : s ∈ heldGU 2 E τ hτ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hsc_mem) g.2
  have hdet_s : Matrix.GeneralLinearGroup.det s = 1 := by
    rw [show s = sc⁻¹ * g from rfl, map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin]
    rw [show ((Matrix.GeneralLinearGroup.det (g : GL (Fin 2) E) : Eˣ)) = ρ ^ 2 from
      Units.ext (by simpa using hρ.symm)]
    simp
  have hsu : s ∈ heldSU 2 E τ hτ := Subgroup.mem_inf.mpr ⟨hgu, by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    exact congrArg Units.val hdet_s⟩
  refine ⟨⟨s, hsu⟩, ?_⟩
  intro x
  have hcomm : Commute sc (x : GL (Fin 2) E) := Matrix.GeneralLinearGroup.scalar_commute _ _
  have hscg : Commute sc (g : GL (Fin 2) E) := Matrix.GeneralLinearGroup.scalar_commute _ _
  have hscz : Commute sc ((g : GL (Fin 2) E) * (x : GL (Fin 2) E) * (g : GL (Fin 2) E)⁻¹) :=
    (hscg.mul_right hcomm).mul_right hscg.inv_right
  show (g : GL (Fin 2) E) * (x : GL (Fin 2) E) * (g : GL (Fin 2) E)⁻¹ =
    s * (x : GL (Fin 2) E) * s⁻¹
  calc (g : GL (Fin 2) E) * (x : GL (Fin 2) E) * (g : GL (Fin 2) E)⁻¹
      = sc⁻¹ * ((g : GL (Fin 2) E) * (x : GL (Fin 2) E) * (g : GL (Fin 2) E)⁻¹) * sc := by
        rw [hscz.inv_left.eq]; group
    _ = s * (x : GL (Fin 2) E) * s⁻¹ := by
        rw [show s = sc⁻¹ * (g : GL (Fin 2) E) from rfl, mul_inv_rev, inv_inv]; group

end

public section

private theorem ltrspb4_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x : G | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have hba : b * a' = a' * b := (hcomm a' ha' b hb).symm
        calc (a * b) * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hba]
          _ = (a * a') * (b * b') := by group
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hba : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ :=
          (hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * b⁻¹ := hba }
  have hAP : A ≤ P := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBP : B ≤ P := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  exact sup_le hAP hBP hx

private theorem ltrspb4_isComponentOf_map_subtype {G : Type*} [Group G] {K : Subgroup G}
    {L : Subgroup ↥K} (h : CFSG.Open.IsComponentOf L ⊤) :
    CFSG.Open.IsComponentOf (L.map K.subtype) K := by
  refine ⟨?_, ?_, ?_⟩
  · calc L.map K.subtype ≤ (⊤ : Subgroup ↥K).map K.subtype := Subgroup.map_mono le_top
      _ = K := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · have hsub := CFSG.Open.IsSubnormal.map K.subtype h.2.1
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hsub
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective L K.subtype K.subtype_injective).symm h.2.2

private theorem ltrspb4_heldSU_factorization_two {q r : ℕ} {E : Type} [Field E] [Finite E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y} (hr : 1 ≤ r)
    (hUF : UnitaryFieldData 2 q E) (hSU : unitarySU 2 q E r = heldSU r E τ hτ) :
    (Nat.card (heldSU r E τ hτ)).factorization 2 = q * (r * (r - 1) / 2) := by
  have hfac := (CFSG.SeitzReduction.LinearPilot.card_unitarySU_and_factorization
    (p := 2) (e := q) (K := E) (h := hUF) (n := r) hr).2
  rw [hSU, ← pow_mul] at hfac
  exact Nat.pow_right_injective (by norm_num : 1 < 2) hfac

private theorem ltrspb4_center_odd {q r : ℕ} {E : Type} [Field E] [Finite E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y} (hUF : UnitaryFieldData 2 q E)
    (hSU : unitarySU 2 q E r = heldSU r E τ hτ) :
    Odd (Nat.card (Subgroup.center ↥(heldSU r E τ hτ))) := by
  have h := CFSG.SeitzReduction.UnitaryPilot.odd_card_center_unitarySU hUF r
  rwa [hSU] at h

private theorem ltrspb4_heldSU_card_three {E : Type} [Field E] [Finite E]
    {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hUF : UnitaryFieldData 2 1 E) (hSU : unitarySU 2 1 E 3 = heldSU 3 E τ hτ) :
    Nat.card (heldSU 3 E τ hτ) = 216 := by
  have h := (CFSG.SeitzReduction.LinearPilot.card_unitarySU_and_factorization
    (p := 2) (e := 1) (K := E) (h := hUF) (n := 3) (by norm_num)).1
  rw [hSU] at h
  norm_num [Finset.prod_Icc_succ_top] at h
  exact_mod_cast h

theorem spUnitaryBlock_action {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {x : ↥(StatedSp m K)} {A₁ A₂ : Subgroup ↥(StatedSp m K)}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hY : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set ↥(StatedSp m K))) (hxA : x ∈ A₂)
    {r : ℕ} {E : Type} [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hr : 1 ≤ r) (hE : Nat.card E = Nat.card K ^ 2) (hτF : ∀ y, τ y = y ^ Nat.card K)
    (e₂ : A₂ ≃* heldGU r E τ hτ) {C : Subgroup ↥(StatedSp m K)}
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({x} : Set ↥(StatedSp m K))))
    (hle : C ≤ A₂) (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C))
    {y : ↥(StatedSp m K)} (hxy : x * y = y * x) (hyC : ∀ c ∈ C, MulAut.conj y c ∈ C) :
    QuotientInner C (MulAut.conj y) := by
  classical
  have hyY : y ∈ A₁ ⊔ A₂ := by
    rw [hY]
    exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hxy)
  obtain ⟨a, ha, b, hb, hab⟩ := ltrspb4_mem_sup_of_commute hcomm hyY
  have hcompA₂ : CFSG.Open.IsComponentOf C A₂ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open C A₂).mp
      (hC.of_le_of_le hle (le_sup_right.trans hY.le))
  have hcompTop : CFSG.Open.IsComponentOf (C.subgroupOf A₂) ⊤ :=
    isComponentOf_subgroupOf_top_of hcompA₂
  let L' : Subgroup ↥(heldGU r E τ hτ) := (C.subgroupOf A₂).map e₂.toMonoidHom
  have hL'comp : CFSG.Open.IsComponentOf L' ⊤ := by
    have h := ltrspb3b_isComponentOf_map e₂ hcompTop
    rw [Subgroup.map_top_of_surjective _ e₂.surjective] at h
    exact h
  have hJeq : L'.map (heldGU r E τ hτ).subtype = heldSU r E τ hτ :=
    ltrspb3b_component_heldSU (Q := Nat.card K) hE hτF
      (ltrspb4_isComponentOf_map_subtype hL'comp)
  have hL'eq : L' = (heldSU r E τ hτ).subgroupOf (heldGU r E τ hτ) := by
    have h1 : L' = (L'.map (heldGU r E τ hτ).subtype).subgroupOf (heldGU r E τ hτ) :=
      (Subgroup.subgroupOf_map_subtype_eq_self L').symm
    rwa [hJeq] at h1
  have eC : ↥C ≃* ↥L' :=
    (Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (Subgroup.equivMapOfInjective (C.subgroupOf A₂) e₂.toMonoidHom e₂.injective)
  have eSU : ↥C ≃* ↥(heldSU r E τ hτ) :=
    eC.trans ((MulEquiv.subgroupCongr hL'eq).trans
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : heldSU r E τ hτ ≤ heldGU r E τ hτ)))
  have hcard504 : Nat.card (↥C ⧸ Subgroup.center ↥C) = 504 := by
    have hlabel : CFSG.Assembly.LargeEvenRecipeLinear 2 8
        (fun R' _ _ _ => Nonempty (↥C ⧸ Subgroup.center ↥C ≃* R')) := by
      have h := hlab
      unfold GGHasLabel at h
      dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
      norm_num at h
      exact h
    unfold CFSG.Assembly.LargeEvenRecipeLinear at hlabel
    obtain ⟨K₀, hK0f, hK0fin, hK0card, ⟨ψ⟩⟩ := hlabel
    letI : Field K₀ := hK0f
    letI : Finite K₀ := hK0fin
    have e1 : (↥C ⧸ Subgroup.center ↥C) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin 2) K₀) := ψ
    have eL : (↥C ⧸ Subgroup.center ↥C) ≃*
        CFSG.LieType.SemisimpleCentralizers.HeldLang.PSL (Fin 2) K₀ :=
      e1.trans (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.pslEquivLarge (K := K₀) 2).symm
    have eSP : (↥C ⧸ Subgroup.center ↥C) ≃* StatedProj (StatedSL 2 K₀) :=
      eL.trans (Classical.choice
        (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_psl_equiv_statedProj 2 K₀))
    have eM : (↥C ⧸ Subgroup.center ↥C) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) K₀ :=
      eSP.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K₀).symm
    rw [Nat.card_congr eM.toEquiv]
    rw [CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_projective_two_field K₀, hK0card]
    norm_num
  have eSUq : (↥C ⧸ Subgroup.center ↥C) ≃*
      (↥(heldSU r E τ hτ) ⧸ Subgroup.center ↥(heldSU r E τ hτ)) :=
    QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥(heldSU r E τ hτ)) eSU
      (Subgroup.map_center_eq eSU)
  have hQ : Nat.card (↥(heldSU r E τ hτ) ⧸ Subgroup.center ↥(heldSU r E τ hτ)) = 504 := by
    rw [← Nat.card_congr eSUq.toEquiv]
    exact hcard504
  obtain ⟨e, he1, heK⟩ :=
    CFSG.SeitzReduction.LinearPilot.exists_natCard_eq_two_pow_of_charP K
  have hE' : Nat.card E = (2 ^ e) ^ 2 := by rw [hE, heK]
  have hUF : UnitaryFieldData 2 e E :=
    ⟨Nat.prime_two, he1, by rw [hE', ← pow_mul, Nat.mul_comm e 2]⟩
  have hSU : unitarySU 2 e E r = heldSU r E τ hτ := by
    have h : heldSU r E τ hτ = StatedSU r (Nat.card K) E :=
      CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU
        (a := r) (Q := Nat.card K) (M := E) hτF
    rw [heK] at h
    show StatedSU r (2 ^ e) E = heldSU r E τ hτ
    exact h.symm
  have hfacSU : (Nat.card (heldSU r E τ hτ)).factorization 2 = e * (r * (r - 1) / 2) :=
    ltrspb4_heldSU_factorization_two hr hUF hSU
  have hcenterOdd : Odd (Nat.card (Subgroup.center ↥(heldSU r E τ hτ))) :=
    ltrspb4_center_odd hUF hSU
  have hfac3 : (Nat.card (heldSU r E τ hτ)).factorization 2 = 3 := by
    have hcenter : (Nat.card (heldSU r E τ hτ)).factorization 2 =
        (Nat.card (↥(heldSU r E τ hτ) ⧸
          Subgroup.center ↥(heldSU r E τ hτ))).factorization 2 := by
      have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(heldSU r E τ hτ))
      have hQnz : Nat.card (↥(heldSU r E τ hτ) ⧸
          Subgroup.center ↥(heldSU r E τ hτ)) ≠ 0 := by
        rw [hQ]; norm_num
      have hZnz : Nat.card (Subgroup.center ↥(heldSU r E τ hτ)) ≠ 0 := by
        rintro h0
        exact (Nat.not_even_iff_odd.mpr hcenterOdd) (by simpa [h0] using Nat.even_zero)
      have hZfac : (Nat.card (Subgroup.center ↥(heldSU r E τ hτ))).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd
          (p := 2) (n := Nat.card (Subgroup.center ↥(heldSU r E τ hτ))) (by
            intro hdvd
            exact (Nat.not_even_iff_odd.mpr hcenterOdd) (even_iff_two_dvd.mpr hdvd))
      rw [hcard, Nat.factorization_mul hQnz hZnz, Finsupp.add_apply, hZfac, add_zero]
    rw [hcenter, hQ]
    exact ltrspb3b_factorization_504
  have h504dvd : 504 ∣ Nat.card (heldSU r E τ hτ) := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(heldSU r E τ hτ))
    rw [hcard, hQ]
    exact dvd_mul_right 504 _
  have hr2 : r = 2 := by
    by_contra hne
    have heq : e * (r * (r - 1) / 2) = 3 := by
      rw [← hfacSU]
      exact hfac3
    rcases ltrspb3b_arith hr heq with h2 | h3
    · exact hne h2
    · have he1' : e = 1 := by
        rw [h3] at heq
        norm_num at heq
        omega
      have hUF1 : UnitaryFieldData 2 1 E := by
        have hh := hUF
        rw [he1'] at hh
        exact hh
      have hSU1 : unitarySU 2 1 E 3 = heldSU 3 E τ hτ := by
        have hh := hSU
        rw [he1', h3] at hh
        exact hh
      have hcardSU3 : Nat.card (heldSU 3 E τ hτ) = 216 :=
        ltrspb4_heldSU_card_three hUF1 hSU1
      have hdvd : 504 ∣ Nat.card (heldSU 3 E τ hτ) := by
        have hh := h504dvd
        rw [h3] at hh
        exact hh
      rw [hcardSU3] at hdvd
      norm_num at hdvd
  subst r
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype E := Fintype.ofFinite E
  haveI hcharE : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := e * 2) (by
    rw [Fintype.card_eq_nat_card, hE, heK, ← pow_mul])
  have hEven : Even (Nat.card E) := by
    rw [hE, heK, ← pow_mul]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : e * 2 ≠ 0))
  let gb : ↥(heldGU 2 E τ hτ) := e₂ ⟨b, hb⟩
  obtain ⟨s, hs⟩ := ltrspb3b_heldGU_two_conj_eq_heldSU (E := E) (τ := τ) (hτ := hτ) hEven gb
  have hs_mem : (⟨s, (Subgroup.mem_inf.mp s.2).1⟩ : ↥(heldGU 2 E τ hτ)) ∈ L' := by
    rw [hL'eq]
    exact s.2
  obtain ⟨bA, hbA, hbAeq⟩ := Subgroup.mem_map.mp hs_mem
  let b' : ↥C := (Subgroup.subgroupOfEquivOfLe hle) ⟨bA, hbA⟩
  have hb'gh : e₂ (⟨b', hle b'.2⟩ : ↥A₂) =
      (⟨s, (Subgroup.mem_inf.mp s.2).1⟩ : ↥(heldGU 2 E τ hτ)) := by
    rw [show (⟨b', hle b'.2⟩ : ↥A₂) = bA from Subtype.ext rfl]
    exact hbAeq
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥C) b', ?_⟩
  intro c c' hcc'
  have hcSU : (e₂ ⟨(c : ↥(StatedSp m K)), hle c.2⟩ : GL (Fin 2) E) ∈ heldSU 2 E τ hτ := by
    have hmem : e₂ ⟨(c : ↥(StatedSp m K)), hle c.2⟩ ∈ L' :=
      Subgroup.mem_map.mpr ⟨⟨(c : ↥(StatedSp m K)), hle c.2⟩,
        by simpa only [Subgroup.mem_subgroupOf] using c.2, rfl⟩
    rw [hL'eq] at hmem
    exact hmem
  have hconj : MulAut.conj y (c : ↥(StatedSp m K)) = b * (c : ↥(StatedSp m K)) * b⁻¹ := by
    rw [hab, MulAut.conj_apply]
    calc (a * b) * (c : ↥(StatedSp m K)) * (a * b)⁻¹
        = a * (b * (c : ↥(StatedSp m K)) * b⁻¹) * a⁻¹ := by group
      _ = b * (c : ↥(StatedSp m K)) * b⁻¹ := by
          have hX : b * (c : ↥(StatedSp m K)) * b⁻¹ ∈ A₂ :=
            A₂.mul_mem (A₂.mul_mem hb (hle c.2)) (A₂.inv_mem hb)
          rw [hcomm a ha (b * (c : ↥(StatedSp m K)) * b⁻¹) hX]
          group
  have hbb' : (⟨b, hb⟩ * ⟨(c : ↥(StatedSp m K)), hle c.2⟩ * ⟨b, hb⟩⁻¹ : ↥A₂) =
      ⟨b', hle b'.2⟩ * ⟨(c : ↥(StatedSp m K)), hle c.2⟩ * ⟨b', hle b'.2⟩⁻¹ := by
    apply e₂.injective
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hb'gh]
    apply Subtype.ext
    exact hs ⟨(e₂ ⟨(c : ↥(StatedSp m K)), hle c.2⟩ : GL (Fin 2) E), hcSU⟩
  have hconj_eq : (MulAut.conj y (c : ↥(StatedSp m K)) : ↥(StatedSp m K)) =
      (b' : ↥(StatedSp m K)) * (c : ↥(StatedSp m K)) *
        (b' : ↥(StatedSp m K))⁻¹ := by
    rw [hconj]
    have h := congrArg (fun t : ↥A₂ => (t : ↥(StatedSp m K))) hbb'
    simpa using h
  have hLval : c' = b' * c * b'⁻¹ := by
    apply Subtype.ext
    show (c' : ↥(StatedSp m K)) =
      (b' : ↥(StatedSp m K)) * (c : ↥(StatedSp m K)) * (b' : ↥(StatedSp m K))⁻¹
    rw [← hcc', hconj_eq]
  rw [hLval]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk'_apply]

end

end S2MathAs3_1619Final

end
