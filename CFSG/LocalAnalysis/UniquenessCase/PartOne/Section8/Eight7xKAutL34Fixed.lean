module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.Open.Defs
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL34b
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320A5
public import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.CGT.PushingUpLit.A78.LQ4Count
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
public import CFSG.CGT.PushingUpLit.BHS6.OffenderNormalizes
public import CFSG.CGT.PushingUpLit.CGT6.SixFiveArrow
public import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoOff
public import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
public import CFSG.CGT.PushingUpLit.NineContent
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LieType.SeitzGeneration.OuterLinearCat
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped commutatorElement

private noncomputable def eqLocusMulEquivCongr {L P : Type*} [Group L] [Group P]
    (φ : L ≃* P) (α : MulAut L) :
    ↥((α.toMonoidHom).eqLocus (MonoidHom.id L)) ≃*
      ↥(((MulAut.congr φ α).toMonoidHom).eqLocus (MonoidHom.id P)) where
  toFun x := ⟨φ x, by
    have hx : α (x : L) = (x : L) := x.2
    have hcongr : (MulAut.congr φ α) (φ (x : L)) = φ (α (x : L)) := by
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (MulAut.congr φ α) (φ (x : L)) = φ (x : L)
    rw [hcongr, hx]⟩
  invFun y := ⟨φ.symm y, by
    have hy : φ (α (φ.symm (y : P))) = (y : P) := y.2
    change α (φ.symm (y : P)) = φ.symm (y : P)
    apply φ.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := Subtype.ext (map_mul φ (x : L) (y : L))

private theorem false_of_commutator_mem_center {G : Type*} [Group G] [Finite G]
    (C Z : Subgroup G) (w : G)
    (hCcard : Nat.card C = 21) (hZcard : Nat.card Z = 3) (hZC : Z ≤ C)
    (hZker : C ⊓ Subgroup.centralizer ({w} : Set G) = Z)
    (hZcentral : ∀ z ∈ Z, ∀ g : G, z * g = g * z)
    (hcomm : ∀ c : C, ⁅w, (c : G)⁆ ∈ Z) : False := by
  classical
  let ψ : C →* Z :=
    { toFun := fun c => ⟨⁅w, (c : G)⁆, hcomm c⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro c d
        apply Subtype.ext
        change ⁅w, (c : G) * (d : G)⁆ = ⁅w, (c : G)⁆ * ⁅w, (d : G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hd : ⁅w, (d : G)⁆ ∈ Z := hcomm d
        have hcz : (c : G) * ⁅w, (d : G)⁆ = ⁅w, (d : G)⁆ * (c : G) :=
          (hZcentral _ hd (c : G)).symm
        have hconj : (c : G) * ⁅w, (d : G)⁆ * (c : G)⁻¹ = ⁅w, (d : G)⁆ := by
          rw [hcz, mul_inv_cancel_right]
        calc ⁅w, (c : G)⁆ * (c : G) * ⁅w, (d : G)⁆ * (c : G)⁻¹
            = ⁅w, (c : G)⁆ * ((c : G) * ⁅w, (d : G)⁆ * (c : G)⁻¹) := by group
          _ = ⁅w, (c : G)⁆ * ⁅w, (d : G)⁆ := by rw [hconj] }
  have hker : Nat.card ↥ψ.ker = 3 := by
    have heq : ψ.ker = Z.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change (⟨⁅w, (c : G)⁆, hcomm c⟩ : Z) = 1 ↔ (c : G) ∈ Z
      rw [Subtype.ext_iff]
      simp only [Subgroup.coe_one]
      rw [commutatorElement_eq_one_iff_mul_comm, ← hZker, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        exact ⟨c.2, h.symm⟩
      · rintro ⟨-, h⟩
        exact h.symm
    rw [heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZcard]
  have hcard := CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range ψ
  have hrange : Nat.card ↥ψ.range = 7 := by
    rw [hCcard, hker] at hcard
    omega
  have hle : Nat.card ↥ψ.range ≤ 3 := by
    calc Nat.card ↥ψ.range ≤ Nat.card ↥(⊤ : Subgroup ↥Z) := Subgroup.card_le_of_le le_top
      _ = Nat.card ↥Z := Subgroup.card_top
      _ = 3 := hZcard
  omega

private theorem c25Fix_zpowers_eq_autFixed {G : Type*} [Group G] (α : MulAut G) :
    CFSG.HardMathSupport.Solomon.Coordinator.c25Fix (Subgroup.zpowers α) =
      CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed α := by
  ext x
  rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.mem_c25Fix_zpowers_iff,
    CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.mem_autFixed]

private theorem autFixed_conj_iso {G : Type*} [Group G] (h α : MulAut G) :
    Nonempty (↥(CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
        (h * α * h⁻¹)) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed α)) := by
  rw [CFSG.RankThree.PartTwo.KFacts.L34.autFixed_conj]
  exact ⟨(Subgroup.equivMapOfInjective
    (CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed α) h.toMonoidHom
    h.injective).symm⟩

private theorem a5Sub_mulEquiv_alternating {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) :
    Nonempty (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.a5Sub (k := K) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨e1⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.a5Sub_mul_equiv (k := K)
  obtain ⟨e2⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_psl2_mulEquiv_alternating_five
    (k := K) (Or.inl hK)
  refine ⟨e1.trans ?_⟩
  exact ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K).symm.trans
    ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      2 K).symm.trans e2))

private theorem autFixed_diagE_eq_a5Sub {K : Type} [Field K] [Finite K] [CharP K 2] [Fintype K]
    (hK : Nat.card K = 4) {e : Kˣ} (he : e ≠ 1) (he3 : (e : K) ^ 3 = 1) :
    CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
          (CFSG.RankThree.PartTwo.Sec4.diagE e)) =
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.a5Sub (k := K) := by
  classical
  have hKpi : CFSG.RankThree.PartTwo.Sec4.PiField true 2 2 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num [CFSG.RankThree.PartTwo.Sec4.piCard]⟩
  have h3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h31 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [h31]
    exact one_ne_zero
  have hle : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.a5Sub (k := K) ≤
      CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
          (CFSG.RankThree.PartTwo.Sec4.diagE e)) := by
    rintro x ⟨h, rfl⟩
    rw [CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.mem_autFixed]
    apply CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.conjAut_proj_eq_of_comm
    rw [CFSG.RankThree.PartTwo.Sec4.coe_diagE,
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.coe_iota]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three,
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.iotaMat]
  have hcardA5 : Nat.card (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.a5Sub
      (k := K)) = 60 := by
    obtain ⟨e1⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.a5Sub_mul_equiv
      (k := K)
    rw [Nat.card_congr e1.toEquiv]
    exact CFSG.Quasithin.H13.KGL34P.card_sl_two hK
  have hcardfix : Nat.card (CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
        (CFSG.RankThree.PartTwo.Sec4.diagE e))) = 60 := by
    have hb := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34b.card_fix_conjAut_mul_three
      hK (A := CFSG.RankThree.PartTwo.Sec4.diagE e) (z := 1) (by exact Subgroup.one_mem _)
    rw [mul_one] at hb
    have hcent : Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.centMod
        (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K)
        (CFSG.RankThree.PartTwo.Sec4.diagE e)) = 180 := by
      rw [CFSG.RankThree.PartTwo.Sec4.centMod_diagE_eq true he3 h3]
      obtain ⟨iso⟩ := CFSG.RankThree.PartTwo.Sec4.centralizer_diagE_mulEquiv
        (π := true) (p := 2) (f := 2) hKpi he
      rw [Nat.card_congr iso.toEquiv]
      have hk' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
      change Nat.card (⊤ : Subgroup (GL (Fin 2) K)) = 180
      rw [Subgroup.card_top, Matrix.card_GL_field, hk', Fin.prod_univ_two]
      norm_num
    rw [hcent] at hb
    have hc25 : Nat.card (CFSG.HardMathSupport.Solomon.Coordinator.c25Fix
        (Subgroup.zpowers (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
          (CFSG.RankThree.PartTwo.Sec4.diagE e)))) = 60 := by omega
    have heq : CFSG.HardMathSupport.Solomon.Coordinator.c25Fix
        (Subgroup.zpowers (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
          (CFSG.RankThree.PartTwo.Sec4.diagE e))) =
        CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
            (CFSG.RankThree.PartTwo.Sec4.diagE e)) := c25Fix_zpowers_eq_autFixed _
    rw [heq] at hc25
    exact hc25
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardfix, hcardA5])).symm


private theorem fixed_subgroup_of_outer_orderThree_projectiveSL
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (β : MulAut (projectiveSL 3 K)) (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Nonempty (↥((β.toMonoidHom).eqLocus (MonoidHom.id (projectiveSL 3 K))) ≃*
        alternatingGroup (Fin 5)) ∨
      (Nat.card ↥((β.toMonoidHom).eqLocus (MonoidHom.id (projectiveSL 3 K))) = 21 ∧
        ∃ a b : ↥((β.toMonoidHom).eqLocus (MonoidHom.id (projectiveSL 3 K))),
          a * b ≠ b * a) := by
  classical
  have hβ3 : β ^ 3 = 1 := by
    have h := pow_orderOf_eq_one β
    rwa [hβ] at h
  have hlin : β ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup 3 K := by
    by_contra hD
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (n := 3) le_rfl β hβ3 hD
    have h3dvd :=
      (CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three (p := 2) (f := 2)
        Nat.prime_two (by norm_num) (by rw [hK]; norm_num) hσ).1
    omega
  obtain ⟨A, hAβ⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_linearAutGroup_iff.1 hlin
  have hAs : A ∉ CFSG.Open.StatedScalars (Fin 3) K := by
    intro hAsc
    apply hout
    rw [← hAβ]
    obtain ⟨c, rfl⟩ := hAsc
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar]
    exact Subgroup.one_mem _
  have hA3 : A ^ 3 ∈ CFSG.Open.StatedScalars (Fin 3) K := by
    have h : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K (A ^ 3) = 1 := by
      rw [map_pow, hAβ, hβ3]
    obtain ⟨-, c, hc⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
        (n := 3) le_rfl (A ^ 3) 1 (by rw [map_one, mul_one, h])
    exact ⟨c, hc⟩
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_units_ne_one hK
  have hu3u : u ^ 3 = 1 := by
    have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    have h := pow_card_eq_one' (x := u)
    rwa [hcard] at h
  have hu3 : (u : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3u, Units.val_one]
  have hτ1 : (u : K) ≠ 1 := CFSG.RankThree.PartTwo.KFacts.L34.val_ne_one hu
  have hKpi : CFSG.RankThree.PartTwo.Sec4.PiField true 2 2 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num [CFSG.RankThree.PartTwo.Sec4.piCard]⟩
  have hq : CFSG.RankThree.PartTwo.Sec4.ModThree true (2 ^ 2) := by
    change 2 ^ 2 % 3 = 1
    norm_num
  have hπ : true = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 K :=
    fun h => absurd h (by decide)
  have hπ' : true = false → CFSG.RankThree.PartTwo.Sec4.ModThree false (2 ^ 2) :=
    fun h => absurd h (by decide)
  have hzPi : CFSG.RankThree.PartTwo.Sec4.zPi true 3 (2 ^ 2) K =
      CFSG.RankThree.PartTwo.Sec4.glPi true 3 (2 ^ 2) K ⊓
        CFSG.Open.StatedScalars (Fin 3) K :=
    CFSG.RankThree.PartTwo.Sec4.zPi_eq hπ hπ' hu3 hτ1
  have hxZ : A ∉ CFSG.RankThree.PartTwo.Sec4.zPi true 3 (2 ^ 2) K := by
    rw [hzPi]
    exact fun h => hAs h.2
  have hx3 : A ^ 3 ∈ CFSG.RankThree.PartTwo.Sec4.zPi true 3 (2 ^ 2) K := by
    rw [hzPi]
    exact ⟨CFSG.RankThree.PartTwo.Sec4.mem_glPi_true (2 ^ 2) A, hA3⟩
  obtain ⟨y, ⟨z, hz, hyz⟩, hcase⟩ :=
    CFSG.RankThree.PartTwo.Sec4.rank3II_4_10_one hKpi hq hu3 hτ1
      (CFSG.RankThree.PartTwo.Sec4.mem_glPi_true (2 ^ 2) A) hxZ hx3
  have hzs : z ∈ CFSG.Open.StatedScalars (Fin 3) K := by
    rw [hzPi] at hz
    exact hz.2
  have hβy : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K y = β := by
    rw [hyz, map_mul, hAβ]
    obtain ⟨c, rfl⟩ := hzs
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar, mul_one]
  change Nonempty (↥(CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed β) ≃*
      alternatingGroup (Fin 5)) ∨
    (Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed β) = 21 ∧
      ∃ a b : ↥(CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed β),
        a * b ≠ b * a)
  rcases hcase with hcase1 | hcase2 | hcase3
  ·
    obtain ⟨⟨g, hg, hgy⟩, -, -⟩ := hcase1
    exfalso
    apply hout
    have hy_eq : y = g * CFSG.RankThree.PartTwo.Sec4.diagTau hu3 * g⁻¹ := by
      rw [← hgy]
      group
    set s : Matrix.SpecialLinearGroup (Fin 3) K :=
      ⟨CFSG.RankThree.PartTwo.Sec4.diagTau hu3,
        (CFSG.RankThree.PartTwo.Sec4.mem_slPi_true _).1
          (CFSG.RankThree.PartTwo.Sec4.diagTau_mem_slPi hπ hπ' hu3)⟩ with hs
    have hsl : Matrix.SpecialLinearGroup.toGL s = CFSG.RankThree.PartTwo.Sec4.diagTau hu3 :=
      Units.ext rfl
    have hinner : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
        (CFSG.RankThree.PartTwo.Sec4.diagTau hu3) ∈
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
      rw [← hsl, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_toGL]
      exact ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s, rfl⟩
    rw [← hβy, hy_eq, map_mul, map_mul, map_inv]
    exact (Subgroup.Normal.conj_mem (inferInstance :
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range.Normal)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
        (CFSG.RankThree.PartTwo.Sec4.diagTau hu3)) hinner
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K g))
  ·
    obtain ⟨⟨g, hg, e, he, hgy⟩, -, -⟩ := hcase2
    left
    have he1 : e ≠ 1 := by
      intro h1
      rw [h1, Units.val_one] at he
      rcases he with he | he
      · exact hτ1 he.symm
      · apply hτ1
        calc (u : K) = (u : K) ^ 3 / (u : K) ^ 2 := by field_simp
          _ = 1 := by rw [hu3, ← he, div_one]
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he <;> rw [he]
      · exact hu3
      · rw [← pow_mul, pow_mul', hu3, one_pow]
    have hy_eq : y = g * CFSG.RankThree.PartTwo.Sec4.diagE e * g⁻¹ := by
      rw [← hgy]
      group
    have hconj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K y =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K g *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
            (CFSG.RankThree.PartTwo.Sec4.diagE e) *
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K g)⁻¹ := by
      rw [hy_eq, map_mul, map_mul, map_inv]
    have heqDiag : CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
          (CFSG.RankThree.PartTwo.Sec4.diagE e)) =
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.a5Sub (k := K) :=
      @autFixed_diagE_eq_a5Sub K _ _ (CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hK) (Fintype.ofFinite K) hK e he1 he3
    obtain ⟨eA5⟩ := @a5Sub_mulEquiv_alternating K _ _ (CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hK) hK
    have hβeq : CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed β =
        CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K g *
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
              (CFSG.RankThree.PartTwo.Sec4.diagE e) *
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K g)⁻¹) := by
      rw [← hβy, hconj]
    rw [hβeq]
    obtain ⟨iso1⟩ := autFixed_conj_iso
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K g)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K
        (CFSG.RankThree.PartTwo.Sec4.diagE e))
    exact ⟨iso1.trans ((MulEquiv.subgroupCongr heqDiag).trans eA5)⟩
  ·
    right
    obtain ⟨-, -, -, hcyc, hcardC, w, hwL, hwo, hwC, hcent, hcard3⟩ := hcase3
    set C : Subgroup (GL (Fin 3) K) :=
      CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K ⊓ Subgroup.centralizer {y} with hC
    have hcardC21 : Nat.card ↥C = 21 := by
      rw [hC, hcardC]
      norm_num [CFSG.RankThree.PartTwo.Sec4.qSubPi]
    have hcent' : CFSG.RankThree.PartTwo.Sec4.centMod
        (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K) y =
        C ⊔ Subgroup.zpowers w := by
      rw [hC, hcent]
    have hwcard : Nat.card ↥(Subgroup.zpowers w) = 3 := by
      rw [Nat.card_zpowers, hwo]
    have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (C : Set (GL (Fin 3) K)) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_normalizer_fintype fun l hl => ?_
      obtain ⟨hlL, hly⟩ := Subgroup.mem_inf.1 hl
      rw [Subgroup.mem_centralizer_singleton_iff] at hly
      have hwM : w ∈ CFSG.RankThree.PartTwo.Sec4.centMod
          (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K) y := by
        rw [hcent']
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
      obtain ⟨-, z', ⟨c', rfl⟩, hz'⟩ :=
        CFSG.RankThree.PartTwo.Sec4.mem_centMod_iff_scalar.1 hwM
      set Z' := Matrix.GeneralLinearGroup.scalar (Fin 3) c' with hZ'
      have hZi : ∀ g : GL (Fin 3) K, g * Z'⁻¹ = Z'⁻¹ * g := fun g =>
        ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c' g).inv_right).eq
      set yy := y with hyy
      have hwy : w⁻¹ * yy * w = Z'⁻¹ * yy := by
        calc w⁻¹ * yy * w = w⁻¹ * (Z'⁻¹ * (Z' * yy)) * w := by group
          _ = w⁻¹ * (Z'⁻¹ * (w * yy * w⁻¹)) * w := by rw [hz']
          _ = w⁻¹ * (Z'⁻¹ * w) * yy := by group
          _ = w⁻¹ * (w * Z'⁻¹) * yy := by rw [hZi w]
          _ = Z'⁻¹ * yy := by group
      refine Subgroup.mem_inf.2 ⟨(CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K).mul_mem
        ((CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K).mul_mem hwL hlL)
        ((CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K).inv_mem hwL), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * l * w⁻¹ * yy = w * l * (w⁻¹ * yy * w) * w⁻¹ := by group
        _ = w * l * (Z'⁻¹ * yy) * w⁻¹ := by rw [hwy]
        _ = w * (Z'⁻¹ * l) * yy * w⁻¹ := by rw [← hZi l]; group
        _ = w * Z'⁻¹ * (l * yy) * w⁻¹ := by group
        _ = w * Z'⁻¹ * (yy * l) * w⁻¹ := by rw [hly]
        _ = w * (Z'⁻¹ * yy) * l * w⁻¹ := by group
        _ = w * (w⁻¹ * yy * w) * l * w⁻¹ := by rw [hwy]
        _ = yy * (w * l * w⁻¹) := by group
    have hinf : C ⊓ Subgroup.zpowers w = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      have hdvd : Nat.card ↥(C ⊓ Subgroup.zpowers w) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le
          (inf_le_right : C ⊓ Subgroup.zpowers w ≤ Subgroup.zpowers w)
        rwa [hwcard] at h
      have hne : Nat.card ↥(C ⊓ Subgroup.zpowers w) ≠ 3 := by
        intro h3
        have hbot : C ⊓ Subgroup.zpowers w = Subgroup.zpowers w :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hwcard])
        have hleC : Subgroup.zpowers w ≤ C := by
          rw [← hbot]
          exact inf_le_left
        exact hwC (hleC (Subgroup.mem_zpowers w))
      rcases (Nat.dvd_prime (show Nat.Prime 3 by norm_num)).1 hdvd with h1 | h3
      · exact h1
      · exact absurd h3 hne
    have hcentcard : Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.centMod
        (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K) y) = 63 := by
      have h := CFSG.QuasithinUnique.Lin2.card_sup_mul_card_inf
        (A := Subgroup.zpowers w) (B := C) hwN
      rw [sup_comm, ← hcent', hwcard, hcardC21, inf_comm, hinf, Subgroup.card_bot, mul_one] at h
      omega
    have hfixcard : Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed β) = 21 := by
      have hb := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34b.card_fix_conjAut_mul_three
        hK (A := y) (z := 1) (by exact Subgroup.one_mem _)
      rw [mul_one, hcentcard] at hb
      have hc25 : Nat.card (CFSG.HardMathSupport.Solomon.Coordinator.c25Fix
          (Subgroup.zpowers (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K y))) = 21 := by
        omega
      have heq : CFSG.HardMathSupport.Solomon.Coordinator.c25Fix
          (Subgroup.zpowers (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K y)) =
          CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 K y) :=
        c25Fix_zpowers_eq_autFixed _
      rw [heq] at hc25
      rwa [hβy] at hc25
    refine ⟨hfixcard, ?_⟩
    by_contra hnab
    push Not at hnab
    let L : Subgroup (GL (Fin 3) K) := CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K
    let Z : Subgroup (GL (Fin 3) K) :=
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K).map
        Matrix.SpecialLinearGroup.toGL
    have hZcard : Nat.card ↥Z = 3 := by
      change Nat.card ↥((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K).map
        Matrix.SpecialLinearGroup.toGL) = 3
      rw [Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective]
      exact CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars hK
    have hZst : Z ≤ CFSG.Open.StatedScalars (Fin 3) K := by
      rintro z ⟨s, hs, rfl⟩
      obtain ⟨c, -, hc⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars.1 hs
      refine ⟨c, ?_⟩
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc,
        Matrix.GeneralLinearGroup.coe_scalar]
    have hZcentral : ∀ z ∈ Z, ∀ g : GL (Fin 3) K, z * g = g * z := by
      intro z hz g
      exact (CFSG.RankThree.PartTwo.Sec4.commute_of_mem_statedScalars (hZst hz) g).symm
    have hZC : Z ≤ C := by
      rintro z hz
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [CFSG.RankThree.PartTwo.Sec4.mem_slPi_true (2 ^ 2)]
        rcases hz with ⟨s, hs, rfl⟩
        change (↑s : Matrix (Fin 3) (Fin 3) K).det = 1
        exact s.2
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hZcentral z hz y
    have hZker : C ⊓ Subgroup.centralizer ({w} : Set (GL (Fin 3) K)) = Z := by
      have hCZ : C ⊓ Subgroup.centralizer ({w} : Set (GL (Fin 3) K)) =
          CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K ⊓
            Subgroup.centralizer ({y, w} : Set (GL (Fin 3) K)) := by
        rw [hC]
        ext a
        simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
        tauto
      have hcard' : Nat.card ↥(C ⊓ Subgroup.centralizer ({w} : Set (GL (Fin 3) K))) = 3 := by
        rw [hCZ, hcard3]
      have hZle : Z ≤ C ⊓ Subgroup.centralizer ({w} : Set (GL (Fin 3) K)) := by
        intro z hz
        exact Subgroup.mem_inf.2 ⟨hZC hz,
          Subgroup.mem_centralizer_singleton_iff.2 (hZcentral z hz w)⟩
      exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [hcard', hZcard])).symm
    have hwdet : (w : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      (CFSG.RankThree.PartTwo.Sec4.mem_slPi_true (2 ^ 2)).1 hwL
    have hwM : w ∈ CFSG.RankThree.PartTwo.Sec4.centMod
        (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K) y := by
      rw [hcent']
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    have hcomm : ∀ c : C, ⁅w, (c : GL (Fin 3) K)⁆ ∈ Z := by
      intro c
      have hcL : (c : GL (Fin 3) K) ∈
          CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K := (Subgroup.mem_inf.1 c.2).1
      have hcdet : ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
        (CFSG.RankThree.PartTwo.Sec4.mem_slPi_true (2 ^ 2)).1 hcL
      have hcM : (c : GL (Fin 3) K) ∈ CFSG.RankThree.PartTwo.Sec4.centMod
          (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K) y :=
        (CFSG.RankThree.PartTwo.Sec4.centralizer_le_centMod
          (CFSG.RankThree.PartTwo.Sec4.slPi true 3 (2 ^ 2) K) y) c.2
      set s_c : Matrix.SpecialLinearGroup (Fin 3) K := ⟨(c : GL (Fin 3) K), hcdet⟩ with hsc
      set s_w : Matrix.SpecialLinearGroup (Fin 3) K := ⟨w, hwdet⟩ with hsw
      have hsc_gl : Matrix.SpecialLinearGroup.toGL s_c = (c : GL (Fin 3) K) := Units.ext rfl
      have hsw_gl : Matrix.SpecialLinearGroup.toGL s_w = w := Units.ext rfl
      have hc_fix : β (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c := by
        rw [← hβy]
        exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34.conjAut_fix_of_mem_centMod
          hK (A := y) (z := 1) (by exact Subgroup.one_mem _) (by simpa using hcM) hsc_gl
      have hw_fix : β (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w := by
        rw [← hβy]
        exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34.conjAut_fix_of_mem_centMod
          hK (A := y) (z := 1) (by exact Subgroup.one_mem _) (by simpa using hwM) hsw_gl
      have key : (⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c, hc_fix⟩ :
            ↥(CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.autFixed β)) *
          ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w, hw_fix⟩ =
          ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w, hw_fix⟩ *
          ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c, hc_fix⟩ :=
        hnab _ _
      have hproj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c *
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w := by
        have h := congrArg Subtype.val key
        change (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c) *
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w) =
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_w) *
              (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K s_c) at h
        exact h.symm
      have hone : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K
          (s_w * s_c * s_w⁻¹ * s_c⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hproj]
        group
      have hscalar : s_w * s_c * s_w⁻¹ * s_c⁻¹ ∈
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K :=
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff.1 hone
      refine ⟨s_w * s_c * s_w⁻¹ * s_c⁻¹, hscalar, ?_⟩
      simp only [hsw_gl, hsc_gl, map_mul, map_inv, commutatorElement_def]
    exact false_of_commutator_mem_center C Z w hcardC21 hZcard hZC hZker hZcentral hcomm


theorem fixed_subgroup_of_outer_orderThree_psl_three_four {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2) (α : MulAut L) (hα : orderOf α = 3)
    (hout : α ∉ inner L) :
    Nonempty (↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id L)) ≃*
        alternatingGroup (Fin 5)) ∨
      (Nat.card ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id L)) = 21 ∧
        ∃ a b : ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id L)), a * b ≠ b * a) := by
  obtain ⟨K, hfield, hfin, hK, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  let β : MulAut (projectiveSL 3 K) := MulAut.congr φ α
  have hβ : orderOf β = 3 := by
    change orderOf (MulAut.congr φ α) = 3
    rw [MulEquiv.orderOf_eq, hα]
  have hout' : β ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    change MulAut.congr φ α ∉ _
    intro h
    apply hout
    have hinnerimg : (inner L).map (MulAut.congr φ).toMonoidHom =
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ
    have hmem : MulAut.congr φ α ∈ (inner L).map (MulAut.congr φ).toMonoidHom := by
      rw [hinnerimg]; exact h
    obtain ⟨γ, hγ, hγα⟩ := hmem
    rw [(MulAut.congr φ).injective hγα] at hγ
    exact hγ
  have hmain := fixed_subgroup_of_outer_orderThree_projectiveSL hK4 β hβ hout'
  have heq := eqLocusMulEquivCongr φ α
  rcases hmain with h | ⟨hcard, a, b, hab⟩
  · rcases h with ⟨e⟩
    left
    exact ⟨heq.trans e⟩
  · right
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr heq.toEquiv]; exact hcard
    · refine ⟨heq.symm a, heq.symm b, fun h => hab ?_⟩
      have h' := congrArg (fun x => heq x) h
      simp only [map_mul, MulEquiv.apply_symm_apply] at h'
      exact h'


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
