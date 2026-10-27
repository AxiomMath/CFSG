module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreStruct
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle
public import Certificates.Certificate8064
public import Certificates.Certificate13659
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelSmall
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmall
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcChar2
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovQ8
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Eight
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit
import CFSG.Blueprint.LieModelAPI
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.Models.Transport
import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (iform)

private theorem conj_mem_model_of_mem_componentRootSpan_of_frobGL_fixed
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {σ : L ≃+* L} {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) ↔
      z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ i))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {y : ModGL τ L} (hy : y ∈ rootSpan τ L (componentRoots χ i))
    (hfix : frobGL σ y = y) :
    z * y * z⁻¹ ∈ rootSpan τ L (componentRoots χ i) ⊓ D.model := by
  have hS : z * y * z⁻¹ ∈ rootSpan τ L (componentRoots χ i) := (hnorm y).1 hy
  refine Subgroup.mem_inf.2 ⟨hS, ?_⟩
  have hstep : D.n * D.Φ (z * y * z⁻¹) * D.n⁻¹ = z * y * z⁻¹ := by
    have h := hz y hy
    rwa [hfix] at h
  exact (LangDatum.mem_model (D := D)).2 ⟨rootSpan_le_adjointGroup L _ hS, hstep⟩

private theorem mem_componentRootSpan_and_frobGL_fixed_of_mem_model
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {σ : L ≃+* L} {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) ↔
      z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ i))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {x : ModGL τ L} (hx : x ∈ rootSpan τ L (componentRoots χ i) ⊓ D.model) :
    z⁻¹ * x * z ∈ rootSpan τ L (componentRoots χ i) ∧
      frobGL σ (z⁻¹ * x * z) = z⁻¹ * x * z := by
  have hzx : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
  have hyS : z⁻¹ * x * z ∈ rootSpan τ L (componentRoots χ i) :=
    (hnorm _).2 (by rw [hzx]; exact hx.1)
  have hstep : D.n * D.Φ x * D.n⁻¹ = x := (LangDatum.mem_model (D := D)).1 hx.2 |>.2
  constructor
  · exact hyS
  · have h := hz (z⁻¹ * x * z) hyS
    have h1 : iterHom D.step 1 x = x := hstep
    rw [hzx, h1] at h
    exact (mul_left_cancel (mul_right_cancel (hzx.trans h))).symm

private theorem commutator_inf_model_le_map_commutator_CQ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (D : LangDatum τ L)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {σ : L ≃+* L} (hσ : ∀ c, σ c = c ^ 2) {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) ↔
      z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ i))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    ⁅rootSpan τ L (componentRoots χ i) ⊓ D.model,
        rootSpan τ L (componentRoots χ i) ⊓ D.model⁆ ≤
      Subgroup.map (MulAut.conj z).toMonoidHom ⁅CQ σ i, CQ σ i⁆ := by
  classical
  have hs : ∃ s : Lˣ, s ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h' | h'
    · simp [sub_eq_zero.1 h']
    · simp [eq_neg_of_add_eq_zero_left h']
  have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
    intro d hd hd0
    have h2 : d ^ 2 = d := by rw [← hσ, hd]
    have h3 : d * (d - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hd0
    · exact sub_eq_zero.1 h
  rw [Subgroup.commutator_le]
  intro x hx x' hx'
  generalize hy : z⁻¹ * x * z = y
  generalize hy' : z⁻¹ * x' * z = y'
  have hzx : z * y * z⁻¹ = x := by rw [← hy]; group
  have hzx' : z * y' * z⁻¹ = x' := by rw [← hy']; group
  obtain ⟨hyS, hyfix⟩ := mem_componentRootSpan_and_frobGL_fixed_of_mem_model D i hnorm hz hx
  obtain ⟨hyS', hyfix'⟩ := mem_componentRootSpan_and_frobGL_fixed_of_mem_model D i hnorm hz hx'
  rw [hy] at hyS hyfix
  rw [hy'] at hyS' hyfix'
  have hyU : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    rw [unionRootSpan, unionRoots_singleton]; exact hyS
  have hyU' : y' ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
    rw [unionRootSpan, unionRoots_singleton]; exact hyS'
  have hcm := commutator_mem_commutator_CQ (i := i) (σ := σ) hs hF
    (Z := ⊥) (by intro w hw a _; rw [Subgroup.mem_bot.1 hw]; simp)
    hyU hyU' (by rw [Subgroup.mem_bot, hyfix, mul_inv_cancel])
    (by rw [Subgroup.mem_bot, hyfix', mul_inv_cancel])
  change y * y' * y⁻¹ * y'⁻¹ ∈ ⁅CQ σ i, CQ σ i⁆ at hcm
  change x * x' * x⁻¹ * x'⁻¹ ∈
    Subgroup.map (MulAut.conj z).toMonoidHom ⁅CQ σ i, CQ σ i⁆
  have hxy : x = (MulAut.conj z) y := by rw [MulAut.conj_apply, ← hy]; group
  have hxy' : x' = (MulAut.conj z) y' := by rw [MulAut.conj_apply, ← hy']; group
  have hgoal : x * x' * x⁻¹ * x'⁻¹ =
      (MulAut.conj z) (y * y' * y⁻¹ * y'⁻¹) := by
    rw [hxy, hxy']
    simp only [map_mul, map_inv]
  rw [hgoal]
  exact Subgroup.mem_map_of_mem _ hcm

private theorem map_conj_CQ_le_twoElemGp
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (D : LangDatum τ L)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {σ : L ≃+* L} {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) ↔
      z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ i))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    Subgroup.map (MulAut.conj z).toMonoidHom (CQ σ i) ≤
      twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model) := by
  rw [Subgroup.map_le_iff_le_comap, CQ]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨γ, hγ, c, hc, rfl⟩
  change (MulAut.conj z) (pinnedX τ L γ c) ∈
    twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model)
  rw [MulAut.conj_apply]
  rw [unionRoots_singleton] at hγ
  have hX : pinnedX τ L γ c ∈ rootSpan τ L (componentRoots χ i) :=
    pinnedX_mem_rootSpan hγ c
  have hfix : frobGL σ (pinnedX τ L γ c) = pinnedX τ L γ c := by
    rw [frobGL_pinnedX, hc]
  have hmem := conj_mem_model_of_mem_componentRootSpan_of_frobGL_fixed D i hnorm hz hX hfix
  have hord : orderOf (z * pinnedX τ L γ c * z⁻¹) = orderOf (pinnedX τ L γ c) := by
    rw [← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective _
  refine Subgroup.subset_closure ⟨hmem, ?_⟩
  have hsq : pinnedX τ L γ c * pinnedX τ L γ c = 1 := by
    have hcc : c + c = 0 := CharTwo.add_self_eq_zero c
    rw [← pinnedX_add, hcc, pinnedX_zero]
  have hdvd : orderOf (pinnedX τ L γ c) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by rw [hord, h, pow_zero]⟩
  · exact ⟨1, by rw [hord, h, pow_one]⟩

theorem commutator_twoElemGp_eq_of_untwist
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {σ : L ≃+* L} (hσ : ∀ c, σ c = c ^ 2) {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) ↔
      z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ i))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    ⁅twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model),
        twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model)⁆ =
      Subgroup.map (MulAut.conj z).toMonoidHom
        (Subgroup.map (baseChangeGL (fixSubfield σ).subtype)
          ⁅componentRootSpan (fixSubfield σ) χ i, componentRootSpan (fixSubfield σ) χ i⁆) ∧
    ⁅rootSpan τ L (componentRoots χ i) ⊓ D.model, rootSpan τ L (componentRoots χ i) ⊓ D.model⁆ ≤
      ⁅twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model),
        twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model)⁆ ∧
    Subgroup.map (MulAut.conj z).toMonoidHom (CQ σ i) ≤
      twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model) := by
  have hCQeq : CQ σ i =
      Subgroup.map (baseChangeGL (fixSubfield σ).subtype)
        (componentRootSpan (fixSubfield σ) χ i) := CQ_eq_map i σ
  have hcommCQ : Subgroup.map (baseChangeGL (fixSubfield σ).subtype)
      ⁅componentRootSpan (fixSubfield σ) χ i, componentRootSpan (fixSubfield σ) χ i⁆ =
      ⁅CQ σ i, CQ σ i⁆ := by
    rw [Subgroup.map_commutator, ← hCQeq]
  have hB := commutator_inf_model_le_map_commutator_CQ D i hσ hnorm hz
  have hC := map_conj_CQ_le_twoElemGp D i hnorm hz
  have hle : Subgroup.map (MulAut.conj z).toMonoidHom ⁅CQ σ i, CQ σ i⁆ ≤
      ⁅twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model),
        twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hC hC
  have hI_le : ⁅twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model),
        twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model)⁆ ≤
      ⁅rootSpan τ L (componentRoots χ i) ⊓ D.model,
        rootSpan τ L (componentRoots χ i) ⊓ D.model⁆ := by
    have hIM : twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model) ≤
        rootSpan τ L (componentRoots χ i) ⊓ D.model := by
      rw [twoElemGp]
      exact (Subgroup.closure_le _).2 fun x hx => hx.1
    exact Subgroup.commutator_mono hIM hIM
  refine ⟨?_, hB.trans hle, hC⟩
  rw [hcommCQ]
  exact le_antisymm (hI_le.trans hB) hle

private lemma finite_card_fixSubfield_of_sq {L : Type} [Field L] {σ : L ≃+* L}
    (hσ : ∀ c, σ c = c ^ 2) :
    Finite (fixSubfield σ) ∧ Nat.card (fixSubfield σ) ≤ 3 := by
  have hset : (fixSubfield σ : Set L) = ({0, 1} : Set L) := by
    ext c
    change σ c = c ↔ c ∈ ({0, 1} : Set L)
    rw [hσ]
    constructor
    · intro h
      have h' : c * (c - 1) = 0 := by
        rw [mul_sub, mul_one, sub_eq_zero]
        simpa [pow_two] using h
      rcases mul_eq_zero.1 h' with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.1 h1)
    · rintro (rfl | rfl)
      · simp
      · norm_num
  have hfin : (fixSubfield σ : Set L).Finite := by
    rw [hset]
    exact (Set.finite_singleton (1 : L)).insert 0
  refine ⟨hfin.to_subtype, ?_⟩
  have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
    Nat.card_coe_set_eq (fixSubfield σ : Set L)
  rw [h1, hset, Set.ncard_pair (zero_ne_one : (0 : L) ≠ 1)]
  norm_num

private lemma isSolvable_map_conj_baseChange_commutator
    {τ : Tag} {L : Type} [Field L]
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (K : Subfield L) (i : KernelComponent χ) {z : ModGL τ L}
    (hC : Group.IsSolvable ↥(componentRootSpan K χ i)) :
    Group.IsSolvable ↥(Subgroup.map (MulAut.conj z).toMonoidHom
      (Subgroup.map (baseChangeGL K.subtype)
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆)) := by
  have := hC
  have hCC : Group.IsSolvable
      ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (Subgroup.commutator_le_self (componentRootSpan K χ i)))
      (Subgroup.inclusion_injective _)
  let eB : ↥⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ ≃*
      ↥(Subgroup.map (baseChangeGL K.subtype)
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) :=
    Subgroup.equivMapOfInjective _ (baseChangeGL K.subtype)
      (baseChangeGL_injective K.subtype)
  have hB : Group.IsSolvable
      ↥(Subgroup.map (baseChangeGL K.subtype)
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) :=
    Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective
  let eZ : ↥(Subgroup.map (baseChangeGL K.subtype)
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆) ≃*
      ↥(Subgroup.map (MulAut.conj z).toMonoidHom
        (Subgroup.map (baseChangeGL K.subtype)
          ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆)) :=
    Subgroup.equivMapOfInjective _ _ (MulAut.conj z).injective
  exact Group.isSolvable_of_surjective (f := eZ.toMonoidHom) eZ.surjective

theorem isSolvable_twoElemGp_of_rankOne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {σ : L ≃+* L} (hσ : ∀ c, σ c = c ^ 2) {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) ↔
      z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ i))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      iterHom D.step 1 (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (h2 : (componentRoots χ i).ncard = 2) :
    IsSolvable ↥(twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model)) := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hrank :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.forall_eq_or_eq_neg_of_ncard_two hΨ h2
  obtain ⟨hKfin, hK⟩ := finite_card_fixSubfield_of_sq hσ
  have := hKfin
  have hCsolv : Group.IsSolvable ↥(componentRootSpan (fixSubfield σ) χ i) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_componentRootSpan_of_rank_one
      hK i hrank
  obtain ⟨hII, hMM, -⟩ := commutator_twoElemGp_eq_of_untwist D i hσ hnorm hz
  have hTsolv := isSolvable_map_conj_baseChange_commutator (fixSubfield σ) i (z := z) hCsolv
  have hMMT : ⁅rootSpan τ L (componentRoots χ i) ⊓ D.model,
      rootSpan τ L (componentRoots χ i) ⊓ D.model⁆ ≤
      Subgroup.map (MulAut.conj z).toMonoidHom
        (Subgroup.map (baseChangeGL (fixSubfield σ).subtype)
          ⁅componentRootSpan (fixSubfield σ) χ i,
            componentRootSpan (fixSubfield σ) χ i⁆) :=
    hMM.trans (le_of_eq hII)
  have hMsolv : Group.IsSolvable
      ↥(rootSpan τ L (componentRoots χ i) ⊓ D.model) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isSolvable_of_commutator_le _ _ hMMT
  have hle : twoElemGp (rootSpan τ L (componentRoots χ i) ⊓ D.model) ≤
      rootSpan τ L (componentRoots χ i) ⊓ D.model := by
    rw [twoElemGp]
    exact (Subgroup.closure_le _).2 fun _ hx => hx.1
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end CFSG.StandardType.LieCore
