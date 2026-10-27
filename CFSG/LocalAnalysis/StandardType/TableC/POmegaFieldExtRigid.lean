module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaLeafDefs
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaNoFieldExt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideUniType
public import CFSG.Adapters.StatedQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma117
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightSpGood
public import CFSG.RankThree.PartOne.TCP.AlModel
public import CFSG.Goldschmidt.Steps.Sec82Tools
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
public import CFSG.RankThree.PartOne.TCP.AlSL2

public section

namespace CFSG.StandardType.TableC

open Module QuadraticMap
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.RankThree.Classical2
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks

private theorem j2l_commutator_le_self {U : Type} [Group U] (G : Subgroup U) :
    ⁅G, G⁆ ≤ G := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
    (Subgroup.inv_mem _ h₂)

private theorem j2l_not_isSolvable_GL {U : Type} [Group U] {G J' : Subgroup U}
    (hJ' : IsComponentOf J' ⁅G, G⁆) {m : ℕ} {E : Type} [Field E] [Fintype E]
    (eG : ↥G ≃* GL (Fin m) E) : ¬ Group.IsSolvable (GL (Fin m) E) := by
  intro hGL
  haveI : Group.IsSolvable (GL (Fin m) E) := hGL
  have hG : Group.IsSolvable ↥G :=
    Group.isSolvable_of_isSolvable_injective (f := eG.toMonoidHom) eG.injective
  haveI : Group.IsSolvable ↥G := hG
  have hle : ⁅G, G⁆ ≤ G := j2l_commutator_le_self G
  have hJ'sol : Group.IsSolvable ↥J' :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (le_trans hJ'.1 hle))
      (Subgroup.inclusion_injective (le_trans hJ'.1 hle))
  have hq : CFSG.IsQuasisimple ↥J' :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J').mp hJ'.2.2
  haveI : Nontrivial ↥J' := CFSG.LocalCores.isQuasisimple_nontrivial hq
  haveI : Group.IsPerfect ↥J' := hq.1
  exact (Group.IsPerfect.not_isSolvable ↥J') hJ'sol

private theorem j2l_GL_solvable_of_small {E : Type} [Field E] [Fintype E] {m a : ℕ}
    (hE : Fintype.card E = 2 ^ a)
    (hbad : ¬ (2 ≤ m ∧ (3 ≤ m ∨ 4 ≤ Fintype.card E))) :
    Group.IsSolvable (GL (Fin m) E) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exact CFSG.LocalAnalysis.GLTheoremA.H1431c.lieSEightSp_isSolvable_gl_of_le_one
      (E := E) (by omega)
  · have hm2 : m = 2 := by
      by_contra hne
      have hm3 : 3 ≤ m := by omega
      exact hbad ⟨hm, Or.inl hm3⟩
    subst hm2
    have hc4 : Fintype.card E < 4 := by
      by_contra hge
      exact hbad ⟨le_refl 2, Or.inr (not_lt.mp hge)⟩
    have hc : Nat.card E = 2 ∨ Nat.card E = 3 := by
      left
      have ha : a = 1 := by
        rcases Nat.lt_or_ge a 2 with hlt | hge
        · rcases (show a = 0 ∨ a = 1 by omega) with h0 | h1
          · exfalso
            have h2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
            rw [hE, h0, pow_zero] at h2
            omega
          · exact h1
        · exfalso
          have h2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
          have h4 : 4 ≤ 2 ^ a := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hge
          rw [hE] at hc4
          omega
      rw [Nat.card_eq_fintype_card, hE, ha, pow_one]
    exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
      E hc

private theorem j2l_solvable_small {U : Type} [Group U] {G J' : Subgroup U}
    (hJ' : IsComponentOf J' ⁅G, G⁆) {m a : ℕ} {E : Type} [Field E] [Fintype E]
    (hE : Fintype.card E = 2 ^ a) (eG : ↥G ≃* GL (Fin m) E) :
    2 ≤ m ∧ (3 ≤ m ∨ 4 ≤ Fintype.card E) := by
  by_contra hbad
  exact (j2l_not_isSolvable_GL hJ' eG) (j2l_GL_solvable_of_small hE hbad)

private theorem j2l_component_eq {U : Type} [Group U] {G J' : Subgroup U}
    (hJ' : IsComponentOf J' ⁅G, G⁆) (hHqs : CFSG.IsQuasisimple ↥⁅G, G⁆) :
    J' = ⁅G, G⁆ := by
  have hOpenH : CFSG.Open.IsQuasisimple ↥⁅G, G⁆ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥⁅G, G⁆).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
        ↥⁅G, G⁆).mpr hHqs)
  have hOpenJ : CFSG.Open.IsComponentOf J' ⁅G, G⁆ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open J' ⁅G, G⁆).mp hJ'
  exact CFSG.LocalAnalysis.GLTheoremA.S11.y10xD_eq_of_qs hOpenH hOpenJ

private theorem j2l_lieModel_SL {U X : Type} [Group U] [Group X] (ψ : U →* X)
    (hψ : Function.Injective ψ) {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆)
    {m a : ℕ} {E : Type} [Field E] [Fintype E] (hE : Fintype.card E = 2 ^ a)
    (eG : ↥G ≃* GL (Fin m) E) (hm2 : 2 ≤ m) (hmcond : 3 ≤ m ∨ 4 ≤ Fintype.card E) :
    CFSG.Blueprint.LieModel
      (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL m 2 a := by
  have hcond : 3 ≤ m ∨ ∃ s : Finset E, s.card = 4 := by
    rcases hmcond with h3 | h4
    · exact Or.inl h3
    · refine Or.inr ?_
      have h4' : 4 ≤ (Finset.univ : Finset E).card := by
        rw [Finset.card_univ]
        exact h4
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4'
      exact ⟨s, hs⟩
  have hcomm : commutator (GL (Fin m) E) = CFSG.Open.StatedSL m E :=
    CFSG.StandardType.GGNbrLSideKit.commutator_generalLinear_eq_statedSL hm2 hcond
  have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) E) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hm2 hcond
  have hStated : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSL m E) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E) hSL
  have hB : CFSG.IsQuasisimple ↥(commutator (GL (Fin m) E)) := by
    rw [hcomm]; exact hStated
  have hHqs : CFSG.IsQuasisimple ↥⁅G, G⁆ :=
    (CFSG.StandardType.GGNbrLSideKit.quasisimple_commutator_iff eG).2 hB
  have hK : Nat.card E = 2 ^ a := by rw [Nat.card_eq_fintype_card, hE]
  have ha1 : 1 ≤ a := by
    have h2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
    by_contra h
    have h0 : a = 0 := by omega
    rw [hE, h0, pow_zero] at h2
    omega
  have hRefGG : CFSG.Blueprint.LieModel
      (↥⁅G, G⁆ ⧸ Subgroup.center ↥⁅G, G⁆) .PSL m 2 a :=
    CFSG.StandardType.ggNbrLSideSp_typeGL hK ha1 eG hHqs
  have hJeq : J' = ⁅G, G⁆ := j2l_component_eq hJ' hHqs
  have hRefJ' : CFSG.Blueprint.LieModel
      (↥J' ⧸ Subgroup.center ↥J') .PSL m 2 a := by
    rw [hJeq]; exact hRefGG
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv
    (J'.equivMapOfInjective ψ hψ) hRefJ'

theorem fieldExt_lin_lt
    {U X : Type} [Group U] [Group X] (ψ : U →* X) (hψ : Function.Injective ψ)
    {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆) {m a f : ℕ} {E : Type} [Field E]
    [Fintype E] (hE : Fintype.card E = 2 ^ a) (eG : ↥G ≃* GL (Fin m) E) {t : StatedLieTag}
    (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f) : f < a := by
  obtain ⟨hm2, hmcond⟩ := j2l_solvable_small hJ' hE eG
  obtain ⟨t', m', f', hff', hM', -⟩ := hFE
  have hRef : CFSG.Blueprint.LieModel
      (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL m 2 a :=
    j2l_lieModel_SL ψ hψ hJ' hE eG hm2 hmcond
  have hf'a : f' = a := by
    by_cases hm : m = 2
    · subst hm
      exact CFSG.ComponentClassification.CatLeafProof.fieldExponent_eq_of_isChar2LieShape
        hRef (Or.inl ⟨rfl, rfl⟩) hM'
    · have hm3 : 3 ≤ m := by omega
      exact (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hm3 hRef hM').2.2
  omega


section UnitaryHelpers

open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.Burgoyne.O

private lemma j2u_one_le_of_card {E : Type} [Field E] [Fintype E] {a : ℕ}
    (hE : Fintype.card E = (2 ^ a) ^ 2) : 1 ≤ a := by
  by_contra h
  have ha : a = 0 := by omega
  subst ha
  norm_num at hE
  have := Fintype.one_lt_card (α := E)
  omega

private lemma j2u_GUFull_eq_primeFormUnitary {E : Type} [Field E] {m a : ℕ}
    (h : UnitaryFieldData 2 a E) :
    GUFull m (2 ^ a) E = primeFormUnitary h (idGram E m) := by
  have hbar : ∀ x : E, h.bar x = x ^ (2 ^ a) := fun x => h.bar_apply x
  apply le_antisymm
  · rw [GUFull, Subgroup.closure_le]
    intro A hA
    rw [Set.mem_setOf_eq] at hA
    change A ∈ primeFormUnitary h (idGram E m)
    rw [mem_primeFormUnitary]
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ (2 ^ a)) := by
      ext i j
      simp only [Matrix.map_apply, hbar]
    rw [hmap]
    simpa only [idGram, Units.val_one, Matrix.mul_one] using hA
  · intro A hA
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq]
    have hA' := (mem_primeFormUnitary.mp hA)
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ (2 ^ a)) := by
      ext i j
      simp only [Matrix.map_apply, hbar]
    rw [idGram, Units.val_one, Matrix.mul_one] at hA'
    rwa [hmap] at hA'

private lemma j2u_uGrp_eq_primeFormUnitary {E : Type} [Field E] {m a : ℕ}
    (h : UnitaryFieldData 2 a E) :
    uGrp h.bar (1 : Matrix (Fin m) (Fin m) E) = primeFormUnitary h (idGram E m) := by
  ext Y
  rw [mem_uGrp, mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]

private lemma j2u_unitarySU_le_GUFull {E : Type} [Field E] {m a : ℕ}
    (h : UnitaryFieldData 2 a E) : unitarySU 2 a E m ≤ GUFull m (2 ^ a) E := by
  rw [j2u_GUFull_eq_primeFormUnitary h]
  intro x hx
  rw [mem_unitarySU_iff h] at hx
  rw [mem_primeFormUnitary]
  simpa only [idGram, Units.val_one, Matrix.mul_one] using hx.2

private lemma j2u_comm_le_SU {E : Type} [Field E] {m a : ℕ}
    (h : UnitaryFieldData 2 a E) :
    ⁅GUFull m (2 ^ a) E, GUFull m (2 ^ a) E⁆ ≤ unitarySU 2 a E m := by
  rw [j2u_GUFull_eq_primeFormUnitary h, ← j2u_uGrp_eq_primeFormUnitary h]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [← Matrix.GeneralLinearGroup.val_det_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), Units.val_one]
  · have hm : ⁅x, y⁆ ∈ uGrp h.bar (1 : Matrix (Fin m) (Fin m) E) :=
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    rw [mem_uGrp, Matrix.mul_one] at hm
    exact hm

private theorem j2u_commutator_GU_of_qs {E : Type} [Field E] {m a : ℕ}
    (h : UnitaryFieldData 2 a E)
    (hq : CFSG.IsQuasisimple ↥(unitarySU 2 a E m)) :
    ⁅GUFull m (2 ^ a) E, GUFull m (2 ^ a) E⁆ = unitarySU 2 a E m := by
  apply le_antisymm (j2u_comm_le_SU h)
  calc unitarySU 2 a E m = ⁅unitarySU 2 a E m, unitarySU 2 a E m⁆ :=
        (CFSG.ComponentClassification.Burgoyne.PSL.commutator_eq_self_of_isQuasisimple hq).symm
    _ ≤ ⁅GUFull m (2 ^ a) E, GUFull m (2 ^ a) E⁆ :=
        Subgroup.commutator_mono (j2u_unitarySU_le_GUFull h) (j2u_unitarySU_le_GUFull h)

private noncomputable def j2u_commIso {U E : Type} [Group U] [Field E] {m a : ℕ}
    {G : Subgroup U} (eG : ↥G ≃* ↥(GUFull m (2 ^ a) E)) :
    ↥⁅G, G⁆ ≃* ↥⁅GUFull m (2 ^ a) E, GUFull m (2 ^ a) E⁆ := by
  have htop : (⊤ : Subgroup ↥G).map G.subtype = G := by
    simp only [← MonoidHom.range_eq_map, Subgroup.subtype_range]
  have htopU : (⊤ : Subgroup ↥(GUFull m (2 ^ a) E)).map
      (GUFull m (2 ^ a) E).subtype = GUFull m (2 ^ a) E := by
    simp only [← MonoidHom.range_eq_map, Subgroup.subtype_range]
  have hCG : (⁅(⊤ : Subgroup ↥G), (⊤ : Subgroup ↥G)⁆).map G.subtype = ⁅G, G⁆ := by
    simp only [Subgroup.map_commutator, htop]
  have hCGU : (⁅(⊤ : Subgroup ↥(GUFull m (2 ^ a) E)),
      (⊤ : Subgroup ↥(GUFull m (2 ^ a) E))⁆).map
      (GUFull m (2 ^ a) E).subtype = ⁅GUFull m (2 ^ a) E, GUFull m (2 ^ a) E⁆ := by
    simp only [Subgroup.map_commutator, htopU]
  have hmap : (⁅(⊤ : Subgroup ↥G), (⊤ : Subgroup ↥G)⁆).map eG.toMonoidHom =
      (⁅(⊤ : Subgroup ↥(GUFull m (2 ^ a) E)),
        (⊤ : Subgroup ↥(GUFull m (2 ^ a) E))⁆) := by
    rw [Subgroup.map_commutator]
    congr 1 <;> exact Subgroup.map_equiv_top eG
  exact (MulEquiv.subgroupCongr hCG).symm.trans
    ((Subgroup.equivMapOfInjective _ G.subtype (Subgroup.subtype_injective G)).symm.trans
      ((Subgroup.equivMapOfInjective _ eG.toMonoidHom eG.injective).trans
        ((MulEquiv.subgroupCongr hmap).trans
          ((Subgroup.equivMapOfInjective _ (GUFull m (2 ^ a) E).subtype
              (Subgroup.subtype_injective (GUFull m (2 ^ a) E))).trans
            (MulEquiv.subgroupCongr hCGU)))))

private lemma j2u_map_center {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ g
    obtain ⟨w, rfl⟩ := e.surjective g
    calc e w * e y = e (w * y) := (map_mul e w y).symm
      _ = e (y * w) := by rw [hy w]
      _ = e y * e w := map_mul e y w
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro g
    apply e.injective
    calc e (g * e.symm x) = e g * e (e.symm x) := map_mul e g _
      _ = e g * x := by rw [e.apply_symm_apply]
      _ = x * e g := hx (e g)
      _ = e (e.symm x) * e g := by rw [e.apply_symm_apply]
      _ = e (e.symm x * g) := (map_mul e _ g).symm

private noncomputable def j2u_commIsoSU {U E : Type} [Group U] [Field E] {m a : ℕ}
    (h : UnitaryFieldData 2 a E) {G : Subgroup U}
    (eG : ↥G ≃* ↥(GUFull m (2 ^ a) E))
    (hq : CFSG.IsQuasisimple ↥(unitarySU 2 a E m)) :
    ↥⁅G, G⁆ ≃* ↥(unitarySU 2 a E m) :=
  (j2u_commIso eG).trans (MulEquiv.subgroupCongr (j2u_commutator_GU_of_qs h hq))

private theorem j2u_component_eq {U E : Type} [Group U] [Field E] {m a : ℕ}
    {G J' : Subgroup U} (eG : ↥G ≃* ↥(GUFull m (2 ^ a) E))
    (h : UnitaryFieldData 2 a E) (hq : CFSG.IsQuasisimple ↥(unitarySU 2 a E m))
    (hJ' : CFSG.Assembly.IsComponentOf J' ⁅G, G⁆) : J' = ⁅G, G⁆ := by
  have hq' : CFSG.Open.IsQuasisimple ↥(unitarySU 2 a E m) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq)
  have hX : CFSG.Open.IsQuasisimple ↥⁅G, G⁆ :=
    CFSG.Goldschmidt.Sec82.isQuasisimple_of_mulEquiv
      (j2u_commIsoSU h eG hq).symm hq'
  have hJq : CFSG.Open.IsQuasisimple ↥J' :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥J').mp hJ'.2.2
  have hKq : CFSG.Open.IsQuasisimple ↥(J'.subgroupOf ⁅G, G⁆) :=
    CFSG.Goldschmidt.Sec82.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hJ'.1).symm hJq
  have hKsub : CFSG.Open.IsSubnormal (J'.subgroupOf ⁅G, G⁆) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib _).mpr
        (CFSG.Assembly.IsSubnormal.subgroupOf hJ'.2.1))
  have hK : CFSG.Open.IsComponentOf (J'.subgroupOf ⁅G, G⁆) ⊤ :=
    ⟨le_top, hKsub, hKq⟩
  have htop : J'.subgroupOf ⁅G, G⁆ = ⊤ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313.eq_top_of_isComponentOf_quasisimple hX hK
  exact le_antisymm hJ'.1 (Subgroup.subgroupOf_eq_top.mp htop)

private noncomputable def j2u_ePSU {U X E : Type} [Group U] [Group X] [Field E] [Fintype E]
    {m a : ℕ} (h : UnitaryFieldData 2 a E) (ψ : U →* X) (hψ : Function.Injective ψ)
    {G J' : Subgroup U} (eG : ↥G ≃* ↥(GUFull m (2 ^ a) E))
    (hq : CFSG.IsQuasisimple ↥(unitarySU 2 a E m))
    (hJ' : CFSG.Assembly.IsComponentOf J' ⁅G, G⁆) :
    (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) ≃* unitaryPSU h m := by
  have hJ'eq : J' = ⁅G, G⁆ := j2u_component_eq eG h hq hJ'
  have hα : ↥J' ≃* ↥(unitarySU 2 a E m) :=
    (MulEquiv.subgroupCongr hJ'eq).trans (j2u_commIsoSU h eG hq)
  let e : ↥(J'.map ψ) ≃* ↥(unitarySU 2 a E m) :=
    (Subgroup.equivMapOfInjective J' ψ hψ).symm.trans hα
  have he : (Subgroup.center ↥(J'.map ψ)).map e.toMonoidHom = unitaryScalars h m := by
    rw [j2u_map_center e]
    exact CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars h m
  exact QuotientGroup.congr (G' := Subgroup.center ↥(J'.map ψ)) (H' := unitaryScalars h m) e he

private lemma j2u_gramSU_eq_unitarySU {E : Type} [Field E] {a : ℕ}
    (h : UnitaryFieldData 2 a E) (n : ℕ) :
    gramSU h (idGram E n) = unitarySU 2 a E n := by
  ext g
  rw [mem_gramSU_iff_unitary, mem_primeFormUnitary, mem_unitarySU_iff h]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  tauto

private noncomputable def j2u_unitarySU_two_iso_SL2 {E : Type} [Field E] {a : ℕ}
    (h : UnitaryFieldData 2 a E) :
    ↥(unitarySU 2 a E 2) ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  (MulEquiv.subgroupCongr (j2u_gramSU_eq_unitarySU h 2)).symm.trans
    (Classical.choice (CFSG.RankThree.PartOne.KFU.nonempty_gramSU_two_mulEquiv_SL2 h))

private theorem j2u_solvable_J' {U E : Type} [Group U] [Field E] {m a : ℕ}
    (h : UnitaryFieldData 2 a E) {G J' : Subgroup U}
    (eG : ↥G ≃* ↥(GUFull m (2 ^ a) E))
    (hJ' : CFSG.Assembly.IsComponentOf J' ⁅G, G⁆)
    (hsol : Group.IsSolvable ↥(unitarySU 2 a E m)) : Group.IsSolvable ↥J' := by
  haveI : Group.IsSolvable ↥(unitarySU 2 a E m) := hsol
  haveI : Group.IsSolvable ↥⁅GUFull m (2 ^ a) E, GUFull m (2 ^ a) E⁆ :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (j2u_comm_le_SU h)) (Subgroup.inclusion_injective _)
  haveI : Group.IsSolvable ↥⁅G, G⁆ :=
    Group.isSolvable_of_isSolvable_injective
      (f := (j2u_commIso eG).toMonoidHom) (j2u_commIso eG).injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hJ'.1) (Subgroup.inclusion_injective hJ'.1)

end UnitaryHelpers

theorem fieldExt_unitary_lt
    {U X : Type} [Group U] [Group X] (ψ : U →* X) (hψ : Function.Injective ψ)
    {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆) {m a f : ℕ} {E : Type} [Field E]
    [Fintype E] (hE : Fintype.card E = (2 ^ a) ^ 2) (eG : ↥G ≃* ↥(GUFull m (2 ^ a) E))
    {t : StatedLieTag} (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f) : f < a := by
  have ha1 : 1 ≤ a := j2u_one_le_of_card hE
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 a E :=
    { prime := Nat.prime_two, one_le := ha1,
      card := by rw [Nat.card_eq_fintype_card, hE, ← pow_mul, Nat.mul_comm] }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite E := h.finite
  haveI : CharP E 2 := h.charP
  have hJq : CFSG.Open.IsQuasisimple ↥J' :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥J').mp hJ'.2.2
  have hnot : ¬ Group.IsSolvable ↥J' :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts6.not_isSolvable_of_isQuasisimple hJq
  rcases (by omega : m ≤ 1 ∨ m = 2 ∨ 3 ≤ m) with hm1 | hm2 | hm3
  · haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 a E m) := by
      haveI : Group.IsSolvable (GL (Fin m) E) := by
        rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
        · infer_instance
        · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_one_solvable E
      infer_instance
    exact absurd (j2u_solvable_J' h eG hJ' inferInstance) hnot
  · subst hm2
    by_cases ha : a = 1
    · subst ha
      haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 E 2) :=
        CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one h (by omega) (by omega)
      exact absurd (j2u_solvable_J' h eG hJ' inferInstance) hnot
    · have ha2 : 2 ≤ a := by omega
      have h4a : 4 ≤ 2 ^ a := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
      haveI : Finite ↥h.fixedField := inferInstance
      have h4F : 4 ≤ Nat.card ↥h.fixedField := by
        rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.card_fixedField h]; exact h4a
      have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) ↥h.fixedField) :=
        CFSG.ComponentClassification.CatFactsSp4.isQuasisimple_SL2' h4F
      have hqSL' : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) ↥h.fixedField) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqSL)
      have hq : CFSG.IsQuasisimple ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 a E 2) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
            (CFSG.Goldschmidt.Sec82.isQuasisimple_of_mulEquiv
              (j2u_unitarySU_two_iso_SL2 h).symm hqSL'))
      obtain ⟨t', m', f', hff, hL', -⟩ := hFE
      have eSL : ↥(J'.map ψ) ≃* Matrix.SpecialLinearGroup (Fin 2) ↥h.fixedField :=
        (Subgroup.equivMapOfInjective J' ψ hψ).symm.trans
          ((MulEquiv.subgroupCongr (j2u_component_eq eG h hq hJ')).trans
            ((j2u_commIsoSU h eG hq).trans (j2u_unitarySU_two_iso_SL2 h)))
      haveI : CharP ↥h.fixedField 2 := inferInstance
      have hX : LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL 2 2 a :=
        CFSG.RankThree.PartOne.TCP.lieModel_of_equiv_SL2 h4a
          (by rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.card_fixedField h]) eSL
      have hadm : CFSG.Open.StatedLieAdmissible t' m' 2 f' := LieModel.admissible hL'
      have hf'a : f' = a :=
        (CFSG.SeitzReduction.RankOne.sl2EvenTypeDet
          (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) a t' m' f' hX hadm hL').2.2
      omega
  · by_cases h32 : (m, 2 ^ a) = (3, 2)
    · have ha : a = 1 := by
        by_contra hne
        have h2 : 2 ≤ a := by omega
        have hle : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h2
        have h2' := congrArg Prod.snd h32
        norm_num at hle h2'
        omega
      subst ha
      have hm3eq : m = 3 := congrArg Prod.fst h32
      haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 E m) :=
        CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one h (by omega) (by omega)
      exact absurd (j2u_solvable_J' h eG hJ' inferInstance) hnot
    · have hq : CFSG.IsQuasisimple ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 a E m) :=
        CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_unitarySU h hm3 h32
      obtain ⟨t', m', f', hff, hL', -⟩ := hFE
      have ePSU := j2u_ePSU h ψ hψ eG hq hJ'
      have hX : LieModel (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSU m 2 a :=
        CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_of_mulEquiv_unitaryPSU h hm3 h32 ePSU
      have hadm : CFSG.Open.StatedLieAdmissible t' m' 2 f' := LieModel.admissible hL'
      have hf'a : f' = a := by
        rcases (by omega : m = 3 ∨ 4 ≤ m) with hm3' | hm4
        · subst hm3'
          exact (CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet
            (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) a t' m' f' hX hadm hL').2.2
        · exact (CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt hm4
            (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) a t' m' f' hX hadm hL').2.2
      omega


private noncomputable abbrev j2o_ML {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] :
    GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  (Matrix.GeneralLinearGroup.toLin (R := K)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

private lemma j2o_ML_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (A : GL ι K) (v : ι → K) :
    j2o_ML A v = Matrix.mulVec (A : Matrix ι ι K) v := by
  simp only [j2o_ML, MulEquiv.trans_apply,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.mulVecLin_apply]

private lemma j2o_matrixOrthogonal_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : QuadraticForm K (ι → K)) :
    CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Q =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (j2o_ML (ι := ι) (K := K)).toMonoidHom := by
  ext A
  simp only [CFSG.Blueprint.EvenSource.matrixOrthogonal, Set.mem_setOf_eq, Subgroup.mem_comap,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  change (∀ v, Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v) ↔ ∀ v, Q (j2o_ML A v) = Q v
  simp only [j2o_ML_apply]

private lemma j2o_map_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : QuadraticForm K (ι → K)) :
    (StatedOmega ⇑Q).map (j2o_ML (ι := ι) (K := K)).toMonoidHom = orthDerived Q := by
  rw [CFSG.Blueprint.EvenSource.statedOmega_eq_commutator, j2o_matrixOrthogonal_eq,
    Subgroup.map_commutator]
  rw [Subgroup.map_comap_eq_self_of_surjective (j2o_ML (ι := ι) (K := K)).surjective]

private noncomputable def j2o_statedOmega_equiv {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Q : QuadraticForm K (ι → K)) :
    ↥(StatedOmega ⇑Q) ≃* ↥(orthDerived Q) :=
  (Subgroup.equivMapOfInjective (StatedOmega ⇑Q) (j2o_ML (ι := ι) (K := K)).toMonoidHom
    (j2o_ML (ι := ι) (K := K)).injective).trans
    (MulEquiv.subgroupCongr (j2o_map_statedOmega Q))

private lemma j2o_commutator_le_self {U : Type} [Group U] (G : Subgroup U) : ⁅G, G⁆ ≤ G := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact G.mul_mem (G.mul_mem (G.mul_mem ha hb) (G.inv_mem ha)) (G.inv_mem hb)

private lemma j2o_even_cases {r : ℕ} (h : Even r) :
    r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6 ∨ 8 ≤ r := by
  obtain ⟨k, rfl⟩ := h
  by_cases hk : k ≤ 3
  · interval_cases k <;> omega
  · right; right; right; right; omega

private lemma j2o_small
    {U : Type} [Group U] {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆)
    {K ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁] [Field K] [CharP K 2]
    (Φ₁ : QuadraticForm K (ι₁ → K)) (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (eG : ↥G ≃* ↥(StatedOmega ⇑Φ₁))
    (h2 : Module.finrank K (ι₁ → K) ≤ 2) : False := by
  have hSolO : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Φ₁) :=
    CFSG.StandardType.LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two hΦ₁ h2
  have hle : orthDerived Φ₁ ≤ TauCeti.QuadraticMap.orthogonalGroup Φ₁ :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
  have hSolD : Group.IsSolvable ↥(orthDerived Φ₁) := by
    haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Φ₁) := hSolO
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  have hSolS : Group.IsSolvable ↥(StatedOmega ⇑Φ₁) := by
    haveI : Group.IsSolvable ↥(orthDerived Φ₁) := hSolD
    exact Group.isSolvable_of_surjective
      (f := (j2o_statedOmega_equiv Φ₁).symm.toMonoidHom)
      (j2o_statedOmega_equiv Φ₁).symm.surjective
  have hSolG : Group.IsSolvable ↥G := by
    haveI : Group.IsSolvable ↥(StatedOmega ⇑Φ₁) := hSolS
    exact Group.isSolvable_of_surjective (f := eG.symm.toMonoidHom) eG.symm.surjective
  have hJG : J' ≤ G := hJ'.1.trans (j2o_commutator_le_self G)
  have hSolJ : Group.IsSolvable ↥J' := by
    haveI : Group.IsSolvable ↥G := hSolG
    have hSolJsub : Group.IsSolvable ↥(J'.subgroupOf G) := inferInstance
    haveI : Group.IsSolvable ↥(J'.subgroupOf G) := hSolJsub
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hJG).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJG).surjective
  have hqJ : CFSG.Open.IsQuasisimple ↥J' := hJ'.2.2
  haveI : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hqJ.2
  haveI : Nontrivial ↥J' :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J'))
  haveI : Group.IsPerfect ↥J' := ⟨hqJ.1⟩
  exact (Group.IsPerfect.not_isSolvable ↥J') hSolJ

private lemma j2o_eq_top_of_isQuasisimple
    {U : Type} [Group U] {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆)
    {K ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁] [Field K] [Fintype K] [CharP K 2]
    (Φ₁ : QuadraticForm K (ι₁ → K)) (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (eG : ↥G ≃* ↥(StatedOmega ⇑Φ₁))
    (h3 : 3 ≤ Module.finrank K (ι₁ → K))
    (hns : ¬ (Module.finrank K (ι₁ → K) = 4 ∧ ∃ S : Submodule K (ι₁ → K),
      Module.finrank K S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0)) : J' = G := by
  have hqO : CFSG.IsQuasisimple ↥(orthDerived Φ₁) :=
    (CFSG.StandardType.LayerPDiv.isQuasisimple_commutator_of_not_split hΦ₁ h3 hns).1
  have eOD : ↥G ≃* ↥(orthDerived Φ₁) := eG.trans (j2o_statedOmega_equiv Φ₁)
  have hqGn : CFSG.IsQuasisimple ↥G := CFSG.IsQuasisimple.of_mulEquiv eOD hqO
  have hGq : CFSG.Open.IsQuasisimple ↥G := ⟨hqGn.1.commutator_eq_top, hqGn.2.1⟩
  have hmap : Subgroup.map G.subtype (⊤ : Subgroup ↥G) = G := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomm_eq : ⁅G, G⁆ = G := by
    have h := Subgroup.map_subtype_commutator G
    rw [hGq.1, hmap] at h
    exact h.symm
  have hJ'G_sub : CFSG.Assembly.IsSubnormal J' G := hcomm_eq ▸ hJ'.2.1
  haveI : Finite (Matrix ι₁ ι₁ K) := Fintype.finite inferInstance
  haveI : Finite (GL ι₁ K) :=
    Finite.of_injective (fun A : GL ι₁ K => (A : Matrix ι₁ ι₁ K))
      (fun _ _ h => Units.ext h)
  haveI : Finite ↥(StatedOmega ⇑Φ₁) := Subtype.finite
  haveI : Finite ↥G := Finite.of_injective eG.toMonoidHom eG.injective
  have hJG : J' ≤ G := hJ'.1.trans (j2o_commutator_le_self G)
  have hsubM : (J'.subgroupOf G).IsSubnormal := hJ'G_sub.subgroupOf
  have hsubA : CFSG.Assembly.IsSubnormal (J'.subgroupOf G) ⊤ :=
    CFSG.Assembly.IsSubnormal.of_mathlib hsubM
  have hsub : CFSG.Open.IsSubnormal (J'.subgroupOf G) ⊤ :=
    (CFSG.Assembly.isSubnormal_iff_open).mp hsubA
  have hqK : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥G) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hGq
  have hqJ' : CFSG.Open.IsQuasisimple ↥(J'.subgroupOf G) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJG) hJ'.2.2
  have htop : J'.subgroupOf G = ⊤ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i253_eq_of_isSubnormal hqK hqJ' hsub
  have hmapG : Subgroup.map G.subtype (⊤ : Subgroup ↥G) = G := hmap
  have hmb := Subgroup.map_subgroupOf_eq_of_le hJG
  rw [htop, hmapG] at hmb
  exact hmb.symm

private lemma j2o_big
    {U X : Type} [Group U] [Group X] (ψ : U →* X) (hψ : Function.Injective ψ)
    {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆)
    {K ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁] [Field K] [Fintype K] [CharP K 2]
    (Φ₁ : QuadraticForm K (ι₁ → K)) (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (eG : ↥G ≃* ↥(StatedOmega ⇑Φ₁)) {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    {t : StatedLieTag} (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f)
    (h8 : 8 ≤ Fintype.card ι₁) : False := by
  have h3 : 3 ≤ Module.finrank K (ι₁ → K) := by rw [Module.finrank_pi]; omega
  have hns : ¬ (Module.finrank K (ι₁ → K) = 4 ∧ ∃ S : Submodule K (ι₁ → K),
      Module.finrank K S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0) := by
    rintro ⟨h4, -⟩
    rw [Module.finrank_pi] at h4
    omega
  have hJ'G : J' = G := j2o_eq_top_of_isQuasisimple hJ' Φ₁ hΦ₁ eG h3 hns
  have eOD : ↥G ≃* ↥(orthDerived Φ₁) := eG.trans (j2o_statedOmega_equiv Φ₁)
  have eJ : ↥(J'.map ψ) ≃* ↥(orthDerived Φ₁) :=
    (Subgroup.equivMapOfInjective J' ψ hψ).symm.trans
      ((MulEquiv.subgroupCongr hJ'G).trans eOD)
  have h8' : 8 ≤ Module.finrank K (ι₁ → K) := by rw [Module.finrank_pi]; exact h8
  have hF : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card]; exact hK
  exact (CFSG.StandardType.TableC.not_fieldExtCase_of_mulEquiv_orthDerived
    (J := J'.map ψ) (t := t) (f := f) (F := K) hF hΦ₁ h8' eJ) hFE

private lemma j2o_six_plus
    {U X : Type} [Group U] [Group X] (ψ : U →* X) (hψ : Function.Injective ψ)
    {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆)
    {K ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁] [Field K] [Fintype K] [CharP K 2]
    (Φ₁ : QuadraticForm K (ι₁ → K)) (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (eG : ↥G ≃* ↥(StatedOmega ⇑Φ₁)) {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    {t : StatedLieTag} (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f)
    (hdim : Module.finrank K (ι₁ → K) = 6)
    (hts : ∃ U : Submodule K (ι₁ → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Φ₁ u = 0) :
    False := by
  have h3 : 3 ≤ Module.finrank K (ι₁ → K) := by omega
  have hns : ¬ (Module.finrank K (ι₁ → K) = 4 ∧ ∃ S : Submodule K (ι₁ → K),
      Module.finrank K S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0) := by
    rintro ⟨h4, -⟩
    omega
  have hJ'G : J' = G := j2o_eq_top_of_isQuasisimple hJ' Φ₁ hΦ₁ eG h3 hns
  have eOD : ↥G ≃* ↥(orthDerived Φ₁) := eG.trans (j2o_statedOmega_equiv Φ₁)
  have eSL : ↥(J'.map ψ) ≃* ↥(StatedSL 4 K) := by
    have hSL := Classical.choice
      (CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_klein_commutator_six Φ₁ hΦ₁ hdim hts)
    have eO : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Φ₁)) ≃*
        ↥(orthDerived Φ₁) :=
      (Subgroup.equivMapOfInjective (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Φ₁))
        (TauCeti.QuadraticMap.orthogonalGroup Φ₁).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr
          (Subgroup.map_subtype_commutator (TauCeti.QuadraticMap.orthogonalGroup Φ₁)))
    exact ((Subgroup.equivMapOfInjective J' ψ hψ).symm.trans
      ((MulEquiv.subgroupCongr hJ'G).trans eOD)).trans (eO.symm.trans hSL)
  have hcard : 2 ≤ 2 ^ f := by rw [← hK]; exact Fintype.one_lt_card
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst h0
    simp only [pow_zero] at hcard
    omega
  have hE : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card]; exact hK
  have hqSL : CFSG.IsQuasisimple ↥(StatedSL 4 K) :=
    CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 3) (by norm_num) K
  have hqJ : CFSG.IsQuasisimple ↥(J'.map ψ) := CFSG.IsQuasisimple.of_mulEquiv eSL hqSL
  have hX : CFSG.Blueprint.LieModel
      (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL 4 2 f :=
    CFSG.StandardType.ggNbrLSideUni_typeSL hf hE eSL hqJ
  obtain ⟨t', m, f', hff, hLM, -⟩ := hFE
  have hf' : f' = f := (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique
    (m := 4) (by norm_num) hX hLM).2.2
  omega

private lemma j2o_six_minus
    {U X : Type} [Group U] [Group X] (ψ : U →* X) (hψ : Function.Injective ψ)
    {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆)
    {K ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁] [Field K] [Fintype K] [CharP K 2]
    (Φ₁ : QuadraticForm K (ι₁ → K)) (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (eG : ↥G ≃* ↥(StatedOmega ⇑Φ₁)) {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    {t : StatedLieTag} (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f)
    (hdim : Module.finrank K (ι₁ → K) = 6)
    (hnts : ∀ U : Submodule K (ι₁ → K), Module.finrank K U = 3 → ∃ u ∈ U, Φ₁ u ≠ 0) :
    False := by
  have h3 : 3 ≤ Module.finrank K (ι₁ → K) := by omega
  have hns : ¬ (Module.finrank K (ι₁ → K) = 4 ∧ ∃ S : Submodule K (ι₁ → K),
      Module.finrank K S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0) := by
    rintro ⟨h4, -⟩
    omega
  have hJ'G : J' = G := j2o_eq_top_of_isQuasisimple hJ' Φ₁ hΦ₁ eG h3 hns
  have eOD : ↥G ≃* ↥(orthDerived Φ₁) := eG.trans (j2o_statedOmega_equiv Φ₁)
  have hF : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card]; exact hK
  have hcard : 2 ≤ 2 ^ f := by rw [← hK]; exact Fintype.one_lt_card
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst h0
    simp only [pow_zero] at hcard
    omega
  obtain ⟨E, hFieldE, hFiniteE, hEcard, heSU⟩ :=
    CFSG.SeitzReduction.OmegaPilot.nonempty_orthDerived_mulEquiv_statedSU_of_six
      hF hΦ₁ hdim hnts
  letI : Field E := hFieldE
  letI : Finite E := hFiniteE
  have eSU : ↥(J'.map ψ) ≃* ↥(StatedSU 4 (2 ^ f) E) :=
    ((Subgroup.equivMapOfInjective J' ψ hψ).symm.trans
      ((MulEquiv.subgroupCongr hJ'G).trans eOD)).trans (Classical.choice heSU)
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E :=
    ⟨Nat.prime_two, hf, by rw [hEcard, ← pow_mul, Nat.mul_comm f 2]⟩
  have hX : CFSG.Blueprint.LieModel
      (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSU 4 2 f :=
    CFSG.StandardType.SUFacts.lieModel_quotient_center_of_mulEquiv_unitarySU (m := 4) hUF
      (by norm_num) (by rintro h; exact absurd (congrArg Prod.fst h) (by norm_num)) eSU
  obtain ⟨t', m, f', hff, hLM, -⟩ := hFE
  have hf' : f' = f := (CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq
    (m := 4) (by norm_num) hX hLM rfl).2.2
  omega

theorem fieldExt_one_card
    {U X : Type} [Group U] [Group X] (ψ : U →* X) (hψ : Function.Injective ψ)
    {G J' : Subgroup U} (hJ' : IsComponentOf J' ⁅G, G⁆) {K ι₁ : Type} [Fintype ι₁]
    [DecidableEq ι₁] [Field K] [Fintype K] [CharP K 2] {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    (Φ₁ : QuadraticForm K (ι₁ → K)) (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate)
    (eG : ↥G ≃* ↥(StatedOmega ⇑Φ₁)) {t : StatedLieTag}
    (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f) : Fintype.card ι₁ = 4 := by
  have hfin : Module.finrank K (ι₁ → K) = Fintype.card ι₁ := Module.finrank_pi K
  have heven : Even (Fintype.card ι₁) := by
    have h := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Φ₁ hΦ₁
    rwa [hfin] at h
  have hcases := j2o_even_cases heven
  by_contra h4
  rcases hcases with h0 | h2 | h4' | h6 | h8
  · exact j2o_small hJ' Φ₁ hΦ₁ eG (by rw [hfin]; omega)
  · exact j2o_small hJ' Φ₁ hΦ₁ eG (by rw [hfin]; omega)
  · exact h4 h4'
  · have hdim : Module.finrank K (ι₁ → K) = 6 := by rw [hfin]; exact h6
    by_cases hts : ∃ U : Submodule K (ι₁ → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Φ₁ u = 0
    · exact j2o_six_plus ψ hψ hJ' Φ₁ hΦ₁ eG hK hFE hdim hts
    · exact j2o_six_minus ψ hψ hJ' Φ₁ hΦ₁ eG hK hFE hdim (fun U hU => by
        by_contra h
        push_neg at h
        exact hts ⟨U, hU, h⟩)
  · exact j2o_big ψ hψ hJ' Φ₁ hΦ₁ eG hK hFE h8

end CFSG.StandardType.TableC

end
