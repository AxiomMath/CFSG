module

public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CentralQuotient
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniSub
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

private theorem kgLangS1AUniCompAux_normalizerMonoidHom_coe {G : Type*} [Group G] {H : Subgroup G}
    (A : Subgroup.normalizer (H : Set G)) (h : H) :
    ((H.normalizerMonoidHom A h : H) : G) = (A : G) * h * (A : G)⁻¹ :=
  rfl

private noncomputable def kgLangS1AUniCompAux_inclusion {d n p : ℕ} {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p) :
    ↥(LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p))) →*
      ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) where
  toFun A := ⟨Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype A.1, by
    have hσOdd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
    haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
      (f := 2 * n) (by rw [hF, ← pow_mul, mul_comm])
    have hAsu : A.1 ∈ LargeEvenSUGroup (Fin d)
        (CFSG.LocalAnalysis.GLTheoremA.FQ.fixF σ) (2 ^ (n / orderOf σ)) := by
      have hpow : 2 ^ (n / p) = 2 ^ (n / orderOf σ) := by rw [hσ]
      exact hpow ▸ A.2
    exact (CFSG.LocalAnalysis.GLTheoremA.FR.su_hiff (d := d) hn hF σ hσOdd A.1).2 hAsu⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)

private theorem kgLangS1AUniCompAux_inclusion_apply {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    (A : ↥(LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p)))) :
    ((kgLangS1AUniCompAux_inclusion (d := d) hF hn hp hp2 hσ A :
        ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) : GL (Fin d) F) =
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
        (A : GL (Fin d) (semilinearFixedSubfield σ)) :=
  rfl

private theorem kgLangS1AUniCompAux_inclusion_injective {d n p : ℕ} {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p) :
    Function.Injective (kgLangS1AUniCompAux_inclusion (d := d) hF hn hp hp2 hσ) := by
  intro a b h
  apply Subtype.ext
  exact CFSG.LocalAnalysis.GLTheoremA.FQ.glMap_subtype_injective σ
    (congrArg (fun x : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) =>
      (x : GL (Fin d) F)) h)

private theorem kgLangS1AUniCompAux_fixSubgroup_eq_range {d n p : ℕ} {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.GLTheoremA.FQ.matAct (LargeEvenSUGroup (Fin d) F (2 ^ n))
          (CFSG.LocalAnalysis.GLTheoremA.T156.Uni.suMapStable d F (2 ^ n)) σ) =
      (kgLangS1AUniCompAux_inclusion (d := d) hF hn hp hp2 hσ).range := by
  classical
  have hσOdd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
  haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 2 * n) (by rw [hF, ← pow_mul, mul_comm])
  ext x
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MonoidHom.mem_range]
  constructor
  · intro hx
    have hxGL : Matrix.GeneralLinearGroup.map σ.toRingHom (x : GL (Fin d) F) =
        (x : GL (Fin d) F) := by
      have h := congrArg (fun y : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) =>
        (y : GL (Fin d) F)) hx
      simpa [CFSG.LocalAnalysis.GLTheoremA.FQ.matAct_coe] using h
    obtain ⟨A, hA⟩ := CFSG.LocalAnalysis.GLTheoremA.FQ.exists_descend σ
      (x : GL (Fin d) F) hxGL
    refine ⟨⟨A, ?_⟩, ?_⟩
    · have hAsu : A ∈ LargeEvenSUGroup (Fin d)
          (CFSG.LocalAnalysis.GLTheoremA.FQ.fixF σ) (2 ^ (n / orderOf σ)) :=
        (CFSG.LocalAnalysis.GLTheoremA.FR.su_hiff (d := d) hn hF σ hσOdd A).1 (hA ▸ x.2)
      have hpow : 2 ^ (n / orderOf σ) = 2 ^ (n / p) := by rw [hσ]
      exact hpow ▸ hAsu
    · apply Subtype.ext
      exact hA
  · rintro ⟨A, rfl⟩
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.GLTheoremA.FQ.matAct_coe]
    exact CFSG.LocalAnalysis.GLTheoremA.FQ.glMap_subtype_fixed σ A.1

private theorem kgLangS1AUniCompAux_conj_compat {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    (C : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)))
    (c : Fˣ)
    (M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p)) :
      Set (GL (Fin d) (semilinearFixedSubfield σ))))
    (hC : (C : GL (Fin d) F) = Matrix.GeneralLinearGroup.scalar (Fin d) c *
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
        (M : GL (Fin d) (semilinearFixedSubfield σ)))
    (h : ↥(LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p)))) :
    kgLangS1AUniCompAux_inclusion (d := d) hF hn hp hp2 hσ
        ((LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p))).normalizerMonoidHom
          M h) =
      (LargeEvenSUGroup (Fin d) F (2 ^ n)).normalizerMonoidHom C
        (kgLangS1AUniCompAux_inclusion (d := d) hF hn hp hp2 hσ h) := by
  apply Subtype.ext
  rw [kgLangS1AUniCompAux_inclusion_apply]
  rw [kgLangS1AUniCompAux_normalizerMonoidHom_coe M h]
  rw [kgLangS1AUniCompAux_normalizerMonoidHom_coe C
    (kgLangS1AUniCompAux_inclusion (d := d) hF hn hp hp2 hσ h)]
  rw [kgLangS1AUniCompAux_inclusion_apply]
  change Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
      ((M : GL (Fin d) (semilinearFixedSubfield σ)) *
        (h : GL (Fin d) (semilinearFixedSubfield σ)) *
        (M : GL (Fin d) (semilinearFixedSubfield σ))⁻¹) =
    (C : GL (Fin d) F) *
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
        (h : GL (Fin d) (semilinearFixedSubfield σ))) *
      (C : GL (Fin d) F)⁻¹
  rw [hC]
  have hconj : ∀ X : GL (Fin d) F, Matrix.GeneralLinearGroup.scalar (Fin d) c * X *
      (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ = X := by
    intro X
    rw [Matrix.GeneralLinearGroup.scalar_commute c X, mul_assoc, mul_inv_cancel, mul_one]
  simp only [map_mul, map_inv, mul_inv_rev]
  rw [show (Matrix.GeneralLinearGroup.scalar (Fin d) c *
        Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
          (M : GL (Fin d) (semilinearFixedSubfield σ))) *
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
        (h : GL (Fin d) (semilinearFixedSubfield σ)) *
      ((Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
        (M : GL (Fin d) (semilinearFixedSubfield σ)))⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹) =
      Matrix.GeneralLinearGroup.scalar (Fin d) c *
        (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
          (M : GL (Fin d) (semilinearFixedSubfield σ)) *
          Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
            (h : GL (Fin d) (semilinearFixedSubfield σ)) *
          (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
            (M : GL (Fin d) (semilinearFixedSubfield σ)))⁻¹) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ from by group]
  rw [hconj]

theorem kgLangS1A_uni_component {d n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p) (hdq₀ : ¬(d = 3 ∧ 2 ^ (n / p) = 2))
    {K : Type} [Group K] [Finite K]
    (κ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* K) (hκ : Function.Surjective κ)
    (hker : κ.ker ≤ Subgroup.center ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (ψ₀ : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) →* ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)))
    (hψ₀ : ∀ g, ((ψ₀ g : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) : GL (Fin d) F) =
      Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin d) F))
    {ξ : MulAut K} (hξ : ∀ h, ξ (κ h) = κ (ψ₀ h))
    {J₀ : Subgroup K} (hJ₀ : IsComponentOf J₀ (ggFixSub ξ)) :
    ∃ ρ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p))),
      ∀ (β : MulAut K)
        (C : Subgroup.normalizer (LargeEvenSUGroup (Fin d) F (2 ^ n) : Set (GL (Fin d) F)))
        (c : Fˣ)
        (M : Subgroup.normalizer (LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ)
          (2 ^ (n / p)) : Set (GL (Fin d) (semilinearFixedSubfield σ)))),
        (C : GL (Fin d) F) = Matrix.GeneralLinearGroup.scalar (Fin d) c *
          Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype
            (M : GL (Fin d) (semilinearFixedSubfield σ)) →
        (∀ h, β (κ h) = κ ((LargeEvenSUGroup (Fin d) F (2 ^ n)).normalizerMonoidHom C h)) →
        ∀ j : ↥J₀, ∃ j' : ↥J₀, (j' : K) = β j ∧
          ρ (QuotientGroup.mk j') =
            TableB.projConj (LargeEvenSUGroup (Fin d) (semilinearFixedSubfield σ) (2 ^ (n / p))) M
              (ρ (QuotientGroup.mk j)) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let F₀ := semilinearFixedSubfield σ
  let ι := kgLangS1AUniCompAux_inclusion (d := d) hF hn hp hp2 hσ
  let α : MulAut ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) :=
    CFSG.LocalAnalysis.GLTheoremA.FQ.matAct (LargeEvenSUGroup (Fin d) F (2 ^ n))
      (CFSG.LocalAnalysis.GLTheoremA.T156.Uni.suMapStable d F (2 ^ n)) σ
  have hψα : ∀ x, ψ₀ x = α x := by
    intro x
    apply Subtype.ext
    rw [hψ₀ x]
    exact (CFSG.LocalAnalysis.GLTheoremA.FQ.matAct_coe _ _ σ x).symm
  have hαβ : ∀ x, κ (α x) = ξ (κ x) := by
    intro x
    rw [← hψα x]
    exact (hξ x).symm
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α = ι.range :=
    kgLangS1AUniCompAux_fixSubgroup_eq_range (d := d) hF hn hp hp2 hσ
  have hinj : Function.Injective ι :=
    kgLangS1AUniCompAux_inclusion_injective (d := d) hF hn hp hp2 hσ
  have hF₀ : Nat.card F₀ = (2 ^ (n / p)) ^ 2 :=
    (kgLangTorA_card_fixed_unitary hn hp hp2 hF hσ).2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F₀ 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 2 * (n / p)) (by rw [hF₀, ← pow_mul, mul_comm])
  have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := F₀) (p := 2) (f := n / p) hF₀ hd
    (by intro h; exact hdq₀ (Prod.ext_iff.mp h))
  have hquasiSU : CFSG.IsQuasisimple ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) :=
    (CFSG.Assembly.largeEvenSUGroup_eq_statedSU (K := F₀) d (2 ^ (n / p))) ▸ hSU.1
  have hcenterSU : Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) =
      (LargeEvenScalars (Fin d) F₀).subgroupOf (LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) :=
    (CFSG.Assembly.largeEvenSUGroup_eq_statedSU (K := F₀) d (2 ^ (n / p))) ▸ hSU.2
  have hperf : commutator ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) = ⊤ :=
    hquasiSU.1.commutator_eq_top
  have hq : CFSG.IsQuasisimple ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hfix.symm)) hquasiSU
  let ψtriv : ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) →* Unit := 1
  have hψtriv : ∀ x : ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α),
      ψtriv x = 1 → (x : ↥(LargeEvenSUGroup (Fin d) F (2 ^ n))) ∈
        ⨆ _ : PUnit, CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
    intro x _
    exact Subgroup.mem_iSup_of_mem () x.2
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_centralQuotient
      κ hκ hker α ξ hαβ (fun _ : PUnit => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α)
      (fun _ => le_rfl)
      (fun _ c hc g hg => (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).mul_mem
        ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).mul_mem hc hg)
        ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).inv_mem hc))
      (fun _ => hq) ψtriv hψtriv J₀ (CFSG.Assembly.isComponentOf_iff_open.mp hJ₀)
  have hJ₀eq : J₀ = (κ.comp ι).range := by
    rw [hi, hfix, MonoidHom.range_comp]
  let κ₀ : ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) →* K := κ.comp ι
  have hrange : J₀ = κ₀.range := hJ₀eq
  let fbase : ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) →* ↥J₀ :=
    { toFun := fun h => ⟨κ₀ h, by rw [hrange]; exact ⟨h, rfl⟩⟩
      map_one' := Subtype.ext (map_one κ₀)
      map_mul' := fun a b => Subtype.ext (map_mul κ₀ a b) }
  have hfbase_surj : Function.Surjective fbase := by
    intro y
    have hy : (y : K) ∈ κ₀.range := by rw [← hrange]; exact y.2
    obtain ⟨h, hh⟩ := hy
    exact ⟨h, Subtype.ext hh⟩
  have hker_fbase : fbase.ker ≤
      Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have h1 : κ₀ h = 1 := congrArg Subtype.val hh
    have h2 : ι h ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin d) F (2 ^ n)) :=
      hker (by rw [MonoidHom.mem_ker]; exact h1)
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro x
    apply hinj
    rw [map_mul, map_mul]
    exact h2 (ι x)
  let Φ : ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) →*
      ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (QuotientGroup.mk' (Subgroup.center ↥J₀)).comp fbase
  have hmapcenter : (Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p)))).map fbase =
      Subgroup.center ↥J₀ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_center_of_surjective hperf fbase
      hfbase_surj hker_fbase
  have hkerΦ : Φ.ker = Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) := by
    ext h
    change QuotientGroup.mk (fbase h) = 1 ↔ h ∈
      Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p)))
    rw [QuotientGroup.eq_one_iff, ← hmapcenter, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hfx⟩
      have hmem : x * h⁻¹ ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) :=
        hker_fbase (by rw [MonoidHom.mem_ker, map_mul, map_inv, hfx, mul_inv_cancel])
      have : h * x⁻¹ ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) := by
        simpa [mul_inv_rev, inv_inv] using Subgroup.inv_mem _ hmem
      simpa using Subgroup.mul_mem _ this hx
    · intro hh
      exact ⟨h, hh, rfl⟩
  let ΦbarHom : ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) →*
      (↥J₀ ⧸ Subgroup.center ↥J₀) :=
    QuotientGroup.lift (Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p)))) Φ
      (le_of_eq hkerΦ.symm)
  have hΦbarHom_mk : ∀ h, ΦbarHom (QuotientGroup.mk h) = QuotientGroup.mk (fbase h) := by
    intro h
    rw [QuotientGroup.lift_mk]
    rfl
  have hΦbar_surj : Function.Surjective ΦbarHom := by
    intro y
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨h, rfl⟩ := hfbase_surj j
    exact ⟨QuotientGroup.mk h, hΦbarHom_mk h⟩
  have hΦbar_inj : Function.Injective ΦbarHom := by
    intro a b hab
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hΦbarHom_mk, hΦbarHom_mk] at hab
    have h1 : (fbase h)⁻¹ * fbase k ∈ Subgroup.center ↥J₀ := QuotientGroup.eq.mp hab
    have h2 : fbase (h⁻¹ * k) ∈ Subgroup.center ↥J₀ := by
      rw [map_mul, map_inv]; exact h1
    rw [← hmapcenter, Subgroup.mem_map] at h2
    obtain ⟨z, hz, hfz⟩ := h2
    have h3 : z⁻¹ * (h⁻¹ * k) ∈
        Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) :=
      hker_fbase (by rw [MonoidHom.mem_ker, map_mul, map_inv, hfz, inv_mul_cancel])
    have h4 : h⁻¹ * k ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) := by
      have := Subgroup.mul_mem _ hz h3
      convert this using 1
      group
    exact QuotientGroup.eq.mpr h4
  let Φbar : ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) ≃*
      (↥J₀ ⧸ Subgroup.center ↥J₀) :=
    MulEquiv.ofBijective ΦbarHom ⟨hΦbar_inj, hΦbar_surj⟩
  have hΦbar_mk : ∀ h, Φbar (QuotientGroup.mk h) = QuotientGroup.mk (fbase h) := hΦbarHom_mk
  let ψ : ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) :=
    QuotientGroup.quotientMulEquivOfEq hcenterSU
  let ρ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) :=
    Φbar.symm.trans ψ
  have hψ_mk : ∀ h, ψ (QuotientGroup.mk h) = LargeEvenProjMk _ h := by
    intro h
    exact QuotientGroup.quotientMulEquivOfEq_mk hcenterSU h
  have hρ_formula : ∀ h, ρ (QuotientGroup.mk (fbase h)) = LargeEvenProjMk _ h := by
    intro h
    change ψ (Φbar.symm (QuotientGroup.mk (fbase h))) = LargeEvenProjMk _ h
    rw [show QuotientGroup.mk (fbase h) = Φbar (QuotientGroup.mk h) from (hΦbar_mk h).symm]
    rw [MulEquiv.symm_apply_apply]
    exact hψ_mk h
  refine ⟨ρ, ?_⟩
  intro β C c M hC hβ j
  obtain ⟨h, rfl⟩ := hfbase_surj j
  refine ⟨fbase ((LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))).normalizerMonoidHom M h), ?_, ?_⟩
  · change κ (ι ((LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))).normalizerMonoidHom M h)) =
      β (κ (ι h))
    rw [hβ (ι h)]
    congr 1
    exact kgLangS1AUniCompAux_conj_compat hF hn hp hp2 hσ C c M hC h
  · rw [hρ_formula ((LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))).normalizerMonoidHom M h),
      hρ_formula h]
    exact (TableB.projConj_mk (LargeEvenSUGroup (Fin d) F₀ (2 ^ (n / p))) M h).symm

theorem kgLangS1A_uni_not_component {n p : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : F ≃+* F} (hσ : orderOf σ = p) (hq₀ : 2 ^ (n / p) = 2)
    {K : Type} [Group K] [Finite K]
    (κ : ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n)) →* K) (hκ : Function.Surjective κ)
    (hker : κ.ker ≤ Subgroup.center ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n)))
    (ψ₀ : ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n)) →* ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n)))
    (hψ₀ : ∀ g, ((ψ₀ g : ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n))) : GL (Fin 3) F) =
      Matrix.GeneralLinearGroup.map (σ : F →+* F) (g : GL (Fin 3) F))
    {ξ : MulAut K} (hξ : ∀ h, ξ (κ h) = κ (ψ₀ h)) (J₀ : Subgroup K) :
    ¬ IsComponentOf J₀ (ggFixSub ξ) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let F₀ := semilinearFixedSubfield σ
  let ι := kgLangS1AUniCompAux_inclusion (d := 3) hF hn hp hp2 hσ
  let α : MulAut ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n)) :=
    CFSG.LocalAnalysis.GLTheoremA.FQ.matAct (LargeEvenSUGroup (Fin 3) F (2 ^ n))
      (CFSG.LocalAnalysis.GLTheoremA.T156.Uni.suMapStable 3 F (2 ^ n)) σ
  have hψα : ∀ x, ψ₀ x = α x := by
    intro x
    apply Subtype.ext
    rw [hψ₀ x]
    exact (CFSG.LocalAnalysis.GLTheoremA.FQ.matAct_coe _ _ σ x).symm
  have hαβ : ∀ x, κ (α x) = ξ (κ x) := by
    intro x
    rw [← hψα x]
    exact (hξ x).symm
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α = ι.range :=
    kgLangS1AUniCompAux_fixSubgroup_eq_range (d := 3) hF hn hp hp2 hσ
  have hinj : Function.Injective ι :=
    kgLangS1AUniCompAux_inclusion_injective (d := 3) hF hn hp hp2 hσ
  have hF₀ : Nat.card F₀ = (2 ^ (n / p)) ^ 2 :=
    (kgLangTorA_card_fixed_unitary hn hp hp2 hF hσ).2
  have hsolSU₀ : Group.IsSolvable ↥(LargeEvenSUGroup (Fin 3) F₀ (2 ^ (n / p))) := by
    have hF₀' : Nat.card F₀ = (2 ^ 1) ^ 2 := by rw [hF₀, hq₀, pow_one]
    rw [hq₀, CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
    exact CFSG.Quasithin.isSolvable_statedSU_one hF₀'
  haveI : Group.IsSolvable ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
    let e : ↥(LargeEvenSUGroup (Fin 3) F₀ (2 ^ (n / p))) ≃*
        ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hfix.symm)
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  intro hJ₀
  have hJ₀' := CFSG.Assembly.isComponentOf_iff_open.mp hJ₀
  obtain ⟨i, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_centralQuotient
      κ hκ hker α ξ hαβ (fun i : Empty => i.elim) (fun i => i.elim) (fun i => i.elim)
      (fun i => i.elim) (Q := ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α))
      (MonoidHom.id _) (by
        intro x hx
        have hx1 : (x : ↥(LargeEvenSUGroup (Fin 3) F (2 ^ n))) = 1 := congrArg Subtype.val hx
        simpa using hx1)
      J₀ hJ₀'
  exact i.elim

end CFSG.StandardType
