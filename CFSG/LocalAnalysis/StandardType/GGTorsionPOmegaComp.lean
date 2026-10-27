module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGroup
import CFSG.Quasithin.EmptyFaithful.SzC4ChiGrpSq
import TauCeti.GroupTheory.DerivedCentralQuotient
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel
import CFSG.LieType.Universal.Symplectic
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.Open.StatedAPI
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionPOmegaComp

private theorem tpo_model_psl {X : Type} [Group X] {E : Type} [Field E] [Fintype E] {g m : ℕ}
    (hg : 1 ≤ g) (hm : 2 ≤ m) (h4 : m = 2 → 4 ≤ 2 ^ g) (hE : Nat.card E = 2 ^ g)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin m) E) :
    CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSL m 2 g := by
  refine ⟨⟨Nat.prime_two, hg, hm, fun hc => ?_, fun hc => ?_⟩, E, inferInstance,
    Finite.of_fintype E, hE,
    ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)⟩⟩
  · have h1 : m = 2 := (Prod.mk.inj hc).1
    have h2 : 2 ^ g = 2 := (Prod.mk.inj hc).2
    have := h4 h1
    omega
  · have h1 : m = 2 := (Prod.mk.inj hc).1
    have h2 : 2 ^ g = 3 := (Prod.mk.inj hc).2
    have := h4 h1
    omega

private theorem tpo_model_psu {X : Type} [Group X] {E : Type} [Field E] [Fintype E]
    {g m q' : ℕ} (hg : 1 ≤ g) (hm : 3 ≤ m) (hq : q' = 2 ^ g)
    (hne : (m, q') ≠ (3, 2)) (hE : Nat.card E = q' ^ 2)
    (e : X ≃* ↥(CFSG.Open.StatedSU m q' E)) :
    CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU m 2 g := by
  subst hq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite E := Finite.of_fintype E
  obtain ⟨-, hZ⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (F := E) (p := 2) (f := g) (n := m) hE hm hne
  exact ⟨⟨Nat.prime_two, hg, hm, hne⟩, E, inferInstance, inferInstance, hE,
    ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (QuotientGroup.quotientMulEquivOfEq hZ)⟩⟩

private theorem tpo_model_of_orthFactor {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorOver 2 (2 ^ f) X) :
    ∃ (t' : CFSG.Open.StatedLieTag) (n' f' : ℕ),
      CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) t' n' 2 f' := by
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorOver at h
  rcases h with
    ⟨m, j, E, hEfield, hEfintype, hm2, hj, -, hcard, h4, ⟨e⟩⟩
    | ⟨m, j, q', E, hEfield, hEfintype, hm3, hj, -, hq', hcard, hne, ⟨e⟩⟩
    | ⟨K', hKfield, hKfintype, hKcard, -, s, hs2, hne, ⟨e⟩⟩
    | ⟨K', hKfield, hKfintype, V, hVadd, hVmod, hVfindim, Q, hKcard, -, hQ, hd, hT, ⟨e⟩⟩
  · have hE : Nat.card E = 2 ^ (f * j) := by
      rw [Nat.card_eq_fintype_card, hcard, pow_mul]
    have h4' : m = 2 → 4 ≤ 2 ^ (f * j) := by
      intro hm
      rw [← hE, Nat.card_eq_fintype_card]
      exact h4 hm
    exact ⟨.PSL, m, f * j, tpo_model_psl (Nat.mul_pos hf hj) hm2 h4' hE e⟩
  · have hq : q' = 2 ^ (f * j) := by rw [hq', pow_mul]
    have hE : Nat.card E = q' ^ 2 := by rw [Nat.card_eq_fintype_card, hcard]
    exact ⟨.PSU, m, f * j, tpo_model_psu (Nat.mul_pos hf hj) hm3 hq hne hE e⟩
  · haveI : Finite K' := Finite.of_fintype K'
    have hadm : CFSG.Open.StatedLieAdmissible .PSp s 2 f :=
      ⟨Nat.prime_two, hf, hs2, by rw [← hKcard]; exact hne⟩
    have hSp : CFSG.Open.StatedClassicalModel
        (↥(CFSG.Open.StatedSp s K') ⧸ Subgroup.center ↥(CFSG.Open.StatedSp s K')) .PSp s 2 f :=
      CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient
        (n := s) (F := K') hadm hKcard
    have hcongr : X ⧸ Subgroup.center X ≃*
        ↥(CFSG.Open.StatedSp s K') ⧸ Subgroup.center ↥(CFSG.Open.StatedSp s K') :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    exact ⟨.PSp, s, f,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv hcongr.symm hSp⟩
  · obtain ⟨s, hs | hs⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel.exists_statedClassicalModel_quotCenter_orthDerived
        hKcard hQ hd hT e
    · exact ⟨.POmegaPlus, s, f, hs⟩
    · exact ⟨.POmegaMinus, s, f, hs⟩

private theorem tpo_isComponentOf_open {G : Type} [Group G] {a : G} {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup (MulAut.conj a))) :
    CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a)) := by
  have hfix : ggAutFixedSubgroup (MulAut.conj a) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a) :=
    Subgroup.ext fun _ => Iff.rfl
  rw [← hfix]
  exact CFSG.Assembly.isComponentOf_iff_open.1 hJ

theorem ggTorsion_pomega_components {G : Type} [Group G] {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (hG : CFSG.Open.StatedClassicalModel G t n 2 f) (hZ : Subgroup.center G = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {δ : MulAut G} (hδp : δ ^ p = 1)
    (hδ : δ ∈ LargeEvenInnSet G) {J : Subgroup G}
    (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    ∃ (t' : CFSG.Open.StatedLieTag) (n' f' : ℕ),
      CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) t' n' 2 f' := by
  obtain ⟨a, rfl⟩ := hδ
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have ha : a ^ p = 1 := hinj (by rw [map_pow, hδp, map_one])
  obtain ⟨X, inst, -, hXLie, hfac, -, g, hg, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_lieFactor_of_component_conj_omega_card
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorField_holds
      hp hp2 (Or.inr ht) hG hp2 a ha J (tpo_isComponentOf_open hJ)
  letI := inst
  obtain ⟨eXJ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hXLie.perfect g hg hker
  obtain ⟨t', n', f', hM⟩ := tpo_model_of_orthFactor (show 1 ≤ f from hG.1.2.1) hfac
  exact ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eXJ hM⟩

end TorsionPOmegaComp

private theorem quotient_gamma_eq_of_induces
    {G : Type} [Group G] {K Bs : Subgroup G} {x : G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hx : x ∈ Bs)
    {R : Type} [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    {r : R} {φ : MulAut R} (hφ : φ = MulAut.conj r)
    (hind : LargeEvenInduces θ (fun l l' => (l' : G) = x * l * x⁻¹) φ)
    (k : ↥K) (hk : θ (QuotientGroup.mk k) = r) (y : ↥K) :
    QuotientGroup.mk' (Subgroup.center ↥K) (ggGamma K hN ⟨x, hx⟩ y) =
      QuotientGroup.mk' (Subgroup.center ↥K) k *
        QuotientGroup.mk' (Subgroup.center ↥K) y *
        (QuotientGroup.mk' (Subgroup.center ↥K) k)⁻¹ := by
  have h := hind y (ggGamma K hN ⟨x, hx⟩ y) (ggGamma_coe K hN ⟨x, hx⟩ y)
  rw [hφ, MulAut.conj_apply, ← hk] at h
  apply θ.injective
  simpa [QuotientGroup.mk'_apply, map_mul, map_inv, hk] using h.symm

private theorem exists_inn_of_rawD
    {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (hrank : 4 ≤ lab.rank) (htag : lab.tag = .D ∨ lab.tag = .twD)
    (h : LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (hR : Group R) (I F : Set (MulAut R)),
      @Q R hR I F ∧ I = @LargeEvenInnSet R hR := by
  rcases lab with ⟨tag, rank, n⟩
  dsimp only at hrank
  rcases htag with hD | htwD
  · cases hD
    dsimp only [LargeEvenRawDatum] at h
    rw [if_neg (by omega : ¬ rank = 3)] at h
    obtain ⟨K, hField, hFinite, hCard, hQ⟩ := h
    exact ⟨_, inferInstance, _, _, hQ, rfl⟩
  · cases htwD
    dsimp only [LargeEvenRawDatum] at h
    rw [if_neg (by omega : ¬ rank = 2), if_neg (by omega : ¬ rank = 3)] at h
    obtain ⟨K, hField, hFinite, hCard, b, c, hbc, hQ⟩ := h
    exact ⟨_, inferInstance, _, _, hQ, rfl⟩

theorem ggInnerDiagOn_orthogonal_quotient_gamma_inner
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} {x : G} (hmarkK : GGInnerDiagOn Bs K) (hx : x ∈ Bs)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hKlab : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K))
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hrank : 4 ≤ lab.rank) :
    ∃ β : MulAut (↥K ⧸ Subgroup.center ↥K), β ∈ LargeEvenInnSet _ ∧
      ∀ y : K, QuotientGroup.mk (ggGamma K (GGInnerDiagOn.le_normalizer hmarkK) ⟨x, hx⟩ y) =
        β (QuotientGroup.mk y) := by
  have hmark' := ggInnerDiagOn_relabel hRig hmarkK hΛ hKlab
  obtain ⟨hKperf, lab', hΛ', hraw'⟩ := hmark'
  obtain ⟨R₀, hGroup₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw'
  letI : Group R₀ := hGroup₀
  obtain ⟨hsimple₀, hnonab₀, θ₀, hEqLab, hN₀, hAct₀⟩ := hQ₀
  cases hEqLab
  obtain ⟨R, hGroup, I, F, hQ, hIeq⟩ := exists_inn_of_rawD hrank htag hraw'
  letI : Group R := hGroup
  obtain ⟨hsimple, hnonab, θ, hEqLab, hN, hAct⟩ := hQ
  obtain ⟨φ, hφI, hind⟩ := hAct x⁻¹ (Subgroup.inv_mem Bs hx)
  rw [hIeq] at hφI
  obtain ⟨r, rfl⟩ := hφI
  obtain ⟨z, hz⟩ := θ.surjective r
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective z
  let β : MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.conj (QuotientGroup.mk k)
  refine ⟨β, ⟨QuotientGroup.mk k, rfl⟩, ?_⟩
  intro y
  have hkθ : θ (QuotientGroup.mk k) = r := by rw [hk, hz]
  have hind' : LargeEvenInduces θ (fun l l' => (l' : G) = x * l * x⁻¹) (MulAut.conj r) := by
    simpa [inv_inv] using hind
  have h := quotient_gamma_eq_of_induces (K := K) (Bs := Bs) (x := x)
    (GGInnerDiagOn.le_normalizer hmarkK) hx θ rfl hind' k hkθ y
  simpa [β, MulAut.conj_apply] using h

theorem center_quotient_eq_bot_of_innerDiagOn
    {G : Type} [Group G] {Bs K : Subgroup G} (hmarkK : GGInnerDiagOn Bs K) :
    Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := by
  obtain ⟨hKperf, lab, hΛ, hraw⟩ := hmarkK
  obtain ⟨R, hGroup, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  letI : Group R := hGroup
  obtain ⟨hsimple, hnonab, θ, hN, hAct⟩ := hQ
  have hsimple' : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) :=
    (MulEquiv.isSimpleGroup_congr θ).mpr hsimple
  have hnonab' : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨θ.symm a, θ.symm b, fun h => hab (by simpa using congrArg θ h)⟩
  letI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hsimple'
  apply TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
  intro hcomm
  letI := hcomm
  obtain ⟨a, b, hab⟩ := hnonab'
  exact hab (mul_comm a b)

end CFSG.StandardType
