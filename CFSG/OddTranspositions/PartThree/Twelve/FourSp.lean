module

public import CFSG.OddTranspositions.PartThree.Twelve.Four
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockSp
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsC
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
import CFSG.RankThree.GF2n.Tim78a.GriessSpMultiplier
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.Adapters.RankTwoModelTransports
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.OddTranspositions.WidthSylow
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width
import Certificates.Certificate1
import Certificates.Certificate2
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.OddTranspositions.PartFour

section SpModel

variable {k : ℕ} {F : Type} [Field F]

theorem exists_spForm_eq_zero_forall_ne_smul (hk : 2 ≤ k) {u : Fin k ⊕ Fin k → F}
    (hu : u ≠ 0) : ∃ w, spForm k F w u = 0 ∧ ∀ a : F, w ≠ a • u := by
  classical
  set f : (Fin k ⊕ Fin k → F) →ₗ[F] F := (spForm k F).flip u with hf
  have hfx : ∀ x, f x = spForm k F x u := fun x => rfl
  obtain ⟨z, hz⟩ : ∃ z, spForm k F z u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (spForm_nondegenerate.2 u h)
  have hrange : LinearMap.range f = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨(c / spForm k F z u) • z, ?_⟩
    rw [map_smul, hfx, smul_eq_mul, div_mul_cancel₀ _ hz]
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, Fintype.card_fin] at hdim
  have hnle : ¬ LinearMap.ker f ≤ Submodule.span F {u} := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu] at this
    omega
  obtain ⟨w, hwk, hws⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨w, by simpa [hfx] using LinearMap.mem_ker.mp hwk, fun a hwa => hws ?_⟩
  rw [hwa]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self u)

theorem spEnd_spTransvection_mul_mul_apply {a b e : Fin k ⊕ Fin k → F}
    (hba : spForm k F b a = 0) (hea : spForm k F e a = 0) (heb : spForm k F e b = 0) (c : F)
    (x : Fin k ⊕ Fin k → F) :
    spEnd (spTransvection a c * spTransvection b c * spTransvection e c) x =
      x + (c * spForm k F x a) • a + (c * spForm k F x b) • b + (c * spForm k F x e) • e := by
  simp only [spEnd_mul, Module.End.mul_apply, spEnd_spTransvection, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hba, hea, heb, mul_zero, add_zero,
    zero_smul]

theorem spTransvection_eq_mul_mul [CharP F 2] {u w : Fin k ⊕ Fin k → F}
    (huw : spForm k F u w = 0) (c l : F) :
    spTransvection u c = spTransvection (u + l • w) c * spTransvection (u + w) c *
      spTransvection (u + (l + 1) • w) c := by
  have hwu : spForm k F w u = 0 := by rw [← spForm_isAlt.neg_eq, huw, neg_zero]
  have h0 : ∀ a b : F, spForm k F (u + a • w) (u + b • w) = 0 := by
    intro a b
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [spForm_isAlt u, spForm_isAlt w, huw, hwu]
    ring
  have h1 : ∀ a : F, spForm k F (u + a • w) (u + w) = 0 := fun a => by
    have := h0 a 1
    rwa [one_smul] at this
  have h2 : ∀ b : F, spForm k F (u + w) (u + b • w) = 0 := fun b => by
    have := h0 1 b
    rwa [one_smul] at this
  refine spLin_injective (Units.ext (LinearMap.ext fun x => ?_))
  change spEnd (spTransvection u c) x = spEnd (spTransvection (u + l • w) c *
    spTransvection (u + w) c * spTransvection (u + (l + 1) • w) c) x
  rw [spEnd_spTransvection_mul_mul_apply (h2 l) (h0 (l + 1) l) (h1 (l + 1))]
  rw [spEnd_spTransvection]
  simp only [map_add, map_smul, smul_eq_mul]
  generalize spForm k F x u = p
  generalize spForm k F x w = q
  have key : x + (c * (p + l * q)) • (u + l • w) + (c * (p + q)) • (u + w) +
      (c * (p + (l + 1) * q)) • (u + (l + 1) • w) = x + (c * p) • u +
      (2 : F) • ((c * p + c * (l + 1) * q) • u +
        (c * p * (l + 1) + c * q * (l ^ 2 + l + 1)) • w) := by
    module
  rw [key, CharTwo.two_eq_zero, zero_smul, add_zero]

theorem exists_ne_zero_ne_one_of_four_le [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  haveI := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun l _ => by
    by_cases hl : l = 0
    · simp [hl]
    · simp [hcon l hl]
  have hle : Fintype.card F ≤ 2 :=
    (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Nat.card_eq_fintype_card] at h4
  omega

theorem isRootTriple_of_isSymplecticTransvection {X : Type} [Group X] {E : Set X}
    (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g}) (hZ : Subgroup.center X = ⊥) {s : X} (hs : s ∈ E)
    {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f) (h : IsSymplecticTransvection X m f s) :
    IsRootTriple E s := by
  classical
  obtain ⟨k, hmk, F, _, _, hF, e, hrank⟩ := h
  have hk : 2 ≤ k := by omega
  haveI : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  set ψ : X →* StatedSp k F := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    with hψdef
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨u, c, hu, hc, hψs⟩ := borel86_spn_eq_spTransvection hrank
  change ψ s = spTransvection u c at hψs
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => hψinj (by rw [map_mul, map_mul]; exact h.eq)⟩
  have hEs : ∀ x, x ∈ E ↔ IsConj s x := by
    obtain ⟨d₀, rfl⟩ := hcls
    intro x
    exact ⟨fun hx => (isConj_comm.mp hs).trans hx, fun hx => (show IsConj d₀ s from hs).trans hx⟩
  have hEmem : ∀ v, v ≠ 0 → ∃ y ∈ E, ψ y = spTransvection v c := by
    intro v hv
    obtain ⟨g, hg⟩ := exists_spEnd_eq hu hv
    obtain ⟨g', hg'⟩ := hψsurj g
    refine ⟨g' * s * g'⁻¹, (hEs _).mpr (isConj_iff.mpr ⟨g', rfl⟩), ?_⟩
    rw [map_mul, map_mul, map_inv, hg', hψs, conj_spTransvection, hg]
  have hout : ∀ y ∈ E, ∀ a, ψ y = spTransvection a c → (∀ t : F, a ≠ t • u) →
      y ∉ rootBlock E s := by
    intro y _ a hya ha hyr
    obtain ⟨x, hxu, hxa⟩ := exists_spForm_eq_zero_ne_zero hu ha
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxa (by simp)
    obtain ⟨z, hz, hψz⟩ := hEmem x hx0
    have h1 : Commute z s := by
      rw [hcomm, hψz, hψs, commute_spTransvection_iff hc hc]
      exact hxu
    have h2 : ¬ Commute z y := by
      rw [hcomm, hψz, hya, commute_spTransvection_iff hc hc]
      exact hxa
    exact h2 ((hyr.2 z hz).mpr h1)
  obtain ⟨w, hwu, hw⟩ := exists_spForm_eq_zero_forall_ne_smul hk hu
  have huw : spForm k F u w = 0 := by rw [← spForm_isAlt.neg_eq, hwu, neg_zero]
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one_of_four_le (F := F) (by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
  have hl1' : l + 1 ≠ 0 := by
    intro h
    apply hl1
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have hnot : ∀ t : F, t ≠ 0 → ∀ r : F, u + t • w ≠ r • u := by
    intro t ht r hr
    apply hw (t⁻¹ * (r - 1))
    have htw : t • w = (r - 1) • u := by
      rw [sub_smul, one_smul, ← hr]
      abel
    rw [mul_smul, ← htw, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hne0 : ∀ t : F, t ≠ 0 → u + t • w ≠ 0 := fun t ht h0 =>
    hnot t ht 0 (by rw [h0, zero_smul])
  have hB : ∀ a b : F, spForm k F (u + a • w) (u + b • w) = 0 := by
    intro a b
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [spForm_isAlt u, spForm_isAlt w, huw, hwu]
    ring
  obtain ⟨y₁, hy₁, hψ₁⟩ := hEmem _ (hne0 l hl0)
  obtain ⟨y₂, hy₂, hψ₂⟩ := hEmem _ (hne0 1 one_ne_zero)
  obtain ⟨y₃, hy₃, hψ₃⟩ := hEmem _ (hne0 (l + 1) hl1')
  refine ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hout y₁ hy₁ _ hψ₁ (hnot l hl0),
    hout y₂ hy₂ _ hψ₂ (hnot 1 one_ne_zero), hout y₃ hy₃ _ hψ₃ (hnot _ hl1'), ?_, ?_, ?_, ?_⟩
  · rw [hcomm, hψ₁, hψ₂, commute_spTransvection_iff hc hc]
    exact hB l 1
  · rw [hcomm, hψ₁, hψ₃, commute_spTransvection_iff hc hc]
    exact hB l (l + 1)
  · rw [hcomm, hψ₂, hψ₃, commute_spTransvection_iff hc hc]
    exact hB 1 (l + 1)
  · apply hψinj
    rw [map_mul, map_mul, hψ₁, hψ₂, hψ₃, hψs, one_smul]
    exact spTransvection_eq_mul_mul huw c l

theorem commutator_eq_top_and_ker_eq_bot_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (h : IsSymplecticTransvection X m f s) :
    commutator X = ⊤ ∧ ∀ (Γ : Type) [Group Γ] (φ : Γ →* X), Function.Surjective φ →
      φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ → φ.ker = ⊥ := by
  classical
  obtain ⟨k, hmk, F, _, _, hF, e, -⟩ := h
  have hk : 2 ≤ k := by omega
  haveI : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let ψ : X ≃* StatedSp k F :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  let φF : F ≃+* GaloisField 2 f := (GaloisField.algEquivGaloisField 2 f hF).toRingEquiv
  let χ : StatedSp k F ≃* StatedSp k (GaloisField 2 f) :=
    ((StatedSp k F).equivMapOfInjective
      (CFSG.Adapters.RankTwoModelTransports.glCongr φF).toMonoidHom
      (CFSG.Adapters.RankTwoModelTransports.glCongr φF).injective).trans
      (MulEquiv.subgroupCongr (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φF k))
  refine ⟨?_, fun Γ _ φ hφ hcen hcomm => ?_⟩
  · have h4 : ∃ t : Finset F, t.card = 4 := by
      haveI := Fintype.ofFinite F
      have : 4 ≤ (Finset.univ : Finset F).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq this
      exact ⟨t, ht⟩
    haveI : Group.IsPerfect (StatedSp k F) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp k F (Or.inl h4)
    haveI : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  · have hker : ((ψ.trans χ).toMonoidHom.comp φ).ker = φ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    have h1 := CFSG.RankThree.GF2n.Tim79a.griessSpMultiplierStatement_holds k f (by omega)
      (by omega)
      (by intro h; simp only [Prod.mk.injEq] at h; omega)
      (by intro h; simp only [Prod.mk.injEq] at h; omega)
      (by intro h; simp only [Prod.mk.injEq] at h; omega)
      (by intro h; simp only [Prod.mk.injEq] at h; omega)
      Γ ((ψ.trans χ).toMonoidHom.comp φ) ((ψ.trans χ).surjective.comp hφ)
      (by rw [hker]; exact hcen) (by rw [hker]; exact hcomm)
    rwa [hker] at h1

end SpModel

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem alpha_eq_singleton_of_isSymplecticTransvection (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {m f : ℕ} (hm : 4 ≤ m) (hf : 2 ≤ f)
    (h : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) :
    hC.alpha = {hC.d} := by
  have hZ : Subgroup.center
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ := by
    have h1 := center_le_solvableRadical
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    rw [solvableRadical_quotient_H hC] at h1
    exact le_bot_iff.mp h1
  obtain ⟨hb1, hne⟩ :=
    subset_rootBlock_and_ne_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs h
  have htri := isRootTriple_of_isSymplecticTransvection (imageClass_isClass hC) hZ hs hm hf h
  obtain ⟨htop, hmult⟩ := commutator_eq_top_and_ker_eq_bot_of_isSymplecticTransvection hZ hm hf h
  have hodd := odd_card_center_inf_commutator_of_multiplier hC hMZ
    (by rw [htop, ← commutator_def, htop]) (by
      intro Γ _ _ φ hφ hcen hcomm
      let θ : ↥(commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) ≃*
          (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      have hker : (θ.toMonoidHom.comp φ).ker = φ.ker := by
        ext g
        simp [MonoidHom.mem_ker]
      have h1 := hmult Γ (θ.toMonoidHom.comp φ) (θ.surjective.comp hφ)
        (by rw [hker]; exact hcen) (by rw [hker]; exact hcomm)
      rw [hker] at h1
      rw [h1, Subgroup.card_bot]
      exact odd_one)
  exact alpha_eq_singleton_of_isRootTriple hC hMZ hs hb1 hne htri hodd

end CFSG.OddTranspositions.PartThree
