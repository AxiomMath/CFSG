module

public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyNormalizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Root
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.ExcSplitRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableB Multiplicative

variable {τ : Tag} {K : Type} [Field K] {p : ℕ}

private theorem rootChar_zetaVec_eq_one_iff [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (t : Fin τ.rank → ZMod p) (β : Fin τ.rank → ℤ) :
    rootChar (CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ t) β = 1 ↔
      ∑ j, (β j : ZMod p) * t j = 0 := by
  rw [CFSG.StandardType.NoOffE8Five.rootChar_zetaVec]
  constructor
  · intro h
    have h1 : Multiplicative.ofAdd (∑ j, (β j : ZMod p) * t j) = 1 :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [h, map_one])
    simpa using congrArg Multiplicative.toAdd h1
  · intro h
    rw [h]
    simp

private theorem familyKernel_zetaVec [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hroot : ∀ β, IsRoot τ β → (∀ t : Fin τ.rank → ZMod p,
      ∑ j, (α j : ZMod p) * t j = 0 → ∑ j, (β j : ZMod p) * t j = 0) →
      β = α ∨ β = -α) :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel
      (fun t : {t : Fin τ.rank → ZMod p // ∑ j, (α j : ZMod p) * t j = 0} =>
        CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ t.1) = {α, -α} := by
  ext β
  simp only [CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hβ, hβ1⟩
    have hzero : ∀ t : Fin τ.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
        ∑ j, (β j : ZMod p) * t j = 0 := by
      intro t ht
      have h := hβ1 ⟨t, ht⟩
      rwa [rootChar_zetaVec_eq_one_iff hζo hζ t β] at h
    rcases hroot β hβ hzero with h | h <;> simp [h]
  · intro hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with h | h
    · rw [h]
      exact ⟨hα, fun t => (rootChar_zetaVec_eq_one_iff hζo hζ t.1 α).2 t.2⟩
    · rw [h]
      refine ⟨IsRoot.neg hα, fun t => (rootChar_zetaVec_eq_one_iff hζo hζ t.1 (-α)).2 ?_⟩
      have ht := t.2
      simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, ht, neg_zero]

private theorem componentRoots_eq_pair
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {α : Fin τ.rank → ℤ} (hker : kernelRoots χ = {α, -α}) (hαk : α ∈ kernelRoots χ) :
    componentRoots χ (⟦⟨α, hαk⟩⟧ : KernelComponent χ) = {α, -α} := by
  have hα : IsRoot τ α := hαk.1
  have hnegk : -α ∈ kernelRoots χ := by rw [hker]; exact Or.inr rfl
  have hne : CFSG.LieType.Steinberg.Adjoint.iform (-α) α ≠ 0 := by
    have hpos : 0 < CFSG.LieType.Steinberg.Adjoint.iform α α := iform_self_pos_of_isRoot hα
    have hneg : CFSG.LieType.Steinberg.Adjoint.iform (-α) α =
        -CFSG.LieType.Steinberg.Adjoint.iform α α := by
      simp only [CFSG.LieType.Steinberg.Adjoint.iform, Pi.neg_apply, neg_mul,
        Finset.sum_neg_distrib]
    rw [hneg]
    omega
  ext β
  change (∃ h : β ∈ kernelRoots χ, (⟦⟨β, h⟩⟧ : KernelComponent χ) = ⟦⟨α, hαk⟩⟧) ↔
    β ∈ ({α, -α} : Set (Fin τ.rank → ℤ))
  constructor
  · rintro ⟨hβ, -⟩
    rw [hker] at hβ
    exact hβ
  · intro hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with h | h
    · rw [h]
      exact ⟨hαk, rfl⟩
    · rw [h]
      exact ⟨hnegk,
        mk_eq_of_iform_ne_zero (α := (⟨-α, hnegk⟩ : kernelRoots χ))
          (β := (⟨α, hαk⟩ : kernelRoots χ)) hne⟩

section Dvd


theorem dvd_card_excComp [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hroot : ∀ β, IsRoot τ β → (∀ t : Fin τ.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
      ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α) :
    p ∣ Nat.card (excComp (K := K) α) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  let a : {t : Fin τ.rank → ZMod p // ∑ j, (α j : ZMod p) * t j = 0} →
      Fin τ.rank → Kˣ := fun t => CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ t.1
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a = {α, -α} :=
    familyKernel_zetaVec hζo hζ hα hroot
  have hχker : kernelRoots (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) =
      {α, -α} := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.kernelRoots_familyChar, hker]
  have hαk : α ∈ kernelRoots (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) := by
    rw [hχker]; exact Or.inl rfl
  have hcomp := componentRoots_eq_pair hχker hαk
  have hQ : componentRootSpan K (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a)
      ⟦⟨α, hαk⟩⟧ = rootSpan τ K {α, -α} := by
    change rootSpan τ K (componentRoots (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a)
      ⟦⟨α, hαk⟩⟧) = rootSpan τ K {α, -α}
    rw [hcomp]
  change p ∣ Nat.card ((rootSpan τ K {α, -α}).subgroupOf (adjointGroup τ K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (rootSpan_le_adjointGroup (τ := τ) K ({α, -α} : Set (Fin τ.rank → ℤ)))).toEquiv]
  rw [← hQ]
  exact LayerPDivExc.dvd_card_componentRootSpan (Fact.out : p.Prime) hp2 hζo _

end Dvd

section Comp


theorem isComponentOf_excComp [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hfixset : ∀ t, excRefl α t = t ↔ ∑ j, (α j : ZMod p) * t j = 0)
    (hroot : ∀ β, IsRoot τ β → (∀ t : Fin τ.rank → ZMod p, ∑ j, (α j : ZMod p) * t j = 0 →
      ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α) :
    IsComponentOf (excComp (K := K) α)
      (Subgroup.centralizer (SuSplitRootGen.torusFix (excTorusHom hfullp hζ) (excRefl α))) := by
  let ι := {t : Fin τ.rank → ZMod p // ∑ j, (α j : ZMod p) * t j = 0}
  let a : ι → Fin τ.rank → Kˣ := fun t => CFSG.StandardType.TableBExc.E6Three.zetaVec ζ hζ t.1
  let u : ι → ↥(adjointGroup τ K) :=
    fun t => excTorusHom hfullp hζ (Multiplicative.ofAdd t.1)
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a = {α, -α} :=
    familyKernel_zetaVec hζo hζ hα hroot
  have hfix : SuSplitRootGen.torusFix (excTorusHom hfullp hζ) (excRefl α) = Set.range u := by
    ext y
    simp only [SuSplitRootGen.torusFix, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨Multiplicative.toAdd x, (hfixset (Multiplicative.toAdd x)).1 hx⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.ofAdd t.1, (hfixset t.1).2 t.2, rfl⟩
  have hXmap : (Subgroup.centralizer
        (SuSplitRootGen.torusFix (excTorusHom hfullp hζ) (excRefl α))).map
        (adjointGroup τ K).subtype =
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ K a := by
    rw [hfix]
    ext g
    rw [Subgroup.mem_map, CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, fun s => ?_⟩
      have hu : (u s : ModGL τ K) = rootDiagUnit τ (a s) :=
        coe_excTorusHom hfullp hζ (Multiplicative.ofAdd s.1)
      have hcomm := congrArg (fun z : ↥(adjointGroup τ K) => (z : ModGL τ K))
        ((Subgroup.mem_centralizer_iff.1 hx) (u s) (Set.mem_range_self s))
      simp only [Subgroup.coe_mul] at hcomm
      rw [hu] at hcomm
      calc rootDiagUnit τ (a s) * (x : ModGL τ K) * (rootDiagUnit τ (a s))⁻¹
          = (x : ModGL τ K) * rootDiagUnit τ (a s) * (rootDiagUnit τ (a s))⁻¹ := by
            rw [hcomm]
        _ = (x : ModGL τ K) := by rw [mul_assoc, mul_inv_cancel, mul_one]
    · rintro ⟨hgC, hgs⟩
      refine ⟨⟨g, hgC⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨s, rfl⟩
      apply Subtype.ext
      have hu : (u s : ModGL τ K) = rootDiagUnit τ (a s) :=
        coe_excTorusHom hfullp hζ (Multiplicative.ofAdd s.1)
      have hs := hgs s
      have hcongr := congrArg (fun z => z * rootDiagUnit τ (a s)) hs
      simp only [Subgroup.coe_mul]
      rw [hu]
      have hleft : rootDiagUnit τ (a s) * g * (rootDiagUnit τ (a s))⁻¹ *
          rootDiagUnit τ (a s) = rootDiagUnit τ (a s) * g := by group
      rw [hleft] at hcongr
      exact hcongr
  have hHX : excComp (K := K) α ≤
      Subgroup.centralizer (SuSplitRootGen.torusFix (excTorusHom hfullp hζ) (excRefl α)) := by
    rw [hfix]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨s, rfl⟩
    have hxQ : (x : ModGL τ K) ∈ rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ)) := hx
    have hS : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ rootCharKernel (a s) := by
      intro β hβ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
      rcases hβ with h | h
      · rw [h]
        exact ⟨hα, (rootChar_zetaVec_eq_one_iff hζo hζ s.1 α).2 s.2⟩
      · rw [h]
        refine ⟨IsRoot.neg hα, ?_⟩
        have hα1 : rootChar (a s) α = 1 :=
          (rootChar_zetaVec_eq_one_iff hζo hζ s.1 α).2 s.2
        have hadd := rootChar_add (a s) (-α) α
        rw [neg_add_cancel, rootChar_zero, hα1, mul_one] at hadd
        simpa using hadd.symm
    have hcent := rootSpan_le_centralizer (a s) hS hxQ
    rw [Subgroup.mem_centralizer_iff] at hcent
    have hcomm := hcent (rootDiagUnit τ (a s)) (Set.mem_singleton _)
    apply Subtype.ext
    have hu : (u s : ModGL τ K) = rootDiagUnit τ (a s) :=
      coe_excTorusHom hfullp hζ (Multiplicative.ofAdd s.1)
    simp only [Subgroup.coe_mul]
    rw [hu]
    exact hcomm
  have hN := CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_normalizer_rootSpan
    (K := K) a
  rw [hker] at hN
  have hle : (Subgroup.centralizer
        (SuSplitRootGen.torusFix (excTorusHom hfullp hζ) (excRefl α))).map
        (adjointGroup τ K).subtype ≤
      Subgroup.normalizer (rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ)) :
        Set (ModGL τ K)) := by
    rw [hXmap]
    exact hN
  have hnorm : ((excComp (K := K) α).subgroupOf (Subgroup.centralizer
      (SuSplitRootGen.torusFix (excTorusHom hfullp hζ) (excRefl α)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHX]
    change Subgroup.centralizer (SuSplitRootGen.torusFix (excTorusHom hfullp hζ) (excRefl α)) ≤
      Subgroup.normalizer ((rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ))).subgroupOf
        (adjointGroup τ K))
    rw [← Subgroup.subgroupOf_normalizer_eq
      (H := rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ))) (N := adjointGroup τ K)
      (rootSpan_le_adjointGroup K _)]
    intro x hx
    exact hle (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  refine ⟨hHX, CFSG.Assembly.IsSubnormal.step hHX hnorm (CFSG.Assembly.IsSubnormal.refl _), ?_⟩
  have ht : ζ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 h
    rw [hζo] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp2 h2
  have hχker : kernelRoots (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) =
      {α, -α} := by
    rw [CFSG.HardMathSupport.Timmesfeld.Torality.kernelRoots_familyChar, hker]
  have hαk : α ∈ kernelRoots (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) := by
    rw [hχker]; exact Or.inl rfl
  have hcomp := componentRoots_eq_pair hχker hαk
  have hQ : componentRootSpan K (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a)
      ⟦⟨α, hαk⟩⟧ = rootSpan τ K {α, -α} := by
    change rootSpan τ K (componentRoots (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a)
      ⟦⟨α, hαk⟩⟧) = rootSpan τ K {α, -α}
    rw [hcomp]
  have hqs : CFSG.IsQuasisimple (componentRootSpan K
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) ⟦⟨α, hαk⟩⟧) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isQuasisimple_componentRootSpan_of_sq_ne_one
      ht ⟦⟨α, hαk⟩⟧
  have hqs' : CFSG.Assembly.IsQuasisimple (componentRootSpan K
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) ⟦⟨α, hαk⟩⟧) :=
    ⟨Group.isPerfect_def.mp hqs.1, hqs.2.1⟩
  have hQle : componentRootSpan K (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a)
      ⟦⟨α, hαk⟩⟧ ≤ adjointGroup τ K := rootSpan_le_adjointGroup K _
  have heq : excComp (K := K) α = (componentRootSpan K
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) ⟦⟨α, hαk⟩⟧).subgroupOf
      (adjointGroup τ K) := by
    change (rootSpan τ K {α, -α}).subgroupOf (adjointGroup τ K) = _
    rw [hQ]
  rw [heq]
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hQle) hqs'

end Comp

end CFSG.StandardType.ExcSplitRootGen
