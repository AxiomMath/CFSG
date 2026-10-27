module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenSL
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative

private theorem rootChar_zetaVec_eq_one_iff
    {Ω : Type} [Field Ω] {p : ℕ} [NeZero p] {τ : Tag}
    {ζ : Ωˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (t : Fin τ.rank → ZMod p)
    (β : Fin τ.rank → ℤ) :
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

private theorem familyKernel_zetaVec
    {Ω : Type} [Field Ω] {p : ℕ} [NeZero p] {τ : Tag}
    {ζ : Ωˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α)
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

private theorem torusFix_eq_range
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {T : Multiplicative (Fin τ.rank → ZMod p) →*
    adjointGroup τ K} {β : Fin τ.rank → ℤ}
    (hfixset : ∀ t, ExcSplitRootGen.excRefl β t = t ↔
      ∑ j, (β j : ZMod p) * t j = 0) :
    SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β) =
      Set.range (fun t : {t : Fin τ.rank → ZMod p //
        ∑ j, (β j : ZMod p) * t j = 0} => T (Multiplicative.ofAdd t.1)) := by
  ext y
  simp only [SuSplitRootGen.torusFix, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨Multiplicative.toAdd x, (hfixset (Multiplicative.toAdd x)).1 hx⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t.1, (hfixset t.1).2 t.2, rfl⟩

private theorem phiTwoComp_le_centralizer
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [NeZero p]
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {g0 : ModGL τ (AlgebraicClosure K)}
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (Multiplicative.ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hfixset : ∀ t, ExcSplitRootGen.excRefl β t = t ↔
      ∑ j, (β j : ZMod p) * t j = 0) :
    phiTwoComp g0 β ≤
      Subgroup.centralizer (SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro y hy
  rw [torusFix_eq_range hfixset] at hy
  obtain ⟨t, rfl⟩ := hy
  set u : ModGL τ (AlgebraicClosure K) :=
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K) * g0 with hu
  have hxQ : u ∈ rootSpan τ (AlgebraicClosure K) ({β, -β} : Set (Fin τ.rank → ℤ)) := by
    rw [hu]
    exact (mem_phiTwoComp_iff).1 hx
  have hS : ({β, -β} : Set (Fin τ.rank → ℤ)) ⊆
      rootCharKernel (TableBExc.E6Three.zetaVec ζ hζ t.1) := by
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with h | h
    · rw [h]
      exact ⟨hβ, (rootChar_zetaVec_eq_one_iff hζo hζ t.1 β).2 t.2⟩
    · rw [h]
      refine ⟨IsRoot.neg hβ, ?_⟩
      have hβ1 : rootChar (TableBExc.E6Three.zetaVec ζ hζ t.1) β = 1 :=
        (rootChar_zetaVec_eq_one_iff hζo hζ t.1 β).2 t.2
      have hadd := rootChar_add (TableBExc.E6Three.zetaVec ζ hζ t.1) (-β) β
      rw [neg_add_cancel, rootChar_zero, hβ1, mul_one] at hadd
      simpa using hadd.symm
  have hcent := rootSpan_le_centralizer (TableBExc.E6Three.zetaVec ζ hζ t.1) hS hxQ
  rw [Subgroup.mem_centralizer_iff] at hcent
  have hcomm := hcent (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.1))
    (Set.mem_singleton _)
  have hxL : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K) = g0 * u * g0⁻¹ := by
    rw [hu]
    group
  apply Subtype.ext
  apply baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K))
  simp only [Subgroup.coe_mul, map_mul]
  rw [hT t.1, hxL]
  calc
    (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.1) * g0⁻¹) *
        (g0 * u * g0⁻¹) =
      g0 * (rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.1) * u) * g0⁻¹ := by group
    _ = g0 * (u * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.1)) * g0⁻¹ := by rw [hcomm]
    _ = (g0 * u * g0⁻¹) *
        (g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t.1) * g0⁻¹) := by group

private theorem conj_mem_familyCentralizer
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {g0 : ModGL τ (AlgebraicClosure K)}
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    {β : Fin τ.rank → ℤ}
    (hfixset : ∀ t, ExcSplitRootGen.excRefl β t = t ↔
      ∑ j, (β j : ZMod p) * t j = 0)
    {a : {t : Fin τ.rank → ZMod p // ∑ j, (β j : ZMod p) * t j = 0} →
      Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : ∀ t : {t : Fin τ.rank → ZMod p // ∑ j, (β j : ZMod p) * t j = 0},
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (Multiplicative.ofAdd t.1) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (a t) * g0⁻¹)
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    {c : adjointGroup τ K}
    (hc : c ∈ Subgroup.centralizer (SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β))) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0 ∈
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer τ (AlgebraicClosure K) a := by
  let f := algebraMap K (AlgebraicClosure K)
  have hxadj : g0⁻¹ * baseChangeGL f (c : ModGL τ K) * g0 ∈
      adjointGroup τ (AlgebraicClosure K) :=
    mul_mem (mul_mem (inv_mem hg0C)
      (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup f c.2)) hg0C
  refine CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.2 ⟨hxadj, ?_⟩
  intro t
  have htmem : T (Multiplicative.ofAdd t.1) ∈
      SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β) := by
    rw [torusFix_eq_range hfixset]
    exact Set.mem_range_self t
  have hcomm := (Subgroup.mem_centralizer_iff.1 hc) (T (Multiplicative.ofAdd t.1)) htmem
  have hcomm' : (T (Multiplicative.ofAdd t.1) : ModGL τ K) * (c : ModGL τ K) =
      (c : ModGL τ K) * (T (Multiplicative.ofAdd t.1) : ModGL τ K) := by
    simpa only [Subgroup.coe_mul] using
      congrArg (fun z : adjointGroup τ K => (z : ModGL τ K)) hcomm
  have hcommL : baseChangeGL f ((T (Multiplicative.ofAdd t.1) : adjointGroup τ K) :
        ModGL τ K) * baseChangeGL f (c : ModGL τ K) =
      baseChangeGL f (c : ModGL τ K) *
        baseChangeGL f ((T (Multiplicative.ofAdd t.1) : adjointGroup τ K) : ModGL τ K) := by
    simpa only [map_mul] using congrArg (baseChangeGL f) hcomm'
  have hcommD : (g0 * rootDiagUnit τ (a t) * g0⁻¹) *
      baseChangeGL f (c : ModGL τ K) =
      baseChangeGL f (c : ModGL τ K) *
        (g0 * rootDiagUnit τ (a t) * g0⁻¹) := by
    rw [← hT t]
    exact hcommL
  calc
    rootDiagUnit τ (a t) * (g0⁻¹ * baseChangeGL f (c : ModGL τ K) * g0) *
        (rootDiagUnit τ (a t))⁻¹ =
      g0⁻¹ * ((g0 * rootDiagUnit τ (a t) * g0⁻¹) *
        baseChangeGL f (c : ModGL τ K)) * g0 * (rootDiagUnit τ (a t))⁻¹ := by group
    _ = g0⁻¹ * (baseChangeGL f (c : ModGL τ K) *
        (g0 * rootDiagUnit τ (a t) * g0⁻¹)) * g0 * (rootDiagUnit τ (a t))⁻¹ := by rw [hcommD]
    _ = g0⁻¹ * baseChangeGL f (c : ModGL τ K) * g0 := by group

private theorem centralizer_le_normalizer_phiTwoComp
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [NeZero p]
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {g0 : ModGL τ (AlgebraicClosure K)}
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (Multiplicative.ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hfixset : ∀ t, ExcSplitRootGen.excRefl β t = t ↔
      ∑ j, (β j : ZMod p) * t j = 0)
    (hroot : ∀ γ, IsRoot τ γ → (∀ t : Fin τ.rank → ZMod p,
      ∑ j, (β j : ZMod p) * t j = 0 → ∑ j, (γ j : ZMod p) * t j = 0) →
      γ = β ∨ γ = -β)
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)) :
    Subgroup.centralizer (SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β)) ≤
      Subgroup.normalizer (phiTwoComp g0 β) := by
  let ι := {t : Fin τ.rank → ZMod p // ∑ j, (β j : ZMod p) * t j = 0}
  let a : ι → Fin τ.rank → (AlgebraicClosure K)ˣ :=
    fun t => TableBExc.E6Three.zetaVec ζ hζ t.1
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel a = {β, -β} :=
    familyKernel_zetaVec hζo hζ hβ hroot
  have hfamily :=
    CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_normalizer_rootSpan
      (K := AlgebraicClosure K) a
  rw [hker] at hfamily
  have key : ∀ d : adjointGroup τ K,
      d ∈ Subgroup.centralizer (SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β)) →
      ∀ x : adjointGroup τ K, x ∈ phiTwoComp g0 β →
        d * x * d⁻¹ ∈ phiTwoComp g0 β := by
    intro d hd x hx
    have hdN : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (d : ModGL τ K) * g0 ∈
        Subgroup.normalizer
          (rootSpan τ (AlgebraicClosure K) ({β, -β} : Set (Fin τ.rank → ℤ))) :=
      hfamily (conj_mem_familyCentralizer (β := β) (a := a) (hfixset := hfixset)
        (hT := fun t : {t : Fin τ.rank → ZMod p // ∑ j, (β j : ZMod p) * t j = 0} =>
          hT t.1) (hg0C := hg0C) (hc := hd))
    rw [mem_phiTwoComp_iff]
    have hxQ := (mem_phiTwoComp_iff).1 hx
    have hstep : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((d * x * d⁻¹ : adjointGroup τ K) : ModGL τ K)) * g0 =
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (d : ModGL τ K) * g0) *
          (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0) *
          (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (d : ModGL τ K) * g0)⁻¹ := by
      rw [show ((d * x * d⁻¹ : adjointGroup τ K) : ModGL τ K) =
          (d : ModGL τ K) * (x : ModGL τ K) * (d : ModGL τ K)⁻¹ from rfl]
      rw [map_mul, map_mul, map_inv]
      group
    rw [hstep]
    exact (Subgroup.mem_normalizer_iff.1 hdN
      (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0)).1 hxQ
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key c hc x hx
  · intro hx
    have h := key c⁻¹ (Subgroup.inv_mem _ hc) (c * x * c⁻¹) hx
    rwa [show c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x by group] at h

theorem isComponentOf_phiTwoComp
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] [Finite K] (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T (ofAdd t) : adjointGroup τ K) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hwβ : w • β = -β)
    (hfixset : ∀ t, ExcSplitRootGen.excRefl β t = t ↔ ∑ j, (β j : ZMod p) * t j = 0)
    (hroot : ∀ γ, IsRoot τ γ → (∀ t : Fin τ.rank → ZMod p, ∑ j, (β j : ZMod p) * t j = 0 →
      ∑ j, (γ j : ZMod p) * t j = 0) → γ = β ∨ γ = -β) :
    IsComponentOf (phiTwoComp g0 β)
      (Subgroup.centralizer (SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let C := Subgroup.centralizer (SuSplitRootGen.torusFix T (ExcSplitRootGen.excRefl β))
  have hle : phiTwoComp g0 β ≤ C :=
    phiTwoComp_le_centralizer hζo hζ hT hβ hfixset
  have hnorm : ((phiTwoComp g0 β).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    exact centralizer_le_normalizer_phiTwoComp hζo hζ hT hβ hfixset hroot hg0C
  refine ⟨hle, CFSG.Assembly.IsSubnormal.step hle hnorm
    (CFSG.Assembly.IsSubnormal.refl C), ?_⟩
  have hqs : CFSG.IsQuasisimple (phiTwoComp g0 β) :=
    isQuasisimple_phiTwoComp hK4 hFr hrat hg0C hg0 hβ hwβ
  exact ⟨Group.isPerfect_def.mp hqs.1, hqs.2.1⟩

end CFSG.StandardType.PhiTwoRootGen

end
