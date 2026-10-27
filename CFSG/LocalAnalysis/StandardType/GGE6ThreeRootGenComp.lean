module

public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenKernel
import CFSG.RankThree.PartOne.KLR.RootKernel
import CFSG.RankThree.PartOne.KLR.CoreGroup
import CFSG.RankThree.PartOne.KLR.FrobTrick

public section

namespace CFSG.StandardType.E6ThreeRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three

theorem excWeyl_conj_rootDiagUnit
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (α : {α : Fin τ.rank → ℤ // IsRoot τ α}) (x : Fin τ.rank → ZMod p) :
    ((ExcSplitRootGen.excWeyl α : adjointGroup τ K) : ModGL τ K) *
        rootDiagUnit τ (zetaVec ζ hζ x) *
        ((ExcSplitRootGen.excWeyl α : adjointGroup τ K) : ModGL τ K)⁻¹ =
      rootDiagUnit τ (zetaVec ζ hζ (ExcSplitRootGen.excRefl α.1 x)) := by
  obtain ⟨-, hmono, hmaps⟩ := rootWeylOne_spec (K := K) α.2
  have h := monomial_conj_rootDiagUnit_weylTuple (K := K) hmono hmaps (zetaVec ζ hζ x)
  rw [weylTuple_zetaVec] at h
  simpa only [ExcSplitRootGen.excWeyl, ExcSplitRootGen.excRefl] using h

private theorem rootChar_zetaVec_eq_one_iff {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p)
    (β : Fin τ.rank → ℤ) :
    rootChar (zetaVec ζ hζ x) β = 1 ↔ ∑ j, (β j : ZMod p) * x j = 0 := by
  rw [show zetaVec ζ hζ x = fun i => ζ ^ (x i).val from funext (zetaVec_apply ζ hζ x)]
  exact CFSG.RankThree.PartOne.KLR.rootChar_zetaPow_eq_one_iff_charVal
    (hζo ▸ IsPrimitiveRoot.orderOf ζ) x β

private theorem familyKernel_zetaVec_of_mem {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {V : Set (Fin τ.rank → ZMod p)} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hroot : ∀ β, IsRoot τ β → (∀ x ∈ V, ∑ j, (α j : ZMod p) * x j = 0 →
      ∑ j, (β j : ZMod p) * x j = 0) → β = α ∨ β = -α) :
    CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel (τ := τ) (K := K)
      (fun x : {x : Fin τ.rank → ZMod p // x ∈ V ∧
        ∑ j, (α j : ZMod p) * x j = 0} => zetaVec ζ hζ x.1) = {α, -α} := by
  ext β
  simp only [CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hβ, hβ1⟩
    have hzero : ∀ x ∈ V, ∑ j, (α j : ZMod p) * x j = 0 →
        ∑ j, (β j : ZMod p) * x j = 0 := by
      intro x hxV hx
      have h := hβ1 ⟨x, hxV, hx⟩
      rwa [rootChar_zetaVec_eq_one_iff hζo hζ x β] at h
    exact hroot β hβ hzero
  · intro hβ
    rcases hβ with h | h
    · rw [h]
      exact ⟨hα, fun x => (rootChar_zetaVec_eq_one_iff hζo hζ x.1 α).2 x.2.2⟩
    · rw [h]
      refine ⟨IsRoot.neg hα, fun x =>
        (rootChar_zetaVec_eq_one_iff hζo hζ x.1 (-α)).2 ?_⟩
      have hx := x.2.2
      simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, hx, neg_zero]

private theorem image_rootDiagUnit_zetaVec_eq_range {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1) {V : Set (Fin τ.rank → ZMod p)}
    {α : Fin τ.rank → ℤ} :
    (fun x => rootDiagUnit τ (zetaVec ζ hζ x)) ''
        {x | x ∈ V ∧ ∑ j, (α j : ZMod p) * x j = 0} =
      Set.range (fun i : {x : Fin τ.rank → ZMod p // x ∈ V ∧
        ∑ j, (α j : ZMod p) * x j = 0} => rootDiagUnit τ (zetaVec ζ hζ i.1)) := by
  rw [Set.image_eq_range]
  rfl

private theorem map_comap_centralizer_rootDiagUnit_eq {τ : Tag} {K : Type} [Field K]
    {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1) {V : Set (Fin τ.rank → ZMod p)}
    {α : Fin τ.rank → ℤ} :
    ((Subgroup.centralizer (Set.range (fun i : {x : Fin τ.rank → ZMod p //
        x ∈ V ∧ ∑ j, (α j : ZMod p) * x j = 0} =>
        rootDiagUnit τ (zetaVec ζ hζ i.1)))).comap (adjointGroup τ K).subtype).map
      (adjointGroup τ K).subtype =
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer (τ := τ) (K := K)
        (fun i : {x : Fin τ.rank → ZMod p // x ∈ V ∧
          ∑ j, (α j : ZMod p) * x j = 0} => zetaVec ζ hζ i.1) := by
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  ext g
  rw [CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hcent, hg⟩
    refine ⟨hg, fun i => ?_⟩
    have hc := hcent _ (Set.mem_range_self i)
    rw [hc]
    group
  · rintro ⟨hg, hconj⟩
    refine ⟨?_, hg⟩
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    calc rootDiagUnit τ (zetaVec ζ hζ i.1) * g
        = (rootDiagUnit τ (zetaVec ζ hζ i.1) * g *
            (rootDiagUnit τ (zetaVec ζ hζ i.1))⁻¹) *
            rootDiagUnit τ (zetaVec ζ hζ i.1) := by group
      _ = g * rootDiagUnit τ (zetaVec ζ hζ i.1) := by rw [hconj i]

private theorem excComp_le_comap_centralizer_rootDiagUnit
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {V : Set (Fin τ.rank → ZMod p)} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    ExcSplitRootGen.excComp (K := K) α ≤
      (Subgroup.centralizer (Set.range (fun i : {x : Fin τ.rank → ZMod p //
        x ∈ V ∧ ∑ j, (α j : ZMod p) * x j = 0} =>
        rootDiagUnit τ (zetaVec ζ hζ i.1)))).comap (adjointGroup τ K).subtype := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  rintro y ⟨s, rfl⟩
  have hsum : ∑ j, (α j : ZMod p) * s.1 j = 0 := s.2.2
  have hS : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ rootCharKernel (zetaVec ζ hζ s.1) := by
    intro β hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with h | h
    · rw [h]
      exact ⟨hα, (rootChar_zetaVec_eq_one_iff hζo hζ s.1 α).2 hsum⟩
    · rw [h]
      refine ⟨IsRoot.neg hα, ?_⟩
      have hα1 : rootChar (zetaVec ζ hζ s.1) α = 1 :=
        (rootChar_zetaVec_eq_one_iff hζo hζ s.1 α).2 hsum
      have hadd := rootChar_add (zetaVec ζ hζ s.1) (-α) α
      rw [neg_add_cancel, rootChar_zero, hα1, mul_one] at hadd
      simpa using hadd.symm
  have hxQ : (x : ModGL τ K) ∈ rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ)) := hx
  have hcent := rootSpan_le_centralizer (zetaVec ζ hζ s.1) hS hxQ
  rw [Subgroup.mem_centralizer_iff] at hcent
  exact hcent _ (Set.mem_singleton _)

private theorem isQuasisimple_excComp_of_familyKernel
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {V : Set (Fin τ.rank → ZMod p)}
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hroot : ∀ β, IsRoot τ β → (∀ x ∈ V, ∑ j, (α j : ZMod p) * x j = 0 →
      ∑ j, (β j : ZMod p) * x j = 0) → β = α ∨ β = -α) :
    CFSG.Assembly.IsQuasisimple (ExcSplitRootGen.excComp (K := K) α) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ι := {x : Fin τ.rank → ZMod p // x ∈ V ∧ ∑ j, (α j : ZMod p) * x j = 0}
  let a : ι → Fin τ.rank → Kˣ := fun x => zetaVec ζ hζ x.1
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel (τ := τ) (K := K)
      a = {α, -α} := familyKernel_zetaVec_of_mem (ζ := ζ) hζo hζ hα hroot
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
  have hcomp := ExcSplitRootGen.componentRoots_eq_pair hχker hαk
  have hQ : componentRootSpan K (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a)
      ⟦⟨α, hαk⟩⟧ = rootSpan τ K {α, -α} := by
    change rootSpan τ K (componentRoots
      (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a) ⟦⟨α, hαk⟩⟧) =
      rootSpan τ K {α, -α}
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
  have heq : ExcSplitRootGen.excComp (K := K) α =
      (componentRootSpan K (CFSG.HardMathSupport.Timmesfeld.Torality.familyChar a)
        ⟦⟨α, hαk⟩⟧).subgroupOf (adjointGroup τ K) := by
    change (rootSpan τ K {α, -α}).subgroupOf (adjointGroup τ K) = _
    rw [hQ]
  rw [heq]
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hQle) hqs'

theorem isComponentOf_excComp_of_forall_mem
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {V : Set (Fin τ.rank → ZMod p)}
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hroot : ∀ β, IsRoot τ β → (∀ x ∈ V, ∑ j, (α j : ZMod p) * x j = 0 →
      ∑ j, (β j : ZMod p) * x j = 0) → β = α ∨ β = -α) :
    IsComponentOf (ExcSplitRootGen.excComp (K := K) α)
      ((Subgroup.centralizer ((fun x => rootDiagUnit τ (zetaVec ζ hζ x)) ''
        {x | x ∈ V ∧ ∑ j, (α j : ZMod p) * x j = 0})).comap (adjointGroup τ K).subtype) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let ι := {x : Fin τ.rank → ZMod p // x ∈ V ∧ ∑ j, (α j : ZMod p) * x j = 0}
  let a : ι → Fin τ.rank → Kˣ := fun x => zetaVec ζ hζ x.1
  have himg : (fun x => rootDiagUnit τ (zetaVec ζ hζ x)) ''
      {x | x ∈ V ∧ ∑ j, (α j : ZMod p) * x j = 0} =
      Set.range (fun i : ι => rootDiagUnit τ (a i)) :=
    image_rootDiagUnit_zetaVec_eq_range (ζ := ζ) (hζ := hζ) (V := V) (α := α)
  rw [himg]
  have hker : CFSG.HardMathSupport.Timmesfeld.Torality.familyKernel (τ := τ) (K := K)
      a = {α, -α} := familyKernel_zetaVec_of_mem (ζ := ζ) hζo hζ hα hroot
  have hD : ((Subgroup.centralizer (Set.range (fun i : ι => rootDiagUnit τ (a i)))).comap
      (adjointGroup τ K).subtype).map (adjointGroup τ K).subtype =
      CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer (τ := τ) (K := K) a :=
    map_comap_centralizer_rootDiagUnit_eq (ζ := ζ) (hζ := hζ) (V := V) (α := α)
  have hHX : ExcSplitRootGen.excComp (K := K) α ≤
      (Subgroup.centralizer (Set.range (fun i : ι => rootDiagUnit τ (a i)))).comap
        (adjointGroup τ K).subtype :=
    excComp_le_comap_centralizer_rootDiagUnit (ζ := ζ) hζo hζ hα
  have hN := CFSG.HardMathSupport.Timmesfeld.Torality.familyCentralizer_le_normalizer_rootSpan
    (K := K) a
  rw [hker] at hN
  have hle : ((Subgroup.centralizer (Set.range (fun i : ι => rootDiagUnit τ (a i)))).comap
      (adjointGroup τ K).subtype).map (adjointGroup τ K).subtype ≤
      Subgroup.normalizer (rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ)) :
        Set (ModGL τ K)) := by
    rw [hD]
    exact hN
  have hnorm : ((ExcSplitRootGen.excComp (K := K) α).subgroupOf
      ((Subgroup.centralizer (Set.range (fun i : ι => rootDiagUnit τ (a i)))).comap
        (adjointGroup τ K).subtype)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHX]
    change ((Subgroup.centralizer (Set.range (fun i : ι => rootDiagUnit τ (a i)))).comap
        (adjointGroup τ K).subtype) ≤
      Subgroup.normalizer ((rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ))).subgroupOf
        (adjointGroup τ K))
    rw [← Subgroup.subgroupOf_normalizer_eq
      (H := rootSpan τ K ({α, -α} : Set (Fin τ.rank → ℤ))) (N := adjointGroup τ K)
      (rootSpan_le_adjointGroup K _)]
    intro x hx
    exact hle (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  refine ⟨hHX, CFSG.Assembly.IsSubnormal.step hHX hnorm
    (CFSG.Assembly.IsSubnormal.refl _), ?_⟩
  exact isQuasisimple_excComp_of_familyKernel (ζ := ζ) hp2 hζo hζ hα hroot

end CFSG.StandardType.E6ThreeRootGen

end
