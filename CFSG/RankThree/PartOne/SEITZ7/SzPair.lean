module

public import CFSG.RankThree.PartOne.SEITZ7.SzRoot
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne
public import CFSG.LieType.Ree.LargeReeB2FixedCoordinates
public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

@[expose] def szSetA : Set (Fin Tag.F4.rank → ℤ) := {γ | γ ∈ szRootsA}

@[expose] def szSetB : Set (Fin Tag.F4.rank → ℤ) := {γ | γ ∈ szRootsB}

@[expose] def szW : WeylGroup F4.tag := F4.fixedRelElt ⟨5, by decide⟩

@[expose] def szWord : List (Fin Tag.F4.rank) :=
  (F4.fixedRelWord ⟨5, by decide⟩).flatMap F4.fixedOrbitWord

@[expose] def szFold (w : List (Fin Tag.F4.rank)) (γ : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → ℤ :=
  w.foldr (reflect Tag.F4) γ

theorem szW_foldr : ∀ γ ∈ szRootsA, szFold szWord γ ∈ szRootsB := by
  decide +kernel

theorem szRootsA_mem_largeReeRoot : ∀ i : Fin 4, largeReeRoot i ∈ szRootsA := by
  decide +kernel

theorem szRootsA_single : ∀ j : Fin Tag.F4.rank, j.val = 1 ∨ j.val = 2 →
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ szRootsA ∧
      (-Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ szRootsA := by
  decide +kernel

theorem isRoot_of_mem_szRootsA
    {γ : Fin Tag.F4.rank → ℤ} (h : γ ∈ szRootsA) : IsRoot Tag.F4 γ := by
  obtain ⟨m, hm, rfl⟩ := szRootsA_pos γ h
  exact RootWalk.isRoot_rootCertificate_root hm

theorem isRoot_of_mem_szRootsB
    {γ : Fin Tag.F4.rank → ℤ} (h : γ ∈ szRootsB) : IsRoot Tag.F4 γ := by
  obtain ⟨m, hm, rfl⟩ := szRootsB_pos γ h
  exact RootWalk.isRoot_rootCertificate_root hm

theorem szW_smul
    {γ : Fin F4.tag.rank → ℤ} (hγ : γ ∈ szRootsA) : szW • γ ∈ szRootsB := by
  rw [szW, ReeTag.fixedRelElt, ReeTag.list_prod_map_fixedOrbitElement,
    CFSG.LieType.Ree.wordProd_smul]
  exact szW_foldr γ hγ

theorem rootSpan_mono' {τ : Tag} {K : Type} [Field K]
    {S T : Set (Fin τ.rank → ℤ)} (h : S ⊆ T) :
    rootSpan τ K S ≤ rootSpan τ K T :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (h hα) le_rfl

theorem weylElt_mem_rootSpan' {τ : Tag} {K : Type} [Field K]
    {S : Set (Fin τ.rank → ℤ)} {j : Fin τ.rank}
    (h1 : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ S) (h2 : (-Pi.single j 1 : Fin τ.rank → ℤ) ∈ S)
    (u : Kˣ) : weylElt τ K j u ∈ rootSpan τ K S := by
  have hx : ∀ c : K, xUnit τ K j c ∈ rootSpan τ K S := fun c =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ S) => rootSubgroup τ K δ) _ h1 le_rfl
      (xUnit_mem_rootSubgroup j c)
  have hy : ∀ c : K, yUnit τ K j c ∈ rootSpan τ K S := fun c =>
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ S) => rootSubgroup τ K δ) _ h2 le_rfl
      (yUnit_mem_rootSubgroup j c)
  rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem torusElt_mem_rootSpan' {τ : Tag} {K : Type} [Field K]
    {S : Set (Fin τ.rank → ℤ)} {j : Fin τ.rank}
    (h1 : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ S) (h2 : (-Pi.single j 1 : Fin τ.rank → ℤ) ∈ S)
    (u : Kˣ) : torusElt τ K j u ∈ rootSpan τ K S := by
  have e : torusElt τ K j u = weylElt τ K j u * (weylElt τ K j 1)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElt_eq_torusElt_mul_weylElt_one j u).symm
  rw [e]
  exact mul_mem (weylElt_mem_rootSpan' h1 h2 u) (inv_mem (weylElt_mem_rootSpan' h1 h2 1))

section Pair

variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

variable {K a}

theorem rankOneGroupTwo_le_rootSpan
    : rankOneGroupTwo K a ≤ rootSpan F4.tag K szSetA := by
  have hS1 : ∀ j : Fin Tag.F4.rank, j.val = 1 ∨ j.val = 2 →
      (Pi.single j 1 : Fin F4.tag.rank → ℤ) ∈ szSetA ∧
        (-Pi.single j 1 : Fin F4.tag.rank → ℤ) ∈ szSetA := fun j hj => szRootsA_single j hj
  rw [rankOneGroupTwo, Subgroup.closure_le]
  rintro g ((hg | ⟨v, rfl⟩) | rfl)
  · refine rootSpan_mono' ?_ (Subgroup.mem_inf.1 hg).1
    intro α hα
    rw [F4_fixedOrbitRoots_one] at hα
    obtain ⟨i, rfl⟩ := mem_largeReeBlockRoots.1 hα
    exact szRootsA_mem_largeReeRoot i
  · rw [SetLike.mem_coe, LargeReeCover.pairedTorusHom_apply]
    exact mul_mem (torusElt_mem_rootSpan' (hS1 _ (Or.inl rfl)).1 (hS1 _ (Or.inl rfl)).2 _)
      (torusElt_mem_rootSpan' (hS1 _ (Or.inr rfl)).1 (hS1 _ (Or.inr rfl)).2 _)
  · have hred : (coxeterSystem F4.tag).IsReduced (F4.fixedOrbitWord ⟨1, by decide⟩) := by
      have h := CFSG.LieType.Simplicity.isReduced_reeOrbitWord F4 (1 : Fin 4)
      have e : F4.reeOrbitWord (1 : Fin 4) = F4.fixedOrbitWord ⟨1, by decide⟩ := by decide
      rwa [e] at h
    have hword : ∀ i ∈ F4.fixedOrbitWord ⟨1, by decide⟩, i.val = 1 ∨ i.val = 2 := by
      decide +kernel
    show canonicalRep (coxeterSystem F4.tag) K
      ((coxeterSystem F4.tag).wordProd (F4.fixedOrbitWord ⟨1, by decide⟩)) ∈ _
    rw [canonicalRep_wordProd hred]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' := hS1 i (hword i hi)
    exact weylElt_mem_rootSpan' hi'.1 hi'.2 1

@[expose] noncomputable def szNw (K : Type) [Field K] :
    ModGL F4.tag K :=
  canonicalRep (coxeterSystem F4.tag) K szW

@[expose] noncomputable def szSubB (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    : Subgroup (ModGL F4.tag K) :=
  (rankOneGroupTwo K a).map (MulAut.conj (szNw K)).toMonoidHom

theorem szNw_mem_reeGamma
    : szNw K ∈ F4.reeGamma K a :=
  (Subgroup.mem_inf.1 (canonicalRep_mem_reeFixedMonomial F4 K a (fixedRelElt_mem _))).2

theorem szSubB_le_rootSpan
    : szSubB K a ≤ rootSpan F4.tag K szSetB := by
  rintro _ ⟨g, hg, rfl⟩
  have h1 : g ∈ rootSpan F4.tag K szSetA := rankOneGroupTwo_le_rootSpan hg
  have hS : ∀ α ∈ szSetA, IsRoot F4.tag α := fun α hα => isRoot_of_mem_szRootsA hα
  have h2 := canonicalRep_conj_mem_rootSpan (w := szW) hS h1
  refine rootSpan_mono' ?_ h2
  rintro _ ⟨α, hα, rfl⟩
  exact szW_smul hα

theorem commute_rankOneGroupTwo_szSubB :
    ∀ x ∈ rankOneGroupTwo K a, ∀ y ∈ szSubB K a, x * y = y * x := by
  intro x hx y hy
  have : CharP K 2 := ‹CharP K F4.prime›
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  exact (commute_of_mem_rootSpan (S := szSetA) (T := szSetB)
    (fun α hα β hβ s t => commute_pinnedX_szRoots h2 hα hβ s t)
    (rankOneGroupTwo_le_rootSpan hx) (szSubB_le_rootSpan hy)).eq

theorem rankOneGroupTwo_le_reeGamma'
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : rankOneGroupTwo K a ≤ F4.reeGamma K a := by
  rw [rankOneGroupTwo_eq_map hK]
  rintro _ ⟨x, -, rfl⟩
  rw [← map_reeFixed_eq_reeGamma]
  exact ⟨x, x.2, rfl⟩

theorem szSubB_le_reeGamma
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : szSubB K a ≤ F4.reeGamma K a := by
  rintro _ ⟨g, hg, rfl⟩
  exact mul_mem (mul_mem szNw_mem_reeGamma (rankOneGroupTwo_le_reeGamma' hK hg))
    (inv_mem szNw_mem_reeGamma)

@[expose] noncomputable def szSubBEquiv
    : rankOneGroupTwo K a ≃* szSubB K a :=
  Subgroup.equivMapOfInjective _ (MulAut.conj (szNw K)).toMonoidHom
    (MulAut.conj (szNw K)).injective

theorem rankOneGroupTwo_inf_szSubB
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupTwo K a ⊓ szSubB K a = ⊥ := by
  obtain ⟨hsimple, x, y, hxy⟩ := isSimpleGroup_rankOneGroupTwo ha hK
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hgA, hgB⟩ := hg
  have hz : (⟨g, hgA⟩ : rankOneGroupTwo K a) ∈ Subgroup.center (rankOneGroupTwo K a) := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (commute_rankOneGroupTwo_szSubB z.1 z.2 g hgB)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (rankOneGroupTwo K a)) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  · exfalso
    have hx : x ∈ Subgroup.center (rankOneGroupTwo K a) := h ▸ Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.1 hx y).symm

end Pair

end CFSG.RankThree.PartOne.SEITZ7
