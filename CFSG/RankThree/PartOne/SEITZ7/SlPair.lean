module

public import CFSG.RankThree.PartOne.SEITZ7.SzPair

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

@[expose] def slRootsA : List (Fin Tag.F4.rank → ℤ) :=
  ReeTag.largeReeBlockTable 0 ++ ReeTag.largeReeBlockTable 2

@[expose] def slRootsB : List (Fin Tag.F4.rank → ℤ) :=
  ReeTag.largeReeBlockTable 12 ++ ReeTag.largeReeBlockTable 15

@[expose] def slRcCheck : Bool :=
  (List.range Tag.F4.rootCertificate.roots.length).all fun m =>
    (List.range Tag.F4.rootCertificate.roots.length).all fun n =>
      !(decide (Tag.F4.rootCertificate.root m ∈ slRootsA)) ||
        !(decide (Tag.F4.rootCertificate.root n ∈ slRootsB)) ||
          (Nat.blt (pairLab Tag.F4 m n) (repsOf Tag.F4).length &&
            evenRow Tag.F4 (pairLab Tag.F4 m n))

theorem slRcCheck_true : slRcCheck = true := by decide +kernel

theorem slRootsA_pos : ∀ γ ∈ slRootsA, ∃ m < Tag.F4.rootCertificate.roots.length,
    Tag.F4.rootCertificate.root m = γ := by decide +kernel

theorem slRootsB_pos : ∀ γ ∈ slRootsB, ∃ m < Tag.F4.rootCertificate.roots.length,
    Tag.F4.rootCertificate.root m = γ := by decide +kernel

theorem slRootsA_mem_single :
    (Pi.single (⟨0, by decide⟩ : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ slRootsA ∧
      (Pi.single (⟨3, by decide⟩ : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ slRootsA := by
  decide +kernel

theorem slRootsA_mem_neg_single :
    (-Pi.single (⟨0, by decide⟩ : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ slRootsA ∧
      (-Pi.single (⟨3, by decide⟩ : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ∈ slRootsA := by
  decide +kernel

theorem commute_pinnedX_slRoots
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {γ δ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ slRootsA) (hδ : δ ∈ slRootsB) (x y : R) :
    Commute (pinnedX Tag.F4 R γ x) (pinnedX Tag.F4 R δ y) := by
  obtain ⟨m, hm, rfl⟩ := slRootsA_pos γ hγ
  obtain ⟨n, hn, rfl⟩ := slRootsB_pos δ hδ
  have h := slRcCheck_true
  simp only [slRcCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, Nat.blt_eq] at h
  rcases h m hm n hn with (h | h) | h
  · exact absurd hγ h
  · exact absurd hδ h
  · exact commute_pinnedX_of_label h2 hm hn h.1 h.2 x y

@[expose] def slSetA : Set (Fin Tag.F4.rank → ℤ) := {γ | γ ∈ slRootsA}

@[expose] def slSetB : Set (Fin Tag.F4.rank → ℤ) := {γ | γ ∈ slRootsB}

@[expose] def slW : WeylGroup F4.tag := F4.fixedRelElt ⟨6, by decide⟩

@[expose] def slWord : List (Fin Tag.F4.rank) :=
  (F4.fixedRelWord ⟨6, by decide⟩).flatMap F4.fixedOrbitWord

theorem slW_foldr : ∀ γ ∈ slRootsA, szFold slWord γ ∈ slRootsB := by
  decide +kernel

theorem isRoot_of_mem_slRootsA
    {γ : Fin Tag.F4.rank → ℤ} (h : γ ∈ slRootsA) : IsRoot Tag.F4 γ := by
  obtain ⟨m, hm, rfl⟩ := slRootsA_pos γ h
  exact RootWalk.isRoot_rootCertificate_root hm

theorem slW_smul
    {γ : Fin F4.tag.rank → ℤ} (hγ : γ ∈ slRootsA) : slW • γ ∈ slRootsB := by
  rw [slW, ReeTag.fixedRelElt, ReeTag.list_prod_map_fixedOrbitElement,
    CFSG.LieType.Ree.wordProd_smul]
  exact slW_foldr γ hγ

section Pair

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem rankOneGroupOne_le_rootSpan
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : rankOneGroupOne K a ≤ rootSpan F4.tag K slSetA := by
  rw [rankOneGroupOne_eq_range hK, largeReeA1Hom_range hK, largeReeA1M]
  refine sup_le (fun g hg => rootSpan_mono' ?_ (Subgroup.mem_inf.1 hg).1)
    (fun g hg => rootSpan_mono' ?_ (Subgroup.mem_inf.1 hg).1)
  · intro α hα
    rw [F4_fixedOrbitRoots_zero] at hα
    rcases hα with rfl | rfl
    · exact slRootsA_mem_single.1
    · exact slRootsA_mem_single.2
  · rintro _ ⟨α, hα, rfl⟩
    rw [F4_fixedOrbitRoots_zero] at hα
    rcases hα with rfl | rfl
    · exact slRootsA_mem_neg_single.1
    · exact slRootsA_mem_neg_single.2

@[expose] noncomputable def slNw (K : Type) [Field K] :
    ModGL F4.tag K :=
  canonicalRep (coxeterSystem F4.tag) K slW

@[expose] noncomputable def slSubB (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    : Subgroup (ModGL F4.tag K) :=
  (rankOneGroupOne K a).map (MulAut.conj (slNw K)).toMonoidHom

theorem slNw_mem_reeGamma
    : slNw K ∈ F4.reeGamma K a :=
  (Subgroup.mem_inf.1 (canonicalRep_mem_reeFixedMonomial F4 K a (fixedRelElt_mem _))).2

theorem slSubB_le_rootSpan
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : slSubB K a ≤ rootSpan F4.tag K slSetB := by
  rintro _ ⟨g, hg, rfl⟩
  have h1 : g ∈ rootSpan F4.tag K slSetA := rankOneGroupOne_le_rootSpan hK hg
  have hS : ∀ α ∈ slSetA, IsRoot F4.tag α := fun α hα => isRoot_of_mem_slRootsA hα
  have h2 := canonicalRep_conj_mem_rootSpan (w := slW) hS h1
  refine rootSpan_mono' ?_ h2
  rintro _ ⟨α, hα, rfl⟩
  exact slW_smul hα

theorem commute_rankOneGroupOne_slSubB
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ x ∈ rankOneGroupOne K a, ∀ y ∈ slSubB K a, x * y = y * x := by
  intro x hx y hy
  have : CharP K 2 := ‹CharP K F4.prime›
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  exact (commute_of_mem_rootSpan (S := slSetA) (T := slSetB)
    (fun α hα β hβ s t => commute_pinnedX_slRoots h2 hα hβ s t)
    (rankOneGroupOne_le_rootSpan hK hx) (slSubB_le_rootSpan hK hy)).eq

theorem rankOneGroupOne_le_reeGamma'
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : rankOneGroupOne K a ≤ F4.reeGamma K a := by
  rw [rankOneGroupOne_eq_range hK, largeReeA1Hom_range hK, largeReeA1M]
  exact sup_le (fun g hg => (Subgroup.mem_inf.1 hg).2) (fun g hg => (Subgroup.mem_inf.1 hg).2)

theorem slSubB_le_reeGamma
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : slSubB K a ≤ F4.reeGamma K a := by
  rintro _ ⟨g, hg, rfl⟩
  exact mul_mem (mul_mem slNw_mem_reeGamma (rankOneGroupOne_le_reeGamma' hK hg))
    (inv_mem slNw_mem_reeGamma)

@[expose] noncomputable def slSubBEquiv
    : rankOneGroupOne K a ≃* slSubB K a :=
  Subgroup.equivMapOfInjective _ (MulAut.conj (slNw K)).toMonoidHom
    (MulAut.conj (slNw K)).injective

theorem rankOneGroupOne_inf_slSubB
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ⊓ slSubB K a = ⊥ := by
  obtain ⟨hsimple, x, y, hxy⟩ := isSimpleGroup_rankOneGroupOne ha hK
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hgA, hgB⟩ := hg
  have hz : (⟨g, hgA⟩ : rankOneGroupOne K a) ∈ Subgroup.center (rankOneGroupOne K a) := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (commute_rankOneGroupOne_slSubB hK z.1 z.2 g hgB)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (rankOneGroupOne K a))
    with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  · exfalso
    have hx : x ∈ Subgroup.center (rankOneGroupOne K a) := h ▸ Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.1 hx y).symm

end Pair

end CFSG.RankThree.PartOne.SEITZ7
