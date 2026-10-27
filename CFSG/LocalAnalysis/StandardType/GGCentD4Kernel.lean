module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTable
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacShape
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacD
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private lemma d1a_notMem_d4Nodes {i : Fin Tag.E6.rank} :
    i ∉ d4Nodes Tag.E6 ↔ i.val = 0 ∨ i.val = 5 := by
  rw [d4Nodes, Set.mem_setOf_eq]
  constructor
  · intro h
    have h' : ¬(1 ≤ i.val ∧ i.val ≤ 4) := fun hc => h hc
    have hlt : i.val < 6 := i.isLt
    omega
  · rintro (h | h) ⟨h1, h2⟩ <;> omega

private def d1a_JList : List (Fin Tag.E6.rank → ℤ) :=
  e6RootList.filter (fun α => (α 0 == 0) && (α 5 == 0))

private def d1a_KList : List (Fin Tag.E6.rank → ℤ) :=
  e6RootList.filter (fun α => (pairVec (reps 4) α == 0))

private def d1a_applyRoot : List (Fin Tag.E6.rank) → (Fin Tag.E6.rank → ℤ) →
    (Fin Tag.E6.rank → ℤ)
  | [], α => α
  | i :: l, α => reflect Tag.E6 i (d1a_applyRoot l α)

private theorem d1a_mem_parabolic_iff (α : Fin Tag.E6.rank → ℤ) :
    α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) ↔ α ∈ d1a_JList := by
  rw [parabolicRoots, Set.mem_setOf_eq, d1a_JList, List.mem_filter]
  constructor
  · rintro ⟨hroot, hJ⟩
    refine ⟨(isRoot_iff_mem_e6RootList α).1 hroot, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hJ 0 (d1a_notMem_d4Nodes.mpr (Or.inl rfl)),
      hJ 5 (d1a_notMem_d4Nodes.mpr (Or.inr rfl))⟩
  · rintro ⟨hmem, hb⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    refine ⟨(isRoot_iff_mem_e6RootList α).2 hmem, fun i hi => ?_⟩
    rcases (d1a_notMem_d4Nodes.1 hi) with h0 | h5
    · have hi0 : i = (0 : Fin Tag.E6.rank) := Fin.ext h0
      rw [hi0]; exact hb.1
    · have hi5 : i = (5 : Fin Tag.E6.rank) := Fin.ext h5
      rw [hi5]; exact hb.2

private def d1a_base : Fin Tag.E6.rank → ℤ := Pi.single 3 1

private theorem d1a_base_mem : d1a_base ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
  rw [d1a_mem_parabolic_iff]
  decide +kernel

private def d1a_connBool : Bool :=
  d1a_JList.all fun a => (iform a d1a_base != 0) ||
    d1a_JList.any fun c => (iform a c != 0) && (iform c d1a_base != 0)

private theorem d1a_connBool_eq : d1a_connBool = true := by decide +kernel

private theorem d1a_connJ_ambient (a b : Fin Tag.E6.rank → ℤ)
    (ha : a ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hb : b ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    Relation.EqvGen (fun x y => x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) ∧
      y ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) ∧ iform x y ≠ 0) a b := by
  have key : ∀ a, a ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) →
      Relation.EqvGen (fun x y => x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) ∧
        y ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) ∧ iform x y ≠ 0) a d1a_base := by
    intro a ha
    have haJ : a ∈ d1a_JList := (d1a_mem_parabolic_iff a).1 ha
    have h := List.all_eq_true.mp d1a_connBool_eq a haJ
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, List.any_eq_true] at h
    rcases h with h1 | ⟨c, hcJ, h2, h3⟩
    · exact Relation.EqvGen.rel _ _ ⟨ha, d1a_base_mem, h1⟩
    · have hc : c ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
        (d1a_mem_parabolic_iff c).2 hcJ
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨ha, hc, h2⟩)
        (Relation.EqvGen.rel _ _ ⟨hc, d1a_base_mem, h3⟩)
  exact Relation.EqvGen.trans _ _ _ (key a ha) (Relation.EqvGen.symm _ _ (key b hb))

private def d1a_u : WeylGroup Tag.E6 :=
  (([4, 5, 2, 0] : List (Fin Tag.E6.rank)).map (simple Tag.E6)).prod

private theorem d1a_u_smul (α : Fin Tag.E6.rank → ℤ) :
    d1a_u • α = d1a_applyRoot [4, 5, 2, 0] α := by
  simp only [d1a_u, d1a_applyRoot, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_smul, one_smul, simple_smul]

private theorem d1a_kerRoots_reps4 :
    kerRoots (reps 4) =
      (fun α => d1a_u • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
  have hcomp : (d1a_JList.map (d1a_applyRoot [4, 5, 2, 0])).toFinset = d1a_KList.toFinset := by
    decide +kernel
  have hK : kerRoots (reps 4) = (↑d1a_KList.toFinset : Set (Fin Tag.E6.rank → ℤ)) := by
    ext α
    simp only [kerRoots, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, d1a_KList,
      List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨hroot, hp⟩
      exact ⟨(isRoot_iff_mem_e6RootList α).1 hroot, hp⟩
    · rintro ⟨hmem, hp⟩
      exact ⟨(isRoot_iff_mem_e6RootList α).2 hmem, hp⟩
  have hJ : parabolicRoots Tag.E6 (d4Nodes Tag.E6) =
      (↑d1a_JList.toFinset : Set (Fin Tag.E6.rank → ℤ)) := by
    ext α
    rw [Finset.mem_coe, List.mem_toFinset, d1a_mem_parabolic_iff]
  have himg : d1a_JList.toFinset.image (d1a_applyRoot [4, 5, 2, 0]) =
      (d1a_JList.map (d1a_applyRoot [4, 5, 2, 0])).toFinset := by
    ext x; simp
  rw [hK, hJ]
  rw [show (fun α => d1a_u • α) = (fun α => d1a_applyRoot [4, 5, 2, 0] α)
    from funext d1a_u_smul]
  rw [← Finset.coe_image, himg, hcomp]

private theorem d1a_compRank_parabolic :
    compRank (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) = 4 := by
  let C : Finset (Option (Fin Tag.E6.rank)) := {some 1, some 2, some 3, some 4}
  have hnone : none ∉ C := by decide
  have hCJ : ∀ j, some j ∈ C ↔ j ∈ d4Nodes Tag.E6 := by
    intro j; rw [d4Nodes, Set.mem_setOf_eq]; revert j; decide
  have hCcard : C.card = 4 := by decide
  have hroots : kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) =
      parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    ext γ
    rw [mem_rootsOf_iff kacE6 facts_E6 ⟨none, hnone⟩]
    constructor
    · rintro ⟨hγ, htest⟩
      refine ⟨hγ, fun i hi => ?_⟩
      rcases htest with h | ⟨hnone', -⟩
      · exact h i (fun hc => hi ((hCJ i).1 hc))
      · exact absurd hnone' hnone
    · rintro ⟨hγ, hJ⟩
      exact ⟨hγ, Or.inl fun j hj => hJ j (fun hj' => hj ((hCJ j).2 hj'))⟩
  calc compRank (parabolicRoots Tag.E6 (d4Nodes Tag.E6))
      = compRank (kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank)))) := by rw [hroots]
    _ = C.card := compRank_rootsOf kacE6 facts_E6 ⟨none, hnone⟩
    _ = 4 := hCcard

private theorem d1a_eqvGen_map {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : α} (h : Relation.EqvGen R x y) :
    Relation.EqvGen R' (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private theorem d1a_eqvGen_mem {S : Set (Fin Tag.E6.rank → ℤ)} {a b : Fin Tag.E6.rank → ℤ}
    (h : Relation.EqvGen (fun x y => x ∈ S ∧ y ∈ S ∧ iform x y ≠ 0) a b) :
    a ∈ S ↔ b ∈ S := by
  induction h with
  | rel x y h => exact ⟨fun _ => h.2.1, fun _ => h.1⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private theorem d1a_eqvGen_image
    {S : Set (Fin Tag.E6.rank → ℤ)} (v : WeylGroup Tag.E6)
    {a b : Fin Tag.E6.rank → ℤ}
    (h : Relation.EqvGen (fun x y => x ∈ S ∧ y ∈ S ∧ iform x y ≠ 0) a b) :
    Relation.EqvGen (fun x y => x ∈ (fun α => v • α) '' S ∧
      y ∈ (fun α => v • α) '' S ∧ iform x y ≠ 0) (v • a) (v • b) := by
  refine d1a_eqvGen_map (fun x => v • x) ?_ h
  intro x y hxy
  exact ⟨⟨x, hxy.1, rfl⟩, ⟨y, hxy.2.1, rfl⟩, by rw [iform_smul]; exact hxy.2.2⟩

private theorem d1a_eqvGen_subtype {S : Set (Fin Tag.E6.rank → ℤ)}
    {a b : Fin Tag.E6.rank → ℤ}
    (h : Relation.EqvGen (fun x y => x ∈ S ∧ y ∈ S ∧ iform x y ≠ 0) a b) :
    ∀ (ha : a ∈ S) (hb : b ∈ S),
      Relation.EqvGen (fun x y : ↥S => iform x.1 y.1 ≠ 0) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | rel x y hxy => intro _ _; exact Relation.EqvGen.rel _ _ hxy.2.2
  | refl x =>
      intro ha hb
      have he : (⟨x, ha⟩ : ↥S) = ⟨x, hb⟩ := Subtype.ext rfl
      rw [he]; exact Relation.EqvGen.refl _
  | symm x y _ ih => intro ha hb; exact Relation.EqvGen.symm _ _ (ih hb ha)
  | trans x y z hab _ ih1 ih2 =>
      intro ha hb
      have hy : y ∈ S := (d1a_eqvGen_mem hab).1 ha
      exact Relation.EqvGen.trans _ _ _ (ih1 ha hy) (ih2 hy hb)

private theorem d1a_subsingleton_of_smul_image
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M)
    (v : WeylGroup Tag.E6) {S : Set (Fin Tag.E6.rank → ℤ)}
    (hker : kernelRoots χ = (fun α => v • α) '' S)
    (hconn : ∀ a b : Fin Tag.E6.rank → ℤ, a ∈ S → b ∈ S →
      Relation.EqvGen (fun x y => x ∈ S ∧ y ∈ S ∧ iform x y ≠ 0) a b) :
    Subsingleton (KernelComponent χ) := by
  refine ⟨fun i j => ?_⟩
  induction i using Quotient.inductionOn with
  | h a =>
  induction j using Quotient.inductionOn with
  | h b =>
  obtain ⟨a0, ha0, haeq⟩ := (Set.mem_image _ _ _).1 (hker.le a.2)
  obtain ⟨b0, hb0, hbeq⟩ := (Set.mem_image _ _ _).1 (hker.le b.2)
  have hmem_a : v • a0 ∈ kernelRoots χ := hker.ge ⟨a0, ha0, rfl⟩
  have hmem_b : v • b0 ∈ kernelRoots χ := hker.ge ⟨b0, hb0, rfl⟩
  have hA : (⟨v • a0, hmem_a⟩ : kernelRoots χ) = a := Subtype.ext haeq
  have hB : (⟨v • b0, hmem_b⟩ : kernelRoots χ) = b := Subtype.ext hbeq
  rw [← hA, ← hB]
  apply Quotient.sound
  have hab := d1a_eqvGen_image v (hconn a0 b0 ha0 hb0)
  rw [← hker] at hab
  have hsub := d1a_eqvGen_subtype (S := kernelRoots χ) hab hmem_a hmem_b
  exact d1a_eqvGen_map (fun x : kernelRoots χ => x)
    (fun x y hxy => by rwa [dotProduct_mulVec_eq_iform]) hsub

private theorem d1a_applyWord_eq_prod_smul (l : List (Fin Tag.E6.rank)) (x : X3) :
    applyWord l x = (l.map (simple Tag.E6)).prod • x := by
  induction l with
  | nil => simp [applyWord]
  | cons i l ih =>
    show dualRefl i (applyWord l x) = _
    rw [List.map_cons, List.prod_cons, mul_smul, ← ih, ← simple_smul_X3]

private theorem d1a_kerRoots_smul (w : WeylGroup Tag.E6) (x : X3) :
    kerRoots (w • x) = (fun α : Fin Tag.E6.rank → ℤ => w • α) '' kerRoots x := by
  ext α
  constructor
  · intro hα
    refine ⟨w⁻¹ • α, ⟨IsRoot.smul hα.1 w⁻¹, ?_⟩,
      by change w • (w⁻¹ • α) = α; exact smul_inv_smul w α⟩
    have h := hα.2
    rw [pairVec_smul] at h
    exact h
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨IsRoot.smul hβ.1 w, by rw [pairVec_smul_self, hβ.2]⟩

theorem ntpD4_kernel
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (ha3 : ∀ i, a i ^ 3 = 1)
    (hker : (rootCharKernel a).ncard = 24) :
    ∃ (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6),
      (∀ j : KernelComponent (rootCharHom a), j = i) ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6) ∧
      compRank (componentRoots (rootCharHom a) i) = 4 := by
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1] at hker
    have hset : rootCharKernel (1 : Fin Tag.E6.rank → Lˣ) =
        (↑(rootFinset Tag.E6) : Set (Fin Tag.E6.rank → ℤ)) := by
      ext α
      simp only [rootCharKernel, Set.mem_setOf_eq, Finset.mem_coe, mem_rootFinset]
      exact ⟨fun h => h.1, fun h => ⟨h, by simp [rootChar]⟩⟩
    have hcard : (rootCharKernel (1 : Fin Tag.E6.rank → Lˣ)).ncard = 72 := by
      rw [hset, Set.ncard_coe_finset, card_rootFinset]
      rfl
    omega
  obtain ⟨x, hx0, hxchar⟩ := exists_vec_of_cube_roots a ha3 ha1
  have hkerx : rootCharKernel a = kerRoots x := by
    ext α
    rw [rootCharKernel, kerRoots]
    exact ⟨fun h => ⟨h.1, (hxchar α).1 h.2⟩, fun h => ⟨h.1, (hxchar α).2 h.2⟩⟩
  obtain ⟨k, l, hl⟩ := exists_word_to_rep x hx0
  set w : WeylGroup Tag.E6 := (l.map (simple Tag.E6)).prod with hwdef
  have hw : w • x = reps k := (d1a_applyWord_eq_prod_smul l x).symm.trans hl
  have hk4 : k = 4 := by
    have h1 : (kerRoots (reps k)).ncard = 24 := by
      rw [← hw, d1a_kerRoots_smul,
        Set.ncard_image_of_injective (f := fun α : Fin Tag.E6.rank → ℤ => w • α) _
          (MulAction.injective w), ← hkerx]
      exact hker
    have hrep : repKerCard k = 24 := by
      rcases lt_or_ge k.val 3 with hk | hk
      · rw [← ncard_kerRoots_rep_lt3 k hk]; exact h1
      · rw [← ncard_kerRoots_rep_ge3 k hk]; exact h1
    have h : ∀ k : Fin 7, repKerCard k = 24 → k = 4 := by decide
    exact h k hrep
  have hw4 : w • x = reps 4 := by rw [hw, hk4]
  have hker4 : kerRoots (reps 4) = (fun α => w • α) '' kerRoots x := by
    rw [← hw4]; exact d1a_kerRoots_smul w x
  have hkerx4 : kerRoots x = (fun α => w⁻¹ • α) '' kerRoots (reps 4) := by
    rw [hker4, Set.image_image]
    rw [show (fun α : Fin Tag.E6.rank → ℤ => w⁻¹ • (w • α)) = fun α => α from
      funext fun α => inv_smul_smul w α]
    exact (Set.image_id _).symm
  have hv : kerRoots x =
      (fun α => (w⁻¹ * d1a_u) • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    rw [hkerx4, d1a_kerRoots_reps4, Set.image_image]
    apply Set.image_congr
    intro α _
    rw [mul_smul]
  have hkerχ : kernelRoots (rootCharHom a) = kerRoots x := hkerx
  have hkerχ' : kernelRoots (rootCharHom a) =
      (fun α => (w⁻¹ * d1a_u) • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
    hkerχ.trans hv
  have hsub : Subsingleton (KernelComponent (rootCharHom a)) :=
    d1a_subsingleton_of_smul_image (rootCharHom a) (w⁻¹ * d1a_u) hkerχ' d1a_connJ_ambient
  have hbase : (w⁻¹ * d1a_u) • d1a_base ∈ kernelRoots (rootCharHom a) := by
    rw [hkerχ']; exact ⟨d1a_base, d1a_base_mem, rfl⟩
  let i : KernelComponent (rootCharHom a) := ⟦⟨(w⁻¹ * d1a_u) • d1a_base, hbase⟩⟧
  have hcomp : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) := by
    ext α
    constructor
    · rintro ⟨hα, -⟩; exact hα
    · intro hα; exact ⟨hα, Subsingleton.elim _ _⟩
  refine ⟨i, w⁻¹ * d1a_u, fun j => Subsingleton.elim j i, ?_, ?_⟩
  · rw [hcomp, hkerχ']
  · rw [hcomp, hkerχ', compRank_image, d1a_compRank_parabolic]

end CFSG.StandardType.NTPlane

end
