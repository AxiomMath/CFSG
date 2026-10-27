module

public import CFSG.Monster.B.Geometry.ProjectivePlane
public import CFSG.Monster.B.Geometry.ModelResidue

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

section Plane

variable {k : Type*} [Field k]

@[expose] def PlaneFlag.SamePt (x y : PlaneFlag k) : Prop := x.pt = y.pt

@[expose] def PlaneFlag.SameLine (x y : PlaneFlag k) : Prop := x.line = y.line

theorem pathLE_of_not_isOpposite {x y : PlaneFlag k} (h : ¬x.IsOpposite y) :
    PathLE PlaneFlag.SamePt PlaneFlag.SameLine 2 x y := by
  simp only [PlaneFlag.IsOpposite, not_and_or, not_not] at h
  rcases h with h | h
  · let z : PlaneFlag k := ⟨x.pt, y.line, x.finrank_pt, y.finrank_line, h⟩
    exact .step (b := z) (Or.inl (show x.pt = z.pt from rfl))
      (.step (b := y) (Or.inr (show z.line = y.line from rfl)) (.refl 0 y))
  · let z : PlaneFlag k := ⟨y.pt, x.line, y.finrank_pt, x.finrank_line, h⟩
    exact .step (b := z) (Or.inr (show x.line = z.line from rfl))
      (.step (b := y) (Or.inl (show z.pt = y.pt from rfl)) (.refl 0 y))

end Plane

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W}

variable (cs δ) in
@[expose] def IsPlaneFlagResidue (k : Type*) [Field k] (i j : ι) (x : C) : Prop :=
  ∃ f : C → PlaneFlag k,
    IsModelResidue cs δ PlaneFlag.SamePt PlaneFlag.SameLine i j x f ∨
      IsModelResidue cs δ PlaneFlag.SameLine PlaneFlag.SamePt i j x f

section Residue

variable {k : Type*} [Field k]

theorem IsPlaneFlagResidue.swap {i j : ι} {x : C} (h : IsPlaneFlagResidue cs δ k i j x) :
    IsPlaneFlagResidue cs δ k j i x := by
  obtain ⟨f, hf | hf⟩ := h
  · exact ⟨f, Or.inr hf.swap⟩
  · exact ⟨f, Or.inl hf.swap⟩

theorem IsPlaneFlagResidue.exists_model {i j : ι} {x : C} (h : IsPlaneFlagResidue cs δ k i j x) :
    ∃ f : C → PlaneFlag k, IsModelResidue cs δ PlaneFlag.SamePt PlaneFlag.SameLine i j x f ∨
      IsModelResidue cs δ PlaneFlag.SamePt PlaneFlag.SameLine j i x f := by
  obtain ⟨f, hf | hf⟩ := h
  · exact ⟨f, Or.inl hf⟩
  · exact ⟨f, Or.inr hf.swap⟩

variable (hδ : IsWeylDistanceBuilding cs δ)
include hδ

omit hδ in
theorem length_longest_pair {i j : ι} (hij : i ≠ j) (hM : M i j ≠ 0) :
    cs.length (longest cs {i, j}) = M i j := by
  have := finite_parabolic_pair (cs := cs) hM
  obtain ⟨h1, -, h3⟩ := isLongest_braidWord (cs := cs) hij hM
  rw [← h1.eq_longest, h3]

theorem isOpposite_of_isModelResidue {i j : ι} (hij : i ≠ j) (hM : M i j = 3) {x : C}
    {f : C → PlaneFlag k} (hf : IsModelResidue cs δ PlaneFlag.SamePt PlaneFlag.SameLine i j x f)
    {a b : C} (ha : a ∈ residue cs δ {i, j} x) (hb : b ∈ residue cs δ {i, j} x)
    (hab : δ a b = longest cs {i, j}) : (f a).IsOpposite (f b) := by
  by_contra h
  have h1 := hf.length_le hδ ha hb (pathLE_of_not_isOpposite h)
  rw [hab, length_longest_pair hij (by omega), hM] at h1
  omega

theorem fix_of_isModelResidue {i j : ι} (hij : i ≠ j) (hM : M i j = 3) {a : C}
    {f : C → PlaneFlag k} (hf : IsModelResidue cs δ PlaneFlag.SamePt PlaneFlag.SameLine i j a f)
    {b : C} (hb : b ∈ residue cs δ {i, j} a) (hab : δ a b = longest cs {i, j}) {g : C → C}
    (hg : IsTypeIso cs δ δ (residue cs δ {i, j} a) (residue cs δ {i, j} a) g) (hgb : g b = b)
    (hfix : ∀ y ∈ panel cs δ i a ∪ panel cs δ j a, g y = y) :
    ∀ y ∈ residue cs δ {i, j} a, g y = y := by
  have ha := self_mem_residue (cs := cs) (δ := δ) {i, j} a
  obtain ⟨G, hG, hG1, hG2⟩ := hf.exists_perm (fun _ => rfl) (fun _ => rfl) hg
  have hGmem : G ∈ planeTypeAut k := fun u v => ⟨hG1 u v, hG2 u v⟩
  have hGstab : G ∈ planePairStab k (f a) (f b) := by
    refine ⟨hGmem, ?_, ?_⟩
    · rw [hG a ha, hfix a (Or.inl (self_mem_residue _ a))]
    · rw [hG b hb, hgb]
  have hga : g a = a := hfix a (Or.inl (self_mem_residue _ a))
  have hpanel : ∀ u ∈ (f a).pointPanel ∪ (f a).linePanel, G u = u := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := hf.1.surjOn (Set.mem_univ u)
    rw [hG y hy]
    by_cases e : y = a
    · rw [e, hga]
    · congr 1
      refine hfix y ?_
      rcases hu with hu | hu
      · left
        exact (mem_panel_iff hδ).mpr (Or.inr ((hf.2 a ha y hy).1.mpr ⟨Ne.symm e, hu.symm⟩))
      · right
        exact (mem_panel_iff hδ).mpr (Or.inr ((hf.2 a ha y hy).2.mpr ⟨Ne.symm e, hu.symm⟩))
  have h1 := eq_one_of_mem_planePairStab_of_forall_panel
    (isOpposite_of_isModelResidue hδ hij hM hf ha hb hab) hGstab hpanel
  intro y hy
  have := hG y hy
  rw [h1] at this
  exact (hf.1.injOn hy (hg.1.mapsTo hy) this).symm

theorem IsPlaneFlagResidue.fix {i j : ι} (hij : i ≠ j) (hM : M i j = 3) {a : C}
    (h : IsPlaneFlagResidue cs δ k i j a) {b : C} (hb : b ∈ residue cs δ {i, j} a)
    (hab : δ a b = longest cs {i, j}) {g : C → C}
    (hg : IsTypeIso cs δ δ (residue cs δ {i, j} a) (residue cs δ {i, j} a) g) (hgb : g b = b)
    (hfix : ∀ y ∈ panel cs δ i a ∪ panel cs δ j a, g y = y) :
    ∀ y ∈ residue cs δ {i, j} a, g y = y := by
  obtain ⟨f, hf | hf⟩ := h.exists_model
  · exact fix_of_isModelResidue hδ hij hM hf hb hab hg hgb hfix
  · rw [Set.pair_comm] at hb hab hg ⊢
    exact fix_of_isModelResidue hδ hij.symm (by rw [M.symmetric]; exact hM) hf hb hab hg hgb
      fun y hy => hfix y hy.symm

theorem IsPlaneFlagResidue.fix_of_card_two (hk : Nat.card k = 2) {i j : ι} (hij : i ≠ j)
    (hM : M i j = 3) {a : C} (h : IsPlaneFlagResidue cs δ k i j a) {b : C}
    (hb : b ∈ residue cs δ {i, j} a) (hab : δ a b = longest cs {i, j}) {g : C → C}
    (hg : IsTypeIso cs δ δ (residue cs δ {i, j} a) (residue cs δ {i, j} a) g) (hga : g a = a)
    (hgb : g b = b) : ∀ y ∈ residue cs δ {i, j} a, g y = y := by
  have ha := self_mem_residue (cs := cs) (δ := δ) {i, j} a
  obtain ⟨f, hf⟩ := h.exists_model
  have key : ∀ {i' j' : ι}, i' ≠ j' → M i' j' = 3 → residue cs δ {i', j'} a =
      residue cs δ {i, j} a → longest cs {i', j'} = longest cs {i, j} →
      IsModelResidue cs δ PlaneFlag.SamePt PlaneFlag.SameLine i' j' a f →
      ∀ y ∈ residue cs δ {i, j} a, g y = y := by
    intro i' j' hij' hM' hR hL hf'
    rw [← hR] at hb hg ⊢
    rw [← hL] at hab
    have ha' := self_mem_residue (cs := cs) (δ := δ) {i', j'} a
    obtain ⟨G, hG, hG1, hG2⟩ := hf'.exists_perm (fun _ => rfl) (fun _ => rfl) hg
    have hGstab : G ∈ planePairStab k (f a) (f b) := by
      refine ⟨fun u v => ⟨hG1 u v, hG2 u v⟩, ?_, ?_⟩
      · rw [hG a ha', hga]
      · rw [hG b hb, hgb]
    rw [planePairStab_eq_bot_of_card_two hk
      (isOpposite_of_isModelResidue hδ hij' hM' hf' ha' hb hab), Subgroup.mem_bot] at hGstab
    intro y hy
    have := hG y hy
    rw [hGstab] at this
    exact (hf'.1.injOn hy (hg.1.mapsTo hy) this).symm
  rcases hf with hf | hf
  · exact key hij hM rfl rfl hf
  · exact key hij.symm (by rw [M.symmetric]; exact hM) (by rw [Set.pair_comm])
      (by rw [Set.pair_comm]) hf

theorem isOpposite_of_isModelResidue' {i j : ι} (hij : i ≠ j) (hM : M i j = 3) {x : C}
    {f : C → PlaneFlag k} (hf : IsModelResidue cs δ PlaneFlag.SameLine PlaneFlag.SamePt i j x f)
    {a b : C} (ha : a ∈ residue cs δ {i, j} x) (hb : b ∈ residue cs δ {i, j} x)
    (hab : δ a b = longest cs {i, j}) : (f a).IsOpposite (f b) := by
  by_contra h
  have h1 := hf.length_le hδ ha hb (pathLE_of_not_isOpposite h).swap
  rw [hab, length_longest_pair hij (by omega), hM] at h1
  omega

theorem IsPlaneFlagResidue.nat_card_residueStab {i j : ι} (hij : i ≠ j) (hM : M i j = 3)
    {x : C} (h : IsPlaneFlagResidue cs δ k i j x) (a b : residue cs δ {i, j} x)
    (hab : δ a b = longest cs {i, j}) :
    Nat.card (residueStab cs δ (residue cs δ {i, j} x) a b) = Nat.card (planeOppStab k) := by
  obtain ⟨f, hf | hf⟩ := h
  · rw [hf.nat_card_residueStab hδ (fun _ => rfl) (fun _ => rfl) a b,
      ← nat_card_planePairStab_of_isOpposite
        (isOpposite_of_isModelResidue hδ hij hM hf a.2 b.2 hab)]
    exact Nat.card_congr
      { toFun := fun G => ⟨G.1, fun u v => ⟨G.2.1 u v, G.2.2.1 u v⟩, G.2.2.2⟩
        invFun := fun G => ⟨G.1, fun u v => (G.2.1 u v).1, fun u v => (G.2.1 u v).2, G.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · rw [hf.nat_card_residueStab hδ (fun _ => rfl) (fun _ => rfl) a b,
      ← nat_card_planePairStab_of_isOpposite
        (isOpposite_of_isModelResidue' hδ hij hM hf a.2 b.2 hab)]
    exact Nat.card_congr
      { toFun := fun G => ⟨G.1, fun u v => ⟨G.2.2.1 u v, G.2.1 u v⟩, G.2.2.2⟩
        invFun := fun G => ⟨G.1, fun u v => (G.2.1 u v).2, fun u v => (G.2.1 u v).1, G.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

end Residue

end CFSG.Monster.B.Geometry
