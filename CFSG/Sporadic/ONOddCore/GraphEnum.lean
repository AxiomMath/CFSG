module

public import CFSG.Sporadic.ONOddCore.GraphDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.Sporadic.Schreier.ONPermArr

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.ONSchreier
open CFSG.ONSchreier.Native

section Tree

variable {G : Type*} [Group G] {m : ℕ} {gens : Array Tab} {root : Tab} {E : Enum}
  {Rel : Tab → G → Prop} {a : ℕ → G}

theorem rel_tree_sound (h : treeOK (leftStep m gens) gens.size root E = true)
    (hf : ∀ j < gens.size, ∀ t g, Rel t g → Rel (leftStep m gens j t) (a j * g))
    (hroot : Rel root 1) :
    ∀ i < E.tabs.size, ∃ g ∈ Subgroup.closure (a '' {j | j < gens.size}), Rel E.tabs[i]! g := by
  obtain ⟨-, h0, -, -, htree⟩ := treeOK_spec h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨1, Subgroup.one_mem _, h0 ▸ hroot⟩
    · obtain ⟨hpar, hlab, he⟩ := htree i hi hi0
      obtain ⟨g, hg, hrep⟩ := ih _ hpar (hpar.trans hi)
      exact ⟨a _ * g, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hlab, rfl⟩) hg,
        he ▸ hf _ hlab _ _ hrep⟩

theorem rel_tree_complete [Finite G] (h : treeOK (leftStep m gens) gens.size root E = true)
    (hf : ∀ j < gens.size, ∀ t g, Rel t g → Rel (leftStep m gens j t) (a j * g))
    (hroot : Rel root 1) :
    ∀ g ∈ Subgroup.closure (a '' {j | j < gens.size}), ∃ t ∈ E.tabs.toList, Rel t g := by
  obtain ⟨hpos, h0, -, hclosed, -⟩ := treeOK_spec h
  intro g hg
  let F : Set G := {g | ∃ t ∈ E.tabs.toList, Rel t g}
  have hAF : ∀ x ∈ a '' {j | j < gens.size}, ∀ y ∈ F, x • y ∈ F := by
    rintro _ ⟨j, hj, rfl⟩ y ⟨t, ht, hrep⟩
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    exact ⟨_, hclosed i hi j hj, hf j hj _ _ hrep⟩
  have h1 : (1 : G) ∈ F := ⟨_, getElem!_mem hpos, h0 ▸ hroot⟩
  have := CFSG.Perm.smul_mem_of_finite_of_mem_closure (Set.toFinite F) hAF hg h1
  rwa [smul_eq_mul, mul_one] at this

theorem rel_card [Finite G] (h : treeOK (leftStep m gens) gens.size root E = true)
    (hf : ∀ j < gens.size, ∀ t g, Rel t g → Rel (leftStep m gens j t) (a j * g))
    (hroot : Rel root 1) (hinj : ∀ t g g', Rel t g → Rel t g' → g = g')
    (hfun : ∀ t t' g, Rel t g → Rel t' g → t = t') :
    Nat.card (Subgroup.closure (a '' {j | j < gens.size})) = E.tabs.size := by
  classical
  obtain ⟨-, -, hnodup, -, -⟩ := treeOK_spec h
  set K := Subgroup.closure (a '' {j | j < gens.size})
  have key : ∀ t : {t // t ∈ E.tabs.toList}, ∃ g : K, Rel t.1 (g : G) := fun t => by
    obtain ⟨i, hi, hti⟩ := exists_getElem!_of_mem t.2
    obtain ⟨g, hg, hrep⟩ := rel_tree_sound h hf hroot i hi
    exact ⟨⟨g, hg⟩, hti ▸ hrep⟩
  let F : {t // t ∈ E.tabs.toList} → K := fun t => (key t).choose
  have hF : ∀ t, Rel t.1 (F t : G) := fun t => (key t).choose_spec
  have hbij : Function.Bijective F := by
    constructor
    · intro t t' htt
      apply Subtype.ext
      have h' := hF t'
      rw [← htt] at h'
      exact hfun _ _ _ (hF t) h'
    · intro g
      obtain ⟨t, ht, hr⟩ := rel_tree_complete h hf hroot g g.2
      exact ⟨⟨t, ht⟩, Subtype.ext (hinj _ _ _ (hF ⟨t, ht⟩) hr)⟩
  rw [← Nat.card_eq_of_bijective F hbij]
  have e : {t // t ∈ E.tabs.toList} ≃ E.tabs.toList.toFinset :=
    Equiv.subtypeEquivRight fun t => List.mem_toFinset.symm
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnodup,
    Array.length_toList]

end Tree

section Graph

variable {A B : Type*} [Group A] [Group B]

theorem exists_hom_of_graph [Finite A] [Finite B] (S : Set (A × B))
    (hcard : Nat.card (Subgroup.closure S) ≤ Nat.card (Subgroup.closure (Prod.fst '' S))) :
    ∃ φ : Subgroup.closure (Prod.fst '' S) →* B,
      ∀ s (hs : s ∈ S), φ ⟨s.1, Subgroup.subset_closure ⟨s, hs, rfl⟩⟩ = s.2 := by
  set H := Subgroup.closure S
  set K := Subgroup.closure (Prod.fst '' S)
  have hmap : H.map (MonoidHom.fst A B) = K := by
    rw [MonoidHom.map_closure]
    rfl
  let p : H →* K := ((MonoidHom.fst A B).comp H.subtype).codRestrict K fun x => by
    rw [← hmap]
    exact ⟨x, x.2, rfl⟩
  have hsurj : Function.Surjective p := by
    rintro ⟨k, hk⟩
    rw [← hmap] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    exact ⟨⟨x, hx⟩, rfl⟩
  have hbij : Function.Bijective p := hsurj.bijective_of_nat_card_le hcard
  let e : H ≃* K := MulEquiv.ofBijective p hbij
  refine ⟨(MonoidHom.snd A B).comp (H.subtype.comp e.symm.toMonoidHom), fun s hs => ?_⟩
  have hp : e ⟨s, Subgroup.subset_closure hs⟩ = ⟨s.1, Subgroup.subset_closure ⟨s, hs, rfl⟩⟩ :=
    rfl
  show ((e.symm ⟨s.1, Subgroup.subset_closure ⟨s, hs, rfl⟩⟩ : H) : A × B).2 = s.2
  rw [← hp, MulEquiv.symm_apply_apply]

end Graph

section Pairs

variable {n : ℕ}

theorem dbl_get_left {a b : Array ℕ} (ha : a.size = n) {i : ℕ} (hi : i < n) :
    (dbl n a b)[i]! = a[i]! := by
  rw [dbl, getElem!_pos _ i (by simp; omega), getElem!_pos a i (by omega),
    Array.getElem_append_left (by omega)]

theorem dbl_get_right {a b : Array ℕ} (ha : a.size = n) (hb : b.size = n) {i : ℕ} (hi : i < n) :
    (dbl n a b)[n + i]! = n + b[i]! := by
  rw [dbl, getElem!_pos _ (n + i) (by simp; omega), getElem!_pos b i (by omega),
    Array.getElem_append_right (by omega)]
  simp [ha, Nat.add_comm]

@[expose] def pairRel (n : ℕ) (base : List (Fin n)) (t : Tab)
    (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) : Prop :=
  t.size = 2 * base.length ∧ ∀ k (hk : k < base.length),
    t[k]! = (g.1 (base[k]) : ℕ) ∧ t[base.length + k]! = n + (g.2 (base[k]) : ℕ)

theorem pairRel_root (base : List (Fin n)) :
    pairRel n base (dblBase n (base.map Fin.val).toArray) 1 := by
  refine ⟨by simp [dblBase]; omega, fun k hk => ⟨?_, ?_⟩⟩
  · rw [dblBase, getElem!_pos _ k (by simp; omega), Array.getElem_append_left (by simpa using hk)]
    simp
  · rw [dblBase, getElem!_pos _ (base.length + k) (by simp; omega),
      Array.getElem_append_right (by simp)]
    simp [Nat.add_comm]

theorem pairRel_step {base : List (Fin n)} {a b : Array ℕ} {g₁ g₂ : Equiv.Perm (Fin n)}
    (ha : PRep n a g₁) (hb : PRep n b g₂) (has : a.size = n) (hbs : b.size = n) {t : Tab}
    {g : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)} (ht : pairRel n base t g) :
    pairRel n base (comp (2 * base.length) (dbl n a b) t) ((g₁, g₂) * g) := by
  obtain ⟨hs, hk⟩ := ht
  refine ⟨Array.size_ofFn, fun k hkl => ?_⟩
  obtain ⟨h1, h2⟩ := hk k hkl
  constructor
  · rw [TabRep.comp_getElem! (n := 2 * base.length) _ _ ⟨k, by omega⟩]
    simp only
    rw [h1, dbl_get_left has (g.1 (base[k])).isLt, ha.apply (g.1 (base[k])).isLt]
    rfl
  · rw [TabRep.comp_getElem! (n := 2 * base.length) _ _ ⟨base.length + k, by omega⟩]
    simp only
    rw [h2, dbl_get_right has hbs (g.2 (base[k])).isLt, hb.apply (g.2 (base[k])).isLt]
    rfl

theorem pairRel_fun {base : List (Fin n)} {t t' : Tab}
    {g : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)} (ht : pairRel n base t g)
    (ht' : pairRel n base t' g) : t = t' := by
  apply Array.ext (ht.1.trans ht'.1.symm)
  intro i hi hi'
  have hi2 : i < 2 * base.length := ht.1 ▸ hi
  rw [← getElem!_pos t i hi, ← getElem!_pos t' i hi']
  by_cases hk : i < base.length
  · rw [(ht.2 i hk).1, (ht'.2 i hk).1]
  · obtain ⟨k, rfl⟩ : ∃ k, i = base.length + k := ⟨i - base.length, by omega⟩
    have hk' : k < base.length := by omega
    rw [(ht.2 k hk').2, (ht'.2 k hk').2]

end Pairs

end CFSG.Sporadic.ONOddCore
