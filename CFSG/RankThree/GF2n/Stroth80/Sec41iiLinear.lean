module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {V H : Type*} [AddCommGroup V] [Group H]

@[expose] def fixedIn (ρ : H →* Multiplicative (AddAut V)) (S : Subgroup H)
    (W : AddSubgroup V) : AddSubgroup V where
  carrier := {v | v ∈ W ∧ ∀ s ∈ S, (ρ s).toAdd v = v}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨W.add_mem ha hb, fun s hs => by rw [map_add, ha' s hs, hb' s hs]⟩
  zero_mem' := ⟨W.zero_mem, fun s _ => map_zero _⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨W.neg_mem ha, fun s hs => by rw [map_neg, ha' s hs]⟩

@[expose] def commIn (ρ : H →* Multiplicative (AddAut V)) (S : Subgroup H)
    (W : AddSubgroup V) : AddSubgroup V :=
  AddSubgroup.closure {x | ∃ s ∈ S, ∃ w ∈ W, x = (ρ s).toAdd w - w}

private def sumMap (A B : AddSubgroup V) (p : ↥A × ↥B) : ↥(A ⊔ B) :=
  ⟨(p.1 : V) + p.2, add_mem (AddSubgroup.mem_sup_left p.1.2) (AddSubgroup.mem_sup_right p.2.2)⟩

private lemma sumMap_surjective (A B : AddSubgroup V) : Function.Surjective (sumMap A B) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

private lemma sumMap_injective (A B : AddSubgroup V) (h : Disjoint A B) :
    Function.Injective (sumMap A B) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
  have hv : a + b = a' + b' := congrArg Subtype.val hab
  have key : a - a' - (b' - b) = (a + b) - (a' + b') := by abel
  rw [hv, sub_self] at key
  have hEq : a - a' = b' - b := sub_eq_zero.mp key
  have hmem : a - a' ∈ A ⊓ B := by
    refine AddSubgroup.mem_inf.mpr ⟨A.sub_mem ha ha', ?_⟩
    rw [hEq]
    exact B.sub_mem hb' hb
  rw [disjoint_iff.mp h, AddSubgroup.mem_bot] at hmem
  have h1 : a = a' := sub_eq_zero.mp hmem
  have h2 : b = b' := by
    have h3 : b' - b = 0 := by
      rw [← hEq]
      exact hmem
    exact (sub_eq_zero.mp h3).symm
  subst h1 h2
  rfl

private lemma card_sup_le_mul [Finite V] (A B : AddSubgroup V) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have h := Nat.card_le_card_of_surjective (sumMap A B) (sumMap_surjective A B)
  rwa [Nat.card_prod] at h

private lemma card_sup_of_disjoint [Finite V] {A B : AddSubgroup V} (h : Disjoint A B) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hbij : Function.Bijective (sumMap A B) := ⟨sumMap_injective A B h, sumMap_surjective A B⟩
  have h' := Nat.card_congr (Equiv.ofBijective (sumMap A B) hbij)
  rw [Nat.card_prod] at h'
  exact h'.symm

private lemma card_biSup_le_prod [Finite V] {ι : Type*} (W : ι → AddSubgroup V) (s : Finset ι) :
    Nat.card ↥(⨆ i ∈ s, W i) ≤ ∏ i ∈ s, Nat.card ↥(W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.iSup_insert, Finset.prod_insert hj]
    exact (card_sup_le_mul _ _).trans (Nat.mul_le_mul le_rfl ih)

private lemma card_biSup_of_iSupIndep [Finite V] {ι : Type*} {W : ι → AddSubgroup V}
    (hW : iSupIndep W) (s : Finset ι) :
    Nat.card ↥(⨆ i ∈ s, W i) = ∏ i ∈ s, Nat.card ↥(W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hdisj : Disjoint (W j) (⨆ i ∈ s, W i) :=
      hW.disjoint_biSup (x := j) (y := (s : Set ι)) (by simpa using hj)
    rw [Finset.iSup_insert, Finset.prod_insert hj, card_sup_of_disjoint hdisj, ih]

theorem card_iSup_le_prod [Finite V] {ι : Type*} [Fintype ι] (W : ι → AddSubgroup V) :
    Nat.card ↥(⨆ i, W i) ≤ ∏ i, Nat.card ↥(W i) := by
  simpa using card_biSup_le_prod W Finset.univ

theorem card_iSup_of_iSupIndep [Finite V] {ι : Type*} [Fintype ι] (W : ι → AddSubgroup V)
    (hW : iSupIndep W) : Nat.card ↥(⨆ i, W i) = ∏ i, Nat.card ↥(W i) := by
  simpa using card_biSup_of_iSupIndep hW Finset.univ

private lemma sub_mem_commIn {ρ : H →* Multiplicative (AddAut V)} {S : Subgroup H}
    {W : AddSubgroup V} {s : H} {w : V} (hs : s ∈ S) (hw : w ∈ W) :
    (ρ s).toAdd w - w ∈ commIn ρ S W :=
  AddSubgroup.subset_closure ⟨s, hs, w, hw, rfl⟩

theorem commIn_iSup_le {ι : Type*} (ρ : H →* Multiplicative (AddAut V)) (S : Subgroup H)
    (W : ι → AddSubgroup V) :
    commIn ρ S (⨆ i, W i) ≤ ⨆ i, commIn ρ S (W i) := by
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro x ⟨s, hs, w, hw, rfl⟩
  refine AddSubgroup.iSup_induction W
    (C := fun w' => (ρ s).toAdd w' - w' ∈ ⨆ i, commIn ρ S (W i)) hw ?_ ?_ ?_
  · intro i x hx
    exact le_iSup (fun j => commIn ρ S (W j)) i (sub_mem_commIn hs hx)
  · simp
  · intro x y hx hy
    have e : (ρ s).toAdd (x + y) - (x + y) = ((ρ s).toAdd x - x) + ((ρ s).toAdd y - y) := by
      rw [map_add]
      abel
    show (ρ s).toAdd (x + y) - (x + y) ∈ ⨆ i, commIn ρ S (W i)
    rw [e]
    exact add_mem hx hy

theorem card_commIn_iSup_le [Finite V] {ι : Type*} [Fintype ι]
    (ρ : H →* Multiplicative (AddAut V)) (S : Subgroup H) (W : ι → AddSubgroup V) :
    Nat.card ↥(commIn ρ S (⨆ i, W i)) ≤ ∏ i, Nat.card ↥(commIn ρ S (W i)) := by
  refine le_trans ?_ (card_iSup_le_prod fun i => commIn ρ S (W i))
  exact Nat.card_le_card_of_injective (AddSubgroup.inclusion (commIn_iSup_le ρ S W))
    (AddSubgroup.inclusion_injective _)

private lemma mem_fixedIn_iff {ρ : H →* Multiplicative (AddAut V)} {S : Subgroup H}
    {W : AddSubgroup V} {v : V} : v ∈ fixedIn ρ S W ↔ v ∈ W ∧ ∀ s ∈ S, (ρ s).toAdd v = v :=
  Iff.rfl

private lemma eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι] {W : ι → AddSubgroup V}
    (hW : iSupIndep W) {u : ι → V} (hu : ∀ i, u i ∈ W i) (hs : ∑ i, u i = 0) (j : ι) :
    u j = 0 := by
  classical
  have hdisj : Disjoint (W j) (⨆ i ∈ (Finset.univ.erase j : Finset ι), W i) :=
    hW.disjoint_biSup (x := j) (y := ((Finset.univ.erase j : Finset ι) : Set ι)) (by simp)
  have hsum' : u j = -∑ i ∈ Finset.univ.erase j, u i := by
    have h := Finset.add_sum_erase Finset.univ u (Finset.mem_univ j)
    rw [hs] at h
    exact eq_neg_of_add_eq_zero_left h
  have hmem : ∑ i ∈ Finset.univ.erase j, u i ∈ ⨆ i ∈ (Finset.univ.erase j : Finset ι), W i :=
    AddSubgroup.sum_mem _ fun i hi =>
      le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ.erase j : Finset ι)) => W i) i hi (hu i)
  have hmem' : u j ∈ W j ⊓ ⨆ i ∈ (Finset.univ.erase j : Finset ι), W i := by
    refine AddSubgroup.mem_inf.mpr ⟨hu j, ?_⟩
    rw [hsum']
    exact neg_mem hmem
  rw [disjoint_iff.mp hdisj, AddSubgroup.mem_bot] at hmem'
  exact hmem'

private lemma exists_sum_eq_of_mem_iSup {ι : Type*} [Fintype ι] {W : ι → AddSubgroup V} {v : V}
    (hv : v ∈ ⨆ i, W i) : ∃ w : ι → V, (∀ i, w i ∈ W i) ∧ ∑ i, w i = v := by
  classical
  refine AddSubgroup.iSup_induction W
    (C := fun v => ∃ w : ι → V, (∀ i, w i ∈ W i) ∧ ∑ i, w i = v) hv ?_
    ⟨0, fun i => (W i).zero_mem, by simp⟩ ?_
  · intro j x hx
    refine ⟨Pi.single j x, fun i => ?_, by simp⟩
    by_cases h : i = j
    · subst h
      simpa using hx
    · rw [Pi.single_eq_of_ne h]
      exact (W i).zero_mem
  · rintro x y ⟨w₁, h₁, e₁⟩ ⟨w₂, h₂, e₂⟩
    refine ⟨w₁ + w₂, fun i => (W i).add_mem (h₁ i) (h₂ i), ?_⟩
    simp [Finset.sum_add_distrib, e₁, e₂]

theorem card_fixedIn_iSup [Finite V] {ι : Type*} [Fintype ι]
    (ρ : H →* Multiplicative (AddAut V)) (S : Subgroup H)
    (W : ι → AddSubgroup V) (hW : iSupIndep W)
    (hinv : ∀ (i : ι) (h : H) (v : V), v ∈ W i → (ρ h).toAdd v ∈ W i) :
    Nat.card ↥(fixedIn ρ S (⨆ i, W i)) = ∏ i, Nat.card ↥(fixedIn ρ S (W i)) := by
  have heq : fixedIn ρ S (⨆ i, W i) = ⨆ i, fixedIn ρ S (W i) := by
    refine le_antisymm ?_ (iSup_le fun i => ?_)
    · intro v hv
      obtain ⟨hvW, hvfix⟩ := mem_fixedIn_iff.mp hv
      obtain ⟨w, hw, hsum⟩ := exists_sum_eq_of_mem_iSup hvW
      have hwfix : ∀ i, ∀ s ∈ S, (ρ s).toAdd (w i) = w i := by
        intro i s hs
        have hu : ∀ j, (ρ s).toAdd (w j) - w j ∈ W j := fun j =>
          (W j).sub_mem (hinv j s (w j) (hw j)) (hw j)
        have hsum0 : ∑ j, ((ρ s).toAdd (w j) - w j) = 0 := by
          rw [Finset.sum_sub_distrib, ← map_sum, hsum, hvfix s hs, sub_self]
        exact sub_eq_zero.mp (eq_zero_of_sum_eq_zero hW hu hsum0 i)
      rw [← hsum]
      exact AddSubgroup.sum_mem _ fun i _ =>
        le_iSup (fun j => fixedIn ρ S (W j)) i (mem_fixedIn_iff.mpr ⟨hw i, hwfix i⟩)
    · intro v hv
      obtain ⟨hvW, hvfix⟩ := mem_fixedIn_iff.mp hv
      exact mem_fixedIn_iff.mpr ⟨le_iSup W i hvW, hvfix⟩
  have hind : iSupIndep (fun i => fixedIn ρ S (W i)) :=
    hW.mono fun i v hv => (mem_fixedIn_iff.mp hv).1
  rw [heq]
  exact card_iSup_of_iSupIndep (fun i => fixedIn ρ S (W i)) hind

theorem exists_iSupIndep_of_simple {V H ι : Type*} [AddCommGroup V] [Finite V] [Group H]
    (ρ : H →* Multiplicative (AddAut V)) (W : ι → AddSubgroup V)
    (hinv : ∀ (i : ι) (h : H) (v : V), v ∈ W i → (ρ h).toAdd v ∈ W i)
    (hsimple : ∀ i, W i ≠ ⊥ ∧ ∀ T : AddSubgroup V, T ≤ W i →
      (∀ (h : H) (v : V), v ∈ T → (ρ h).toAdd v ∈ T) → T = ⊥ ∨ T = W i) :
    ∃ J : Set ι, J.Finite ∧ iSupIndep (fun j : J => W j) ∧ (⨆ j : J, W j) = ⨆ i, W i := by
  classical
  have hfin : Finite (AddSubgroup V) :=
    Finite.of_injective (fun K : AddSubgroup V => (K : Set V)) SetLike.coe_injective
  set S : Set (AddSubgroup V) := {T | ∃ J : Finset ι, J.SupIndep W ∧ T = J.sup W} with hS
  have hmemS : ∀ T, T ∈ S ↔ ∃ J : Finset ι, J.SupIndep W ∧ T = J.sup W := fun T => Iff.rfl
  have hne : S.Nonempty := ⟨⊥, (hmemS _).2 ⟨∅, Finset.supIndep_empty W, by simp⟩⟩
  obtain ⟨T, hTS, hTmax⟩ := (Set.toFinite S).exists_maximal hne
  obtain ⟨J, hJ, rfl⟩ := (hmemS T).1 hTS
  have hinvT : ∀ (h : H) (v : V), v ∈ J.sup W → (ρ h).toAdd v ∈ J.sup W := by
    refine Finset.sup_induction
      (p := fun K : AddSubgroup V => ∀ (h : H) (v : V), v ∈ K → (ρ h).toAdd v ∈ K) ?_ ?_ ?_
    · intro h v hv
      rw [AddSubgroup.mem_bot] at hv
      rw [hv, map_zero]
      exact zero_mem _
    · intro a ha b hb h v hv
      obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
      rw [map_add]
      exact add_mem (AddSubgroup.mem_sup_left (ha h y hy)) (AddSubgroup.mem_sup_right (hb h z hz))
    · intro i _ h v hv
      exact hinv i h v hv
  have hWle : ∀ i, W i ≤ J.sup W := by
    intro i
    have hne' := (hsimple i).1
    rcases (hsimple i).2 (W i ⊓ J.sup W) inf_le_left
        (fun h v hv => ⟨hinv i h v hv.1, hinvT h v hv.2⟩) with hbot | htop
    · exfalso
      have hdisj : Disjoint (W i) (J.sup W) := disjoint_iff.2 hbot
      have hmem : W i ⊔ J.sup W ∈ S :=
        (hmemS _).2 ⟨insert i J, hJ.insert hdisj, by rw [Finset.sup_insert]⟩
      have hle : W i ⊔ J.sup W ≤ J.sup W := hTmax hmem le_sup_right
      have hWT : W i ≤ J.sup W := le_trans le_sup_left hle
      exact hne' (le_bot_iff.1 (by rw [← hbot]; exact le_inf le_rfl hWT))
    · exact inf_eq_left.1 htop
  have hsub : J.sup W ≤ ⨆ j : (J : Set ι), W j :=
    Finset.sup_le fun j hj => le_iSup (fun j : (J : Set ι) => W j) ⟨j, hj⟩
  refine ⟨(J : Set ι), J.finite_toSet, ?_, ?_⟩
  · exact (iSupIndep_comp_coe_iff_supIndep).2 hJ
  · exact le_antisymm (iSup_le fun j => le_iSup W (j : ι)) (iSup_le fun i => le_trans (hWle i) hsub)

section Isometry

variable {K : Type*} [Field K] [Module K V]

theorem card_commIn_mul_card_fixedIn [Finite K] [Module.Finite K V] (f : LinearMap.BilinForm K V)
    (halt : ∀ v, f v v = 0) (hnd : ∀ v, (∀ w, f v w = 0) → v = 0)
    (ρ : H →* Multiplicative (AddAut V))
    (hK : ∀ (h : H) (c : K) (v : V), (ρ h).toAdd (c • v) = c • (ρ h).toAdd v)
    (hiso : ∀ (h : H) (v w : V), f ((ρ h).toAdd v) ((ρ h).toAdd w) = f v w)
    (S : Subgroup H) :
    Nat.card (commIn ρ S ⊤) * Nat.card (fixedIn ρ S ⊤) = Nat.card V := by
  have hneg : ∀ x y : V, f x y = -f y x := by
    intro x y
    have h1 : f (x + y) (x + y) = 0 := halt _
    simp only [map_add, LinearMap.add_apply, halt] at h1
    linear_combination h1
  have hsepR : ∀ y : V, (∀ x : V, f x y = 0) → y = 0 := fun y hy =>
    hnd y (fun w => by rw [hneg y w, hy w, neg_zero])
  have hnondeg : LinearMap.BilinForm.Nondegenerate f := ⟨hnd, hsepR⟩
  have hgen : ∀ s ∈ S, ∀ u : V, (ρ s).toAdd u - u ∈ commIn ρ S ⊤ := by
    intro s hs u
    unfold commIn
    exact AddSubgroup.subset_closure ⟨s, hs, u, AddSubgroup.mem_top u, rfl⟩
  have hle : ∀ A : AddSubgroup V, (∀ s ∈ S, ∀ u : V, (ρ s).toAdd u - u ∈ A) →
      ∀ x ∈ commIn ρ S ⊤, x ∈ A := by
    intro A hA x hx
    have hsub : commIn ρ S ⊤ ≤ A := by
      unfold commIn
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro _ ⟨s, hs, u, _, rfl⟩
      exact hA s hs u
    exact hsub hx
  have hsmul : ∀ (c : K) (x : V), x ∈ commIn ρ S ⊤ → c • x ∈ commIn ρ S ⊤ := by
    intro c x hx
    let A : AddSubgroup V :=
      { carrier := {y | c • y ∈ commIn ρ S ⊤}
        add_mem' := fun {a b} ha hb => by
          have ha' : c • a ∈ commIn ρ S ⊤ := ha
          have hb' : c • b ∈ commIn ρ S ⊤ := hb
          show c • (a + b) ∈ commIn ρ S ⊤
          rw [smul_add]
          exact AddSubgroup.add_mem (commIn ρ S ⊤) ha' hb'
        zero_mem' := by
          show c • (0 : V) ∈ commIn ρ S ⊤
          rw [smul_zero]
          exact AddSubgroup.zero_mem (commIn ρ S ⊤)
        neg_mem' := fun {a} ha => by
          have ha' : c • a ∈ commIn ρ S ⊤ := ha
          show c • (-a) ∈ commIn ρ S ⊤
          rw [smul_neg]
          exact AddSubgroup.neg_mem (commIn ρ S ⊤) ha' }
    refine hle A (fun s hs u => ?_) x hx
    show c • ((ρ s).toAdd u - u) ∈ commIn ρ S ⊤
    rw [smul_sub, ← hK]
    exact hgen s hs (c • u)
  obtain ⟨D, hD⟩ : ∃ D : Submodule K V, ∀ x, x ∈ D ↔ x ∈ commIn ρ S ⊤ :=
    ⟨{ carrier := {x | x ∈ commIn ρ S ⊤}
       add_mem' := fun {a b} ha hb => AddSubgroup.add_mem (commIn ρ S ⊤) ha hb
       zero_mem' := AddSubgroup.zero_mem (commIn ρ S ⊤)
       smul_mem' := fun c {x} hx => hsmul c x hx }, fun x => Iff.rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Submodule K V, ∀ x, x ∈ C ↔ ∀ s ∈ S, (ρ s).toAdd x = x := by
    refine ⟨{ carrier := {x | ∀ s ∈ S, (ρ s).toAdd x = x}
              add_mem' := ?_
              zero_mem' := ?_
              smul_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      have ha' : ∀ s ∈ S, (ρ s).toAdd a = a := ha
      have hb' : ∀ s ∈ S, (ρ s).toAdd b = b := hb
      show ∀ s ∈ S, (ρ s).toAdd (a + b) = a + b
      intro s hs
      rw [map_add, ha' s hs, hb' s hs]
    · show ∀ s ∈ S, (ρ s).toAdd (0 : V) = 0
      intro s _
      exact map_zero _
    · intro c x hx
      have hx' : ∀ s ∈ S, (ρ s).toAdd x = x := hx
      show ∀ s ∈ S, (ρ s).toAdd (c • x) = c • x
      intro s hs
      rw [hK, hx' s hs]
  have hfix : ∀ x, x ∈ fixedIn ρ S ⊤ ↔ x ∈ C := by
    intro x
    rw [hC x]
    exact ⟨fun h => h.2, fun h => ⟨AddSubgroup.mem_top x, h⟩⟩
  have hCD : f.orthogonal D = C := by
    ext w
    rw [LinearMap.BilinForm.mem_orthogonal_iff, hC w]
    constructor
    · intro hw s hs
      have key : ∀ v : V, f v ((ρ s).toAdd w - w) = 0 := by
        intro v
        obtain ⟨u, rfl⟩ : ∃ u, (ρ s).toAdd u = v :=
          ⟨AddEquiv.symm (ρ s).toAdd v, AddEquiv.apply_symm_apply (ρ s).toAdd v⟩
        have h1 : f ((ρ s).toAdd u - u) w = 0 := hw _ ((hD _).mpr (hgen s hs u))
        have h2 := hiso s u w
        simp only [map_sub, LinearMap.sub_apply] at h1 ⊢
        linear_combination h2 - h1
      exact sub_eq_zero.mp (hsepR _ key)
    · intro hw x hx
      have hxc : x ∈ commIn ρ S ⊤ := (hD x).mp hx
      let A : AddSubgroup V :=
        { carrier := {y | f y w = 0}
          add_mem' := fun {a b} ha hb => by
            have ha' : f a w = 0 := ha
            have hb' : f b w = 0 := hb
            show f (a + b) w = 0
            rw [map_add, LinearMap.add_apply, ha', hb', add_zero]
          zero_mem' := by
            show f 0 w = 0
            rw [map_zero, LinearMap.zero_apply]
          neg_mem' := fun {a} ha => by
            have ha' : f a w = 0 := ha
            show f (-a) w = 0
            rw [map_neg, LinearMap.neg_apply, ha', neg_zero] }
      refine hle A (fun s hs u => ?_) x hxc
      show f ((ρ s).toAdd u - u) w = 0
      have h2 := hiso s u w
      rw [hw s hs] at h2
      simp only [map_sub, LinearMap.sub_apply]
      rw [h2, sub_self]
  have hfin : Module.finrank K D + Module.finrank K C = Module.finrank K V := by
    have h2 := LinearMap.BilinForm.finrank_orthogonal hnondeg D
    have h3 := Submodule.finrank_le D
    rw [hCD] at h2
    omega
  have hcardC : Nat.card (commIn ρ S ⊤) = Nat.card D :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hD x).symm)
  have hcardF : Nat.card (fixedIn ρ S ⊤) = Nat.card C :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  rw [hcardC, hcardF, Module.natCard_eq_pow_finrank (K := K) (V := ↥D),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥C),
    Module.natCard_eq_pow_finrank (K := K) (V := V), ← pow_add, hfin]

end Isometry

end CFSG.RankThree.GF2n.Stroth80
