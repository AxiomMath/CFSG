module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Counterexample

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open scoped commutatorElement

section Support

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

@[expose] def suppSubgroup (G : ι → Type*) [∀ i, Group (G i)] (p : ι → Prop) :
    Subgroup (∀ i, G i) where
  carrier := {x | ∀ i, ¬ p i → x i = 1}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb i hi := by simp [ha i hi, hb i hi]
  inv_mem' {a} ha i hi := by simp [ha i hi]

theorem mem_suppSubgroup {p : ι → Prop} {x : ∀ i, G i} :
    x ∈ suppSubgroup G p ↔ ∀ i, ¬ p i → x i = 1 := Iff.rfl

@[expose] def suppOf (N : Subgroup (∀ i, G i)) : ι → Prop := fun i => ∃ y ∈ N, y i ≠ 1

theorem suppOf_iff {N : Subgroup (∀ i, G i)} {i : ι} : suppOf N i ↔ ∃ y ∈ N, y i ≠ 1 :=
  Iff.rfl

theorem eq_one_of_forall_commute {J : Type*} [Group J] [IsSimpleGroup J]
    (hnc : ¬ IsMulCommutative J) {z : J} (hz : ∀ g : J, g * z = z * g) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · have : z ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr hz
    rwa [h, Subgroup.mem_bot] at this
  · refine absurd (IsMulCommutative.of_comm fun x y => ?_) hnc
    have : y ∈ Subgroup.center J := h ▸ Subgroup.mem_top y
    exact Subgroup.mem_center_iff.mp this x

theorem mem_of_mulSingle_mem [Fintype ι] [DecidableEq ι] (N : Subgroup (∀ i, G i))
    (x : ∀ i, G i) (h : ∀ i, Pi.mulSingle i (x i) ∈ N) : x ∈ N := by
  have key : ∀ t : Finset ι, ∀ x : ∀ i, G i, (∀ i, i ∉ t → x i = 1) →
      (∀ i, Pi.mulSingle i (x i) ∈ N) → x ∈ N := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx _
      have : x = 1 := funext fun i => hx i (Finset.notMem_empty i)
      rw [this]
      exact one_mem N
    | insert j t hj ih =>
      intro x hx hN
      have h1 : x = Pi.mulSingle j (x j) * Function.update x j 1 := by
        funext i
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      rw [h1]
      refine mul_mem (hN j) (ih _ (fun i hi => ?_) (fun i => ?_))
      · by_cases hij : i = j
        · subst hij
          simp
        · rw [Function.update_of_ne hij]
          exact hx i (by simp [hij, hi])
      · by_cases hij : i = j
        · subst hij
          simp
        · rw [Function.update_of_ne hij]
          exact hN i
  exact key Finset.univ x (fun i hi => absurd (Finset.mem_univ i) hi) h

theorem mulSingle_mem_of_mem_suppOf [DecidableEq ι] [∀ i, IsSimpleGroup (G i)]
    (hnc : ∀ i, ¬ IsMulCommutative (G i)) (N : Subgroup (∀ i, G i)) [N.Normal] {i : ι}
    (hi : suppOf N i) (g : G i) : Pi.mulSingle i g ∈ N := by
  obtain ⟨y, hyN, hyi⟩ := hi
  let L : Subgroup (G i) := N.comap (MonoidHom.mulSingle G i)
  have hLn : L.Normal := Subgroup.Normal.comap inferInstance _
  have hcomm : ∀ g : G i, Pi.mulSingle i ⁅y i, g⁆ ∈ N := by
    intro g
    have h1 : Pi.mulSingle i ⁅y i, g⁆ = ⁅y, Pi.mulSingle i g⁆ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [commutatorElement_def]
      · simp [hj, commutatorElement_def]
    rw [h1, commutatorElement_def]
    have h2 : Pi.mulSingle i g * y⁻¹ * (Pi.mulSingle i g)⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem (inferInstance : N.Normal) y⁻¹ (inv_mem hyN) (Pi.mulSingle i g)
    have e : y * Pi.mulSingle i g * y⁻¹ * (Pi.mulSingle i g)⁻¹ =
        y * (Pi.mulSingle i g * y⁻¹ * (Pi.mulSingle i g)⁻¹) := by group
    rw [e]
    exact mul_mem hyN h2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
  · exfalso
    refine hyi (eq_one_of_forall_commute (hnc i) fun g => ?_)
    have : ⁅y i, g⁆ ∈ L := hcomm g
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  · have : g ∈ L := h ▸ Subgroup.mem_top g
    exact this

theorem eq_suppSubgroup_suppOf [Fintype ι] [∀ i, IsSimpleGroup (G i)]
    (hnc : ∀ i, ¬ IsMulCommutative (G i)) (N : Subgroup (∀ i, G i)) [N.Normal] :
    N = suppSubgroup G (suppOf N) := by
  classical
  ext x
  constructor
  · intro hx i hi
    by_contra hxi
    exact hi ⟨x, hx, hxi⟩
  · intro hx
    refine mem_of_mulSingle_mem N x fun i => ?_
    by_cases hi : suppOf N i
    · exact mulSingle_mem_of_mem_suppOf hnc N hi (x i)
    · rw [hx i hi, Pi.mulSingle_one]
      exact one_mem N

@[expose] noncomputable def embSub (G : ι → Type*) [∀ i, Group (G i)] (p : ι → Prop) :
    (∀ i : {i // p i}, G i) →* ∀ i, G i := by
  classical
  exact
  { toFun := fun x i => if h : p i then x ⟨i, h⟩ else 1
    map_one' := by
      funext i
      by_cases h : p i <;> simp [h]
    map_mul' := fun x y => by
      funext i
      by_cases h : p i <;> simp [h] }

theorem embSub_apply_of_pos (p : ι → Prop) (x : ∀ i : {i // p i}, G i) {i : ι} (hi : p i) :
    embSub G p x i = x ⟨i, hi⟩ := by
  classical
  simp [embSub, hi]

theorem embSub_apply_of_neg (p : ι → Prop) (x : ∀ i : {i // p i}, G i) {i : ι} (hi : ¬ p i) :
    embSub G p x i = 1 := by
  classical
  simp [embSub, hi]

theorem embSub_injective (p : ι → Prop) : Function.Injective (embSub G p) := by
  intro x y h
  funext ⟨i, hi⟩
  have := congrFun h i
  rwa [embSub_apply_of_pos p x hi, embSub_apply_of_pos p y hi] at this

theorem embSub_mem_suppSubgroup (p : ι → Prop) (x : ∀ i : {i // p i}, G i) :
    embSub G p x ∈ suppSubgroup G p := fun _ hi => embSub_apply_of_neg p x hi

theorem embSub_commute (p : ι → Prop) (x : ∀ i : {i // p i}, G i)
    (y : ∀ i : {i // ¬ p i}, G i) : Commute (embSub G p x) (embSub G (fun i => ¬ p i) y) := by
  rw [Commute, SemiconjBy]
  funext i
  by_cases hi : p i
  · simp [embSub_apply_of_neg (fun i => ¬ p i) y (not_not.mpr hi)]
  · simp [embSub_apply_of_neg p x hi]

theorem eq_embSub_mul_embSub (p : ι → Prop) (q : ∀ i, G i) :
    q = embSub G p (fun i => q i) * embSub G (fun i => ¬ p i) (fun i => q i) := by
  funext i
  by_cases hi : p i
  · simp [embSub_apply_of_pos p _ hi, embSub_apply_of_neg (fun i => ¬ p i) _ (not_not.mpr hi)]
  · simp [embSub_apply_of_neg p _ hi, embSub_apply_of_pos (fun i => ¬ p i) _ hi]

theorem exists_eq_embSub_mul (p : ι → Prop) (q : ∀ i, G i) :
    ∃ (x : ∀ i : {i // p i}, G i) (y : ∀ i : {i // ¬ p i}, G i),
      q = embSub G p x * embSub G (fun i => ¬ p i) y :=
  ⟨_, _, eq_embSub_mul_embSub p q⟩

theorem embSub_suppOf_mem [Fintype ι] [∀ i, IsSimpleGroup (G i)]
    (hnc : ∀ i, ¬ IsMulCommutative (G i)) (N : Subgroup (∀ i, G i)) [N.Normal]
    (y : ∀ i : {i // suppOf N i}, G i) : embSub G (suppOf N) y ∈ N :=
  (SetLike.ext_iff.mp (eq_suppSubgroup_suppOf hnc N) _).mpr (embSub_mem_suppSubgroup _ y)

theorem eq_one_of_embSub_mem [Fintype ι] [∀ i, IsSimpleGroup (G i)]
    (hnc : ∀ i, ¬ IsMulCommutative (G i)) (N : Subgroup (∀ i, G i)) [N.Normal]
    (y : ∀ i : {i // ¬ suppOf N i}, G i)
    (h : embSub G (fun i => ¬ suppOf N i) y ∈ N) : y = 1 := by
  have h' := (SetLike.ext_iff.mp (eq_suppSubgroup_suppOf hnc N) _).mp h
  funext ⟨i, hi⟩
  have := h' i hi
  rwa [embSub_apply_of_pos (fun i => ¬ suppOf N i) y hi] at this

end Support

end CFSG.SignalizerFunctorTheorem.McBride.Near
