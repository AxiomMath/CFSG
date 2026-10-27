module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Sylow
import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Map
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup

noncomputable def kleinSub (a b : El) : Subgroup (MulAut S4) := Subgroup.closure {autOf a, autOf b}

private def w183finSp44_pairSub {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) : Subgroup G where
  carrier := {1, a, b, a * b}
  mul_mem' := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
    have h3 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
    have h6 : b * a = a * b := hab.symm
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, ha, hb, h1, h2,
        h3, h4, h5, h6, true_or, or_true]
  one_mem' := Or.inl rfl
  inv_mem' := by
    have h5 : a * b * (a * b) = 1 := by
      rw [← mul_assoc, mul_assoc a b a, ← hab, ← mul_assoc, ha, one_mul, hb]
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · rw [inv_eq_of_mul_eq_one_right ha]
      exact Or.inr (Or.inl rfl)
    · rw [inv_eq_of_mul_eq_one_right hb]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [inv_eq_of_mul_eq_one_right h5]
      exact Or.inr (Or.inr (Or.inr rfl))

private theorem w183finSp44_mem_pairSub {G : Type*} [Group G] {a b : G}
    {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : G} :
    x ∈ w183finSp44_pairSub ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

private theorem w183finSp44_closure_pair_eq {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup.closure ({a, b} : Set G) = w183finSp44_pairSub ha hb hab := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    change x = 1 ∨ x = a ∨ x = b ∨ x = a * b
    rcases hx with hx | hx
    · rw [hx]; exact Or.inr (Or.inl rfl)
    · rw [hx]; exact Or.inr (Or.inr (Or.inl rfl))
  · intro x hx
    change x = 1 ∨ x = a ∨ x = b ∨ x = a * b at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact one_mem _
    · rw [hx]; exact Subgroup.subset_closure (by simp)
    · rw [hx]; exact Subgroup.subset_closure (by simp)
    · rw [hx]
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private theorem w183finSp44_closure_pair_mem {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) {x : G} :
    x ∈ Subgroup.closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  rw [w183finSp44_closure_pair_eq ha hb hab]
  exact Iff.rfl

private theorem w183finSp44_card_pairSub {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (w183finSp44_pairSub ha hb hab) = 4 := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, ha, one_mul])
  have haab : a ≠ a * b := fun h => hb1 (by
    rw [← one_mul b, ← ha, mul_assoc, ← h, ha])
  have hbab : b ≠ a * b := fun h => ha1 (by
    rw [← mul_one a, ← hb, ← mul_assoc, ← h, hb])
  classical
  have e : ((w183finSp44_pairSub ha hb hab : Subgroup G) : Set G) =
      ({1, a, b, a * b} : Finset G) := by
    ext y
    simp only [SetLike.mem_coe, w183finSp44_mem_pairSub, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem (by simp [ha1.symm, hb1.symm, hab1.symm]),
    Finset.card_insert_of_notMem (by simp [hne, haab]),
    Finset.card_insert_of_notMem (by simp [hbab]), Finset.card_singleton]

private theorem w183finSp44_isElemAbelian_closure_pair {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    IsElemAbelian 2 (Subgroup.closure ({a, b} : Set G)) :=
  ⟨Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rw [hx, hy]
      · rw [hx, hy]; exact hab
      · rw [hx, hy]; exact hab.symm
      · rw [hx, hy]),
    by
      intro x hx
      rw [w183finSp44_closure_pair_mem ha hb hab] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp
      · simpa [pow_two] using ha
      · simpa [pow_two] using hb
      · have h4 : (a * b) * (a * b) = (a * a) * (b * b) :=
          (Commute.mul_mul_mul_comm hab a b).symm
        rw [pow_two, h4, ha, one_mul, hb]⟩

private theorem w183finSp44_mem_Pel_of_mem_invs {x : El} (hx : x ∈ invs) : x ∈ Pel :=
  (List.mem_filter.mp hx).1

private theorem w183finSp44_ne_one_of_mem_invs {x : El} (hx : x ∈ invs) : x ≠ oneE := by
  have hcond := (List.mem_filter.mp hx).2
  rw [Bool.and_eq_true_iff] at hcond
  exact of_decide_eq_true hcond.1

private theorem w183finSp44_gmulE_self_of_mem_invs {x : El} (hx : x ∈ invs) :
    gmulE x x = oneE := by
  have hcond := (List.mem_filter.mp hx).2
  rw [Bool.and_eq_true_iff] at hcond
  exact beq_iff_eq.mp hcond.2

private theorem w183finSp44_invsA_mem {i : Nat} (hi : i < n127) : invsA[i]! ∈ invs := by
  rw [invsA, List.getElem!_toArray, List.getElem!_eq_getElem?_getD]
  have hsome : invs[i]? = some (invs[i]'hi) :=
    (List.getElem?_eq_some_getElem_iff hi).mpr trivial
  simpa [hsome] using List.mem_of_getElem? hsome

private theorem w183finSp44_invsA_ne_one {i : Nat} (hi : i < n127) : invsA[i]! ≠ oneE :=
  w183finSp44_ne_one_of_mem_invs (w183finSp44_invsA_mem hi)

private theorem w183finSp44_valid_invsA {i : Nat} (hi : i < n127) :
    validB invsA[i]! = true :=
  Pel_valid _ (w183finSp44_mem_Pel_of_mem_invs (w183finSp44_invsA_mem hi))

private theorem w183finSp44_invs_nodup : invs.Nodup := by decide +kernel

private theorem w183finSp44_invsA_ne {i j : Nat} (hi : i < n127) (hj : j < n127)
    (hij : i < j) : invsA[i]! ≠ invsA[j]! := by
  intro h
  have hi' : i < invs.length := hi
  have hj' : j < invs.length := hj
  have h1 : invs[i]! = invs[i]'hi' := by
    rw [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact (List.getElem_eq_getD (l := invs) (i := i) (h := hi') default).symm
  have h2 : invs[j]! = invs[j]'hj' := by
    rw [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact (List.getElem_eq_getD (l := invs) (i := j) (h := hj') default).symm
  have e1 : invsA[i]! = invs[i]'hi' := by
    rw [invsA, List.getElem!_toArray]; exact h1
  have e2 : invsA[j]! = invs[j]'hj' := by
    rw [invsA, List.getElem!_toArray]; exact h2
  have h' : invs[i]'hi' = invs[j]'hj' := by
    rw [← e1, ← e2]; exact h
  exact absurd ((List.Nodup.getElem_inj_iff w183finSp44_invs_nodup (hi := hi')
    (hj := hj')).mp h') (ne_of_lt hij)

private theorem w183finSp44_mem_pairsFrom_imp {lo hi : Nat} {p : Nat × Nat}
    (hp : p ∈ pairsFrom lo hi) :
    p.1 < p.2 ∧ p.2 < n127 ∧
      gmulE invsA[p.1]! invsA[p.2]! = gmulE invsA[p.2]! invsA[p.1]! := by
  rw [pairsFrom] at hp
  obtain ⟨i, -, hfil⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, hj, hf⟩ := List.mem_filterMap.mp hfil
  rw [List.mem_range] at hj
  by_cases hc : i < j && (gmulE invsA[i]! invsA[j]! == gmulE invsA[j]! invsA[i]!)
  · rw [if_pos hc, Option.some.injEq] at hf
    obtain ⟨hij, hcomm⟩ := Bool.and_eq_true_iff.mp hc
    have h1 : i = p.1 := congrArg Prod.fst hf
    have h2 : j = p.2 := congrArg Prod.snd hf
    exact ⟨by rw [← h1, ← h2]; exact of_decide_eq_true hij, by rw [← h2]; exact hj,
      by rw [← h1, ← h2]; exact beq_iff_eq.mp hcomm⟩
  · rw [if_neg hc] at hf
    exact absurd hf (by simp)

private theorem w183finSp44_mem_pairsFrom_of {lo hi : Nat} {p : Nat × Nat}
    (hlo : lo ≤ p.1) (hhi : p.1 < hi) (hp12 : p.1 < p.2) (hp2 : p.2 < n127)
    (hcomm : gmulE invsA[p.1]! invsA[p.2]! = gmulE invsA[p.2]! invsA[p.1]!) :
    p ∈ pairsFrom lo hi := by
  rw [pairsFrom]
  refine List.mem_flatMap.mpr ⟨p.1, ?_, ?_⟩
  · rw [List.mem_range']
    exact ⟨p.1 - lo, by omega, by omega⟩
  · rw [List.mem_filterMap]
    refine ⟨p.2, List.mem_range.mpr hp2, ?_⟩
    have hc : (p.1 < p.2 &&
        (gmulE invsA[p.1]! invsA[p.2]! == gmulE invsA[p.2]! invsA[p.1]!)) = true := by
      rw [Bool.and_eq_true_iff]
      exact ⟨by simpa using hp12, by rw [beq_iff_eq]; exact hcomm⟩
    rw [if_pos hc]

private def w183finSp44_pairBlocksCover : Bool :=
  (List.range 127).all fun i => pairBlocks.any fun b => decide (b.1 ≤ i ∧ i < b.2)

private theorem w183finSp44_pairBlocksCover_eq : w183finSp44_pairBlocksCover = true := by
  decide +kernel

private theorem w183finSp44_pairBlocks_cover {i : Nat} (hi : i < 127) :
    ∃ b ∈ pairBlocks, b.1 ≤ i ∧ i < b.2 := by
  have h := List.all_eq_true.mp w183finSp44_pairBlocksCover_eq i (List.mem_range.mpr hi)
  obtain ⟨b, hb, hb'⟩ := List.any_eq_true.mp h
  exact ⟨b, hb, of_decide_eq_true hb'⟩

private theorem w183finSp44_kleinSub_comm (a b : El) : kleinSub a b = kleinSub b a := by
  rw [kleinSub, kleinSub, Set.pair_comm]

private theorem w183finSp44_mem_klein_iff {a b x : El} :
    x ∈ klein a b ↔ x = oneE ∨ x = a ∨ x = b ∨ x = gmulE a b := by
  rw [klein]
  simp only [List.mem_cons, List.mem_nil_iff, List.not_mem_nil, false_or, or_false]

private theorem w183finSp44_mem_kleinSub_aux (a b : El) (α : MulAut S4)
    (hva : validB a = true) (hvb : validB b = true)
    (ha : autOf a * autOf a = 1) (hb : autOf b * autOf b = 1)
    (hab : autOf a * autOf b = autOf b * autOf a) :
    α ∈ kleinSub a b ↔ ∃ x ∈ klein a b, autOf x = α := by
  have hcl := w183finSp44_closure_pair_mem (a := autOf a) (b := autOf b) ha hb hab (x := α)
  refine hcl.trans ?_
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨oneE, w183finSp44_mem_klein_iff.mpr (Or.inl rfl), autOf_oneE⟩
    · exact ⟨a, w183finSp44_mem_klein_iff.mpr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨b, w183finSp44_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    · exact ⟨gmulE a b, w183finSp44_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inr rfl))),
        autOf_gmulE hva hvb⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' := w183finSp44_mem_klein_iff.mp hx
    rcases hx' with rfl | rfl | rfl | rfl
    · exact Or.inl autOf_oneE
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (autOf_gmulE hva hvb)))

theorem mem_invs_iff (α : MulAut S4) :
    (α ∈ Psub ∧ orderOf α = 2) ↔ ∃ x ∈ invs, autOf x = α := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hP, hord⟩
    obtain ⟨x, hxPel, hxα⟩ := (mem_Psub_iff α).mp hP
    have hval : validB x = true := Pel_valid x hxPel
    have hxne : x ≠ oneE := by
      intro h
      have hα1 : α = 1 := by rw [← hxα, h, autOf_oneE]
      rw [hα1] at hord
      simp at hord
    have hself : gmulE x x = oneE := by
      apply autOf_inj (validB_gmulE hval hval) validB_oneE
      rw [autOf_gmulE hval hval, autOf_oneE]
      have hiff := (orderOf_eq_prime_iff (x := autOf x) (p := 2)).mp (by rw [hxα]; exact hord)
      have h2 : autOf x * autOf x = 1 := by simpa [pow_two] using hiff.1
      exact h2
    refine ⟨x, ?_, hxα⟩
    rw [invs, List.mem_filter]
    exact ⟨hxPel, by simp [hxne, hself]⟩
  · rintro ⟨x, hx, hxα⟩
    have hxPel : x ∈ Pel := w183finSp44_mem_Pel_of_mem_invs hx
    have hval : validB x = true := Pel_valid x hxPel
    have hxne : x ≠ oneE := w183finSp44_ne_one_of_mem_invs hx
    have hself : gmulE x x = oneE := w183finSp44_gmulE_self_of_mem_invs hx
    refine ⟨?_, ?_⟩
    · rw [← hxα]; exact (mem_Psub_iff (autOf x)).mpr ⟨x, hxPel, rfl⟩
    · rw [← hxα]
      apply orderOf_eq_prime
      · rw [pow_two, ← autOf_gmulE hval hval, hself, autOf_oneE]
      · intro h1
        exact hxne (autOf_inj hval validB_oneE (by rw [h1, autOf_oneE]))

theorem exists_conj_invs (α : MulAut S4) (hα : orderOf α = 2) :
    ∃ (h : MulAut S4) (x : El), x ∈ invs ∧ h * α * h⁻¹ = autOf x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 (Subgroup.zpowers α) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, hα, pow_one])
  obtain ⟨k, -, hk⟩ := W183L34.exists_conj_le_isSylowIn (H := ⊤) (A := Subgroup.zpowers α)
    (P := Psub) le_top hA Psub_sylow
  have hmem : MulAut.conj k α ∈ Psub :=
    hk (Subgroup.mem_map.mpr ⟨α, Subgroup.mem_zpowers α, rfl⟩)
  have hord : orderOf (MulAut.conj k α) = 2 := by
    rw [← hα]
    exact orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective α
  obtain ⟨x, hx, hxaut⟩ := (mem_invs_iff (MulAut.conj k α)).mp ⟨hmem, hord⟩
  exact ⟨k, x, hx, by rw [hxaut, MulAut.conj_apply]⟩

theorem mem_pairsL_iff (p : Nat × Nat) : p ∈ pairsL ↔
    p.1 < p.2 ∧ p.2 < 127 ∧ gmulE invsA[p.1]! invsA[p.2]! = gmulE invsA[p.2]! invsA[p.1]! := by
  have hn127 : n127 = 127 := invs_length
  constructor
  · intro hp
    rw [pairsL] at hp
    obtain ⟨b, -, hpb⟩ := List.mem_flatMap.mp hp
    obtain ⟨h12, h2, hcomm⟩ := w183finSp44_mem_pairsFrom_imp hpb
    exact ⟨h12, by rwa [← hn127], hcomm⟩
  · rintro ⟨h12, h2, hcomm⟩
    have h2n : p.2 < n127 := by rwa [hn127]
    obtain ⟨b, hb, h1lo, h1hi⟩ :=
      w183finSp44_pairBlocks_cover (lt_trans h12 h2)
    rw [pairsL]
    exact List.mem_flatMap.mpr ⟨b, hb, w183finSp44_mem_pairsFrom_of h1lo h1hi h12 h2n hcomm⟩

theorem mem_kleinSub_iff {p : Nat × Nat} (hp : p ∈ pairsL) (α : MulAut S4) :
    α ∈ kleinSub invsA[p.1]! invsA[p.2]! ↔
      ∃ x ∈ klein invsA[p.1]! invsA[p.2]!, autOf x = α := by
  obtain ⟨h12, h2, hcomm⟩ := (mem_pairsL_iff p).mp hp
  have hn127 : n127 = 127 := invs_length
  have h2n : p.2 < n127 := by rwa [hn127]
  have h1n : p.1 < n127 := lt_trans h12 h2n
  have hva : validB invsA[p.1]! = true := w183finSp44_valid_invsA h1n
  have hvb : validB invsA[p.2]! = true := w183finSp44_valid_invsA h2n
  have ha : autOf invsA[p.1]! * autOf invsA[p.1]! = 1 := by
    rw [← autOf_gmulE hva hva, w183finSp44_gmulE_self_of_mem_invs
      (w183finSp44_invsA_mem h1n), autOf_oneE]
  have hb : autOf invsA[p.2]! * autOf invsA[p.2]! = 1 := by
    rw [← autOf_gmulE hvb hvb, w183finSp44_gmulE_self_of_mem_invs
      (w183finSp44_invsA_mem h2n), autOf_oneE]
  have hab : autOf invsA[p.1]! * autOf invsA[p.2]! =
      autOf invsA[p.2]! * autOf invsA[p.1]! := by
    rw [← autOf_gmulE hva hvb, ← autOf_gmulE hvb hva, hcomm]
  exact w183finSp44_mem_kleinSub_aux (invsA[p.1]!) (invsA[p.2]!) α hva hvb ha hb hab

theorem card_isElemAbelian_kleinSub {p : Nat × Nat} (hp : p ∈ pairsL) :
    Nat.card (kleinSub invsA[p.1]! invsA[p.2]!) = 4 ∧
      IsElemAbelian 2 (kleinSub invsA[p.1]! invsA[p.2]!) := by
  obtain ⟨h12, h2, hcomm⟩ := (mem_pairsL_iff p).mp hp
  have hn127 : n127 = 127 := invs_length
  have h2n : p.2 < n127 := by rwa [hn127]
  have h1n : p.1 < n127 := lt_trans h12 h2n
  have hva : validB invsA[p.1]! = true := w183finSp44_valid_invsA h1n
  have hvb : validB invsA[p.2]! = true := w183finSp44_valid_invsA h2n
  have hne : invsA[p.1]! ≠ invsA[p.2]! := w183finSp44_invsA_ne h1n h2n h12
  have ha : autOf invsA[p.1]! * autOf invsA[p.1]! = 1 := by
    rw [← autOf_gmulE hva hva, w183finSp44_gmulE_self_of_mem_invs
      (w183finSp44_invsA_mem h1n), autOf_oneE]
  have hb : autOf invsA[p.2]! * autOf invsA[p.2]! = 1 := by
    rw [← autOf_gmulE hvb hvb, w183finSp44_gmulE_self_of_mem_invs
      (w183finSp44_invsA_mem h2n), autOf_oneE]
  have hab : autOf invsA[p.1]! * autOf invsA[p.2]! =
      autOf invsA[p.2]! * autOf invsA[p.1]! := by
    rw [← autOf_gmulE hva hvb, ← autOf_gmulE hvb hva, hcomm]
  have ha1 : autOf invsA[p.1]! ≠ 1 := by
    intro h
    exact w183finSp44_invsA_ne_one h1n (autOf_inj hva validB_oneE (by rw [h, autOf_oneE]))
  have hb1 : autOf invsA[p.2]! ≠ 1 := by
    intro h
    exact w183finSp44_invsA_ne_one h2n (autOf_inj hvb validB_oneE (by rw [h, autOf_oneE]))
  have hneAut : autOf invsA[p.1]! ≠ autOf invsA[p.2]! :=
    fun h => hne (autOf_inj hva hvb h)
  constructor
  · rw [kleinSub, w183finSp44_closure_pair_eq ha hb hab]
    exact w183finSp44_card_pairSub ha hb hab ha1 hb1 hneAut
  · rw [kleinSub]
    exact w183finSp44_isElemAbelian_closure_pair ha hb hab

theorem exists_conj_klein (A : Subgroup (MulAut S4)) (hel : IsElemAbelian 2 A)
    (hc : Nat.card A = 4) :
    ∃ (h : MulAut S4) (p : Nat × Nat), p ∈ pairsL ∧
      autConj h A = kleinSub invsA[p.1]! invsA[p.2]! := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut S4) :=
    Finite.of_injective (fun f : MulAut S4 => (f : S4 → S4))
      (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨k, -, hk⟩ := W183L34.exists_conj_le_isSylowIn (H := ⊤) (A := A) (P := Psub)
    le_top hel.isPGroup Psub_sylow
  have hA'el : IsElemAbelian 2 (autConj k A) := hel.map (MulAut.conj k).toMonoidHom
  have hA'card : Nat.card (autConj k A) = 4 := by
    rw [autConj, Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hc
  haveI : Fintype (autConj k A) := Fintype.ofFinite _
  have hcardF : Fintype.card (autConj k A) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hA'card
  have hscard : (Finset.univ.erase (1 : autConj k A)).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, hcardF]
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < (Finset.univ.erase (1 : autConj k A)).card by
      rw [hscard]; norm_num)
  have ha1 : a ≠ 1 := (Finset.mem_erase.mp ha).1
  have hb1 : b ≠ 1 := (Finset.mem_erase.mp hb).1
  have hαne : (a : MulAut S4) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hβne : (b : MulAut S4) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hαβ : (a : MulAut S4) ≠ (b : MulAut S4) := fun h => hab (Subtype.ext h)
  have hαord : orderOf (a : MulAut S4) = 2 := by
    apply orderOf_eq_prime
    · simpa [pow_two] using hA'el.2 (a : MulAut S4) a.2
    · exact hαne
  have hβord : orderOf (b : MulAut S4) = 2 := by
    apply orderOf_eq_prime
    · simpa [pow_two] using hA'el.2 (b : MulAut S4) b.2
    · exact hβne
  obtain ⟨x, hx, hxaut⟩ := (mem_invs_iff (a : MulAut S4)).mp ⟨hk a.2, hαord⟩
  obtain ⟨y, hy, hyaut⟩ := (mem_invs_iff (b : MulAut S4)).mp ⟨hk b.2, hβord⟩
  have hxy : x ≠ y := by
    intro h
    exact hαβ (by rw [← hxaut, ← hyaut, h])
  have hvx : validB x = true := Pel_valid x (w183finSp44_mem_Pel_of_mem_invs hx)
  have hvy : validB y = true := Pel_valid y (w183finSp44_mem_Pel_of_mem_invs hy)
  have hcomm : gmulE x y = gmulE y x := by
    apply autOf_inj (validB_gmulE hvx hvy) (validB_gmulE hvy hvx)
    rw [autOf_gmulE hvx hvy, autOf_gmulE hvy hvx, hxaut, hyaut]
    exact hA'el.comm a.2 b.2
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
  have hi_lt : i < invs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hj_lt : j < invs.length := (List.getElem?_eq_some_iff.mp hj).1
  have hix : invsA[i]! = x := by
    rw [invsA, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, hi]
    rfl
  have hjy : invsA[j]! = y := by
    rw [invsA, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, hj]
    rfl
  have hij : i ≠ j := by
    intro h
    exact hxy (by rw [← hix, ← hjy, h])
  have hle : kleinSub x y ≤ autConj k A := by
    rw [kleinSub, Subgroup.closure_le]
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [hxaut]; exact a.2
    · rw [hyaut]; exact b.2
  by_cases hij' : i < j
  · have hpij : (i, j) ∈ pairsL := by
      rw [mem_pairsL_iff]
      exact ⟨hij', by rw [← invs_length]; exact hj_lt,
        by rw [hix, hjy]; exact hcomm⟩
    have hcardk : Nat.card (kleinSub invsA[i]! invsA[j]!) = 4 :=
      (card_isElemAbelian_kleinSub hpij).1
    have hkeq : kleinSub invsA[i]! invsA[j]! = autConj k A := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [hix, hjy]; exact hle
      · rw [hcardk, hA'card]
    exact ⟨k, (i, j), hpij, by rw [hkeq]⟩
  · have hji : j < i := by omega
    have hpji : (j, i) ∈ pairsL := by
      rw [mem_pairsL_iff]
      exact ⟨hji, by rw [← invs_length]; exact hi_lt,
        by rw [hjy, hix]; exact hcomm.symm⟩
    have hcardk : Nat.card (kleinSub invsA[j]! invsA[i]!) = 4 :=
      (card_isElemAbelian_kleinSub hpji).1
    have hkeq : kleinSub invsA[j]! invsA[i]! = autConj k A := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [hjy, hix, w183finSp44_kleinSub_comm y x]; exact hle
      · rw [hcardk, hA'card]
    exact ⟨k, (j, i), hpji, by rw [hkeq]⟩

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
