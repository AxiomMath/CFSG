module

public import CFSG.Permutation.TranspositionCentralizer

public section

namespace CFSG.Permutation.FivePairs

open Equiv

@[expose] def pairFst (k : Fin 5) : Fin 11 := ⟨2 * k.val, by have := k.isLt; omega⟩

@[expose] def pairSnd (k : Fin 5) : Fin 11 := ⟨2 * k.val + 1, by have := k.isLt; omega⟩

@[expose] def pairSwap (k : Fin 5) : Equiv.Perm (Fin 11) := Equiv.swap (pairFst k) (pairSnd k)

@[expose] def pairGroup : Subgroup (Equiv.Perm (Fin 11)) := Subgroup.closure (Set.range pairSwap)

@[expose] def pairParabolic (k : Fin 5) : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure (insert (Equiv.swap (pairFst k) 10) (Set.range pairSwap))

private abbrev triple (k : Fin 5) : Set (Fin 11) := {pairFst k, pairSnd k, 10}

private abbrev sk (k : Fin 5) : Subgroup (Equiv.Perm (Fin 11)) :=
  fixingSubgroup (Equiv.Perm (Fin 11)) (triple k)ᶜ

private abbrev bk (k : Fin 5) : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k})

private lemma pairFst_ne_pairSnd (k : Fin 5) : pairFst k ≠ pairSnd k := by
  intro h
  have hv := congrArg Fin.val h
  simp [pairFst, pairSnd] at hv

private lemma pairFst_ne_ten (k : Fin 5) : pairFst k ≠ 10 := by
  intro h
  have hv := congrArg Fin.val h
  simp [pairFst] at hv
  have := k.isLt
  omega

private lemma pairSnd_ne_ten (k : Fin 5) : pairSnd k ≠ 10 := by
  intro h
  have hv := congrArg Fin.val h
  simp [pairSnd] at hv
  have := k.isLt
  omega

private lemma pair_points_ne_of_ne {k j : Fin 5} (h : k ≠ j) :
    pairFst k ≠ pairFst j ∧ pairFst k ≠ pairSnd j ∧
      pairSnd k ≠ pairFst j ∧ pairSnd k ≠ pairSnd j := by
  fin_cases k <;> fin_cases j <;> simp_all [pairFst, pairSnd]

private lemma pairSwap_apply_fst (k : Fin 5) : pairSwap k (pairFst k) = pairSnd k :=
  Equiv.swap_apply_left _ _

private lemma pairSwap_apply_snd (k : Fin 5) : pairSwap k (pairSnd k) = pairFst k :=
  Equiv.swap_apply_right _ _

private lemma pairSwap_apply_of_ne {k : Fin 5} {x : Fin 11}
    (hx : x ≠ pairFst k) (hy : x ≠ pairSnd k) : pairSwap k x = x :=
  Equiv.swap_apply_of_ne_of_ne hx hy

private lemma pairSwap_mul_self (k : Fin 5) : pairSwap k * pairSwap k = 1 :=
  Equiv.swap_mul_self _ _

private lemma pairSwap_fixes_ten (k : Fin 5) : pairSwap k 10 = 10 :=
  pairSwap_apply_of_ne (pairFst_ne_ten k).symm (pairSnd_ne_ten k).symm

private lemma pairSwap_commute_of_ne {k j : Fin 5} (h : k ≠ j) :
    Commute (pairSwap k) (pairSwap j) := by
  refine Equiv.Perm.Disjoint.commute ?_
  intro x
  by_cases hx : x = pairFst k ∨ x = pairSnd k
  · right
    rcases hx with rfl | rfl
    · exact pairSwap_apply_of_ne (pair_points_ne_of_ne h).1 (pair_points_ne_of_ne h).2.1
    · exact pairSwap_apply_of_ne (pair_points_ne_of_ne h).2.2.1 (pair_points_ne_of_ne h).2.2.2
  · left
    push Not at hx
    exact pairSwap_apply_of_ne hx.1 hx.2

private lemma pairwise_commute_pairSwap : (Set.range pairSwap).Pairwise Commute := by
  rintro a ⟨k, rfl⟩ b ⟨j, rfl⟩ hab
  exact pairSwap_commute_of_ne (fun h => hab (by rw [h]))

private lemma pairSwap_mem_pairGroup (k : Fin 5) : pairSwap k ∈ pairGroup :=
  Subgroup.subset_closure ⟨k, rfl⟩

private lemma pairSwap_mem_pairParabolic (k j : Fin 5) : pairSwap j ∈ pairParabolic k :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨j, rfl⟩)

private lemma extra_mem_pairParabolic (k : Fin 5) :
    Equiv.swap (pairFst k) 10 ∈ pairParabolic k :=
  Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))

theorem pairGroup_le_pairParabolic (k : Fin 5) : pairGroup ≤ pairParabolic k :=
  Subgroup.closure_mono (Set.subset_insert _ _)

private lemma pairGroup_le_stabilizer_ten :
    pairGroup ≤ MulAction.stabilizer (Equiv.Perm (Fin 11)) (10 : Fin 11) := by
  rw [pairGroup, Subgroup.closure_le]
  rintro g ⟨k, rfl⟩
  exact MulAction.mem_stabilizer_iff.mpr (by simpa using pairSwap_fixes_ten k)

private lemma pairSwap_mem_sk (k : Fin 5) :
    pairSwap k ∈
      fixingSubgroup (Equiv.Perm (Fin 11)) ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)) := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x ≠ pairFst k ∧ x ≠ pairSnd k ∧ x ≠ (10 : Fin 11) := by
    simpa using hx
  show pairSwap k x = x
  exact pairSwap_apply_of_ne hx'.1 hx'.2.1

private lemma extra_mem_sk (k : Fin 5) :
    Equiv.swap (pairFst k) 10 ∈
      fixingSubgroup (Equiv.Perm (Fin 11)) ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)) := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x ≠ pairFst k ∧ x ≠ pairSnd k ∧ x ≠ (10 : Fin 11) := by
    simpa using hx
  show Equiv.swap (pairFst k) 10 x = x
  exact Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2.2

private lemma pairSwap_other_mem_bk {k j : Fin 5} (h : j ≠ k) :
    pairSwap j ∈ Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k}) :=
  Subgroup.subset_closure ⟨j, h, rfl⟩

private lemma pairwise_commute_pairSwap_other (k : Fin 5) :
    (pairSwap '' {j : Fin 5 | j ≠ k}).Pairwise Commute := by
  rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩ hab
  exact pairSwap_commute_of_ne (fun h => hab (by rw [h]))

private lemma bk_le_pairParabolic (k : Fin 5) :
    Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k}) ≤ pairParabolic k := by
  rw [Subgroup.closure_le]
  rintro g ⟨j, hj, rfl⟩
  exact pairSwap_mem_pairParabolic k j

private lemma pairGroup_eq_zpowers_sup_bk (k : Fin 5) :
    pairGroup = Subgroup.zpowers (pairSwap k) ⊔
      Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k}) := by
  rw [pairGroup]
  have hset : Set.range pairSwap =
      insert (pairSwap k) (pairSwap '' {j : Fin 5 | j ≠ k}) := by
    ext g
    constructor
    · rintro ⟨j, rfl⟩
      by_cases h : j = k
      · subst h
        exact Or.inl rfl
      · exact Set.mem_insert_of_mem _ ⟨j, h, rfl⟩
    · intro hg
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact ⟨k, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := hg
        exact ⟨j, rfl⟩
  rw [hset, Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure]

private lemma fixingSubgroup_triple_le_closure_three_swaps {a b c : Fin 11}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    fixingSubgroup (Equiv.Perm (Fin 11)) ({a, b, c}ᶜ : Set (Fin 11)) ≤
      Subgroup.closure ({Equiv.swap a b, Equiv.swap a c, Equiv.swap b c} :
        Set (Equiv.Perm (Fin 11))) := by
  let s : Set (Fin 11) := {a, b, c}
  have hfix : fixingSubgroup (Equiv.Perm (Fin 11)) sᶜ =
      (Equiv.Perm.ofSubtype (p := fun x => x ∈ s)).range :=
    CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype s
  rw [hfix]
  rw [MonoidHom.range_eq_map]
  have htop : Subgroup.closure {σ : Equiv.Perm s | σ.IsSwap} = ⊤ :=
    Equiv.Perm.closure_isSwap
  rw [← htop, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  rw [Equiv.Perm.ofSubtype_swap_eq]
  refine Subgroup.subset_closure ?_
  have hxT : x = ⟨a, by simp [s]⟩ ∨ x = ⟨b, by simp [s]⟩ ∨ x = ⟨c, by simp [s]⟩ := by
    have h := x.2
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have hyT : y = ⟨a, by simp [s]⟩ ∨ y = ⟨b, by simp [s]⟩ ∨ y = ⟨c, by simp [s]⟩ := by
    have h := y.2
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  rcases hxT with rfl | rfl | rfl <;> rcases hyT with rfl | rfl | rfl <;>
    simp_all [Equiv.swap_comm]

private lemma sk_le_pairParabolic (k : Fin 5) :
    fixingSubgroup (Equiv.Perm (Fin 11)) ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)) ≤
      pairParabolic k := by
  refine (fixingSubgroup_triple_le_closure_three_swaps (pairFst_ne_pairSnd k)
    (pairFst_ne_ten k) (pairSnd_ne_ten k)).trans ?_
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact pairSwap_mem_pairParabolic k k
  · exact Subgroup.subset_closure (Or.inl rfl)
  · have hconj : Equiv.swap (pairFst k) (pairSnd k) * Equiv.swap (pairFst k) 10 *
        Equiv.swap (pairFst k) (pairSnd k) = Equiv.swap (pairSnd k) 10 := by
      simpa [Equiv.swap_comm] using
        Equiv.swap_mul_swap_mul_swap (x := 10) (y := pairFst k) (z := pairSnd k)
          (Ne.symm (pairFst_ne_ten k)) (Ne.symm (pairSnd_ne_ten k))
    rw [← hconj]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (pairSwap_mem_pairParabolic k k)
        (Subgroup.subset_closure (Or.inl rfl)))
      (pairSwap_mem_pairParabolic k k)

private lemma pairParabolic_eq_sk_sup_bk (k : Fin 5) :
    pairParabolic k = fixingSubgroup (Equiv.Perm (Fin 11))
        ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)) ⊔
      Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k}) := by
  apply le_antisymm
  · rw [pairParabolic, Subgroup.closure_le]
    intro g hg
    rw [Set.mem_insert_iff] at hg
    rcases hg with rfl | hg
    · exact Subgroup.mem_sup_left (extra_mem_sk k)
    · obtain ⟨j, rfl⟩ := hg
      by_cases hjk : j = k
      · subst j
        exact Subgroup.mem_sup_left (pairSwap_mem_sk k)
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hjk, rfl⟩)
  · exact sup_le (sk_le_pairParabolic k) (bk_le_pairParabolic k)

private lemma bk_le_fixingSubgroup_triple (k : Fin 5) :
    Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k}) ≤
      fixingSubgroup (Equiv.Perm (Fin 11)) ({pairFst k, pairSnd k, 10} : Set (Fin 11)) := by
  rw [Subgroup.closure_le]
  rintro g ⟨j, hj, rfl⟩
  refine (mem_fixingSubgroup_iff (Equiv.Perm (Fin 11))).mpr ?_
  intro x hx
  have hx' : x = pairFst k ∨ x = pairSnd k ∨ x = (10 : Fin 11) := by
    simpa using hx
  rcases hx' with rfl | rfl | rfl
  · show pairSwap j (pairFst k) = pairFst k
    exact pairSwap_apply_of_ne (pair_points_ne_of_ne (Ne.symm hj)).1
      (pair_points_ne_of_ne (Ne.symm hj)).2.1
  · show pairSwap j (pairSnd k) = pairSnd k
    exact pairSwap_apply_of_ne (pair_points_ne_of_ne (Ne.symm hj)).2.2.1
      (pair_points_ne_of_ne (Ne.symm hj)).2.2.2
  · show pairSwap j (10 : Fin 11) = 10
    exact pairSwap_fixes_ten j

private lemma commute_of_mem_sk_of_mem_bk {k : Fin 5} {s b : Equiv.Perm (Fin 11)}
    (hs : s ∈ fixingSubgroup (Equiv.Perm (Fin 11))
      ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)))
    (hb : b ∈ Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k})) :
    Commute s b := by
  refine Equiv.Perm.Disjoint.commute ?_
  intro x
  by_cases hx : x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))
  · right
    have hbfix := bk_le_fixingSubgroup_triple k hb
    have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin 11))).mp hbfix x hx
    simpa using this
  · left
    have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin 11))).mp hs x (by simpa using hx)
    simpa using this

private lemma sk_apply_mem_triple {k : Fin 5} {s : Equiv.Perm (Fin 11)}
    (hs : s ∈ fixingSubgroup (Equiv.Perm (Fin 11))
      ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11))) {x : Fin 11}
    (hx : x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))) :
    s x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11)) := by
  by_contra h
  have hfix : s (s x) = s x := by
    have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin 11))).mp hs (s x) (by simpa using h)
    simpa using this
  have hx' : s x = x := s.injective hfix
  exact h (by rwa [← hx'] at hx)

private lemma mem_zpowers_pairSwap_of_mem_sk_of_apply_ten {k : Fin 5}
    {s : Equiv.Perm (Fin 11)}
    (hs : s ∈ fixingSubgroup (Equiv.Perm (Fin 11))
      ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)))
    (hs10 : s 10 = 10) : s ∈ Subgroup.zpowers (pairSwap k) := by
  have hsa_mem : s (pairFst k) ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11)) :=
    sk_apply_mem_triple hs (by simp)
  have hsb_mem : s (pairSnd k) ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11)) :=
    sk_apply_mem_triple hs (by simp)
  have hsa_ne10 : s (pairFst k) ≠ 10 := by
    intro h
    exact pairFst_ne_ten k (s.injective (h.trans hs10.symm))
  have hsb_ne10 : s (pairSnd k) ≠ 10 := by
    intro h
    exact pairSnd_ne_ten k (s.injective (h.trans hs10.symm))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsa_mem hsb_mem
  rcases hsa_mem with hsa | hsa | hsa
  · rcases hsb_mem with hsb | hsb | hsb
    · exfalso
      exact pairFst_ne_pairSnd k (s.injective (hsa.trans hsb.symm))
    · have hs_eq : s = 1 := by
        ext x
        by_cases hx : x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · rw [hsa] <;> simp
          · rw [hsb] <;> simp
          · rw [hs10] <;> simp
        · have hsx : s x = x := by
            have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin 11))).mp hs x (by simpa using hx)
            simpa using this
          rw [hsx] <;> simp
      rw [hs_eq]
      exact Subgroup.one_mem _
    · exact absurd hsb hsb_ne10
  · rcases hsb_mem with hsb | hsb | hsb
    · have hs_eq : s = pairSwap k := by
        ext x
        by_cases hx : x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · rw [hsa, pairSwap_apply_fst] <;> simp
          · rw [hsb, pairSwap_apply_snd] <;> simp
          · rw [hs10, pairSwap_fixes_ten] <;> simp
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
          have hsx : s x = x := by
            have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin 11))).mp hs x (by simpa using hx)
            simpa using this
          rw [hsx, pairSwap_apply_of_ne hx.1 hx.2.1]
      rw [hs_eq]
      exact Subgroup.mem_zpowers _
    · exfalso
      exact pairFst_ne_pairSnd k (s.injective (hsa.trans hsb.symm))
    · exact absurd hsb hsb_ne10
  · exact absurd hsa hsa_ne10

private lemma pairSwap_other_mem_normalizer_sk {k j : Fin 5} (h : j ≠ k) :
    pairSwap j ∈ Subgroup.normalizer
      (fixingSubgroup (Equiv.Perm (Fin 11))
        ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)) :
        Set (Equiv.Perm (Fin 11))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  have hconj_of_mem {x : Equiv.Perm (Fin 11)}
      (hx : x ∈ fixingSubgroup (Equiv.Perm (Fin 11))
        ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11))) :
      pairSwap j * x * (pairSwap j)⁻¹ = x := by
    have hc : Commute (pairSwap j) x :=
      (commute_of_mem_sk_of_mem_bk hx (pairSwap_other_mem_bk h)).symm
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hs
    rw [hconj_of_mem hs]
    exact hs
  · intro hs
    have hEq : pairSwap j * (pairSwap j * s * (pairSwap j)⁻¹) * (pairSwap j)⁻¹ = s := by
      have hginv : (pairSwap j)⁻¹ = pairSwap j := by
        rw [pairSwap]
        exact Equiv.swap_inv _ _
      rw [hginv]
      have hgroup : pairSwap j * (pairSwap j * s * pairSwap j) * pairSwap j =
          (pairSwap j * pairSwap j) * s * (pairSwap j * pairSwap j) := by group
      rw [hgroup, pairSwap_mul_self]
      group
    have hconj := hconj_of_mem hs
    rw [hconj] at hEq
    rw [← hEq]
    exact hs

private lemma pairParabolic_le_normalizer_sk (k : Fin 5) :
    pairParabolic k ≤ Subgroup.normalizer
      (fixingSubgroup (Equiv.Perm (Fin 11))
        ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11)) :
        Set (Equiv.Perm (Fin 11))) := by
  rw [pairParabolic, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_insert_iff] at hg
  rcases hg with rfl | hg
  · exact Subgroup.le_normalizer (extra_mem_sk k)
  · obtain ⟨j, rfl⟩ := hg
    by_cases hjk : j = k
    · subst j
      exact Subgroup.le_normalizer (pairSwap_mem_sk k)
    · exact pairSwap_other_mem_normalizer_sk hjk

private lemma sk_subgroupOf_pairParabolic_normal (k : Fin 5) :
    ((fixingSubgroup (Equiv.Perm (Fin 11))
      ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11))).subgroupOf (pairParabolic k)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (sk_le_pairParabolic k)]
  intro h g hh hg
  exact (Subgroup.mem_normalizer_iff.mp (pairParabolic_le_normalizer_sk k hg) h).mp hh

private lemma bk_isMulCommutative (k : Fin 5) :
    IsMulCommutative (Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k})) :=
  Subgroup.isMulCommutative_closure (pairwise_commute_pairSwap_other k)

private lemma bk_isSolvable (k : Fin 5) :
    IsSolvable (Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k})) := by
  haveI : IsMulCommutative (Subgroup.closure (pairSwap '' {j : Fin 5 | j ≠ k})) :=
    bk_isMulCommutative k
  exact Group.instIsSolvableOfIsMulCommutative

private lemma sk_isSolvable (k : Fin 5) :
    IsSolvable (fixingSubgroup (Equiv.Perm (Fin 11))
      ({pairFst k, pairSnd k, 10}ᶜ : Set (Fin 11))) :=
  CFSG.Permutation.TranspositionCentralizer.isSolvable_fixingSubgroup_compl_triple
    (pairFst k) (pairSnd k) 10

theorem isSolvable_pairParabolic (k : Fin 5) : IsSolvable (pairParabolic k) := by
  classical
  let P := pairParabolic k
  have hP : P = sk k ⊔ bk k := pairParabolic_eq_sk_sup_bk k
  have hSP : sk k ≤ P := by rw [hP]; exact le_sup_left
  have hBP : bk k ≤ P := by rw [hP]; exact le_sup_right
  have hSNormal : ((sk k).subgroupOf P).Normal := sk_subgroupOf_pairParabolic_normal k
  have hSkSol : IsSolvable (sk k) := sk_isSolvable k
  have hSkSubSol : IsSolvable ((sk k).subgroupOf P) := by
    let e : (sk k).subgroupOf P ≃* sk k := Subgroup.subgroupOfEquivOfLe hSP
    exact @Group.isSolvable_of_surjective (sk k) ((sk k).subgroupOf P) _ _
      e.symm.toMonoidHom (MulEquiv.surjective e.symm) hSkSol
  have hBkSol : IsSolvable (bk k) := bk_isSolvable k
  let f : bk k →* P ⧸ ((sk k).subgroupOf P) :=
    (QuotientGroup.mk' ((sk k).subgroupOf P)).comp (Subgroup.inclusion hBP)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((sk k).subgroupOf P) q
    have hsup : (sk k).subgroupOf P ⊔ (bk k).subgroupOf P = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hSP hBP, ← hP, Subgroup.subgroupOf_self]
    have hx : x ∈ (sk k).subgroupOf P ⊔ (bk k).subgroupOf P := by
      rw [hsup]
      exact Subgroup.mem_top x
    obtain ⟨s, hs, b, hb, hsb⟩ := (Subgroup.mem_sup_of_normal_left).mp hx
    have hsKer : QuotientGroup.mk' ((sk k).subgroupOf P) s = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hs
    refine ⟨⟨b, Subgroup.mem_subgroupOf.mp hb⟩, ?_⟩
    change QuotientGroup.mk' ((sk k).subgroupOf P) b =
      QuotientGroup.mk' ((sk k).subgroupOf P) x
    rw [← hsb, map_mul, hsKer, one_mul]
  have hQuotSol : IsSolvable (P ⧸ ((sk k).subgroupOf P)) :=
    @Group.isSolvable_of_surjective (bk k) (P ⧸ ((sk k).subgroupOf P)) _ _ f hf hBkSol
  exact @Group.isSolvable_of_subgroup_quotient P _ ((sk k).subgroupOf P) hSNormal hSkSubSol hQuotSol

private lemma pairGroup_square_eq_one : ∀ g ∈ pairGroup, g * g = 1 := by
  intro g hg
  haveI : IsMulCommutative pairGroup :=
    Subgroup.isMulCommutative_closure pairwise_commute_pairSwap
  refine Subgroup.closure_induction (p := fun x _ => x * x = 1) ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact pairSwap_mul_self k
  · simp
  · intro x y hx hy ihx ihy
    have hxy : x * y = y * x :=
      Subgroup.mul_comm_of_mem_isMulCommutative pairGroup hx hy
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, mul_one]
  · intro x hx ih
    have hxinv : x⁻¹ = x := mul_eq_one_iff_inv_eq.mp ih
    rw [hxinv]
    exact ih

theorem isPGroup_pairGroup : IsPGroup 2 pairGroup := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using pairGroup_square_eq_one g g.2

private lemma generator_maps_triple (k : Fin 5) {a : Equiv.Perm (Fin 11)}
    (ha : a ∈ insert (Equiv.swap (pairFst k) 10) (Set.range pairSwap))
    {x : Fin 11} (hx : x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))) :
    a x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11)) := by
  rw [Set.mem_insert_iff] at ha
  rcases ha with rfl | ha
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · rw [Equiv.swap_apply_left]; simp
    · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (pairFst_ne_pairSnd k)) (pairSnd_ne_ten k)]
      simp
    · rw [Equiv.swap_apply_right]; simp
  · obtain ⟨j, rfl⟩ := ha
    by_cases hjk : j = k
    · subst j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl <;>
        simp [pairSwap_apply_fst, pairSwap_apply_snd, pairSwap_fixes_ten]
    · have hkj : k ≠ j := Ne.symm hjk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · rw [pairSwap_apply_of_ne (pair_points_ne_of_ne hkj).1 (pair_points_ne_of_ne hkj).2.1]
        simp
      · rw [pairSwap_apply_of_ne (pair_points_ne_of_ne hkj).2.2.1 (pair_points_ne_of_ne hkj).2.2.2]
        simp
      · rw [pairSwap_fixes_ten]
        simp

private lemma pairParabolic_apply_mem_triple (k : Fin 5) {g : Equiv.Perm (Fin 11)}
    (hg : g ∈ pairParabolic k) {x : Fin 11}
    (hx : x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))) :
    g x ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11)) := by
  refine Subgroup.closure_induction_left ?one ?mul ?inv hg
  · simpa using hx
  · intro a ha y hy ih
    change a (y x) ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))
    exact generator_maps_triple k ha ih
  · intro a ha y hy ih
    have hainv : a⁻¹ = a := by
      rw [Set.mem_insert_iff] at ha
      rcases ha with rfl | ha
      · exact Equiv.swap_inv _ _
      · obtain ⟨j, rfl⟩ := ha
        exact Equiv.swap_inv _ _
    change a⁻¹ (y x) ∈ ({pairFst k, pairSnd k, 10} : Set (Fin 11))
    rw [hainv]
    exact generator_maps_triple k ha ih

private lemma orbit_ten_pairParabolic (k : Fin 5) :
    MulAction.orbit (pairParabolic k) (10 : Fin 11) =
      ({pairFst k, pairSnd k, 10} : Set (Fin 11)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
    rw [← hg]
    exact pairParabolic_apply_mem_triple k g.2 (by simp)
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact MulAction.mem_orbit_iff.mpr
        ⟨⟨Equiv.swap (pairFst k) 10, extra_mem_pairParabolic k⟩, by simp⟩
    · exact MulAction.mem_orbit_iff.mpr
        ⟨⟨pairSwap k * Equiv.swap (pairFst k) 10,
          Subgroup.mul_mem (pairParabolic k) (pairSwap_mem_pairParabolic k k)
            (extra_mem_pairParabolic k)⟩,
          by simp [Subgroup.coe_mul, Subgroup.smul_def, Equiv.Perm.mul_apply, pairSwap_apply_fst]⟩
    · exact MulAction.mem_orbit_iff.mpr ⟨1, by simp⟩

private lemma ncard_triple (k : Fin 5) :
    ({pairFst k, pairSnd k, 10} : Set (Fin 11)).ncard = 3 := by
  have ha : pairFst k ∉ ({pairSnd k, 10} : Set (Fin 11)) := by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    push Not
    exact ⟨pairFst_ne_pairSnd k, pairFst_ne_ten k⟩
  change (insert (pairFst k) ({pairSnd k, 10} : Set (Fin 11))).ncard = 3
  rw [Set.ncard_insert_of_notMem ha, Set.ncard_pair (pairSnd_ne_ten k)]

private lemma pairParabolic_inf_stabilizer_ten (k : Fin 5) :
    pairParabolic k ⊓ MulAction.stabilizer (Equiv.Perm (Fin 11)) (10 : Fin 11) = pairGroup := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgP, hg10⟩ := Subgroup.mem_inf.mp hg
    have hg10' : g 10 = 10 := by
      have := (MulAction.mem_stabilizer_iff.mp hg10)
      simpa using this
    let P := pairParabolic k
    have hP : P = sk k ⊔ bk k := pairParabolic_eq_sk_sup_bk k
    have hSP : sk k ≤ P := by rw [hP]; exact le_sup_left
    have hBP : bk k ≤ P := by rw [hP]; exact le_sup_right
    have hSNormal : ((sk k).subgroupOf P).Normal := sk_subgroupOf_pairParabolic_normal k
    let gp : P := ⟨g, hgP⟩
    have hsup : (sk k).subgroupOf P ⊔ (bk k).subgroupOf P = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hSP hBP, ← hP, Subgroup.subgroupOf_self]
    have hx : gp ∈ (sk k).subgroupOf P ⊔ (bk k).subgroupOf P := by
      rw [hsup]
      exact Subgroup.mem_top gp
    obtain ⟨sp, hsp, bp, hbp, hspbp⟩ := (Subgroup.mem_sup_of_normal_left).mp hx
    have hs : (sp : Equiv.Perm (Fin 11)) ∈ sk k := Subgroup.mem_subgroupOf.mp hsp
    have hb : (bp : Equiv.Perm (Fin 11)) ∈ bk k := Subgroup.mem_subgroupOf.mp hbp
    have hb10 : (bp : Equiv.Perm (Fin 11)) 10 = 10 := by
      have hbfix := bk_le_fixingSubgroup_triple k hb
      have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin 11))).mp hbfix 10 (by simp)
      simpa using this
    have hsp10 : (sp : Equiv.Perm (Fin 11)) 10 = 10 := by
      have h := congrArg (fun q : P => (q : Equiv.Perm (Fin 11)) 10) hspbp
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at h
      rw [hb10] at h
      simpa [gp, hg10'] using h
    have hszp : (sp : Equiv.Perm (Fin 11)) ∈ Subgroup.zpowers (pairSwap k) :=
      mem_zpowers_pairSwap_of_mem_sk_of_apply_ten hs hsp10
    have hg_eq : (sp : Equiv.Perm (Fin 11)) * (bp : Equiv.Perm (Fin 11)) = g := by
      have h := congrArg (fun q : P => (q : Equiv.Perm (Fin 11))) hspbp
      simpa [Subgroup.coe_mul, gp] using h
    rw [pairGroup_eq_zpowers_sup_bk k, ← hg_eq]
    exact Subgroup.mul_mem_sup hszp hb
  · intro g hg
    exact Subgroup.mem_inf.mpr ⟨pairGroup_le_pairParabolic k hg, pairGroup_le_stabilizer_ten hg⟩

private lemma pairGroup_subgroupOf_pairParabolic_eq_stabilizer (k : Fin 5) :
    pairGroup.subgroupOf (pairParabolic k) =
      MulAction.stabilizer (pairParabolic k) (10 : Fin 11) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hx' : (x : Equiv.Perm (Fin 11)) ∈
        pairParabolic k ⊓ MulAction.stabilizer (Equiv.Perm (Fin 11)) (10 : Fin 11) := by
      rw [pairParabolic_inf_stabilizer_ten k]
      exact hx
    exact (Subgroup.mem_inf.mp hx').2
  · intro hx
    have hx' : (x : Equiv.Perm (Fin 11)) ∈
        MulAction.stabilizer (Equiv.Perm (Fin 11)) (10 : Fin 11) := by
      have := (MulAction.mem_stabilizer_iff.mp hx)
      simpa [Subgroup.smul_def] using this
    have hmem : (x : Equiv.Perm (Fin 11)) ∈
        pairParabolic k ⊓ MulAction.stabilizer (Equiv.Perm (Fin 11)) (10 : Fin 11) :=
      Subgroup.mem_inf.mpr ⟨x.2, hx'⟩
    rwa [pairParabolic_inf_stabilizer_ten k] at hmem

theorem relIndex_pairGroup_pairParabolic (k : Fin 5) :
    pairGroup.relIndex (pairParabolic k) = 3 := by
  have hle : pairGroup ≤ pairParabolic k := pairGroup_le_pairParabolic k
  have hidx : pairGroup.relIndex (pairParabolic k) =
      (pairGroup.subgroupOf (pairParabolic k)).index := by
    simpa [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] using
      (Subgroup.relIndex_subgroupOf (H := pairGroup) (K := pairParabolic k)
        (L := pairParabolic k) (le_refl _)).symm
  rw [hidx, pairGroup_subgroupOf_pairParabolic_eq_stabilizer,
    MulAction.index_stabilizer, orbit_ten_pairParabolic, ncard_triple]

private def blockSwap (k j : Fin 5) : Equiv.Perm (Fin 11) :=
  Equiv.swap (pairFst k) (pairFst j) * Equiv.swap (pairSnd k) (pairSnd j)

private lemma blockSwap_conj_pairSwap {k j l : Fin 5} (h : j ≠ k) :
    blockSwap k j * pairSwap l * (blockSwap k j)⁻¹ =
      pairSwap (Equiv.swap k j l) := by
  fin_cases k <;> fin_cases j <;> first | exact absurd rfl h | (fin_cases l <;> decide)

private lemma swap_swap_apply (k j l : Fin 5) :
    Equiv.swap k j (Equiv.swap k j l) = l := by
  rw [← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply]

private lemma blockSwap_mem_normalizer {k j : Fin 5} (h : j ≠ k) :
    blockSwap k j ∈ Subgroup.normalizer (pairGroup : Set (Equiv.Perm (Fin 11))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have himage : (⇑(MulAut.conj (blockSwap k j))) '' Set.range pairSwap = Set.range pairSwap := by
    ext g
    constructor
    · rintro ⟨x, ⟨l, rfl⟩, hx⟩
      refine ⟨Equiv.swap k j l, ?_⟩
      rw [← hx, MulAut.conj_apply]
      exact (blockSwap_conj_pairSwap h).symm
    · rintro ⟨l, rfl⟩
      refine ⟨pairSwap (Equiv.swap k j l), ⟨Equiv.swap k j l, rfl⟩, ?_⟩
      rw [MulAut.conj_apply, blockSwap_conj_pairSwap h, swap_swap_apply]
  rw [pairGroup, MonoidHom.map_closure]
  change Subgroup.closure (⇑(MulAut.conj (blockSwap k j)) '' Set.range pairSwap) =
    Subgroup.closure (Set.range pairSwap)
  rw [himage]

private lemma exists_pair_eq_of_ne_ten {m : Fin 11} (hm : m ≠ 10) :
    ∃ k : Fin 5, m = pairFst k ∨ m = pairSnd k := by
  fin_cases m
  · exact ⟨0, Or.inl (by decide)⟩
  · exact ⟨0, Or.inr (by decide)⟩
  · exact ⟨1, Or.inl (by decide)⟩
  · exact ⟨1, Or.inr (by decide)⟩
  · exact ⟨2, Or.inl (by decide)⟩
  · exact ⟨2, Or.inr (by decide)⟩
  · exact ⟨3, Or.inl (by decide)⟩
  · exact ⟨3, Or.inr (by decide)⟩
  · exact ⟨4, Or.inl (by decide)⟩
  · exact ⟨4, Or.inr (by decide)⟩
  · exact absurd rfl hm

private lemma blockSwap_conj_extra {k j : Fin 5} (h : j ≠ k) :
    blockSwap k j * Equiv.swap (pairFst k) 10 * (blockSwap k j)⁻¹ =
      Equiv.swap (pairFst j) 10 := by
  fin_cases k <;> fin_cases j <;> first | exact absurd rfl h | decide

private lemma pairSwap_conj_extra (j : Fin 5) :
    pairSwap j * Equiv.swap (pairFst j) 10 * (pairSwap j)⁻¹ =
      Equiv.swap (pairSnd j) 10 := by
  have h := Equiv.swap_mul_swap_mul_swap (x := 10) (y := pairFst j) (z := pairSnd j)
    (Ne.symm (pairFst_ne_ten j)) (Ne.symm (pairSnd_ne_ten j))
  simpa [pairSwap, Equiv.swap_comm, Equiv.swap_inv] using h

theorem normalizer_pairGroup_sup_pairParabolic (k : Fin 5) :
    Subgroup.normalizer (pairGroup : Set (Equiv.Perm (Fin 11))) ⊔ pairParabolic k = ⊤ := by
  let H := Subgroup.normalizer (pairGroup : Set (Equiv.Perm (Fin 11))) ⊔ pairParabolic k
  have hExtra : Equiv.swap (pairFst k) 10 ∈ H :=
    Subgroup.mem_sup_right (extra_mem_pairParabolic k)
  have hPair : ∀ l : Fin 5, pairSwap l ∈ H := fun l =>
    Subgroup.mem_sup_right (pairSwap_mem_pairParabolic k l)
  have hBlock : ∀ {j : Fin 5}, j ≠ k → blockSwap k j ∈ H := fun h =>
    Subgroup.mem_sup_left (blockSwap_mem_normalizer h)
  have hEven : ∀ {j : Fin 5}, j ≠ k → Equiv.swap (pairFst j) 10 ∈ H := by
    intro j hjk
    have hconj := blockSwap_conj_extra hjk
    rw [← hconj]
    exact H.mul_mem (H.mul_mem (hBlock hjk) hExtra) (H.inv_mem (hBlock hjk))
  have hThree : ∀ m : Fin 11, m ≠ 10 → Equiv.swap m 10 ∈ H := by
    intro m hm
    obtain ⟨j, rfl | rfl⟩ := exists_pair_eq_of_ne_ten hm
    · by_cases hjk : j = k
      · subst j
        exact hExtra
      · exact hEven hjk
    · by_cases hjk : j = k
      · subst j
        have hconj := pairSwap_conj_extra k
        rw [← hconj]
        exact H.mul_mem (H.mul_mem (hPair k) hExtra) (H.inv_mem (hPair k))
      · have hbase : Equiv.swap (pairFst j) 10 ∈ H := hEven hjk
        have hconj := pairSwap_conj_extra j
        rw [← hconj]
        exact H.mul_mem (H.mul_mem (hPair j) hbase) (H.inv_mem (hPair j))
  have hTrans : ∀ {p q : Fin 11}, p ≠ q → Equiv.swap p q ∈ H := by
    intro p q hpq
    by_cases hp : p = 10
    · subst p
      have hq : q ≠ 10 := fun h => hpq (by rw [h])
      simpa [Equiv.swap_comm] using hThree q hq
    · by_cases hq : q = 10
      · subst q
        exact hThree p hp
      · have hpq10 : Equiv.swap p 10 * Equiv.swap q 10 * Equiv.swap p 10 =
            Equiv.swap p q := by
          have h := Equiv.swap_mul_swap_mul_swap (x := q) (y := 10) (z := p)
            hq (Ne.symm hpq)
          rwa [Equiv.swap_comm 10 p] at h
        rw [← hpq10]
        exact H.mul_mem (H.mul_mem (hThree p hp) (hThree q hq)) (hThree p hp)
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨p, q, hpq, rfl⟩
  exact hTrans hpq

private lemma extra_conj_pairSwap (k : Fin 5) :
    Equiv.swap (pairFst k) 10 * pairSwap k * (Equiv.swap (pairFst k) 10)⁻¹ =
      Equiv.swap (pairSnd k) 10 := by
  have h := Equiv.swap_mul_swap_mul_swap (x := pairSnd k) (y := pairFst k) (z := 10)
    (Ne.symm (pairFst_ne_pairSnd k)) (pairSnd_ne_ten k)
  simpa [pairSwap, Equiv.swap_comm, Equiv.swap_inv] using h

theorem pairParabolic_not_le_normalizer (k : Fin 5) :
    ¬ pairParabolic k ≤ Subgroup.normalizer (pairGroup : Set (Equiv.Perm (Fin 11))) := by
  intro hle
  have hmem : Equiv.swap (pairFst k) 10 ∈
      Subgroup.normalizer (pairGroup : Set (Equiv.Perm (Fin 11))) :=
    hle (extra_mem_pairParabolic k)
  have hconj : Equiv.swap (pairFst k) 10 * pairSwap k * (Equiv.swap (pairFst k) 10)⁻¹ =
      Equiv.swap (pairSnd k) 10 := extra_conj_pairSwap k
  have hconjmem : Equiv.swap (pairSnd k) 10 ∈ pairGroup := by
    have hiff := (Subgroup.mem_normalizer_iff.mp hmem) (pairSwap k)
    have hpg : pairSwap k ∈ pairGroup := pairSwap_mem_pairGroup k
    have := hiff.mp hpg
    rwa [hconj] at this
  have hfix : Equiv.swap (pairSnd k) 10 10 = 10 := by
    have := (MulAction.mem_stabilizer_iff.mp (pairGroup_le_stabilizer_ten hconjmem))
    simpa using this
  rw [Equiv.swap_apply_right] at hfix
  exact pairSnd_ne_ten k hfix

private lemma eq_top_of_forall_swap_ten {H : Subgroup (Equiv.Perm (Fin 11))}
    (h : ∀ m : Fin 11, m ≠ 10 → Equiv.swap m 10 ∈ H) : H = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨p, q, hpq, rfl⟩
  by_cases hp : p = 10
  · subst p
    have hq : q ≠ 10 := fun hq => hpq (by rw [hq])
    simpa [Equiv.swap_comm] using h q hq
  · by_cases hq : q = 10
    · subst q
      exact h p hp
    · have hpq10 : Equiv.swap p 10 * Equiv.swap q 10 * Equiv.swap p 10 =
          Equiv.swap p q := by
        have h' := Equiv.swap_mul_swap_mul_swap (x := q) (y := 10) (z := p)
          hq (Ne.symm hpq)
        rwa [Equiv.swap_comm 10 p] at h'
      rw [← hpq10]
      exact H.mul_mem (H.mul_mem (h p hp) (h q hq)) (h p hp)

theorem iSup_pairParabolic : ⨆ k, pairParabolic k = ⊤ := by
  refine eq_top_of_forall_swap_ten ?_
  intro m hm
  obtain ⟨j, rfl | rfl⟩ := exists_pair_eq_of_ne_ten hm
  · exact (le_iSup (fun k : Fin 5 => pairParabolic k) j) (extra_mem_pairParabolic j)
  · have hconj := pairSwap_conj_extra j
    rw [← hconj]
    refine (le_iSup (fun k : Fin 5 => pairParabolic k) j) ?_
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (pairSwap_mem_pairParabolic j j) (extra_mem_pairParabolic j))
      (Subgroup.inv_mem _ (pairSwap_mem_pairParabolic j j))

private lemma ten_notMem_support_pairSwap (j : Fin 5) :
    (10 : Fin 11) ∉ (pairSwap j).support := by
  rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j)]
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact (pairFst_ne_ten j) h.symm
  · exact (pairSnd_ne_ten j) h.symm

theorem swap_mem_pairGroup_of_commute {τ : Equiv.Perm (Fin 11)} (hτ : τ.IsSwap)
    (hcomm : ∀ k, Commute τ (pairSwap k)) : τ ∈ pairGroup := by
  obtain ⟨p, q, hpq, rfl⟩ := hτ
  have hpres : ∀ k : Fin 5, ∀ x : Fin 11, x ∈ (pairSwap k).support →
      Equiv.swap p q x ∈ (pairSwap k).support := by
    intro k x hx
    exact (Equiv.Perm.mem_support_iff_of_commute (hcomm k) x).mpr hx
  have hten_of_supp : ∀ (j : Fin 5), (10 : Fin 11) ∈ (pairSwap j).support → False :=
    fun j => ten_notMem_support_pairSwap j
  have hp_ne_ten : p ≠ 10 := by
    intro hp10
    have hq_ne : q ≠ 10 := fun h => hpq (hp10.trans h.symm)
    obtain ⟨j, hqj | hqj⟩ := exists_pair_eq_of_ne_ten hq_ne
    · have hq_supp : q ∈ (pairSwap j).support := by
        rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j), hqj]
        exact Finset.mem_insert_self _ _
      have hten : (10 : Fin 11) ∈ (pairSwap j).support := by
        have := hpres j q hq_supp
        have hτq : Equiv.swap p q q = 10 := by rw [hp10, Equiv.swap_apply_right]
        rwa [hτq] at this
      exact hten_of_supp j hten
    · have hq_supp : q ∈ (pairSwap j).support := by
        rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j), hqj]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hten : (10 : Fin 11) ∈ (pairSwap j).support := by
        have := hpres j q hq_supp
        have hτq : Equiv.swap p q q = 10 := by rw [hp10, Equiv.swap_apply_right]
        rwa [hτq] at this
      exact hten_of_supp j hten
  have hq_ne_ten : q ≠ 10 := by
    intro hq10
    have hp_ne : p ≠ 10 := fun h => hpq (h.trans hq10.symm)
    obtain ⟨j, hpj | hpj⟩ := exists_pair_eq_of_ne_ten hp_ne
    · have hp_supp : p ∈ (pairSwap j).support := by
        rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j), hpj]
        exact Finset.mem_insert_self _ _
      have hten : (10 : Fin 11) ∈ (pairSwap j).support := by
        have := hpres j p hp_supp
        have hτp : Equiv.swap p q p = 10 := by rw [Equiv.swap_apply_left, hq10]
        rwa [hτp] at this
      exact hten_of_supp j hten
    · have hp_supp : p ∈ (pairSwap j).support := by
        rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j), hpj]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hten : (10 : Fin 11) ∈ (pairSwap j).support := by
        have := hpres j p hp_supp
        have hτp : Equiv.swap p q p = 10 := by rw [Equiv.swap_apply_left, hq10]
        rwa [hτp] at this
      exact hten_of_supp j hten
  obtain ⟨j, hpj | hpj⟩ := exists_pair_eq_of_ne_ten hp_ne_ten
  · have hp_supp : p ∈ (pairSwap j).support := by
      rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j), hpj]
      exact Finset.mem_insert_self _ _
    have hq_supp : q ∈ (pairSwap j).support := by
      have := hpres j p hp_supp
      rwa [show Equiv.swap p q p = q from Equiv.swap_apply_left p q] at this
    rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j)] at hq_supp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq_supp
    have hq : q = pairSnd j := by
      rcases hq_supp with h | h
      · exact absurd (h.trans hpj.symm).symm hpq
      · exact h
    simpa [pairSwap, hpj, hq] using pairSwap_mem_pairGroup j
  · have hp_supp : p ∈ (pairSwap j).support := by
      rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j), hpj]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hq_supp : q ∈ (pairSwap j).support := by
      have := hpres j p hp_supp
      rwa [show Equiv.swap p q p = q from Equiv.swap_apply_left p q] at this
    rw [pairSwap, Equiv.Perm.support_swap (pairFst_ne_pairSnd j)] at hq_supp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq_supp
    have hq : q = pairFst j := by
      rcases hq_supp with h | h
      · exact h
      · exact absurd (h.trans hpj.symm).symm hpq
    simpa [pairSwap, hpj, hq, Equiv.swap_comm] using pairSwap_mem_pairGroup j

end CFSG.Permutation.FivePairs
