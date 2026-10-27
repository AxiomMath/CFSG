module

public import CFSG.Quasithin.EmptyFaithful.S151YC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def ya7QList : List (Equiv.Perm (Fin 7)) :=
  [ya7MkP [0,1,2,3,4,5,6] [0,1,2,3,4,5,6] (by decide) (by decide),
   ya7MkP [0,1,3,2,5,4,6] [0,1,3,2,5,4,6] (by decide) (by decide),
   ya7MkP [0,1,4,5,2,3,6] [0,1,4,5,2,3,6] (by decide) (by decide),
   ya7MkP [0,1,5,4,3,2,6] [0,1,5,4,3,2,6] (by decide) (by decide),
   ya7MkP [1,0,2,3,5,4,6] [1,0,2,3,5,4,6] (by decide) (by decide),
   ya7MkP [1,0,3,2,4,5,6] [1,0,3,2,4,5,6] (by decide) (by decide),
   ya7MkP [1,0,4,5,3,2,6] [1,0,5,4,2,3,6] (by decide) (by decide),
   ya7MkP [1,0,5,4,2,3,6] [1,0,4,5,3,2,6] (by decide) (by decide),
   ya7MkP [2,3,0,1,4,5,6] [2,3,0,1,4,5,6] (by decide) (by decide),
   ya7MkP [2,3,1,0,5,4,6] [3,2,0,1,5,4,6] (by decide) (by decide),
   ya7MkP [2,3,4,5,0,1,6] [4,5,0,1,2,3,6] (by decide) (by decide),
   ya7MkP [2,3,5,4,1,0,6] [5,4,0,1,3,2,6] (by decide) (by decide),
   ya7MkP [3,2,0,1,5,4,6] [2,3,1,0,5,4,6] (by decide) (by decide),
   ya7MkP [3,2,1,0,4,5,6] [3,2,1,0,4,5,6] (by decide) (by decide),
   ya7MkP [3,2,4,5,1,0,6] [5,4,1,0,2,3,6] (by decide) (by decide),
   ya7MkP [3,2,5,4,0,1,6] [4,5,1,0,3,2,6] (by decide) (by decide),
   ya7MkP [4,5,0,1,2,3,6] [2,3,4,5,0,1,6] (by decide) (by decide),
   ya7MkP [4,5,1,0,3,2,6] [3,2,5,4,0,1,6] (by decide) (by decide),
   ya7MkP [4,5,2,3,0,1,6] [4,5,2,3,0,1,6] (by decide) (by decide),
   ya7MkP [4,5,3,2,1,0,6] [5,4,3,2,0,1,6] (by decide) (by decide),
   ya7MkP [5,4,0,1,3,2,6] [2,3,5,4,1,0,6] (by decide) (by decide),
   ya7MkP [5,4,1,0,2,3,6] [3,2,4,5,1,0,6] (by decide) (by decide),
   ya7MkP [5,4,2,3,1,0,6] [5,4,2,3,1,0,6] (by decide) (by decide),
   ya7MkP [5,4,3,2,0,1,6] [4,5,3,2,1,0,6] (by decide) (by decide)]

@[expose] def ya7Q (i : Fin 24) : Equiv.Perm (Fin 7) := ya7QList.getD i.val 1

theorem ya7Q_stab : ∀ i : Fin 24, StabilizesPartition (ya7Q i) ya7P0 := by
  unfold ya7Q ya7QList ya7MkP StabilizesPartition ya7P0; decide +kernel

theorem ya7Q_sign : ∀ i : Fin 24, Equiv.Perm.sign (ya7Q i) = 1 := by
  unfold ya7Q ya7QList ya7MkP; decide +kernel

theorem ya7Q_inj : ∀ i j : Fin 24, ya7Q i = ya7Q j → i = j := by
  unfold ya7Q ya7QList ya7MkP; decide +kernel

@[expose] def ya7QOddList : List (Equiv.Perm (Fin 7)) :=
  [
   ya7MkP [0,1,2,3,5,4,6] [0,1,2,3,5,4,6] (by decide) (by decide),
   ya7MkP [0,1,3,2,4,5,6] [0,1,3,2,4,5,6] (by decide) (by decide),
   ya7MkP [0,1,4,5,3,2,6] [0,1,5,4,2,3,6] (by decide) (by decide),
   ya7MkP [0,1,5,4,2,3,6] [0,1,4,5,3,2,6] (by decide) (by decide),
   ya7MkP [1,0,2,3,4,5,6] [1,0,2,3,4,5,6] (by decide) (by decide),
   ya7MkP [1,0,3,2,5,4,6] [1,0,3,2,5,4,6] (by decide) (by decide),
   ya7MkP [1,0,4,5,2,3,6] [1,0,4,5,2,3,6] (by decide) (by decide),
   ya7MkP [1,0,5,4,3,2,6] [1,0,5,4,3,2,6] (by decide) (by decide),
   ya7MkP [2,3,0,1,5,4,6] [2,3,0,1,5,4,6] (by decide) (by decide),
   ya7MkP [2,3,1,0,4,5,6] [3,2,0,1,4,5,6] (by decide) (by decide),
   ya7MkP [2,3,4,5,1,0,6] [5,4,0,1,2,3,6] (by decide) (by decide),
   ya7MkP [2,3,5,4,0,1,6] [4,5,0,1,3,2,6] (by decide) (by decide),
   ya7MkP [3,2,0,1,4,5,6] [2,3,1,0,4,5,6] (by decide) (by decide),
   ya7MkP [3,2,1,0,5,4,6] [3,2,1,0,5,4,6] (by decide) (by decide),
   ya7MkP [3,2,4,5,0,1,6] [4,5,1,0,2,3,6] (by decide) (by decide),
   ya7MkP [3,2,5,4,1,0,6] [5,4,1,0,3,2,6] (by decide) (by decide),
   ya7MkP [4,5,0,1,3,2,6] [2,3,5,4,0,1,6] (by decide) (by decide),
   ya7MkP [4,5,1,0,2,3,6] [3,2,4,5,0,1,6] (by decide) (by decide),
   ya7MkP [4,5,2,3,1,0,6] [5,4,2,3,0,1,6] (by decide) (by decide),
   ya7MkP [4,5,3,2,0,1,6] [4,5,3,2,0,1,6] (by decide) (by decide),
   ya7MkP [5,4,0,1,2,3,6] [2,3,4,5,1,0,6] (by decide) (by decide),
   ya7MkP [5,4,1,0,3,2,6] [3,2,5,4,1,0,6] (by decide) (by decide),
   ya7MkP [5,4,2,3,0,1,6] [4,5,2,3,1,0,6] (by decide) (by decide),
   ya7MkP [5,4,3,2,1,0,6] [5,4,3,2,1,0,6] (by decide) (by decide)]

@[expose] def ya7Q48 (i : Fin 48) : Equiv.Perm (Fin 7) := (ya7QList ++ ya7QOddList).getD i.val 1

theorem ya7Q48_eq : ∀ i : Fin 24, ya7Q48 ⟨i.val, by omega⟩ = ya7Q i := by
  unfold ya7Q48 ya7Q ya7QList ya7QOddList ya7MkP; decide +kernel

theorem ya7Q48_sign : ∀ i : Fin 48, 24 ≤ i.val → Equiv.Perm.sign (ya7Q48 i) = -1 := by
  unfold ya7Q48 ya7QList ya7QOddList ya7MkP; decide +kernel

theorem ya7_ofFn_mem (σ : Equiv.Perm (Fin 7)) :
    List.ofFn σ ∈ List.permutations' (List.finRange 7) := by
  rw [List.mem_permutations']
  have hnd1 : (List.ofFn σ).Nodup := by
    rw [List.nodup_ofFn]
    exact σ.injective
  refine List.perm_of_nodup_nodup_toFinset_eq hnd1 (List.nodup_finRange 7) ?_
  ext x
  simp only [List.mem_toFinset, List.mem_ofFn, List.mem_finRange, iff_true]
  exact ⟨σ⁻¹ x, by simp⟩

@[expose] def ya7PairOK (a b : Fin 7) : Prop := a ≠ b ∧ a.val < 6 ∧ a.val / 2 = b.val / 2

instance (a b : Fin 7) : Decidable (ya7PairOK a b) := by unfold ya7PairOK; infer_instance

theorem ya7_pair_mem : ∀ a b : Fin 7, a ≠ b → ({a, b} : Finset (Fin 7)) ∈ ya7P0 → ya7PairOK a b := by
  unfold ya7P0 ya7PairOK; decide +kernel

theorem ya7_single_mem : ∀ a : Fin 7, ({a} : Finset (Fin 7)) ∈ ya7P0 → a = 6 := by
  unfold ya7P0; decide +kernel

@[expose] def ya7TabOK (t : List (Fin 7)) : Prop :=
  t.getD 6 0 = 6 ∧ ya7PairOK (t.getD 0 0) (t.getD 1 0) ∧ ya7PairOK (t.getD 2 0) (t.getD 3 0) ∧
    ya7PairOK (t.getD 4 0) (t.getD 5 0)

instance (t : List (Fin 7)) : Decidable (ya7TabOK t) := by unfold ya7TabOK; infer_instance

set_option maxRecDepth 100000 in
theorem ya7_tab_check : ∀ t ∈ List.permutations' (List.finRange 7), ya7TabOK t →
    ∃ i : Fin 48, List.ofFn (ya7Q48 i) = t := by
  unfold ya7TabOK ya7PairOK ya7Q48 ya7QList ya7QOddList ya7MkP; decide +kernel

theorem ya7_tabOK_of_stab {σ : Equiv.Perm (Fin 7)} (h : StabilizesPartition σ ya7P0) :
    ya7TabOK (List.ofFn σ) := by
  have hget : ∀ k : Fin 7, (List.ofFn σ).getD k.val 0 = σ k := by
    intro k
    fin_cases k <;> simp
  have hmem : ∀ B ∈ ya7P0, B.image σ ∈ ya7P0 := by
    intro B hB
    have : B.image σ ∈ ya7P0.image (Finset.image σ) := Finset.mem_image_of_mem _ hB
    rw [show ya7P0.image (Finset.image σ) = ya7P0 from h] at this
    exact this
  have h6 : σ 6 = 6 := by
    have := hmem {6} (by unfold ya7P0; decide)
    rw [Finset.image_singleton] at this
    exact ya7_single_mem _ this
  have hpair : ∀ a b : Fin 7, a ≠ b → ({a, b} : Finset (Fin 7)) ∈ ya7P0 →
      ya7PairOK (σ a) (σ b) := by
    intro a b hab hP
    have := hmem _ hP
    rw [Finset.image_insert, Finset.image_singleton] at this
    exact ya7_pair_mem _ _ (fun h => hab (σ.injective h)) this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hget 6).trans h6
  · have := hpair 0 1 (by decide) (by unfold ya7P0; decide)
    rwa [← hget 0, ← hget 1] at this
  · have := hpair 2 3 (by decide) (by unfold ya7P0; decide)
    rwa [← hget 2, ← hget 3] at this
  · have := hpair 4 5 (by decide) (by unfold ya7P0; decide)
    rwa [← hget 4, ← hget 5] at this

theorem ya7Q_complete (σ : alternatingGroup (Fin 7))
    (h : StabilizesPartition (σ : Equiv.Perm (Fin 7)) ya7P0) :
    ∃ i : Fin 24, (σ : Equiv.Perm (Fin 7)) = ya7Q i := by
  obtain ⟨i, hi⟩ := ya7_tab_check _ (ya7_ofFn_mem (σ : Equiv.Perm (Fin 7))) (ya7_tabOK_of_stab h)
  have hσ : ya7Q48 i = (σ : Equiv.Perm (Fin 7)) :=
    Equiv.ext (congrFun (List.ofFn_injective hi))
  have hsign : Equiv.Perm.sign (σ : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp σ.2
  have hlt : i.val < 24 := by
    by_contra hge
    have := ya7Q48_sign i (not_lt.mp hge)
    rw [hσ, hsign] at this
    exact absurd this (by decide)
  refine ⟨⟨i.val, hlt⟩, ?_⟩
  rw [← hσ, ← ya7Q48_eq ⟨i.val, hlt⟩]

theorem ya7_card_Q0 : Nat.card ↥(ya7PartStab ya7P0) = 24 := by
  let e : Fin 24 → ↥(ya7PartStab ya7P0) := fun i =>
    ⟨⟨ya7Q i, Equiv.Perm.mem_alternatingGroup.mpr (ya7Q_sign i)⟩, ya7Q_stab i⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro i j hij
      exact ya7Q_inj i j (congrArg (fun x : ↥(ya7PartStab ya7P0) =>
        ((x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) hij)
    · rintro ⟨σ, hσ⟩
      obtain ⟨i, hi⟩ := ya7Q_complete σ hσ
      exact ⟨i, Subtype.ext (Subtype.ext hi.symm)⟩
  rw [← Nat.card_eq_of_bijective e hbij]
  simp

theorem ya7_between (K : Subgroup (alternatingGroup (Fin 7))) (h1 : ya7D0 ≤ K)
    (h2 : K ≤ ya7PartStab ya7P0) : K = ya7D0 ∨ K = ya7PartStab ya7P0 := by
  have hd1 : Nat.card ↥ya7D0 ∣ Nat.card ↥K := Subgroup.card_dvd_of_le h1
  have hd2 : Nat.card ↥K ∣ Nat.card ↥(ya7PartStab ya7P0) := Subgroup.card_dvd_of_le h2
  rw [ya7D0_card] at hd1
  rw [ya7_card_Q0] at hd2
  have hle : Nat.card ↥K ≤ 24 := Nat.le_of_dvd (by norm_num) hd2
  obtain ⟨k, hk⟩ := hd1
  have hk3 : k ≤ 3 := by omega
  have hK : Nat.card ↥K = 8 ∨ Nat.card ↥K = 24 := by
    interval_cases k
    · rw [hk] at hd2; omega
    · left; omega
    · rw [hk] at hd2; omega
    · right; omega
  rcases hK with hK | hK
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hK, ya7D0_card])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h2 (by rw [hK, ya7_card_Q0])

theorem ya7_notD0_conj : ∀ j : Fin 8, ya7Q 10 * ya7E 4 * (ya7Q 10)⁻¹ ≠ ya7E j := by
  unfold ya7Q ya7QList ya7E ya7MkP; decide +kernel

theorem ya7_D0_not_normal :
    ∃ q ∈ ya7PartStab ya7P0, ∃ d ∈ ya7D0, q * d * q⁻¹ ∉ ya7D0 := by
  refine ⟨⟨ya7Q 10, Equiv.Perm.mem_alternatingGroup.mpr (ya7Q_sign 10)⟩, ya7Q_stab 10,
    ⟨ya7E 4, Equiv.Perm.mem_alternatingGroup.mpr (ya7E_sign 4)⟩, ⟨4, rfl⟩, ?_⟩
  intro h
  obtain ⟨j, hj⟩ := Subgroup.mem_subgroupOf.mp h
  exact ya7_notD0_conj j hj.symm

@[expose] def ya7Delta : Finset (Fin 7 → ZMod 2) := Finset.univ.filter fun v => ∑ i, v i = 0

@[expose] def ya7Sub (σ : Equiv.Perm (Fin 7)) (v : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  fun i => v i - v (σ⁻¹ i)

@[expose] def ya7Sub3 (σ : Equiv.Perm (Fin 7)) (v : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  ya7Sub σ (ya7Sub σ (ya7Sub σ v))

@[expose] def ya7ImVecs3 (σ : Equiv.Perm (Fin 7)) : Finset (Fin 7 → ZMod 2) :=
  ya7Delta.image (ya7Sub3 σ)

theorem ya7_im3_card : ∀ i : Fin 24, (ya7Q i) ^ 3 = 1 → ya7Q i ≠ 1 →
    16 ≤ (ya7ImVecs3 (ya7Q i)).card := by
  unfold ya7ImVecs3 ya7Delta ya7Sub3 ya7Sub ya7Q ya7QList ya7MkP; decide +kernel

theorem ya7_comm_three : ∀ i j : Fin 24, (ya7Q i) ^ 3 = 1 → ya7Q i ≠ 1 → (ya7Q j) ^ 3 = 1 → ya7Q j ≠ 1 →
    ya7Q i * ya7Q j = ya7Q j * ya7Q i → ya7Q j = ya7Q i ∨ ya7Q j = (ya7Q i)⁻¹ := by
  unfold ya7Q ya7QList ya7MkP; decide +kernel

theorem ya7_fixed_pt : ∀ d : Fin 7, (∀ i : Fin 8, ya7E i d = d) → d = 6 := by
  unfold ya7E ya7MkP; decide +kernel

theorem ya7_unique_core :
    ((((Finset.univ.erase (6 : Fin 7)).powersetCard 2).powersetCard 3).filter
      (fun P' => ∀ i : Fin 8, (insert ({(6 : Fin 7)} : Finset (Fin 7)) P').image (Finset.image ⇑(ya7E i)) =
        insert ({(6 : Fin 7)} : Finset (Fin 7)) P')) =
      ({({{0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 7)))} : Finset (Finset (Finset (Fin 7)))) := by
  unfold ya7E ya7MkP; decide +kernel

theorem ya7P0_eq : ya7P0 = insert ({6} : Finset (Fin 7)) {{0, 1}, {2, 3}, {4, 5}} := by
  unfold ya7P0; decide +kernel

theorem ya7_unique_stable {P : Finset (Finset (Fin 7))} (hP : IsPartitionOfType P {2, 2, 2, 1})
    (hst : ∀ i : Fin 8, StabilizesPartition (ya7E i) P) : P = ya7P0 := by
  classical
  obtain ⟨-, hdisj, -, hcard⟩ := hP
  have h1 : (1 : ℕ) ∈ P.val.map Finset.card := by
    rw [hcard]
    decide
  obtain ⟨B, hB, hB1⟩ := Multiset.mem_map.mp h1
  obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp hB1
  have hdP : ({d} : Finset (Fin 7)) ∈ P := hB
  have hPval : P.val = {d} ::ₘ (P.erase {d}).val := by
    rw [Finset.erase_val]
    exact (Multiset.cons_erase (Finset.mem_val.mpr hdP)).symm
  have hcard' : (P.erase {d}).val.map Finset.card = {2, 2, 2} := by
    rw [hPval, Multiset.map_cons, Finset.card_singleton] at hcard
    have h : ({2, 2, 2, 1} : Multiset ℕ) = 1 ::ₘ {2, 2, 2} := by decide
    rw [h] at hcard
    exact (Multiset.cons_inj_right 1).mp hcard
  have hcardP' : (P.erase {d}).card = 3 := by
    have h := congrArg Multiset.card hcard'
    rw [Multiset.card_map] at h
    have h3 : Multiset.card ({2, 2, 2} : Multiset ℕ) = 3 := by decide
    rw [h3] at h
    exact h
  have hB2 : ∀ B ∈ P.erase {d}, B.card = 2 := by
    intro B hB
    have hm : B.card ∈ (P.erase {d}).val.map Finset.card := Multiset.mem_map_of_mem _ hB
    rw [hcard'] at hm
    simpa using hm
  have hfix : ∀ i : Fin 8, ya7E i d = d := by
    intro i
    have hmem : ({ya7E i d} : Finset (Fin 7)) ∈ P := by
      have h := Finset.mem_image_of_mem (Finset.image (ya7E i)) hdP
      rw [show P.image (Finset.image ⇑(ya7E i)) = P from hst i] at h
      simpa using h
    by_contra hne
    have hne' : ({ya7E i d} : Finset (Fin 7)) ≠ {d} := fun h => hne (Finset.singleton_injective h)
    have := hB2 _ (Finset.mem_erase.mpr ⟨hne', hmem⟩)
    simp at this
  have hd6 : d = 6 := ya7_fixed_pt d hfix
  subst hd6
  have hsub : ∀ B ∈ P.erase {6}, B ⊆ Finset.univ.erase 6 := by
    intro B hB x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    have hBP : B ∈ P := Finset.mem_of_mem_erase hB
    have hne' : B ≠ {6} := Finset.ne_of_mem_erase hB
    exact Finset.disjoint_left.mp (hdisj B hBP {6} hdP hne') hx (Finset.mem_singleton_self 6)
  have hmem : P.erase {6} ∈ ((Finset.univ.erase (6 : Fin 7)).powersetCard 2).powersetCard 3 := by
    rw [Finset.mem_powersetCard]
    refine ⟨fun B hB => ?_, hcardP'⟩
    rw [Finset.mem_powersetCard]
    exact ⟨hsub B hB, hB2 B hB⟩
  have hPeq : P = insert {6} (P.erase {6}) := (Finset.insert_erase hdP).symm
  have hst' : ∀ i : Fin 8, (insert ({(6 : Fin 7)} : Finset (Fin 7)) (P.erase {6})).image
      (Finset.image ⇑(ya7E i)) = insert ({(6 : Fin 7)} : Finset (Fin 7)) (P.erase {6}) := by
    intro i
    rw [← hPeq]
    exact hst i
  have hfil : P.erase {6} ∈ ((((Finset.univ.erase (6 : Fin 7)).powersetCard 2).powersetCard 3).filter
      (fun P' => ∀ i : Fin 8, (insert ({(6 : Fin 7)} : Finset (Fin 7)) P').image (Finset.image ⇑(ya7E i)) =
        insert ({(6 : Fin 7)} : Finset (Fin 7)) P')) :=
    Finset.mem_filter.mpr ⟨hmem, hst'⟩
  rw [ya7_unique_core, Finset.mem_singleton] at hfil
  rw [hPeq, hfil, ya7P0_eq]

end CFSG.Quasithin
