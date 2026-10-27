module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcAbelSq

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

namespace AbelPset

theorem pset_eq_map (r l : H) (T : Finset ℕ) :
    pset r l T = ((T.sort (· ≤ ·)).map fun t : ℕ => tx r l (t : ℤ)).prod := by
  simp only [pset]
  rw [show (do let a ← T.sort (· ≤ ·); pure (a : ℤ) : List ℤ) =
    (T.sort (· ≤ ·)).map (fun a : ℕ => (a : ℤ)) from by
      simp [List.map_eq_flatMap], List.map_map]
  rfl

theorem pset_empty (r l : H) : pset r l ∅ = 1 := by
  simp [pset]

theorem pset_singleton (r l : H) (a : ℕ) : pset r l {a} = tx r l a := by
  simp [pset]

theorem symmDiff_singleton_of_notMem {a : ℕ} {U : Finset ℕ} (ha : a ∉ U) :
    symmDiff {a} U = insert a U := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  by_cases hx : x = a
  · subst hx
    simp [ha]
  · simp [hx]

theorem symmDiff_singleton_of_mem {a : ℕ} {T : Finset ℕ} (ha : a ∈ T) :
    symmDiff {a} T = T.erase a := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
  by_cases hx : x = a
  · subst hx
    simp [ha]
  · simp [hx]

theorem symmDiff_subset {A B C : Finset ℕ} (hA : A ⊆ C) (hB : B ⊆ C) : symmDiff A B ⊆ C := by
  intro x hx
  rcases Finset.mem_symmDiff.1 hx with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hA h1
  · exact hB h1

section Abelian

variable (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : i < s) (hab : Abel Hs i)

include h hi hab

omit hab in
theorem tx_mem_Hs {t : ℕ} (ht : t ∈ Finset.Icc 1 i) : tx r l t ∈ Hs i :=
  tx_mem_of_le h (Finset.mem_Icc.1 ht).2 hi.le

omit hab in
theorem pset_mem {T : Finset ℕ} (hT : T ⊆ Finset.Icc 1 i) : pset r l T ∈ Hs i := by
  rw [pset_eq_map]
  refine Subgroup.list_prod_mem _ ?_
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hg
  exact tx_mem_Hs h hi (hT ((Finset.mem_sort _).1 ht))

theorem pset_insert {a : ℕ} {U : Finset ℕ} (hT : insert a U ⊆ Finset.Icc 1 i) (ha : a ∉ U) :
    pset r l (insert a U) = tx r l a * pset r l U := by
  rw [pset_eq_map, pset_eq_map]
  have hperm : List.Perm ((insert a U).sort (· ≤ ·)) (a :: U.sort (· ≤ ·)) := by
    refine List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _)
      (List.nodup_cons.2 ⟨by simpa using ha, Finset.sort_nodup _ _⟩) ?_
    ext x
    simp
  have hc : (((insert a U).sort (· ≤ ·)).map fun t : ℕ => tx r l (t : ℤ)).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.pairwise_of_forall_mem_list fun x hx y hy => ?_
    exact hab _ (tx_mem_Hs h hi (hT ((Finset.mem_sort _).1 hx))) _
      (tx_mem_Hs h hi (hT ((Finset.mem_sort _).1 hy)))
  rw [(hperm.map _).prod_eq' hc]
  simp

theorem pset_single_mul {a : ℕ} (ha : a ∈ Finset.Icc 1 i) {T : Finset ℕ}
    (hT : T ⊆ Finset.Icc 1 i) : tx r l a * pset r l T = pset r l (symmDiff {a} T) := by
  by_cases haT : a ∈ T
  · have hT' : insert a (T.erase a) = T := Finset.insert_erase haT
    have hT'' : insert a (T.erase a) ⊆ Finset.Icc 1 i := by
      rw [hT']
      exact hT
    have h1 : pset r l T = tx r l a * pset r l (T.erase a) := by
      have := pset_insert h hi hab hT'' (Finset.notMem_erase a T)
      rwa [hT'] at this
    have hsq := abel_sq_eq_one h hi hab (Finset.mem_Icc.1 ha).1 (Finset.mem_Icc.1 ha).2
    rw [h1, ← mul_assoc, ← pow_two, hsq, one_mul, symmDiff_singleton_of_mem haT]
  · rw [symmDiff_singleton_of_notMem haT]
    exact (pset_insert h hi hab (Finset.insert_subset ha hT) haT).symm

end Abelian

end AbelPset

open AbelPset in
theorem pset_mul (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : i < s) (hab : Abel Hs i)
    {T T' : Finset ℕ} (hT : T ⊆ Finset.Icc 1 i) (hT' : T' ⊆ Finset.Icc 1 i) :
    pset r l T * pset r l T' = pset r l (symmDiff T T') := by
  induction T' using Finset.induction_on generalizing T with
  | empty =>
    rw [pset_empty, mul_one, ← Finset.bot_eq_empty, symmDiff_bot]
  | insert a U ha ih =>
    have hU : U ⊆ Finset.Icc 1 i := (Finset.subset_insert a U).trans hT'
    have haI : a ∈ Finset.Icc 1 i := hT' (Finset.mem_insert_self a U)
    have hcomm : pset r l T * tx r l a = tx r l a * pset r l T :=
      hab _ (pset_mem h hi hT) _ (tx_mem_Hs h hi haI)
    have hsub : symmDiff {a} T ⊆ Finset.Icc 1 i :=
      symmDiff_subset (Finset.singleton_subset_iff.2 haI) hT
    calc pset r l T * pset r l (insert a U)
        = pset r l T * (tx r l a * pset r l U) := by rw [pset_insert h hi hab hT' ha]
      _ = (tx r l a * pset r l T) * pset r l U := by rw [← mul_assoc, hcomm, mul_assoc]
      _ = pset r l (symmDiff {a} T) * pset r l U := by rw [pset_single_mul h hi hab haI hT]
      _ = pset r l (symmDiff (symmDiff {a} T) U) := ih hsub hU
      _ = pset r l (symmDiff T (insert a U)) := by
        rw [← symmDiff_singleton_of_notMem ha, ← symmDiff_assoc, symmDiff_comm T {a}]

open AbelPset in
theorem exists_pset (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : i < s) (hab : Abel Hs i) {g : H}
    (hg : g ∈ Hs i) : ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 i ∧ g = pset r l T := by
  rw [Hs_eq_closure h hi.le] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk1, hki, rfl⟩ := hx
    exact ⟨{k}, by simpa [Finset.singleton_subset_iff] using And.intro hk1 hki,
      (pset_singleton r l k).symm⟩
  | one => exact ⟨∅, Finset.empty_subset _, (pset_empty r l).symm⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨T, hT, rfl⟩ := ihx
    obtain ⟨T', hT', rfl⟩ := ihy
    exact ⟨symmDiff T T', symmDiff_subset hT hT', pset_mul h hi hab hT hT'⟩
  | inv x hx ih =>
    obtain ⟨T, hT, rfl⟩ := ih
    refine ⟨T, hT, inv_eq_of_mul_eq_one_right ?_⟩
    rw [pset_mul h hi hab hT hT, symmDiff_self, Finset.bot_eq_empty, pset_empty]

open AbelPset in
theorem pset_inj (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : i < s) (hab : Abel Hs i)
    {T T' : Finset ℕ} (hT : T ⊆ Finset.Icc 1 i) (hT' : T' ⊆ Finset.Icc 1 i)
    (heq : pset r l T = pset r l T') : T = T' := by
  classical
  let F : ↥((Finset.Icc 1 i).powerset) → ↥(Hs i) := fun T =>
    ⟨pset r l T.1, pset_mem h hi (Finset.mem_powerset.1 T.2)⟩
  have hsurj : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨T, hT, rfl⟩ := exists_pset h hi hab hg
    exact ⟨⟨T, Finset.mem_powerset.2 hT⟩, rfl⟩
  have hcard : Nat.card ↥((Finset.Icc 1 i).powerset) = Nat.card ↥(Hs i) := by
    rw [h.card_lt i hi, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powerset,
      Nat.card_Icc, Nat.add_sub_cancel]
  have hbij : Function.Bijective F := hsurj.bijective_of_nat_card_le hcard.le
  have := hbij.1 (a₁ := ⟨T, Finset.mem_powerset.2 hT⟩) (a₂ := ⟨T', Finset.mem_powerset.2 hT'⟩)
    (Subtype.ext heq)
  exact congrArg Subtype.val this

namespace AbelPset

variable (h : IsTutteSys s r l ξ Hs) {k : ℕ} (hk : k < s) (hab : Abel Hs k)

include h hk hab

theorem tx_int_sq {t : ℤ} (ht1 : 1 ≤ t) (htk : t ≤ k) : tx r l t ^ 2 = 1 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
  exact abel_sq_eq_one h hk hab (by omega) (by omega)

theorem nfw_eq_prod (e : ℤ) (he : e = 1 ∨ e = -1) {K : List ℤ} (hK : ∀ t ∈ K, 1 ≤ t ∧ t ≤ k) :
    nfw r l e K = (K.map fun t => tx r l t).prod := by
  induction K generalizing e with
  | nil => simp [nfw]
  | cons t L ih =>
    have ht := hK t List.mem_cons_self
    have hL : ∀ u ∈ L, 1 ≤ u ∧ u ≤ k := fun u hu => hK u (List.mem_cons_of_mem _ hu)
    have hsq := tx_int_sq h hk hab ht.1 ht.2
    have hinv : (tx r l t)⁻¹ = tx r l t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq)
    have he' : -e = 1 ∨ -e = -1 := by rcases he with rfl | rfl <;> simp
    have hz : tx r l t ^ e = tx r l t := by
      rcases he with rfl | rfl
      · exact zpow_one _
      · rw [zpow_neg_one, hinv]
    simp only [nfw, List.map_cons, List.prod_cons]
    rw [hz, ih (-e) he' hL]

theorem prod_eq_pset {K : List ℤ} (hK : ∀ t ∈ K, 1 ≤ t ∧ t ≤ k) :
    (K.map fun t => tx r l t).prod =
      pset r l ((Finset.Icc 1 k).filter fun u : ℕ => ¬ Even (K.count (u : ℤ))) := by
  classical
  induction K with
  | nil => simp [pset_empty]
  | cons t L ih =>
    have ht := hK t List.mem_cons_self
    have hL : ∀ u ∈ L, 1 ≤ u ∧ u ≤ k := fun u hu => hK u (List.mem_cons_of_mem _ hu)
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
    have hnI : n ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hTL : ((Finset.Icc 1 k).filter fun u : ℕ => ¬ Even (L.count (u : ℤ))) ⊆
        Finset.Icc 1 k := Finset.filter_subset _ _
    rw [List.map_cons, List.prod_cons, ih hL, pset_single_mul h hk hab hnI hTL]
    congr 1
    ext u
    have hcount : ((n : ℤ) :: L).count (u : ℤ) = L.count (u : ℤ) + if n = u then 1 else 0 := by
      rw [List.count_cons]
      by_cases hnu : n = u
      · subst hnu
        simp
      · have : ¬ ((n : ℤ) = (u : ℤ)) := by exact_mod_cast hnu
        simp [this, hnu]
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_filter, hcount]
    by_cases hnu : n = u
    · subst hnu
      simp [hnI, Nat.even_add_one]
    · have : ¬ u = n := fun h' => hnu h'.symm
      simp [hnu, this]

end AbelPset

open AbelPset in
theorem nfw_abel_eq_one (h : IsTutteSys s r l ξ Hs) {k : ℕ} (hk : k < s) (hab : Abel Hs k)
    (e : ℤ) (he : e = 1 ∨ e = -1) (K : List ℤ) (hK : ∀ t ∈ K, 1 ≤ t ∧ t ≤ k)
    (h1 : nfw r l e K = 1) : ∀ t : ℤ, Even (K.count t) := by
  classical
  set T := (Finset.Icc 1 k).filter fun u : ℕ => ¬ Even (K.count (u : ℤ)) with hTdef
  have hTsub : T ⊆ Finset.Icc 1 k := Finset.filter_subset _ _
  have hpset : pset r l T = pset r l ∅ := by
    rw [pset_empty, ← prod_eq_pset h hk hab hK, ← nfw_eq_prod h hk hab e he hK, h1]
  have hT0 : T = ∅ := pset_inj h hk hab hTsub (Finset.empty_subset _) hpset
  intro t
  by_cases ht : 1 ≤ t ∧ t ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t)
    have hn : n ∉ T := by
      rw [hT0]
      exact Finset.notMem_empty n
    have hnI : n ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    simpa [hTdef, hnI] using hn
  · have : K.count t = 0 := List.count_eq_zero.2 fun hmem => ht (hK t hmem)
    rw [this]
    exact ⟨0, rfl⟩

end CFSG.Quasithin.Fan86.Tutte
