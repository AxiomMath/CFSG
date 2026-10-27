module

public import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def k0patPerm (a : List ℕ) (N : ℕ) : Prop :=
  a.Nodup ∧ a.length = N ∧ ∀ x ∈ a, x < N

instance k0patPerm.instDecidablePred (N : ℕ) : DecidablePred (fun a : List ℕ => k0patPerm a N) :=
  fun a => decidable_of_iff (a.Nodup ∧ a.length = N ∧ ∀ x ∈ a, x < N) (by unfold k0patPerm; rfl)

private theorem k0patPerm_id (N : ℕ) : k0patPerm (k0pId N) N := by
  refine ⟨?_, ?_, ?_⟩
  · exact List.nodup_range
  · exact List.length_range
  · intro x hx
    exact List.mem_range.mp hx

theorem k0patPerm_mul {a b : List ℕ} {N : ℕ} (ha : k0patPerm a N) (hb : k0patPerm b N) :
    k0patPerm (k0pMul a b) N := by
  obtain ⟨hna, hla, hba⟩ := ha
  obtain ⟨hnb, hlb, hbb⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · rw [k0pMul]
    refine List.Nodup.map_on (f := fun i => a.getD i 0) (fun x hx y hy hxy => ?_) hnb
    exact (hna.getD_inj (by rw [hla]; exact hbb x hx) (by rw [hla]; exact hbb y hy)).mp hxy
  · rw [k0pMul, List.length_map, hlb]
  · intro x hx
    rw [k0pMul, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y < a.length := by rw [hla]; exact hbb y hy
    have hmem : a.getD y 0 ∈ a := by
      rw [← List.getElem_eq_getD (h := hy') 0]
      exact List.getElem_mem hy'
    exact hba _ hmem

private theorem k0patPerm_exists_getD {a : List ℕ} {N : ℕ} (h : k0patPerm a N)
    {j : ℕ} (hj : j < N) :
    ∃ i < a.length, a.getD i 0 = j := by
  have hsub : a.toFinset ⊆ Finset.range N := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.mpr (h.2.2 x hx)
  have hcard : a.toFinset.card = N := by
    rw [List.toFinset_card_of_nodup h.1, h.2.1]
  have heq : a.toFinset = Finset.range N := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    simp [hcard]
  have hj' : j ∈ a.toFinset := by
    rw [heq]
    exact Finset.mem_range.mpr hj
  rw [List.mem_toFinset] at hj'
  obtain ⟨i, hi, hij⟩ := List.mem_iff_getElem.mp hj'
  exact ⟨i, hi, (List.getElem_eq_getD (h := hi) 0).symm.trans hij⟩

private theorem k0patAct_getD_set_ne {l : List ℕ} {i j : ℕ} (h : i ≠ j) (a d : ℕ) :
    (l.set i a).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_ne h]

private theorem k0patAct_getD_set_self {l : List ℕ} {i : ℕ} (h : i < l.length) (a d : ℕ) :
    (l.set i a).getD i d = a := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_self h]
  rfl

theorem k0patAct_getD_map (f : ℕ → ℕ) (hf : f 0 = 0) (s : List ℕ) (i : ℕ) :
    (s.map f).getD i 0 = f (s.getD i 0) := by
  induction s generalizing i with
  | nil => simpa [hf]
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i

private theorem k0patAct_length (a s : List ℕ) : (k0pAct a s).length = s.length := by
  have h : ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ),
      (k0pAct.go s i l acc).length = acc.length := by
    intro l
    induction l with
    | nil => intro i acc; rw [k0pAct.go.eq_1]
    | cons x xs ih =>
        intro i acc
        rw [k0pAct.go.eq_2]
        exact (ih (i + 1) (acc.set x (s.getD i 0))).trans List.length_set
  rw [k0pAct]
  simpa using h a 0 (List.replicate s.length 0)

private lemma k0patAct_go_getD_not_mem (s : List ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ) (j : ℕ), j ∉ l →
      (k0pAct.go s i l acc).getD j 0 = acc.getD j 0 := by
  intro l
  induction l with
  | nil => intro i acc j _; rw [k0pAct.go.eq_1]
  | cons x xs ih =>
      intro i acc j hj
      rw [k0pAct.go.eq_2]
      rw [ih (i + 1) (acc.set x (s.getD i 0)) j (by simp at hj ⊢; tauto)]
      exact k0patAct_getD_set_ne (by simp at hj; tauto) _ _

private lemma k0patAct_go_getD_mem (s : List ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ), l.Nodup → (∀ x ∈ l, x < acc.length) →
      ∀ k < l.length, (k0pAct.go s i l acc).getD (l.getD k 0) 0 = s.getD (i + k) 0 := by
  intro l
  induction l with
  | nil => intro i acc _ _ k hk; simp at hk
  | cons x xs ih =>
      intro i acc hnd hlt k hk
      have hxacc : x < acc.length := hlt x (by simp)
      have hxnx : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hlt' : ∀ y ∈ xs, y < (acc.set x (s.getD i 0)).length := by
        intro y hy
        rw [List.length_set]
        exact hlt y (by simp [hy])
      rw [k0pAct.go.eq_2]
      cases k with
      | zero =>
          rw [List.getD_cons_zero, k0patAct_go_getD_not_mem s xs (i + 1) _ x hxnx,
            k0patAct_getD_set_self hxacc, Nat.add_zero]
      | succ k =>
          rw [List.getD_cons_succ,
            ih (i + 1) (acc.set x (s.getD i 0)) hnd' hlt' k (by simpa using hk)]
          congr 1
          omega

theorem k0patAct_eq_iff_of_perm {a s : List ℕ} {N : ℕ} (ha : k0patPerm a N) (hs : s.length = N) :
    k0pAct a s = s ↔ ∀ i < a.length, s.getD (a.getD i 0) 0 = s.getD i 0 := by
  obtain ⟨hnd, hlen, hlt⟩ := ha
  have hle : ∀ x ∈ a, x < (List.replicate s.length 0).length := by
    intro x hx
    rw [List.length_replicate]
    have := hlt x hx
    omega
  constructor
  · intro hfix i hi
    have hmem := k0patAct_go_getD_mem s a 0 (List.replicate s.length 0) hnd hle i hi
    rw [← k0pAct] at hmem
    have h1 : s.getD (a.getD i 0) 0 = (k0pAct a s).getD (a.getD i 0) 0 := by rw [hfix]
    rw [h1, hmem, Nat.zero_add]
  · intro hpt
    have hlen' : (k0pAct a s).length = s.length := k0patAct_length a s
    refine List.ext_getElem hlen' (fun j hj hj' => ?_)
    rw [List.getElem_eq_getD (h := hj) 0, List.getElem_eq_getD (h := hj') 0]
    obtain ⟨i, hi, hia⟩ := k0patPerm_exists_getD ⟨hnd, hlen, hlt⟩ (j := j) (by omega)
    have hmem := k0patAct_go_getD_mem s a 0 (List.replicate s.length 0) hnd hle i hi
    rw [← k0pAct] at hmem
    have h1 : (k0pAct a s).getD j 0 = s.getD i 0 := by
      rw [← hia, hmem, Nat.zero_add]
    rw [h1, ← hia, hpt i hi]

theorem k0patAct_map (a s : List ℕ) (f : ℕ → ℕ) (hf : f 0 = 0) :
    k0pAct a (s.map f) = (k0pAct a s).map f := by
  have h : ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ),
      k0pAct.go (s.map f) i l (acc.map f) = (k0pAct.go s i l acc).map f := by
    intro l
    induction l with
    | nil =>
        intro i acc
        rw [k0pAct.go.eq_1, k0pAct.go.eq_1]
    | cons x xs ih =>
        intro i acc
        rw [k0pAct.go.eq_2, k0pAct.go.eq_2, k0patAct_getD_map f hf, ← List.map_set, ih]
  rw [k0pAct, k0pAct, List.length_map]
  have hrep : List.map f (List.replicate s.length 0) = List.replicate s.length 0 := by
    rw [List.map_replicate, hf]
  have hgoal := h a 0 (List.replicate s.length 0)
  rwa [hrep] at hgoal

theorem k0pat_foldl_gcd_dvd (l : List ℕ) (f : ℕ → ℕ) (g : ℕ) :
    l.foldl (fun g i => Nat.gcd g (f i)) g ∣ g ∧
      ∀ i ∈ l, l.foldl (fun g i => Nat.gcd g (f i)) g ∣ f i := by
  induction l generalizing g with
  | nil => simpa using (dvd_refl g)
  | cons a l ih =>
      have h := ih (Nat.gcd g (f a))
      rw [List.foldl_cons]
      refine ⟨h.1.trans (Nat.gcd_dvd_left g (f a)), ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact h.1.trans (Nat.gcd_dvd_right g (f i))
      · exact h.2 i hi

end CFSG.StandardType

end
