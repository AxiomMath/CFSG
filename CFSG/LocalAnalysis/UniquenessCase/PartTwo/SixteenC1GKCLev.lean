module

public import CFSG.LargeExtraspecial.O62Rank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

@[expose] def s16c1cInvs : List ℕ := ((sylowWords true).map wordC).filter isInv

@[expose] def s16c1cIns (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: s16c1cIns x ys

@[expose] def s16c1cSort : List ℕ → List ℕ
  | [] => []
  | x :: xs => s16c1cIns x (s16c1cSort xs)

@[expose] def s16c1cExt (H : List ℕ) (x : ℕ) : List ℕ := H ++ H.map fun h => mul h x

@[expose] def s16c1cGood (H : List ℕ) (x : ℕ) : Bool := (H.all fun h => comm h x) && !H.contains x

@[expose] def s16c1cStep (Ls : List (List ℕ)) : List (List ℕ) :=
  (Ls.flatMap fun H => (s16c1cInvs.filter (s16c1cGood H)).map fun x =>
    s16c1cSort (s16c1cExt H x)).eraseDups

@[expose] def s16c1cLev : ℕ → List (List ℕ)
  | 0 => [[one]]
  | k + 1 => s16c1cStep (s16c1cLev k)

@[expose] def s16c1cIndep : List (V₀ ≃ₗ[ZMod 2] V₀) → Prop
  | [] => True
  | x :: xs => x ∉ spanG xs ∧ s16c1cIndep xs

theorem s16c1cIns_eq (x : ℕ) (l : List ℕ) : s16c1cIns x l = l.orderedInsert (· ≤ ·) x := by
  induction l with
  | nil => simp [s16c1cIns]
  | cons y ys ih =>
    simp only [s16c1cIns, List.orderedInsert_cons]
    split_ifs <;> simp [ih]

theorem s16c1cSort_eq (l : List ℕ) : s16c1cSort l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => simp [s16c1cSort]
  | cons x xs ih => simp [s16c1cSort, List.insertionSort_cons, ih, s16c1cIns_eq]

theorem s16c1cSort_perm (l : List ℕ) : (s16c1cSort l).Perm l := by
  rw [s16c1cSort_eq]
  exact List.perm_insertionSort _ l

theorem s16c1cSort_eq_of_perm {l l' : List ℕ} (h : l.Perm l') : s16c1cSort l = s16c1cSort l' := by
  rw [s16c1cSort_eq, s16c1cSort_eq]
  exact List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _)
    (List.pairwise_insertionSort _ _)
    ((List.perm_insertionSort _ l).trans (h.trans (List.perm_insertionSort _ l').symm))

theorem s16c1c_lev_five : s16c1cLev 5 = [] := by
  decide +kernel

theorem s16c1c_mem_lev_succ {k : ℕ} {H : List ℕ} (hH : H ∈ s16c1cLev k) {x : ℕ}
    (hx : x ∈ s16c1cInvs) (hg : s16c1cGood H x = true) :
    s16c1cSort (s16c1cExt H x) ∈ s16c1cLev (k + 1) := by
  show _ ∈ s16c1cStep (s16c1cLev k)
  unfold s16c1cStep
  rw [List.mem_eraseDups, List.mem_flatMap]
  exact ⟨H, hH, List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, hg⟩, rfl⟩⟩

theorem s16c1c_coded_apply {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} (hx : Coded x c) (n : ℕ) :
    x (vec n) = vec (act c n) := by
  have h := hx.1
  rw [vec_act, ← h, LinearMap.toMatrix'_mulVec]
  rfl

theorem s16c1c_forall₂_exists_right {xs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded xs cs) {c : ℕ} (hc : c ∈ cs) : ∃ x ∈ xs, Coded x c := by
  induction h with
  | nil => simp at hc
  | cons hab _ ih =>
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, hxc⟩ := ih hc
      exact ⟨x, List.mem_cons_of_mem _ hx, hxc⟩

theorem s16c1c_forall₂_exists_left {xs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded xs cs) {x : V₀ ≃ₗ[ZMod 2] V₀} (hx : x ∈ xs) :
    ∃ c ∈ cs, Coded x c := by
  induction h with
  | nil => simp at hx
  | cons hab _ ih =>
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨c, hc, hxc⟩ := ih hx
      exact ⟨c, List.mem_cons_of_mem _ hc, hxc⟩

theorem s16c1c_lev_chain {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1)
    (hcode : ∀ x ∈ P, ∃ c ∈ (sylowWords true).map wordC, Coded x c) :
    ∀ (xs : List (V₀ ≃ₗ[ZMod 2] V₀)) (cs : List ℕ), (∀ x ∈ xs, x ∈ P) →
      List.Forall₂ Coded xs cs → s16c1cIndep xs → s16c1cSort (spanC cs) ∈ s16c1cLev xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro cs _ hF _
    cases hF
    simp [spanC, s16c1cSort, s16c1cIns, s16c1cLev]
  | cons x xs ih =>
    intro cs hP hF hI
    cases hF with
    | cons hc hF' =>
      rename_i c cs'
      have hxP : x ∈ P := hP x List.mem_cons_self
      have hxsP : ∀ y ∈ xs, y ∈ P := fun y hy => hP y (List.mem_cons_of_mem _ hy)
      have ih' := ih cs' hxsP hF' hI.2
      have hperm : (s16c1cSort (spanC cs')).Perm (spanC cs') := s16c1cSort_perm _
      have hx_ne : x ∉ spanG xs := hI.1
      have hcinv : c ∈ s16c1cInvs := by
        obtain ⟨c', hc'mem, hc'⟩ := hcode x hxP
        have : c' = c := (hc'.eq_iff hc).mp rfl
        subst this
        exact List.mem_filter.2 ⟨hc'mem, isInv_of_coded hc (h2 x hxP)
          (fun h => hx_ne (h ▸ one_mem_spanG xs))⟩
      have hgood : s16c1cGood (s16c1cSort (spanC cs')) c = true := by
        unfold s16c1cGood
        rw [Bool.and_eq_true]
        constructor
        · rw [List.all_eq_true]
          intro h hh
          have hh' : h ∈ spanC cs' := hperm.subset hh
          obtain ⟨y, hy, hyc⟩ := s16c1c_forall₂_exists_right (forall₂_spanG hF') hh'
          have hyP : y ∈ P := spanG_subset hxsP y hy
          exact comm_of_coded hyc hc (hab y hyP x hxP)
        · have hn : c ∉ spanC cs' := not_mem_spanC_of_coded hF' hc hx_ne
          have hn' : c ∉ s16c1cSort (spanC cs') := fun h => hn (hperm.subset h)
          simpa using hn'
      have hmem := s16c1c_mem_lev_succ ih' hcinv hgood
      have heq : s16c1cSort (spanC (c :: cs')) =
          s16c1cSort (s16c1cExt (s16c1cSort (spanC cs')) c) := by
        apply s16c1cSort_eq_of_perm
        exact hperm.symm.append (hperm.symm.map _)
      rw [heq]
      exact hmem

theorem s16c1c_exists_chain {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} :
    ∀ k : ℕ, 2 ^ k < Nat.card P → ∃ xs : List (V₀ ≃ₗ[ZMod 2] V₀), xs.length = k + 1 ∧
      (∀ x ∈ xs, x ∈ P) ∧ s16c1cIndep xs := by
  have := finite_linearEquiv (V := V₀)
  intro k
  induction k with
  | zero =>
    intro h
    obtain ⟨x, hx, hn⟩ := exists_mem_not_mem_spanG (P := P) [] (by simpa using h)
    exact ⟨[x], rfl, by simpa using hx, hn, trivial⟩
  | succ k ih =>
    intro h
    have h' : 2 ^ k < Nat.card P :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) h
    obtain ⟨xs, hlen, hP, hI⟩ := ih h'
    obtain ⟨y, hy, hn⟩ := exists_mem_not_mem_spanG (P := P) xs (by rw [hlen]; exact h)
    refine ⟨y :: xs, by simp [hlen], ?_, hn, hI⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hy
    · exact hP z hz

theorem s16c1c_exists_forall₂ {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hcode : ∀ x ∈ P, ∃ c ∈ (sylowWords true).map wordC, Coded x c) :
    ∀ xs : List (V₀ ≃ₗ[ZMod 2] V₀), (∀ x ∈ xs, x ∈ P) → ∃ cs, List.Forall₂ Coded xs cs := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨[], .nil⟩
  | cons x xs ih =>
    intro h
    obtain ⟨c, -, hc⟩ := hcode x (h x List.mem_cons_self)
    obtain ⟨cs, hcs⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨c :: cs, .cons hc hcs⟩

theorem s16c1c_card_le_of_codes {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1)
    (hcode : ∀ x ∈ P, ∃ c ∈ (sylowWords true).map wordC, Coded x c) : Nat.card P ≤ 16 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨xs, hlen, hP, hI⟩ := s16c1c_exists_chain (P := P) 4 (by norm_num; omega)
  obtain ⟨cs, hF⟩ := s16c1c_exists_forall₂ hcode xs hP
  have h := s16c1c_lev_chain hab h2 hcode xs cs hP hF hI
  rw [hlen, s16c1c_lev_five] at h
  exact List.not_mem_nil h

theorem s16c1c_describe {P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (h2 : ∀ x ∈ P, x ^ 2 = 1)
    (hcode : ∀ x ∈ P, ∃ c ∈ (sylowWords true).map wordC, Coded x c) (hcard : Nat.card P = 16) :
    ∃ H ∈ s16c1cLev 4, (∀ y ∈ P, ∃ c ∈ H, Coded y c) ∧ (∀ c ∈ H, ∃ y ∈ P, Coded y c) := by
  obtain ⟨xs, hlen, hP, hI⟩ := s16c1c_exists_chain (P := P) 3 (by rw [hcard]; norm_num)
  obtain ⟨cs, hF⟩ := s16c1c_exists_forall₂ hcode xs hP
  have hmem := s16c1c_lev_chain hab h2 hcode xs cs hP hF hI
  rw [hlen] at hmem
  refine ⟨_, hmem, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ spanG xs := by
      by_contra hn
      obtain ⟨cy, -, hcy⟩ := hcode y hy
      have hP' : ∀ z ∈ y :: xs, z ∈ P := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hy
        · exact hP z hz
      have h5 := s16c1c_lev_chain hab h2 hcode (y :: xs) (cy :: cs) hP' (.cons hcy hF) ⟨hn, hI⟩
      rw [List.length_cons, hlen, s16c1c_lev_five] at h5
      exact List.not_mem_nil h5
    obtain ⟨c, hc, hyc⟩ := s16c1c_forall₂_exists_left (forall₂_spanG hF) hy'
    exact ⟨c, (s16c1cSort_perm _).symm.subset hc, hyc⟩
  · intro c hc
    have hc' := (s16c1cSort_perm _).subset hc
    obtain ⟨y, hy, hyc⟩ := s16c1c_forall₂_exists_right (forall₂_spanG hF) hc'
    exact ⟨y, spanG_subset hP y hy, hyc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
