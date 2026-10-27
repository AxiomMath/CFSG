module

public import CFSG.Sporadic.Schreier.LyBFS
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.LySchreier

variable {M : Type*} [DecidableEq M]

@[expose] def appendImages (x : M) (gs : List (M → M)) (L : List M) : List M :=
  gs.foldl (fun L' g => if g x ∈ L' then L' else L' ++ [g x]) L

theorem appendImages_nil (x : M) (L : List M) : appendImages x [] L = L := rfl

theorem appendImages_cons (x : M) (g : M → M) (gs : List (M → M)) (L : List M) :
    appendImages x (g :: gs) L =
      appendImages x gs (if g x ∈ L then L else L ++ [g x]) := rfl

theorem appendImages_isPrefix (x : M) (gs : List (M → M)) (L : List M) :
    L <+: appendImages x gs L := by
  induction gs generalizing L with
  | nil => exact List.prefix_refl L
  | cons g gs ih =>
    rw [appendImages_cons]
    refine List.IsPrefix.trans ?_ (ih _)
    split_ifs
    · exact List.prefix_refl L
    · exact List.prefix_append L _

theorem appendImages_nodup (x : M) (gs : List (M → M)) {L : List M} (hL : L.Nodup) :
    (appendImages x gs L).Nodup := by
  induction gs generalizing L with
  | nil => exact hL
  | cons g gs ih =>
    rw [appendImages_cons]
    apply ih
    split_ifs with h
    · exact hL
    · exact List.nodup_append.2 ⟨hL, List.nodup_singleton _, by
        intro a ha b hb
        rw [List.mem_singleton] at hb
        rintro rfl
        exact h (hb ▸ ha)⟩

theorem mem_appendImages (x : M) (gs : List (M → M)) (L : List M) {g : M → M} (hg : g ∈ gs) :
    g x ∈ appendImages x gs L := by
  induction gs generalizing L with
  | nil => exact absurd hg List.not_mem_nil
  | cons g' gs ih =>
    rw [appendImages_cons]
    rcases List.mem_cons.1 hg with rfl | hg
    · refine (appendImages_isPrefix x gs _).subset ?_
      split_ifs with h
      · exact h
      · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ih _ hg

theorem mem_of_mem_appendImages (x : M) (gs : List (M → M)) (L : List M) {y : M}
    (hy : y ∈ appendImages x gs L) : y ∈ L ∨ ∃ g ∈ gs, y = g x := by
  induction gs generalizing L with
  | nil => exact Or.inl hy
  | cons g gs ih =>
    rw [appendImages_cons] at hy
    rcases ih _ hy with h | ⟨g', hg', rfl⟩
    · split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨g, List.mem_cons_self, List.mem_singleton.1 h⟩
    · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', rfl⟩

theorem IsPrefix.getElem?_some {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ} {a : α}
    (hi : l₁[i]? = some a) : l₂[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  have hlt : i < l₁.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hi
    exact absurd hi (by simp)
  rw [List.getElem?_append_left hlt]
  exact hi

theorem getElem?_appendImages_of_le (x : M) (gs : List (M → M)) (L : List M) {j : ℕ} {y : M}
    (hj : (appendImages x gs L)[j]? = some y) (hLj : L.length ≤ j) :
    ∃ (k : ℕ) (g : M → M), gs[k]? = some g ∧ g x = y := by
  induction gs generalizing L with
  | nil =>
    rw [appendImages_nil, List.getElem?_eq_none (by omega)] at hj
    exact absurd hj (by simp)
  | cons g gs ih =>
    rw [appendImages_cons] at hj
    by_cases hmem : g x ∈ L
    · rw [ite_eq_left hmem] at hj
      obtain ⟨k, g', hk, he⟩ := ih L hj hLj
      exact ⟨k + 1, g', by rw [List.getElem?_cons_succ]; exact hk, he⟩
    · rw [ite_eq_right hmem] at hj
      by_cases hj' : (L ++ [g x]).length ≤ j
      · obtain ⟨k, g', hk, he⟩ := ih (L ++ [g x]) hj hj'
        exact ⟨k + 1, g', by rw [List.getElem?_cons_succ]; exact hk, he⟩
      · have hjL : j = L.length := by simp at hj'; omega
        refine ⟨0, g, rfl, ?_⟩
        have hpre := appendImages_isPrefix x gs (L ++ [g x])
        have h1 : (L ++ [g x])[j]? = some (g x) := by simp [hjL]
        rw [IsPrefix.getElem?_some hpre h1] at hj
        exact Option.some_injective _ hj

variable (gs : List (M → M)) (root : M)

theorem bfsVisit_eq_of_lt {i : ℕ} {L : List M} (h : i < L.length) :
    bfsVisit gs i L = appendImages L[i] gs L := by
  rw [bfsVisit, dite_eq_left h]
  rfl

theorem bfsVisit_eq_of_le {i : ℕ} {L : List M} (h : L.length ≤ i) : bfsVisit gs i L = L := by
  rw [bfsVisit, dite_eq_right (by omega)]

theorem bfsVisit_isPrefix (i : ℕ) (L : List M) : L <+: bfsVisit gs i L := by
  by_cases h : i < L.length
  · rw [bfsVisit_eq_of_lt gs h]
    exact appendImages_isPrefix _ _ _
  · rw [bfsVisit_eq_of_le gs (by omega)]

theorem bfsList_isPrefix_succ (N : ℕ) : bfsList gs root N <+: bfsList gs root (N + 1) := by
  rw [bfsList_succ]
  exact bfsVisit_isPrefix gs _ _

theorem bfsList_isPrefix {N N' : ℕ} (h : N ≤ N') : bfsList gs root N <+: bfsList gs root N' := by
  induction N', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ N' _ ih => exact ih.trans (bfsList_isPrefix_succ gs root N')

theorem bfsList_nodup (N : ℕ) : (bfsList gs root N).Nodup := by
  induction N with
  | zero => exact List.nodup_singleton root
  | succ N ih =>
    rw [bfsList_succ]
    by_cases h : N < (bfsList gs root N).length
    · rw [bfsVisit_eq_of_lt gs h]
      exact appendImages_nodup _ _ ih
    · rw [bfsVisit_eq_of_le gs (by omega)]
      exact ih

theorem bfsList_getElem?_zero (N : ℕ) : (bfsList gs root N)[0]? = some root :=
  IsPrefix.getElem?_some (bfsList_isPrefix gs root (Nat.zero_le N)) (by simp [bfsList_zero])

theorem bfsList_length_pos (N : ℕ) : 0 < (bfsList gs root N).length := by
  have h := bfsList_getElem?_zero gs root N
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem root_mem_bfsList (N : ℕ) : root ∈ bfsList gs root N :=
  List.mem_of_getElem? (bfsList_getElem?_zero gs root N)

theorem bfsList_exists_disc (N : ℕ) {j : ℕ} {y : M} (hj : (bfsList gs root N)[j]? = some y)
    (h1 : 1 ≤ j) : ∃ p < j, ∃ (k : ℕ) (g : M → M) (z : M), gs[k]? = some g ∧
      (bfsList gs root N)[p]? = some z ∧ g z = y := by
  induction N generalizing j y with
  | zero =>
    rw [bfsList_zero] at hj
    rcases j with _ | j
    · omega
    · simp at hj
  | succ N ih =>
    have hpre := bfsList_isPrefix_succ gs root N
    by_cases hjN : j < (bfsList gs root N).length
    · obtain ⟨y', hy'⟩ : ∃ y', (bfsList gs root N)[j]? = some y' :=
        ⟨_, List.getElem?_eq_getElem hjN⟩
      have hyy : y' = y := Option.some_injective _ ((IsPrefix.getElem?_some hpre hy').symm.trans hj)
      subst hyy
      obtain ⟨p, hp, k, g, z, hk, hz, he⟩ := ih hy' h1
      exact ⟨p, hp, k, g, z, hk, IsPrefix.getElem?_some hpre hz, he⟩
    · have hvis : N < (bfsList gs root N).length := by
        by_contra hc
        rw [bfsList_succ, bfsVisit_eq_of_le gs (by omega)] at hj
        rw [List.getElem?_eq_none (by omega)] at hj
        exact absurd hj (by simp)
      rw [bfsList_succ, bfsVisit_eq_of_lt gs hvis] at hj
      obtain ⟨k, g, hk, he⟩ := getElem?_appendImages_of_le _ gs _ hj (by omega)
      refine ⟨N, by omega, k, g, (bfsList gs root N)[N], hk, ?_, he⟩
      exact IsPrefix.getElem?_some hpre (List.getElem?_eq_getElem hvis)

theorem bfsList_mem_of_closed {S : Set M} (hroot : root ∈ S) (hS : ∀ g ∈ gs, ∀ x ∈ S, g x ∈ S)
    (N : ℕ) : ∀ y ∈ bfsList gs root N, y ∈ S := by
  induction N with
  | zero =>
    intro y hy
    rw [bfsList_zero, List.mem_singleton] at hy
    exact hy ▸ hroot
  | succ N ih =>
    intro y hy
    rw [bfsList_succ] at hy
    by_cases h : N < (bfsList gs root N).length
    · rw [bfsVisit_eq_of_lt gs h] at hy
      rcases mem_of_mem_appendImages _ gs _ hy with hy | ⟨g, hg, rfl⟩
      · exact ih y hy
      · exact hS g hg _ (ih _ (List.getElem_mem h))
    · rw [bfsVisit_eq_of_le gs (by omega)] at hy
      exact ih y hy

theorem bfsList_images_mem (N : ℕ) {i : ℕ} (hiN : i < N) {z : M}
    (hz : (bfsList gs root N)[i]? = some z) {g : M → M} (hg : g ∈ gs) :
    g z ∈ bfsList gs root N := by
  induction N generalizing i z with
  | zero => omega
  | succ N ih =>
    have hpre := bfsList_isPrefix_succ gs root N
    by_cases hiN' : i < N
    · by_cases hi' : i < (bfsList gs root N).length
      · have hz' : (bfsList gs root N)[i]? = some (bfsList gs root N)[i] :=
          List.getElem?_eq_getElem hi'
        have hzz : (bfsList gs root N)[i] = z :=
          Option.some_injective _ ((IsPrefix.getElem?_some hpre hz').symm.trans hz)
        rw [← hzz]
        exact hpre.subset (ih hiN' hz')
      · have hlen : (bfsList gs root N).length ≤ N := by omega
        rw [bfsList_succ, bfsVisit_eq_of_le gs hlen] at hz ⊢
        rw [List.getElem?_eq_none (by omega)] at hz
        exact absurd hz (by simp)
    · have hiN'' : i = N := by omega
      subst hiN''
      have hvis : i < (bfsList gs root i).length := by
        by_contra hc
        rw [bfsList_succ, bfsVisit_eq_of_le gs (by omega), List.getElem?_eq_none (by omega)] at hz
        exact absurd hz (by simp)
      have hzz : (bfsList gs root i)[i] = z := Option.some_injective _
        ((IsPrefix.getElem?_some hpre (List.getElem?_eq_getElem hvis)).symm.trans hz)
      rw [bfsList_succ, bfsVisit_eq_of_lt gs hvis, hzz]
      exact mem_appendImages _ gs _ hg

theorem bfsList_closed {N : ℕ} (hN : (bfsList gs root N).length ≤ N) {g : M → M} (hg : g ∈ gs)
    {y : M} (hy : y ∈ bfsList gs root N) : g y ∈ bfsList gs root N := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact bfsList_images_mem gs root N (by omega) (List.getElem?_eq_getElem hi) hg

theorem bfsList_stable {N : ℕ} (hN : (bfsList gs root N).length ≤ N) {N' : ℕ} (h : N ≤ N') :
    bfsList gs root N' = bfsList gs root N := by
  induction N', h using Nat.le_induction with
  | base => rfl
  | succ N' hle ih =>
    rw [bfsList_succ, ih, bfsVisit_eq_of_le gs (by omega)]

omit [DecidableEq M] in
theorem length_le_ncard_of_subset {L : List M} (hL : L.Nodup) {S : Set M} (hS : S.Finite)
    (h : ∀ y ∈ L, y ∈ S) : L.length ≤ S.ncard := by
  classical
  rw [← List.toFinset_card_of_nodup hL]
  have hsub : (L.toFinset : Set M) ⊆ S := fun y hy => h y (List.mem_toFinset.1 hy)
  calc L.toFinset.card = (L.toFinset : Set M).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub hS

theorem bfsList_length_le {S : Set M} (hS : S.Finite) (hroot : root ∈ S)
    (hclosed : ∀ g ∈ gs, ∀ x ∈ S, g x ∈ S) {N : ℕ} (hN : S.ncard ≤ N) :
    (bfsList gs root N).length ≤ N :=
  (length_le_ncard_of_subset (bfsList_nodup gs root N) hS
    (bfsList_mem_of_closed gs root hroot hclosed N)).trans hN

section Orbit

variable {G Y : Type*} [Group G] [MulAction G Y] [DecidableEq Y]

theorem bfsList_orbit {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (y₀ : Y)
    (hfin : (MulAction.orbit G y₀).Finite) {N : ℕ} (hN : (MulAction.orbit G y₀).ncard ≤ N) :
    (bfsList [fun y => a • y, fun y => b • y] y₀ N).Nodup ∧
      (∀ y, y ∈ bfsList [fun y => a • y, fun y => b • y] y₀ N ↔ y ∈ MulAction.orbit G y₀) ∧
      (bfsList [fun y => a • y, fun y => b • y] y₀ N).length ≤ N := by
  set gs : List (Y → Y) := [fun y => a • y, fun y => b • y] with hgs
  have hclosedO : ∀ g ∈ gs, ∀ x ∈ MulAction.orbit G y₀, g x ∈ MulAction.orbit G y₀ := by
    intro g hg x hx
    simp only [hgs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact MulAction.mem_orbit_of_mem_orbit a hx
    · exact MulAction.mem_orbit_of_mem_orbit b hx
  have hsub := bfsList_mem_of_closed gs y₀ (MulAction.mem_orbit_self y₀) hclosedO N
  have hlen := bfsList_length_le gs y₀ hfin (MulAction.mem_orbit_self y₀) hclosedO hN
  refine ⟨bfsList_nodup gs y₀ N, fun y => ⟨hsub y, ?_⟩, hlen⟩
  rintro ⟨g, rfl⟩
  have hS : {y | y ∈ bfsList gs y₀ N}.Finite := (bfsList gs y₀ N).finite_toSet
  exact CFSG.Sporadic.Th.smul_mem_of_closure hgen hS
    (fun y hy => bfsList_closed gs y₀ hlen (by simp [hgs]) hy)
    (fun y hy => bfsList_closed gs y₀ hlen (by simp [hgs]) hy) g y₀ (root_mem_bfsList gs y₀ N)

end Orbit

section Disc

variable (L : List M)

@[expose] def IsDisc (j d : ℕ) : Prop :=
  ∃ (p k : ℕ) (g : M → M) (z : M), d = p * gs.length + k ∧ k < gs.length ∧ gs[k]? = some g ∧
    L[p]? = some z ∧ L[j]? = some (g z)

open Classical in
@[expose] noncomputable def firstDisc (j : ℕ) : ℕ :=
  if h : ∃ d, IsDisc gs L j d then Nat.find h else 0

omit [DecidableEq M] in
theorem firstDisc_spec {j : ℕ} (h : ∃ d, IsDisc gs L j d) : IsDisc gs L j (firstDisc gs L j) := by
  classical
  rw [firstDisc, dite_eq_left h]
  exact Nat.find_spec h

omit [DecidableEq M] in
theorem firstDisc_le {j d : ℕ} (h : IsDisc gs L j d) : firstDisc gs L j ≤ d := by
  classical
  rw [firstDisc, dite_eq_left ⟨d, h⟩]
  exact Nat.find_min' _ h

@[expose] noncomputable def discParent (j : ℕ) : ℕ := firstDisc gs L j / gs.length

@[expose] noncomputable def discGen (j : ℕ) : ℕ := firstDisc gs L j % gs.length

omit [DecidableEq M] in
theorem isDisc_div_mod {j d : ℕ} (h : IsDisc gs L j d) :
    ∃ (g : M → M) (z : M), gs[d % gs.length]? = some g ∧ L[d / gs.length]? = some z ∧
      L[j]? = some (g z) := by
  obtain ⟨p, k, g, z, hd, hk, hg, hz, hj⟩ := h
  have hK : 0 < gs.length := by omega
  have h1 : d / gs.length = p := by
    rw [hd, Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hk, zero_add]
  have h2 : d % gs.length = k := by
    rw [hd, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  rw [h1, h2]
  exact ⟨g, z, hg, hz, hj⟩

omit [DecidableEq M] in
theorem discParent_spec {j : ℕ} (h : ∃ d, IsDisc gs L j d) :
    ∃ (g : M → M) (z : M), gs[discGen gs L j]? = some g ∧ L[discParent gs L j]? = some z ∧
      L[j]? = some (g z) :=
  isDisc_div_mod gs L (firstDisc_spec gs L h)

omit [DecidableEq M] in
theorem discGen_lt {j : ℕ} (h : ∃ d, IsDisc gs L j d) : discGen gs L j < gs.length := by
  obtain ⟨g, -, hg, -⟩ := discParent_spec gs L h
  exact (List.getElem?_eq_some_iff.1 hg).1

end Disc

theorem bfsList_exists_isDisc (N : ℕ) {j : ℕ} {y : M} (hj : (bfsList gs root N)[j]? = some y)
    (h1 : 1 ≤ j) : ∃ d, IsDisc gs (bfsList gs root N) j d := by
  obtain ⟨p, hp, k, g, z, hk, hz, he⟩ := bfsList_exists_disc gs root N hj h1
  exact ⟨p * gs.length + k, p, k, g, z, rfl, (List.getElem?_eq_some_iff.1 hk).1, hk, hz,
    he ▸ hj⟩

theorem bfsList_discParent_lt (N : ℕ) {j : ℕ} {y : M} (hj : (bfsList gs root N)[j]? = some y)
    (h1 : 1 ≤ j) : discParent gs (bfsList gs root N) j < j := by
  obtain ⟨p, hp, k, g, z, hk, hz, he⟩ := bfsList_exists_disc gs root N hj h1
  have hk' : k < gs.length := (List.getElem?_eq_some_iff.1 hk).1
  have hle := firstDisc_le gs (bfsList gs root N) (d := p * gs.length + k)
    ⟨p, k, g, z, rfl, hk', hk, hz, he ▸ hj⟩
  have hK : 0 < gs.length := by omega
  unfold discParent
  calc firstDisc gs (bfsList gs root N) j / gs.length ≤ (p * gs.length + k) / gs.length :=
        Nat.div_le_div_right hle
    _ = p := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hk', zero_add]
    _ < j := hp

end CFSG.Sporadic.ThSchreier
