module

public import CFSG.Sporadic.SmallOddCore.CentData
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

variable {n : ℕ}

noncomputable abbrev tp (n : ℕ) (T : Table) : Equiv.Perm (Fin n) :=
  CFSG.Monster.B.Co2.permOfArr n (natArr T)

theorem rep_tp {T : Table} (h : permOK n T = true) : Rep n T (tp n T) := rep_permOfArr_natArr h

theorem rep_invT {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g)
    (h : invOK n T (invT n T) = true) : Rep n (invT n T) g⁻¹ :=
  Rep.inv_of_invOK hT h

theorem tblEq_iff_eq {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h) :
    tblEq n S T = true ↔ g = h := by
  constructor
  · intro e
    exact rep_unique hS (rep_of_tblEq hT e)
  · rintro rfl
    rw [tblEq_iff]
    intro i hi
    rw [hS i hi, hT i hi]

theorem tblEq_idT_iff (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    tblEq n T (idT n) = true ↔ g = 1 :=
  tblEq_iff_eq hT (Rep.idT hn)

theorem sq_eq_one_of_invoOK {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g)
    (h : invoOK n T = true) : g ^ 2 = 1 := by
  apply perm_faithful
  intro i
  apply Fin.ext
  have := idx_sq_of_invoOK hT h i.val i.2
  rw [idx_of_lt _ i.2] at this
  exact this

theorem orderOf_eq_two_of_involOK (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)}
    (hT : Rep n T g) (h : involOK n T = true) : orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [involOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine orderOf_eq_prime (sq_eq_one_of_invoOK hT h.1) fun h1 => ?_
  rw [(tblEq_idT_iff hn hT).2 h1] at h
  exact Bool.false_ne_true h.2.symm

theorem involOK_of_orderOf (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g)
    (h : orderOf g = 2) : involOK n T = true := by
  rw [involOK, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rw [invoOK, allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hT i hi, hT _ (idx_lt g hi), ← idx_mul, ← pow_two, ← h, pow_orderOf_eq_one,
      idx_one]
  · cases e : tblEq n T (idT n)
    · rfl
    · rw [(tblEq_idT_iff hn hT).1 e, orderOf_one] at h
      exact absurd h (by norm_num)

theorem commTT_iff {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h) :
    commTT n S T = true ↔ g * h = h * g :=
  tblEq_iff_eq (Rep.compT hS hT) (Rep.compT hT hS)

theorem ordTest_iff_perm {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) {m : ℕ}
    (hm : 0 < m) : ordTest n m T = true ↔ orderOf g = m :=
  ordTest_iff perm_faithful hT hm

theorem selOK_iff (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g)
    {ps : List ℕ} : selOK n ps T = true ↔ g ≠ 1 ∧ ∃ p ∈ ps, g ^ p = 1 := by
  rw [selOK, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true]
  refine and_congr ?_ (exists_congr fun p => and_congr Iff.rfl ?_)
  · constructor
    · intro h e
      rw [(tblEq_idT_iff hn hT).2 e] at h
      exact Bool.false_ne_true h.symm
    · intro h
      cases e : tblEq n T (idT n)
      · rfl
      · exact absurd ((tblEq_idT_iff hn hT).1 e) h
  · exact tblEq_idT_iff hn (Rep.powT hn hT p)

structure GroupData (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n))) (pg : Array Table)
    (gg : ℕ → Equiv.Perm (Fin n)) (sift : Table → Bool) : Prop where
  lt : n < 2 ^ 32
  rep : ∀ l < pg.size, Rep n pg[l]! (gg l)
  gen : P = closure (gg '' {l | l < pg.size})
  sift : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → (sift T = true ↔ g ∈ P)

variable {P : Subgroup (Equiv.Perm (Fin n))} {pg pgInv : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

theorem GroupData.mem (hD : GroupData n P pg gg sift) {l : ℕ} (hl : l < pg.size) : gg l ∈ P := by
  rw [hD.gen]
  exact subset_closure ⟨l, hl, rfl⟩

theorem GroupData.conj_mem (hD : GroupData n P pg gg sift) {U : Equiv.Perm (Fin n)}
    (hU : ∀ l < pg.size, U * gg l * U⁻¹ ∈ P) : ∀ p ∈ P, U * p * U⁻¹ ∈ P := by
  have hle : P.map (MulAut.conj U).toMonoidHom ≤ P := by
    conv_lhs => rw [hD.gen]
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact hU l hl
  intro p hp
  exact hle ⟨p, hp, rfl⟩

theorem mem_R_of_sift (hD : GroupData n P pg gg sift) {U : Equiv.Perm (Fin n)} (hU2 : U ^ 2 = 1)
    (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P) {u x : Table} (hu : Rep n u U) {g : Equiv.Perm (Fin n)}
    (hx : Rep n x g) (h : (sift x || sift (compT n x u)) = true) : g ∈ P ⊔ zpowers U := by
  rw [mem_sup_zpowers_iff hU2 hUn]
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl ((hD.sift x g hx).1 h)
  · exact Or.inr ((hD.sift _ _ (Rep.compT hx hu)).1 h)

theorem getElem!_mem_array {A : Array Table} {l : ℕ} (hl : l < A.size) : A[l]! ∈ A := by
  rw [getElem!_pos A l hl]
  exact Array.getElem_mem hl

theorem enum_spec (hn : n < 2 ^ 32) {A : Array Table} (hg : ∀ x ∈ A, permOK n x = true)
    (hginv : ∀ x ∈ A, invOK n x (invT n x) = true) {cap : ℕ}
    (htree : mulTreeOK n A (mulClosureH n A cap).1 (mulClosureH n A cap).2.1
      (mulClosureH n A cap).2.2 = true)
    (hclosed : closedOK n (A ++ A.map (invT n)) (mulClosureH n A cap).1 = true)
    (hdist : hkeysDistinct n (mulClosureH n A cap).1.toList = true) :
    (∀ k < (mulClosureH n A cap).1.size,
        Rep n (mulClosureH n A cap).1[k]! (tablePerm n (mulClosureH n A cap).1[k]!) ∧
        tablePerm n (mulClosureH n A cap).1[k]! ∈ closure (tp n '' {x | x ∈ A})) ∧
      (∀ x ∈ closure (tp n '' {x | x ∈ A}), ∃ k < (mulClosureH n A cap).1.size,
        Rep n (mulClosureH n A cap).1[k]! x) ∧
      Nat.card ↥(closure (tp n '' {x | x ∈ A})) = (mulClosureH n A cap).1.size := by
  set E := (mulClosureH n A cap).1
  set K := closure (tp n '' {x | x ∈ A})
  have hga : ∀ l < A.size, Rep n A[l]! (tp n A[l]!) ∧ tp n A[l]! ∈ K := fun l hl =>
    ⟨rep_tp (hg _ (getElem!_mem_array hl)), subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hE := mulTreeOK_spec hn K (gg := fun l => tp n A[l]!) hga htree
  have hErep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!) ∧ tablePerm n E[k]! ∈ K := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hE k hk
    rw [tablePerm_eq hrep]
    exact ⟨hrep, hc⟩
  let gg' : ℕ → Equiv.Perm (Fin n) := fun l =>
    if l < A.size then tp n A[l]! else (tp n A[l - A.size]!)⁻¹
  have hall : (A ++ A.map (invT n)).size = 2 * A.size := by simp [two_mul]
  have hgall : ∀ l < (A ++ A.map (invT n)).size, Rep n (A ++ A.map (invT n))[l]! (gg' l) := by
    intro l hl
    rw [hall] at hl
    by_cases hl1 : l < A.size
    · simp only [gg', hl1, ite_true]
      rw [getElem!_pos _ l (by rw [hall]; omega), Array.getElem_append_left hl1,
        ← getElem!_pos A l hl1]
      exact (hga l hl1).1
    · simp only [gg', hl1, ite_false]
      have hl2 : l - A.size < A.size := by omega
      rw [getElem!_pos _ l (by rw [hall]; omega),
        Array.getElem_append_right (by omega)]
      simp only [Array.getElem_map]
      rw [← getElem!_pos A _ hl2]
      exact rep_invT (hga _ hl2).1 (hginv _ (getElem!_mem_array hl2))
  have hginv' : ∀ l < (A ++ A.map (invT n)).size,
      ∃ l' < (A ++ A.map (invT n)).size, gg' l' = (gg' l)⁻¹ := by
    intro l hl
    rw [hall] at hl ⊢
    by_cases hl1 : l < A.size
    · refine ⟨l + A.size, by omega, ?_⟩
      simp only [gg', hl1, ite_true, show ¬ (l + A.size < A.size) by omega, ite_false,
        Nat.add_sub_cancel]
    · refine ⟨l - A.size, by omega, ?_⟩
      simp only [gg', hl1, ite_false, show l - A.size < A.size by omega, ite_true, inv_inv]
  have h1 : ∃ k < E.size, tablePerm n E[k]! = 1 := by
    simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
    exact ⟨0, htree.1.1, tablePerm_eq (rep_of_tblEq (Rep.idT hn) htree.1.2)⟩
  have hcov := closedOK_spec hgall hginv' (fun k hk => (hErep k hk).1) h1 hclosed
  have hKeq : closure (gg' '' {l | l < (A ++ A.map (invT n)).size}) = K := by
    apply le_antisymm
    · rw [closure_le]
      rintro _ ⟨l, hl, rfl⟩
      simp only [Set.mem_ofPred_eq] at hl
      rw [hall] at hl
      by_cases hl1 : l < A.size
      · simp only [gg', hl1, ite_true]
        exact (hga l hl1).2
      · simp only [gg', hl1, ite_false]
        exact K.inv_mem (hga _ (by omega)).2
    · rw [closure_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, hl, rfl⟩ := Array.getElem_of_mem hx
      refine subset_closure ⟨l, show l < (A ++ A.map (invT n)).size by rw [hall]; omega, ?_⟩
      simp only [gg', hl, ite_true]
      rw [getElem!_pos A l hl]
  rw [hKeq] at hcov
  have hcov' : ∀ x ∈ K, ∃ k < E.size, Rep n E[k]! x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hcov x hx
    exact ⟨k, hk, (hErep k hk).1⟩
  refine ⟨hErep, hcov', ?_⟩
  have hrepL : List.Forall₂ (Rep n) E.toList (E.toList.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro T hT
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
    have := (hErep k hk).1
    rwa [getElem!_pos E k hk] at this
  have hnodup : (E.toList.map (tablePerm n)).Nodup := nodup_of_hkeysDistinct hrepL hdist
  have hcard := card_eq_length (fun g => g ∈ K) id Function.injective_id _ hnodup (by
    intro g
    simp only [List.mem_map, id]
    constructor
    · rintro ⟨T, hT, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
      have := (hErep k hk).2
      rw [getElem!_pos E k hk] at this
      exact ⟨_, this, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, hk, hrep⟩ := hcov' g hg
      refine ⟨E[k]!, ?_, tablePerm_eq hrep⟩
      rw [getElem!_pos E k hk]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hk))
  rw [List.length_map, Array.length_toList] at hcard
  rw [← hcard]

theorem sylowOK_spec (hD : GroupData n P pg gg sift) {cap : ℕ} {u : Table}
    {sylowGens : List Table} {sylowOrder : ℕ}
    (h : sylowOK n cap pg pgInv sift u sylowGens sylowOrder = true) :
    Rep n u (tp n u) ∧ Rep n (invT n u) (tp n u)⁻¹ ∧ (tp n u) ^ 2 = 1 ∧ tp n u ≠ 1 ∧
      tp n u ∉ P ∧ (∀ p ∈ P, tp n u * p * (tp n u)⁻¹ ∈ P) ∧
      (∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹) ∧ pg.size = pgInv.size ∧
      closure (tp n '' {x | x ∈ sylowGens.toArray}) ≤ P ⊔ zpowers (tp n u) ∧
      Nat.card ↥(closure (tp n '' {x | x ∈ sylowGens.toArray})) = sylowOrder ∧
      (∀ x ∈ closure (tp n '' {x | x ∈ sylowGens.toArray}),
        ∃ k < (mulClosureH n sylowGens.toArray cap).1.size,
          Rep n (mulClosureH n sylowGens.toArray cap).1[k]! x) := by
  have hn := hD.lt
  simp only [sylowOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu1, hu2⟩, hu3⟩, hu4⟩, -⟩, hsz⟩, hinv⟩, hconj⟩, hsg⟩, htree⟩, hclosed⟩,
    hdist⟩, hsize⟩ := h
  have hU := rep_tp hu1
  have hUi := rep_invT hU hu4
  have hord := orderOf_eq_two_of_involOK hn hU hu2
  have hU2 : (tp n u) ^ 2 = 1 := hord ▸ pow_orderOf_eq_one _
  have hU1 : tp n u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hUP : tp n u ∉ P := by
    intro hm
    rw [← hD.sift u _ hU] at hm
    rw [hm] at hu3
    exact Bool.noConfusion hu3
  have hUn : ∀ p ∈ P, tp n u * p * (tp n u)⁻¹ ∈ P := by
    apply hD.conj_mem
    intro l hl
    rw [Array.all_eq_true] at hconj
    have h1 := hconj l hl
    have hl' := hD.rep l hl
    rw [getElem!_pos pg l hl] at hl'
    exact (hD.sift _ _ (rep_conjT hU hUi hl')).1 h1
  have hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹ := by
    intro l hl
    have := allIn_eq_true.1 hinv l (Nat.zero_le _) hl
    exact Rep.inv_of_invOK (hD.rep l hl) this
  rw [Array.all_eq_true'] at hsg
  simp only [Bool.and_eq_true] at hsg
  have hg : ∀ x ∈ sylowGens.toArray, permOK n x = true := fun x hx => (hsg x hx).1.1
  have hginv : ∀ x ∈ sylowGens.toArray, invOK n x (invT n x) = true := fun x hx => (hsg x hx).1.2
  obtain ⟨-, hcov, hcard⟩ := enum_spec hn hg hginv htree hclosed hdist
  refine ⟨hU, hUi, hU2, hU1, hUP, hUn, hpgi, hsz, ?_, hcard.trans hsize, hcov⟩
  rw [closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact mem_R_of_sift hD hU2 hUn hU (rep_tp (hg x hx)) (hsg x hx).2

theorem length_le_card_of_nodup {K : Subgroup (Equiv.Perm (Fin n))} {L : List (Equiv.Perm (Fin n))}
    (hL : L.Nodup) (hK : ∀ x ∈ L, x ∈ K) : L.length ≤ Nat.card K := by
  classical
  have : L.length = (L.toFinset : Set (Equiv.Perm (Fin n))).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
  rw [this, show Nat.card K = (K : Set (Equiv.Perm (Fin n))).ncard from Nat.card_coe_set_eq _]
  exact Set.ncard_le_ncard (fun x hx => hK x (List.mem_toFinset.mp hx)) (Set.toFinite _)

theorem length_le_ncard_of_nodup {S : Set (Equiv.Perm (Fin n))} {L : List (Equiv.Perm (Fin n))}
    (hL : L.Nodup) (hS : ∀ x ∈ L, x ∈ S) : L.length ≤ S.ncard := by
  classical
  have : L.length = (L.toFinset : Set (Equiv.Perm (Fin n))).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
  rw [this]
  exact Set.ncard_le_ncard (fun x hx => hS x (List.mem_toFinset.mp hx)) (Set.toFinite _)

theorem mem_of_nodup_of_card_le {K : Subgroup (Equiv.Perm (Fin n))}
    {L : List (Equiv.Perm (Fin n))} (hL : L.Nodup) (hK : ∀ x ∈ L, x ∈ K)
    (hlen : Nat.card K ≤ L.length) : ∀ y ∈ K, y ∈ L := by
  classical
  have hsub : (L.toFinset : Set (Equiv.Perm (Fin n))) ⊆ K := fun x hx =>
    hK x (List.mem_toFinset.mp hx)
  have hcard : (K : Set (Equiv.Perm (Fin n))).ncard ≤
      (L.toFinset : Set (Equiv.Perm (Fin n))).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL,
      ← show Nat.card K = (K : Set (Equiv.Perm (Fin n))).ncard from Nat.card_coe_set_eq _]
    exact hlen
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  intro y hy
  have : y ∈ (L.toFinset : Set (Equiv.Perm (Fin n))) := by rw [heq]; exact hy
  exact List.mem_toFinset.mp this

theorem forall₂_tablePerm {E : Array Table} {e : ℕ → Equiv.Perm (Fin n)}
    (hE : ∀ k < E.size, Rep n E[k]! (e k)) :
    List.Forall₂ (Rep n) E.toList (E.toList.map (tablePerm n)) := by
  rw [List.forall₂_map_right_iff]
  apply List.forall₂_same.mpr
  intro T hT
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
  have := hE k hk
  rw [getElem!_pos E k hk] at this
  rw [tablePerm_eq this]
  exact this

theorem mem_map_tablePerm {E : Array Table} {e : ℕ → Equiv.Perm (Fin n)}
    (hE : ∀ k < E.size, Rep n E[k]! (e k)) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ E.toList.map (tablePerm n)) : ∃ k < E.size, g = e k := by
  rw [List.mem_map] at hg
  obtain ⟨T, hT, rfl⟩ := hg
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
  have := hE k hk
  rw [getElem!_pos E k hk] at this
  exact ⟨k, hk, tablePerm_eq this⟩

theorem classOK_spec (hD : GroupData n P pg gg sift) {NP cap : ℕ} {u : Table}
    (hP : Nat.card P = NP) (hpgi : ∀ l < pg.size, Rep n pgInv[l]! (gg l)⁻¹)
    (hU : Rep n u (tp n u)) (hU2 : (tp n u) ^ 2 = 1)
    (hUn : ∀ p ∈ P, tp n u * p * (tp n u)⁻¹ ∈ P) {r : ClassRow}
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 2 → q ∈ r.oddPrimes)
    (h : classOK n NP cap pg pgInv sift u r (conjClosureH n pg pgInv r.rep cap) = true) :
    Rep n r.rep (tp n r.rep) ∧ orderOf (tp n r.rep) = 2 ∧ tp n r.rep ∈ P ⊔ zpowers (tp n u) ∧
      (r.outer = true ↔ tp n r.rep ∉ P) ∧
      (∀ k < (conjClosureH n pg pgInv r.rep cap).1.size, ∃ c ∈ P,
        Rep n (conjClosureH n pg pgInv r.rep cap).1[k]! (c * tp n r.rep * c⁻¹)) ∧
      closure (tp n '' {x | x ∈ r.centGens.toArray}) = P ⊓ centralizer ({tp n r.rep} : Set _) ∧
      Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder ∧
      (conjClass P (tp n r.rep)).ncard = r.classSize ∧
      CFSG.oddCore ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = ⊥ := by
  have hn := hD.lt
  set t := tp n r.rep
  set o := conjClosureH n pg pgInv r.rep cap
  set cg := r.centGens.toArray
  set cgInv := cg.map (invT n)
  set C := mulClosureH n cg cap
  set queues := r.odd.map fun s => (s, conjClosureH n cg cgInv s.rep cap)
  simp only [classOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ht1, ht2⟩, hout⟩, horb⟩, hodist⟩, hosize⟩, hcg⟩, hCtree⟩, hCdist⟩,
    hCsize⟩, hprod⟩, hodd⟩, hqtree⟩, hcov⟩ := h
  have hT := rep_tp ht1
  have hord := orderOf_eq_two_of_involOK hn hT ht2
  have hR : t ∈ P ⊔ zpowers (tp n u) ∧ (r.outer = true ↔ t ∉ P) := by
    by_cases ho : r.outer = true
    · simp only [ho, ite_true, Bool.and_eq_true, Bool.not_eq_true'] at hout
      have h1 : t ∉ P := fun hm => by
        rw [← hD.sift _ _ hT] at hm
        rw [hm] at hout
        exact Bool.noConfusion hout.1
      exact ⟨mem_R_of_sift hD hU2 hUn hU hT (by rw [hout.2, Bool.or_true]),
        ⟨fun _ => h1, fun _ => ho⟩⟩
    · simp only [ho, ite_false, Bool.false_eq_true] at hout
      have h1 : t ∈ P := (hD.sift _ _ hT).1 hout
      exact ⟨mem_sup_left h1, ⟨fun h2 => absurd h2 ho, fun h2 => absurd h1 h2⟩⟩
  have hgP : ∀ l < pg.size, Rep n pg[l]! (gg l) ∧ Rep n pgInv[l]! (gg l)⁻¹ ∧ gg l ∈ P :=
    fun l hl => ⟨hD.rep l hl, hpgi l hl, hD.mem hl⟩
  have horb' := conjTreeOK_spec P hgP hT horb
  rw [Array.all_eq_true'] at hcg
  simp only [Bool.and_eq_true] at hcg
  have hcgP : ∀ c ∈ cg, Rep n c (tp n c) ∧ tp n c ∈ P ⊓ centralizer ({t} : Set _) := by
    intro c hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hcg c hc
    have hc' := rep_tp h1
    refine ⟨hc', mem_inf.mpr ⟨(hD.sift _ _ hc').1 h2, ?_⟩⟩
    rw [mem_centralizer_singleton_iff]
    exact (commTT_iff hc' hT).1 h3
  set K := closure (tp n '' {x | x ∈ cg})
  have hKle : K ≤ P ⊓ centralizer ({t} : Set _) := by
    rw [closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact (hcgP c hc).2
  have hga : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧ tp n cg[l]! ∈ K := fun l hl =>
    ⟨(hcgP _ (getElem!_mem_array hl)).1, subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have hCK := mulTreeOK_spec hn K (gg := fun l => tp n cg[l]!) hga hCtree
  have hCrep : ∀ k < C.1.size, Rep n C.1[k]! (tablePerm n C.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have hCmem : ∀ k < C.1.size, tablePerm n C.1[k]! ∈ K := by
    intro k hk
    obtain ⟨c, hc, hrep⟩ := hCK k hk
    rw [tablePerm_eq hrep]
    exact hc
  have hCnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hCrep) hCdist
  have hKcard : r.centOrder ≤ Nat.card K := by
    have := length_le_card_of_nodup hCnodup fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
      exact hCmem k hk
    rwa [List.length_map, Array.length_toList, hCsize] at this
  have horep : ∀ k < o.1.size, Rep n o.1[k]! (tablePerm n o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb' k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hodist
  have hclass : r.classSize ≤ (conjClass P t).ncard := by
    have := length_le_ncard_of_nodup honodup (S := conjClass P t) fun x hx => by
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hx
      obtain ⟨c, hc, hrep⟩ := horb' k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩
    rwa [List.length_map, Array.length_toList, hosize] at this
  have hos := ncard_conjClass_mul_card P t
  rw [hP, ← hprod] at hos
  have hCle : Nat.card K ≤ Nat.card ↥(P ⊓ centralizer ({t} : Set _)) := card_le_of_le hKle
  have hpos1 : 0 < r.classSize := by
    rcases Nat.eq_zero_or_pos r.classSize with h0 | h0
    · rw [h0, zero_mul] at hprod
      rw [← hprod] at hP
      exact absurd hP (Nat.card_pos (α := P)).ne'
    · exact h0
  have hpos2 : 0 < r.centOrder := by
    rcases Nat.eq_zero_or_pos r.centOrder with h0 | h0
    · rw [h0, mul_zero] at hprod
      rw [← hprod] at hP
      exact absurd hP (Nat.card_pos (α := P)).ne'
    · exact h0
  have hcent : Nat.card ↥(P ⊓ centralizer ({t} : Set _)) = r.centOrder := by
    by_contra hne
    have hlt : r.centOrder < Nat.card ↥(P ⊓ centralizer ({t} : Set _)) := by omega
    have : r.classSize * r.centOrder < (conjClass P t).ncard *
        Nat.card ↥(P ⊓ centralizer ({t} : Set _)) :=
      Nat.mul_lt_mul_of_le_of_lt hclass hlt (hpos1.trans_le hclass)
    omega
  have hcls : (conjClass P t).ncard = r.classSize := by
    rw [hcent] at hos
    exact Nat.eq_of_mul_eq_mul_right hpos2 hos
  have hKeq : K = P ⊓ centralizer ({t} : Set _) :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hcent]; exact hKcard)
  refine ⟨hT, hord, hR.1, hR.2, horb', hKeq, hcent, hcls, ?_⟩
  have hCcov : ∀ y ∈ P ⊓ centralizer ({t} : Set _), ∃ k < C.1.size, Rep n C.1[k]! y := by
    intro y hy
    have hmem := mem_of_nodup_of_card_le hCnodup (K := P ⊓ centralizer ({t} : Set _))
      (fun x hx => by
        obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hx
        exact hKle (hCmem k hk))
      (by rw [List.length_map, Array.length_toList, hCsize, hcent]) y hy
    obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hCrep hmem
    exact ⟨k, hk, hCrep k hk⟩
  have hcgK : ∀ l < cg.size, Rep n cg[l]! (tp n cg[l]!) ∧ Rep n cgInv[l]! (tp n cg[l]!)⁻¹ ∧
      tp n cg[l]! ∈ P ⊓ centralizer ({t} : Set _) := by
    intro l hl
    have hc := hcgP _ (getElem!_mem_array hl)
    refine ⟨hc.1, ?_, hc.2⟩
    have hinv := (hcg _ (getElem!_mem_array hl)).2
    rw [getElem!_pos cgInv l (by simpa [cgInv] using hl), Array.getElem_map,
      ← getElem!_pos cg l hl]
    exact rep_invT hc.1 hinv
  rw [List.all_eq_true] at hodd hqtree
  apply oddCore_eq_bot_of_witnesses (P ⊓ centralizer ({t} : Set _)) (r.odd.map fun s => tp n s.rep)
  · intro y hy hyp hy2
    obtain ⟨k, hk, hrep⟩ := hCcov y hy
    have hsel : selOK n r.oddPrimes C.1[k]! = true := by
      rw [selOK_iff hn hrep]
      refine ⟨fun h1 => ?_, orderOf y, hprimes _ hyp ?_ hy2, pow_orderOf_eq_one y⟩
      · rw [h1, orderOf_one] at hyp
        exact Nat.not_prime_one hyp
      · rw [← hcent, ← Subgroup.orderOf_mk y hy]
        exact orderOf_dvd_natCard _
    rw [Array.all_eq_true] at hcov
    have h2 := hcov k hk
    rw [← getElem!_pos C.1 k hk, hsel, Bool.not_true, Bool.false_or, List.any_eq_true] at h2
    obtain ⟨q, hq, hmemq⟩ := h2
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    have hsrep := rep_tp (by
      have := hodd s hs
      simp only [oddRowOK, Bool.and_eq_true] at this
      exact this.1.1.1.1)
    have hqspec := conjTreeOK_spec (P ⊓ centralizer ({t} : Set _)) hcgK hsrep
      (hqtree _ (List.mem_map.mpr ⟨s, hs, rfl⟩))
    have hqrep : ∀ j < (conjClosureH n cg cgInv s.rep cap).1.size,
        Rep n (conjClosureH n cg cgInv s.rep cap).1[j]!
          (tablePerm n (conjClosureH n cg cgInv s.rep cap).1[j]!) := by
      intro j hj
      obtain ⟨c, -, hc⟩ := hqspec j hj
      rw [tablePerm_eq hc]
      exact hc
    obtain ⟨j, hj, hyj⟩ := memT_spec hqrep hrep hmemq
    obtain ⟨c, hcK, hc⟩ := hqspec j hj
    rw [tablePerm_eq hc] at hyj
    exact ⟨tp n s.rep, List.mem_map.mpr ⟨s, hs, rfl⟩, c, hcK, hyj⟩
  · intro x hx N hNK hNn hxN
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    have hrow := hodd s hs
    obtain ⟨srep, sprime, ssize, swit⟩ := s
    simp only [oddRowOK, Bool.and_eq_true] at hrow
    obtain ⟨⟨⟨⟨hs1, -⟩, -⟩, -⟩, hwit⟩ := hrow
    have hsrep := rep_tp hs1
    cases swit with
    | conj h ord =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwit
      obtain ⟨⟨⟨⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩, hord2⟩, hordpos⟩, hordt⟩ := hwit
      have hH := rep_tp hh1
      have hHK : tp n h ∈ P ⊓ centralizer ({t} : Set _) := by
        refine mem_inf.mpr ⟨(hD.sift _ _ hH).1 hh2, ?_⟩
        rw [mem_centralizer_singleton_iff]
        exact (commTT_iff hH hT).1 hh3
      refine ⟨tp n srep * (tp n h * tp n srep * (tp n h)⁻¹),
        N.mul_mem hxN (hNn _ hHK _ hxN), ?_⟩
      have hz := Rep.compT hsrep (rep_conjT hH (rep_invT hH hh4) hsrep)
      rw [(ordTest_iff_perm hz hordpos).1 hordt]
      exact Nat.dvd_of_mod_eq_zero hord2
    | normal gs _ =>
      simp only [Bool.and_eq_true, List.all_eq_true] at hwit
      obtain ⟨⟨⟨hqt, hgs⟩, het⟩, hinvol⟩ := hwit
      have hqspec := conjTreeOK_spec (P ⊓ centralizer ({t} : Set _)) hcgK hsrep hqt
      have hqrep : ∀ j < (conjClosureH n cg cgInv srep cap).1.size,
          Rep n (conjClosureH n cg cgInv srep cap).1[j]!
            (tablePerm n (conjClosureH n cg cgInv srep cap).1[j]!) := by
        intro j hj
        obtain ⟨c, -, hc⟩ := hqspec j hj
        rw [tablePerm_eq hc]
        exact hc
      have hgsN : ∀ g ∈ gs, Rep n g (tp n g) ∧ tp n g ∈ N := by
        intro g hg
        obtain ⟨hg1, hg2⟩ := hgs g hg
        have hgr := rep_tp hg1
        obtain ⟨j, hj, hgj⟩ := memT_spec hqrep hgr hg2
        obtain ⟨c, hcK, hc⟩ := hqspec j hj
        rw [tablePerm_eq hc] at hgj
        refine ⟨hgr, ?_⟩
        rw [hgj]
        exact hNn _ hcK _ hxN
      have hga : ∀ l < gs.toArray.size, Rep n gs.toArray[l]! (tp n gs.toArray[l]!) ∧
          tp n gs.toArray[l]! ∈ N := by
        intro l hl
        have hmem : gs.toArray[l]! ∈ gs := by
          have := getElem!_mem_array hl
          simpa using this
        exact hgsN _ hmem
      have heN := mulTreeOK_spec hn N (gg := fun l => tp n gs.toArray[l]!) hga het
      rw [Array.any_eq_true] at hinvol
      obtain ⟨k, hk, hk2⟩ := hinvol
      obtain ⟨z, hzN, hzrep⟩ := heN k hk
      rw [getElem!_pos _ k hk] at hzrep
      refine ⟨z, hzN, ?_⟩
      rw [orderOf_eq_two_of_involOK hn hzrep hk2]

theorem centData_spec (hD : GroupData n P pg gg sift) {NP cap : ℕ} {u : Table}
    {sylowGens : List Table} {sylowOrder : ℕ} {rows : List ClassRow} (hP : Nat.card P = NP)
    (hprimes : ∀ r ∈ rows, ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 2 → q ∈ r.oddPrimes)
    (hsyl : sylowOrder = 2 ^ (2 * NP).factorization 2)
    (h : centDataOK n NP cap pg pgInv sift u sylowGens sylowOrder rows = true) :
    (tp n u) ^ 2 = 1 ∧ tp n u ≠ 1 ∧ tp n u ∉ P ∧ P.map (MulAut.conj (tp n u)).toMonoidHom = P ∧
      (∀ x, x ∈ P ⊔ zpowers (tp n u) ↔ x ∈ P ∨ x * tp n u ∈ P) ∧
      Nat.card ↥(P ⊔ zpowers (tp n u)) = 2 * NP ∧
      closure (tp n '' {x | x ∈ sylowGens.toArray}) ≤ P ⊔ zpowers (tp n u) ∧
      Nat.card ↥(closure (tp n '' {x | x ∈ sylowGens.toArray})) = sylowOrder ∧
      (∀ r ∈ rows, tp n r.rep ∈ P ⊔ zpowers (tp n u) ∧ orderOf (tp n r.rep) = 2 ∧
        (r.outer = true ↔ tp n r.rep ∉ P) ∧
        closure (tp n '' {x | x ∈ r.centGens.toArray}) =
          P ⊓ centralizer ({tp n r.rep} : Set _) ∧
        Nat.card ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder ∧
        (conjClass P (tp n r.rep)).ncard = r.classSize ∧
        CFSG.oddCore ↥(P ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = ⊥) ∧
      (∀ t ∈ P ⊔ zpowers (tp n u), orderOf t = 2 → ∃ r ∈ rows, ∃ g ∈ P, t = g * tp n r.rep * g⁻¹) ∧
      (∀ t ∈ P ⊔ zpowers (tp n u), orderOf t = 2 →
        CFSG.oddCore ↥(P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) = ⊥) := by
  have hn := hD.lt
  simp only [centDataOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hsy, hcl⟩, hco⟩ := h
  obtain ⟨hU, hUi, hU2, hU1, hUP, hUn, hpgi, -, hSR, hScard, hScov⟩ := sylowOK_spec hD hsy
  set U := tp n u
  have hRmem : ∀ x, x ∈ P ⊔ zpowers U ↔ x ∈ P ∨ x * U ∈ P := fun x => mem_sup_zpowers_iff hU2 hUn
  have hRcard : Nat.card ↥(P ⊔ zpowers U) = 2 * NP := by
    rw [card_sup_zpowers hU2 hUn hUP, hP]
  have hcl' : ∀ r ∈ rows,
      classOK n NP cap pg pgInv sift u r (conjClosureH n pg pgInv r.rep cap) = true :=
    fun r hr => hcl (r, conjClosureH n pg pgInv r.rep cap) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hrow := fun r (hr : r ∈ rows) =>
    classOK_spec hD hP hpgi hU hU2 hUn (hprimes r hr) (hcl' r hr)
  have hmap : P.map (MulAut.conj U).toMonoidHom = P := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨p, hp, rfl⟩
      exact hUn p hp
    · rw [Subgroup.card_map_of_injective (MulAut.conj U).injective]
  simp only [coverOK, Bool.and_eq_true, Array.all_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_map] at hco
  obtain ⟨hcovS, hcovU⟩ := hco
  have hconjOf : ∀ r ∈ rows, ∀ k < (conjClosureH n pg pgInv r.rep cap).1.size,
      ∃ c ∈ P, Rep n (conjClosureH n pg pgInv r.rep cap).1[k]! (c * tp n r.rep * c⁻¹) :=
    fun r hr => (hrow r hr).2.2.2.2.1
  have hmemOrb : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g →
      (∃ p, (∃ r ∈ rows, (r, conjClosureH n pg pgInv r.rep cap) = p) ∧ memT n p.2.1 x = true) →
      ∃ r ∈ rows, ∃ c ∈ P, g = c * tp n r.rep * c⁻¹ := by
    rintro x g hx ⟨_, ⟨r, hr, rfl⟩, hm⟩
    have hqrep : ∀ j < (conjClosureH n pg pgInv r.rep cap).1.size,
        Rep n (conjClosureH n pg pgInv r.rep cap).1[j]!
          (tablePerm n (conjClosureH n pg pgInv r.rep cap).1[j]!) := by
      intro j hj
      obtain ⟨c, -, hc⟩ := hconjOf r hr j hj
      rw [tablePerm_eq hc]
      exact hc
    obtain ⟨j, hj, hgj⟩ := memT_spec hqrep hx hm
    obtain ⟨c, hcP, hc⟩ := hconjOf r hr j hj
    rw [tablePerm_eq hc] at hgj
    exact ⟨r, hr, c, hcP, hgj⟩
  have hcover : ∀ t ∈ P ⊔ zpowers U, orderOf t = 2 →
      ∃ r ∈ rows, ∃ g ∈ P, t = g * tp n r.rep * g⁻¹ := by
    intro t ht ht2
    obtain ⟨x, hxR, hxS⟩ := exists_conj_mem_of_card hSR (by rw [hScard, hRcard, hsyl]) ht ht2
    have hs2 : orderOf (x⁻¹ * t * x) = 2 := by
      rw [show x⁻¹ * t * x = (MulAut.conj x⁻¹) t by simp, MulEquiv.orderOf_eq, ht2]
    obtain ⟨k, hk, hkrep⟩ := hScov _ hxS
    have hinv : involOK n (mulClosureH n sylowGens.toArray cap).1[k]! = true :=
      involOK_of_orderOf hn hkrep hs2
    have h1 := hcovS k hk
    rw [← getElem!_pos _ k hk, hinv, Bool.not_true, Bool.false_or] at h1
    simp only [List.any_eq_true, List.mem_map] at h1
    obtain ⟨r, hr, c, hcP, hc⟩ := hmemOrb _ _ hkrep h1
    have htx : t = x * c * tp n r.rep * (x * c)⁻¹ := by
      calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
        _ = _ := by rw [hc]; group
    rcases (hRmem x).1 hxR with hxP | hxU
    · exact ⟨r, hr, x * c, P.mul_mem hxP hcP, htx⟩
    ·
      have hUU : U * U = 1 := by rw [← sq, hU2]
      have hUinv : U⁻¹ = U := inv_eq_of_mul_eq_one_right hUU
      obtain ⟨r', hr', c', hc'P, hc'⟩ := hmemOrb _ _ (rep_conjT hU hUi (hrow r hr).1)
        (hcovU (r, conjClosureH n pg pgInv r.rep cap) ⟨r, hr, rfl⟩)
      have hc'' : U⁻¹ * tp n r.rep * U = c' * tp n r'.rep * c'⁻¹ := by
        rw [hUinv] at hc' ⊢
        exact hc'
      have hmid : U⁻¹ * c * U ∈ P := by
        have := hUn c hcP
        rw [hUinv] at this ⊢
        exact this
      refine ⟨r', hr', (x * U) * (U⁻¹ * c * U) * c', P.mul_mem (P.mul_mem hxU hmid) hc'P, ?_⟩
      calc t = x * c * tp n r.rep * (x * c)⁻¹ := htx
        _ = (x * U) * (U⁻¹ * c * U) * (U⁻¹ * tp n r.rep * U) *
            ((x * U) * (U⁻¹ * c * U))⁻¹ := by group
        _ = _ := by rw [hc'']; group
  refine ⟨hU2, hU1, hUP, hmap, hRmem, hRcard, hSR, hScard, fun r hr => ?_, hcover, ?_⟩
  · obtain ⟨-, hord, hR, hout, -, hK, hcent, hcls, hodd⟩ := hrow r hr
    exact ⟨hR, hord, hout, hK, hcent, hcls, hodd⟩
  · intro t ht ht2
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht ht2
    exact oddCore_inf_centralizer_conj P hg (hrow r hr).2.2.2.2.2.2.2.2

end CFSG.Sporadic.SmallOddCore
