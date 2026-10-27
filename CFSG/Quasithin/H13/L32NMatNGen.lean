module

public import CFSG.Quasithin.H13.L32NMatN
public import CFSG.Quasithin.H13.L32NS7Inputs
public import Std.Data.HashSet.Lemmas
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.MatNCert

variable {n : ℕ}

theorem length_evalW (gens : List (List ℕ)) (w : List ℕ) : (evalW n gens w).length = n := by
  induction w with
  | nil => simp [evalW, oneN]
  | cons i w ih =>
    show (mulN (gens.getD i (oneN n)) (evalW n gens w)).length = n
    rw [length_mulN, ih]

theorem evalW_cons (gens : List (List ℕ)) (i : ℕ) (w : List ℕ) :
    evalW n gens (i :: w) = mulN (gens.getD i (oneN n)) (evalW n gens w) := rfl

theorem validN_getD {gens : List (List ℕ)} (hgens : ∀ g ∈ gens, ValidN n g) (i : ℕ) :
    ValidN n (gens.getD i (oneN n)) := by
  by_cases hi : i < gens.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hgens _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact validN_oneN

theorem validN_evalW (gens : List (List ℕ)) (hgens : ∀ g ∈ gens, ValidN n g) (w : List ℕ) :
    ValidN n (evalW n gens w) := by
  induction w with
  | nil => exact validN_oneN
  | cons i w ih =>
    rw [evalW_cons]
    exact validN_mulN (validN_getD hgens i) ih

@[expose] def genSubN (n : ℕ) (gens : List (List ℕ)) : Subgroup (GL (Fin n) (ZMod 2)) :=
  Subgroup.closure {g | colsN (g : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens}

theorem eq_of_colsN_eq {u v : GL (Fin n) (ZMod 2)}
    (h : colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) =
      colsN (v : Matrix (Fin n) (Fin n) (ZMod 2))) : u = v := by
  apply Units.ext
  rw [← decN_colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)), h, decN_colsN]

theorem exists_evalW (gens : List (List ℕ)) (hgens : ∀ g ∈ gens, ValidN n g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin n) (ZMod 2),
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g) (w : List ℕ) :
    ∃ u ∈ genSubN n gens, (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n (evalW n gens w) := by
  induction w with
  | nil => exact ⟨1, one_mem _, by rw [Units.val_one]; exact decN_oneN.symm⟩
  | cons i w ih =>
    obtain ⟨u, hu, hu'⟩ := ih
    rw [evalW_cons, decN_mulN (validN_getD hgens i).1 (length_evalW gens w), ← hu']
    by_cases hi : i < gens.length
    · rw [List.getD_eq_getElem _ _ hi]
      obtain ⟨v, hv⟩ := hunit _ (List.getElem_mem hi)
      refine ⟨v * u, mul_mem (Subgroup.subset_closure ?_) hu, by rw [Units.val_mul, hv]⟩
      show colsN (v : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens
      rw [hv, colsN_decN (hgens _ (List.getElem_mem hi))]
      exact List.getElem_mem hi
    · rw [List.getD_eq_default _ _ (by omega), decN_oneN, one_mul]
      exact ⟨u, hu, rfl⟩

theorem mem_genSubN_iff (gens L : List (List ℕ)) (hgens : ∀ g ∈ gens, ValidN n g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin n) (ZMod 2),
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g)
    (hL : ∀ x ∈ L, ∃ w, x = evalW n gens w) (hone : oneN n ∈ L)
    (hclosed : ∀ x ∈ L, ∀ g ∈ gens, mulN g x ∈ L) (u : GL (Fin n) (ZMod 2)) :
    u ∈ genSubN n gens ↔ colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L := by
  constructor
  · intro hu
    have hstep : ∀ s : GL (Fin n) (ZMod 2),
        colsN (s : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens →
        ∀ y : GL (Fin n) (ZMod 2), colsN (y : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L →
        colsN ((s * y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L := by
      intro s hs y hy
      rw [Units.val_mul, colsN_mul]
      exact hclosed _ hy _ hs
    have hpow : ∀ s : GL (Fin n) (ZMod 2),
        colsN (s : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ gens → ∀ (m : ℕ)
        (y : GL (Fin n) (ZMod 2)), colsN (y : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L →
        colsN ((s ^ m * y : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L := by
      intro s hs m
      induction m with
      | zero => intro y hy; rwa [pow_zero, one_mul]
      | succ m ih =>
        intro y hy
        rw [pow_succ', mul_assoc]
        exact hstep s hs _ (ih y hy)
    unfold genSubN at hu
    refine Subgroup.closure_induction_left (p := fun (u : GL (Fin n) (ZMod 2)) _ =>
      colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L) ?_ ?_ ?_ hu
    · rw [Units.val_one, colsN_one]
      exact hone
    · intro s hs y _ hy
      exact hstep s hs y hy
    · intro s hs y _ hy
      have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s
      have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos_iff.mpr hfin), pow_orderOf_eq_one]
      rw [hinv]
      exact hpow s hs _ y hy
  · intro hu
    obtain ⟨w, hw⟩ := hL _ hu
    obtain ⟨v, hv, hv'⟩ := exists_evalW gens hgens hunit w
    have : u = v := by
      apply Units.ext
      rw [hv', ← hw, decN_colsN]
    exact this ▸ hv

theorem le_card_of_list {M : Subgroup (GL (Fin n) (ZMod 2))} {B : List (List ℕ)} (hB : B.Nodup)
    (hBM : ∀ b ∈ B, ∃ u ∈ M, (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n b)
    (hval : ∀ b ∈ B, ValidN n b) : B.length ≤ Nat.card M := by
  classical
  let f : {b // b ∈ B} → M := fun b =>
    ⟨Classical.choose (hBM b.1 b.2), (Classical.choose_spec (hBM b.1 b.2)).1⟩
  have hf : Function.Injective f := by
    intro b b' h
    have h1 := congrArg (fun u : M => ((u : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))) h
    simp only [f, (Classical.choose_spec (hBM b.1 b.2)).2,
      (Classical.choose_spec (hBM b'.1 b'.2)).2] at h1
    exact Subtype.ext (decN_injOn (hval _ b.2) (hval _ b'.2) h1)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := B) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hB] at this

theorem card_of_cols {S : Subgroup (GL (Fin n) (ZMod 2))} {L : List (List ℕ)}
    (hS : ∀ u, u ∈ S ↔ colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ L) (hL : L.Nodup)
    (hval : ∀ x ∈ L, ValidN n x)
    (hex : ∀ x ∈ L, ∃ u : GL (Fin n) (ZMod 2), (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n x) :
    Nat.card S = L.length := by
  let f : S → {x // x ∈ L} := fun u =>
    ⟨colsN ((u : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)), (hS u).mp u.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · exact Subtype.ext (eq_of_colsN_eq (congrArg Subtype.val h))
    · obtain ⟨v, hv⟩ := hex x hx
      have hvx : colsN (v : Matrix (Fin n) (Fin n) (ZMod 2)) = x := by
        rw [hv, colsN_decN (hval x hx)]
      exact ⟨⟨v, (hS v).mpr (hvx ▸ hx)⟩, Subtype.ext hvx⟩
  rw [Nat.card_eq_of_bijective f hf,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := L) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hL]

theorem card_genSubN (gens L : List (List ℕ)) (hgens : ∀ g ∈ gens, ValidN n g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin n) (ZMod 2),
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g)
    (hL : ∀ x ∈ L, ∃ w, x = evalW n gens w) (hvalid : ∀ x ∈ L, ValidN n x) (hone : oneN n ∈ L)
    (hclosed : ∀ x ∈ L, ∀ g ∈ gens, mulN g x ∈ L) (hnd : L.Nodup) :
    Nat.card (genSubN n gens) = L.length := by
  refine card_of_cols (mem_genSubN_iff gens L hgens hunit hL hone hclosed) hnd hvalid
    fun x hx => ?_
  obtain ⟨w, hw⟩ := hL _ hx
  obtain ⟨v, -, hv'⟩ := exists_evalW gens hgens hunit w
  exact ⟨v, hv'.trans (congrArg (decN n) hw.symm)⟩

theorem validB_iff {x : List ℕ} : validB n x = true ↔ ValidN n x := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  rfl

theorem nodup_of_nodupB {L : List (List ℕ)} (h : nodupB n L = true) : L.Nodup := by
  simp only [nodupB, decide_eq_true_eq] at h
  have h2 : ((L.map (codeL n)).mergeSort).Nodup :=
    (List.isChain_iff_pairwise.mp h).imp (fun hab => ne_of_lt hab)
  exact List.Nodup.of_map _ ((List.mergeSort_perm _ _).nodup_iff.mp h2)

theorem subB_spec {gens L : List (List ℕ)} (h : subB n gens L = true) :
    (∀ x ∈ L, ValidN n x) ∧ (∀ x ∈ L, ∀ g ∈ gens, mulN g x ∈ L) ∧ L.Nodup ∧ oneN n ∈ L ∧
      ∀ g ∈ gens, ValidN n g := by
  simp only [subB, closedB, Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨hv, hc⟩, hn⟩, ho⟩, hg⟩ := h
  exact ⟨fun x hx => validB_iff.mp (hv x hx), hc, nodup_of_nodupB hn, ho,
    fun g hg' => validB_iff.mp (hg g hg')⟩

theorem mem_elemsOf {gens : List (List ℕ)} {cap : ℕ} {x : List ℕ}
    (hx : x ∈ elemsOf n gens cap) : ∃ w, x = evalW n gens w := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨w, rfl⟩

theorem mem_genSubN_iff_of {gens : List (List ℕ)} {cap : ℕ}
    (h : subB n gens (elemsOf n gens cap) = true)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin n) (ZMod 2),
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g) (u : GL (Fin n) (ZMod 2)) :
    u ∈ genSubN n gens ↔ colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) ∈ elemsOf n gens cap := by
  obtain ⟨-, hc, -, ho, hg⟩ := subB_spec h
  exact mem_genSubN_iff gens _ hg hunit (fun _ hx => mem_elemsOf hx) ho hc u

theorem card_genSubN_of {gens : List (List ℕ)} {cap : ℕ}
    (h : subB n gens (elemsOf n gens cap) = true)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin n) (ZMod 2),
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g) :
    Nat.card (genSubN n gens) = (elemsOf n gens cap).length := by
  obtain ⟨hv, hc, hn, ho, hg⟩ := subB_spec h
  exact card_genSubN gens _ hg hunit (fun _ hx => mem_elemsOf hx) hv ho hc hn

theorem mem_genSubN_of_mem {gens : List (List ℕ)} (hgens : ∀ g ∈ gens, ValidN n g)
    {u : GL (Fin n) (ZMod 2)} {g : List ℕ} (hg : g ∈ gens)
    (hu : (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g) : u ∈ genSubN n gens :=
  Subgroup.subset_closure (show colsN _ ∈ gens by rw [hu, colsN_decN (hgens g hg)]; exact hg)

theorem exists_mem_of_elemsOf {gens : List (List ℕ)} {cap : ℕ}
    (h : subB n gens (elemsOf n gens cap) = true)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin n) (ZMod 2),
      (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n g) {c : List ℕ}
    (hc : c ∈ elemsOf n gens cap) :
    ∃ u ∈ genSubN n gens, (u : Matrix (Fin n) (Fin n) (ZMod 2)) = decN n c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  exact exists_evalW gens (subB_spec h).2.2.2.2 hunit w

theorem colsN_pow (u : GL (Fin n) (ZMod 2)) (k : ℕ) :
    colsN ((u ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      powN n (colsN (u : Matrix (Fin n) (Fin n) (ZMod 2))) k := by
  induction k with
  | zero => rw [pow_zero, Units.val_one, colsN_one]; rfl
  | succ k ih => rw [pow_succ', Units.val_mul, colsN_mul, ih]; rfl

theorem colsN_pow_two_pow (u : GL (Fin n) (ZMod 2)) (k : ℕ) :
    colsN ((u ^ 2 ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      sqN (colsN (u : Matrix (Fin n) (Fin n) (ZMod 2))) k := by
  induction k with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ k ih => rw [pow_succ, pow_mul, sq, Units.val_mul, colsN_mul, ih]; rfl

theorem eq_one_iff_colsN (u : GL (Fin n) (ZMod 2)) :
    u = 1 ↔ colsN (u : Matrix (Fin n) (Fin n) (ZMod 2)) = oneN n := by
  constructor
  · rintro rfl
    rw [Units.val_one, colsN_one]
  · intro h
    apply eq_of_colsN_eq
    rw [h, Units.val_one, colsN_one]

theorem odd_orderOf_iff_of_card {G : Type*} [Group G] {M : Subgroup G} {a : ℕ}
    (hM : Nat.card M = 2 ^ a * 3) {x : G} (hx : x ∈ M) : Odd (orderOf x) ↔ x ^ 3 = 1 := by
  have hd : orderOf x ∣ 2 ^ a * 3 := by
    rw [← hM, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  constructor
  · intro ho
    have hc : Nat.Coprime (orderOf x) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr ho)
    exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left hd)
  · intro h3
    rcases (Nat.dvd_prime (by norm_num)).mp (orderOf_dvd_of_pow_eq_one h3) with h | h <;>
      rw [h] <;> decide

theorem mem_of_blkOf {blks : List (List ℕ)} {v i : ℕ} (h : blkOf blks v = i) (hi : i < 3) :
    v ∈ blks.getD i [] := by
  unfold blkOf at h
  split_ifs at h with h0 h1 h2 <;> subst h
  · exact List.contains_iff_mem.mp h0
  · exact List.contains_iff_mem.mp h1
  · exact List.contains_iff_mem.mp h2
  · omega

theorem getD_blkPerm (blks : List (List ℕ)) (x : List ℕ) {i : ℕ} (hi : i < 3) (d : ℕ) :
    (blkPerm blks x).getD i d = blkOf blks (mvN x ((blks.getD i []).getD 0 0)) := by
  interval_cases i <;> rfl

theorem blkInvB_spec {blks : List (List ℕ)} {x : List ℕ} (h : blkInvB blks x = true) {i : ℕ}
    (hi : i < 3) {v : ℕ} (hv : v ∈ blks.getD i []) :
    blkOf blks (mvN x v) = blkOf blks (mvN x ((blks.getD i []).getD 0 0)) := by
  simp only [blkInvB, List.all_eq_true, beq_iff_eq] at h
  rw [h i (by interval_cases i <;> simp) v hv, getD_blkPerm blks x hi]

theorem getD_lt_of_perm3L {l : List ℕ} (hl : l ∈ S7Cert.perm3L) {i : ℕ} (hi : i < 3) :
    l.getD i 0 < 3 := by
  simp only [S7Cert.perm3L, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases i <;> decide

theorem getD_compL (l l' : List ℕ) {i : ℕ} (hi : i < l'.length) :
    (S7Cert.compL l l').getD i 0 = l.getD (l'.getD i 0) 0 := by
  simp only [S7Cert.compL, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem blkPerm_mulN {blks : List (List ℕ)} {x y : List ℕ} (hx : blkInvB blks x = true)
    (hyp : blkPerm blks y ∈ S7Cert.perm3L) :
    blkPerm blks (mulN x y) = S7Cert.compL (blkPerm blks x) (blkPerm blks y) := by
  have key : ∀ i < 3, blkOf blks (mvN (mulN x y) ((blks.getD i []).getD 0 0)) =
      (blkPerm blks x).getD ((blkPerm blks y).getD i 0) 0 := by
    intro i hi
    have hj3 := getD_lt_of_perm3L hyp hi
    have hjdef : blkOf blks (mvN y ((blks.getD i []).getD 0 0)) = (blkPerm blks y).getD i 0 :=
      (getD_blkPerm blks y hi 0).symm
    have hmem := mem_of_blkOf hjdef hj3
    rw [mvN_mulN, blkInvB_spec hx hj3 hmem, getD_blkPerm _ _ hj3]
  have hlen : (blkPerm blks (mulN x y)).length = 3 := rfl
  have hlen' : (S7Cert.compL (blkPerm blks x) (blkPerm blks y)).length = 3 := by
    simp [S7Cert.compL, blkPerm]
  apply List.ext_getElem (hlen.trans hlen'.symm)
  intro i h1 h2
  have hi : i < 3 := hlen ▸ h1
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2, getD_blkPerm _ _ hi,
    key i hi, getD_compL _ _ (by simp [blkPerm]; omega)]

end CFSG.Quasithin.H13.MatNCert
