module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

section Group

variable {M : Type*} [Group M]

@[expose] def letterW (x y : M) (l : ℕ) : M :=
  if l = 0 then x else if l = 1 then y else if l = 2 then x⁻¹ else y⁻¹

@[expose] def evalW (x y : M) (w : List ℕ) : M := (w.map (letterW x y)).prod

@[expose] def WordsRel (ws : List (List ℕ × ℕ)) (x y : M) : Prop :=
  ∀ p ∈ ws, orderOf (evalW x y p.1) = p.2

noncomputable instance (ws : List (List ℕ × ℕ)) (x : M) : DecidablePred (WordsRel ws x) :=
  Classical.decPred _

theorem evalW_map {M' : Type*} [Group M'] (f : M →* M') (x y : M) (w : List ℕ) :
    f (evalW x y w) = evalW (f x) (f y) w := by
  induction w with
  | nil => simp [evalW]
  | cons l w ih =>
    simp only [evalW, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    unfold letterW
    split_ifs <;> simp

theorem wordsRel_map {M' : Type*} [Group M'] (f : M ≃* M') (ws : List (List ℕ × ℕ)) (x y : M) :
    WordsRel ws (f x) (f y) ↔ WordsRel ws x y := by
  unfold WordsRel
  refine forall₂_congr fun p _ => ?_
  have h := evalW_map f.toMonoidHom x y p.1
  simp only [MulEquiv.coe_toMonoidHom] at h
  rw [← h, MulEquiv.orderOf_eq]

theorem wordsRel_coe {H : Subgroup M} (ws : List (List ℕ × ℕ)) (x y : H) :
    WordsRel ws (x : M) (y : M) ↔ WordsRel ws x y := by
  unfold WordsRel
  refine forall₂_congr fun p _ => ?_
  have h := evalW_map H.subtype x y p.1
  simp only [Subgroup.coe_subtype] at h
  rw [← h, Subgroup.orderOf_coe]

theorem card_mulAut_le_wordPairs [Finite M] (a b : M)
    (hgen : Subgroup.closure ({a, b} : Set M) = ⊤) (ws : List (List ℕ × ℕ))
    (hab : WordsRel ws a b) :
    Nat.card (MulAut M) ≤ Nat.card {p : M × M // orderOf p.1 = orderOf a ∧
      orderOf p.2 = orderOf b ∧ WordsRel ws p.1 p.2} := by
  let e : MulAut M → {p : M × M // orderOf p.1 = orderOf a ∧
      orderOf p.2 = orderOf b ∧ WordsRel ws p.1 p.2} := fun α =>
    ⟨(α a, α b), MulEquiv.orderOf_eq α a, MulEquiv.orderOf_eq α b, (wordsRel_map α ws a b).2 hab⟩
  refine Nat.card_le_card_of_injective e fun α β hαβ => ?_
  have hpairs := congrArg Subtype.val hαβ
  have hx : α a = β a := congrArg Prod.fst hpairs
  have hy : α b = β b := congrArg Prod.snd hpairs
  have hgenerators : Set.EqOn (α : M → M) β ({a, b} : Set M) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · exact Set.mem_singleton_iff.mp hz ▸ hy
  have hclosure := MonoidHom.eqOn_closure (f := α.toMonoidHom) (g := β.toMonoidHom) hgenerators
  rw [hgen] at hclosure
  exact MulEquiv.ext fun z => hclosure (by simp)

end Group

variable {n : ℕ}

@[expose] def wordElts {M : Type*} [Group M] (x y : M) (mx my : ℕ) (w : List ℕ) : List M :=
  w.flatMap fun l =>
    if l = 0 then [x] else if l = 1 then [y] else if l = 2 then List.replicate (mx - 1) x
    else List.replicate (my - 1) y

theorem prod_wordElts {M : Type*} [Group M] {x y : M} {mx my : ℕ} (hx : orderOf x = mx)
    (hy : orderOf y = my) (hmx : 0 < mx) (hmy : 0 < my) (w : List ℕ) :
    (wordElts x y mx my w).prod = evalW x y w := by
  have hinv : ∀ (z : M) (m : ℕ), orderOf z = m → 0 < m → z ^ (m - 1) = z⁻¹ := by
    intro z m hz hm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hm, ← hz, pow_orderOf_eq_one]
  induction w with
  | nil => simp [wordElts, evalW]
  | cons l w ih =>
    simp only [wordElts, List.flatMap_cons, List.prod_append] at ih ⊢
    rw [ih]
    simp only [evalW, List.map_cons, List.prod_cons, letterW]
    congr 1
    split_ifs <;> simp [List.prod_replicate, hinv x mx hx hmx, hinv y my hy hmy]

theorem forall₂_wordTbls {G : Type*} [Group G] [MulAction G (Fin n)] {x y : Table} {xg yg : G}
    (hx : Rep n x xg) (hy : Rep n y yg) (mx my : ℕ) (w : List ℕ) :
    List.Forall₂ (Rep n) (wordTbls x y mx my w) (wordElts xg yg mx my w) := by
  induction w with
  | nil => exact List.Forall₂.nil
  | cons l w ih =>
    simp only [wordTbls, wordElts, List.flatMap_cons] at ih ⊢
    refine forall₂_append ?_ ih
    split_ifs
    · exact List.Forall₂.cons hx List.Forall₂.nil
    · exact List.Forall₂.cons hy List.Forall₂.nil
    · exact forall₂_replicate hx _
    · exact forall₂_replicate hy _

theorem wordsTest_iff {G : Type*} [Group G] [MulAction G (Fin n)]
    (hf : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) {x y : Table} {xg yg : G}
    (hx : Rep n x xg) (hy : Rep n y yg) {mx my : ℕ} (hxo : orderOf xg = mx)
    (hyo : orderOf yg = my) (hmx : 0 < mx) (hmy : 0 < my) {ws : List (List ℕ × ℕ)}
    (hws : ∀ p ∈ ws, 0 < p.2) : wordsTest n mx my ws x y = true ↔ WordsRel ws xg yg := by
  rw [wordsTest, List.all_eq_true]
  refine forall₂_congr fun p hp => ?_
  rw [ordW_iff hf (forall₂_wordTbls hx hy mx my p.1) (hws p hp),
    prod_wordElts hxo hyo hmx hmy]

@[expose] noncomputable def partnersW (L : List (Equiv.Perm (Fin n))) (my : ℕ)
    (ws : List (List ℕ × ℕ)) (x : Equiv.Perm (Fin n)) : ℕ :=
  (L.filter fun h => decide (orderOf h = my)).countP fun y => decide (WordsRel ws x y)

theorem partnersW_conj (H : Subgroup (Equiv.Perm (Fin n))) (L : List (Equiv.Perm (Fin n)))
    (hL : L.Nodup) (hmem : ∀ g, g ∈ L ↔ g ∈ H) (my : ℕ) (ws : List (List ℕ × ℕ))
    {c : Equiv.Perm (Fin n)} (hc : c ∈ H) (x : Equiv.Perm (Fin n)) :
    partnersW L my ws (c * x * c⁻¹) = partnersW L my ws x := by
  have hcard : ∀ z, partnersW L my ws z =
      Nat.card {y : H // orderOf (y : Equiv.Perm (Fin n)) = my ∧ WordsRel ws z y} := by
    intro z
    rw [partnersW, List.countP_filter,
      card_subtype_eq_countP H L hL hmem (fun y => orderOf y = my ∧ WordsRel ws z y)]
    congr 1
    funext y
    rw [Bool.decide_and, Bool.and_comm]
  rw [hcard, hcard]
  let e : H ≃ H := (MulAut.conj (⟨c, hc⟩ : H)).toEquiv
  refine (Nat.card_congr (e.subtypeEquiv fun y => ?_)).symm
  have he : ((e y : H) : Equiv.Perm (Fin n)) = c * y * c⁻¹ := rfl
  rw [he, ← MulAut.conj_apply, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
    wordsRel_map (MulAut.conj c)]

theorem card_pairs_eq_repsTotal (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {mx my : ℕ} (hmx : 0 < mx) (hmy : 0 < my) {ws : List (List ℕ × ℕ)}
    (hws : ∀ p ∈ ws, 0 < p.2) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (reps : List (Equiv.Perm (Fin n)))
    (hreps : ∀ r ∈ reps, r ∈ Q.originalSubgroup ∧ orderOf r = mx) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q 1 mx) (reps.map toTable) cap = true) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ WordsRel ws p.1 p.2} =
      repsTotal n gens gensInv (reps.map toTable) (orderTables Q my) cap
        (wordsTest n mx my ws) := by
  set H := Q.originalSubgroup
  set L := enumeration Q
  have hL : L.Nodup := enumeration_nodup Q hQ
  have hmem : ∀ g, g ∈ L ↔ g ∈ H := mem_enumeration_iff Q hQ
  set XG := L.filter fun h => decide (orderOf h = mx)
  have hX := forall₂_cosetOrderTables hn Q 1 hmx
  simp only [one_mul, List.map_id'] at hX
  have hY := forall₂_orderTables hn Q hmy
  have hcoe : ∀ p : H × H,
      (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ WordsRel ws p.1 p.2) ↔
      (orderOf (p.1 : Equiv.Perm (Fin n)) = mx ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = my ∧
        WordsRel ws (p.1 : Equiv.Perm (Fin n)) p.2) := fun p => by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, wordsRel_coe]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
    card_pairs_eq_sum H L hL hmem (fun h => orderOf h = mx) (fun h => orderOf h = my)
      (WordsRel ws)]
  simp only [repsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨htree, hdist⟩, hsum⟩ := hok
  have hXGmem : ∀ x ∈ XG, x ∈ H ∧ orderOf x = mx := fun x hx => by
    rw [List.mem_filter, decide_eq_true_eq] at hx
    exact ⟨(hmem x).1 hx.1, hx.2⟩
  have key := sum_eq_classSum H (partnersW L my ws) (fun c hc x => partnersW_conj H L hL hmem
    my ws hc x) XG (fun c hc x hx => by
      obtain ⟨hxH, hxo⟩ := hXGmem x hx
      rw [List.mem_filter, decide_eq_true_eq, hmem]
      exact ⟨H.mul_mem (H.mul_mem hc hxH) (H.inv_mem hc),
        (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hxo⟩) hg
    (fun T => (orderTables Q my).countP (wordsTest n mx my ws T)) ?_
    ((reps.map toTable).map fun r => (r, conjClosure n gens gensInv r cap)) ?_ htree hdist ?_
  · rw [repsTotal]
    rw [List.map_map] at key
    exact key
  · intro T x hT hx
    obtain ⟨-, hxo⟩ := hXGmem x hx
    have hrev : partnersW L my ws x =
        (L.filter fun h => decide (orderOf h = my)).reverse.countP
          (fun y => decide (WordsRel ws x y)) := List.countP_reverse.symm
    rw [hrev]
    refine countP_eq_of_forall₂ hY fun y yg hy hyg => ?_
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hyg
    rw [wordsTest_iff perm_faithful hT hy hxo hyg.2 hmx hmy hws, decide_eq_true_iff]
  · intro c hc
    simp only [List.map_map, List.mem_map, Function.comp] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    refine ⟨r, ?_, rep_toTable hn r⟩
    rw [List.mem_filter, decide_eq_true_eq, hmem]
    exact ⟨(hreps r hr).1, (hreps r hr).2⟩
  · rw [hsum, hX.length_eq, List.length_reverse]

end CFSG.Sporadic.Schreier
