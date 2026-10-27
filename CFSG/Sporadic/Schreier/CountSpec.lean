module

public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem foldl_add_eq_sum {α : Type*} (h : α → ℕ) :
    ∀ (l : List α) (c : ℕ), l.foldl (fun c t => c + h t) c = c + (l.map h).sum
  | [], c => by simp
  | t :: l, c => by
    rw [List.foldl_cons, foldl_add_eq_sum h l, List.map_cons, List.sum_cons]
    omega

theorem sum_map_eq_of_forall₂ {α β : Type*} {S : α → β → Prop} {u : α → ℕ} {v : β → ℕ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ S l m → (∀ a b, S a b → b ∈ m → u a = v b) →
      (l.map u).sum = (m.map v).sum
  | [], [], .nil, _ => rfl
  | a :: l, b :: m, .cons hab hlm, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, h a b hab List.mem_cons_self,
      sum_map_eq_of_forall₂ hlm fun a' b' h' hb' => h a' b' h' (List.mem_cons_of_mem b hb')]

theorem countP_eq_of_forall₂ {α β : Type*} {S : α → β → Prop} {p : α → Bool} {q : β → Bool} :
    ∀ {l : List α} {m : List β}, List.Forall₂ S l m →
      (∀ a b, S a b → b ∈ m → (p a = true ↔ q b = true)) → l.countP p = m.countP q
  | [], [], .nil, _ => rfl
  | a :: l, b :: m, .cons hab hlm, h => by
    have hpq := h a b hab List.mem_cons_self
    rw [List.countP_cons, List.countP_cons,
      countP_eq_of_forall₂ hlm fun a' b' h' hb' => h a' b' h' (List.mem_cons_of_mem b hb')]
    by_cases hp : p a = true
    · simp [hp, hpq.1 hp]
    · have hq : ¬q b = true := fun hq => hp (hpq.2 hq)
      simp [hp, hq]

theorem forall₂_replicate {α β : Type*} {S : α → β → Prop} {a : α} {b : β} (h : S a b) :
    ∀ k, List.Forall₂ S (List.replicate k a) (List.replicate k b)
  | 0 => .nil
  | k + 1 => .cons h (forall₂_replicate h k)

theorem forall₂_append {α β : Type*} {S : α → β → Prop} :
    ∀ {l₁ : List α} {m₁ : List β} {l₂ : List α} {m₂ : List β}, List.Forall₂ S l₁ m₁ →
      List.Forall₂ S l₂ m₂ → List.Forall₂ S (l₁ ++ l₂) (m₁ ++ m₂)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons hab h₁, h₂ => .cons hab (forall₂_append h₁ h₂)

theorem length_filter_product {α β : Type*} (A : List α) (B : List β) (R : α → β → Bool) :
    ((A ×ˢ B).filter fun q => R q.1 q.2).length = (A.map fun a => B.countP (R a)).sum := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.product_cons, List.filter_append, List.length_append, ih, List.map_cons,
      List.sum_cons, List.filter_map, List.length_map, List.countP_eq_length_filter]
    rfl

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem apW_spec {w : List Table} {gs : List G} (h : List.Forall₂ (Rep n) w gs) {i : ℕ}
    (hi : i < n) : apW w i = idx n gs.prod i := by
  induction h with
  | nil => simp [apW, idx_one]
  | cons hT _ ih =>
    simp only [apW, List.foldr_cons] at ih ⊢
    rw [ih, hT _ (idx_lt _ hi), List.prod_cons, idx_mul]

theorem apPowW_spec {w : List Table} {gs : List G} (h : List.Forall₂ (Rep n) w gs) (e : ℕ)
    {i : ℕ} (hi : i < n) : apPowW w e i = idx n (gs.prod ^ e) i := by
  induction e with
  | zero => simp [apPowW, idx_one]
  | succ e ih => rw [apPowW, ih, apW_spec h (idx_lt _ hi), pow_succ', idx_mul]

theorem powFixW_iff (hf : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) {w : List Table}
    {gs : List G} (h : List.Forall₂ (Rep n) w gs) (e : ℕ) :
    powFixW n w e = true ↔ gs.prod ^ e = 1 := by
  rw [powFixW, allIn_eq_true]
  constructor
  · intro H
    apply hf
    intro i
    have := H i.val (Nat.zero_le _) i.isLt
    rw [beq_iff_eq, apPowW_spec h e i.isLt, idx_of_lt _ i.isLt] at this
    exact Fin.ext this
  · intro H i _ hi
    rw [beq_iff_eq, apPowW_spec h e hi, H, idx_one]

theorem mem_divParts {m e : ℕ} : e ∈ divParts m ↔ ∃ d, d ≤ m ∧ 1 < d ∧ d ∣ m ∧ m / d = e := by
  simp only [divParts, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Nat.lt_succ_iff]
  constructor
  · rintro ⟨d, ⟨hdm, hd1, hmod⟩, rfl⟩
    exact ⟨d, hdm, hd1, Nat.dvd_of_mod_eq_zero hmod, rfl⟩
  · rintro ⟨d, hdm, hd1, hdvd, rfl⟩
    exact ⟨d, ⟨hdm, hd1, Nat.mod_eq_zero_of_dvd hdvd⟩, rfl⟩

theorem ordW_iff (hf : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) {w : List Table}
    {gs : List G} (h : List.Forall₂ (Rep n) w gs) {m : ℕ} (hm : 0 < m) :
    ordW n w m = true ↔ orderOf gs.prod = m := by
  rw [ordW, Bool.and_eq_true, powFixW_iff hf h, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine orderOf_eq_of_pow_and_pow_div_prime hm h1 fun p hp hpm hc => ?_
    have hmem : m / p ∈ divParts m :=
      mem_divParts.2 ⟨p, Nat.le_of_dvd hm hpm, hp.one_lt, hpm, rfl⟩
    have := h2 (m / p) hmem
    rw [(powFixW_iff hf h _).2 hc] at this
    exact Bool.false_ne_true this
  · intro ho
    refine ⟨ho ▸ pow_orderOf_eq_one _, fun e he => ?_⟩
    obtain ⟨d, hdm, hd1, -, rfl⟩ := mem_divParts.1 he
    have hlt : m / d < m := Nat.div_lt_self hm hd1
    have hne : gs.prod ^ (m / d) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (Nat.div_pos hdm (by omega)).ne' (by rw [ho]; exact hlt)
    cases hpf : powFixW n w (m / d)
    · rfl
    · exact absurd ((powFixW_iff hf h _).1 hpf) hne

theorem ordW_single_iff (hf : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) {T : Table} {g : G}
    (h : Rep n T g) {m : ℕ} (hm : 0 < m) : ordW n [T] m = true ↔ orderOf g = m := by
  rw [ordW_iff hf (List.Forall₂.cons h List.Forall₂.nil) hm, List.prod_singleton]

theorem ordTest_iff (hf : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) {T : Table} {g : G}
    (h : Rep n T g) {m : ℕ} (hm : 0 < m) : ordTest n m T = true ↔ orderOf g = m :=
  ordW_single_iff hf h hm

theorem prod_commWord {x y : G} {mx my : ℕ} (hx : orderOf x = mx) (hy : orderOf y = my)
    (hmx : 0 < mx) (hmy : 0 < my) :
    (x :: y :: (List.replicate (mx - 1) x ++ List.replicate (my - 1) y)).prod =
      x * y * x⁻¹ * y⁻¹ := by
  have hinv : ∀ (z : G) (m : ℕ), orderOf z = m → 0 < m → z ^ (m - 1) = z⁻¹ := by
    intro z m hz hm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hm, ← hz, pow_orderOf_eq_one]
  rw [List.prod_cons, List.prod_cons, List.prod_append, List.prod_replicate, List.prod_replicate,
    hinv x mx hx hmx, hinv y my hy hmy]
  simp only [mul_assoc]

theorem pairTest_iff (hf : ∀ g : G, (∀ i : Fin n, g • i = i) → g = 1) {x y : Table} {xg yg : G}
    (hx : Rep n x xg) (hy : Rep n y yg) {r s mx my : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hxo : orderOf xg = mx) (hyo : orderOf yg = my) (hmx : 0 < mx) (hmy : 0 < my) :
    pairTest n r s mx my x y = true ↔
      orderOf (xg * yg) = r ∧ orderOf (xg * yg * xg⁻¹ * yg⁻¹) = s := by
  have hxy : List.Forall₂ (Rep n) [x, y] [xg, yg] := .cons hx (.cons hy .nil)
  have hc : List.Forall₂ (Rep n) (commWord x y mx my)
      (xg :: yg :: (List.replicate (mx - 1) xg ++ List.replicate (my - 1) yg)) := by
    refine .cons hx (.cons hy ?_)
    exact forall₂_append (forall₂_replicate hx _) (forall₂_replicate hy _)
  rw [pairTest, Bool.and_eq_true, ordW_iff hf hxy hr, ordW_iff hf hc hs,
    prod_commWord hxo hyo hmx hmy]
  simp

theorem products_map_mul (g : G) (Gs : List G) (Gss : List (List G)) :
    (products (Gs :: Gss)).map (g * ·) =
      Gs.flatMap fun t => (products Gss).map ((g * t) * ·) := by
  rw [products, List.map_flatMap]
  congr 1
  funext t
  rw [List.map_map]
  congr 1
  funext u
  simp [mul_assoc]

theorem countProducts_spec {f : Table → Bool} {P : G → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g)) :
    ∀ {Tss : List (List Table)} {Gss : List (List G)},
      List.Forall₂ (List.Forall₂ (Rep n)) Tss Gss → ∀ {gT : Table} {g : G}, Rep n gT g →
        countProducts n f Tss gT = ((products Gss).map (g * ·)).countP fun h => decide (P h)
  | [], [], .nil, gT, g, hg => by
    simp only [countProducts, products, List.map_cons, List.map_nil, mul_one]
    by_cases hP : P g
    · simp [hP, (hfP gT g hg).2 hP]
    · have hf : ¬f gT = true := fun hf => hP ((hfP gT g hg).1 hf)
      simp [hP, hf]
  | T :: Ts, Gs :: Gss, .cons hT hTs, gT, g, hg => by
    rw [countProducts, foldl_add_eq_sum, zero_add, products_map_mul, List.countP_flatMap]
    refine sum_map_eq_of_forall₂ hT fun t x htx _ => ?_
    exact countProducts_spec hfP hTs (Rep.compT hg htx)

theorem filterProducts_spec {f : Table → Bool} {P : G → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g)) :
    ∀ {Tss : List (List Table)} {Gss : List (List G)},
      List.Forall₂ (List.Forall₂ (Rep n)) Tss Gss → ∀ {gT : Table} {g : G}, Rep n gT g →
        ∀ {acc : List Table} {accG : List G}, List.Forall₂ (Rep n) acc accG →
          List.Forall₂ (Rep n) (filterProducts n f Tss gT acc)
            ((((products Gss).map (g * ·)).filter fun h => decide (P h)).reverse ++ accG)
  | [], [], .nil, gT, g, hg, acc, accG, hacc => by
    simp only [filterProducts, products, List.map_cons, List.map_nil, mul_one]
    by_cases hP : P g
    · simpa [hP, (hfP gT g hg).2 hP] using List.Forall₂.cons hg hacc
    · have hf : ¬f gT = true := fun hf => hP ((hfP gT g hg).1 hf)
      simpa [hP, hf] using hacc
  | T :: Ts, Gs :: Gss, .cons hT hTs, gT, g, hg, acc, accG, hacc => by
    rw [filterProducts, products_map_mul]
    induction hT generalizing acc accG with
    | nil => simpa using hacc
    | @cons t x T' Gs' htx _ ih =>
      rw [List.foldl_cons, List.flatMap_cons, List.filter_append, List.reverse_append,
        List.append_assoc]
      exact ih _ _ (filterProducts_spec hfP hTs (Rep.compT hg htx) hacc)

theorem pairCount_spec {r : Table → Table → Bool} {R : G → G → Prop} [∀ x, DecidablePred (R x)]
    {X Y : List Table} {Xg Yg : List G} (hX : List.Forall₂ (Rep n) X Xg)
    (hY : List.Forall₂ (Rep n) Y Yg)
    (hr : ∀ x xg y yg, Rep n x xg → Rep n y yg → xg ∈ Xg → yg ∈ Yg → (r x y = true ↔ R xg yg)) :
    pairCount X Y r = (Xg.map fun x => Yg.countP fun y => decide (R x y)).sum := by
  rw [pairCount, foldl_add_eq_sum, zero_add]
  refine sum_map_eq_of_forall₂ hX fun x xg hx hxg => ?_
  exact countP_eq_of_forall₂ hY fun y yg hy hyg => by
    rw [hr x xg y yg hx hy hxg hyg, decide_eq_true_iff]

theorem card_subtype_eq_countP {M : Type*} [Group M] (H : Subgroup M) (L : List M)
    (hL : L.Nodup) (hmem : ∀ g, g ∈ L ↔ g ∈ H) (P : M → Prop) [DecidablePred P] :
    Nat.card {x : H // P x} = L.countP fun g => decide (P g) := by
  rw [List.countP_eq_length_filter]
  refine card_eq_length _ Subtype.val Subtype.val_injective _ (hL.filter _) fun g => ?_
  simp only [List.mem_filter, hmem, decide_eq_true_eq]
  exact ⟨fun ⟨hg, hP⟩ => ⟨⟨g, hg⟩, hP, rfl⟩, fun ⟨x, hx, hxg⟩ => hxg ▸ ⟨x.2, hx⟩⟩

theorem card_pairs_eq_sum {M : Type*} [Group M] (H : Subgroup M) (L : List M) (hL : L.Nodup)
    (hmem : ∀ g, g ∈ L ↔ g ∈ H) (P₁ P₂ : M → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (R : M → M → Prop) [∀ x, DecidablePred (R x)] :
    Nat.card {p : H × H // P₁ p.1 ∧ P₂ p.2 ∧ R p.1 p.2} =
      ((L.filter fun g => decide (P₁ g)).map fun x =>
        (L.filter fun g => decide (P₂ g)).countP fun y => decide (R x y)).sum := by
  rw [← length_filter_product]
  refine card_eq_length _ (fun p : H × H => ((p.1 : M), (p.2 : M)))
    (fun p q h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))) _
    (((hL.filter _).product (hL.filter _)).filter _) ?_
  rintro ⟨g, h⟩
  simp only [List.mem_filter, List.mem_product, hmem, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hg, hg1⟩, hh, hh2⟩, hR⟩
    exact ⟨(⟨g, hg⟩, ⟨h, hh⟩), ⟨hg1, hh2, hR⟩, rfl, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hR⟩, rfl, rfl⟩
    exact ⟨⟨⟨x.2, hx⟩, y.2, hy⟩, hR⟩

@[expose] def toTable {n : ℕ} (g : Equiv.Perm (Fin n)) : Table :=
  Array.ofFn fun i => UInt32.ofNat (g i).val

theorem rep_toTable {n : ℕ} (hn : n < 2 ^ 32) (g : Equiv.Perm (Fin n)) :
    Rep n (toTable g) g := by
  intro i hi
  rw [idx_of_lt _ hi, toTable, ap_ofFn _ hi, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt ((g _).isLt.trans hn)]
  rfl

theorem perm_faithful {n : ℕ} (g : Equiv.Perm (Fin n)) (hg : ∀ i : Fin n, g • i = i) : g = 1 :=
  Equiv.ext hg

@[expose] def levelTables {n : ℕ} (Q : CFSG.Certificates.RawSchreierDatum n) :
    List (List Table) :=
  ((List.finRange Q.baseCount).map (levelTransversals Q)).map fun T => T.map toTable

theorem forall₂_levelTables {n : ℕ} (hn : n < 2 ^ 32) (Q : CFSG.Certificates.RawSchreierDatum n) :
    List.Forall₂ (List.Forall₂ (Rep n)) (levelTables Q)
      ((List.finRange Q.baseCount).map (levelTransversals Q)) := by
  rw [levelTables, List.forall₂_map_left_iff]
  refine List.forall₂_same.2 fun T _ => ?_
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.2 fun g _ => rep_toTable hn g

end CFSG.Sporadic.Schreier
