module

public import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ClassSpec

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

variable {n : ℕ}

@[expose] noncomputable def tablePerm (n : ℕ) (T : Table) : Equiv.Perm (Fin n) :=
  Classical.epsilon fun g => Rep n T g

theorem rep_unique {T : Table} {g h : Equiv.Perm (Fin n)} (hg : Rep n T g) (hh : Rep n T h) :
    g = h := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  have h1 := hg i.val i.isLt
  have h2 := hh i.val i.isLt
  rw [idx_of_lt _ i.isLt] at h1 h2
  simpa using h1.symm.trans h2

theorem tablePerm_eq {T : Table} {g : Equiv.Perm (Fin n)} (hg : Rep n T g) :
    tablePerm n T = g :=
  rep_unique (Classical.epsilon_spec (p := fun g => Rep n T g) ⟨g, hg⟩) hg

theorem sum_flatMap {α β : Type*} (f : α → List β) (g : β → ℕ) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap f g l, List.map_cons,
      List.sum_cons]

theorem sum_eq_classSum (H : Subgroup (Equiv.Perm (Fin n))) (p : Equiv.Perm (Fin n) → ℕ)
    (hp : ∀ c ∈ H, ∀ x, p (c * x * c⁻¹) = p x) (XG : List (Equiv.Perm (Fin n)))
    (hclosed : ∀ c ∈ H, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG)
    {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    (pRep : Table → ℕ) (hpRep : ∀ T x, Rep n T x → x ∈ XG → pRep T = p x)
    (cl : List (Table × Array Table × Array ℕ × Array ℕ))
    (h1 : ∀ c ∈ cl, ∃ x ∈ XG, Rep n c.1 x)
    (h2 : ∀ c ∈ cl, conjTreeOK n gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true)
    (h3 : keysDistinct n (cl.flatMap fun c => c.2.1.toList) = true)
    (h4 : (cl.map fun c => c.2.1.size).sum = XG.length) :
    (XG.map p).sum = (cl.map fun c => c.2.1.size * pRep c.1).sum := by
  have hconj : ∀ c ∈ cl, ∃ x ∈ XG, Rep n c.1 x ∧
      ∀ T ∈ c.2.1.toList, ∃ d ∈ H, Rep n T (d * x * d⁻¹) := by
    intro c hc
    obtain ⟨x, hx, hrep⟩ := h1 c hc
    refine ⟨x, hx, hrep, fun T hT => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hk
    obtain ⟨d, hd, hrepd⟩ := conjTreeOK_spec H hg hrep (h2 c hc) k hk
    refine ⟨d, hd, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos c.2.1 k hk] at hrepd
  set U := cl.flatMap fun c => c.2.1.toList
  have hUrep : ∀ T ∈ U, ∃ x ∈ XG, Rep n T x := by
    intro T hT
    obtain ⟨c, hc, hT⟩ := List.mem_flatMap.1 hT
    obtain ⟨x, hx, -, hall⟩ := hconj c hc
    obtain ⟨d, hd, hrep⟩ := hall T hT
    exact ⟨d * x * d⁻¹, hclosed d hd x hx, hrep⟩
  have hU : List.Forall₂ (Rep n) U (U.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨x, -, hrep⟩ := hUrep T hT
    rw [tablePerm_eq hrep]
    exact hrep
  have hnodup : (U.map (tablePerm n)).Nodup := nodup_of_keysDistinct hU h3
  have hsub : U.map (tablePerm n) ⊆ XG := by
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
    obtain ⟨x, hx, hrep⟩ := hUrep T hT
    rw [tablePerm_eq hrep]
    exact hx
  have hlen : XG.length ≤ (U.map (tablePerm n)).length := by
    rw [List.length_map, List.length_flatMap, ← h4]
    simp
  have hperm := (hnodup.subperm hsub).perm_of_length_le hlen
  rw [← (hperm.map p).sum_eq, List.map_map, sum_flatMap]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨x, hx, hrep, hall⟩ := hconj c hc
  have hconst : ∀ T ∈ c.2.1.toList, (p ∘ tablePerm n) T = p x := by
    intro T hT
    obtain ⟨d, hd, hrepd⟩ := hall T hT
    rw [Function.comp_apply, tablePerm_eq hrepd, hp d hd x]
  rw [List.map_congr_left hconst, List.map_const', List.sum_replicate, smul_eq_mul,
    Array.length_toList, hpRep _ _ hrep hx]

@[expose] def PartnerRel (r s : ℕ) (x y : Equiv.Perm (Fin n)) : Prop :=
  orderOf (x * y) = r ∧ orderOf (x * y * x⁻¹ * y⁻¹) = s

noncomputable instance (r s : ℕ) (x : Equiv.Perm (Fin n)) :
    DecidablePred (PartnerRel r s x) := fun y =>
  inferInstanceAs (Decidable (orderOf (x * y) = r ∧ orderOf (x * y * x⁻¹ * y⁻¹) = s))

@[expose] noncomputable def partners (L : List (Equiv.Perm (Fin n))) (my r s : ℕ)
    (x : Equiv.Perm (Fin n)) : ℕ :=
  (L.filter fun h => decide (orderOf h = my)).countP fun y => decide (PartnerRel r s x y)

theorem partners_conj (H : Subgroup (Equiv.Perm (Fin n))) (L : List (Equiv.Perm (Fin n)))
    (hL : L.Nodup) (hmem : ∀ g, g ∈ L ↔ g ∈ H) (my r s : ℕ) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ H) (x : Equiv.Perm (Fin n)) :
    partners L my r s (c * x * c⁻¹) = partners L my r s x := by
  have hcard : ∀ z, partners L my r s z =
      Nat.card {y : H // orderOf (y : Equiv.Perm (Fin n)) = my ∧ PartnerRel r s z y} := by
    intro z
    rw [partners, List.countP_filter,
      card_subtype_eq_countP H L hL hmem (fun y => orderOf y = my ∧ PartnerRel r s z y)]
    congr 1
    funext y
    rw [Bool.decide_and, Bool.and_comm]
  rw [hcard, hcard]
  let e : H ≃ H := (MulAut.conj (⟨c, hc⟩ : H)).toEquiv
  refine (Nat.card_congr (e.subtypeEquiv fun y => ?_)).symm
  have hconj : ∀ g : Equiv.Perm (Fin n), orderOf (c * g * c⁻¹) = orderOf g := fun g =>
    MulEquiv.orderOf_eq (MulAut.conj c) g
  have he : ((e y : H) : Equiv.Perm (Fin n)) = c * y * c⁻¹ := rfl
  simp only [PartnerRel, he]
  rw [show c * x * c⁻¹ * (c * ↑y * c⁻¹) * (c * x * c⁻¹)⁻¹ * (c * ↑y * c⁻¹)⁻¹ =
      c * (x * ↑y * x⁻¹ * (↑y)⁻¹) * c⁻¹ by group,
    show c * x * c⁻¹ * (c * ↑y * c⁻¹) = c * (x * ↑y) * c⁻¹ by group, hconj, hconj, hconj]

theorem card_image_pairs_eq_classTotal (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {mx my r s : ℕ} (hmx : 0 < mx) (hmy : 0 < my) (hr : 0 < r)
    (hs : 0 < s) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (cap : ℕ) (hok : classOK n gens gensInv (orderTables Q mx) cap = true) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s} =
      classTotal n gens gensInv (orderTables Q mx) (orderTables Q my) cap r s mx my := by
  set H := Q.originalSubgroup
  set L := enumeration Q
  have hL : L.Nodup := enumeration_nodup Q hQ
  have hmem : ∀ g, g ∈ L ↔ g ∈ H := mem_enumeration_iff Q hQ
  set XG := L.filter fun h => decide (orderOf h = mx)
  have hX := forall₂_orderTables hn Q hmx
  have hY := forall₂_orderTables hn Q hmy
  have hcoe : ∀ p : H × H,
      (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s) ↔
      (orderOf (p.1 : Equiv.Perm (Fin n)) = mx ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = my ∧
        PartnerRel r s (p.1 : Equiv.Perm (Fin n)) p.2) := fun p => by
    simp only [PartnerRel, ← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
    card_pairs_eq_sum H L hL hmem (fun h => orderOf h = mx) (fun h => orderOf h = my)
      (PartnerRel r s)]
  simp only [classOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hidx, htree⟩, hdist⟩, hsum⟩ := hok
  have hXGmem : ∀ x ∈ XG, x ∈ H ∧ orderOf x = mx := fun x hx => by
    rw [List.mem_filter, decide_eq_true_eq] at hx
    exact ⟨(hmem x).1 hx.1, hx.2⟩
  have key := sum_eq_classSum H (partners L my r s) (fun c hc x => partners_conj H L hL hmem
    my r s hc x) XG (fun c hc x hx => by
      obtain ⟨hxH, hxo⟩ := hXGmem x hx
      rw [List.mem_filter, decide_eq_true_eq, hmem]
      exact ⟨H.mul_mem (H.mul_mem hc hxH) (H.inv_mem hc),
        (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hxo⟩) hg
    (fun T => (orderTables Q my).countP (pairTest n r s mx my T)) ?_
    (classes n gens gensInv (orderTables Q mx) cap) ?_ htree hdist ?_
  · exact key
  · intro T x hT hx
    obtain ⟨-, hxo⟩ := hXGmem x hx
    have hrev : (L.filter fun h => decide (orderOf h = my)).countP
        (fun y => decide (PartnerRel r s x y)) =
        (L.filter fun h => decide (orderOf h = my)).reverse.countP
          (fun y => decide (PartnerRel r s x y)) := List.countP_reverse.symm
    show _ = (L.filter fun h => decide (orderOf h = my)).countP _
    rw [hrev]
    refine countP_eq_of_forall₂ hY fun y yg hy hyg => ?_
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hyg
    rw [pairTest_iff perm_faithful hT hy hr hs hxo hyg.2 hmx hmy, decide_eq_true_iff]
    rfl
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    have hi' := hidx i hi
    have hlen : i < XG.reverse.length := by rw [← hX.length_eq]; exact hi'
    refine ⟨XG.reverse[i], List.mem_reverse.1 (List.getElem_mem hlen), ?_⟩
    have h := hX.get hi' hlen
    have harr : (orderTables Q mx).toArray[i]! = (orderTables Q mx)[i] := by
      rw [getElem!_pos (orderTables Q mx).toArray i (by simpa using hi')]
      simp
    simpa [harr] using h
  · rw [hsum, hX.length_eq, List.length_reverse]

@[expose] def pairTables (a b : Equiv.Perm (Fin n)) : Array Table := #[toTable a, toTable b]

theorem card_image_pairs_eq_classTotal₂ (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {mx my r s : ℕ} (hmx : 0 < mx) (hmy : 0 < my) (hr : 0 < r)
    (hs : 0 < s) {a b : Equiv.Perm (Fin n)} (ha : a ∈ Q.originalSubgroup)
    (hb : b ∈ Q.originalSubgroup) (cap : ℕ)
    (hok : classOK n (pairTables a b) (pairTables a⁻¹ b⁻¹) (orderTables Q mx) cap = true) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s} =
      classTotal n (pairTables a b) (pairTables a⁻¹ b⁻¹) (orderTables Q mx) (orderTables Q my)
        cap r s mx my := by
  refine card_image_pairs_eq_classTotal hn Q hQ hmx hmy hr hs
    (gg := fun l => if l = 0 then a else b) (fun l hl => ?_) cap hok
  have hl2 : l < 2 := by simpa [pairTables] using hl
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact ⟨by simpa [pairTables] using rep_toTable hn a,
      by simpa [pairTables] using rep_toTable hn a⁻¹, by simpa using ha⟩
  · exact ⟨by simpa [pairTables] using rep_toTable hn b,
      by simpa [pairTables] using rep_toTable hn b⁻¹, by simpa using hb⟩

end CFSG.Sporadic.Schreier
