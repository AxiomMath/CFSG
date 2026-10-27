module

public import CFSG.Certificates.SchreierTransversalProduct

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates

variable {n : ℕ}

@[expose] def products {M : Type*} [Monoid M] : List (List M) → List M
  | [] => [1]
  | T :: Ts => T.flatMap fun t => (products Ts).map (t * ·)

theorem length_products {M : Type*} [Monoid M] (Ts : List (List M)) :
    (products Ts).length = (Ts.map List.length).prod := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih =>
    simp only [products, List.length_flatMap, List.length_map, ih, List.map_cons,
      List.prod_cons, List.map_const', List.sum_replicate, smul_eq_mul]

theorem prod_map_mem_products {M ι : Type*} [Monoid M] (T : ι → List M) (f : ι → M) :
    ∀ l : List ι, (∀ i ∈ l, f i ∈ T i) → (l.map f).prod ∈ products (l.map T)
  | [], _ => by simp [products]
  | i :: l, h => by
    simp only [List.map_cons, List.prod_cons, products, List.mem_flatMap, List.mem_map]
    exact ⟨f i, h i List.mem_cons_self, (l.map f).prod,
      prod_map_mem_products T f l fun j hj => h j (List.mem_cons_of_mem i hj), rfl⟩

theorem mem_of_mem_products {M : Type*} [Monoid M] (H : Submonoid M) :
    ∀ Ts : List (List M), (∀ T ∈ Ts, ∀ t ∈ T, t ∈ H) → ∀ g ∈ products Ts, g ∈ H
  | [], _, g, hg => by
    simp only [products, List.mem_singleton] at hg
    exact hg ▸ H.one_mem
  | T :: Ts, h, g, hg => by
    simp only [products, List.mem_flatMap, List.mem_map] at hg
    obtain ⟨t, ht, u, hu, rfl⟩ := hg
    exact H.mul_mem (h T List.mem_cons_self t ht)
      (mem_of_mem_products H Ts (fun T' hT' => h T' (List.mem_cons_of_mem T hT')) u hu)

@[expose] def levelTransversals (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    List (Equiv.Perm (Fin n)) :=
  let q := Q.orbitSearch i
  q.keys.map fun x => (q.transversal? x).getD 1

@[expose] def enumeration (Q : RawSchreierDatum n) : List (Equiv.Perm (Fin n)) :=
  products ((List.finRange Q.baseCount).map (levelTransversals Q))

theorem length_levelTransversals (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    (levelTransversals Q i).length = Q.orbitSize i := by
  simp [levelTransversals, RawSchreierDatum.orbitSize]

theorem length_enumeration (Q : RawSchreierDatum n) :
    (enumeration Q).length = Q.orderCertificate := by
  rw [enumeration, length_products, List.map_map, RawSchreierDatum.orderCertificate]
  congr 1
  exact List.map_congr_left fun i _ => length_levelTransversals Q i

theorem mem_levelSubgroup_of_mem_levelTransversals (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) {t : Equiv.Perm (Fin n)} (ht : t ∈ levelTransversals Q i) :
    t ∈ Q.levelSubgroup i.val := by
  simp only [levelTransversals, List.mem_map] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  have hx' : x ∈ Q.orbitPoints i :=
    (SchreierOrbitState.mem_points_iff_mem_keys (Q.orbitSearch i) x).2 hx
  exact (Q.transversal_getD_spec i x hx').2.1

theorem orbitTransversal_mem_levelTransversals (Q : RawSchreierDatum n)
    (i : Fin Q.baseCount) (x : Q.orbitPoints i) :
    Q.orbitTransversal i x ∈ levelTransversals Q i := by
  simp only [levelTransversals, List.mem_map]
  exact ⟨x, (SchreierOrbitState.mem_points_iff_mem_keys (Q.orbitSearch i) x).1 x.2, rfl⟩

theorem mem_enumeration_iff (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (g : Equiv.Perm (Fin n)) : g ∈ enumeration Q ↔ g ∈ Q.originalSubgroup := by
  constructor
  · intro hg
    rw [← Q.levelSubgroup_zero_eq_original hQ]
    refine mem_of_mem_products (Q.levelSubgroup 0).toSubmonoid _ ?_ g hg
    intro T hT t ht
    simp only [List.mem_map, List.mem_finRange, true_and] at hT
    obtain ⟨i, rfl⟩ := hT
    exact Q.levelSubgroup_antitone 0 i.val (Nat.zero_le _)
      (mem_levelSubgroup_of_mem_levelTransversals Q i ht)
  · intro hg
    obtain ⟨Φ, hΦ, hbij, -⟩ := (Q.schreier_transversal_product_bijection hQ).2
    obtain ⟨v, hv⟩ := hbij.2 ⟨g, hg⟩
    have hgv : g = ((List.finRange Q.baseCount).map fun i => Q.orbitTransversal i (v i)).prod := by
      rw [← List.ofFn_eq_map, ← hΦ v, hv]
    rw [hgv]
    exact prod_map_mem_products (levelTransversals Q) (fun i => Q.orbitTransversal i (v i)) _
      fun i _ => orbitTransversal_mem_levelTransversals Q i (v i)

theorem enumeration_nodup (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) :
    (enumeration Q).Nodup := by
  classical
  apply List.nodup_iff_le_length_dedup.2
  rw [length_enumeration, Q.orderCertificate_eq_card hQ, ← List.card_toFinset]
  let e : Q.originalSubgroup → (enumeration Q).toFinset := fun g =>
    ⟨g.1, List.mem_toFinset.2 ((mem_enumeration_iff Q hQ g.1).2 g.2)⟩
  have he : Function.Injective e := fun g h hgh =>
    Subtype.ext (congrArg (fun x : (enumeration Q).toFinset => (x : Equiv.Perm (Fin n))) hgh)
  have := Nat.card_le_card_of_injective e he
  rwa [Nat.card_eq_fintype_card (α := (enumeration Q).toFinset), Fintype.card_coe] at this

theorem card_eq_length {α β : Type*} (p : α → Prop) (e : α → β) (he : Function.Injective e)
    (L : List β) (hL : L.Nodup) (hmem : ∀ b, b ∈ L ↔ ∃ a, p a ∧ e a = b) :
    Nat.card {a // p a} = L.length := by
  classical
  let f : {a // p a} → L.toFinset := fun a =>
    ⟨e a.1, List.mem_toFinset.2 ((hmem _).2 ⟨a.1, a.2, rfl⟩)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (he (congrArg Subtype.val hab)), fun b => ?_⟩
    obtain ⟨a, ha, hab⟩ := (hmem b.1).1 (List.mem_toFinset.1 b.2)
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hL]

@[expose] def tab (g : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  let f := Array.ofFn g
  let f' := Array.ofFn g.symm
  { toFun := fun i => f[i.val]'(by simp [f])
    invFun := fun i => f'[i.val]'(by simp [f'])
    left_inv := fun i => by simp [f, f']
    right_inv := fun i => by simp [f, f'] }

theorem tab_eq (g : Equiv.Perm (Fin n)) : tab g = g := by
  ext i
  simp [tab]

@[expose] def evalCodes (S : List (Equiv.Perm (Fin n))) : List ℤ → Equiv.Perm (Fin n)
  | [] => 1
  | z :: w =>
    (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) * evalCodes S w

@[expose] def buildStrong (S : List (Equiv.Perm (Fin n))) :
    List (List ℤ) → List (Equiv.Perm (Fin n))
  | [] => S
  | w :: ws => buildStrong (S ++ [tab (evalCodes S w)]) ws

theorem length_buildStrong (S : List (Equiv.Perm (Fin n))) (ws : List (List ℤ)) :
    (buildStrong S ws).length = S.length + ws.length := by
  induction ws generalizing S with
  | nil => rfl
  | cons w ws ih =>
    rw [buildStrong, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

@[expose] def decodeLetter (j : ℕ) (z : ℤ) : Option (SchreierLetter j) :=
  if h : z.natAbs - 1 < j then some (⟨z.natAbs - 1, h⟩, decide (0 < z)) else none

@[expose] def decodeWord (j : ℕ) (w : List ℤ) : List (SchreierLetter j) :=
  w.filterMap (decodeLetter j)

@[expose] def certificate (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) {k : ℕ} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) :
    RawSchreierDatum n where
  degree_pos := hn
  originalCount := gens.length
  strongCount := gens.length + words.length
  baseCount := k
  originalCount_le := Nat.le_add_right _ _
  original := ⟨gens.toArray, List.size_toArray⟩
  strong := ⟨(buildStrong gens words).toArray, by
    rw [List.size_toArray, length_buildStrong]⟩
  base := base
  base_distinct := hbase
  derivation := fun j _ => decodeWord j.val (words.getD (j.val - gens.length) [])

theorem certificate_original (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) {k : ℕ} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) :
    (certificate hn gens words base hbase).original.toList = gens := by
  simp [certificate]

theorem certificate_originalSubgroup (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) {k : ℕ} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) :
    (certificate hn gens words base hbase).originalSubgroup =
      Subgroup.closure {g | g ∈ gens} := by
  rw [RawSchreierDatum.originalSubgroup, certificate_original]

@[expose] def orderIs {M : Type*} [Monoid M] [DecidableEq M] (g : M) (m : ℕ) : Bool :=
  decide (g ^ m = 1) && (List.range m).all fun k => k == 0 || !decide (g ^ k = 1)

theorem orderIs_iff {M : Type*} [Monoid M] [DecidableEq M] (g : M) {m : ℕ} (hm : 0 < m) :
    orderIs g m = true ↔ orderOf g = m := by
  rw [orderOf_eq_iff hm]
  simp only [orderIs, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk hk0 => ?_⟩
    rcases h2 k hk with h | h
    · omega
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inl h
    · exact Or.inr (h2 k hk h)

end CFSG.Sporadic.Schreier
