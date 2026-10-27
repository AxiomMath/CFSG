module

public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

variable {n : ℕ}

theorem eq_of_commT {x y : Table} {xg yg : Equiv.Perm (Fin n)} (hx : Rep n x xg)
    (hy : Rep n y yg) (h : commT n x y = true) : xg * yg = yg * xg := by
  have h1 := Rep.compT hx hy
  have h2 := Rep.compT hy hx
  exact rep_unique h1 (rep_of_tblEq h2 h)

theorem eq_one_of_tblEq_idT (hn : n < 2 ^ 32) {x : Table} {xg : Equiv.Perm (Fin n)}
    (hx : Rep n x xg) (h : tblEq n x (idT n) = true) : xg = 1 :=
  rep_unique hx (rep_of_tblEq (Rep.idT hn) h)

@[expose] def allTables (Q : RawSchreierDatum n) : List Table :=
  filterProducts n allTrue (levelTables Q) (idT n) []

theorem forall₂_allTables (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) :
    List.Forall₂ (Rep n) (allTables Q) (enumeration Q).reverse := by
  have h := filterProducts_spec (f := allTrue) (P := fun _ : Equiv.Perm (Fin n) => True)
    (fun T g _ => by simp [allTrue]) (forall₂_levelTables hn Q) (Rep.idT hn) (acc := [])
    (accG := []) List.Forall₂.nil
  simp only [one_mul, List.map_id', List.append_nil, decide_true, List.filter_true] at h
  exact h

theorem exists_mem_of_forall₂_left {α β : Type*} {S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ S l m → ∀ b ∈ m, ∃ a ∈ l, S a b
  | _, _, .nil, b, hb => absurd hb (List.not_mem_nil)
  | a :: _, _ :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := exists_mem_of_forall₂_left h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem exists_mem_of_forall₂_right {α β : Type*} {S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ S l m → ∀ a ∈ l, ∃ b ∈ m, S a b
  | _, _, .nil, a, ha => absurd ha (List.not_mem_nil)
  | _ :: _, b :: _, .cons hab h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', h'⟩ := exists_mem_of_forall₂_right h a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem oddWitness_of_oddWitnessOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {m : ℕ} (h : oddWitnessOK n m (allTables Q) = true) :
    OddWitness Q.originalSubgroup m := by
  have hA := forall₂_allTables hn Q
  have hmem : ∀ g, g ∈ (enumeration Q).reverse ↔ g ∈ Q.originalSubgroup := fun g => by
    rw [List.mem_reverse, mem_enumeration_iff Q hQ]
  intro x hx hx1 hxm
  obtain ⟨X, hX, hXx⟩ := exists_mem_of_forall₂_left hA x ((hmem x).2 hx)
  have hall := (List.all_eq_true.1 h) X hX
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true] at hall
  rcases hall with ((hid | hpow) | ⟨H, hH, hinv, hne⟩) | ⟨H₁, hH₁, hinv₁, H₂, hH₂, hinv₂, hne⟩
  · exact absurd (eq_one_of_tblEq_idT hn hXx hid) hx1
  · have := (powFixW_iff perm_faithful (List.Forall₂.cons hXx List.Forall₂.nil) m).2
      (by simpa using hxm)
    rw [this] at hpow
    exact absurd hpow.symm Bool.false_ne_true
  · obtain ⟨hg, hhg, hHh⟩ := exists_mem_of_forall₂_right hA H hH
    have hHi := Rep.inv_of_invOK hHh hinv
    refine Or.inl ⟨hg, (hmem hg).1 hhg, fun heq => ?_⟩
    have hw : List.Forall₂ (Rep n) [X, H, X, invT n H] [x, hg, x, hg⁻¹] :=
      .cons hXx (.cons hHh (.cons hXx (.cons hHi .nil)))
    have := (powFixW_iff perm_faithful hw m).2 (by
      simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using heq)
    rw [this] at hne
    exact Bool.false_ne_true hne.symm
  · obtain ⟨hg₁, hhg₁, hH₁h⟩ := exists_mem_of_forall₂_right hA H₁ hH₁
    obtain ⟨hg₂, hhg₂, hH₂h⟩ := exists_mem_of_forall₂_right hA H₂ hH₂
    have hH₁i := Rep.inv_of_invOK hH₁h hinv₁
    have hH₂i := Rep.inv_of_invOK hH₂h hinv₂
    refine Or.inr ⟨hg₁, (hmem hg₁).1 hhg₁, hg₂, (hmem hg₂).1 hhg₂, fun heq => ?_⟩
    have hw : List.Forall₂ (Rep n) [X, H₁, X, invT n H₁, H₂, X, invT n H₂]
        [x, hg₁, x, hg₁⁻¹, hg₂, x, hg₂⁻¹] :=
      .cons hXx (.cons hH₁h (.cons hXx (.cons hH₁i (.cons hH₂h (.cons hXx (.cons hH₂i .nil))))))
    have := (powFixW_iff perm_faithful hw m).2 (by
      simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using heq)
    rw [this] at hne
    exact Bool.false_ne_true hne.symm

theorem centralizer_witness_of_reps (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n)) × ℕ × ℕ))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2.1 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2.1 =
        Nat.card Q.originalSubgroup ∧
      Nat.card d.2.1 = 2 ^ d.2.2.2 * d.2.2.1 ∧ OddWitness d.2.1 d.2.2.1) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 → ∃ mu vu : ℕ,
      Nat.card (centralizerIn Q.originalSubgroup u) = 2 ^ vu * mu ∧
        OddWitness (centralizerIn Q.originalSubgroup u) mu := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) ((data.map Prod.fst).map toTable)
      cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard, hKv, hKw⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  refine ⟨d.2.2.1, d.2.2.2, ?_, ?_⟩
  · rw [centralizerIn_conj _ hc, hcent,
      Subgroup.card_map_of_injective (MulAut.conj c).injective, hKv]
  · rw [centralizerIn_conj _ hc, hcent]
    exact hKw.map_conj c

section Shapes

variable {M : Type*} [Group M]

theorem map_centralizer_subtype (H : Subgroup M) (t : H) :
    (Subgroup.centralizer ({t} : Set H)).map H.subtype = centralizerIn H (t : M) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
    mem_centralizerIn]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxt, rfl⟩

theorem inner_oddCore_eq_bot (H : Subgroup M)
    (hw : ∀ u ∈ H, orderOf u = 2 → ∃ mu vu : ℕ, Nat.card (centralizerIn H u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn H u) mu) (t : H) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set H)) = ⊥ := by
  obtain ⟨mu, vu, hcard, hwit⟩ := hw t t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  rw [← map_centralizer_subtype] at hcard hwit
  rw [Subgroup.card_map_of_injective H.subtype_injective] at hcard
  exact oddCore_eq_bot_of_oddWitness hcard (hwit.of_map H.subtype_injective)

@[expose] def fixSub {G : Type*} [Group G] (α : MulAut G) : Subgroup G where
  carrier := {g | α g = g}
  one_mem' := map_one α
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_mul, hx, hy]
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_inv, hx]

theorem mem_fixSub {G : Type*} [Group G] {α : MulAut G} {g : G} : g ∈ fixSub α ↔ α g = g :=
  Iff.rfl

theorem map_fixSub_conjOn (H : Subgroup M) (α : MulAut H) (u : M)
    (hα : ∀ h : H, (α h : M) = u * h * u⁻¹) :
    (fixSub α).map H.subtype = centralizerIn H u := by
  ext x
  simp only [Subgroup.mem_map, mem_fixSub, Subgroup.coe_subtype, mem_centralizerIn]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have := congrArg Subtype.val hy
    rw [hα] at this
    calc (y : M) * u = u * y * u⁻¹ * u := by rw [this]
      _ = u * y := by group
  · rintro ⟨hx, hxu⟩
    refine ⟨⟨x, hx⟩, Subtype.ext ?_, rfl⟩
    rw [hα]
    calc u * x * u⁻¹ = x * u * u⁻¹ := by rw [hxu]
      _ = x := by group

theorem fixSub_oddCore_eq_bot (H : Subgroup M) (α : MulAut H) (u : M)
    (hα : ∀ h : H, (α h : M) = u * h * u⁻¹) {mu vu : ℕ}
    (hcard : Nat.card (centralizerIn H u) = 2 ^ vu * mu)
    (hwit : OddWitness (centralizerIn H u) mu) : CFSG.oddCore (fixSub α) = ⊥ := by
  rw [← map_fixSub_conjOn H α u hα] at hcard hwit
  rw [Subgroup.card_map_of_injective H.subtype_injective] at hcard
  exact oddCore_eq_bot_of_oddWitness hcard (hwit.of_map H.subtype_injective)

end Shapes

theorem evalCodes_mem (H : Subgroup (Equiv.Perm (Fin n))) {S : List (Equiv.Perm (Fin n))}
    (hS : ∀ g ∈ S, g ∈ H) : ∀ w : List ℤ, evalCodes S w ∈ H
  | [] => H.one_mem
  | z :: w => by
    have hget : ∀ k, S.getD k 1 ∈ H := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases h : S[k]? with
      | none => exact H.one_mem
      | some g => exact hS g (List.mem_of_getElem? h)
    rw [evalCodes]
    refine H.mul_mem ?_ (evalCodes_mem H hS w)
    split_ifs
    · exact hget _
    · exact H.inv_mem (hget _)

theorem pairTables_spec (hn : n < 2 ^ 32) {H : Subgroup (Equiv.Perm (Fin n))}
    {a b : Equiv.Perm (Fin n)} (ha : a ∈ H) (hb : b ∈ H) :
    ∀ l < (pairTables a b).size, Rep n (pairTables a b)[l]! (if l = 0 then a else b) ∧
      Rep n (pairTables a⁻¹ b⁻¹)[l]! (if l = 0 then a else b)⁻¹ ∧
      (if l = 0 then a else b) ∈ H := by
  intro l hl
  have hl2 : l < 2 := by simpa [pairTables] using hl
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact ⟨by simpa [pairTables] using rep_toTable hn a,
      by simpa [pairTables] using rep_toTable hn a⁻¹, by simpa using ha⟩
  · exact ⟨by simpa [pairTables] using rep_toTable hn b,
      by simpa [pairTables] using rep_toTable hn b⁻¹, by simpa using hb⟩

theorem closure_le_centralizerIn (hn : n < 2 ^ 32) {H : Subgroup (Equiv.Perm (Fin n))}
    {r : Equiv.Perm (Fin n)} {gs : List (Equiv.Perm (Fin n))} (hH : ∀ g ∈ gs, g ∈ H)
    (hc : gs.all (fun g => commT n (toTable g) (toTable r)) = true) :
    Subgroup.closure {g | g ∈ gs} ≤ centralizerIn H r := by
  rw [Subgroup.closure_le]
  intro g hg
  refine mem_centralizerIn.2 ⟨hH g hg, ?_⟩
  exact eq_of_commT (rep_toTable hn g) (rep_toTable hn r) (List.all_eq_true.1 hc g hg)

end CFSG.Sporadic.Schreier
