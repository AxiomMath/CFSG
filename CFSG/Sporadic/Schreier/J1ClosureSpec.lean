module

public import CFSG.Sporadic.Schreier.ClassSum

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def mulClosure (n : ℕ) (gens : Array Table) (cap : ℕ) :
    Array Table × Array ℕ × Array ℕ := Id.run do
  let mut seen : Std.HashSet ℕ := (∅ : Std.HashSet ℕ).insert (key n (idT n))
  let mut elts : Array Table := #[idT n]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  for h in [0:cap] do
    if h < elts.size then
      let y := elts[h]!
      for l in [0:gens.size] do
        let z := compT n y gens[l]!
        let kz := key n z
        if !seen.contains kz then
          seen := seen.insert kz
          elts := elts.push z
          par := par.push h
          lab := lab.push l
    else break
  return (elts, par, lab)

@[expose] def mulTreeOK (n : ℕ) (gens elts : Array Table) (par lab : Array ℕ) : Bool :=
  0 < elts.size && tblEq n elts[0]! (idT n) &&
    allIn 1 elts.size fun k => decide (par[k]! < k) && decide (lab[k]! < gens.size) &&
      tblEq n elts[k]! (compT n elts[par[k]!]! gens[lab[k]!]!)

@[expose] def mulClosedOK (n : ℕ) (gens gensInv elts : Array Table) : Bool :=
  elts.all fun e => (List.range gens.size).all fun l =>
    elts.any (fun f => tblEq n f (compT n e gens[l]!)) &&
      elts.any (fun f => tblEq n f (compT n e gensInv[l]!))

variable {n : ℕ}

theorem exists_rep_of_any {elts : Array Table} {T : Table} {g : Equiv.Perm (Fin n)}
    (hT : Rep n T g) (h : elts.any (fun f => tblEq n f T) = true) :
    ∃ k < elts.size, Rep n elts[k]! g := by
  rw [Array.any_eq_true] at h
  obtain ⟨k, hk, hkT⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [getElem!_pos elts k hk]
  exact rep_of_tblEq hT hkT

theorem mem_closure_iff_of_mulTree (hn : n < 2 ^ 32) {gens gensInv elts : Array Table}
    {par lab : Array ℕ} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹)
    (htree : mulTreeOK n gens elts par lab = true)
    (hclosed : mulClosedOK n gens gensInv elts = true) (g : Equiv.Perm (Fin n)) :
    g ∈ Subgroup.closure (gg '' {l | l < gens.size}) ↔ ∃ k < elts.size, Rep n elts[k]! g := by
  simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
  obtain ⟨⟨hpos, h0⟩, hstep⟩ := htree
  have hcl := fun e (he : e ∈ elts) l (hl : l < gens.size) =>
    (List.all_eq_true.1 ((Array.all_eq_true_iff_forall_mem.1 hclosed) e he) l
      (List.mem_range.2 hl))
  constructor
  · intro hgm
    induction hgm using Subgroup.closure_induction_right with
    | one => exact ⟨0, hpos, rep_of_tblEq (Rep.idT hn) h0⟩
    | mul_right x _ y hy ih =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨k, hk, hrep⟩ := ih
      have hmem : elts[k]! ∈ elts := by
        rw [getElem!_pos elts k hk]
        exact Array.getElem_mem hk
      have := hcl _ hmem l hl
      rw [Bool.and_eq_true] at this
      exact exists_rep_of_any (Rep.compT hrep (hg l hl).1) this.1
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨k, hk, hrep⟩ := ih
      have hmem : elts[k]! ∈ elts := by
        rw [getElem!_pos elts k hk]
        exact Array.getElem_mem hk
      have := hcl _ hmem l hl
      rw [Bool.and_eq_true] at this
      exact exists_rep_of_any (Rep.compT hrep (hg l hl).2) this.2
  · rintro ⟨k, hk, hrep⟩
    have key : ∀ k, k < elts.size → ∃ g' ∈ Subgroup.closure (gg '' {l | l < gens.size}),
        Rep n elts[k]! g' := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · exact ⟨1, Subgroup.one_mem _, rep_of_tblEq (Rep.idT hn) h0⟩
        · have hs := allIn_eq_true.1 hstep k hk0 hk
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
          obtain ⟨⟨hpar, hlab⟩, heq⟩ := hs
          obtain ⟨g', hg', hrep'⟩ := ih _ hpar (hpar.trans hk)
          exact ⟨g' * gg lab[k]!, Subgroup.mul_mem _ hg'
            (Subgroup.subset_closure ⟨_, hlab, rfl⟩),
            rep_of_tblEq (Rep.compT hrep' (hg _ hlab).1) heq⟩
    obtain ⟨g', hg', hrep'⟩ := key k hk
    rw [rep_unique hrep hrep']
    exact hg'

theorem exists_rep_of_mulTree (hn : n < 2 ^ 32) {gens elts : Array Table} {par lab : Array ℕ}
    {gg : ℕ → Equiv.Perm (Fin n)} (hg : ∀ l < gens.size, Rep n gens[l]! (gg l))
    (htree : mulTreeOK n gens elts par lab = true) :
    ∀ k < elts.size, ∃ g : Equiv.Perm (Fin n), Rep n elts[k]! g := by
  simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
  obtain ⟨⟨-, h0⟩, hstep⟩ := htree
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨1, rep_of_tblEq (Rep.idT hn) h0⟩
    · have hs := allIn_eq_true.1 hstep k hk0 hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨hpar, hlab⟩, heq⟩ := hs
      obtain ⟨g', hrep'⟩ := ih _ hpar (hpar.trans hk)
      exact ⟨g' * gg lab[k]!, rep_of_tblEq (Rep.compT hrep' (hg _ hlab)) heq⟩

@[expose] noncomputable def closurePerms (n : ℕ) (elts : Array Table) :
    List (Equiv.Perm (Fin n)) :=
  elts.toList.map (tablePerm n)

theorem card_closure_of_mulTree (hn : n < 2 ^ 32) {gens gensInv elts : Array Table}
    {par lab : Array ℕ} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size, Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹)
    (htree : mulTreeOK n gens elts par lab = true)
    (hclosed : mulClosedOK n gens gensInv elts = true)
    (hkeys : keysDistinct n elts.toList = true) :
    List.Forall₂ (Rep n) elts.toList (closurePerms n elts) ∧ (closurePerms n elts).Nodup ∧
      (∀ g, g ∈ closurePerms n elts ↔ g ∈ Subgroup.closure (gg '' {l | l < gens.size})) ∧
      Nat.card (Subgroup.closure (gg '' {l | l < gens.size})) = elts.size := by
  have hrep : ∀ k (hk : k < elts.size), Rep n elts[k] (tablePerm n elts[k]) := by
    intro k hk
    obtain ⟨g', hg'⟩ := exists_rep_of_mulTree hn (fun l hl => (hg l hl).1) htree k hk
    rw [getElem!_pos elts k hk] at hg'
    rw [tablePerm_eq hg']
    exact hg'
  have hF : List.Forall₂ (Rep n) elts.toList (closurePerms n elts) := by
    rw [closurePerms, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    simp only [Array.length_toList] at hk
    simpa using hrep k hk
  have hnd := nodup_of_keysDistinct hF hkeys
  have hmem : ∀ g, g ∈ closurePerms n elts ↔
      g ∈ Subgroup.closure (gg '' {l | l < gens.size}) := by
    intro g
    rw [mem_closure_iff_of_mulTree hn hg htree hclosed]
    constructor
    · intro hgm
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hgm
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
      simp only [Array.length_toList] at hk
      refine ⟨k, hk, ?_⟩
      rw [getElem!_pos elts k hk]
      simpa using hrep k hk
    · rintro ⟨k, hk, hrk⟩
      rw [getElem!_pos elts k hk] at hrk
      refine List.mem_map.2 ⟨elts[k], by simp, ?_⟩
      exact rep_unique (hrep k hk) hrk
  refine ⟨hF, hnd, hmem, ?_⟩
  have h := card_eq_length (fun g => g ∈ Subgroup.closure (gg '' {l | l < gens.size}))
    (fun g => g) (fun _ _ h => h) _ hnd fun g => by
      rw [hmem]
      exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨a, ha, hag⟩ => hag ▸ ha⟩
  rw [closurePerms, List.length_map, Array.length_toList] at h
  exact h

theorem isSimpleGroup_of_labels {M : Type*} [Group M] (D : Subgroup M) {N₀ r : ℕ} (hr : 0 < r)
    (hcard : Nat.card D = N₀) (h1 : 1 < N₀) (e : ℕ → M)
    (he : ∀ k < N₀, e k ∈ D) (hinj : ∀ i < N₀, ∀ j < N₀, e i = e j → i = j)
    (hsurj : ∀ g ∈ D, ∃ k < N₀, e k = g) (lab cj rep : ℕ → ℕ) (hrep0 : e (rep 0) = 1)
    (hrep : ∀ i < r, rep i < N₀)
    (hlab : ∀ k < N₀, lab k < r ∧ cj k < N₀ ∧ e k = e (cj k) * e (rep (lab k)) * (e (cj k))⁻¹)
    (hsub : ∀ b : Fin r → Bool, b ⟨0, hr⟩ = true →
      ((List.range N₀).countP fun k => if h : lab k < r then b ⟨lab k, h⟩ else false) ∣ N₀ →
      ((List.range N₀).countP fun k => if h : lab k < r then b ⟨lab k, h⟩ else false) = 1 ∨
      ((List.range N₀).countP fun k => if h : lab k < r then b ⟨lab k, h⟩ else false) = N₀) :
    IsSimpleGroup D := by
  classical
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial D := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  refine ⟨fun N hN => ?_⟩
  set N' : Subgroup M := N.map D.subtype with hN'
  have hmemN : ∀ x : D, (x : M) ∈ N' ↔ x ∈ N := fun x => by
    rw [hN', Subgroup.mem_map]
    exact ⟨fun ⟨y, hy, hyx⟩ => (Subtype.ext hyx : y = x) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hconj : ∀ c x : M, c ∈ D → x ∈ D → x ∈ N' → c * x * c⁻¹ ∈ N' := by
    intro c x hc hx hxN
    have := hN.conj_mem ⟨x, hx⟩ ((hmemN ⟨x, hx⟩).1 hxN) ⟨c, hc⟩
    exact (hmemN _).2 this
  have hk : ∀ k < N₀, (e k ∈ N' ↔ e (rep (lab k)) ∈ N') := by
    intro k hk
    obtain ⟨hl, hc, heq⟩ := hlab k hk
    have hcD := he _ hc
    have hrD := he _ (hrep _ hl)
    constructor
    · intro h
      have h' := hconj (e (cj k))⁻¹ (e k) (D.inv_mem hcD) (he k hk) h
      have e' : (e (cj k))⁻¹ * e k * (e (cj k))⁻¹⁻¹ = e (rep (lab k)) := by
        rw [heq]
        group
      rwa [e'] at h'
    · intro h
      rw [heq]
      exact hconj _ _ hcD hrD h
  let b : Fin r → Bool := fun i => decide (e (rep i) ∈ N')
  have hb0 : b ⟨0, hr⟩ = true := by
    simp only [b, decide_eq_true_eq]
    rw [hrep0]
    exact N'.one_mem
  set L := (List.range N₀).map e
  have hLnd : L.Nodup := by
    refine List.Nodup.map_on (fun i hi j hj hij => hinj i (List.mem_range.1 hi) j
      (List.mem_range.1 hj) hij) List.nodup_range
  have hLmem : ∀ g, g ∈ L ↔ g ∈ D := fun g => by
    simp only [L, List.mem_map, List.mem_range]
    exact ⟨fun ⟨k, hk, hkg⟩ => hkg ▸ he k hk, fun hg => hsurj g hg⟩
  have hcardN : Nat.card N =
      (List.range N₀).countP fun k => if h : lab k < r then b ⟨lab k, h⟩ else false := by
    have h₁ : Nat.card N = Nat.card {x : D // (x : M) ∈ N'} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmemN x).symm)
    rw [h₁, card_subtype_eq_countP D L hLnd hLmem (fun g => g ∈ N'), List.countP_map]
    refine List.countP_congr fun k hkm => ?_
    have hk' := List.mem_range.1 hkm
    have hl := (hlab k hk').1
    simp only [Function.comp_apply, hl, dite_true, b, decide_eq_true_eq]
    exact hk k hk'
  have hdvd : Nat.card N ∣ N₀ := hcard ▸ Subgroup.card_subgroup_dvd_card N
  rw [hcardN] at hdvd
  rcases hsub b hb0 hdvd with h | h
  · left
    exact Subgroup.eq_bot_of_card_eq N (hcardN.trans h)
  · right
    exact Subgroup.eq_top_of_card_eq N (by rw [hcardN, h, hcard])

end CFSG.Sporadic.Schreier
