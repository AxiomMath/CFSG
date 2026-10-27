module

public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def prod2A (n : ℕ) (L : Array Level) (a b : ℕ) : Array ℕ :=
  compA n L[0]!.tr[a]! L[1]!.tr[b]!

@[expose] def prod3A (n : ℕ) (L : Array Level) (a b c : ℕ) : Array ℕ :=
  compA n (compA n L[0]!.tr[a]! L[1]!.tr[b]!) L[2]!.tr[c]!

@[expose] def all2 (n : ℕ) (L : Array Level) (p : Array ℕ → Bool) : Bool :=
  allLt L[0]!.pts.size fun a => allLt L[1]!.pts.size fun b => p (prod2A n L a b)

@[expose] def all3 (n : ℕ) (L : Array Level) (p : Array ℕ → Bool) : Bool :=
  allLt L[0]!.pts.size fun a => allLt L[1]!.pts.size fun b => allLt L[2]!.pts.size fun c =>
    p (prod3A n L a b c)

@[expose] def count2 (n : ℕ) (L : Array Level) (p : Array ℕ → Bool) : ℕ :=
  ∑ a ∈ Finset.range L[0]!.pts.size, ∑ b ∈ Finset.range L[1]!.pts.size,
    if p (prod2A n L a b) then 1 else 0

@[expose] def count3 (n : ℕ) (L : Array Level) (p : Array ℕ → Bool) : ℕ :=
  ∑ a ∈ Finset.range L[0]!.pts.size, ∑ b ∈ Finset.range L[1]!.pts.size,
    ∑ c ∈ Finset.range L[2]!.pts.size, if p (prod3A n L a b c) then 1 else 0

theorem card_subtype_of_bijective {α β : Type*} [Fintype α] {Φ : α → β}
    (hΦ : Function.Bijective Φ) (P : β → Prop) [DecidablePred P] :
    Nat.card {g : β // P g} = ∑ x : α, if P (Φ x) then 1 else 0 := by
  classical
  rw [← Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective Φ hΦ) (fun _ => Iff.rfl)),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rfl

section ChainArrays

open CFSG.Certificates.ChainArrays

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

theorem chain_exists_prod2 (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) (h2 : 2 ≤ Q.baseCount)
    (h1 : ∀ i, 2 ≤ i → i < Q.baseCount → (lev n S base i).pts.size = 1)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup) :
    ∃ a < (lev n S base 0).pts.size, ∃ b < (lev n S base 1).pts.size,
      levT n S base 0 a * levT n S base 1 b = g := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  obtain ⟨-, Φ, hΦ, hbij, -⟩ := Q.schreier_transversal_product_bijection hQ
  obtain ⟨y, hy⟩ := hbij.2 ⟨g, hg⟩
  have hg' : g = (List.ofFn fun i => Q.orbitTransversal i (y i)).prod := by
    rw [← hΦ y, hy]
  have hT : ∀ i : Fin Q.baseCount, Q.orbitTransversal i (y i) =
      levT n S base i (lev n S base i).pos[((y i : Fin n) : ℕ)]! := fun i =>
    (hA.orbitPoints_spec hF i.2 (y i).2).2.2
  have hK : ∀ i : Fin Q.baseCount,
      (lev n S base i).pos[((y i : Fin n) : ℕ)]! < (lev n S base i).pts.size := fun i =>
    (hA.orbitPoints_spec hF i.2 (y i).2).1
  have h1' : ∀ i : Fin Q.baseCount, 2 ≤ i.val → Q.orbitTransversal i (y i) = 1 := by
    intro i hi
    have hk := hK i
    rw [h1 i hi i.2] at hk
    rw [hT i, show (lev n S base i).pos[((y i : Fin n) : ℕ)]! = 0 by omega]
    exact hA.levT_zero hF i.2
  rw [prod_ofFn_eq_of_one h2 (fun i => Q.orbitTransversal i (y i)) h1'] at hg'
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, hT] at hg'
  refine ⟨_, hK ⟨0, by omega⟩, _, hK ⟨1, by omega⟩, ?_⟩
  rw [hg']
  rfl

section Facts

variable (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
  (h : rawChainOK n O S base W chunks = true)
include hA hc h

theorem chain_levT_mem_original {i k : ℕ} (hi : i < Q.baseCount)
    (hk : k < (lev n S base i).pts.size) :
    levT n S base i k ∈ Q.originalSubgroup := by
  have hQ := (validSchreier_of_chainOK hA hc h).1
  rw [← Q.levelSubgroup_zero_eq_original hQ]
  exact Q.levelSubgroup_antitone 0 i (Nat.zero_le _) (hA.levT_mem (chainCheckFacts h) hi hk)

omit hc in
theorem chain_rep_prod2A (h2 : 2 ≤ Q.baseCount) {a b : ℕ} (ha : a < (lev n S base 0).pts.size)
    (hb : b < (lev n S base 1).pts.size) :
    Rep n (prod2A n (rawLevels n S base) a b) (levT n S base 0 a * levT n S base 1 b) :=
  rep_compA (hA.rep_levT (chainCheckFacts h) (by omega) ha)
    (hA.rep_levT (chainCheckFacts h) (by omega) hb)

omit hc in
theorem chain_rep_prod3A (h3 : 3 ≤ Q.baseCount) {a b c : ℕ} (ha : a < (lev n S base 0).pts.size)
    (hb : b < (lev n S base 1).pts.size) (hc' : c < (lev n S base 2).pts.size) :
    Rep n (prod3A n (rawLevels n S base) a b c)
      (levT n S base 0 a * levT n S base 1 b * levT n S base 2 c) :=
  rep_compA (rep_compA (hA.rep_levT (chainCheckFacts h) (by omega) ha)
    (hA.rep_levT (chainCheckFacts h) (by omega) hb))
    (hA.rep_levT (chainCheckFacts h) (by omega) hc')

theorem chain_forall_of_all2 (h2 : 2 ≤ Q.baseCount)
    (h1 : ∀ i, 2 ≤ i → i < Q.baseCount → (lev n S base i).pts.size = 1)
    {p : Array ℕ → Bool} {P : Equiv.Perm (Fin n) → Prop}
    (hp : ∀ t g, Rep n t g → p t = true → P g) (hall : all2 n (rawLevels n S base) p = true) :
    ∀ g ∈ Q.originalSubgroup, P g := by
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := chain_exists_prod2 hA hc h h2 h1 hg
  exact hp _ _ (chain_rep_prod2A hA h h2 ha hb) (allLt_spec (allLt_spec hall ha) hb)

theorem chain_forall_of_all3 (h3 : 3 ≤ Q.baseCount)
    (h1 : ∀ i, 3 ≤ i → i < Q.baseCount → (lev n S base i).pts.size = 1)
    {p : Array ℕ → Bool} {P : Equiv.Perm (Fin n) → Prop}
    (hp : ∀ t g, Rep n t g → p t = true → P g) (hall : all3 n (rawLevels n S base) p = true) :
    ∀ g ∈ Q.originalSubgroup, P g := by
  intro g hg
  obtain ⟨a, ha, b, hb, c, hc', rfl⟩ := exists_prod3 hA hc h h3 h1 hg
  exact hp _ _ (chain_rep_prod3A hA h h3 ha hb hc')
    (allLt_spec (allLt_spec (allLt_spec hall ha) hb) hc')

omit hc h in
theorem chain_rawOrbitSizes_eq : rawOrbitSizes n S base =
    (List.range Q.baseCount).map fun i => (lev n S base i).pts.size := by
  rw [rawOrbitSizes]
  apply List.ext_getElem
  · simp [ChainArrays.chainLevels_size, hA.base_size]
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    have hk : k < (rawLevels n S base).size := by simpa using h1
    rw [lev, getElem!_pos _ k hk]

theorem chain_card_of_count2 (h2 : Q.baseCount = 2) {p : Array ℕ → Bool}
    {P : Equiv.Perm (Fin n) → Prop} (hp : ∀ t g, Rep n t g → (p t = true ↔ P g)) :
    Nat.card {g : Q.originalSubgroup // P g} = count2 n (rawLevels n S base) p := by
  classical
  set s0 := (lev n S base 0).pts.size
  set s1 := (lev n S base 1).pts.size
  let Φ : Fin s0 × Fin s1 → Q.originalSubgroup := fun x =>
    ⟨levT n S base 0 x.1 * levT n S base 1 x.2, Q.originalSubgroup.mul_mem
      (chain_levT_mem_original hA hc h (by omega) x.1.2)
      (chain_levT_mem_original hA hc h (by omega) x.2.2)⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      chain_exists_prod2 hA hc h (by omega) (fun i hi hi' => by omega) hg
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hcard : Nat.card Q.originalSubgroup = s0 * s1 := by
    rw [card_originalSubgroup_of_chainOK hA hc h, chain_rawOrbitSizes_eq hA, h2]
    simp [List.range_succ, s0, s1]
  have hbij : Function.Bijective Φ := hsurj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin, hcard])
  rw [card_subtype_of_bijective hbij, Fintype.sum_prod_type]
  have e : ∀ (a : Fin s0) (b : Fin s1), (if P (Φ (a, b)) then 1 else 0) =
      (fun a b : ℕ => if p (prod2A n (rawLevels n S base) a b) then 1 else 0) a b := by
    intro a b
    dsimp only
    rw [(hp _ _ (chain_rep_prod2A hA h (by omega) a.2 b.2)).symm]
    congr
  simp only [e]
  rw [count2]
  have e2 : ∀ a : ℕ, ∑ b : Fin s1, (if p (prod2A n (rawLevels n S base) a b) then 1 else 0) =
      ∑ b ∈ Finset.range s1, (if p (prod2A n (rawLevels n S base) a b) then 1 else 0) :=
    fun a => Fin.sum_univ_eq_sum_range (fun b => if p (prod2A n (rawLevels n S base) a b) then 1
      else 0) s1
  simp only [e2]
  exact Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range s1,
    (if p (prod2A n (rawLevels n S base) a b) then 1 else 0)) s0

theorem chain_card_of_count3 (h3 : Q.baseCount = 3) {p : Array ℕ → Bool}
    {P : Equiv.Perm (Fin n) → Prop} (hp : ∀ t g, Rep n t g → (p t = true ↔ P g)) :
    Nat.card {g : Q.originalSubgroup // P g} = count3 n (rawLevels n S base) p := by
  classical
  set s0 := (lev n S base 0).pts.size
  set s1 := (lev n S base 1).pts.size
  set s2 := (lev n S base 2).pts.size
  let Φ : Fin s0 × Fin s1 × Fin s2 → Q.originalSubgroup := fun x =>
    ⟨levT n S base 0 x.1 * levT n S base 1 x.2.1 * levT n S base 2 x.2.2,
      Q.originalSubgroup.mul_mem (Q.originalSubgroup.mul_mem
        (chain_levT_mem_original hA hc h (by omega) x.1.2)
        (chain_levT_mem_original hA hc h (by omega) x.2.1.2))
        (chain_levT_mem_original hA hc h (by omega) x.2.2.2)⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, c, hc', rfl⟩ := exists_prod3 hA hc h (by omega)
      (fun i hi hi' => by omega) hg
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc'⟩), rfl⟩
  have hcard : Nat.card Q.originalSubgroup = s0 * (s1 * s2) := by
    rw [card_originalSubgroup_of_chainOK hA hc h, chain_rawOrbitSizes_eq hA, h3]
    simp [List.range_succ, s0, s1, s2]
  have hbij : Function.Bijective Φ := hsurj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, hcard])
  rw [card_subtype_of_bijective hbij, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  have e : ∀ (a : Fin s0) (b : Fin s1) (c : Fin s2), (if P (Φ (a, b, c)) then 1 else 0) =
      (fun a b c : ℕ => if p (prod3A n (rawLevels n S base) a b c) then 1 else 0) a b c := by
    intro a b c
    dsimp only
    rw [(hp _ _ (chain_rep_prod3A hA h (by omega) a.2 b.2 c.2)).symm]
    congr
  simp only [e]
  rw [count3]
  have e3 : ∀ a b : ℕ, ∑ c : Fin s2, (if p (prod3A n (rawLevels n S base) a b c) then 1 else 0) =
      ∑ c ∈ Finset.range s2, (if p (prod3A n (rawLevels n S base) a b c) then 1 else 0) :=
    fun a b => Fin.sum_univ_eq_sum_range
      (fun c => if p (prod3A n (rawLevels n S base) a b c) then 1 else 0) s2
  simp only [e3]
  have e2 : ∀ a : ℕ, ∑ b : Fin s1, ∑ c ∈ Finset.range s2,
      (if p (prod3A n (rawLevels n S base) a b c) then 1 else 0) =
      ∑ b ∈ Finset.range s1, ∑ c ∈ Finset.range s2,
        (if p (prod3A n (rawLevels n S base) a b c) then 1 else 0) :=
    fun a => Fin.sum_univ_eq_sum_range (fun b => ∑ c ∈ Finset.range s2,
      (if p (prod3A n (rawLevels n S base) a b c) then 1 else 0)) s1
  simp only [e2]
  exact Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range s1, ∑ c ∈ Finset.range s2,
    (if p (prod3A n (rawLevels n S base) a b c) then 1 else 0)) s0

end Facts

end ChainArrays

end CFSG.Sporadic.RuSchreier
