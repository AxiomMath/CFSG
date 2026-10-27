module

public import CFSG.YGroups.DCE.PermBSpec
public import CFSG.YGroups.DoubleCosetPoints
public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import Batteries.Data.ByteArray

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def recValidN (n β : ℕ) (gens : Array ByteArray)
    (r : Array ℕ × Array ℕ × Array ℕ × Array ℕ) : Bool :=
  decide (β < n) && r.2.1.size == n && r.1.size != 0 && r.1[0]! == β &&
    allLt r.1.size fun t =>
      let x := r.1[t]!
      decide (x < n) && r.2.1[x]! == t &&
        (t == 0 || (decide (r.2.2.2[x]! < gens.size) && decide (r.2.2.1[x]! < n) &&
          decide (r.2.1[r.2.2.1[x]!]! < t) && r.1[r.2.1[r.2.2.1[x]!]!]! == r.2.2.1[x]! &&
          bget gens[r.2.2.2[x]!]! r.2.2.1[x]! == x))

@[expose] def recMemN (n : ℕ) (r : Array ℕ × Array ℕ × Array ℕ × Array ℕ) (x : ℕ) : Bool :=
  decide (x < n) && decide (r.2.1[x]! < r.1.size) && r.1[r.2.1[x]!]! == x

private theorem recValidN_facts {n β : ℕ} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValidN n β gens r = true) :
    β < n ∧ r.1[0]! = β ∧ 0 < r.1.size ∧
      ∀ t < r.1.size, r.1[t]! < n ∧ r.2.1[r.1[t]!]! = t ∧ (t ≠ 0 →
        r.2.2.2[r.1[t]!]! < gens.size ∧ r.2.2.1[r.1[t]!]! < n ∧
        r.2.1[r.2.2.1[r.1[t]!]!]! < t ∧ r.1[r.2.1[r.2.2.1[r.1[t]!]!]!]! = r.2.2.1[r.1[t]!]! ∧
        bget gens[r.2.2.2[r.1[t]!]!]! r.2.2.1[r.1[t]!]! = r.1[t]!) := by
  unfold recValidN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hβ, -⟩, hne⟩, h0⟩, hall⟩ := h
  refine ⟨of_decide_eq_true hβ, beq_iff_eq.1 h0, Nat.pos_of_ne_zero (bne_iff_ne.1 hne),
    fun t ht => ?_⟩
  have := allLt_spec hall ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨h1, h2, fun ht0 => ?_⟩
  rcases h3 with h3 | ⟨⟨⟨⟨h4, h5⟩, h6⟩, h7⟩, h8⟩
  · exact absurd h3 ht0
  · exact ⟨h4, h5, h6, h7, h8⟩

theorem recValidN_spec {n : ℕ} {β : Fin n} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValidN n β gens r = true)
    (K : Subgroup (Equiv.Perm (Fin n))) (hgens : ∀ i < gens.size, ∃ g ∈ K, RepB n gens[i]! g) :
    (∀ t < r.1.size, ∃ hx : r.1[t]! < n, (⟨r.1[t]!, hx⟩ : Fin n) ∈ MulAction.orbit K β) ∧
      ∀ t < r.1.size, r.2.1[r.1[t]!]! = t := by
  obtain ⟨-, h0, -, hpt⟩ := recValidN_facts h
  refine ⟨?_, fun t ht => (hpt t ht).2.1⟩
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    obtain ⟨hx, -, htree⟩ := hpt t ht
    refine ⟨hx, ?_⟩
    by_cases ht0 : t = 0
    · subst ht0
      have : (⟨r.1[0]!, hx⟩ : Fin n) = β := Fin.ext h0
      rw [this]
      exact MulAction.mem_orbit_self _
    · obtain ⟨htl, htp, hpp, hpe, hg⟩ := htree ht0
      obtain ⟨hy, ⟨⟨k, hk⟩, hkβ⟩⟩ := ih _ hpp (hpp.trans ht)
      obtain ⟨g, hgK, hrep⟩ := hgens _ htl
      refine ⟨⟨g * k, K.mul_mem hgK hk⟩, ?_⟩
      have hkβ' : k • β = ⟨r.1[r.2.1[r.2.2.1[r.1[t]!]!]!]!, hy⟩ := hkβ
      show (g * k) • β = ⟨r.1[t]!, hx⟩
      rw [mul_smul, hkβ']
      apply Fin.ext
      have h2 := hrep.2 ⟨r.2.2.1[r.1[t]!]!, htp⟩
      have h3 : (⟨r.1[r.2.1[r.2.2.1[r.1[t]!]!]!]!, hy⟩ : Fin n) =
          ⟨r.2.2.1[r.1[t]!]!, htp⟩ := Fin.ext hpe
      rw [h3]
      exact (h2.symm.trans hg)

theorem le_ncard_orbit_of_recValidN {n : ℕ} {β : Fin n} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValidN n β gens r = true)
    (K : Subgroup (Equiv.Perm (Fin n))) (hgens : ∀ i < gens.size, ∃ g ∈ K, RepB n gens[i]! g) :
    r.1.size ≤ (MulAction.orbit K β).ncard := by
  obtain ⟨hmem, hpos⟩ := recValidN_spec h K hgens
  let f : Fin r.1.size → MulAction.orbit K β := fun t =>
    ⟨⟨r.1[t.1]!, (hmem t.1 t.2).1⟩, (hmem t.1 t.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : r.1[a.1]! = r.1[b.1]! := congrArg (fun x => (x.1 : Fin n).1) hab
    apply Fin.ext
    rw [← hpos a.1 a.2, ← hpos b.1 b.2, h1]
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  rwa [← Nat.card_coe_set_eq]

theorem mem_orbit_of_recMemN {n : ℕ} {β : Fin n} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValidN n β gens r = true)
    (K : Subgroup (Equiv.Perm (Fin n))) (hgens : ∀ i < gens.size, ∃ g ∈ K, RepB n gens[i]! g)
    {y : Fin n} (hy : recMemN n r y = true) : y ∈ MulAction.orbit K β := by
  obtain ⟨hmem, -⟩ := recValidN_spec h K hgens
  unfold recMemN at hy
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hy
  obtain ⟨⟨-, hpos⟩, he⟩ := hy
  obtain ⟨hx, hxo⟩ := hmem _ hpos
  have : (⟨r.1[r.2.1[(y : ℕ)]!]!, hx⟩ : Fin n) = y := Fin.ext he
  rwa [this] at hxo

theorem recMemN_of_mem_orbit {n : ℕ} {β : Fin n} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValidN n β gens r = true)
    (K : Subgroup (Equiv.Perm (Fin n))) (hgens : ∀ i < gens.size, ∃ g ∈ K, RepB n gens[i]! g)
    (hle : (MulAction.orbit K β).ncard ≤ r.1.size) {y : Fin n} (hy : y ∈ MulAction.orbit K β) :
    recMemN n r y = true := by
  obtain ⟨hmem, hpos⟩ := recValidN_spec h K hgens
  let f : Fin r.1.size → Fin n := fun t => ⟨r.1[t.1]!, (hmem t.1 t.2).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : r.1[a.1]! = r.1[b.1]! := congrArg Fin.val hab
    apply Fin.ext
    rw [← hpos a.1 a.2, ← hpos b.1 b.2, h1]
  have hsub : Set.range f ⊆ MulAction.orbit K β := by
    rintro _ ⟨t, rfl⟩
    exact (hmem t.1 t.2).2
  have hcard : (Set.range f).ncard = r.1.size := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hf, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have heq : Set.range f = MulAction.orbit K β :=
    Set.eq_of_subset_of_ncard_le hsub (hle.trans hcard.ge) (Set.toFinite _)
  rw [← heq] at hy
  obtain ⟨t, rfl⟩ := hy
  unfold recMemN
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨(f t).2, ?_⟩, ?_⟩
  · show r.2.1[r.1[t.1]!]! < r.1.size
    rw [hpos t.1 t.2]
    exact t.2
  · show r.1[r.2.1[r.1[t.1]!]!]! = r.1[t.1]!
    rw [hpos t.1 t.2]

theorem recValidN_size_le {n β : ℕ} {gens : Array ByteArray}
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (h : recValidN n β gens r = true) :
    r.1.size ≤ n := by
  obtain ⟨-, -, -, hpt⟩ := recValidN_facts h
  have := Finset.card_le_card_of_injOn (s := Finset.range r.1.size) (t := Finset.range n)
    (fun t => r.1[t]!) (fun t ht => Finset.mem_range.2 (hpt t (Finset.mem_range.1 ht)).1)
    (fun a ha b hb hab => by
      have h1 := (hpt a (Finset.mem_range.1 ha)).2.1
      have h2 := (hpt b (Finset.mem_range.1 hb)).2.1
      rw [← h1, ← h2]
      exact congrArg _ hab)
  simpa using this

theorem chain_exact_spec {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (k : ℕ) (β : ℕ → Fin n)
    (o : ℕ → ℕ) (hpos : ∀ l < k, 0 < o l)
    (ho : ∀ l < k, o l ≤ (MulAction.orbit (chainStab S β l) (β l)).ncard)
    (hS : Nat.card S ≤ ∏ l ∈ Finset.range k, o l) :
    Nat.card (chainStab S β k) = 1 ∧
      ∀ l < k, (MulAction.orbit (chainStab S β l) (β l)).ncard = o l := by
  set a : ℕ → ℕ := fun l => (MulAction.orbit (chainStab S β l) (β l)).ncard with ha
  have hprod : ∀ j, (∏ l ∈ Finset.range j, a l) * Nat.card (chainStab S β j) ≤ Nat.card S := by
    intro j
    induction j with
    | zero => simp [chainStab_zero]
    | succ j ih =>
      rw [Finset.prod_range_succ, mul_assoc]
      exact (Nat.mul_le_mul_left _ (card_chainStab_step S β j le_rfl le_rfl)).trans ih
  have hcpos : 0 < Nat.card (chainStab S β k) := Nat.card_pos
  have hOpos : 0 < ∏ l ∈ Finset.range k, o l :=
    Finset.prod_pos fun l hl => hpos l (Finset.mem_range.1 hl)
  have hOA : ∏ l ∈ Finset.range k, o l ≤ ∏ l ∈ Finset.range k, a l :=
    Finset.prod_le_prod fun l hl => ho l (Finset.mem_range.1 hl)
  have hAc : (∏ l ∈ Finset.range k, a l) * Nat.card (chainStab S β k) ≤
      ∏ l ∈ Finset.range k, a l := (hprod k).trans (hS.trans hOA)
  refine ⟨?_, fun l hl => ?_⟩
  · have hApos : 0 < ∏ l ∈ Finset.range k, a l := hOpos.trans_le hOA
    have : Nat.card (chainStab S β k) ≤ 1 := by
      refine Nat.le_of_mul_le_mul_left (c := ∏ l ∈ Finset.range k, a l) ?_ hApos
      rwa [mul_one]
    omega
  · by_contra hne
    have hlt : o l < a l := lt_of_le_of_ne (ho l hl) (Ne.symm hne)
    have hstrict := Finset.prod_lt_prod₀ (s := Finset.range k) (f := o) (g := a)
      (fun l hl => hpos l (Finset.mem_range.1 hl))
      (fun l hl => ho l (Finset.mem_range.1 hl)) ⟨l, Finset.mem_range.2 hl, hlt⟩
    have hApos : 0 < ∏ l ∈ Finset.range k, a l := hOpos.trans_le hOA
    have : ∏ l ∈ Finset.range k, a l ≤ ∏ l ∈ Finset.range k, o l :=
      (Nat.le_mul_of_pos_right _ hcpos).trans ((hprod k).trans hS)
    omega

private theorem gens_mem_chainStab {n : ℕ} {S : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    {β : ℕ → Fin n} {gens : ℕ → Array ByteArray}
    (hgen : ∀ l < k, ∀ i < (gens l).size,
      ∃ g ∈ S, RepB n (gens l)[i]! g ∧ ∀ m < l, g (β m) = β m)
    {l : ℕ} (hl : l < k) : ∀ i < (gens l).size, ∃ g ∈ chainStab S β l, RepB n (gens l)[i]! g := by
  intro i hi
  obtain ⟨g, hgS, hrep, hfix⟩ := hgen l hl i hi
  exact ⟨g, ⟨hgS, hfix⟩, hrep⟩

section Exact

variable {n : ℕ} {S : Subgroup (Equiv.Perm (Fin n))} {k : ℕ} {β : ℕ → Fin n}
  {gens : ℕ → Array ByteArray}
  (hgen : ∀ l < k, ∀ i < (gens l).size,
    ∃ g ∈ S, RepB n (gens l)[i]! g ∧ ∀ m < l, g (β m) = β m)
  (hrec : ∀ l < k, recValidN n (β l) (gens l) (B.orbitRec n (β l) (gens l)) = true)
  (hcard : Nat.card S ≤ ∏ l ∈ Finset.range k, (B.orbitRec n (β l) (gens l)).1.size)

include hgen hrec hcard

private theorem exact_aux :
    Nat.card (chainStab S β k) = 1 ∧ ∀ l < k, (MulAction.orbit (chainStab S β l) (β l)).ncard =
      (B.orbitRec n (β l) (gens l)).1.size :=
  chain_exact_spec S k β (fun l => (B.orbitRec n (β l) (gens l)).1.size)
    (fun l hl => (recValidN_facts (hrec l hl)).2.2.1)
    (fun l hl => le_ncard_orbit_of_recValidN (hrec l hl) (chainStab S β l)
      (gens_mem_chainStab hgen hl))
    hcard

theorem chainStab_eq_bot_of_exact : chainStab S β k = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (exact_aux hgen hrec hcard).1

theorem recMemN_of_mem_chainStab {l : ℕ} (hl : l < k) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ chainStab S β l) :
    recMemN n (B.orbitRec n (β l) (gens l)) (g (β l)) = true :=
  recMemN_of_mem_orbit (hrec l hl) (chainStab S β l) (gens_mem_chainStab hgen hl)
    ((exact_aux hgen hrec hcard).2 l hl).le ⟨⟨g, hg⟩, rfl⟩

private theorem exists_mul_of_mem_chainStab {l : ℕ} (hl : l < k) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ chainStab S β l) :
    ∃ u ∈ Subgroup.closure {g | ∃ i < (gens l).size, RepB n (gens l)[i]! g},
      ∃ τ ∈ chainStab S β (l + 1), σ = u * τ := by
  set Y : Set (Equiv.Perm (Fin n)) := {g | ∃ i < (gens l).size, RepB n (gens l)[i]! g} with hY
  have hYle : Subgroup.closure Y ≤ chainStab S β l := by
    rw [Subgroup.closure_le]
    rintro g ⟨i, hi, hrep⟩
    obtain ⟨g', hg', hrep'⟩ := gens_mem_chainStab hgen hl i hi
    rw [hrep.unique hrep']
    exact hg'
  have hgensK : ∀ i < (gens l).size, ∃ g ∈ Subgroup.closure Y, RepB n (gens l)[i]! g := by
    intro i hi
    obtain ⟨g, -, hrep⟩ := gens_mem_chainStab hgen hl i hi
    exact ⟨g, Subgroup.subset_closure ⟨i, hi, hrep⟩, hrep⟩
  have hmem := mem_orbit_of_recMemN (hrec l hl) (Subgroup.closure Y) hgensK
    (recMemN_of_mem_chainStab hgen hrec hcard hl hσ)
  obtain ⟨⟨u, hu⟩, hux⟩ := MulAction.mem_orbit_iff.1 hmem
  have hux' : u (β l) = σ (β l) := hux
  have huZ : u ∈ chainStab S β l := hYle hu
  refine ⟨u, hu, u⁻¹ * σ, ⟨S.mul_mem (S.inv_mem huZ.1) hσ.1, fun m hm => ?_⟩, by simp⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
  · rw [hσ.2 m h, huZ.2 m h]
  · exact hux'.symm

theorem le_closure_of_exact :
    S ≤ Subgroup.closure {g | ∃ l < k, ∃ i < (gens l).size, RepB n (gens l)[i]! g} := by
  set Yall : Set (Equiv.Perm (Fin n)) :=
    {g | ∃ l < k, ∃ i < (gens l).size, RepB n (gens l)[i]! g} with hYall
  have key : ∀ d l, l + d = k → ∀ σ ∈ chainStab S β l, σ ∈ Subgroup.closure Yall := by
    intro d
    induction d with
    | zero =>
      intro l hl σ hσ
      obtain rfl : l = k := by omega
      rw [chainStab_eq_bot_of_exact hgen hrec hcard] at hσ
      rw [Subgroup.mem_bot.1 hσ]
      exact one_mem _
    | succ d ih =>
      intro l hl σ hσ
      obtain ⟨u, hu, τ, hτ, rfl⟩ :=
        exists_mul_of_mem_chainStab hgen hrec hcard (show l < k by omega) hσ
      refine mul_mem (Subgroup.closure_mono ?_ hu) (ih (l + 1) (by omega) τ hτ)
      rintro g ⟨i, hi, hrep⟩
      exact ⟨l, by omega, i, hi, hrep⟩
  intro σ hσ
  exact key k 0 (by omega) σ (by rw [chainStab_zero]; exact hσ)

theorem closure_eq_of_exact :
    Subgroup.closure {g | ∃ l < k, ∃ i < (gens l).size, RepB n (gens l)[i]! g} = S := by
  refine le_antisymm ?_ (le_closure_of_exact hgen hrec hcard)
  rw [Subgroup.closure_le]
  rintro g ⟨l, hl, i, hi, hrep⟩
  obtain ⟨g', hg', hrep', -⟩ := hgen l hl i hi
  rw [hrep.unique hrep']
  exact hg'

end Exact

@[expose] def siftLevel (n β : ℕ) (gens : Array ByteArray)
    (r : Array ℕ × Array ℕ × Array ℕ × Array ℕ) : ℕ → ByteArray → Option ByteArray
  | 0, _ => none
  | fuel + 1, σ =>
    let x := bget σ β
    if recMemN n r x then
      if x = β then some σ
      else siftLevel n β gens r fuel (bcomp n (binvCand n gens[r.2.2.2[x]!]!) σ)
    else none

@[expose] def siftChain (n : ℕ) : List (ℕ × Array ByteArray) → ByteArray → Option ByteArray
  | [], σ => some σ
  | (β, gens) :: levels, σ =>
    match siftLevel n β gens (B.orbitRec n β gens) n σ with
    | some τ => siftChain n levels τ
    | none => none

@[expose] def siftB (n : ℕ) (levels : Array (ℕ × Array ByteArray)) (σ : ByteArray) : Bool :=
  match siftChain n levels.toList σ with
  | some τ => bEq n τ (bid n)
  | none => false

private theorem siftLevel_spec {n : ℕ} (hn : n ≤ 65536) {S : Subgroup (Equiv.Perm (Fin n))}
    {β : ℕ → Fin n} {l : ℕ} {gl : Array ByteArray}
    (hgens : ∀ i < gl.size, ∃ g ∈ chainStab S β l, RepB n gl[i]! g)
    (hinv : ∀ i < gl.size, bisInv n gl[i]! (binvCand n gl[i]!) = true)
    {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (hvalid : recValidN n (β l) gl r = true)
    (hlist : ∀ g ∈ chainStab S β l, recMemN n r (g (β l)) = true) :
    ∀ (fuel : ℕ) (σ : Equiv.Perm (Fin n)), σ ∈ chainStab S β l → r.2.1[(σ (β l) : ℕ)]! < fuel →
      ∀ σa, RepB n σa σ → ∃ τ ∈ chainStab S β (l + 1), ∃ τa, RepB n τa τ ∧
        siftLevel n (β l) gl r fuel σa = some τa := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ _ h
    exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro σ hσ hfuel σa hσa
    have hx := hlist σ hσ
    have hxa : bget σa (β l : ℕ) = (σ (β l) : ℕ) := hσa.2 (β l)
    by_cases hxβ : σ (β l) = β l
    · refine ⟨σ, ⟨hσ.1, fun m hm => ?_⟩, σa, hσa, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
        · exact hσ.2 m h
        · exact hxβ
      · have hxβ' : (σ (β l) : ℕ) = (β l : ℕ) := congrArg Fin.val hxβ
        have hx'' : recMemN n r (β l : ℕ) = true := hxβ' ▸ hx
        simp only [siftLevel, hxa, hxβ', hx'', ↓reduceIte]
    · have hxβ' : ¬ (σ (β l) : ℕ) = (β l : ℕ) := fun h => hxβ (Fin.ext h)
      obtain ⟨-, h0, -, hpt⟩ := recValidN_facts hvalid
      have hx' := hx
      unfold recMemN at hx'
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx'
      obtain ⟨⟨-, hxp⟩, hxe⟩ := hx'
      have ht0 : r.2.1[(σ (β l) : ℕ)]! ≠ 0 := by
        intro h
        rw [h] at hxe
        exact hxβ' (hxe.symm.trans h0)
      obtain ⟨-, -, htree⟩ := hpt _ hxp
      rw [hxe] at htree
      obtain ⟨htl, htp, hpp, -, hg⟩ := htree ht0
      obtain ⟨g, hgZ, hrep⟩ := hgens _ htl
      have hnew := repB_bcomp hn (repB_binv hrep (hinv _ htl)) hσa
      have hσ' : g⁻¹ * σ ∈ chainStab S β l :=
        (chainStab S β l).mul_mem ((chainStab S β l).inv_mem hgZ) hσ
      have hgtp : g ⟨r.2.2.1[(σ (β l) : ℕ)]!, htp⟩ = σ (β l) := by
        apply Fin.ext
        rw [← hrep.2 ⟨r.2.2.1[(σ (β l) : ℕ)]!, htp⟩]
        exact hg
      have himg : ((g⁻¹ * σ) (β l) : ℕ) = r.2.2.1[(σ (β l) : ℕ)]! := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.2 hgtp.symm]
      obtain ⟨τ, hτ, τa, hτa, hs⟩ := ih (g⁻¹ * σ) hσ' (by rw [himg]; omega) _ hnew
      refine ⟨τ, hτ, τa, hτa, ?_⟩
      simp only [siftLevel, hxa, hx, hxβ', ↓reduceIte]
      exact hs

section Sift

variable {n : ℕ} {S : Subgroup (Equiv.Perm (Fin n))} {k : ℕ} {β : ℕ → Fin n}
  {gens : ℕ → Array ByteArray} (hn : n ≤ 65536)
  (hgen : ∀ l < k, ∀ i < (gens l).size,
    ∃ g ∈ S, RepB n (gens l)[i]! g ∧ ∀ m < l, g (β m) = β m)
  (hinv : ∀ l < k, ∀ i < (gens l).size,
    bisInv n (gens l)[i]! (binvCand n (gens l)[i]!) = true)
  (hrec : ∀ l < k, recValidN n (β l) (gens l) (B.orbitRec n (β l) (gens l)) = true)
  (hcard : Nat.card S ≤ ∏ l ∈ Finset.range k, (B.orbitRec n (β l) (gens l)).1.size)

include hn hgen hinv hrec hcard

private theorem siftChain_spec :
    ∀ (L : List (ℕ × Array ByteArray)) (j : ℕ), j + L.length = k →
      (∀ i < L.length, L[i]! = ((β (j + i) : ℕ), gens (j + i))) →
      ∀ σ ∈ chainStab S β j, ∀ σa, RepB n σa σ →
        ∃ τ ∈ chainStab S β k, ∃ τa, RepB n τa τ ∧ siftChain n L σa = some τa := by
  intro L
  induction L with
  | nil =>
    intro j hj _ σ hσ σa hσa
    obtain rfl : j = k := by simpa using hj
    exact ⟨σ, hσ, σa, hσa, rfl⟩
  | cons x L ih =>
    intro j hj hL σ hσ σa hσa
    have hjk : j < k := by
      rw [List.length_cons] at hj
      omega
    have hx0 : x = ((β j : ℕ), gens j) := by simpa using hL 0 (by simp)
    subst hx0
    have hx := recMemN_of_mem_chainStab hgen hrec hcard hjk hσ
    have hpos : (B.orbitRec n (β j) (gens j)).2.1[(σ (β j) : ℕ)]! < n := by
      unfold recMemN at hx
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hx
      exact hx.1.2.trans_le (recValidN_size_le (hrec j hjk))
    obtain ⟨τ₁, hτ₁, τa₁, hτa₁, hs₁⟩ := siftLevel_spec hn (gens_mem_chainStab hgen hjk)
      (hinv j hjk) (hrec j hjk) (fun g hg => recMemN_of_mem_chainStab hgen hrec hcard hjk hg) n σ
      hσ hpos σa hσa
    have hL' : ∀ i < L.length, L[i]! = ((β (j + 1 + i) : ℕ), gens (j + 1 + i)) := by
      intro i hi
      have := hL (i + 1) (by rw [List.length_cons]; omega)
      rw [List.getElem!_cons_succ, show j + (i + 1) = j + 1 + i by omega] at this
      exact this
    obtain ⟨τ, hτ, τa, hτa, hs⟩ := ih (j + 1) (by rw [List.length_cons] at hj; omega) hL' τ₁ hτ₁
      τa₁ hτa₁
    refine ⟨τ, hτ, τa, hτa, ?_⟩
    simp only [siftChain, hs₁]
    exact hs

theorem siftB_of_mem {levels : Array (ℕ × Array ByteArray)} (hsize : levels.size = k)
    (hlev : ∀ l < k, levels[l]! = ((β l : ℕ), gens l)) {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ S)
    {σa : ByteArray} (hσa : RepB n σa σ) : siftB n levels σa = true := by
  obtain ⟨τ, hτ, τa, hτa, hs⟩ := siftChain_spec hn hgen hinv hrec hcard levels.toList 0
    (by simpa using hsize)
    (fun i hi => by
      have hi' : i < k := by simpa [hsize] using hi
      rw [zero_add, Array.getElem!_toList]
      exact hlev i hi')
    σ (by rw [chainStab_zero]; exact hσ) σa hσa
  rw [chainStab_eq_bot_of_exact hgen hrec hcard] at hτ
  obtain rfl : τ = 1 := Subgroup.mem_bot.1 hτ
  unfold siftB
  rw [hs]
  exact (bEq_iff hτa (repB_bid hn)).2 rfl

theorem not_mem_of_siftB_eq_false {levels : Array (ℕ × Array ByteArray)}
    (hsize : levels.size = k) (hlev : ∀ l < k, levels[l]! = ((β l : ℕ), gens l))
    {σ : Equiv.Perm (Fin n)} {σa : ByteArray} (hσa : RepB n σa σ)
    (hfalse : siftB n levels σa = false) : σ ∉ S := fun hσ => by
  rw [siftB_of_mem hn hgen hinv hrec hcard hsize hlev hσ hσa] at hfalse
  exact Bool.noConfusion hfalse

end Sift

end CFSG.YGroups.DCE
