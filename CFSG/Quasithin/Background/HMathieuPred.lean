module

public import CFSG.Quasithin.Background.HMathieuChain

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

@[expose] def reduceBy (bs : List ℕ) (x : ℕ) : ℕ := bs.foldl (fun x b => min x (x ^^^ b)) x

@[expose] def insertDesc (r : ℕ) : List ℕ → List ℕ
  | [] => [r]
  | b :: bs => if b < r then r :: b :: bs else b :: insertDesc r bs

@[expose] def pickBasis (vs : List ℕ) : List ℕ :=
  (vs.foldl (fun (st : List ℕ × List ℕ) v =>
    let r := reduceBy st.1 v
    if r = 0 then st else (insertDesc r st.1, v :: st.2)) ([], [])).2

@[expose] def indepCheck (r : ℕ) (vs b : List ℕ) : Bool :=
  decide (r ≤ b.length) && b.all (· ∈ vs) && decide (combos b).Nodup

theorem indepCheck_spec {r : ℕ} {vs b : List ℕ} (h : indepCheck r vs b = true) :
    r ≤ b.length ∧ (∀ x ∈ b, x ∈ vs) ∧ (combos b).Nodup := by
  simp only [indepCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, fun x hx => by simpa using h.1.2 x hx, h.2⟩

@[expose] def o2OK (O F : List ℕ) : Bool :=
  let d := Nat.log 2 F.length
  decide (d ≤ 4) || (d == 5 && F.any (· ∈ O)) ||
    (d == 6 && ((F.filter (· ∈ O)).sublists.any fun s => s.length % 2 == 1 && xorAll s == 0))

variable {V : Type*} [CommGroup V] {n : ℕ}

theorem MaskCoords.vm_xorAll (c : MaskCoords V n) :
    ∀ s : List ℕ, (s.map c.vm).prod = c.vm (xorAll s)
  | [] => by simp [xorAll, c.vm_zero]
  | a :: s => by rw [List.map_cons, List.prod_cons, MaskCoords.vm_xorAll c s, xorAll, c.vm_xor]

theorem MaskCoords.sq_eq_one (c : MaskCoords V n) (v : V) : v ^ 2 = 1 := by
  obtain ⟨m, -, rfl⟩ := c.vm_surj v
  rw [sq, ← c.vm_xor, Nat.xor_self, c.vm_zero]

theorem MaskCoords.finite (c : MaskCoords V n) : Finite V := by
  refine Finite.of_surjective (fun m : Fin (2 ^ n) => c.vm m) fun v => ?_
  obtain ⟨m, hm, hmv⟩ := c.vm_surj v
  exact ⟨⟨m, hm⟩, hmv⟩

theorem rk_le_four_of_o2OK (c : MaskCoords V n) {X U : Subgroup V} {F O : List ℕ}
    {Oset : Set V} (hF : ∀ m ∈ F, m < 2 ^ n ∧ c.vm m ∈ X) (hcard : Nat.card X = F.length)
    (hO : ∀ o ∈ O, c.vm o ∈ Oset) (hUX : U ≤ X) (hUO : ∀ v ∈ U, v ∉ Oset)
    (h : o2OK O F = true) : rk U ≤ 4 := by
  have := c.finite
  have hV := c.sq_eq_one
  have hX : Nat.card X = 2 ^ Nat.log 2 F.length := by
    rw [card_eq_two_pow hV X] at hcard ⊢
    rw [← hcard, Nat.log_pow (by norm_num)]
  refine rk_le_four_of_avoid hV hX hUX hUO ?_
  simp only [o2OK, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, List.mem_sublists] at h
  rcases h with (h | ⟨h5, o, hoF, hoO⟩) | ⟨h6, s, hs, hodd, hx⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨h5, c.vm o, (hF o hoF).2, hO o (by simpa using hoO)⟩)
  · refine Or.inr (Or.inr ⟨h6, s.map c.vm, ?_, by simpa using hodd, ?_⟩)
    · intro x hx'
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx'
      have ho' := hs.subset ho
      rw [List.mem_filter] at ho'
      exact ⟨(hF o ho'.1).2, hO o (by simpa using ho'.2)⟩
    · rw [c.vm_xorAll, hx, c.vm_zero]

variable {P : Type*} [Group P] [DecidableEq P]

@[expose] def xiCands (n : ℕ) (act : P → ℕ → ℕ) (l : List P) : List ℕ :=
  ((subprods l).filter (· ≠ 1)).flatMap fun s => fixMasks n act [s]

@[expose] def pairCands (n : ℕ) (act : P → ℕ → ℕ) (l : List P) : List ℕ :=
  let S := (subprods l).filter (· ≠ 1)
  S.flatMap fun s => (S.filter (· ≠ s)).flatMap fun t => fixMasks n act [s, t]

@[expose] def xiCheck (n r : ℕ) (act : P → ℕ → ℕ) (l : List P) : Bool :=
  indepCheck r (xiCands n act l) (pickBasis (xiCands n act l))

@[expose] def pairCheck (n r : ℕ) (act : P → ℕ → ℕ) (l : List P) : Bool :=
  indepCheck r (pairCands n act l) (pickBasis (pairCands n act l))

omit [Group P] [DecidableEq P] in
theorem mem_fixMasks {act : P → ℕ → ℕ} {l : List P} {m : ℕ} :
    m ∈ fixMasks n act l ↔ m < 2 ^ n ∧ ∀ s ∈ l, act s m = m := by
  simp [fixMasks, List.mem_filter, List.mem_range, List.all_eq_true]

variable {c : MaskCoords V n} {aut : P →* MulAut V} {act : P → ℕ → ℕ} {l : List P}
  {A : Subgroup (MulAut V)}

theorem pow_le_card_xiV (hc : ChainAct c aut act) (hA : IsChainSub aut l A)
    (hinj : Function.Injective aut) {r : ℕ} (h : xiCheck n r act l = true) :
    2 ^ r ≤ Nat.card (xiV A) := by
  obtain ⟨hr, hmem, hnd⟩ := indepCheck_spec h
  set b := pickBasis (xiCands n act l)
  have hb : ∀ x ∈ b, x < 2 ^ n ∧ c.vm x ∈ xiV A := by
    intro x hx
    have := hmem x hx
    simp only [xiCands, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at this
    obtain ⟨s, ⟨hs, hs1⟩, hxs⟩ := this
    obtain ⟨hlt, hfix⟩ := mem_fixMasks.1 hxs
    exact ⟨hlt, vm_mem_xiV hc hA hinj hs hs1 hlt (hfix s List.mem_cons_self)⟩
  calc 2 ^ r ≤ 2 ^ b.length := Nat.pow_le_pow_right (by norm_num) hr
    _ ≤ Nat.card (xiV A) := c.pow_le_card _ b hnd (fun x hx => (hb x hx).1)
        (fun x hx => (hb x hx).2)

theorem pow_le_card_iSup_four (hc : ChainAct c aut act) (hA : IsChainSub aut l A)
    (hinj : Function.Injective aut) (hl : IndepList l) {r : ℕ} (h : pairCheck n r act l = true) :
    2 ^ r ≤ Nat.card ↥(⨆ (B : Subgroup (MulAut V)) (_ : B ≤ A) (_ : Nat.card B = 4), fixV B) := by
  obtain ⟨hr, hmem, hnd⟩ := indepCheck_spec h
  set b := pickBasis (pairCands n act l)
  have hb : ∀ x ∈ b, x < 2 ^ n ∧
      c.vm x ∈ ⨆ (B : Subgroup (MulAut V)) (_ : B ≤ A) (_ : Nat.card B = 4), fixV B := by
    intro x hx
    have := hmem x hx
    simp only [pairCands, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at this
    obtain ⟨s, ⟨hs, hs1⟩, t, ⟨⟨ht, ht1⟩, hts⟩, hxst⟩ := this
    obtain ⟨hlt, hfix⟩ := mem_fixMasks.1 hxst
    exact ⟨hlt, vm_mem_iSup_four hc hA hinj hl hs ht hs1 ht1 (Ne.symm hts) hlt
      (hfix s List.mem_cons_self) (hfix t (List.mem_cons_of_mem s List.mem_cons_self))⟩
  calc 2 ^ r ≤ 2 ^ b.length := Nat.pow_le_pow_right (by norm_num) hr
    _ ≤ _ := c.pow_le_card _ b hnd (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2)

theorem MaskCoords.eq_top_of_pow_le (c : MaskCoords V n) {U : Subgroup V}
    (h : 2 ^ n ≤ Nat.card U) : U = ⊤ := by
  have := c.finite
  have hV : Nat.card V = 2 ^ n := by
    have h1 := c.card_eq (⊤ : Subgroup V) (fun _ => true) fun m _ => by simp
    rw [Subgroup.card_top] at h1
    rw [h1, List.filter_true, List.length_range]
  exact Subgroup.eq_top_of_le_card U (hV ▸ h)

theorem MaskCoords.rkIdx_le_one_of_pow_le (c : MaskCoords V n) {U : Subgroup V} (hn : 1 ≤ n)
    (h : 2 ^ (n - 1) ≤ Nat.card U) : rkIdx U ≤ 1 := by
  have := c.finite
  have hV := c.sq_eq_one
  have hVc : Nat.card V = 2 ^ n := by
    have h1 := c.card_eq (⊤ : Subgroup V) (fun _ => true) fun m _ => by simp
    rw [Subgroup.card_top] at h1
    rw [h1, List.filter_true, List.length_range]
  have hrkV : rk V = n := by
    unfold rk
    rw [hVc, padicValNat.prime_pow]
  have hrkU : n - 1 ≤ rk U := by
    rw [card_eq_two_pow hV U] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have := rk_add_rkIdx U
  omega

end CFSG.Quasithin.H.Mathieu
