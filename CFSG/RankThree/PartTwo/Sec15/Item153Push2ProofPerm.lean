module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.RankThree.PartTwo.Sec15.Push153B

open Equiv

section Code

variable {n : ℕ}

@[expose] def pcode (σ : Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

@[expose] def cmul (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

@[expose] def csq (a : List ℕ) : List ℕ := cmul a a

@[expose] def is4 (n : ℕ) (a : List ℕ) : Bool := csq (csq a) == List.range n

@[expose] def crit (n : ℕ) (E : List (List ℕ)) (u : List ℕ) : Bool :=
  is4 n u && E.all fun e =>
    is4 n (cmul u (cmul (cmul e u) (csq e))) &&
      is4 n (cmul u (cmul (cmul e (cmul (csq u) u)) (csq e)))

theorem length_pcode (σ : Perm (Fin n)) : (pcode σ).length = n := List.length_ofFn

theorem pcode_getElem? (σ : Perm (Fin n)) (m : ℕ) :
    (pcode σ)[m]? = if h : m < n then some (σ ⟨m, h⟩ : ℕ) else none := by
  unfold pcode
  rw [List.getElem?_ofFn]

theorem pcode_getD (σ : Perm (Fin n)) (i : Fin n) : (pcode σ).getD i 0 = (σ i : ℕ) := by
  rw [List.getD_eq_getElem?_getD, pcode_getElem?]
  simp

theorem pcode_mul (σ τ : Perm (Fin n)) : pcode (σ * τ) = cmul (pcode σ) (pcode τ) := by
  apply List.ext_getElem?
  intro m
  rw [pcode_getElem?, cmul, List.getElem?_map, pcode_getElem?]
  by_cases hm : m < n
  · simp only [hm, dite_true, Option.map_some]
    congr 1
    rw [pcode_getD]
    rfl
  · simp [hm]

theorem pcode_one : pcode (1 : Perm (Fin n)) = List.range n := by
  apply List.ext_getElem?
  intro m
  by_cases hm : m < n
  · rw [pcode_getElem?, List.getElem?_range hm]
    simp [hm]
  · rw [pcode_getElem?, List.getElem?_eq_none (by simpa using hm)]
    simp [hm]

theorem pcode_injective : Function.Injective (pcode (n := n)) := by
  intro σ τ h
  ext i
  have := congrArg (fun l => l.getD i 0) h
  simp only [pcode_getD] at this
  exact_mod_cast this

theorem pcode_sq (σ : Perm (Fin n)) : pcode (σ ^ 2) = csq (pcode σ) := by
  rw [pow_two, pcode_mul, csq]

theorem is4_pcode (σ : Perm (Fin n)) : is4 n (pcode σ) = true ↔ σ ^ 4 = 1 := by
  have h : σ ^ 4 = (σ ^ 2) ^ 2 := by rw [← pow_mul]
  rw [is4, ← pcode_sq, ← pcode_sq, ← h, ← pcode_one, beq_iff_eq]
  exact pcode_injective.eq_iff

theorem pcode_perm_range (σ : Perm (Fin n)) : (pcode σ).Perm (List.range n) := by
  have h1 : pcode σ = List.ofFn ((fun i : Fin n => (i : ℕ)) ∘ σ) := rfl
  have h2 : List.ofFn (fun i : Fin n => (i : ℕ)) = List.range n := by
    rw [List.ofFn_eq_map, List.map_coe_finRange_eq_range]
  rw [h1, ← h2]
  exact Equiv.Perm.ofFn_comp_perm σ _

theorem pcode_mem_permutations' (σ : Perm (Fin n)) :
    pcode σ ∈ (List.range n).permutations' :=
  List.mem_permutations'.mpr (pcode_perm_range σ)

theorem exists_pcode_eq {l : List ℕ} (hl : l.Perm (List.range n)) :
    ∃ σ : Perm (Fin n), pcode σ = l := by
  have hlen : l.length = n := by rw [hl.length_eq, List.length_range]
  have hlt : ∀ (i : ℕ) (h : i < l.length), l[i] < n := fun i h => by
    have : l[i] ∈ List.range n := hl.subset (List.getElem_mem h)
    simpa using this
  have hnd : l.Nodup := hl.nodup_iff.mpr List.nodup_range
  let f : Fin n → Fin n := fun i => ⟨l[i.1]'(hlen ▸ i.2), hlt _ _⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg Fin.val hij
    simp only [f] at h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  apply List.ext_getElem (by rw [length_pcode, hlen])
  intro i h1 h2
  simp [pcode, f]

theorem exists_pcode_of_perm_check {l : List ℕ} (hl : l ∈ (List.range n).permutations') :
    ∃ σ : Perm (Fin n), pcode σ = l :=
  exists_pcode_eq (List.mem_permutations'.mp hl)

theorem pow_four_of_isPGroup (hn : n < 8) {Q : Subgroup (Perm (Fin n))} (hQ : IsPGroup 2 Q)
    {σ : Perm (Fin n)} (hσ : σ ∈ Q) : σ ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨σ, hσ⟩
  have hk' : σ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h4 : orderOf σ ∣ 4 := by
    rw [← Equiv.Perm.lcm_cycleType]
    refine Multiset.lcm_dvd.mpr fun m hm => ?_
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      ((Equiv.Perm.dvd_of_mem_cycleType hm).trans hdvd)
    have hle : 2 ^ i ≤ n :=
      (Equiv.Perm.le_card_support_of_mem_cycleType hm).trans
        ((Finset.card_le_univ _).trans (by rw [Fintype.card_fin]))
    have hi : i ≤ 2 := by
      by_contra hlt
      have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (pow_dvd_pow 2 hi).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp h4

end Code

section ListSubgroup

variable {n : ℕ}

@[expose] def ofCodes (l : List (List ℕ)) (h1 : List.range n ∈ l)
    (hmul : ∀ a ∈ l, ∀ b ∈ l, cmul a b ∈ l) (h3 : ∀ a ∈ l, cmul (csq a) a = List.range n) :
    Subgroup (Perm (Fin n)) where
  carrier := {σ | pcode σ ∈ l}
  one_mem' := by
    change pcode 1 ∈ l
    rw [pcode_one]
    exact h1
  mul_mem' := by
    intro a b ha hb
    change pcode (a * b) ∈ l
    rw [pcode_mul]
    exact hmul _ ha _ hb
  inv_mem' := by
    intro a ha
    change pcode a⁻¹ ∈ l
    have ha3 : a ^ 3 = 1 := by
      apply pcode_injective
      rw [pow_succ, pcode_mul, pcode_sq, pcode_one]
      exact h3 _ ha
    have hinv : a⁻¹ = a ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact ha3
    rw [hinv, pcode_sq]
    exact hmul _ ha _ ha

theorem mem_ofCodes {l : List (List ℕ)} {h1 : List.range n ∈ l}
    {hmul : ∀ a ∈ l, ∀ b ∈ l, cmul a b ∈ l} {h3 : ∀ a ∈ l, cmul (csq a) a = List.range n}
    {σ : Perm (Fin n)} : σ ∈ ofCodes l h1 hmul h3 ↔ pcode σ ∈ l := Iff.rfl

theorem card_ofCodes {l : List (List ℕ)} {h1 : List.range n ∈ l}
    {hmul : ∀ a ∈ l, ∀ b ∈ l, cmul a b ∈ l} {h3 : ∀ a ∈ l, cmul (csq a) a = List.range n}
    (hnd : l.Nodup) (hperm : ∀ a ∈ l, a ∈ (List.range n).permutations') :
    Nat.card ↥(ofCodes l h1 hmul h3) = l.length := by
  let f : ↥(ofCodes l h1 hmul h3) → {a // a ∈ l.toFinset} :=
    fun σ => ⟨pcode σ.1, List.mem_toFinset.mpr σ.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun σ τ h => Subtype.ext (pcode_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨a, ha⟩
    have ha' : a ∈ l := List.mem_toFinset.mp ha
    obtain ⟨σ, hσ⟩ := exists_pcode_of_perm_check (hperm a ha')
    exact ⟨⟨σ, show pcode σ ∈ l from hσ ▸ ha'⟩, Subtype.ext hσ⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

theorem exists_mem_ofCodes {l : List (List ℕ)} {h1 : List.range n ∈ l}
    {hmul : ∀ a ∈ l, ∀ b ∈ l, cmul a b ∈ l} {h3 : ∀ a ∈ l, cmul (csq a) a = List.range n}
    (hperm : ∀ a ∈ l, a ∈ (List.range n).permutations') {a : List ℕ} (ha : a ∈ l) :
    ∃ σ ∈ ofCodes l h1 hmul h3, pcode σ = a := by
  obtain ⟨σ, hσ⟩ := exists_pcode_of_perm_check (hperm a ha)
  exact ⟨σ, show pcode σ ∈ l from hσ ▸ ha, hσ⟩

end ListSubgroup

section Lattice

variable {n : ℕ}

theorem le_of_lattice_checks (hn : n < 8) {E : Subgroup (Perm (Fin n))}
    (hE3 : ∀ ε ∈ E, ε ^ 3 = 1) {ec es : List (List ℕ)} (hec : ∀ e ∈ ec, ∃ ε ∈ E, pcode ε = e)
    (hes : ∀ e ∈ es, e ∈ ec) (Ts : List (List (List ℕ)))
    (hcrit : ((List.range n).permutations'.all fun u =>
      !(crit n es u) || u == List.range n || Ts.any fun T => T.contains u) = true)
    (hmix : ∀ T ∈ Ts, ∀ T' ∈ Ts, T ≠ T' → ∀ a ∈ T, ∀ b ∈ T',
      ¬ (is4 n (cmul a b) = true ∧ (cmul a b = List.range n ∨ ∃ T'' ∈ Ts, cmul a b ∈ T'')))
    (htr : ∀ T ∈ Ts, ∀ a ∈ T, ∀ b ∈ T, ∃ e ∈ ec, cmul (cmul e a) (csq e) = b)
    {Q₁ Q₂ : Subgroup (Perm (Fin n))} (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂) (hne : Q₁ ≠ ⊥)
    (hn1 : E ≤ Subgroup.normalizer (Q₁ : Set (Perm (Fin n))))
    (hn2 : E ≤ Subgroup.normalizer (Q₂ : Set (Perm (Fin n)))) : Q₂ ≤ Q₁ := by
  have hconj : ∀ {Q : Subgroup (Perm (Fin n))},
      E ≤ Subgroup.normalizer (Q : Set (Perm (Fin n))) → ∀ ε ∈ E, ∀ x ∈ Q, ε * x * ε ^ 2 ∈ Q := by
    intro Q hQ ε hε x hx
    have hinv : ε ^ 2 = ε⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hE3 ε hε
    rw [hinv]
    exact (Subgroup.mem_normalizer_iff.mp (hQ hε) x).mp hx
  have hmem : ∀ σ ∈ Q₂, σ = 1 ∨ ∃ T ∈ Ts, pcode σ ∈ T := by
    intro σ hσ
    have hc : crit n es (pcode σ) = true := by
      simp only [crit, Bool.and_eq_true, List.all_eq_true]
      refine ⟨(is4_pcode σ).mpr (pow_four_of_isPGroup hn h2 hσ), fun e he => ?_⟩
      obtain ⟨ε, hε, rfl⟩ := hec e (hes e he)
      have h1 : σ * (ε * σ * ε ^ 2) ∈ Q₂ := Q₂.mul_mem hσ (hconj hn2 ε hε σ hσ)
      have h2' : σ * (ε * σ ^ 3 * ε ^ 2) ∈ Q₂ :=
        Q₂.mul_mem hσ (hconj hn2 ε hε _ (Q₂.pow_mem hσ 3))
      have e1 : cmul (pcode σ) (cmul (cmul (pcode ε) (pcode σ)) (csq (pcode ε))) =
          pcode (σ * (ε * σ * ε ^ 2)) := by
        rw [pcode_mul, pcode_mul, pcode_mul, pcode_sq]
      have e2 : cmul (pcode σ) (cmul (cmul (pcode ε) (cmul (csq (pcode σ)) (pcode σ)))
          (csq (pcode ε))) = pcode (σ * (ε * σ ^ 3 * ε ^ 2)) := by
        rw [pcode_mul, pcode_mul, pcode_mul, pcode_sq, pow_succ, pcode_mul, pcode_sq]
      rw [e1, e2, is4_pcode, is4_pcode]
      exact ⟨pow_four_of_isPGroup hn h2 h1, pow_four_of_isPGroup hn h2 h2'⟩
    have hall := List.all_eq_true.mp hcrit (pcode σ) (pcode_mem_permutations' σ)
    rw [hc] at hall
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
      List.contains_iff_mem] at hall
    rcases hall with h | ⟨T, hT, hσT⟩
    · left
      apply pcode_injective
      rw [h, pcode_one]
    · exact Or.inr ⟨T, hT, hσT⟩
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht1' : (t : Perm (Fin n)) ≠ 1 := fun h => ht1 (Subtype.ext h)
  rcases hmem t (hle t.2) with h | ⟨T₀, hT₀, htT₀⟩
  · exact absurd h ht1'
  intro σ hσ
  rcases hmem σ hσ with rfl | ⟨T, hT, hσT⟩
  · exact Q₁.one_mem
  have hTT : T = T₀ := by
    by_contra hne'
    have htσ : (t : Perm (Fin n)) * σ ∈ Q₂ := Q₂.mul_mem (hle t.2) hσ
    apply hmix T₀ hT₀ T hT (Ne.symm hne') _ htT₀ _ hσT
    rw [← pcode_mul, is4_pcode]
    refine ⟨pow_four_of_isPGroup hn h2 htσ, ?_⟩
    rcases hmem _ htσ with h | ⟨T'', hT'', h⟩
    · left
      rw [h, pcode_one]
    · exact Or.inr ⟨T'', hT'', h⟩
  subst hTT
  obtain ⟨e, he, hσe⟩ := htr T hT _ htT₀ _ hσT
  obtain ⟨ε, hε, rfl⟩ := hec e he
  have hσ' : σ = ε * t * ε ^ 2 := by
    apply pcode_injective
    rw [← hσe, pcode_mul, pcode_mul, pcode_sq]
  rw [hσ']
  exact hconj hn1 ε hε t t.2

theorem le_of_conj {E E' Q₁ Q₂ : Subgroup (Perm (Fin n))} (g : Perm (Fin n))
    (hE : E.map (MulAut.conj g).toMonoidHom = E')
    (hlat : ∀ R₁ R₂ : Subgroup (Perm (Fin n)), IsPGroup 2 R₂ → R₁ ≤ R₂ → R₁ ≠ ⊥ →
      E' ≤ Subgroup.normalizer (R₁ : Set (Perm (Fin n))) →
      E' ≤ Subgroup.normalizer (R₂ : Set (Perm (Fin n))) → R₂ ≤ R₁)
    (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂) (hne : Q₁ ≠ ⊥)
    (hn1 : E ≤ Subgroup.normalizer (Q₁ : Set (Perm (Fin n))))
    (hn2 : E ≤ Subgroup.normalizer (Q₂ : Set (Perm (Fin n)))) : Q₂ ≤ Q₁ := by
  set c := (MulAut.conj g).toMonoidHom with hc
  have hinj : Function.Injective c := (MulAut.conj g).injective
  have hmapn : ∀ (Q : Subgroup (Perm (Fin n))),
      E ≤ Subgroup.normalizer (Q : Set (Perm (Fin n))) →
      E' ≤ Subgroup.normalizer ((Q.map c : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
    intro Q hQ
    rw [← hE]
    calc E.map c ≤ (Subgroup.normalizer (Q : Set (Perm (Fin n)))).map c := Subgroup.map_mono hQ
      _ ≤ Subgroup.normalizer ((Q.map c : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) :=
        Subgroup.le_normalizer_map c
  have h := hlat (Q₁.map c) (Q₂.map c) (h2.map c) (Subgroup.map_mono hle)
    (fun h0 => hne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h0)) (hmapn Q₁ hn1)
    (hmapn Q₂ hn2)
  exact (Subgroup.map_le_map_iff_of_injective hinj).mp h

end Lattice

section Five

@[expose] def e5c : List (List ℕ) := [[0, 1, 2, 3, 4], [1, 2, 0, 3, 4], [2, 0, 1, 3, 4]]

@[expose] def t5c : List (List (List ℕ)) :=
  [[[0, 1, 2, 4, 3]], [[1, 0, 3, 2, 4], [2, 3, 0, 1, 4], [3, 2, 1, 0, 4]],
    [[1, 0, 4, 3, 2], [2, 4, 0, 3, 1], [4, 2, 1, 3, 0]]]

theorem e5c_one : List.range 5 ∈ e5c := by decide +kernel

theorem e5c_mul : ∀ a ∈ e5c, ∀ b ∈ e5c, cmul a b ∈ e5c := by decide +kernel

theorem e5c_three : ∀ a ∈ e5c, cmul (csq a) a = List.range 5 := by decide +kernel

theorem e5c_perm : ∀ a ∈ e5c, a ∈ (List.range 5).permutations' := by decide +kernel

@[expose] def E5 : Subgroup (Perm (Fin 5)) := ofCodes e5c e5c_one e5c_mul e5c_three

theorem card_E5 : Nat.card ↥E5 = 3 :=
  card_ofCodes (by decide +kernel) e5c_perm

@[expose] noncomputable def E5Sylow : Sylow 3 (Perm (Fin 5)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (show IsPGroup 3 ↥E5 from IsPGroup.of_card (n := 1) (by rw [card_E5]; norm_num)).toSylow (by
    have h := Subgroup.card_mul_index E5
    rw [card_E5, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h5 : (5 : ℕ).factorial = 120 := by decide
    have : E5.index = 40 := by omega
    rw [this]
    decide)

theorem E5Sylow_coe : (E5Sylow : Subgroup (Perm (Fin 5))) = E5 := rfl

theorem crit5_check : ((List.range 5).permutations'.all fun u =>
    !(crit 5 e5c u) || u == List.range 5 || t5c.any fun T => T.contains u) = true := by
  decide +kernel

theorem mix5_check : ∀ T ∈ t5c, ∀ T' ∈ t5c, T ≠ T' → ∀ a ∈ T, ∀ b ∈ T',
    ¬ (is4 5 (cmul a b) = true ∧ (cmul a b = List.range 5 ∨ ∃ T'' ∈ t5c, cmul a b ∈ T'')) := by
  decide +kernel

theorem tr5_check : ∀ T ∈ t5c, ∀ a ∈ T, ∀ b ∈ T, ∃ e ∈ e5c, cmul (cmul e a) (csq e) = b := by
  decide +kernel

theorem E5_pow : ∀ ε ∈ E5, ε ^ 3 = 1 := by
  intro ε hε
  apply pcode_injective
  rw [pow_succ, pcode_mul, pcode_sq, pcode_one]
  exact e5c_three _ hε

theorem E5_comm : ∀ ε ∈ E5, ∀ η ∈ E5, ε * η = η * ε := by
  have h : ∀ a ∈ e5c, ∀ b ∈ e5c, cmul a b = cmul b a := by decide +kernel
  intro ε hε η hη
  apply pcode_injective
  rw [pcode_mul, pcode_mul]
  exact h _ hε _ hη

theorem le_of_E5 {Q₁ Q₂ : Subgroup (Perm (Fin 5))} (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂)
    (hne : Q₁ ≠ ⊥) (hn1 : E5 ≤ Subgroup.normalizer (Q₁ : Set (Perm (Fin 5))))
    (hn2 : E5 ≤ Subgroup.normalizer (Q₂ : Set (Perm (Fin 5)))) : Q₂ ≤ Q₁ :=
  le_of_lattice_checks (by norm_num) E5_pow (fun _ he => exists_mem_ofCodes e5c_perm he)
    (fun _ he => he) t5c crit5_check mix5_check tr5_check h2 hle hne hn1 hn2

end Five

section Seven

@[expose] def e7c : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 4, 5, 3, 6], [0, 1, 2, 5, 3, 4, 6], [1, 2, 0, 3, 4, 5, 6],
    [1, 2, 0, 4, 5, 3, 6], [1, 2, 0, 5, 3, 4, 6], [2, 0, 1, 3, 4, 5, 6], [2, 0, 1, 4, 5, 3, 6],
    [2, 0, 1, 5, 3, 4, 6]]

@[expose] def e7s : List (List ℕ) := [[0, 1, 2, 4, 5, 3, 6], [1, 2, 0, 4, 5, 3, 6]]

@[expose] def t7c : List (List (List ℕ)) :=
  [[[0, 1, 2, 4, 3, 6, 5], [0, 1, 2, 5, 6, 3, 4], [0, 1, 2, 6, 5, 4, 3]],
    [[1, 0, 6, 3, 4, 5, 2], [2, 6, 0, 3, 4, 5, 1], [6, 2, 1, 3, 4, 5, 0]]]

theorem e7c_one : List.range 7 ∈ e7c := by decide +kernel

theorem e7c_mul : ∀ a ∈ e7c, ∀ b ∈ e7c, cmul a b ∈ e7c := by decide +kernel

theorem e7c_three : ∀ a ∈ e7c, cmul (csq a) a = List.range 7 := by decide +kernel

theorem e7c_perm : ∀ a ∈ e7c, a ∈ (List.range 7).permutations' := by decide +kernel

@[expose] def E7 : Subgroup (Perm (Fin 7)) := ofCodes e7c e7c_one e7c_mul e7c_three

theorem card_E7 : Nat.card ↥E7 = 9 :=
  card_ofCodes (by decide +kernel) e7c_perm

@[expose] noncomputable def E7Sylow : Sylow 3 (Perm (Fin 7)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (show IsPGroup 3 ↥E7 from IsPGroup.of_card (n := 2) (by rw [card_E7]; norm_num)).toSylow (by
    have h := Subgroup.card_mul_index E7
    rw [card_E7, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h7 : (7 : ℕ).factorial = 5040 := by decide
    have : E7.index = 560 := by omega
    rw [this]
    decide)

theorem E7Sylow_coe : (E7Sylow : Subgroup (Perm (Fin 7))) = E7 := rfl

theorem crit7_check : ((List.range 7).permutations'.all fun u =>
    !(crit 7 e7s u) || u == List.range 7 || t7c.any fun T => T.contains u) = true := by
  decide +kernel

theorem mix7_check : ∀ T ∈ t7c, ∀ T' ∈ t7c, T ≠ T' → ∀ a ∈ T, ∀ b ∈ T',
    ¬ (is4 7 (cmul a b) = true ∧ (cmul a b = List.range 7 ∨ ∃ T'' ∈ t7c, cmul a b ∈ T'')) := by
  decide +kernel

theorem tr7_check : ∀ T ∈ t7c, ∀ a ∈ T, ∀ b ∈ T, ∃ e ∈ e7c, cmul (cmul e a) (csq e) = b := by
  decide +kernel

theorem e7s_sub : ∀ e ∈ e7s, e ∈ e7c := by decide +kernel

theorem E7_pow : ∀ ε ∈ E7, ε ^ 3 = 1 := by
  intro ε hε
  apply pcode_injective
  rw [pow_succ, pcode_mul, pcode_sq, pcode_one]
  exact e7c_three _ hε

theorem E7_comm : ∀ ε ∈ E7, ∀ η ∈ E7, ε * η = η * ε := by
  have h : ∀ a ∈ e7c, ∀ b ∈ e7c, cmul a b = cmul b a := by decide +kernel
  intro ε hε η hη
  apply pcode_injective
  rw [pcode_mul, pcode_mul]
  exact h _ hε _ hη

theorem le_of_E7 {Q₁ Q₂ : Subgroup (Perm (Fin 7))} (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂)
    (hne : Q₁ ≠ ⊥) (hn1 : E7 ≤ Subgroup.normalizer (Q₁ : Set (Perm (Fin 7))))
    (hn2 : E7 ≤ Subgroup.normalizer (Q₂ : Set (Perm (Fin 7)))) : Q₂ ≤ Q₁ :=
  le_of_lattice_checks (by norm_num) E7_pow (fun _ he => exists_mem_ofCodes e7c_perm he)
    e7s_sub t7c crit7_check mix7_check tr7_check h2 hle hne hn1 hn2

end Seven

section Sylow

variable {n : ℕ}

theorem exists_conj_sylow [Fact (Nat.Prime 3)] (P P₀ : Sylow 3 (Perm (Fin n))) :
    ∃ g : Perm (Fin n), (P : Subgroup (Perm (Fin n))).map (MulAut.conj g).toMonoidHom = P₀ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin n)) P P₀
  refine ⟨g, ?_⟩
  have h : ((g • P : Sylow 3 (Perm (Fin n))) : Subgroup (Perm (Fin n))) =
      (P : Subgroup (Perm (Fin n))).map (MulAut.conj g).toMonoidHom := rfl
  rw [← h, hg]

theorem forall_mem_of_conj {P P₀ : Subgroup (Perm (Fin n))} {g : Perm (Fin n)}
    (hg : P.map (MulAut.conj g).toMonoidHom = P₀) {x : Perm (Fin n)} (hx : x ∈ P) :
    g * x * g⁻¹ ∈ P₀ := by
  rw [← hg]
  exact ⟨x, hx, rfl⟩

end Sylow

section SylowFive

theorem le_of_sylow_five (P : Sylow 3 (Perm (Fin 5))) {Q₁ Q₂ : Subgroup (Perm (Fin 5))}
    (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂) (hne : Q₁ ≠ ⊥)
    (hn1 : (P : Subgroup (Perm (Fin 5))) ≤ Subgroup.normalizer (Q₁ : Set (Perm (Fin 5))))
    (hn2 : (P : Subgroup (Perm (Fin 5))) ≤ Subgroup.normalizer (Q₂ : Set (Perm (Fin 5)))) :
    Q₂ ≤ Q₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E5Sylow
  rw [E5Sylow_coe] at hg
  exact le_of_conj g hg (fun R₁ R₂ h2' hle' hne' h1' h2'' => le_of_E5 h2' hle' hne' h1' h2'')
    h2 hle hne hn1 hn2

theorem sylow_five_pow (P : Sylow 3 (Perm (Fin 5))) : ∀ x ∈ P, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E5Sylow
  rw [E5Sylow_coe] at hg
  intro x hx
  have h := E5_pow _ (forall_mem_of_conj hg hx)
  rw [conj_pow] at h
  have := congrArg (fun y => g⁻¹ * y * g) h
  simpa [mul_assoc] using this

theorem sylow_five_comm (P : Sylow 3 (Perm (Fin 5))) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E5Sylow
  rw [E5Sylow_coe] at hg
  intro x hx y hy
  have h := E5_comm _ (forall_mem_of_conj hg hx) _ (forall_mem_of_conj hg hy)
  have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := h
      _ = g * (y * x) * g⁻¹ := by group
  simpa using h'

theorem card_sylow_five (P : Sylow 3 (Perm (Fin 5))) :
    Nat.card ↥(P : Subgroup (Perm (Fin 5))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E5Sylow
  rw [E5Sylow_coe] at hg
  have h := Subgroup.card_map_of_injective (K := (P : Subgroup (Perm (Fin 5))))
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [hg] at h
  rw [← h]
  exact card_E5

end SylowFive

section SylowSeven

theorem le_of_sylow_seven (P : Sylow 3 (Perm (Fin 7))) {Q₁ Q₂ : Subgroup (Perm (Fin 7))}
    (h2 : IsPGroup 2 Q₂) (hle : Q₁ ≤ Q₂) (hne : Q₁ ≠ ⊥)
    (hn1 : (P : Subgroup (Perm (Fin 7))) ≤ Subgroup.normalizer (Q₁ : Set (Perm (Fin 7))))
    (hn2 : (P : Subgroup (Perm (Fin 7))) ≤ Subgroup.normalizer (Q₂ : Set (Perm (Fin 7)))) :
    Q₂ ≤ Q₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E7Sylow
  rw [E7Sylow_coe] at hg
  exact le_of_conj g hg (fun R₁ R₂ h2' hle' hne' h1' h2'' => le_of_E7 h2' hle' hne' h1' h2'')
    h2 hle hne hn1 hn2

theorem sylow_seven_pow (P : Sylow 3 (Perm (Fin 7))) : ∀ x ∈ P, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E7Sylow
  rw [E7Sylow_coe] at hg
  intro x hx
  have h := E7_pow _ (forall_mem_of_conj hg hx)
  rw [conj_pow] at h
  have := congrArg (fun y => g⁻¹ * y * g) h
  simpa [mul_assoc] using this

theorem sylow_seven_comm (P : Sylow 3 (Perm (Fin 7))) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E7Sylow
  rw [E7Sylow_coe] at hg
  intro x hx y hy
  have h := E7_comm _ (forall_mem_of_conj hg hx) _ (forall_mem_of_conj hg hy)
  have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
    calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := h
      _ = g * (y * x) * g⁻¹ := by group
  simpa using h'

theorem card_sylow_seven (P : Sylow 3 (Perm (Fin 7))) :
    Nat.card ↥(P : Subgroup (Perm (Fin 7))) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_sylow P E7Sylow
  rw [E7Sylow_coe] at hg
  have h := Subgroup.card_map_of_injective (K := (P : Subgroup (Perm (Fin 7))))
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [hg] at h
  rw [← h]
  exact card_E7

end SylowSeven

end CFSG.RankThree.PartTwo.Sec15.Push153B
