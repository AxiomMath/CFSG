module

public import CFSG.Quasithin.Background.JonesParshallWords
public import CFSG.Quasithin.SteinbergCBG2TwoBits

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two Equiv

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem mApp_lt_pow {m : ℕ} : ∀ (M : List ℕ), (∀ c ∈ M, c < 2 ^ m) → ∀ x, mApp M x < 2 ^ m
  | [], _, _ => by simp [mApp]
  | c :: cs, hM, x => by
    simp only [mApp]
    apply Nat.xor_lt_two_pow
    · split_ifs
      · exact hM c (List.mem_cons_self ..)
      · exact Nat.two_pow_pos m
    · exact mApp_lt_pow cs (fun c' hc' => hM c' (List.mem_cons_of_mem _ hc')) _

@[expose] def foxCode {k : ℕ} (cols : List (List ℕ)) (vals : List ℕ) : List (Fin k) → ℕ
  | [] => 0
  | i :: w => vals.getD i 0 ^^^ mApp (cols.getD i []) (foxCode cols vals w)

theorem foxEval_toV {G : Type*} [Group G] {k m : ℕ} {μ : G →* AddMonoid.End (Fin m → ZMod 2)}
    {gens : Fin k → G} {cols : List (List ℕ)} (hcols : ∀ i : Fin k, ∀ c ∈ cols.getD i [], c < 2 ^ m)
    (hμ : ∀ i : Fin k, ∀ x < 2 ^ m, μ (gens i) (toV m x) = toV m (mApp (cols.getD i []) x))
    {vals : List ℕ} (hvals : ∀ i : Fin k, vals.getD i 0 < 2 ^ m) :
    ∀ w : List (Fin k), foxEval μ gens (fun i => toV m (vals.getD i 0)) w =
      toV m (foxCode cols vals w) ∧ foxCode cols vals w < 2 ^ m
  | [] => ⟨(toV_zero m).symm, Nat.two_pow_pos m⟩
  | i :: w => by
    obtain ⟨h1, h2⟩ := foxEval_toV hcols hμ hvals w
    refine ⟨?_, Nat.xor_lt_two_pow (hvals i) (mApp_lt_pow _ (hcols i) _)⟩
    change toV m (vals.getD i 0) + μ (gens i) (foxEval μ gens _ w) = toV m (_ ^^^ _)
    rw [h1, hμ i _ h2, toV_xor]

theorem vec_sub_eq_add {m : ℕ} (a b : Fin m → ZMod 2) : a - b = a + b := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize a i = x
  generalize b i = y
  revert x y
  decide

theorem vec_add_self {m : ℕ} (a : Fin m → ZMod 2) : a + a = 0 := by
  rw [← vec_sub_eq_add, sub_self]

theorem classify_Z1A {G : Type*} [Group G] {m : ℕ} {μ : G →* AddMonoid.End (Fin m → ZMod 2)}
    {gens : Fin 2 → G} (hgen : Subgroup.closure (Set.range gens) = ⊤) {cols : List (List ℕ)}
    (hcols : ∀ i : Fin 2, ∀ c ∈ cols.getD i [], c < 2 ^ m)
    (hμ : ∀ i : Fin 2, ∀ x < 2 ^ m, μ (gens i) (toV m x) = toV m (mApp (cols.getD i []) x))
    {rels : List (List (Fin 2))} (hrels : ∀ r ∈ rels, wordEval gens r = 1)
    {f₀ : G → Fin m → ZMod 2} (hf₀ : f₀ ∈ Z1A μ) {c : List ℕ}
    (hc : ∀ i : Fin 2, f₀ (gens i) = toV m (c.getD i 0))
    (hclass : ∀ v₀ < 2 ^ m, ∀ v₁ < 2 ^ m, (∀ r ∈ rels, foxCode cols [v₀, v₁] r = 0) →
      ∃ x < 2 ^ m, ∃ ε < 2, v₀ = mApp (cols.getD 0 []) x ^^^ x ^^^ ε * c.getD 0 0 ∧
        v₁ = mApp (cols.getD 1 []) x ^^^ x ^^^ ε * c.getD 1 0) :
    ∀ f ∈ Z1A μ, f ∈ B1A μ ∨ f - f₀ ∈ B1A μ := by
  intro f hf
  set vals : List ℕ := [ofV (f (gens 0)), ofV (f (gens 1))] with hvals
  have hvlt : ∀ i : Fin 2, vals.getD i 0 < 2 ^ m := by
    intro i
    fin_cases i
    · exact ofV_lt _
    · exact ofV_lt _
  have hfv : (fun i : Fin 2 => f (gens i)) = fun i : Fin 2 => toV m (vals.getD i 0) := by
    funext i
    fin_cases i
    · exact (toV_ofV _).symm
    · exact (toV_ofV _).symm
  have hfox : ∀ r ∈ rels, foxCode cols vals r = 0 := by
    intro r hr
    have h1 := Z1A_wordEval hf gens r
    rw [hrels r hr, Z1A_one hf, hfv] at h1
    obtain ⟨h2, h3⟩ := foxEval_toV hcols hμ hvlt r
    rw [h2] at h1
    exact toV_inj h3 (Nat.two_pow_pos m) (h1.symm.trans (toV_zero m).symm)
  obtain ⟨x, hx, ε, hε, h0, h1⟩ := hclass _ (hvlt 0) _ (hvlt 1) hfox
  have hval : ∀ i : Fin 2, f (gens i) = μ (gens i) (toV m x) - toV m x +
      toV m (ε * c.getD i 0) := by
    intro i
    have hfi : f (gens i) = toV m (vals.getD i 0) := congrFun hfv i
    have hvi : vals.getD i 0 = mApp (cols.getD i []) x ^^^ x ^^^ ε * c.getD i 0 := by
      fin_cases i
      · exact h0
      · exact h1
    rw [hfi, hvi, toV_xor, toV_xor, hμ i x hx, vec_sub_eq_add]
  have hfin : ∀ g ∈ Z1A μ, (∀ i : Fin 2, g (gens i) = 0) → g = 0 := fun g hg h0 =>
    eq_zero_of_vanish_closure hg hgen (by
      rintro _ ⟨i, rfl⟩
      exact h0 i)
  interval_cases ε
  · left
    refine ⟨toV m x, (sub_eq_zero.1 (hfin _ (sub_mem hf (B1A_le_Z1A _ ⟨toV m x, rfl⟩))
      fun i => ?_)).symm⟩
    change f (gens i) - (μ (gens i) (toV m x) - toV m x) = 0
    rw [hval i, zero_mul, toV_zero, add_zero, sub_self]
  · right
    refine ⟨toV m x, (sub_eq_zero.1 (hfin _ (sub_mem (sub_mem hf hf₀)
      (B1A_le_Z1A _ ⟨toV m x, rfl⟩)) fun i => ?_)).symm⟩
    change f (gens i) - f₀ (gens i) - (μ (gens i) (toV m x) - toV m x) = 0
    rw [hval i, one_mul, ← hc i]
    abel

theorem not_mem_B1A_of_codes {G : Type*} [Group G] {m : ℕ}
    {μ : G →* AddMonoid.End (Fin m → ZMod 2)} {gens : Fin 2 → G} {cols : List (List ℕ)}
    (hcols : ∀ i : Fin 2, ∀ c ∈ cols.getD i [], c < 2 ^ m)
    (hμ : ∀ i : Fin 2, ∀ x < 2 ^ m, μ (gens i) (toV m x) = toV m (mApp (cols.getD i []) x))
    {f₀ : G → Fin m → ZMod 2} {c : List ℕ} (hclt : ∀ i : Fin 2, c.getD i 0 < 2 ^ m)
    (hc : ∀ i : Fin 2, f₀ (gens i) = toV m (c.getD i 0))
    (hno : ∀ x < 2 ^ m, ¬(c.getD 0 0 = mApp (cols.getD 0 []) x ^^^ x ∧
      c.getD 1 0 = mApp (cols.getD 1 []) x ^^^ x)) :
    f₀ ∉ B1A μ := by
  rintro ⟨v, hv⟩
  have hi : ∀ i : Fin 2, c.getD i 0 = mApp (cols.getD i []) (ofV v) ^^^ ofV v := by
    intro i
    have h : μ (gens i) v - v = f₀ (gens i) := congrFun hv (gens i)
    rw [hc i, ← toV_ofV v, hμ i _ (ofV_lt v), vec_sub_eq_add, ← toV_xor] at h
    exact toV_inj (hclt i) (Nat.xor_lt_two_pow (mApp_lt_pow _ (hcols i) _) (ofV_lt v)) h.symm
  exact hno _ (ofV_lt v) ⟨hi 0, hi 1⟩

theorem card_Z1A_eq_two_mul {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    {μ : G →* AddMonoid.End M} (h2 : ∀ x : M, x + x = 0) {f₀ : G → M} (hf₀ : f₀ ∈ Z1A μ)
    (hnot : f₀ ∉ B1A μ) (hcl : ∀ f ∈ Z1A μ, f ∈ B1A μ ∨ f - f₀ ∈ B1A μ) :
    Nat.card (Z1A μ) = 2 * Nat.card (B1A μ) := by
  set H := (B1A μ).addSubgroupOf (Z1A μ)
  have hff : f₀ + f₀ = 0 := funext fun g => h2 (f₀ g)
  have hidx : H.index = 2 := by
    refine AddSubgroup.index_eq_two_iff.2 ⟨⟨f₀, hf₀⟩, fun b => ?_⟩
    simp only [H, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add]
    rcases hcl b b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h => hnot ?_⟩
      have := sub_mem h hb
      rwa [add_sub_cancel_left] at this
    · refine Or.inl ⟨?_, fun h => hnot ?_⟩
      · have := add_mem hb (show f₀ + f₀ ∈ B1A μ by rw [hff]; exact zero_mem _)
        rwa [sub_add_add_cancel] at this
      · have := sub_mem h hb
        rwa [sub_sub_cancel] at this
  have h := AddSubgroup.card_mul_index H
  rw [hidx, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (B1A_le_Z1A μ)).toEquiv] at h
  rw [← h, mul_comm]

theorem val_wordEval {G : Type*} [Group G] {H : Subgroup G} {k : ℕ} (gens : Fin k → ↥H) :
    ∀ w : List (Fin k), ((wordEval gens w : ↥H) : G) = wordEval (fun i => (gens i : G)) w
  | [] => rfl
  | i :: w => by
    change ((gens i : G) * ((wordEval gens w : ↥H) : G)) = _
    rw [val_wordEval gens w]
    rfl

theorem wordEval_mem_closure_range {G : Type*} [Group G] {k : ℕ} (gens : Fin k → G) :
    ∀ w : List (Fin k), wordEval gens w ∈ Subgroup.closure (Set.range gens)
  | [] => Subgroup.one_mem _
  | i :: w => Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
      (wordEval_mem_closure_range gens w)

variable {n : ℕ}

@[expose] def fixLow (K : Subgroup (Perm (Fin n))) (j : ℕ) : Subgroup (Perm (Fin n)) where
  carrier := {g | g ∈ K ∧ ∀ t : Fin n, t.val < j → g t = t}
  mul_mem' := fun {g h} hg hh => ⟨K.mul_mem hg.1 hh.1, fun t ht => by
    rw [Perm.mul_apply, hh.2 t ht, hg.2 t ht]⟩
  one_mem' := ⟨K.one_mem, fun _ _ => rfl⟩
  inv_mem' := fun {g} hg => ⟨K.inv_mem hg.1, fun t ht => by
    rw [Perm.inv_eq_iff_eq]
    exact (hg.2 t ht).symm⟩

theorem mem_fixLow {K : Subgroup (Perm (Fin n))} {j : ℕ} {g : Perm (Fin n)} :
    g ∈ fixLow K j ↔ g ∈ K ∧ ∀ t : Fin n, t.val < j → g t = t := Iff.rfl

theorem fixLow_zero (K : Subgroup (Perm (Fin n))) : fixLow K 0 = K := by
  ext g
  rw [mem_fixLow]
  exact ⟨fun h => h.1, fun h => ⟨h, fun t ht => absurd ht (Nat.not_lt_zero _)⟩⟩

theorem card_fixLow_succ_le (K : Subgroup (Perm (Fin n))) (j : ℕ) (hj : j < n)
    (htr : ∀ y : Fin n, j ≤ y.val → ∃ g ∈ fixLow K j, g ⟨j, hj⟩ = y) :
    (n - j) * Nat.card (fixLow K (j + 1)) ≤ Nat.card (fixLow K j) := by
  let T := {y : Fin n // j ≤ y.val}
  have hT : Nat.card T = n - j := by
    rw [Nat.card_congr (show T ≃ Fin (n - j) from
      { toFun := fun y => ⟨y.1.val - j, by have := y.1.isLt; have := y.2; omega⟩
        invFun := fun i => ⟨⟨i.val + j, by have := i.isLt; omega⟩, by simp⟩
        left_inv := fun y => by
          apply Subtype.ext
          apply Fin.ext
          simp only
          have := y.2
          omega
        right_inv := fun i => by
          apply Fin.ext
          simp })]
    exact Nat.card_eq_fintype_card.trans (Fintype.card_fin _)
  choose g hg hgy using htr
  have hle : fixLow K (j + 1) ≤ fixLow K j := fun s hs =>
    ⟨hs.1, fun t ht => hs.2 t (by omega)⟩
  let F : T × ↥(fixLow K (j + 1)) → ↥(fixLow K j) := fun p =>
    ⟨g p.1.1 p.1.2, hg p.1.1 p.1.2⟩ * ⟨p.2, hle p.2.2⟩
  have hF : Function.Injective F := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ h
    have hpt : ∀ s : ↥(fixLow K (j + 1)), (s : Perm (Fin n)) ⟨j, hj⟩ = ⟨j, hj⟩ := fun s =>
      s.2.2 _ (Nat.lt_succ_self j)
    have hval := congrArg (fun q : ↥(fixLow K j) => (q : Perm (Fin n)) ⟨j, hj⟩) h
    simp only [F, Subgroup.coe_mul, Perm.mul_apply, hpt, hgy] at hval
    have hyy : y = y' := Subtype.ext hval
    subst hyy
    have h' := congrArg Subtype.val h
    simp only [F, Subgroup.coe_mul] at h'
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  have h := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, hT] at h

theorem prod_le_card_fixLow (K : Subgroup (Perm (Fin n)))
    (htr : ∀ j : ℕ, (hj : j + 3 ≤ n) → ∀ y : Fin n, j ≤ y.val →
      ∃ g ∈ fixLow K j, g ⟨j, by omega⟩ = y) :
    ∀ d j : ℕ, j + d = n - 2 → 2 ≤ n →
      ∏ i ∈ Finset.range d, (n - (j + i)) ≤ Nat.card (fixLow K j)
  | 0, j, _, _ => by
    rw [Finset.prod_range_zero]
    exact Nat.card_pos
  | d + 1, j, hjd, hn => by
    rw [Finset.prod_range_succ']
    have ih := prod_le_card_fixLow K htr d (j + 1) (by omega) hn
    have hstep := card_fixLow_succ_le K j (by omega) (htr j (by omega))
    calc (∏ i ∈ Finset.range d, (n - (j + (i + 1)))) * (n - (j + 0)) =
          (n - j) * ∏ i ∈ Finset.range d, (n - (j + 1 + i)) := by
          rw [mul_comm, add_zero]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [add_assoc, add_comm 1 i]
      _ ≤ (n - j) * Nat.card (fixLow K (j + 1)) := Nat.mul_le_mul_left _ ih
      _ ≤ _ := hstep

theorem card_alternatingGroup_fin_mul_two (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) * 2 = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, mul_comm, two_mul_card_alternatingGroup, Fintype.card_perm,
    Fintype.card_fin]

theorem prod_range_mul_two : ∀ d : ℕ, (∏ i ∈ Finset.range d, (d + 2 - i)) * 2 = (d + 2).factorial
  | 0 => rfl
  | d + 1 => by
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have h := prod_range_mul_two d
    have hc : ∏ i ∈ Finset.range d, (d + 1 + 2 - (i + 1)) = ∏ i ∈ Finset.range d, (d + 2 - i) :=
      Finset.prod_congr rfl fun i _ => by omega
    rw [hc, Nat.sub_zero, ← h]
    ring

theorem closure_eq_top_of_transversals (hn : 2 ≤ n) {k : ℕ}
    (gens : Fin k → ↥(alternatingGroup (Fin n))) (tw : ℕ → ℕ → List (Fin k))
    (htw : ∀ j : Fin (n - 2), ∀ y : Fin n, j.val ≤ y.val →
      (∀ t : Fin n, t.val < j.val →
        wordEval (fun i => (gens i : Perm (Fin n))) (tw j y) t = t) ∧
      wordEval (fun i => (gens i : Perm (Fin n))) (tw j y) ⟨j.val, by omega⟩ = y) :
    Subgroup.closure (Set.range gens) = ⊤ := by
  set gP : Fin k → Perm (Fin n) := fun i => (gens i : Perm (Fin n))
  set K := Subgroup.closure (Set.range gP)
  have hKle : K ≤ alternatingGroup (Fin n) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact (gens i).2
  have htr : ∀ j : ℕ, (hj : j + 3 ≤ n) → ∀ y : Fin n, j ≤ y.val →
      ∃ g ∈ fixLow K j, g ⟨j, by omega⟩ = y := by
    intro j hj y hy
    obtain ⟨h1, h2⟩ := htw ⟨j, by omega⟩ y hy
    exact ⟨_, ⟨wordEval_mem_closure_range gP _, h1⟩, h2⟩
  have hprod := prod_le_card_fixLow K htr (n - 2) 0 (by omega) hn
  rw [fixLow_zero] at hprod
  have hcard : Nat.card ↥(alternatingGroup (Fin n)) ≤ Nat.card K := by
    have h1 := card_alternatingGroup_fin_mul_two n hn
    have h2 := prod_range_mul_two (n - 2)
    have hc : ∏ i ∈ Finset.range (n - 2), (n - (0 + i)) =
        ∏ i ∈ Finset.range (n - 2), (n - 2 + 2 - i) :=
      Finset.prod_congr rfl fun i _ => by omega
    have h3 : (n - 2 + 2).factorial = n.factorial := by rw [Nat.sub_add_cancel hn]
    rw [hc] at hprod
    omega
  have hK : K = alternatingGroup (Fin n) := Subgroup.eq_of_le_of_card_ge hKle hcard
  apply Subgroup.map_injective (alternatingGroup (Fin n)).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype, ← Set.range_comp]
  exact hK

end CFSG.Quasithin.SteinbergCB.I16
