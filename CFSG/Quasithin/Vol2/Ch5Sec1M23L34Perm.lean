module

public import CFSG.Sporadic.M23.M23Properties

public section

namespace CFSG.Quasithin.H13

namespace M23Perm

open CFSG.M23.M23Group

@[expose] noncomputable def fixCount (g : ↥H0) : ℕ :=
  (Finset.univ.filter fun p : Fin 23 => g • p = p).card

theorem card_fixingSubgroup_range
    {k : ℕ} (hk : k ≤ 4) (e : Fin k ↪ Fin 23) :
    Nat.card (fixingSubgroup ↥H0 (Set.range e)) * Nat.descFactorial 23 k = 10200960 := by
  let _ : MulAction ↥H0 (Fin k ↪ Fin 23) := Function.Embedding.instMulAction
  have hpre : MulAction.IsMultiplyPretransitive ↥H0 (Fin 23) k :=
    @MulAction.isMultiplyPretransitive_of_le _ _ _ _ k 4 four_pretransitive hk (by simp) _
  have horb : MulAction.orbit ↥H0 e = Set.univ := by
    refine Set.eq_univ_of_forall fun e' => ?_
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq e e'
    exact ⟨g, hg⟩
  have hidx := MulAction.index_stabilizer (↥H0) e
  rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin] at hidx
  have hst : MulAction.stabilizer ↥H0 e = fixingSubgroup ↥H0 (Set.range e) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_fixingSubgroup_iff]
    constructor
    · rintro h _ ⟨i, rfl⟩
      exact congrArg (fun f : Fin k ↪ Fin 23 => f i) h
    · intro h
      exact Function.Embedding.ext fun i => h _ ⟨i, rfl⟩
  rw [← hst, ← hidx, Subgroup.card_mul_index, Nat.card_eq_fintype_card, card_M23]

theorem card_fixingSubgroup
    (s : Finset (Fin 23)) (hs : s.card ≤ 4) :
    Nat.card (fixingSubgroup ↥H0 (s : Set (Fin 23))) * Nat.descFactorial 23 s.card =
      10200960 := by
  have hr : Set.range (s.orderEmbOfFin rfl).toEmbedding = (s : Set (Fin 23)) :=
    Finset.range_orderEmbOfFin s rfl
  rw [← hr]
  exact card_fixingSubgroup_range hs _

@[expose] def emb4 (a b c d : Fin 23) (h : [a, b, c, d].Nodup) : Fin 4 ↪ Fin 23 :=
  ⟨![a, b, c, d], fun i j hij => by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at h
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem exists_smul_eq_of_three
    {x y z u v : Fin 23} (hu : [x, y, z, u].Nodup) (hv : [x, y, z, v].Nodup) :
    ∃ g : ↥H0, g • x = x ∧ g • y = y ∧ g • z = z ∧ g • u = v := by
  let _ : MulAction ↥H0 (Fin 4 ↪ Fin 23) := Function.Embedding.instMulAction
  obtain ⟨g, hg⟩ := (four_pretransitive : MulAction.IsMultiplyPretransitive ↥H0 (Fin 23) 4)
    |>.exists_smul_eq (emb4 x y z u hu) (emb4 x y z v hv)
  have h : ∀ i : Fin 4, g • (emb4 x y z u hu) i = (emb4 x y z v hv) i := fun i =>
    congrArg (fun f : Fin 4 ↪ Fin 23 => f i) hg
  exact ⟨g, h 0, h 1, h 2, h 3⟩

theorem exists_not_mem_of_card_lt {s : Finset (Fin 23)} (hs : s.card < 23) : ∃ q, q ∉ s := by
  by_contra h
  push Not at h
  have h1 := Finset.card_le_card (fun q (_ : q ∈ Finset.univ) => h q)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem nodup_four {a b c d : Fin 23} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : [a, b, c, d].Nodup := by
  simp [List.nodup_cons, hab, hac, had, hbc, hbd, hcd]

theorem exists_fix_two_move
    {x y p : Fin 23} (hxy : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y) : ∃ g : ↥H0, g • x = x ∧ g • y = y ∧ g • p ≠ p := by
  classical
  obtain ⟨q, hq⟩ := exists_not_mem_of_card_lt (s := {x, y, p})
    (Finset.card_le_three.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  obtain ⟨hqx, hqy, hqp⟩ := hq
  obtain ⟨u, hu⟩ := exists_not_mem_of_card_lt (s := {x, y, p, q})
    (Finset.card_le_four.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨hux, huy, hup, huq⟩ := hu
  obtain ⟨g, hgx, hgy, -, hgp⟩ := exists_smul_eq_of_three (z := u)
    (nodup_four hxy (Ne.symm hux) (Ne.symm hpx) (Ne.symm huy) (Ne.symm hpy) hup)
    (nodup_four hxy (Ne.symm hux) (Ne.symm hqx) (Ne.symm huy) (Ne.symm hqy) huq)
  exact ⟨g, hgx, hgy, by rw [hgp]; exact hqp⟩

theorem exists_swap
    {x y : Fin 23} (hxy : x ≠ y) :
    ∃ g : ↥H0, g • x = y ∧ g • y = x := by
  classical
  obtain ⟨u, hu⟩ := exists_not_mem_of_card_lt (s := {x, y})
    (Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨hux, huy⟩ := hu
  obtain ⟨v, hv⟩ := exists_not_mem_of_card_lt (s := {x, y, u})
    (Finset.card_le_three.trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  obtain ⟨hvx, hvy, hvu⟩ := hv
  let _ : MulAction ↥H0 (Fin 4 ↪ Fin 23) := Function.Embedding.instMulAction
  have h1 := nodup_four hxy (Ne.symm hux) (Ne.symm hvx) (Ne.symm huy) (Ne.symm hvy) (Ne.symm hvu)
  have h2 := nodup_four (Ne.symm hxy) (Ne.symm huy) (Ne.symm hvy) (Ne.symm hux) (Ne.symm hvx)
    (Ne.symm hvu)
  obtain ⟨g, hg⟩ := (four_pretransitive : MulAction.IsMultiplyPretransitive ↥H0 (Fin 23) 4)
    |>.exists_smul_eq (emb4 x y u v h1) (emb4 y x u v h2)
  have h : ∀ i : Fin 4, g • (emb4 x y u v h1) i = (emb4 y x u v h2) i := fun i =>
    congrArg (fun f : Fin 4 ↪ Fin 23 => f i) hg
  exact ⟨g, h 0, h 1⟩

theorem card_dvd_of_fixes_four
    {K : Subgroup ↥H0} {s : Finset (Fin 23)} (hs : s.card = 4)
    (hK : ∀ g ∈ K, ∀ p ∈ s, g • p = p) : Nat.card K ∣ 48 := by
  have hle : K ≤ fixingSubgroup ↥H0 (s : Set (Fin 23)) := fun g hg =>
    (mem_fixingSubgroup_iff _).mpr fun p hp => hK g hg p hp
  have h := card_fixingSubgroup s hs.le
  rw [hs] at h
  have h48 : Nat.card (fixingSubgroup ↥H0 (s : Set (Fin 23))) = 48 := by
    have : Nat.descFactorial 23 4 = 212520 := by decide
    rw [this] at h
    omega
  rw [← h48]
  exact Subgroup.card_dvd_of_le hle

theorem fixCount_modEq {g : ↥H0} {p : ℕ} [hp : Fact p.Prime] (hg : orderOf g = p) :
    fixCount g ≡ 23 [MOD p] := by
  have hZ : IsPGroup p ↥(Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have h := hZ.card_modEq_card_fixedPoints (Fin 23)
  have hfix : MulAction.fixedPoints ↥(Subgroup.zpowers g) (Fin 23) =
      {q : Fin 23 | g • q = q} := by
    ext q
    simp only [MulAction.mem_fixedPoints, Set.mem_ofPred_eq]
    constructor
    · intro h'
      exact h' ⟨g, Subgroup.mem_zpowers g⟩
    · rintro h' ⟨z, hz⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hst : g ∈ MulAction.stabilizer ↥H0 q := h'
      exact (MulAction.stabilizer ↥H0 q).zpow_mem hst n
  rw [hfix, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hc : Nat.card ↑{q : Fin 23 | g • q = q} = fixCount g := by
    rw [fixCount, ← Fintype.card_coe, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun q => by simp)
  rw [hc] at h
  exact h.symm

theorem fixCount_le_three
    {g : ↥H0} {p : ℕ} (hg : orderOf g = p) (h48 : ¬ p ∣ 48) : fixCount g ≤ 3 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ.filter fun q : Fin 23 =>
    g • q = q) (n := 4) hlt
  have hK : ∀ h ∈ Subgroup.zpowers g, ∀ q ∈ s, h • q = q := by
    intro h hh q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hq' : g ∈ MulAction.stabilizer ↥H0 q := (Finset.mem_filter.mp (hs hq)).2
    exact (MulAction.stabilizer ↥H0 q).zpow_mem hq' n
  have hdvd := card_dvd_of_fixes_four hcard hK
  rw [Nat.card_zpowers, hg] at hdvd
  exact h48 hdvd

theorem fixCount_eq_two_of_orderOf_seven
    {g : ↥H0} (hg : orderOf g = 7) : fixCount g = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := fixCount_modEq hg
  have h2 := fixCount_le_three hg (by norm_num)
  unfold Nat.ModEq at h1
  omega

theorem fixCount_eq_three_of_orderOf_five
    {g : ↥H0} (hg : orderOf g = 5) : fixCount g = 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 := fixCount_modEq hg
  have h2 := fixCount_le_three hg (by norm_num)
  unfold Nat.ModEq at h1
  omega

end M23Perm

end CFSG.Quasithin.H13
