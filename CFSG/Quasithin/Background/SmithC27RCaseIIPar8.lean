module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimPerm
public import CFSG.Quasithin.Background.SmithC27AltSetup

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.QuasithinUnique Equiv Equiv.Perm

private def xi8 : Perm (Fin 8) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

private def c0GenC : List (List ℕ) :=
  [[1, 0, 3, 2, 4, 5, 6, 7], [2, 3, 0, 1, 4, 5, 6, 7], [4, 5, 6, 7, 0, 1, 2, 3]]

private def c0Tree : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2), (3, 0), (3, 1), (4, 2), (5, 0), (5, 1),
    (6, 0), (6, 1), (7, 1), (7, 2), (8, 2), (9, 0), (9, 1), (10, 1), (10, 2), (11, 2), (12, 1),
    (12, 2), (13, 2), (14, 2), (17, 1), (17, 2), (18, 2), (19, 2), (22, 2), (26, 2)]

private def c0Tbl : List (List ℕ) :=
  [[1, 2, 3], [0, 4, 5], [4, 0, 6], [7, 8, 0], [2, 1, 9], [10, 11, 1], [12, 13, 2], [3, 14, 15],
    [14, 3, 16], [17, 18, 4], [5, 19, 20], [19, 5, 21], [6, 22, 23], [22, 6, 24], [8, 7, 25],
    [20, 23, 7], [21, 24, 8], [9, 26, 27], [26, 9, 28], [11, 10, 29], [15, 27, 10],
    [16, 28, 11], [13, 12, 30], [27, 15, 12], [28, 16, 13], [29, 30, 14], [18, 17, 31],
    [23, 20, 17], [24, 21, 18], [25, 31, 19], [31, 25, 22], [30, 29, 26]]

private theorem c0_tbl : A6Facts.Core.tblCheckC (List.range 8) c0GenC
    (A6Facts.Core.buildCodes (List.range 8) c0GenC c0Tree) c0Tbl = true := by decide +kernel

private def c0Gens : List (Perm (Fin 8)) :=
  [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7]

private theorem c0Gens_code : c0Gens.map (A6Facts.codeN 8) = c0GenC := by decide +kernel

private def cList (u v : Fin 8) : List ℕ :=
  [(u : ℕ), (Claim2526.zeta8 u : ℕ), (xi8 u : ℕ), (Claim2526.zeta8 (xi8 u) : ℕ), (v : ℕ),
    (Claim2526.zeta8 v : ℕ), (xi8 v : ℕ), (Claim2526.zeta8 (xi8 v) : ℕ)]

private theorem cList_mem : ∀ u v : Fin 8, (cList u v).Nodup →
    cList u v ∈ A6Facts.Core.buildCodes (List.range 8) c0GenC c0Tree := by
  decide +kernel

private theorem mem_c0_of_commute {h : Perm (Fin 8)}
    (h1 : h * Claim2526.zeta8 = Claim2526.zeta8 * h) (h2 : h * xi8 = xi8 * h) :
    h ∈ Subgroup.closure {g | g ∈ c0Gens} := by
  rw [(A6Facts.mem_closure_iff_of_tblN c0Gens_code c0_tbl).1 h]
  have key : ∀ (w : Perm (Fin 8)) (x : Fin 8), h * w = w * h → h (w x) = w (h x) := by
    intro w x hw
    have := congrArg (fun f => f x) hw
    simpa using this
  have e1 : h 1 = Claim2526.zeta8 (h 0) := by
    have := key _ 0 h1
    rwa [show Claim2526.zeta8 0 = 1 by decide] at this
  have e2 : h 2 = xi8 (h 0) := by
    have := key _ 0 h2
    rwa [show xi8 0 = 2 by decide] at this
  have e3 : h 3 = Claim2526.zeta8 (xi8 (h 0)) := by
    have := key _ 2 h1
    rwa [show Claim2526.zeta8 2 = 3 by decide, e2] at this
  have e5 : h 5 = Claim2526.zeta8 (h 4) := by
    have := key _ 4 h1
    rwa [show Claim2526.zeta8 4 = 5 by decide] at this
  have e6 : h 6 = xi8 (h 4) := by
    have := key _ 4 h2
    rwa [show xi8 4 = 6 by decide] at this
  have e7 : h 7 = Claim2526.zeta8 (xi8 (h 4)) := by
    have := key _ 6 h1
    rwa [show Claim2526.zeta8 6 = 7 by decide, e6] at this
  have hcode : A6Facts.codeN 8 h = cList (h 0) (h 4) := by
    rw [Claim2526.codeN8, e1, e2, e3, e5, e6, e7]
    rfl
  have hnd : (A6Facts.codeN 8 h).Nodup := by
    unfold A6Facts.codeN
    rw [List.nodup_ofFn]
    intro a b hab
    exact h.injective (Fin.ext hab)
  rw [hcode] at hnd ⊢
  exact cList_mem _ _ hnd

private theorem closure_c0_le_alternatingGroup :
    Subgroup.closure {g | g ∈ c0Gens} ≤ alternatingGroup (Fin 8) := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [c0Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> rw [SetLike.mem_coe, Perm.mem_alternatingGroup] <;> decide

private theorem exists_frame_four_group {z z' : Perm (Fin 8)} (hz : z * z = 1) (hz' : z' * z' = 1)
    (hzz' : z * z' = z' * z) (hfz : ∀ x, z x ≠ x) (hfz' : ∀ x, z' x ≠ x)
    (hfzz' : ∀ x, z (z' x) ≠ x) :
    ∃ E : Perm (Fin 8), z * E = E * Claim2526.zeta8 ∧ z' * E = E * xi8 := by
  have h2 := apply_apply_of_mul_self hz
  have h2' := apply_apply_of_mul_self hz'
  have hc : ∀ p, z (z' p) = z' (z p) := fun p => by
    simpa only [Perm.mul_apply] using congrArg (fun f : Perm (Fin 8) => f p) hzz'
  have hb : ∀ p, p ≠ z p ∧ p ≠ z' p ∧ p ≠ z (z' p) ∧ z p ≠ z' p ∧ z p ≠ z (z' p) ∧
      z' p ≠ z (z' p) := fun p =>
    ⟨(hfz p).symm, (hfz' p).symm, (hfzz' p).symm, fun h => hfzz' p (by rw [← h, h2]),
      fun h => hfz' p (z.injective h).symm, (hfz (z' p)).symm⟩
  set x : Fin 8 := 0
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x, z x, z' x, z (z' x)} : Finset (Fin 8))) (t := Finset.univ)
    (Finset.card_le_four.trans_lt (by simp))
  set S : Fin 8 → Prop := fun q => q = x ∨ q = z x ∨ q = z' x ∨ q = z (z' x)
  have hyS : ¬ S y := by simpa [S] using hy
  have hSz : ∀ q, S q → S (z q) := by
    rintro q (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (h2 x)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (h2 _)))
  have hSz' : ∀ q, S q → S (z' q) := by
    rintro q (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (hc x).symm))
    · exact Or.inl (h2' x)
    · exact Or.inr (Or.inl (by rw [← hc, h2']))
  have hy1 : ¬ S (z y) := fun h => hyS (h2 y ▸ hSz _ h)
  have hy2 : ¬ S (z' y) := fun h => hyS (h2' y ▸ hSz' _ h)
  have hy3 : ¬ S (z (z' y)) := fun h => hy2 (h2 (z' y) ▸ hSz _ h)
  have hout : ∀ q, ¬ S q → x ≠ q ∧ z x ≠ q ∧ z' x ≠ q ∧ z (z' x) ≠ q := fun q hq =>
    ⟨fun h => hq (Or.inl h.symm), fun h => hq (Or.inr (Or.inl h.symm)),
      fun h => hq (Or.inr (Or.inr (Or.inl h.symm))), fun h => hq (Or.inr (Or.inr (Or.inr h.symm)))⟩
  obtain ⟨a01, a02, a03, a12, a13, a23⟩ := hb x
  obtain ⟨b01, b02, b03, b12, b13, b23⟩ := hb y
  obtain ⟨c00, c10, c20, c30⟩ := hout y hyS
  obtain ⟨c01, c11, c21, c31⟩ := hout _ hy1
  obtain ⟨c02, c12, c22, c32⟩ := hout _ hy2
  obtain ⟨c03, c13, c23, c33⟩ := hout _ hy3
  let e : Fin 8 → Fin 8 := ![x, z x, z' x, z (z' x), y, z y, z' y, z (z' y)]
  have hinj : Function.Injective e := by
    rw [← List.nodup_ofFn]
    show [x, z x, z' x, z (z' x), y, z y, z' y, z (z' y)].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    exact ⟨⟨a01, a02, a03, c00, c01, c02, c03⟩, ⟨a12, a13, c10, c11, c12, c13⟩,
      ⟨a23, c20, c21, c22, c23⟩, ⟨c30, c31, c32, c33⟩, ⟨b01, b02, b03⟩, ⟨b12, b13⟩, b23⟩
  let E : Perm (Fin 8) := Equiv.ofBijective e (Finite.injective_iff_bijective.mp hinj)
  have hz8 : ∀ k : Fin 8, Claim2526.zeta8 k = ![1, 0, 3, 2, 5, 4, 7, 6] k := by decide
  have hxi : ∀ k : Fin 8, xi8 k = ![2, 3, 0, 1, 6, 7, 4, 5] k := by decide
  refine ⟨E, Equiv.ext fun k => ?_, Equiv.ext fun k => ?_⟩
  · simp only [Perm.mul_apply, E, Equiv.ofBijective_apply, hz8]
    fin_cases k <;> simp [e, h2]
  · simp only [Perm.mul_apply, E, Equiv.ofBijective_apply, hxi]
    fin_cases k <;> simp [e, h2', ← hc]

theorem sign_eq_one_of_commute_semiregular {z z' g : Perm (Fin 8)} (hz : z * z = 1)
    (hz' : z' * z' = 1) (hzz' : z * z' = z' * z) (hfz : ∀ x, z x ≠ x) (hfz' : ∀ x, z' x ≠ x)
    (hfzz' : ∀ x, z (z' x) ≠ x) (hg : g * z = z * g) (hg' : g * z' = z' * g) :
    Equiv.Perm.sign g = 1 := by
  obtain ⟨E, hE, hE'⟩ := exists_frame_four_group hz hz' hzz' hfz hfz' hfzz'
  have hc : ∀ (w w' : Perm (Fin 8)), w * E = E * w' → g * w = w * g →
      E⁻¹ * g * E * w' = w' * (E⁻¹ * g * E) := by
    intro w w' hw hgw
    have hw' : w' = E⁻¹ * w * E := by rw [mul_assoc, hw, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hw']
    calc E⁻¹ * g * E * (E⁻¹ * w * E) = E⁻¹ * (g * w) * E := by group
      _ = E⁻¹ * (w * g) * E := by rw [hgw]
      _ = E⁻¹ * w * E * (E⁻¹ * g * E) := by group
  have hmem := closure_c0_le_alternatingGroup (mem_c0_of_commute (hc _ _ hE hg) (hc _ _ hE' hg'))
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv,
    mul_comm (Perm.sign E), mul_assoc, Int.units_mul_self, mul_one] at hmem
  exact hmem

private def e8GenC : List (List ℕ) :=
  [[1, 0, 2, 3, 4, 5, 6, 7], [0, 1, 3, 2, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 6, 7],
    [0, 1, 2, 3, 4, 5, 7, 6]]

private def e8Tree : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (5, 2), (5, 3),
    (6, 3), (8, 3), (11, 3)]

private def e8Tbl : List (List ℕ) :=
  [[1, 2, 3, 4], [0, 5, 6, 7], [5, 0, 8, 9], [6, 8, 0, 10], [7, 9, 10, 0], [2, 1, 11, 12],
    [3, 11, 1, 13], [4, 12, 13, 1], [11, 3, 2, 14], [12, 4, 14, 2], [13, 14, 4, 3],
    [8, 6, 5, 15], [9, 7, 15, 5], [10, 15, 7, 6], [15, 10, 9, 8], [14, 13, 12, 11]]

private theorem e8_tbl : A6Facts.Core.tblCheckC (List.range 8) e8GenC
    (A6Facts.Core.buildCodes (List.range 8) e8GenC e8Tree) e8Tbl = true := by decide +kernel

private theorem e8_nodup : (A6Facts.Core.buildCodes (List.range 8) e8GenC e8Tree).Nodup := by
  decide +kernel

private theorem e8_length :
    (A6Facts.Core.buildCodes (List.range 8) e8GenC e8Tree).length = 16 := by
  decide +kernel

private def e8Gens : List (Perm (Fin 8)) := [swap 0 1, swap 2 3, swap 4 5, swap 6 7]

private theorem e8Gens_code : e8Gens.map (A6Facts.codeN 8) = e8GenC := by decide +kernel

private theorem swapGroupOf_zeta8_eq :
    swapGroupOf Claim2526.zeta8 Claim2526.zeta8_mul_self = Subgroup.closure {g | g ∈ e8Gens} := by
  apply le_antisymm
  · rw [swapGroupOf_eq_closure, Subgroup.closure_le]
    rintro s ⟨x, -, rfl⟩
    apply Subgroup.subset_closure
    simp only [e8Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false]
    fin_cases x <;> decide
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [e8Gens, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact mem_swapGroupOf.2 (by decide)

private theorem card_swapGroupOf_zeta8 :
    Nat.card (swapGroupOf Claim2526.zeta8 Claim2526.zeta8_mul_self) = 16 := by
  rw [swapGroupOf_zeta8_eq, A6Facts.card_closure_eq_of_tblN e8Gens_code e8_tbl e8_nodup,
    e8_length]

theorem card_swapGroupOf_eight {z : Perm (Fin 8)} (hz : z * z = 1) (hf : ∀ x, z x ≠ x) :
    Nat.card (swapGroupOf z hz) = 16 := by
  have hsupp : ∀ w : Perm (Fin 8), (∀ x, w x ≠ x) → w.support.card = 8 := fun w hw => by
    rw [Finset.eq_univ_of_forall fun x => Perm.mem_support.2 (hw x), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨σ, hσ⟩ := exists_conj_of_mul_self hz Claim2526.zeta8_mul_self
    (by rw [hsupp z hf, hsupp _ Claim2526.zeta8_ne])
  have hz' : σ * z * σ⁻¹ * (σ * z * σ⁻¹) = 1 := by
    rw [hσ]
    exact Claim2526.zeta8_mul_self
  have heq : ∀ (w : Perm (Fin 8)) (hw : w * w = 1), w = Claim2526.zeta8 →
      swapGroupOf w hw = swapGroupOf Claim2526.zeta8 Claim2526.zeta8_mul_self := by
    rintro w hw rfl
    rfl
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj σ).toMonoidHom) (MulEquiv.injective _),
    map_conj_swapGroupOf hz σ hz', heq _ hz' hσ, card_swapGroupOf_zeta8]

end CFSG.Quasithin.SmithC27
