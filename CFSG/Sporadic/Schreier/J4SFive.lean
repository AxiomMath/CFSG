
module

public import CFSG.Sporadic.Schreier.J4SFiveBase1

public import CFSG.Sporadic.Schreier.J4SPrimesCheck
public import CFSG.Sporadic.Schreier.J4SGL
public import CFSG.Sporadic.Schreier.J4SFrattini
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem card_fixed_eq {k : J} (hk : k ∈ K) :
    Nat.card {a : Fin 11 → ZMod 2 // (ρGL ⟨k, hk⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ a = a} =
      Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup J) := by
  refine Nat.card_congr
    { toFun := fun a => ⟨etaV a.1, Subgroup.mem_inf.2 ⟨?_, etaV_mem_N a.1⟩⟩
      invFun := fun n => ⟨Multiplicative.toAdd (eN.symm ⟨n.1, (Subgroup.mem_inf.1 n.2).2⟩), ?_⟩
      left_inv := fun a => Subtype.ext ?_
      right_inv := fun n => Subtype.ext ?_ }
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have e := etaV_ρGL ⟨k, hk⟩ a.1
    rw [a.2] at e
    calc etaV a.1 * k = k * etaV a.1 * k⁻¹ * k := by rw [← e]
      _ = k * etaV a.1 := by group
  · have hn : etaV (Multiplicative.toAdd (eN.symm ⟨n.1, (Subgroup.mem_inf.1 n.2).2⟩)) = n.1 := by
      rw [← eN_apply, MulEquiv.apply_symm_apply]
    apply etaV_injective
    rw [etaV_ρGL, hn]
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 n.2).1
    rw [← hc, mul_inv_cancel_right]
  · have e : (⟨etaV a.1, etaV_mem_N a.1⟩ : N) = eN (Multiplicative.ofAdd a.1) := by
      apply Subtype.ext
      rw [eN_apply, toAdd_ofAdd]
    dsimp only
    rw [e, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  · dsimp only
    rw [← eN_apply, MulEquiv.apply_symm_apply]

theorem qElt_acts :
    ActsBy qElt q5Cols := by
  change ActsBy (signedWord x y bWord ^ 48964608) q5Cols
  rw [← q5_cols]
  exact actsBy_pow 48964608 (word_conj_η_cols bWord)

theorem card_centralizer_qElt :
    Nat.card (Subgroup.centralizer {qElt} ⊓ N : Subgroup J) = 8 := by
  rw [card_centralizer_N_of_actsBy qElt_acts (bounded_getD q5_facts.2.2.2), q5_facts.2.2.1]

theorem eq_of_actsBy_bounded
    {g : J} {C D : Array ℕ} (hC : ActsBy g C) (hD : ActsBy g D)
    (hCb : Bounded C) (hDb : Bounded D) : C = D :=
  cols_eq_of_actsBy hC hD hCb.1 hDb.1 hCb.2 hDb.2

theorem eq_one_of_actsBy_id
    {g : J} (hg : g ∈ K) (h : ActsBy g (idRows 11)) : g = 1 :=
  eq_of_actsBy hg K.one_mem h actsBy_one

theorem orderOf_of_actsBy
    {g : J} (hg : g ∈ K) {C : Array ℕ} (hC : ActsBy g C) (hCb : Bounded C)
    {p : ℕ} [Fact p.Prime] (hp : powCols C p = idRows 11) (hne : C ≠ idRows 11) :
    orderOf g = p := by
  refine orderOf_eq_prime ?_ ?_
  · refine eq_one_of_actsBy_id (K.pow_mem hg p) ?_
    rw [← hp]
    exact actsBy_pow p hC
  · intro h1
    rw [h1] at hC
    exact hne (eq_of_actsBy_bounded hC actsBy_one hCb idRows_bounded)

theorem orderOf_qElt :
    orderOf qElt = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_of_actsBy qElt_mem_K qElt_acts q5_facts.2.2.2 q5_facts.1 q5_facts.2.1

theorem card_K_eq :

    Nat.card K = 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23 := by rw [card_K]; norm_num

theorem factorization_K
    {p : ℕ} (hp : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23) :
    (Nat.card K).factorization p = 1 := by
  have h2 : Nat.Prime 2 := Nat.prime_two
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  rw [card_K_eq]
  repeat rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow h2, Nat.Prime.factorization_pow h3,
    Nat.Prime.factorization h5, Nat.Prime.factorization h7, Nat.Prime.factorization h11,
    Nat.Prime.factorization h23, Finsupp.single_apply]
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem R3E_J4_local_five_elements_fixed_rank_three :
    qElt = (x * y * x * y * x * y⁻¹ * x * y⁻¹) ^ 48964608 ∧ qElt ∈ K ∧ orderOf qElt = 5 ∧
      Nat.card (Subgroup.centralizer {qElt} ⊓ N : Subgroup J) = 8 ∧
      ∀ (k : J) (hk : k ∈ K), orderOf k = 5 →
        Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup J) = 8 ∧
        Nat.card {a : Fin 11 → ZMod 2 //
          (ρGL ⟨k, hk⟩ : Matrix (Fin 11) (Fin 11) (ZMod 2)) *ᵥ a = a} = 2 ^ 3 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨?_, qElt_mem_K, orderOf_qElt, card_centralizer_qElt, fun k hk ok => ?_⟩
  · rw [qElt, bElt, signedWord_bWord]
  · have h := card_centralizer_N_eq (factorization_K (Or.inl rfl)) hk qElt_mem_K ok orderOf_qElt
    rw [card_centralizer_qElt] at h
    exact ⟨h, by rw [card_fixed_eq hk, h]; norm_num⟩

theorem orderOf_q7Elt :
    orderOf q7Elt = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_of_actsBy q7Elt_mem_K q7Elt_acts q7_facts.2.2.2 q7_facts.1 q7_facts.2.1

theorem card_centralizer_seven
    {k : J} (hk : k ∈ K) (ok : orderOf k = 7) :
    Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup J) = 4 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [card_centralizer_N_eq (factorization_K (Or.inr (Or.inl rfl))) hk q7Elt_mem_K ok
    orderOf_q7Elt, card_centralizer_N_of_actsBy q7Elt_acts (bounded_getD q7_facts.2.2.2),
    q7_facts.2.2.1]

theorem orderOf_q23Elt :
    orderOf q23Elt = 23 :=
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  orderOf_of_actsBy q23Elt_mem_K q23Elt_acts q23_facts.2.2 q23_facts.1 q23_facts.2.1

theorem not_commute_q23
    {k : J} (hk : k ∈ K) (hc : Commute k q23Elt) (ok : orderOf k = 11) :
    False := by
  obtain ⟨hC, hCb⟩ := colsOf_spec hk
  set C := colsOf k with hCdef
  have hQb := q23_facts.2.2
  have hcomm : comp11 C q23Cols = comp11 q23Cols C := by
    have h1 := actsBy_mul hC q23Elt_acts
    have h2 := actsBy_mul q23Elt_acts hC
    rw [hc.eq] at h1
    exact eq_of_actsBy_bounded h1 h2 (bounded_comp11 hCb hQb) (bounded_comp11 hQb hCb)
  have hX : colsMatrix C * colsMatrix q23Cols = colsMatrix q23Cols * colsMatrix C := by
    rw [← colsMatrix_comp11, ← colsMatrix_comp11, hcomm]
  set w := app11 C 1 with hw
  have hwlt : w < 2048 := vecMulN_lt (bounded_getD hCb) 1
  have hXc : Commute (colsMatrix C) (colsMatrix q23Cols) := hX
  have hXB : colsMatrix C * colsMatrix B23 = colsMatrix (polyCols w) := by
    refine matrix_eq_of_cols fun i => ?_
    have hpoly : ∀ v, (polyCols v)[i.val]?.getD 0 = app11 (powCols q23Cols i) v := by
      intro v
      rw [polyCols, Array.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
    rw [← Matrix.mulVec_mulVec, colsMatrix_mulVec_single, colsMatrix_mulVec_single, B23_facts.1,
      hpoly, hpoly, ← colsMatrix_mulVec, ← colsMatrix_mulVec, colsMatrix_powCols,
      Matrix.mulVec_mulVec, (hXc.pow_right i).eq, ← Matrix.mulVec_mulVec, colsMatrix_mulVec]
  have hCeq : C = comp11 (polyCols w) B23inv := by
    refine colsMatrix_inj hCb (bounded_comp11 (polyCols_bounded w hwlt) B23_facts.2.2.2) ?_
    have hBB : colsMatrix B23 * colsMatrix B23inv = 1 := by
      rw [← colsMatrix_comp11, B23_facts.2.1, colsMatrix_idRows]
    rw [colsMatrix_comp11, ← hXB, Matrix.mul_assoc, hBB, Matrix.mul_one]
  have h11 : powCols C 11 = idRows 11 := by
    have h1 := actsBy_pow 11 hC
    have hk11 : k ^ 11 = 1 := by
      rw [← ok]
      exact pow_orderOf_eq_one k
    rw [hk11] at h1
    exact eq_of_actsBy_bounded h1 actsBy_one (bounded_powCols 11 hCb) idRows_bounded
  rw [hCeq] at h11
  have hw1 := no_eleven w hwlt h11
  have hCid : C = idRows 11 := by
    rw [hCeq, hw1, ← B23_facts.1, B23_facts.2.1]
  rw [hCid] at hC
  have := eq_one_of_actsBy_id hk hC
  rw [this, orderOf_one] at ok
  omega

theorem not_commute_eleven_twentythree
    {e f : J} (he : e ∈ K) (hf : f ∈ K) (oe : orderOf e = 11)
    (of : orderOf f = 23) (hc : Commute e f) : False := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨g, hgK, hzp⟩ := exists_conj_zpowers (factorization_K (Or.inr (Or.inr (Or.inr rfl)))) hf
    q23Elt_mem_K of orderOf_q23Elt
  have hc' : Commute (g⁻¹ * e * g) q23Elt := by
    have h1 : Commute e (g * q23Elt * g⁻¹) := (commute_iff_of_zpowers_eq hzp).1 hc
    unfold Commute SemiconjBy at h1 ⊢
    calc g⁻¹ * e * g * q23Elt = g⁻¹ * (e * (g * q23Elt * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * q23Elt * g⁻¹) * e) * g := by rw [h1]
      _ = q23Elt * (g⁻¹ * e * g) := by group
  refine not_commute_q23 (K.mul_mem (K.mul_mem (K.inv_mem hgK) he) hgK) hc' ?_
  rw [show g⁻¹ * e * g = MulAut.conj g⁻¹ e by
    rw [MulAut.conj_apply, inv_inv], MulEquiv.orderOf_eq, oe]

end CFSG.Sporadic.J4Schreier
