module

public import CFSG.Quasithin.Vol2.KGFactJ4M3Cert
public import CFSG.Quasithin.Background.Special2Pairing

public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.KGC31
  CFSG.Quasithin.Special2
open scoped commutatorElement

@[expose] noncomputable def v0 : Fin 3 → J := ![eta uJ 11 422, eta uJ 11 553, eta uJ 11 1131]

@[expose] def v0mask (c : Fin 3 → ZMod 2) : ℕ :=
  (if c 0 = 1 then 422 else 0) ^^^ (if c 1 = 1 then 553 else 0) ^^^ (if c 2 = 1 then 1131 else 0)

@[expose] def cvec (m : ℕ) : Fin 3 → ZMod 2 :=
  if m = 422 then ![1, 0, 0] else if m = 553 then ![0, 1, 0] else if m = 911 then ![1, 1, 0]
  else if m = 1131 then ![0, 0, 1] else if m = 1485 then ![1, 0, 1]
  else if m = 1602 then ![0, 1, 1] else if m = 2020 then ![1, 1, 1] else 0

theorem v0mask_cvec : ∀ m ∈ v0Masks, v0mask (cvec m) = m := by decide

theorem v0mask_lt : ∀ c : Fin 3 → ZMod 2, v0mask c < 2 ^ 11 := by decide

theorem v0mask_eq_zero : ∀ c : Fin 3 → ZMod 2, v0mask c = 0 → c = 0 := by decide

theorem eta_pow_val (c : ℕ) (a : ZMod 2) :
    eta uJ 11 c ^ a.val = eta uJ 11 (if a = 1 then c else 0) := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  rcases ha with rfl | rfl
  · simp [eta_zero]
  · rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, ite_eq_left rfl]


theorem eElt_v0 (c : Fin 3 → ZMod 2) : eElt v0 c = eta uJ 11 (v0mask c) := by
  have hM := j4Facts.mat
  rw [eElt, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.prod_cons, List.prod_nil, mul_one, v0, Matrix.cons_val_zero,
    Matrix.cons_val_succ, eta_pow_val]
  rw [eta_mul_eta hM, eta_mul_eta hM, v0mask, Nat.xor_assoc]
  rfl

theorem hv0 : EBasis v0 := by
  have hM := j4Facts.mat
  refine ⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩
  · fin_cases i <;>
      simp only [v0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      rw [eta_mul_eta hM, Nat.xor_self, eta_zero]
  · show v0 i * v0 j = v0 j * v0 i
    fin_cases i <;> fin_cases j <;>
      simp only [v0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      rw [eta_mul_eta hM, eta_mul_eta hM, Nat.xor_comm]
  · rw [eElt_v0] at hc
    by_contra hc0
    have hne : v0mask c ≠ 0 := fun h => hc0 (v0mask_eq_zero c h)
    exact eta_ne_one hM hne (v0mask_lt c) hc

theorem eSub_v0 : eSub hv0 = V0 := by
  rw [eSub_eq_closure]
  congr 1
  ext x
  simp only [Set.mem_range, Fin.exists_fin_succ, Fin.exists_fin_zero, Set.mem_insert_iff,
    Set.mem_singleton_iff, v0, Matrix.cons_val_zero, Matrix.cons_val_succ, or_false]
  constructor
  · rintro (h | h | h) <;> simp [← h]
  · rintro (h | h | h) <;> simp [h]

theorem eta_mem_eSub {m : ℕ} (hm : m ∈ v0Masks) : eta uJ 11 m ∈ eSub hv0 :=
  eSub_v0.symm ▸ mem_V0_of_mem_v0Masks hm

@[expose] noncomputable def qF (i : Fin 12) : J := qJ i

theorem commTab_mem : ∀ i < 12, ∀ j < 12, (commTab.getD i []).getD j 0 ∈ v0Masks := by decide

theorem sqTab_mem : ∀ i < 12, sqTab.getD i 0 ∈ v0Masks := by decide


theorem pJ_centralizes {i : ℕ} (hi : i < 12) : ∀ v ∈ V0, pJ i * v = v * pJ i := by
  have hle : V0 ≤ Subgroup.centralizer {pJ i} := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl
    · exact (pJ_commute hi (by simp [v0Gens])).symm
    · exact (pJ_commute hi (by simp [v0Gens])).symm
    · exact (pJ_commute hi (by simp [v0Gens])).symm
  intro v hv
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm

theorem qJ_centralizes {i : ℕ} (hi : i < 12) : ∀ v ∈ V0, v * qJ i = qJ i * v := by
  intro v hv
  have hx := xM_mem_normalizer
  have hwV : xM⁻¹ * v * xM ∈ V0 := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) v).mp hv
    simpa using this
  have hpv := pJ_centralizes hi v hv
  have hpw := pJ_centralizes hi _ hwV
  have hw' : (xM⁻¹ * v * xM) * (pJ i)⁻¹ = (pJ i)⁻¹ * (xM⁻¹ * v * xM) := by
    calc (xM⁻¹ * v * xM) * (pJ i)⁻¹
        = (pJ i)⁻¹ * (pJ i * (xM⁻¹ * v * xM)) * (pJ i)⁻¹ := by group
      _ = (pJ i)⁻¹ * ((xM⁻¹ * v * xM) * pJ i) * (pJ i)⁻¹ := by rw [hpw]
      _ = (pJ i)⁻¹ * (xM⁻¹ * v * xM) := by group
  rw [qJ, commutatorElement_def]
  calc v * (pJ i * xM * (pJ i)⁻¹ * xM⁻¹) = (v * pJ i) * xM * (pJ i)⁻¹ * xM⁻¹ := by group
    _ = (pJ i * v) * xM * (pJ i)⁻¹ * xM⁻¹ := by rw [← hpv]
    _ = pJ i * xM * ((xM⁻¹ * v * xM) * (pJ i)⁻¹) * xM⁻¹ := by group
    _ = pJ i * xM * ((pJ i)⁻¹ * (xM⁻¹ * v * xM)) * xM⁻¹ := by rw [hw']
    _ = pJ i * xM * (pJ i)⁻¹ * xM⁻¹ * v := by group

theorem qTable : Table (eSub hv0) qF := by
  have hM := j4Facts.mat
  refine ⟨fun v hv w hw => eSub_comm hv0 v w hv hw, fun v hv i => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [eSub_v0] at hv
    exact qJ_centralizes i.2 v hv
  · show ⁅qJ i, qJ j⁆ ∈ eSub hv0
    rw [qJ_comm i.2 j.2]
    exact eta_mem_eSub (commTab_mem i i.2 j j.2)
  · show qJ i * qJ i ∈ eSub hv0
    rw [qJ_sq i.2]
    exact eta_mem_eSub (sqTab_mem i i.2)

@[expose] noncomputable def cEq : Multiplicative (Fin 3 → ZMod 2) ≃* ↥(eSub hv0) :=
  MonoidHom.ofInjective (f := eHom hv0) fun c d h => (eElt_injective hv0 h : c.toAdd = d.toAdd)

theorem cEq_symm_eta {m : ℕ} (hm : m ∈ v0Masks) :
    cEq.symm ⟨eta uJ 11 m, eta_mem_eSub hm⟩ = Multiplicative.ofAdd (cvec m) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  show eta uJ 11 m = eElt v0 (cvec m)
  rw [eElt_v0, v0mask_cvec m hm]

@[expose] def jsF : Fin 12 → Fin 12 := ![0, 0, 0, 1, 2, 2, 6, 6, 6, 7, 7, 8]

@[expose] def tsF : Fin 12 → Fin 3 := ![0, 1, 2, 2, 0, 1, 0, 1, 2, 0, 1, 0]

@[expose] def mRows : List ℕ := [758, 1657, 1439, 3912, 382, 1773, 20, 44, 49, 46, 33, 41]

@[expose] def mMat (k i : Fin 12) : ZMod 2 := if (mRows.getD k 0).testBit i then 1 else 0

theorem mMat_inv : ∀ k k' : Fin 12,
    ∑ i : Fin 12, mMat k i * cvec ((commTab.getD i []).getD (jsF k') 0) (tsF k') =
      if k = k' then 1 else 0 := by
  decide +kernel

@[expose] noncomputable def fF (k : Fin 12) : ↥(eSub hv0) →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd ((Multiplicative.toAdd (cEq.symm v)) (tsF k))
  map_one' := by
    show Multiplicative.ofAdd ((Multiplicative.toAdd (cEq.symm 1)) (tsF k)) = 1
    rw [MulEquiv.map_one]; rfl
  map_mul' a b := by
    show Multiplicative.ofAdd ((Multiplicative.toAdd (cEq.symm (a * b))) (tsF k)) = _
    rw [MulEquiv.map_mul]; rfl

theorem qPairing : Pairing qTable fF jsF mMat := by
  refine ⟨fun k k' => ?_⟩
  have hA : ∀ i : Fin 12,
      Multiplicative.toAdd (fF k' ⟨⁅qF i, qF (jsF k')⁆, qTable.comm i (jsF k')⟩) =
        cvec ((commTab.getD i []).getD (jsF k') 0) (tsF k') := by
    intro i
    have e : (⟨⁅qF i, qF (jsF k')⁆, qTable.comm i (jsF k')⟩ : ↥(eSub hv0)) =
        ⟨eta uJ 11 ((commTab.getD i []).getD (jsF k') 0),
          eta_mem_eSub (commTab_mem i i.2 (jsF k') (jsF k').2)⟩ :=
      Subtype.ext (qJ_comm i.2 (jsF k').2)
    rw [e]
    show (Multiplicative.toAdd (cEq.symm ⟨eta uJ 11 ((commTab.getD i []).getD (jsF k') 0),
      eta_mem_eSub (commTab_mem i i.2 (jsF k') (jsF k').2)⟩)) (tsF k') = _
    rw [cEq_symm_eta (commTab_mem i i.2 (jsF k') (jsF k').2)]
    rfl
  simp only [hA]
  exact mMat_inv k k'

noncomputable abbrev Qg : Subgroup J := tabGroup (eSub hv0) qF

theorem v0_comm (k : Fin 3) : ∃ i j, v0 k = ⁅qF i, qF j⁆ := by
  have h10 : ⁅qF 0, qF 10⁆ = eta uJ 11 422 := by
    have e : (commTab.getD ((0 : Fin 12) : ℕ) []).getD ((10 : Fin 12) : ℕ) 0 = 422 := by
      decide +kernel
    have := qJ_comm (i := ((0 : Fin 12) : ℕ)) (j := ((10 : Fin 12) : ℕ)) (Fin.isLt _) (Fin.isLt _)
    rw [e] at this
    exact this
  have h7 : ⁅qF 0, qF 7⁆ = eta uJ 11 553 := by
    have e : (commTab.getD ((0 : Fin 12) : ℕ) []).getD ((7 : Fin 12) : ℕ) 0 = 553 := by
      decide +kernel
    have := qJ_comm (i := ((0 : Fin 12) : ℕ)) (j := ((7 : Fin 12) : ℕ)) (Fin.isLt _) (Fin.isLt _)
    rw [e] at this
    exact this
  have h9 : ⁅qF 0, qF 9⁆ = eta uJ 11 1131 := by
    have e : (commTab.getD ((0 : Fin 12) : ℕ) []).getD ((9 : Fin 12) : ℕ) 0 = 1131 := by
      decide +kernel
    have := qJ_comm (i := ((0 : Fin 12) : ℕ)) (j := ((9 : Fin 12) : ℕ)) (Fin.isLt _) (Fin.isLt _)
    rw [e] at this
    exact this
  fin_cases k <;>
    simp only [v0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · exact ⟨0, 10, h10.symm⟩
  · exact ⟨0, 7, h7.symm⟩
  · exact ⟨0, 9, h9.symm⟩

theorem Q_special : IsSpecial2Group 3 12 ↥Qg := isSpecial2Group hv0 qTable qPairing v0_comm

theorem card_Q : Nat.card ↥Qg = 2 ^ 15 := by
  rw [card_eq qPairing, card_eSub hv0]
  norm_num

theorem mem_V0_of_commute {y : J} (hy : y ∈ Qg) (hc : ∀ j, y * qF j = qF j * y) : y ∈ V0 :=
  eSub_v0 ▸ mem_of_forall_commute qPairing hy hc

theorem V0_le_Q : V0 ≤ Qg := eSub_v0 ▸ le_tabGroup

end CFSG.Quasithin.J4M3
