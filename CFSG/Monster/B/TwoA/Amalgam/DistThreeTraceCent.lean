module

public import CFSG.Monster.B.TwoA.Unitary.Transv
public import Certificates.Certificate3126

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
open CFSG.Monster.B.Co2 (v0 decW qbW qbWBasis wAct_mul wAct_one decW_xor decW_zero)
open CFSG.Monster.B.TwoA.Co2Inv (rowsEnd rowsMul rowsEnd_mul rowsEnd_idRows rowsEnd_qbW
  rowsEnd_decW eq_rowsEnd_of)

@[expose] noncomputable def centU
    (w : List (Fin 17)) : Unitary.Usig :=
  w.foldl (fun g k => g * Unitary.genU k) 1

theorem wAct_genK_eq_rowsEnd
    (k : Fin 17) :
    wAct v0 (Unitary.genK k) = rowsEnd (Unitary.genRows k) :=
  eq_rowsEnd_of (Unitary.wAct_genK_qbW k)

theorem wAct_foldl_centU
    (w : List (Fin 17)) :
    ∀ (g : Unitary.Usig) (A : Array ℕ), wAct v0 (g : Kstab v0) = rowsEnd A →
      wAct v0 ((w.foldl (fun g k => g * Unitary.genU k) g : Unitary.Usig) : Kstab v0) =
        rowsEnd (w.foldl (fun A k => rowsMul A (Unitary.genRows k)) A) := by
  induction w with
  | nil => exact fun _ _ h => h
  | cons k w ih =>
    intro g A h
    refine ih _ _ ?_
    rw [Subgroup.coe_mul, wAct_mul, h, show ((Unitary.genU k : Unitary.Usig) : Kstab v0) =
      Unitary.genK k from rfl, wAct_genK_eq_rowsEnd, rowsEnd_mul]

theorem wAct_centU
    (w : List (Fin 17)) :
    wAct v0 (centU w : Kstab v0) = rowsEnd (centRowsOf w) :=
  wAct_foldl_centU w 1 Co2Inv.idRows (by rw [OneMemClass.coe_one, wAct_one, rowsEnd_idRows])

theorem centCheck_comm : ∀ w ∈ centWords,
    rowsMul (centRowsOf w) (Unitary.genRows 6) = rowsMul (Unitary.genRows 6) (centRowsOf w) :=
  Certificates.certificate3126.1

theorem centCheck_rel :
    (∀ t < 22, centP₁[t]! = relRow centRel₁ t ∧ centP₂[t]! = relRow centRel₂ t) ∧
      Co2.Native.actD 22 centP₁ centW0 = 0 ∧ Co2.Native.actD 22 centP₂ centW0 = 0 ∧
      (∀ t < 22, centP₁[t]! < 2 ^ 22 ∧ centP₂[t]! < 2 ^ 22) ∧
      (∀ i ∈ centRel₁, i < 28) ∧ (∀ i ∈ centRel₂, i < 28) ∧ (∀ i ∈ centSel, i < 28) ∧
      centWords.length = 28 ∧ centSel.length = 22 ∧ centW0 < 2 ^ 22 :=
  Certificates.certificate3126.2.1

theorem centCheck_brute : Nat.all (2 ^ 22) (fun y _ =>
    !(Co2.Native.actD 22 centP₁ y == 0 && Co2.Native.actD 22 centP₂ y == 0) ||
      centCands.contains y) = true :=
  Certificates.certificate3126.2.2.1

theorem centCheck_basis : frows centW0 = Co2Inv.idRows :=
  Certificates.certificate3126.2.2.2.1

theorem centCheck_cases : ∀ y ∈ centCands,
    frows y = Co2Inv.idRows ∨ frows y = Unitary.genRows 6 ∨
      (Co2.Native.actD 22 (frows y) 6144 ≠ 6144 ∧ Co2.Native.actD 22 (frows y) 6144 < 2 ^ 22) ∨
      (Co2.Native.actD 22 (frows y) 60 < 2 ^ 22 ∧
        ∀ j < 2300, Co2.Native.vectors[j]! ≠ Co2.Native.actD 22 (frows y) 60) :=
  Certificates.certificate3126.2.2.2.2

theorem actGo_lt22 (rows : Array ℕ) (v : ℕ) (hr : ∀ i < 22, rows[i]! < 2 ^ 22) :
    ∀ n acc, n ≤ 22 → acc < 2 ^ 22 → CFSG.Monster.VisCert.Native.actGo rows v n acc < 2 ^ 22
  | 0, acc, _, h => h
  | n + 1, acc, hn, h => by
    rw [CFSG.Monster.VisCert.Native.actGo]
    refine actGo_lt22 rows v hr n _ (by omega) ?_
    by_cases hb : v.testBit n = true
    · rw [ite_eq_left hb]
      exact Nat.xor_lt_two_pow h (hr n (by omega))
    · rw [ite_eq_right hb]
      exact h

theorem actD_lt22 {rows : Array ℕ} (hr : ∀ i < 22, rows[i]! < 2 ^ 22) (v : ℕ) :
    Co2.Native.actD 22 rows v < 2 ^ 22 :=
  actGo_lt22 rows v hr 22 0 le_rfl (by norm_num)

theorem exists_decW_eq
    (x : Wv v0) : ∃ c < 2 ^ 22, decW c = x := by
  have : Fintype (Wv v0) := Fintype.ofFinite _
  let f : Fin (2 ^ 22) → Wv v0 := fun c => decW c
  have hf : Function.Injective f := fun a b h => Fin.ext (Co2.decW_injective a.2 b.2 h)
  have hcard : Fintype.card (Fin (2 ^ 22)) = Fintype.card (Wv v0) := by
    rw [Fintype.card_fin, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, Co2.finrank_W]
  obtain ⟨c, hc⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩).2 x
  exact ⟨c, c.2, hc⟩

theorem decW_foldl_xor (l : List ℕ) (f : ℕ → ℕ) :
    ∀ acc, decW (l.foldl (fun a i => a ^^^ f i) acc) =
      decW acc + (l.map fun i => decW (f i)).sum := by
  induction l with
  | nil => intro acc; simp
  | cons i l ih =>
    intro acc
    rw [List.foldl_cons, ih, decW_xor, List.map_cons, List.sum_cons, add_assoc]

@[expose] noncomputable def relEnd (r : List ℕ) : Module.End (ZMod 2) (Wv v0) :=
  (r.map fun i => rowsEnd (centRows i)).sum

theorem relEnd_apply (r : List ℕ) (x : Wv v0) :
    relEnd r x = (r.map fun i => rowsEnd (centRows i) x).sum := by
  rw [relEnd]
  induction r with
  | nil => simp
  | cons i r ih => rw [List.map_cons, List.sum_cons, LinearMap.add_apply, ih, List.map_cons,
      List.sum_cons]

theorem relEnd_eq {r : List ℕ} {P : Array ℕ} (h : ∀ t < 22, P[t]! = relRow r t) :
    relEnd r = rowsEnd P := by
  refine (eq_rowsEnd_of fun t => ?_)
  rw [relEnd_apply, h t t.2, relRow, decW_foldl_xor, decW_zero, zero_add]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [rowsEnd_qbW]

section Commutant

variable
  {z : Unitary.Usig}
  (hz : ∀ i < 28, (z : Kstab v0) * (centU centWords[i]! : Kstab v0) =
    (centU centWords[i]! : Kstab v0) * z)

include hz

theorem wAct_comm_centRows
    {i : ℕ} (hi : i < 28) (x : Wv v0) :
    wAct v0 (z : Kstab v0) (rowsEnd (centRows i) x) = rowsEnd (centRows i) (wAct v0 z x) := by
  have h := congrArg (wAct v0) (hz i hi)
  rw [wAct_mul, wAct_mul, wAct_centU] at h
  exact (LinearMap.congr_fun h x).symm

theorem wAct_comm_relEnd
    {r : List ℕ} (hr : ∀ i ∈ r, i < 28) (x : Wv v0) :
    wAct v0 (z : Kstab v0) (relEnd r x) = relEnd r (wAct v0 z x) := by
  rw [relEnd_apply, relEnd_apply, map_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun i hi => wAct_comm_centRows hz (hr i hi) x

theorem wAct_actD_centW0
    {i : ℕ} (hi : i < 28) {y : ℕ}
    (hy : wAct v0 (z : Kstab v0) (decW centW0) = decW y) :
    wAct v0 (z : Kstab v0) (decW (Co2.Native.actD 22 (centRows i) centW0)) =
      decW (Co2.Native.actD 22 (centRows i) y) := by
  rw [← rowsEnd_decW, wAct_comm_centRows hz hi, hy, rowsEnd_decW]

theorem wAct_eq_rowsEnd_frows
    {y : ℕ}
    (hy : wAct v0 (z : Kstab v0) (decW centW0) = decW y) :
    wAct v0 (z : Kstab v0) = rowsEnd (frows y) := by
  obtain ⟨-, -, -, -, -, -, hsel, -, hlen, -⟩ := centCheck_rel
  have hb : wAct v0 (z : Kstab v0) * rowsEnd (bvecs centW0) = rowsEnd (bvecs y) := by
    refine eq_rowsEnd_of fun s => ?_
    have hs : (s : ℕ) < centSel.length := by rw [hlen]; exact s.2
    have e : ∀ c, (bvecs c)[(s : ℕ)]! = Co2.Native.actD 22 (centRows centSel[(s : ℕ)]!) c := by
      intro c
      have hs' : (s : ℕ) < (bvecs c).size := by simp [bvecs, hs]
      rw [getElem!_pos (bvecs c) (s : ℕ) hs', getElem!_pos centSel (s : ℕ) hs]
      simp [bvecs]
    have hmem : centSel[(s : ℕ)]! ∈ centSel := by
      rw [getElem!_pos centSel (s : ℕ) hs]
      exact List.getElem_mem hs
    rw [Module.End.mul_apply, rowsEnd_qbW, e, e]
    exact wAct_actD_centW0 hz (hsel _ hmem) hy
  calc wAct v0 (z : Kstab v0) = wAct v0 (z : Kstab v0) * (rowsEnd (bvecs centW0) *
        rowsEnd centBinv) := by rw [rowsEnd_mul, ← frows, centCheck_basis, rowsEnd_idRows, mul_one]
    _ = rowsEnd (frows y) := by rw [← mul_assoc, hb, rowsEnd_mul, frows]

theorem mem_centCands
    {y : ℕ} (hy0 : y < 2 ^ 22)
    (hy : wAct v0 (z : Kstab v0) (decW centW0) = decW y) : y ∈ centCands := by
  obtain ⟨hrows, h1, h2, hlt, hr1, hr2, -, -, -, -⟩ := centCheck_rel
  have key : ∀ {r : List ℕ} {P : Array ℕ}, (∀ t < 22, P[t]! = relRow r t) →
      (∀ t < 22, P[t]! < 2 ^ 22) → (∀ i ∈ r, i < 28) → Co2.Native.actD 22 P centW0 = 0 →
      Co2.Native.actD 22 P y = 0 := by
    intro r P hP hPlt hr h0
    have e1 : relEnd r (decW centW0) = 0 := by rw [relEnd_eq hP, rowsEnd_decW, h0, decW_zero]
    have e2 : relEnd r (decW y) = 0 := by
      rw [← hy, ← wAct_comm_relEnd hz hr, e1, map_zero]
    rw [relEnd_eq hP, rowsEnd_decW, ← decW_zero] at e2
    exact Co2.decW_injective (actD_lt22 hPlt y) (by norm_num) e2
  have hy1 := key (fun t ht => (hrows t ht).1) (fun t ht => (hlt t ht).1) hr1 h1
  have hy2 := key (fun t ht => (hrows t ht).2) (fun t ht => (hlt t ht).2) hr2 h2
  have h := centCheck_brute
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at h
  have hy' := h ⟨y, hy0⟩ (List.mem_finRange _)
  simp only [hy1, hy2, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    List.contains_iff_mem] at hy'
  exact hy'

end Commutant

theorem centU_mem_Cr
    {w : List (Fin 17)}
    (hw : w ∈ centWords) :
    (centU w : Kstab v0) ∈ Co2Inv.Cr := by
  rw [Co2Inv.Cr, Subgroup.mem_centralizer_singleton_iff, ← genK_six]
  apply Co2Inv.eq_of_wAct_eq
  rw [wAct_mul, wAct_mul, wAct_centU, wAct_genK_eq_rowsEnd, rowsEnd_mul, rowsEnd_mul,
    centCheck_comm w hw]

theorem eq_one_or_eq_genU_six_of_commute
    {z : Unitary.Usig}
    (hz : ∀ u : Unitary.Usig, Unitary.sigmaAct Rsp (Unitary.phiU u) = Rsp → z * u = u * z) :
    z = 1 ∨ z = Unitary.genU 6 := by
  obtain ⟨-, -, -, -, -, -, -, hlen, -, hw0⟩ := centCheck_rel
  have hz' : ∀ i < 28, (z : Kstab v0) * (centU centWords[i]! : Kstab v0) =
      (centU centWords[i]! : Kstab v0) * z := by
    intro i hi
    have hi' : i < centWords.length := by rw [hlen]; exact hi
    have hmem : centWords[i]! ∈ centWords := by
      rw [getElem!_pos centWords i hi']
      exact List.getElem_mem hi'
    have h := hz (centU centWords[i]!) ((mem_Cr_iff_sigmaAct _).1 (centU_mem_Cr hmem))
    exact congrArg Subtype.val h
  obtain ⟨y, hy0, hy⟩ := exists_decW_eq (wAct v0 (z : Kstab v0) (decW centW0))
  have hX := wAct_eq_rowsEnd_frows hz' hy.symm
  have hcand := mem_centCands hz' hy0 hy.symm
  have hσ : wAct v0 (z : Kstab v0) (decW 6144) = decW 6144 := by
    rw [← Unitary.sigmaW_eq_decW]
    exact Unitary.mem_Usig.1 z.2
  rcases centCheck_cases y hcand with h | h | ⟨hne, hlt⟩ | ⟨hlt, hnot⟩
  · left
    apply Subtype.ext
    apply Co2Inv.eq_of_wAct_eq
    rw [hX, h, rowsEnd_idRows, OneMemClass.coe_one, wAct_one]
  · right
    apply Subtype.ext
    apply Co2Inv.eq_of_wAct_eq
    rw [hX, h, show ((Unitary.genU 6 : Unitary.Usig) : Kstab v0) = Unitary.genK 6 from rfl,
      wAct_genK_eq_rowsEnd]
  · exfalso
    rw [hX, rowsEnd_decW] at hσ
    exact hne (Co2.decW_injective hlt (by norm_num) hσ)
  · exfalso
    have hτ : Unitary.tauW ∈ Unitary.OmegaW := Unitary.tauW_mem_OmegaW
    rw [Unitary.mem_OmegaW_iff_wAct (z : Kstab v0), Unitary.OmegaW_eq] at hτ
    obtain ⟨j, hj⟩ := hτ
    rw [Unitary.tauW, Unitary.o14Tau, hX, rowsEnd_decW] at hj
    have e := Co2.decW_injective (Co2.shortVec_lt j) hlt hj
    exact hnot j j.2 e
end CFSG.Monster.B.TwoA.Amalgam
