module

public import CFSG.Sporadic.SuzRecog.Fibre
public import CFSG.Sporadic.SuzRecog.RigidL2Cert
public import CFSG.Sporadic.Co1Patterson.AmalgamInnerCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.RigidL2

open Subgroup CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson

local notation "ψ" => Coord.psi (t := suzInv 1) (q := qVec)

theorem bilM_e0 (x : Fin 6 → ZMod 2) : bilM x (bitVec 1) = x 1 := by
  obtain ⟨v, hv, rfl⟩ := exists_bitVec x
  rw [bilM_bitVec v hv 1 (by norm_num)]
  revert v
  decide

theorem rigBil_eq_zero_iff : ∀ v < 64, rigBil v = 0 ↔ bitVec v 1 = 0 := by decide

theorem e0_add_self : bitVec 1 + bitVec 1 = 0 := by
  rw [← bitVec_xor, Nat.xor_self, bitVec_zero]

theorem add_e0_add_e0 (x : Fin 6 → ZMod 2) : x + bitVec 1 + bitVec 1 = x := by
  rw [add_assoc, e0_add_self, add_zero]

theorem lm_mul_apply (a b : Lm) (x : Fin 6 → ZMod 2) : (a * b).1 x = a.1 (b.1 x) := rfl

theorem lm_inv_apply_apply (a : Lm) (x : Fin 6 → ZMod 2) : (a⁻¹).1 (a.1 x) = x := by
  rw [← lm_mul_apply, inv_mul_cancel]
  rfl

theorem lm_apply_inv_apply (a : Lm) (x : Fin 6 → ZMod 2) : a.1 ((a⁻¹).1 x) = x := by
  rw [← lm_mul_apply, mul_inv_cancel]
  rfl

theorem apply_one_of_fix {l : Lm} (hl : l.1 (bitVec 1) = bitVec 1) {x : Fin 6 → ZMod 2}
    (hx : x 1 = 0) : l.1 x 1 = 0 := by
  have h := bilM_e0 (l.1 x)
  rw [← hl, bilM_apply, Sec2Omega.polarMinus_apply_of_mem l.2, ← bilM_apply, bilM_e0, hx] at h
  exact h.symm

theorem inv_fix {l : Lm} (hl : l.1 (bitVec 1) = bitVec 1) : (l⁻¹).1 (bitVec 1) = bitVec 1 := by
  conv_lhs => rw [← hl]
  exact lm_inv_apply_apply l _

@[expose] noncomputable def uSub : Subgroup Lm where
  carrier := {l | l.1 (bitVec 1) = bitVec 1 ∧
    ∀ x : Fin 6 → ZMod 2, x 1 = 0 → l.1 x = x ∨ l.1 x = x + bitVec 1}
  mul_mem' {a b} ha hb := by
    refine ⟨by rw [lm_mul_apply, hb.1, ha.1], fun x hx => ?_⟩
    rw [lm_mul_apply]
    rcases hb.2 x hx with h | h
    · rw [h]
      exact ha.2 x hx
    · rw [h, map_add, ha.1]
      rcases ha.2 x hx with h' | h'
      · rw [h']
        exact Or.inr rfl
      · rw [h', add_e0_add_e0]
        exact Or.inl rfl
  one_mem' := ⟨rfl, fun _ _ => Or.inl rfl⟩
  inv_mem' {a} ha := by
    refine ⟨inv_fix ha.1, fun x hx => ?_⟩
    have hy : (a⁻¹).1 x 1 = 0 := apply_one_of_fix (inv_fix ha.1) hx
    rcases ha.2 _ hy with h | h
    · rw [lm_apply_inv_apply] at h
      exact Or.inl h.symm
    · rw [lm_apply_inv_apply] at h
      right
      calc (a⁻¹).1 x = (a⁻¹).1 x + bitVec 1 + bitVec 1 := (add_e0_add_e0 _).symm
        _ = x + bitVec 1 := by rw [← h]

theorem mem_uSub {l : Lm} : l ∈ uSub ↔ l.1 (bitVec 1) = bitVec 1 ∧
    ∀ x : Fin 6 → ZMod 2, x 1 = 0 → l.1 x = x ∨ l.1 x = x + bitVec 1 := Iff.rfl

theorem conj_mem_uSub {l u : Lm} (hl : l.1 (bitVec 1) = bitVec 1) (hu : u ∈ uSub) :
    l * u * l⁻¹ ∈ uSub := by
  refine ⟨by rw [lm_mul_apply, lm_mul_apply, inv_fix hl, hu.1, hl], fun x hx => ?_⟩
  rw [lm_mul_apply, lm_mul_apply]
  rcases hu.2 _ (apply_one_of_fix (inv_fix hl) hx) with h | h
  · rw [h, lm_apply_inv_apply]
    exact Or.inl rfl
  · rw [h, map_add, lm_apply_inv_apply, hl]
    exact Or.inr rfl

theorem inv_mul_mem_uSub {a b : Lm} (ha : a.1 (bitVec 1) = bitVec 1)
    (hb : b.1 (bitVec 1) = bitVec 1)
    (h : ∀ x : Fin 6 → ZMod 2, x 1 = 0 → b.1 x = a.1 x ∨ b.1 x = a.1 x + bitVec 1) :
    a⁻¹ * b ∈ uSub := by
  refine ⟨by rw [lm_mul_apply, hb, inv_fix ha], fun x hx => ?_⟩
  rw [lm_mul_apply]
  rcases h x hx with h' | h'
  · rw [h', lm_inv_apply_apply]
    exact Or.inl rfl
  · rw [h', map_add, lm_inv_apply_apply, inv_fix ha]
    exact Or.inr rfl

theorem bitVec_tab {t : Tab} {l : Lm} (ht : TabRep t (kapL l)) {v : ℕ} (hv : v < 64) :
    bitVec t[v]! = l.1 (bitVec v) := by
  have e : ((kapL l) ⟨v, hv⟩ : Fin 64) = bitEquiv.symm (l.1 (bitVec v)) := kappa_apply _ _
  rw [ht.apply ⟨v, hv⟩, e]
  exact bitEquiv.apply_symm_apply _

theorem tab_lt {t : Tab} {l : Lm} (ht : TabRep t (kapL l)) {v : ℕ} (hv : v < 64) : t[v]! < 64 := by
  rw [ht.apply ⟨v, hv⟩]
  exact Fin.isLt _

theorem tab_eq_iff {t : Tab} {l : Lm} (ht : TabRep t (kapL l)) {v m : ℕ} (hv : v < 64)
    (hm : m < 64) : t[v]! = m ↔ l.1 (bitVec v) = bitVec m :=
  ⟨fun h => by rw [← bitVec_tab ht hv, h],
    fun h => bitVec_inj _ (tab_lt ht hv) _ hm (by rw [bitVec_tab ht hv, h])⟩

theorem rigUTest_iff {t : Tab} {l : Lm} (ht : TabRep t (kapL l)) :
    rigUTest t = true ↔ l ∈ uSub := by
  rw [rigUTest, Bool.and_eq_true, beq_iff_eq, allLt_iff,
    tab_eq_iff ht (by norm_num) (by norm_num), mem_uSub]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h v hv => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := exists_bitVec x
    have h1 := h v hv
    have hb : rigBil v = 0 := (rigBil_eq_zero_iff v hv).2 hx
    simp only [hb, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact Or.inl ((tab_eq_iff ht hv hv).1 h1)
    · right
      rw [(tab_eq_iff ht hv (xor_lt hv (by norm_num))).1 h1, bitVec_xor]
  · have key : rigBil v ≠ 0 ∨ t[v]! = v ∨ t[v]! = v ^^^ 1 := by
      by_cases hb : rigBil v = 0
      · right
        rcases h (bitVec v) ((rigBil_eq_zero_iff v hv).1 hb) with h1 | h1
        · exact Or.inl ((tab_eq_iff ht hv hv).2 h1)
        · refine Or.inr ((tab_eq_iff ht hv (xor_lt hv (by norm_num))).2 ?_)
          rw [bitVec_xor]
          exact h1
      · exact Or.inl hb
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    rcases key with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h1

theorem rigAgree_spec {t m : Tab} {a b : Lm} (ht : TabRep t (kapL b)) (hm : TabRep m (kapL a))
    (h : rigAgree t m = true) {x : Fin 6 → ZMod 2} (hx : x 1 = 0) :
    b.1 x = a.1 x ∨ b.1 x = a.1 x + bitVec 1 := by
  obtain ⟨v, hv, rfl⟩ := exists_bitVec x
  have h1 := allLt_iff.1 h v hv
  have hb : rigBil v = 0 := (rigBil_eq_zero_iff v hv).2 hx
  simp only [hb, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  have hmv := tab_lt hm hv
  rw [← bitVec_tab ht hv, ← bitVec_tab hm hv]
  rcases h1 with h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1, bitVec_xor])

theorem rigComm_iff {a b : Array ℕ} {X Y : Equiv.Perm (Fin 1782)} (ha : Rep 1782 a X)
    (hb : Rep 1782 b Y) : rigComm a b = true ↔ X * Y = Y * X := by
  rw [rigComm]
  refine allLt_eq_iff fun z => ?_
  rw [beq_iff_eq, hb z, ha (Y z), ha z, hb (X z)]
  rfl

theorem rigEqComp_iff {a p q : Array ℕ} {X P Q : Equiv.Perm (Fin 1782)} (ha : Rep 1782 a X)
    (hp : Rep 1782 p P) (hq : Rep 1782 q Q) : rigEqComp a p q = true ↔ X = P * Q := by
  rw [rigEqComp]
  refine allLt_eq_iff fun z => ?_
  rw [beq_iff_eq, ha z, hq z, hp (Q z)]
  rfl

section Tables

theorem rigCommV_iff {a b : Array ℕ} {X Y : Equiv.Perm (Fin 1782)} (ha : Rep 1782 a X)
    (hb : Rep 1782 b Y) : rigCommV a b = true ↔ ∃ i < 4, X * Y = qE i * (Y * X) := by
  rw [rigCommV, anyBelow_eq_true]
  refine exists_congr fun i => and_congr_right fun hi => allLt_eq_iff fun z => ?_
  rw [beq_iff_eq, hb z, ha (Y z), ha z, hb (X z), rep_qE (by omega) (Y (X z))]
  rfl

theorem rigModV_iff {a s : Array ℕ} {X S : Equiv.Perm (Fin 1782)} (ha : Rep 1782 a X)
    (hs : Rep 1782 s S) : rigModV a s = true ↔ ∃ i < 4, X = S * qE i := by
  rw [rigModV, anyBelow_eq_true]
  exact exists_congr fun i => and_congr_right fun hi => rigEqComp_iff ha hs (rep_qE (by omega))

theorem rigInV_iff {a : Array ℕ} {X : Equiv.Perm (Fin 1782)} (ha : Rep 1782 a X) :
    rigInV a = true ↔ ∃ i < 4, X = qE i := by
  rw [rigInV, anyBelow_eq_true]
  exact exists_congr fun i => and_congr_right fun hi => eqA_iff ha (rep_qE (by omega))

end Tables

theorem rigUWords_lt (c : ℕ) : ∀ k ∈ rigUWords.getD c [], k < 10 := by
  by_cases hc : c < 16
  · interval_cases c <;> decide
  · rw [List.getD_eq_default _ _ (by simp [rigUWords]; omega)]
    simp

theorem rigRTab_eq {c j : ℕ} (hc : c < 16) (hj : j < 128) :
    rigRTab c j = compA 1782 (rigUTab c) qElts[j]! := by
  rw [rigRTab, rigRTabs, getElem!_ofFn' _ hc, getElem!_ofFn' _ hj]

section Elements

noncomputable abbrev K0 : Subgroup ↥(invE 1) := centralizer ({w0C} : Set ↥(invE 1))

theorem mem_K0 {k : ↥(invE 1)} : k ∈ K0 ↔ k * w0C = w0C * k := mem_centralizer_singleton_iff

theorem coe_mem_K0 {k : ↥(invE 1)} : k ∈ K0 ↔ (k : Equiv.Perm (Fin 1782)) * w0P = w0P * k := by
  rw [mem_K0, ← Subtype.coe_inj, Subgroup.coe_mul, Subgroup.coe_mul]
  rfl

theorem phi0_e0 {k : ↥(invE 1)} (hk : k ∈ K0) : (phi0 k).1 (bitVec 1) = bitVec 1 := by
  rw [coe_phi0, ← psi_w0P, ← psi_conj k w0P_mem]
  congr 1
  rw [coe_mem_K0.1 hk, mul_inv_cancel_right]

theorem t1C_mul_self : t1C * t1C = 1 := Subtype.ext (suzInv_sq (by norm_num))

theorem w0C_mul_self : w0C * w0C = 1 := by
  apply Subtype.ext
  have h := coord_qVec.mul_self_eq (v := 1) (by norm_num) 0
  rw [pow_zero, mul_one, show qMinusBit 1 = 0 by decide, pow_zero] at h
  exact h

theorem t1C_comm_w0C : t1C * w0C = w0C * t1C := Subtype.ext (comm_t1 w0C).symm

theorem t1C_comm (g : ↥(invE 1)) : t1C * g = g * t1C := Subtype.ext (comm_t1 g).symm

@[expose] noncomputable def vSub : Subgroup ↥(invE 1) :=
  fourGroup t1C_mul_self w0C_mul_self t1C_comm_w0C

theorem mem_vSub {v : ↥(invE 1)} : v ∈ vSub ↔ v = 1 ∨ v = t1C ∨ v = w0C ∨ v = w0C * t1C :=
  mem_fourGroup _ _ _

@[expose] noncomputable def qEC (j : ℕ) : ↥(invE 1) :=
  ⟨qE j, mul_mem (qVec_mem_invE _) (pow_mem suzInv_mem_invE _)⟩

theorem qEC_mem_vSub {i : ℕ} (hi : i < 4) : qEC i ∈ vSub := by
  rw [mem_vSub]
  have hq0 : qVec 0 = 1 := coord_qVec.q_zero
  interval_cases i
  · left
    apply Subtype.ext
    change qVec 0 * suzInv 1 ^ 0 = 1
    rw [hq0, pow_zero, mul_one]
  · right; left
    apply Subtype.ext
    change qVec 0 * suzInv 1 ^ 1 = suzInv 1
    rw [hq0, pow_one, one_mul]
  · right; right; left
    apply Subtype.ext
    change qVec 1 * suzInv 1 ^ 0 = qVec 1
    rw [pow_zero, mul_one]
  · right; right; right
    apply Subtype.ext
    change qVec 1 * suzInv 1 ^ 1 = qVec 1 * suzInv 1
    rw [pow_one]

theorem exists_qEC_of_mem_vSub {v : ↥(invE 1)} (hv : v ∈ vSub) : ∃ i < 4, v = qEC i := by
  have e : ∀ i < 4, ∀ v, qEC i = v → ∃ i < 4, v = qEC i := fun i hi v h => ⟨i, hi, h.symm⟩
  have hq0 : qVec 0 = 1 := coord_qVec.q_zero
  rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
  · refine e 0 (by norm_num) _ (Subtype.ext ?_)
    change qVec 0 * suzInv 1 ^ 0 = 1
    rw [hq0, pow_zero, mul_one]
  · refine e 1 (by norm_num) _ (Subtype.ext ?_)
    change qVec 0 * suzInv 1 ^ 1 = suzInv 1
    rw [hq0, pow_one, one_mul]
  · refine e 2 (by norm_num) _ (Subtype.ext ?_)
    change qVec 1 * suzInv 1 ^ 0 = qVec 1
    rw [pow_zero, mul_one]
  · refine e 3 (by norm_num) _ (Subtype.ext ?_)
    change qVec 1 * suzInv 1 ^ 1 = qVec 1 * suzInv 1
    rw [pow_one]

theorem mem_vSub_iff_coe {v : ↥(invE 1)} :
    v ∈ vSub ↔ ∃ i < 4, (v : Equiv.Perm (Fin 1782)) = qE i := by
  refine ⟨fun hv => ?_, fun ⟨i, hi, h⟩ => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := exists_qEC_of_mem_vSub hv
    exact ⟨i, hi, rfl⟩
  · have e : v = qEC i := Subtype.ext h
    rw [e]
    exact qEC_mem_vSub hi

theorem vSub_central : ∀ v ∈ vSub, ∀ g ∈ K0, v * g = g * v := by
  intro v hv g hg
  rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact t1C_comm g
  · exact (mem_K0.1 hg).symm
  · rw [mul_assoc, t1C_comm g, ← mul_assoc, ← mem_K0.1 hg, mul_assoc]

theorem vSub_mul_self : ∀ v ∈ vSub, v * v = 1 := by
  intro v hv
  rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact t1C_mul_self
  · exact w0C_mul_self
  · calc w0C * t1C * (w0C * t1C) = w0C * (t1C * w0C) * t1C := by group
      _ = w0C * (w0C * t1C) * t1C := by rw [t1C_comm_w0C]
      _ = 1 := by rw [← mul_assoc, w0C_mul_self, one_mul, t1C_mul_self]

@[expose] noncomputable def uHat (c : ℕ) : ↥(invE 1) :=
  if rigUFix.getD c 0 = 1 then
    ⟨qVec 2, qVec_mem_invE 2⟩ * wElt (rigUWords.getD c []) (rigUWords_lt c)
  else wElt (rigUWords.getD c []) (rigUWords_lt c)

theorem rep_uHat (c : ℕ) : Rep 1782 (rigUTab c) (uHat c : Equiv.Perm (Fin 1782)) := by
  unfold rigUTab uHat
  split_ifs with h1 h2 h2
  · exact rep_compA (rep_qProds (v := 2) (by norm_num)) (rep_cWord (rigUWords_lt c))
  · exact absurd (beq_iff_eq.1 h1) h2
  · exact absurd (beq_iff_eq.2 h2) h1
  · exact rep_cWord (rigUWords_lt c)

theorem phi0_uHat (c : ℕ) :
    phi0 (uHat c) = phi0 (wElt (rigUWords.getD c []) (rigUWords_lt c)) := by
  unfold uHat
  split_ifs
  · rw [map_mul, (phi0_eq_one_iff ⟨qVec 2, qVec_mem_invE 2⟩).2 (coord_qVec.q_mem (v := 2)
      (by norm_num)), one_mul]
  · rfl

theorem uHat_zero : uHat 0 = 1 := by
  unfold uHat
  rw [ite_eq_right (by decide)]
  rfl

@[expose] noncomputable def rElt (c j : ℕ) : ↥(invE 1) := uHat c * qEC j

theorem rep_rElt {c j : ℕ} (hc : c < 16) (hj : j < 128) :
    Rep 1782 (rigRTab c j) (rElt c j : Equiv.Perm (Fin 1782)) := by
  rw [rigRTab_eq hc hj]
  exact rep_compA (rep_uHat c) (rep_qE hj)

theorem phi0_rElt {c j : ℕ} (hj : j < 128) : phi0 (rElt c j) = phi0 (uHat c) := by
  rw [rElt, map_mul, (phi0_eq_one_iff (qEC j)).2 (qE_mem hj), mul_one]

@[expose] noncomputable def R0 : Subgroup ↥(invE 1) := K0 ⊓ uSub.comap phi0

theorem conj_mem_R0 {k r : ↥(invE 1)} (hk : k ∈ K0) (hr : r ∈ R0) : k * r * k⁻¹ ∈ R0 := by
  refine ⟨K0.mul_mem (K0.mul_mem hk hr.1) (K0.inv_mem hk), ?_⟩
  change phi0 (k * r * k⁻¹) ∈ uSub
  rw [map_mul, map_mul, map_inv]
  exact conj_mem_uSub (phi0_e0 hk) hr.2

theorem vSub_le_R0 : vSub ≤ R0 := by
  intro v hv
  refine ⟨?_, ?_⟩
  · rcases mem_vSub.1 hv with rfl | rfl | rfl | rfl
    · exact K0.one_mem
    · exact mem_K0.2 t1C_comm_w0C
    · exact mem_K0.2 rfl
    · exact K0.mul_mem (mem_K0.2 rfl) (mem_K0.2 t1C_comm_w0C)
  · obtain ⟨i, hi, rfl⟩ := exists_qEC_of_mem_vSub hv
    change phi0 (qEC i) ∈ uSub
    rw [(phi0_eq_one_iff _).2 (qE_mem (by omega))]
    exact uSub.one_mem

theorem exists_eq_rElt {r : ↥(invE 1)} (hr : phi0 r ∈ uSub) :
    ∃ c < 16, ∃ j < 128, r = rElt c j := by
  have hmem : kapL (phi0 r) ∈ rho1.range.map kappa := ⟨rho1 r, ⟨r, rfl⟩, (kapL_phi0 r).symm⟩
  obtain ⟨t, ht, hrep⟩ := kappa_rho1_enumerates.complete _ hmem
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  have hU : rigUTest matEnum.tabs[i]! = true := (rigUTest_iff hrep).2 hr
  have hc := allLt_iff.1 rigUComplete_check i (by rwa [matEnum_size] at hi)
  rw [hU, Bool.not_true, Bool.false_or, anyBelow_eq_true] at hc
  obtain ⟨c, hc16, hce⟩ := hc
  rw [beq_iff_eq] at hce
  rw [hce] at hrep
  have h2 : TabRep (matWord (rigUWords.getD c []))
      (kapL (phi0 (wElt (rigUWords.getD c []) (rigUWords_lt c)))) := by
    rw [kapL_phi0]
    exact tabRep_matWord _
  have h3 : phi0 r = phi0 (uHat c) := by
    rw [phi0_uHat]
    exact kapL_injective (hrep.perm_eq h2)
  have hk : phi0 ((uHat c)⁻¹ * r) = 1 := by rw [map_mul, map_inv, ← h3, inv_mul_cancel]
  obtain ⟨v, hv, a, ha, he⟩ := coord_qVec.mem_Q_iff.mp ((phi0_eq_one_iff _).1 hk)
  refine ⟨c, hc16, 2 * v + a, by omega, Subtype.ext ?_⟩
  have e1 : qE (2 * v + a) = qVec v * suzInv 1 ^ a := by
    rw [qE, show (2 * v + a) / 2 = v by omega, show (2 * v + a) % 2 = a by omega]
  change (r : Equiv.Perm (Fin 1782)) = (uHat c : Equiv.Perm (Fin 1782)) * qE (2 * v + a)
  rw [e1, ← he]
  simp

theorem phi0_uHat_mem {c : ℕ} (hc : c < 16) :
    phi0 (uHat c) ∈ uSub := by
  have h := rigLift_check
  rw [rigLiftOK, List.all_eq_true] at h
  have h' := h c (List.mem_range.2 hc)
  simp only [Bool.and_eq_true] at h'
  have hrep : TabRep (matWord (rigUWords.getD c []))
      (kapL (phi0 (wElt (rigUWords.getD c []) (rigUWords_lt c)))) := by
    rw [kapL_phi0]
    exact tabRep_matWord _
  rw [phi0_uHat]
  exact (rigUTest_iff hrep).1 h'.1.2

theorem rElt_mem_R0 {c j : ℕ} (hc : c < 16) (hj : j < 128)
    (h : rigComm (rigRTab c j) w0Tab = true) : rElt c j ∈ R0 :=
  ⟨coe_mem_K0.2 ((rigComm_iff (rep_rElt hc hj) rep_w0P).1 h),
    by change phi0 (rElt c j) ∈ uSub; rw [phi0_rElt hj]; exact phi0_uHat_mem hc⟩

theorem exists_of_mem_R0 {r : ↥(invE 1)} (hr : r ∈ R0) :
    ∃ c < 16, ∃ j < 128, r = rElt c j ∧ rigComm (rigRTab c j) w0Tab = true := by
  obtain ⟨c, hc, j, hj, rfl⟩ := exists_eq_rElt hr.2
  exact ⟨c, hc, j, hj, rfl, (rigComm_iff (rep_rElt hc hj) rep_w0P).2 (coe_mem_K0.1 hr.1)⟩

theorem R0_le_K0 : R0 ≤ K0 := inf_le_left

end Elements

theorem wPerm_append (a b : List ℕ) : wPerm (a ++ b) = wPerm a * wPerm b := by
  simp only [wPerm, List.map_append, List.prod_append]

theorem rigX1_lt : ∀ k ∈ rigX1, k < 10 := by decide

theorem rigX2_lt : ∀ k ∈ rigX2, k < 10 := by decide

theorem gen_spec {i : ℕ} (hi : i < 8) :
    ∃ s u c j, rigGens.getD i (0, [], 0, 0) = (s, u, c, j) ∧ s < 2 ∧ c < 16 ∧ j < 128 ∧
      (∀ k ∈ u, k < 10) ∧ rigComm (cWord u) w0Tab = true ∧ rigComm (rigRTab c j) w0Tab = true ∧
      allLt 1782 (fun z => (cWord u)[(rigSTab s)[z]!]! == (rigRTab c j)[(cWord u)[z]!]!) =
        true := by
  have h := rigGen_check
  rw [rigGenOK, List.all_eq_true] at h
  have h' := h i (List.mem_range.2 hi)
  rcases e : rigGens.getD i (0, [], 0, 0) with ⟨s, u, c, j⟩
  rw [e] at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨hs, hc⟩, hj⟩, hu⟩, h1⟩, h2⟩, h3⟩ := h'
  exact ⟨s, u, c, j, rfl, hs, hc, hj, hu, h1, h2, h3⟩

theorem seed_spec {s : ℕ} (hs : s < 2) :
    ∃ c j, rigSeeds.getD s (0, 0) = (c, j) ∧ c < 16 ∧ j < 128 ∧
      rigComm (rigRTab c j) w0Tab = true ∧ rigInV (compA 1782 (rigSTab s) (rigSTab s)) = true ∧
      (∀ g ∈ rigGam.getD s [], (∀ k ∈ g, k < 10) ∧ rigComm (cWord g) w0Tab = true ∧
        rigCommV (cWord g) (rigSTab s) = true) ∧
      ∀ c' < 16, ∀ j' < 128, rigComm (rigRTab c' j') w0Tab = true →
        (∀ g ∈ rigGam.getD s [], rigCommV (cWord g) (rigRTab c' j') = true) →
        eqA 1782 (compA 1782 (rigRTab c' j') (rigRTab c' j'))
          (compA 1782 (rigSTab s) (rigSTab s)) = true →
        rigModV (rigRTab c' j') (rigSTab s) = true := by
  have h := rigStab_check
  rw [rigStabOK, List.all_eq_true] at h
  have h' := h s (List.mem_range.2 hs)
  rcases e : rigSeeds.getD s (0, 0) with ⟨c, j⟩
  rw [e] at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hc, hj⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h'
  refine ⟨c, j, rfl, hc, hj, h1, h2, fun g hg => ⟨(h3 g hg).1.1, (h3 g hg).1.2, (h3 g hg).2⟩,
    fun c' hc' j' hj' ha hb hd => ?_⟩
  have h5 := allLt_iff.1 (h4 c' (List.mem_range.2 hc')) j' hj'
  have hB : ((rigGam.getD s []).all fun g => rigCommV (cWord g) (rigRTab c' j')) = true :=
    List.all_eq_true.2 hb
  rw [ha, hB, hd] at h5
  simpa only [Bool.not_true, Bool.false_or] using h5

theorem rigExpand_lt (u : List ℕ) : ∀ k ∈ rigExpand u, k < 10 := by
  intro k hk
  rw [rigExpand, List.mem_flatMap] at hk
  obtain ⟨l, -, hl⟩ := hk
  split_ifs at hl
  · exact rigX1_lt k hl
  · exact rigX2_lt k hl

section Gens

@[expose] noncomputable def tElt (i : ℕ) : ↥(invE 1) :=
  match rigGens.getD i (0, [], 0, 0) with
  | (_, _, c, j) => rElt c j

theorem tElt_eq {i s c j : ℕ} {u : List ℕ} (e : rigGens.getD i (0, [], 0, 0) = (s, u, c, j)) :
    tElt i = rElt c j := by
  simp only [tElt, e]

theorem rep_tElt {i : ℕ} (hi : i < 8) :
    Rep 1782 (rigTTab i) (tElt i : Equiv.Perm (Fin 1782)) := by
  obtain ⟨s, u, c, j, e, -, hc, hj, -⟩ := gen_spec hi
  have e1 : rigTTab i = rigRTab c j := by simp only [rigTTab, e]
  rw [e1, tElt_eq e]
  exact rep_rElt hc hj

theorem tElt_mem_R0 {i : ℕ} (hi : i < 8) : tElt i ∈ R0 := by
  obtain ⟨s, u, c, j, e, -, hc, hj, -, -, h2, -⟩ := gen_spec hi
  rw [tElt_eq e]
  exact rElt_mem_R0 hc hj h2

@[expose] noncomputable def tProd (m : ℕ) : ↥(invE 1) :=
  (List.range 8).foldl (fun acc i => if m.testBit i then acc * tElt i else acc) 1

theorem rep_tProd {m : ℕ} (hm : m < 256) :
    Rep 1782 rigProdTabs[m]! (tProd m : Equiv.Perm (Fin 1782)) := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, i < 8) → ∀ (a : Array ℕ) (A : ↥(invE 1)),
      Rep 1782 a (A : Equiv.Perm (Fin 1782)) →
      Rep 1782 (l.foldl (fun acc i => if m.testBit i then compA 1782 acc (rigTTab i) else acc) a)
        ((l.foldl (fun acc i => if m.testBit i then acc * tElt i else acc) A : ↥(invE 1)) :
          Equiv.Perm (Fin 1782)) := by
    intro l
    induction l with
    | nil => exact fun _ a A h => h
    | cons i l ih =>
      intro hl a A h
      simp only [List.foldl_cons]
      refine ih (fun k hk => hl k (List.mem_cons_of_mem i hk)) _ _ ?_
      rcases hb : m.testBit i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact h
      · simp only [↓reduceIte]
        exact rep_compA h (rep_tElt (hl i List.mem_cons_self))
  rw [rigProdTabs, getElem!_ofFn' _ hm]
  exact key _ (fun i hi => List.mem_range.1 hi) _ _ rep_idA

theorem tProd_mem {F : Subgroup ↥(invE 1)} (hT : ∀ i < 8, tElt i ∈ F) (m : ℕ) : tProd m ∈ F := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, i < 8) → ∀ A ∈ F,
      l.foldl (fun acc i => if m.testBit i then acc * tElt i else acc) A ∈ F := by
    intro l
    induction l with
    | nil => exact fun _ A h => h
    | cons i l ih =>
      intro hl A h
      simp only [List.foldl_cons]
      refine ih (fun k hk => hl k (List.mem_cons_of_mem i hk)) _ ?_
      split_ifs
      · exact F.mul_mem h (hT i (hl i List.mem_cons_self))
      · exact h
  exact key _ (fun i hi => List.mem_range.1 hi) 1 F.one_mem

theorem R0_le_of {F : Subgroup ↥(invE 1)} (hV : vSub ≤ F) (hT : ∀ i < 8, tElt i ∈ F) :
    R0 ≤ F := by
  intro r hr
  obtain ⟨c, hc, j, hj, rfl, hcomm⟩ := exists_of_mem_R0 hr
  have h0 := rigDecomp_check
  rw [rigDecompOK, List.all_eq_true] at h0
  have h1 := allLt_iff.1 (h0 c (List.mem_range.2 hc)) j hj
  rw [hcomm, Bool.not_true, Bool.false_or, anyBelow_eq_true] at h1
  obtain ⟨m, hm, h2⟩ := h1
  obtain ⟨i, hi, he⟩ := anyBelow_eq_true.1 h2
  have e : rElt c j = tProd m * qEC i :=
    Subtype.ext ((rigEqComp_iff (rep_rElt hc hj) (rep_tProd hm) (rep_qE (by omega))).1 he)
  rw [e]
  exact F.mul_mem (tProd_mem hT m) (hV (qEC_mem_vSub hi))

theorem vSub_le_vCent {r : ↥(invE 1)} (hr : r ∈ K0) : vSub ≤ vCent vSub_central r :=
  fun v hv => by
    refine ⟨R0_le_K0 (vSub_le_R0 hv), ?_⟩
    rw [← vSub_central v hv r hr, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem comm_tElt {i k : ℕ} (hi : i < 8) (hk : k < 8) :
    tElt i * tElt k * (tElt i)⁻¹ * (tElt k)⁻¹ ∈ vSub := by
  have h := rigComm_check
  rw [rigCommOK, List.all_eq_true] at h
  have h' := List.all_eq_true.1 (h i (List.mem_range.2 hi)) k (List.mem_range.2 hk)
  obtain ⟨v, hv, e⟩ := (rigCommV_iff (rep_tElt hi) (rep_tElt hk)).1 h'
  have e' : tElt i * tElt k = qEC v * (tElt k * tElt i) := Subtype.ext e
  rw [e', show qEC v * (tElt k * tElt i) * (tElt i)⁻¹ * (tElt k)⁻¹ = qEC v by group]
  exact qEC_mem_vSub hv

theorem mem_vSub_of_comm {r : ↥(invE 1)} (hr : r ∈ R0) (h : ∀ i < 8, r * tElt i = tElt i * r) :
    r ∈ vSub := by
  obtain ⟨c, hc, j, hj, rfl, hcomm⟩ := exists_of_mem_R0 hr
  have h0 := rigCenter_check
  rw [rigCenterOK, List.all_eq_true] at h0
  have h1 := allLt_iff.1 (h0 c (List.mem_range.2 hc)) j hj
  have h2 : ((List.range 8).all fun i => rigComm (rigRTab c j) (rigTTab i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    exact (rigComm_iff (rep_rElt hc hj) (rep_tElt hi')).2 (congrArg Subtype.val (h i hi'))
  rw [hcomm, h2] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨rfl, hj4⟩ := h1
  rw [rElt, uHat_zero, one_mul]
  exact qEC_mem_vSub hj4

theorem coreData : CoreData K0 R0 vSub where
  le_K := R0_le_K0
  le_R := vSub_le_R0
  central := vSub_central
  mul_self := vSub_mul_self
  conj_mem := fun _ hk _ hr => conj_mem_R0 hk hr
  comm_mem := by
    have hsymm : ∀ r s : ↥(invE 1), r * s * r⁻¹ * s⁻¹ ∈ vSub → s * r * s⁻¹ * r⁻¹ ∈ vSub := by
      intro r s h
      rw [show s * r * s⁻¹ * r⁻¹ = (r * s * r⁻¹ * s⁻¹)⁻¹ by group]
      exact inv_mem h
    have ht : ∀ i < 8, R0 ≤ vCent vSub_central (tElt i) := fun i hi =>
      R0_le_of (vSub_le_vCent (R0_le_K0 (tElt_mem_R0 hi))) fun k hk =>
        ⟨R0_le_K0 (tElt_mem_R0 hk), comm_tElt hi hk⟩
    intro r hr s hs
    exact (R0_le_of (vSub_le_vCent (R0_le_K0 hr)) (fun j hj =>
      ⟨R0_le_K0 (tElt_mem_R0 hj), hsymm _ _ (ht j hj hr).2⟩) hs).2
  mem_of_comm := fun r hr h => mem_vSub_of_comm hr fun i hi => h _ (tElt_mem_R0 hi)

@[expose] noncomputable def sElt (s : ℕ) : ↥(invE 1) :=
  match rigSeeds.getD s (0, 0) with
  | (c, j) => rElt c j

theorem sElt_eq {s c j : ℕ} (e : rigSeeds.getD s (0, 0) = (c, j)) : sElt s = rElt c j := by
  simp only [sElt, e]

theorem rep_sElt {s : ℕ} (hs : s < 2) :
    Rep 1782 (rigSTab s) (sElt s : Equiv.Perm (Fin 1782)) := by
  obtain ⟨c, j, e, hc, hj, -⟩ := seed_spec hs
  have e1 : rigSTab s = rigRTab c j := by simp only [rigSTab, e]
  rw [e1, sElt_eq e]
  exact rep_rElt hc hj

theorem sElt_mem_R0 {s : ℕ} (hs : s < 2) : sElt s ∈ R0 := by
  obtain ⟨c, j, e, hc, hj, h1, -⟩ := seed_spec hs
  rw [sElt_eq e]
  exact rElt_mem_R0 hc hj h1

theorem sElt_mul_self {s : ℕ} (hs : s < 2) : sElt s * sElt s ∈ vSub := by
  obtain ⟨c, j, e, -, -, -, h2, -⟩ := seed_spec hs
  obtain ⟨i, hi, he⟩ := (rigInV_iff (rep_compA (rep_sElt hs) (rep_sElt hs))).1 h2
  exact mem_vSub_iff_coe.2 ⟨i, hi, he⟩

@[expose] noncomputable def gamSet (s : ℕ) : Set ↥(invE 1) :=
  {g | ∃ w ∈ rigGam.getD s [], ∃ hw : ∀ k ∈ w, k < 10, g = wElt w hw}

theorem comm_eq_of {g r : ↥(invE 1)} {i : ℕ}
    (e : (g : Equiv.Perm (Fin 1782)) * r = qE i * (r * g)) :
    g * r * g⁻¹ * r⁻¹ = qEC i := by
  have e' : g * r = qEC i * (r * g) := Subtype.ext e
  rw [e']
  group

theorem stab_spec {s : ℕ} (hs : s < 2) : gamSet s ⊆ K0 ∧
    (∀ g ∈ gamSet s, g * sElt s * g⁻¹ * (sElt s)⁻¹ ∈ vSub) ∧
    ∀ r ∈ R0, (∀ g ∈ gamSet s, g * r * g⁻¹ * r⁻¹ ∈ vSub) → r * r = sElt s * sElt s →
      r * (sElt s)⁻¹ ∈ vSub := by
  obtain ⟨c, j, e, hc, hj, -, -, h3, h4⟩ := seed_spec hs
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨w, hw, hw', rfl⟩
    exact coe_mem_K0.2 ((rigComm_iff (rep_cWord hw') rep_w0P).1 (h3 w hw).2.1)
  · rintro g ⟨w, hw, hw', rfl⟩
    obtain ⟨i, hi, he⟩ := (rigCommV_iff (rep_cWord hw') (rep_sElt hs)).1 (h3 w hw).2.2
    rw [comm_eq_of he]
    exact qEC_mem_vSub hi
  · intro r hr hfix hsq
    obtain ⟨c', hc', j', hj', rfl, hcomm⟩ := exists_of_mem_R0 hr
    have hg : ∀ w ∈ rigGam.getD s [], rigCommV (cWord w) (rigRTab c' j') = true := by
      intro w hw
      have hw' := (h3 w hw).1
      obtain ⟨i, hi, hv⟩ := exists_qEC_of_mem_vSub (hfix _ ⟨w, hw, hw', rfl⟩)
      refine (rigCommV_iff (rep_cWord hw') (rep_rElt hc' hj')).2 ⟨i, hi, ?_⟩
      have e2 : wElt w hw' * rElt c' j' = qEC i * (rElt c' j' * wElt w hw') := by
        rw [← hv]
        group
      exact congrArg Subtype.val e2
    have hd : eqA 1782 (compA 1782 (rigRTab c' j') (rigRTab c' j'))
        (compA 1782 (rigSTab s) (rigSTab s)) = true :=
      (eqA_iff (rep_compA (rep_rElt hc' hj') (rep_rElt hc' hj'))
        (rep_compA (rep_sElt hs) (rep_sElt hs))).2 (congrArg Subtype.val hsq)
    obtain ⟨i, hi, he⟩ := (rigModV_iff (rep_rElt hc' hj') (rep_sElt hs)).1
      (h4 c' hc' j' hj' hcomm hg hd)
    have e3 : rElt c' j' = sElt s * qEC i := Subtype.ext he
    have hc3 : qEC i * sElt s = sElt s * qEC i :=
      vSub_central _ (qEC_mem_vSub hi) _ (R0_le_K0 (sElt_mem_R0 hs))
    rw [e3, show sElt s * qEC i * (sElt s)⁻¹ = qEC i * sElt s * (sElt s)⁻¹ by rw [hc3],
      mul_inv_cancel_right]
    exact qEC_mem_vSub hi

theorem R0_le_of_seeds {F : Subgroup ↥(invE 1)} (hV : vSub ≤ F) (hS0 : sElt 0 ∈ F)
    (hS1 : sElt 1 ∈ F) (hinv : ∀ k ∈ K0, ∀ r ∈ F, r ∈ R0 → k * r * k⁻¹ ∈ F) : R0 ≤ F := by
  refine R0_le_of hV fun i hi => ?_
  obtain ⟨s, u, c, j, e, hs, hc, hj, hu, h1, -, h3⟩ := gen_spec hi
  have hU : wElt u hu ∈ K0 := coe_mem_K0.2 ((rigComm_iff (rep_cWord hu) rep_w0P).1 h1)
  have he : (wElt u hu : Equiv.Perm (Fin 1782)) * sElt s = rElt c j * wElt u hu := by
    refine (allLt_eq_iff fun z => ?_).1 h3
    rw [beq_iff_eq, (rep_sElt hs) z, (rep_cWord hu) ((sElt s : Equiv.Perm (Fin 1782)) z),
      (rep_cWord hu) z, (rep_rElt hc hj) (wPerm u z)]
    rfl
  have e2 : tElt i = wElt u hu * sElt s * (wElt u hu)⁻¹ := by
    rw [tElt_eq e]
    have e3 : wElt u hu * sElt s = rElt c j * wElt u hu := Subtype.ext he
    rw [e3, mul_inv_cancel_right]
  have hsF : sElt s ∈ F := by
    interval_cases s
    · exact hS0
    · exact hS1
  rw [e2]
  exact hinv _ hU _ hsF (sElt_mem_R0 hs)

@[expose] noncomputable def x1E : ↥(invE 1) := wElt rigX1 rigX1_lt

@[expose] noncomputable def x2E : ↥(invE 1) := wElt rigX2 rigX2_lt

theorem x1_spec : x1E ∈ K0 ∧ x1E ^ 5 = 1 ∧
    ∀ t ∈ R0, t * x1E * t⁻¹ * x1E⁻¹ ∈ vSub → t ∈ vSub := by
  have h := rigX1_check
  rw [rigX1OK] at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := h
  refine ⟨coe_mem_K0.2 ((rigComm_iff (rep_cWord rigX1_lt) rep_w0P).1 h1), ?_, ?_⟩
  · have h5 : ∀ k ∈ rigX1 ++ rigX1 ++ rigX1 ++ rigX1 ++ rigX1, k < 10 := by decide
    have e := eq_of_eqA (rep_cWord h5) rep_idA h2
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change wPerm rigX1 ^ 5 = 1
    rw [← e]
    simp only [wPerm_append, pow_succ, pow_zero, one_mul]
  · intro t ht hv
    obtain ⟨c, hc, j, hj, rfl, hcomm⟩ := exists_of_mem_R0 ht
    have h4 := allLt_iff.1 (h3 c (List.mem_range.2 hc)) j hj
    obtain ⟨i, hi, hvi⟩ := exists_qEC_of_mem_vSub hv
    have hcv : rigCommV (rigRTab c j) (cWord rigX1) = true := by
      refine (rigCommV_iff (rep_rElt hc hj) (rep_cWord rigX1_lt)).2 ⟨i, hi, ?_⟩
      have e2 : rElt c j * x1E = qEC i * (x1E * rElt c j) := by
        rw [← hvi]
        group
      exact congrArg Subtype.val e2
    rw [hcomm, hcv] at h4
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h4
    obtain ⟨rfl, hj4⟩ := h4
    rw [rElt, uHat_zero, one_mul]
    exact qEC_mem_vSub hj4

theorem x2_spec : x2E ∈ K0 ∧ x2E ^ 3 ∈ R0 := by
  have h := rigX2_check
  rw [rigX2OK] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  have hK : x2E ∈ K0 := coe_mem_K0.2 ((rigComm_iff (rep_cWord rigX2_lt) rep_w0P).1 h1)
  have h3 : ∀ k ∈ rigX2 ++ rigX2 ++ rigX2, k < 10 := by decide
  have e : x2E ^ 3 = wElt (rigX2 ++ rigX2 ++ rigX2) h3 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change wPerm rigX2 ^ 3 = wPerm (rigX2 ++ rigX2 ++ rigX2)
    simp only [wPerm_append, pow_succ, pow_zero, one_mul]
  refine ⟨hK, pow_mem hK 3, ?_⟩
  have hrep : TabRep (matWord (rigX2 ++ rigX2 ++ rigX2))
      (kapL (phi0 (wElt (rigX2 ++ rigX2 ++ rigX2) h3))) := by
    rw [kapL_phi0]
    exact tabRep_matWord _
  change phi0 (x2E ^ 3) ∈ uSub
  rw [e]
  exact (rigUTest_iff hrep).1 h2

theorem wElt_expand_mem {D : Subgroup ↥(invE 1)} (h1 : x1E ∈ D) (h2 : x2E ∈ D) :
    ∀ u : List ℕ, wElt (rigExpand u) (rigExpand_lt u) ∈ D
  | [] => by
    have e : wElt (rigExpand []) (rigExpand_lt []) = 1 := rfl
    rw [e]
    exact D.one_mem
  | l :: u => by
    have e : wElt (rigExpand (l :: u)) (rigExpand_lt _) =
        (if l == 0 then x1E else x2E) * wElt (rigExpand u) (rigExpand_lt u) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      change wPerm (rigExpand (l :: u)) = _
      rw [rigExpand, List.flatMap_cons, wPerm_append]
      split_ifs <;> rfl
    rw [e]
    refine D.mul_mem ?_ (wElt_expand_mem h1 h2 u)
    split_ifs
    · exact h1
    · exact h2

theorem K0_le_of_gens {D : Subgroup ↥(invE 1)} (hD : D ≤ K0) (hR : R0 ≤ D) (h1 : x1E ∈ D)
    (h2 : x2E ∈ D) : K0 ≤ D := by
  intro k hk
  have hmem : kapL (phi0 k) ∈ rho1.range.map kappa := ⟨rho1 k, ⟨k, rfl⟩, (kapL_phi0 k).symm⟩
  obtain ⟨t, ht, hrep⟩ := kappa_rho1_enumerates.complete _ hmem
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
  have h1t : (matEnum.tabs[i]!)[1]! = 1 :=
    (tab_eq_iff hrep (by norm_num) (by norm_num)).2 (phi0_e0 hk)
  have hb := rigBfs_check
  simp only [rigBfsOK] at hb
  have hb' := allLt_iff.1 hb i (by rwa [matEnum_size] at hi)
  rw [h1t] at hb'
  simp only [bne_self_eq_false, Bool.false_or, List.any_map, List.any_eq_true,
    Function.comp_apply] at hb'
  obtain ⟨u, -, hag⟩ := hb'
  have hwD : wElt (rigExpand u) (rigExpand_lt u) ∈ D := wElt_expand_mem h1 h2 u
  have hwK := hD hwD
  have hrepw : TabRep (matWord (rigExpand u))
      (kapL (phi0 (wElt (rigExpand u) (rigExpand_lt u)))) := by
    rw [kapL_phi0]
    exact tabRep_matWord _
  have hU : phi0 ((wElt (rigExpand u) (rigExpand_lt u))⁻¹ * k) ∈ uSub := by
    rw [map_mul, map_inv]
    exact inv_mul_mem_uSub (phi0_e0 hwK) (phi0_e0 hk) fun x hx => rigAgree_spec hrep hrepw hag hx
  have := D.mul_mem hwD (hR ⟨K0.mul_mem (K0.inv_mem hwK) hk, hU⟩)
  rwa [mul_inv_cancel_left] at this

end Gens

@[expose] def clear0 (y : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := y - y 0 • bitVec 1

theorem bitVec_one_zero : bitVec 1 0 = 1 := by decide

theorem bitVec_one_one : bitVec 1 1 = 0 := by decide

theorem clear0_zero (y : Fin 6 → ZMod 2) : clear0 y 0 = 0 := by
  simp [clear0, bitVec_one_zero]

theorem clear0_one (y : Fin 6 → ZMod 2) : clear0 y 1 = y 1 := by
  simp [clear0, bitVec_one_one]

theorem clear0_add (y z : Fin 6 → ZMod 2) : clear0 (y + z) = clear0 y + clear0 z := by
  ext i
  simp only [clear0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem clear0_smul (a : ZMod 2) (y : Fin 6 → ZMod 2) : clear0 (a • y) = a • clear0 y := by
  ext i
  simp only [clear0, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem clear0_e0 : clear0 (bitVec 1) = 0 := by
  simp [clear0, bitVec_one_zero]

theorem clear0_of {y : Fin 6 → ZMod 2} (hy : y 0 = 0) : clear0 y = y := by
  simp [clear0, hy]

theorem eq_clear0_add (y : Fin 6 → ZMod 2) : y = clear0 y + y 0 • bitVec 1 := by
  simp [clear0]

@[expose] def wZero : AddSubgroup (Fin 6 → ZMod 2) where
  carrier := {x | x 0 = 0 ∧ x 1 = 0}
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  neg_mem' ha := ⟨by simp [ha.1], by simp [ha.2]⟩

theorem bitVec_rigXor_mem {F : AddSubmonoid (Fin 6 → ZMod 2)} {b : List ℕ}
    (hb : ∀ y ∈ b, bitVec y ∈ F) (m : ℕ) : bitVec (rigXor b m) ∈ F := by
  have key : ∀ l : List ℕ, (∀ k ∈ l, k < b.length) → ∀ a, bitVec a ∈ F →
      bitVec (l.foldl (fun acc k => acc ^^^ b.getD k 0) a) ∈ F := by
    intro l
    induction l with
    | nil => exact fun _ a ha => ha
    | cons k l ih =>
      intro hl a ha
      simp only [List.foldl_cons]
      refine ih (fun j hj => hl j (List.mem_cons_of_mem k hj)) _ ?_
      rw [bitVec_xor]
      refine F.add_mem ha (hb _ ?_)
      rw [List.getD_eq_getElem _ _ (hl k List.mem_cons_self)]
      exact List.getElem_mem _
  unfold rigXor
  refine key _ (fun k hk => List.mem_range.1 (List.mem_filter.1 hk).1) 0 ?_
  rw [bitVec_zero]
  exact F.zero_mem

section Irred

@[expose] noncomputable def actW0 (c : ↥(invE 1)) (x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  clear0 ((phi0 c).1 x)

theorem actW0_mem {c : ↥(invE 1)} (hc : c ∈ K0) {x : Fin 6 → ZMod 2} (hx : x ∈ wZero) :
    actW0 c x ∈ wZero :=
  ⟨clear0_zero _, by rw [actW0, clear0_one]; exact apply_one_of_fix (phi0_e0 hc) hx.2⟩

theorem actW0_mul {c : ↥(invE 1)} (hc : c ∈ K0) (c' : ↥(invE 1)) (x : Fin 6 → ZMod 2) :
    actW0 (c * c') x = actW0 c (actW0 c' x) := by
  rw [actW0, actW0, actW0, map_mul, lm_mul_apply]
  conv_lhs => rw [eq_clear0_add ((phi0 c').1 x)]
  rw [map_add, map_smul, phi0_e0 hc, clear0_add, clear0_smul, clear0_e0, smul_zero, add_zero]

theorem actW0_one {x : Fin 6 → ZMod 2} (hx : x ∈ wZero) : actW0 1 x = x := by
  rw [actW0, map_one]
  exact clear0_of hx.1

theorem actW0_zero (c : ↥(invE 1)) : actW0 c 0 = 0 := by
  rw [actW0, map_zero]
  simp [clear0]

theorem le_R0 {P : Subgroup ↥(invE 1)} (hPK : P ≤ K0)
    (hnorm : ∀ k ∈ K0, ∀ p ∈ P, k * p * k⁻¹ ∈ P) (hP : IsPGroup 2 P) : P ≤ R0 := by
  let F : AddSubmonoid (Fin 6 → ZMod 2) :=
    { carrier := {x | ∀ p ∈ P, (phi0 p).1 x = x ∨ (phi0 p).1 x = x + bitVec 1}
      add_mem' := fun {x y} hx hy p hp => by
        rw [map_add]
        rcases hx p hp with h1 | h1 <;> rcases hy p hp with h2 | h2 <;> rw [h1, h2]
        · exact Or.inl rfl
        · exact Or.inr (add_assoc _ _ _).symm
        · exact Or.inr (add_right_comm _ _ _)
        · left
          rw [add_add_add_comm, e0_add_self, add_zero]
      zero_mem' := fun p _ => Or.inl (map_zero _) }
  have hFk : ∀ k ∈ K0, ∀ x ∈ F, (phi0 k).1 x ∈ F := by
    intro k hk x hx p hp
    have hq : k⁻¹ * p * k ∈ P := by simpa using hnorm _ (K0.inv_mem hk) p hp
    have e : p * k = k * (k⁻¹ * p * k) := by group
    have h1 : (phi0 p).1 ((phi0 k).1 x) = (phi0 k).1 ((phi0 (k⁻¹ * p * k)).1 x) := by
      rw [← lm_mul_apply, ← lm_mul_apply, ← map_mul, ← map_mul, e]
    rw [h1]
    rcases hx _ hq with h2 | h2
    · rw [h2]
      exact Or.inl rfl
    · rw [h2, map_add, phi0_e0 hk]
      exact Or.inr rfl
  have he0 : bitVec 1 ∈ F := fun p hp => Or.inl (phi0_e0 (hPK hp))
  let _ : MulAction P wZero :=
    { smul := fun p x => ⟨actW0 p x, actW0_mem (hPK p.2) x.2⟩
      one_smul := fun x => Subtype.ext (actW0_one x.2)
      mul_smul := fun p q x => Subtype.ext (actW0_mul (hPK p.2) _ x.1) }
  have hfix : ∃ x : wZero, x ∈ MulAction.fixedPoints P wZero ∧ x ≠ 0 := by
    by_contra hne
    push Not at hne
    have hFix : MulAction.fixedPoints P wZero = {0} := by
      ext x
      refine ⟨fun hx => hne x hx, fun hx => ?_⟩
      rw [Set.mem_singleton_iff.1 hx]
      intro p
      exact Subtype.ext (actW0_zero p)
    have hmod := IsPGroup.card_modEq_card_fixedPoints hP (wZero : Type)
    have h1 : Nat.card ({0} : Set wZero) = 1 := by simp
    rw [hFix, h1] at hmod
    have h4 : bitVec 4 ∈ wZero := ⟨by decide, by decide⟩
    have hne4 : (⟨bitVec 4, h4⟩ : wZero) ≠ 0 := fun h => by
      have := congrArg Subtype.val h
      exact absurd (bitVec_inj 4 (by norm_num) 0 (by norm_num) (this.trans bitVec_zero.symm))
        (by norm_num)
    have h2 : addOrderOf (⟨bitVec 4, h4⟩ : wZero) = 2 :=
      addOrderOf_eq_prime (Subtype.ext (by
        rw [two_smul]
        exact (by rw [← bitVec_xor, Nat.xor_self, bitVec_zero] : bitVec 4 + bitVec 4 = 0))) hne4
    have hdvd := addOrderOf_dvd_natCard (⟨bitVec 4, h4⟩ : wZero)
    rw [h2] at hdvd
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨x₀, hx₀, hx₀0⟩ := hfix
  have hx₀F : (x₀ : Fin 6 → ZMod 2) ∈ F := by
    intro p hp
    have h := congrArg Subtype.val (hx₀ ⟨p, hp⟩)
    change actW0 p x₀ = x₀ at h
    rw [actW0] at h
    have e := eq_clear0_add ((phi0 p).1 x₀)
    rw [h] at e
    generalize ((phi0 p).1 (x₀ : Fin 6 → ZMod 2)) 0 = a at e
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · left
      rw [e, zero_smul, add_zero]
    · right
      rw [e, one_smul]
  obtain ⟨v, hv, hxv⟩ := exists_bitVec (x₀ : Fin 6 → ZMod 2)
  have hv0 : v ≠ 0 := fun h => hx₀0 (Subtype.ext (by rw [← hxv, h, bitVec_zero]; rfl))
  have hv1 : v ≠ 1 := fun h => by
    have := x₀.2.1
    rw [← hxv, h, bitVec_one_zero] at this
    exact one_ne_zero this
  have hbv : rigBil v = 0 := (rigBil_eq_zero_iff v hv).2 (by rw [hxv]; exact x₀.2.2)
  have hirr := rigIrred_check
  simp only [rigIrredOK] at hirr
  have h1 := allLt_iff.1 hirr v hv
  simp only [Bool.or_eq_true, beq_iff_eq, hv0, hv1, hbv, bne_self_eq_false, Bool.false_eq_true,
    false_or] at h1
  have hb : ∀ y ∈ 1 :: (rigIrrWords.map fun u => matWord (rigExpand u)).map fun m => m[v]!,
      bitVec y ∈ F := by
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact he0
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hm
      have hrep : TabRep (matWord (rigExpand u))
          (kapL (phi0 (wElt (rigExpand u) (rigExpand_lt u)))) := by
        rw [kapL_phi0]
        exact tabRep_matWord _
      rw [bitVec_tab hrep hv, hxv]
      exact hFk _ (wElt_expand_mem x1_spec.1 x2_spec.1 u) _ hx₀F
  have hall : ∀ y : Fin 6 → ZMod 2, y 1 = 0 → y ∈ F := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := exists_bitVec y
    have h2 := allLt_iff.1 h1 u hu
    have hbu : rigBil u = 0 := (rigBil_eq_zero_iff u hu).2 hy
    simp only [hbu, bne_self_eq_false, Bool.false_or, anyBelow_eq_true, beq_iff_eq] at h2
    obtain ⟨m, -, hm⟩ := h2
    rw [← hm]
    exact bitVec_rigXor_mem hb m
  intro p hp
  exact ⟨hPK hp, phi0_e0 (hPK hp), fun y hy => hall y hy p hp⟩

theorem exists_conj_R0 {f : ↥(invE 1) → ↥(invE 1)}
    (hf : IsoOn f K0 K0) (hfV : ∀ v ∈ vSub, f v = v) (hfR : ∀ g ∈ K0, f g * g⁻¹ ∈ R0) :
    ∃ s ∈ R0, ∀ g ∈ K0, f g = s * g * s⁻¹ := by
  have hS : ∀ r₀ ∈ ({sElt 0, sElt 1} : Set ↥(invE 1)), ∃ s < 2, r₀ = sElt s := by
    rintro r₀ (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  refine coreData.exists_conj hf hfV hfR (S := {sElt 0, sElt 1}) ?_ ?_ ?_ ?_ x1_spec.1
    (by decide : Odd 5) x1_spec.2.1 x1_spec.2.2 x2_spec.1 (by decide : Odd 3) x2_spec.2
    fun D hD hR h1 h2 => K0_le_of_gens hD hR h1 h2
  · intro r₀ h
    obtain ⟨s, hs, rfl⟩ := hS r₀ h
    exact sElt_mem_R0 hs
  · intro r₀ h
    obtain ⟨s, hs, rfl⟩ := hS r₀ h
    exact sElt_mul_self hs
  · intro r₀ h
    obtain ⟨s, hs, rfl⟩ := hS r₀ h
    exact ⟨gamSet s, (stab_spec hs).1, (stab_spec hs).2.1, (stab_spec hs).2.2⟩
  · intro F hV hSF hinv
    exact R0_le_of_seeds hV (hSF (Or.inl rfl)) (hSF (Or.inr rfl)) hinv

end Irred

end CFSG.Sporadic.SuzRecog.RigidL2
