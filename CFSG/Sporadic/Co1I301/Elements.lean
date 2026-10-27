module

public import CFSG.Sporadic.Co1Patterson.GraphNative
public import Certificates.Certificate810305
public import CFSG.LargeExtraspecial.S12Seven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1I301

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1I301.Native
  CFSG.Sporadic.Co1.Module
open CFSG.Blueprint (NativeSporadic.Co1)


@[expose] noncomputable def cElt (j : ℕ) : NativeSporadic.Co1 :=
  co1MatEquiv.symm ⟨(dagG gBaseGL (cWordsN.map Native.decWord)).getD (j - 1) 1,
    getD_mem_of_forall (dagG_mem gBaseGL_mem _) _⟩


theorem nrep_cElt (h : (cDag ()).2.2 = true) (j : ℕ) : NRep (cEl (cDag ()) j) (cElt j) := by
  refine nrep_of_mrep ?_
  rw [nativeEmb_apply, cElt, MulEquiv.apply_symm_apply]
  exact getD_rep (dag_rep rep_gBase _ h) MRep.one (j - 1)

theorem nrep_aC : NRep aRw aNC := by
  refine nrep_of_mrep ?_
  rw [nativeEmb_aNC]
  exact rep_iotaA

theorem eq_of_nrep {R : Native.Rows} {x y : NativeSporadic.Co1} (hx : NRep R x) (hy : NRep R y) :
    x = y :=
  hx.unique hy

theorem commute_of_nrep {R S : Native.Rows} {x y : NativeSporadic.Co1} (hR : NRep R x)
    (hS : NRep S y) (h : commR R S = true) : x * y = y * x :=
  eq_of_nrep (hR.mul hS) ((beq_iff_eq.1 h) ▸ hS.mul hR)

theorem nrep_pow {R : Native.Rows} {x : NativeSporadic.Co1} (hR : NRep R x) :
    ∀ n : ℕ, NRep (Native.pow R n) (x ^ n)
  | 0 => by rw [pow_zero]; exact NRep.one'
  | n + 1 => by rw [pow_succ]; exact (nrep_pow hR n).mul hR

theorem eq_one_of_nrep {R : Native.Rows} {x : NativeSporadic.Co1} (hR : NRep R x)
    (h : R = Native.one) : x = 1 :=
  eq_of_nrep hR (h ▸ NRep.one')

theorem ne_one_of_nrep {R : Native.Rows} {x : NativeSporadic.Co1} (hR : NRep R x)
    (hv : CFSG.Sporadic.Co1.InvNative.validRows R = true) (h : R ≠ Native.one) : x ≠ 1 := by
  rintro rfl
  exact h (NRep.rows_eq hR NRep.one' hv validRows_one)

theorem validRows_pow {R : Native.Rows} (hR : CFSG.Sporadic.Co1.InvNative.validRows R = true) :
    ∀ n : ℕ, CFSG.Sporadic.Co1.InvNative.validRows (Native.pow R n) = true
  | 0 => validRows_one
  | n + 1 => validRows_mul (validRows_pow hR n) hR

theorem co1RowCheck_parts : chkDag () = true ∧ chkD () = true ∧ chkRoots () = true ∧
    chkOrbit () = true ∧ chkR0 () = true ∧ chkK () = true ∧ chkE () = true := by
  have h := (Certificates.certificate810305 : co1RowCheck () = true)
  simp only [co1RowCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem cDag_flag : (cDag ()).2.2 = true := by
  have h := co1RowCheck_parts.1
  simp only [chkDag, Bool.and_eq_true] at h
  exact h.1.1

theorem cEl_valid {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 32) :
    CFSG.Sporadic.Co1.InvNative.validRows (cEl (cDag ()) j) = true := by
  have h := co1RowCheck_parts.1
  simp only [chkDag, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 (j - 1) (by omega)
  rwa [Nat.sub_add_cancel hj1] at this

theorem nrep_cElt' (j : ℕ) : NRep (cEl (cDag ()) j) (cElt j) := nrep_cElt cDag_flag j

noncomputable abbrev dC : NativeSporadic.Co1 := cElt 21

theorem nrep_dC : NRep (dRw ()) dC := nrep_cElt' 21

theorem dC_pow_three : dC ^ 3 = 1 := by
  have h := co1RowCheck_parts.2.1
  simp only [chkD, Bool.and_eq_true, beq_iff_eq] at h
  exact eq_one_of_nrep (nrep_pow nrep_dC 3) h.1.1.1

theorem dC_ne_one : dC ≠ 1 := by
  have h := co1RowCheck_parts.2.1
  simp only [chkD, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ne_one_of_nrep nrep_dC (cEl_valid (by norm_num) (by norm_num)) h.1.1.2

theorem orderOf_dC : orderOf dC = 3 :=
  orderOf_eq_prime dC_pow_three dC_ne_one

theorem dC_comm_aNC : dC * aNC = aNC * dC := by
  have h := co1RowCheck_parts.2.1
  simp only [chkD, Bool.and_eq_true] at h
  exact commute_of_nrep nrep_dC nrep_aC h.1.2

theorem dC_mem_centralizer : dC ∈ centralizer ({aNC} : Set NativeSporadic.Co1) :=
  (@mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC dC).2 dC_comm_aNC

theorem fixCount_dC_le :
    CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCount (rowsMatrix 24 (dRw ())) ≤ 1 := by
  have h := co1RowCheck_parts.2.1
  simp only [chkD, Bool.and_eq_true] at h
  simpa using CFSG.HardMathSupport.Dickson.I271.TabMFive.card_fixed_le_of_fixCheck
    (by norm_num) h.2

noncomputable abbrev k1C : NativeSporadic.Co1 := cElt 22

noncomputable abbrev k2C : NativeSporadic.Co1 := cElt 23

noncomputable abbrev eC (i : ℕ) : NativeSporadic.Co1 := cElt (24 + i)

noncomputable abbrev rC (i : ℕ) : NativeSporadic.Co1 := cElt (27 + i)

theorem nrep_k1C : NRep (k1Rw ()) k1C := nrep_cElt' 22

theorem nrep_k2C : NRep (k2Rw ()) k2C := nrep_cElt' 23

theorem nrep_eC (i : ℕ) : NRep (eRw i) (eC i) := nrep_cElt' (24 + i)

theorem nrep_rC (i : ℕ) : NRep (rRw i) (rC i) := nrep_cElt' (27 + i)

theorem k_comm : k1C * dC = dC * k1C ∧ k1C * aNC = aNC * k1C ∧ k2C * dC = dC * k2C ∧
    k2C * aNC = aNC * k2C := by
  have h := co1RowCheck_parts.2.2.2.2.2.1
  simp only [chkK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨commute_of_nrep nrep_k1C nrep_dC h1, commute_of_nrep nrep_k1C nrep_aC h2,
    commute_of_nrep nrep_k2C nrep_dC h3, commute_of_nrep nrep_k2C nrep_aC h4⟩

theorem e_facts : (∀ i < 3, eC i ^ 3 = 1 ∧ eC i * dC = dC * eC i ∧ eC i * aNC = aNC * eC i) ∧
    ∀ i < 3, ∀ j < 3, eC i * eC j = eC j * eC i := by
  have h := co1RowCheck_parts.2.2.2.2.2.2
  simp only [chkE, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj => commute_of_nrep (nrep_eC i) (nrep_eC j) (h2 i hi j hj)⟩
  obtain ⟨⟨h3, h4⟩, h5⟩ := h1 i hi
  exact ⟨eq_one_of_nrep (nrep_pow (nrep_eC i) 3) h3, commute_of_nrep (nrep_eC i) nrep_dC h4,
    commute_of_nrep (nrep_eC i) nrep_aC h5⟩

theorem e_indep : ∀ i j k l : ℕ, i < 3 → j < 3 → k < 3 → l < 3 →
    dC ^ i * eC 0 ^ j * eC 1 ^ k * eC 2 ^ l = 1 → i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 := by
  have h := co1RowCheck_parts.2.2.2.2.2.2
  simp only [chkE, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have h3 := h.2
  intro i j k l hi hj hk hl he
  have hn := h3 (i + 3 * j + 9 * k + 27 * l) (by omega)
  have e1 : (i + 3 * j + 9 * k + 27 * l) % 3 = i := by omega
  have e2 : (i + 3 * j + 9 * k + 27 * l) / 3 % 3 = j := by omega
  have e3 : (i + 3 * j + 9 * k + 27 * l) / 9 % 3 = k := by omega
  have e4 : (i + 3 * j + 9 * k + 27 * l) / 27 % 3 = l := by omega
  rw [e1, e2, e3, e4] at hn
  have hrep := (((nrep_pow nrep_dC i).mul (nrep_pow (nrep_eC 0) j)).mul
    (nrep_pow (nrep_eC 1) k)).mul (nrep_pow (nrep_eC 2) l)
  rcases Bool.or_eq_true_iff.1 hn with h0 | h0
  · have := beq_iff_eq.1 h0
    omega
  · exfalso
    have hne := bne_iff_ne.1 h0
    apply hne
    have hv : CFSG.Sporadic.Co1.InvNative.validRows (Native.mul (Native.mul (Native.mul
        (Native.pow (dRw ()) i) (Native.pow (eRw 0) j)) (Native.pow (eRw 1) k))
        (Native.pow (eRw 2) l)) = true := by
      exact validRows_mul (validRows_mul (validRows_mul
        (validRows_pow (cEl_valid (by norm_num) (by norm_num)) i)
        (validRows_pow (cEl_valid (by norm_num) (by norm_num)) j))
        (validRows_pow (cEl_valid (by norm_num) (by norm_num)) k))
        (validRows_pow (cEl_valid (by norm_num) (by norm_num)) l)
    rw [he] at hrep
    exact NRep.rows_eq hrep NRep.one' hv validRows_one

end CFSG.Sporadic.Co1I301
