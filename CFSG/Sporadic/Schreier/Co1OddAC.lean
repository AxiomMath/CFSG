module

public import CFSG.Sporadic.Schreier.Co1OddRows
public import CFSG.Sporadic.Schreier.Co1OddGen
public import CFSG.Sporadic.Schreier.Co1Lift
public import CFSG.Sporadic.Co1.Module.InvRepsBase

public section

namespace CFSG.Sporadic.Co1Schreier.OddAC

open CFSG.Sporadic.SmallF2 (toVecD rowsMatrix)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative Matrix
open CFSG.Sporadic.Co1Schreier.OddGen CFSG.Sporadic.Co1Schreier.OddRows CFSG.Sporadic.Co2Cert

attribute [local instance] xAct

@[expose] noncomputable def hMat : stabH →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 24) (Fin 24) (ZMod 2))).comp stabH.subtype

theorem hMat_injective : Function.Injective hMat := fun _ _ e => Subtype.ext (Units.ext e)

@[expose] noncomputable def acRegsH : List stabH :=
  CFSG.Sporadic.Co1.Module.Odd.runEval [⟨stabH0, stabH0_mem⟩, ⟨stabH1, stabH1_mem⟩]
    Data.oddACProg

@[expose] noncomputable def acElt (i : ℕ) : stabH := acRegsH.getD i 1

attribute [local irreducible] Native.hRows0 Native.hRows1 stabH0 stabH1

theorem acRel :
    CFSG.Sporadic.Co1.Module.Odd.RegsRel hMat acRegsH Native.oddACRegs := by
  refine CFSG.Sporadic.Co1.Module.Odd.runRows_spec hMat Data.oddACProg ?_
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact stabH0_rep.symm
  | 1 => exact stabH1_rep.symm
  | i + 2 => simp [CFSG.Sporadic.SmallF2.rowsMatrix_idRows]

theorem hMat_acElt (i : ℕ) :
    hMat (acElt i) = rowsMatrix 24 (Native.oddReg Native.oddACRegs i) := acRel.2 i

theorem coe_acElt
    (i : ℕ) : (((acElt i : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
    rowsMatrix 24 (Native.oddReg Native.oddACRegs i) := hMat_acElt i

theorem ac_facts :
    validRows (Native.oddReg Native.oddACRegs 3) = true ∧
    validRows (Native.oddReg Native.oddACRegs 10) = true ∧
    mulRows 24 (Native.oddReg Native.oddACRegs 3) (Native.oddReg Native.oddACRegs 3) =
      idRows 24 ∧
    Native.oddReg Native.oddACRegs 3 ≠ idRows 24 ∧
    mulRows 24 (Native.oddReg Native.oddACRegs 8) (Native.oddReg Native.oddACRegs 3) =
      mulRows 24 (Native.oddReg Native.oddACRegs 3) (Native.oddReg Native.oddACRegs 8) ∧
    powRows 24 (Native.oddReg Native.oddACRegs 8) 15 = idRows 24 ∧
    mulRows 24 (Native.oddReg Native.oddACRegs 10) (Native.oddReg Native.oddACRegs 10) =
      idRows 24 ∧
    Native.oddReg Native.oddACRegs 10 ≠ idRows 24 ∧
    mulRows 24 (Native.oddReg Native.oddACRegs 15) (Native.oddReg Native.oddACRegs 10) =
      mulRows 24 (Native.oddReg Native.oddACRegs 10) (Native.oddReg Native.oddACRegs 15) ∧
    mulRows 24 (Native.oddReg Native.oddACRegs 20) (Native.oddReg Native.oddACRegs 10) =
      mulRows 24 (Native.oddReg Native.oddACRegs 10) (Native.oddReg Native.oddACRegs 20) ∧
    powRows 24 (Native.oddReg Native.oddACRegs 15) 3 = idRows 24 ∧
    powRows 24 (Native.oddReg Native.oddACRegs 20) 3 = idRows 24 := by
  have h := odd_ac_check
  simp only [Native.oddACCheckOf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem orderOf_acElt_three :
    orderOf (acElt 3) = 2 := by
  obtain ⟨hv, -, hsq, hne, -⟩ := ac_facts
  refine orderOf_eq_prime ?_ (ne_one_of_rows (hMat_acElt 3) hv hne)
  rw [sq]
  exact mul_eq_one_of_rows hMat_injective (hMat_acElt 3) (hMat_acElt 3) hsq

theorem orderOf_acElt_ten :
    orderOf (acElt 10) = 2 := by
  obtain ⟨-, hv, -, -, -, -, hsq, hne, -⟩ := ac_facts
  refine orderOf_eq_prime ?_ (ne_one_of_rows (hMat_acElt 10) hv hne)
  rw [sq]
  exact mul_eq_one_of_rows hMat_injective (hMat_acElt 10) (hMat_acElt 10) hsq

theorem acElt_eight_comm :
    acElt 8 * acElt 3 = acElt 3 * acElt 8 :=
  commute_of_rows hMat_injective (hMat_acElt 8) (hMat_acElt 3) ac_facts.2.2.2.2.1

theorem acElt_eight_pow :
    acElt 8 ^ 15 = 1 :=
  pow_eq_one_of_rows hMat_injective (hMat_acElt 8) ac_facts.2.2.2.2.2.1

theorem acElt_fifteen_comm :
    acElt 15 * acElt 10 = acElt 10 * acElt 15 :=
  commute_of_rows hMat_injective (hMat_acElt 15) (hMat_acElt 10) ac_facts.2.2.2.2.2.2.2.2.1

theorem acElt_twenty_comm :
    acElt 20 * acElt 10 = acElt 10 * acElt 20 :=
  commute_of_rows hMat_injective (hMat_acElt 20) (hMat_acElt 10) ac_facts.2.2.2.2.2.2.2.2.2.1

theorem acElt_fifteen_pow :
    acElt 15 ^ 3 = 1 :=
  pow_eq_one_of_rows hMat_injective (hMat_acElt 15) ac_facts.2.2.2.2.2.2.2.2.2.2.1

theorem acElt_twenty_pow :
    acElt 20 ^ 3 = 1 :=
  pow_eq_one_of_rows hMat_injective (hMat_acElt 20) ac_facts.2.2.2.2.2.2.2.2.2.2.2

theorem ac_counts :
    {v : Vec24 | rowsMatrix 24 (Native.oddReg Native.oddACRegs 3) *ᵥ v = v}.ncard = 65536 ∧
    {v : Vec24 | rowsMatrix 24 (Native.oddReg Native.oddACRegs 3) *ᵥ v = v ∧
      CFSG.Sporadic.Co1.Module.q₀ v = 1}.ncard = 30720 ∧
    {v : Vec24 | rowsMatrix 24 (Native.oddReg Native.oddACRegs 10) *ᵥ v = v}.ncard = 4096 ∧
    {v : Vec24 | rowsMatrix 24 (Native.oddReg Native.oddACRegs 10) *ᵥ v = v ∧
      CFSG.Sporadic.Co1.Module.q₀ v = 1}.ncard = 2048 := by
  have h := odd_ac_counts
  simp only [Native.oddACCountsOf, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := CFSG.Sporadic.Co1.Module.countsOK_facts h.1
  obtain ⟨h3, h4⟩ := CFSG.Sporadic.Co1.Module.countsOK_facts h.2
  exact ⟨h1, h2, h3, h4⟩

theorem ac_x_counts :
    {v : Vec24 | v ∈ co1X ∧ ∀ M ∈ [Native.oddReg Native.oddACRegs 3],
      rowsMatrix 24 M *ᵥ v = v}.ncard = 2280 ∧
    {v : Vec24 | v ∈ co1X ∧ ∀ M ∈ [Native.oddReg Native.oddACRegs 3,
      Native.oddReg Native.oddACRegs 8], rowsMatrix 24 M *ᵥ v = v}.ncard = 1 ∧
    {v : Vec24 | v ∈ co1X ∧ ∀ M ∈ [Native.oddReg Native.oddACRegs 10],
      rowsMatrix 24 M *ᵥ v = v}.ncard = 264 ∧
    {v : Vec24 | v ∈ co1X ∧ ∀ M ∈ [Native.oddReg Native.oddACRegs 10,
      Native.oddReg Native.oddACRegs 15, Native.oddReg Native.oddACRegs 20],
      rowsMatrix 24 M *ᵥ v = v}.ncard = 2 := by
  have h := odd_ac_x
  simp only [Native.oddACXOf, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ncard_co1X_fix]; exact h1
  · rw [ncard_co1X_fix]; exact h2
  · rw [ncard_co1X_fix]; exact h3
  · rw [ncard_co1X_fix]; exact h4

theorem mem_stabH_iff_fix
    {g : GL24} (hg : g ∈ GA) :
    g ∈ stabH ↔ ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0 := by
  rw [← mem_stab_iff (g := ⟨g, hg⟩), MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [xAct_val] at h'
    exact h'
  · intro h
    apply Subtype.ext
    rw [xAct_val]
    exact h

theorem centOddFreeIn_stabH
    (hCo2 : ∀ (a : CFSG.Sporadic.Co2Cert.co2P), orderOf a = 2 →
      CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥)
    {t : GL24} (ht : t ∈ stabH) (ht2 : orderOf t = 2) : CentOddFreeIn stabH t := by
  have h2 : orderOf (stabPermEquiv ⟨t, ht⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ht2
  have h0 : CentOddFreeIn (⊤ : Subgroup co2P) (stabPermEquiv ⟨t, ht⟩) :=
    centOddFreeIn_of_oddCore (hCo2 _ h2)
  have h := @CentOddFreeIn.map_equiv (↥co2P) (↥stabH) (Subgroup.toGroup co2P)
    (Subgroup.toGroup stabH) stabPermEquiv.symm _ h0
  rw [MulEquiv.symm_apply_apply] at h
  exact CentOddFreeIn.of_subtype ht h

@[expose] def vStab (v : Vec24) : Subgroup GL24 where
  carrier := {h | ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v}
  mul_mem' {a b} ha hb := by
    show ((a * b : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
    rw [Units.val_mul, ← mulVec_mulVec, hb, ha]
  one_mem' := by
    show ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
    rw [Units.val_one, one_mulVec]
  inv_mem' {a} ha := by
    show ((a⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
    have ha' : ((a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v := ha
    conv_lhs => rw [← ha']
    exact inv_mulVec_mulVec a v

theorem mem_vStab {v : Vec24} {h : GL24} :
    h ∈ vStab v ↔ ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v := Iff.rfl

theorem mulVec_conj (g x : GL24) (v : Vec24) :
    ((g⁻¹ * x * g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v =
      ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v)) := by
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]

theorem free_of_fix
    (hH : ∀ t ∈ stabH, orderOf t = 2 → CentOddFreeIn stabH t)
    {a : GL24} (ha : a ∈ GA) (ha2 : orderOf a = 2) (N : Subgroup GL24) (hNG : N ≤ GA)
    (hNa : ∀ n ∈ N, n * a = a * n)
    (hnorm : ∀ c ∈ GA, c * a = a * c → ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hodd : Odd (Nat.card N))
    {v : Vec24} (hv : v ∈ co1X)
    (hav : ((a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) {m : GL24} (hm : m ∈ N)
    (hmv : ((m : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) : m = 1 := by
  rw [co1X_eq_kOrbit] at hv
  obtain ⟨g, hg, rfl⟩ := hv
  have hgi : g⁻¹ ∈ GA := GA.inv_mem hg
  have hfix : ∀ x : GL24, ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0) =
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 →
      ((g⁻¹ * x * g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 =
        stabVecOf 0 := by
    intro x hx
    rw [mulVec_conj, hx, inv_mulVec_mulVec]
  have hconj : ∀ x : GL24, MulAut.conj g⁻¹ x = g⁻¹ * x * g := fun x => by
    rw [MulAut.conj_apply, inv_inv]
  have htGA : g⁻¹ * a * g ∈ GA := GA.mul_mem (GA.mul_mem hgi ha) hg
  have htH : g⁻¹ * a * g ∈ stabH := (mem_stabH_iff_fix htGA).mpr (hfix a hav)
  have ht2 : orderOf (g⁻¹ * a * g) = 2 := by
    rw [← hconj, MulEquiv.orderOf_eq]
    exact ha2
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup GL24, Q = (N ⊓ vStab (((g : GL24) : Matrix (Fin 24) (Fin 24)
      (ZMod 2)) *ᵥ stabVecOf 0)).map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hQb : Q = ⊥ := by
    refine hH _ htH ht2 Q ?_ ?_ ?_ ?_
    · rw [hQ]
      rintro _ ⟨n, ⟨hnN, hnv⟩, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hconj]
      exact (mem_stabH_iff_fix (GA.mul_mem (GA.mul_mem hgi (hNG hnN)) hg)).mpr (hfix n hnv)
    · rw [hQ]
      rintro _ ⟨n, ⟨hnN, -⟩, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hconj]
      have h := hNa n hnN
      calc g⁻¹ * n * g * (g⁻¹ * a * g) = g⁻¹ * (n * a) * g := by group
        _ = g⁻¹ * (a * n) * g := by rw [h]
        _ = g⁻¹ * a * g * (g⁻¹ * n * g) := by group
    · rw [hQ]
      rintro c hcH hct _ ⟨n, ⟨hnN, hnv⟩, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hconj]
      have hcGA : g * c * g⁻¹ ∈ GA := GA.mul_mem (GA.mul_mem hg (stabH_le_GA hcH)) hgi
      have hca : g * c * g⁻¹ * a = a * (g * c * g⁻¹) := by
        calc g * c * g⁻¹ * a = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by rw [hct]
          _ = a * (g * c * g⁻¹) := by group
      have hcz : ((c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0 :=
        stabH_fix_z hcH
      have hcv : g * c * g⁻¹ ∈ vStab (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          stabVecOf 0) := by
        rw [mem_vStab, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec,
          inv_mulVec_mulVec, hcz]
      refine ⟨g * c * g⁻¹ * n * (g * c * g⁻¹)⁻¹, ⟨hnorm _ hcGA hca n hnN, ?_⟩, ?_⟩
      · exact (vStab _).mul_mem ((vStab _).mul_mem hcv hnv) ((vStab _).inv_mem hcv)
      · rw [MulEquiv.coe_toMonoidHom, hconj]
        group
    · rw [hQ, card_map_mulAut_conj]
      have hle : N ⊓ vStab (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0) ≤
        N := inf_le_left
      exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hmQ : MulAut.conj g⁻¹ m ∈ Q := by
    rw [hQ]
    exact ⟨m, ⟨hm, hmv⟩, rfl⟩
  rw [hQb, Subgroup.mem_bot] at hmQ
  exact (MulAut.conj g⁻¹).injective (hmQ.trans (map_one _).symm)

@[expose, instance_reducible] def glAct (N : Subgroup GL24) : MulAction N Vec24 where
  smul g v := ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v
  one_smul v := by
    show (((1 : N) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v
    rw [OneMemClass.coe_one, Units.val_one, one_mulVec]
  mul_smul g h v := by
    show (((g * h : N) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v =
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v)
    rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]

theorem finite_GL24 : Finite GL24 :=
  Finite.of_injective (fun u : GL24 => ((u : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    Fin 24 → Fin 24 → ZMod 2)) fun _ _ h => Units.ext h

theorem card_dvd_of_free (N : Subgroup GL24) {S : Set Vec24} (hfin : S.Finite)
    (hS : ∀ g ∈ N, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ S)
    (hfree : ∀ g ∈ N, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v →
      g = 1) :
    Nat.card N ∣ S.ncard := by
  have := finite_GL24
  exact @card_dvd_ncard_of_free N Vec24 _ (glAct N) _ S hfin (fun g v hv => hS g g.2 v hv)
    (fun g v hv h => Subtype.ext (hfree g g.2 v hv h))

theorem fix_of_two (N : Subgroup GL24) (hodd : Odd (Nat.card N)) {S : Set Vec24}
    (hfin : S.Finite) (h2 : S.ncard ≤ 2)
    (hS : ∀ g ∈ N, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ S) :
    ∀ g ∈ N, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v := by
  have := finite_GL24
  intro g hg v hv
  exact @fix_of_ncard_le_two N Vec24 _ (glAct N) _ hodd S (fun g v hv => hS g g.2 v hv) hfin h2
    ⟨g, hg⟩ v hv

theorem mem_fix_of_comm
    {t g : GL24} (hg : g ∈ GA) (hgt : g * t = t * g) {v : Vec24}
    (hv : v ∈ co1X) (htv : ((t : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) :
    ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ co1X ∧
      ((t : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) =
        ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v := by
  refine ⟨mem_co1X_smul hg hv, ?_⟩
  rw [mulVec_mulVec, ← Units.val_mul, ← hgt, Units.val_mul, ← mulVec_mulVec, htv]

section Classes

variable (hCo2 : ∀ (a : CFSG.Sporadic.Co2Cert.co2P), orderOf a = 2 →
  CFSG.oddCore (Subgroup.centralizer ({a} : Set CFSG.Sporadic.Co2Cert.co2P)) = ⊥)
include hCo2

theorem centOddFreeIn_A :
    CentOddFreeIn GA ((acElt 3 : stabH) : GL24) := by
  intro N hNG hNa hnorm hodd
  have hH := fun t ht ht2 => centOddFreeIn_stabH hCo2 (t := t) ht ht2
  have ha : ((acElt 3 : stabH) : GL24) ∈ GA := stabH_le_GA (acElt 3).2
  have ha2 : orderOf ((acElt 3 : stabH) : GL24) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_acElt_three
  obtain ⟨hX1, hX2, -, -⟩ := ac_x_counts
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    ← coe_acElt] at hX1 hX2
  have hdvd : Nat.card N ∣ 2280 := by
    rw [← hX1]
    refine card_dvd_of_free N (Set.toFinite _) (fun g hg v hv => mem_fix_of_comm (hNG hg)
      (hNa g hg) hv.1 hv.2) fun g hg v hv h => ?_
    exact free_of_fix hH ha ha2 N hNG hNa hnorm hodd hv.1 hv.2 hg h
  have hdvdG : Nat.card N ∣ 4157776806543360000 := card_GA_eq ▸ Subgroup.card_dvd_of_le hNG
  have h285 : Nat.card N ∣ 285 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd))
      (by rw [show 2 ^ 3 * 285 = 2280 by norm_num]; exact hdvd)
  have h15 : Nat.card N ∣ 15 := by
    have := Nat.dvd_gcd h285 hdvdG
    rwa [show Nat.gcd 285 4157776806543360000 = 15 by norm_num] at this
  have hfinN : Finite N := by
    have := finite_GL24
    infer_instance
  have hcyc : IsCyclic N := isCyclic_of_card_dvd_fifteen h15
  have hsGA : ((acElt 8 : stabH) : GL24) ∈ GA := stabH_le_GA (acElt 8).2
  have hsa : ((acElt 8 : stabH) : GL24) * ((acElt 3 : stabH) : GL24) =
      ((acElt 3 : stabH) : GL24) * ((acElt 8 : stabH) : GL24) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, acElt_eight_comm]
  have hs15 : ((acElt 8 : stabH) : GL24) ^ 15 = 1 := by
    rw [← Subgroup.coe_pow, acElt_eight_pow, OneMemClass.coe_one]
  have harith : ∀ e < Nat.card N, e ^ 15 % Nat.card N = 1 % Nat.card N →
      e % Nat.card N = 1 % Nat.card N := by
    have hd : Nat.card N ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨h15, by norm_num⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h | h <;> rw [h] <;> decide
  have hcomm := commute_of_cyclic (C := GL24) (M := N)
    (fun m hm => hnorm _ hsGA hsa m hm) hs15 harith
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hX2
  have hwmem : w ∈ {v : Vec24 | v ∈ co1X ∧
      (((acElt 3 : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v ∧
      (((acElt 8 : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} := by
    rw [hw]
    exact Set.mem_singleton w
  rw [eq_bot_iff]
  intro m hm
  have hm1 := mem_fix_of_comm (hNG hm) (hNa m hm) hwmem.1 hwmem.2.1
  have hm2 := mem_fix_of_comm (hNG hm) (hcomm m hm).symm hwmem.1 hwmem.2.2
  have hmw : ((m : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ {v : Vec24 | v ∈ co1X ∧
      (((acElt 3 : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v ∧
      (((acElt 8 : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} :=
    ⟨hm1.1, hm1.2, hm2.2⟩
  rw [hw, Set.mem_singleton_iff] at hmw
  exact (Subgroup.mem_bot).mpr (free_of_fix hH ha ha2 N hNG hNa hnorm hodd hwmem.1 hwmem.2.1 hm
    hmw)

theorem centOddFreeIn_C :
    CentOddFreeIn GA ((acElt 10 : stabH) : GL24) := by
  intro N hNG hNa hnorm hodd
  have hH := fun t ht ht2 => centOddFreeIn_stabH hCo2 (t := t) ht ht2
  have ha : ((acElt 10 : stabH) : GL24) ∈ GA := stabH_le_GA (acElt 10).2
  have ha2 : orderOf ((acElt 10 : stabH) : GL24) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_acElt_ten
  obtain ⟨-, -, hX1, hX2⟩ := ac_x_counts
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    ← coe_acElt] at hX1 hX2
  have hdvd : Nat.card N ∣ 264 := by
    rw [← hX1]
    refine card_dvd_of_free N (Set.toFinite _) (fun g hg v hv => mem_fix_of_comm (hNG hg)
      (hNa g hg) hv.1 hv.2) fun g hg v hv h => ?_
    exact free_of_fix hH ha ha2 N hNG hNa hnorm hodd hv.1 hv.2 hg h
  have h33 : Nat.card N ∣ 33 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd))
      (by rw [show 2 ^ 3 * 33 = 264 by norm_num]; exact hdvd)
  have hfinN : Finite N := by
    have := finite_GL24
    infer_instance
  have hcyc : IsCyclic N := isCyclic_of_card_dvd_thirtythree h33
  have harith : ∀ e < Nat.card N, e ^ 3 % Nat.card N = 1 % Nat.card N →
      e % Nat.card N = 1 % Nat.card N := by
    have hd : Nat.card N ∈ Nat.divisors 33 := Nat.mem_divisors.mpr ⟨h33, by norm_num⟩
    rw [show Nat.divisors 33 = {1, 3, 11, 33} by decide] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h | h <;> rw [h] <;> decide
  have key : ∀ i : ℕ, acElt i * acElt 10 = acElt 10 * acElt i → acElt i ^ 3 = 1 →
      ∀ m ∈ N, ((acElt i : stabH) : GL24) * m = m * ((acElt i : stabH) : GL24) := by
    intro i hi hi3
    have hiGA : ((acElt i : stabH) : GL24) ∈ GA := stabH_le_GA (acElt i).2
    have hic : ((acElt i : stabH) : GL24) * ((acElt 10 : stabH) : GL24) =
        ((acElt 10 : stabH) : GL24) * ((acElt i : stabH) : GL24) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hi]
    have hi3' : ((acElt i : stabH) : GL24) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hi3, OneMemClass.coe_one]
    exact commute_of_cyclic (C := GL24) (M := N) (fun m hm => hnorm _ hiGA hic m hm) hi3' harith
  have hc1 := key 15 acElt_fifteen_comm acElt_fifteen_pow
  have hc2 := key 20 acElt_twenty_comm acElt_twenty_pow
  set F : Set Vec24 := {v : Vec24 | v ∈ co1X ∧
      (((acElt 10 : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v ∧
      (((acElt 15 : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v ∧
      (((acElt 20 : stabH) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} with hF
  have hFinv : ∀ g ∈ N, ∀ v ∈ F, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ F := by
    intro g hg v hv
    have h1 := mem_fix_of_comm (hNG hg) (hNa g hg) hv.1 hv.2.1
    have h2 := mem_fix_of_comm (hNG hg) (hc1 g hg).symm hv.1 hv.2.2.1
    have h3 := mem_fix_of_comm (hNG hg) (hc2 g hg).symm hv.1 hv.2.2.2
    exact ⟨h1.1, h1.2, h2.2, h3.2⟩
  have hfix := fix_of_two N hodd (Set.toFinite F) (by rw [hX2]) hFinv
  obtain ⟨w, hw⟩ : F.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hX2]; norm_num)
  rw [eq_bot_iff]
  intro m hm
  exact (Subgroup.mem_bot).mpr (free_of_fix hH ha ha2 N hNG hNa hnorm hodd hw.1 hw.2.1 hm
    (hfix m hm w hw))

end Classes

end CFSG.Sporadic.Co1Schreier.OddAC
