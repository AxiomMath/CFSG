module

public import CFSG.Sporadic.Th.Recog.MFactsB.Rows
public import Certificates.Certificate687011

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th.Recog.MFactsCData


private abbrev rowsE0M : Array V4 := rowsE0 (rowsWJ 2) (rowsWJ 3)

private abbrev rowsE1M : Array V4 := rowsE1 (rowsWJ 7) rowsE0M (rowsUI (rowsWJ 7))

private abbrev rowsE8TM : Array (Array V4) := e8Tab rowsA rowsE0M rowsE1M

private abbrev rowsW1M : Array V4 := rowsW1 (rowsWJ 3) (rowsWJ 4)

private abbrev rowsW2M : Array V4 := rowsW2 (rowsWJ 7) rowsW1M (rowsUI (rowsWJ 7))

private abbrev rowsPreTM : Array (Array V4) := preTab rowsW1M rowsW2M (rowsWJ 3)

private abbrev rowsNETM : Array (Array V4) :=
  neTab (rowsWJ 2) (rowsWJ 3) (rowsWJ 4) (rowsWJ 7) (rowsUI (rowsWJ 7))

private abbrev rowsCETM : Array (Array V4) := ceTab (rowsWJ 5) (rowsWJ 6)

private abbrev rowsCEITM : Array (Array V4) := ceiTab (rowsWJ 5) (rowsWJ 6)

private abbrev rowsCNTM : Array (Array V4) :=
  cnTab (rowsWJ 3) (rowsWJ 4) (rowsWJ 7) (rowsWJ 5) (rowsWJ 6)

private abbrev rowsCNITM : Array (Array V4) :=
  cniTab (rowsWJ 3) (rowsWJ 4) (rowsUI (rowsWJ 7)) (rowsWJ 5) (rowsWJ 6)

private theorem check_spec :
    checkR687011 () = true ∧ checkE687011 () = true ∧ checkN687011 () = true ∧
      checkCE687011 () = true ∧ checkC687011 () = true ∧ checkA687011 () = true :=
  Certificates.certificate687011

private theorem check_R_sound :
    y₁ * x₁ = x₁ ^ 3 * y₁ ∧ ω₁ * y₁ = y₁ * x₁ * ω₁ ∧
      x₁ * x₂ = x₂ * x₁ ∧ x₁ * ω₂ = ω₂ * x₁ ∧
      ω₁ * x₂ = x₂ * ω₁ ∧ ω₁ * ω₂ = ω₂ * ω₁ := by
  have h := check_spec.1
  simp only [checkR687011, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact IsRows.eq_of_eqRows (isRows_y₁.mul isRows_x₁)
      ((isRows_x₁.pow 3).mul isRows_y₁) h1
  · apply Subtype.ext
    exact IsRows.eq_of_eqRows (isRows_ω₁.mul isRows_y₁)
      ((isRows_y₁.mul isRows_x₁).mul isRows_ω₁) h2
  · apply Subtype.ext
    exact eq_of_commR isRows_x₁ isRows_x₂ h3
  · apply Subtype.ext
    exact eq_of_commR isRows_x₁ isRows_ω₂ h4
  · apply Subtype.ext
    exact eq_of_commR isRows_ω₁ isRows_x₂ h5
  · apply Subtype.ext
    exact eq_of_commR isRows_ω₁ isRows_ω₂ h6

private theorem e8_injective_of_check
    (h : (List.finRange 8).all (fun l : Fin 8 =>
      (List.finRange l.val).all (fun l' : Fin l.val =>
        eqRows (rowsE8TM[l.val]!) (rowsE8TM[l'.val]!) == false)) = true) :
    Function.Injective e8 := by
  have hall : ∀ x : Fin 8, x ∈ List.finRange 8 → ∀ y : Fin x.val,
      y ∈ List.finRange x.val →
      (eqRows (rowsE8TM[x.val]!) (rowsE8TM[y.val]!) == false) = true := by
    intro x hx
    exact List.all_eq_true.mp (List.all_eq_true.mp h x hx)
  intro l l' hll
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hf := hall l' (List.mem_finRange l') ⟨l.val, hlt⟩ (List.mem_finRange _)
    have hf' : eqRows (rowsE8TM[l'.val]!) (rowsE8TM[l.val]!) = false := by
      simpa only [beq_iff_eq] using hf
    exact (IsRows.ne_of_eqRows (isRows_e8Tab l') (isRows_e8Tab l) hf')
      (congrArg Subtype.val hll.symm)
  · have hf := hall l (List.mem_finRange l) ⟨l'.val, hgt⟩ (List.mem_finRange _)
    have hf' : eqRows (rowsE8TM[l.val]!) (rowsE8TM[l'.val]!) = false := by
      simpa only [beq_iff_eq] using hf
    exact (IsRows.ne_of_eqRows (isRows_e8Tab l) (isRows_e8Tab l') hf')
      (congrArg Subtype.val hll)

private theorem check_E_sound : e₀ * e₁ = e₁ * e₀ ∧ Function.Injective e8 := by
  have h := check_spec.2.1
  simp only [checkE687011, Bool.and_eq_true] at h
  refine ⟨?_, e8_injective_of_check h.2⟩
  apply Subtype.ext
  exact eq_of_commR isRows_e₀ isRows_e₁ h.1

private theorem neTgt0_eq (i : Fin 5) :
    (⟨neTgt0[i.val]!, by fin_cases i <;> decide⟩ : Fin 8) = ![3, 4, 5, 6, 7] i := by
  apply Fin.ext
  fin_cases i <;> rfl

private theorem neTgt1_eq (i : Fin 5) :
    (⟨neTgt1[i.val]!, by fin_cases i <;> decide⟩ : Fin 8) = ![5, 2, 3, 3, 2] i := by
  apply Fin.ext
  fin_cases i <;> rfl

private theorem ofFn_getElem!_nat {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) (i : ℕ)
    (h : i < n) : (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos _ _ (by simpa using h)]
  simp

private theorem isRows_E1E8 (l : Fin 8) :
    IsRows ((Array.ofFn fun l : Fin 8 => mulRows rowsE1M (rowsE8TM[l.val]!))[l]!)
      (((e₁ * e8 l : ↥Max3.M) : J)) := by
  rw [show (Array.ofFn fun l : Fin 8 => mulRows rowsE1M (rowsE8TM[l.val]!))[l]! =
    (Array.ofFn fun l : Fin 8 => mulRows rowsE1M (rowsE8TM[l.val]!))[l.val]! from rfl]
  rw [ofFn_getElem!_nat (fun l : Fin 8 => mulRows rowsE1M (rowsE8TM[l.val]!)) l.val l.isLt]
  exact isRows_e₁.mul (isRows_e8Tab l)

private theorem check_N_sound (i : Fin 5) :
    nE i * tLetter = tLetter * nE i ∧
      nE i * e₀ * (nE i)⁻¹ = e8 (![3, 4, 5, 6, 7] i) ∧
      nE i * e₁ * (nE i)⁻¹ = e8 (![5, 2, 3, 3, 2] i) := by
  have h := check_spec.2.2.1
  simp only [checkN687011, List.all_eq_true, List.mem_finRange, true_implies] at h
  have hi := h i
  simp only [Bool.and_eq_true] at hi
  have hcomm : commR (rowsNETM[i]!) (rowsWJ 6) = true := hi.1.1
  have hconj0 : eqRows (mulRows (rowsNETM[i]!) rowsE0M)
      (mulRows (rowsE8TM[neTgt0[i.val]!]!) (rowsNETM[i]!)) = true := hi.1.2
  have hconj1 : eqRows (mulRows (rowsNETM[i]!) rowsE1M)
      (mulRows (rowsE8TM[neTgt1[i.val]!]!) (rowsNETM[i]!)) = true := hi.2
  refine ⟨Subtype.ext (eq_of_commR (isRows_nE i) isRows_tLetter hcomm), ?_, ?_⟩
  · let l : Fin 8 := ⟨neTgt0[i.val]!, by fin_cases i <;> decide⟩
    have hJ : ((nE i : ↥Max3.M) : J) * ((e₀ : ↥Max3.M) : J) =
        ((e8 l : ↥Max3.M) : J) * ((nE i : ↥Max3.M) : J) :=
      IsRows.eq_of_eqRows ((isRows_nE i).mul isRows_e₀)
        ((isRows_e8Tab l).mul (isRows_nE i)) hconj0
    have hM : nE i * e₀ = e8 l * nE i := Subtype.ext hJ
    have he8 : e8 l = e8 (![3, 4, 5, 6, 7] i) := by
      apply congrArg e8
      exact neTgt0_eq i
    calc nE i * e₀ * (nE i)⁻¹ = (e8 l * nE i) * (nE i)⁻¹ := by rw [hM]
      _ = e8 l := by group
      _ = e8 (![3, 4, 5, 6, 7] i) := he8
  · let l : Fin 8 := ⟨neTgt1[i.val]!, by fin_cases i <;> decide⟩
    have hJ : ((nE i : ↥Max3.M) : J) * ((e₁ : ↥Max3.M) : J) =
        ((e8 l : ↥Max3.M) : J) * ((nE i : ↥Max3.M) : J) :=
      IsRows.eq_of_eqRows ((isRows_nE i).mul isRows_e₁)
        ((isRows_e8Tab l).mul (isRows_nE i)) hconj1
    have hM : nE i * e₁ = e8 l * nE i := Subtype.ext hJ
    have he8 : e8 l = e8 (![5, 2, 3, 3, 2] i) := by
      apply congrArg e8
      exact neTgt1_eq i
    calc nE i * e₁ * (nE i)⁻¹ = (e8 l * nE i) * (nE i)⁻¹ := by rw [hM]
      _ = e8 l := by group
      _ = e8 (![5, 2, 3, 3, 2] i) := he8

private theorem check_C_spec :
    (∀ i : Fin 7, cE i * cEI i = 1 ∧ cE i * e₀ = e₀ * cE i) ∧
      (∀ j : Fin 6, cN j * cNI j = 1 ∧ cN j * e₀ = e₀ * cN j) := by
  have h := check_spec.2.2.2.2.1
  simp only [checkC687011, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true] at h
  refine ⟨fun i => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    exact IsRows.eq_of_eqRows ((isRows_cE i).mul (isRows_cEI i)) IsRows.one (h.1 i).1
  · apply Subtype.ext
    exact eq_of_commR (isRows_cE i) isRows_e₀ (h.1 i).2
  · apply Subtype.ext
    exact IsRows.eq_of_eqRows ((isRows_cN j).mul (isRows_cNI j)) IsRows.one (h.2 j).1
  · apply Subtype.ext
    exact eq_of_commR (isRows_cN j) isRows_e₀ (h.2 j).2

private theorem cEI_eq_inv (i : Fin 7) : cEI i = (cE i)⁻¹ :=
  eq_inv_of_mul_eq_one_right (check_C_spec.1 i).1

private theorem cNI_eq_inv (j : Fin 6) : cNI j = (cN j)⁻¹ :=
  eq_inv_of_mul_eq_one_right (check_C_spec.2 j).1

private theorem commR_of_commute {X Y : Array V4} {g h : J} (hX : IsRows X g)
    (hY : IsRows Y h) (hgh : g * h = h * g) : commR X Y = true := by
  rw [commR, eqRows_iff]
  have hS : IsRows (mulRows Y X) (g * h) := by
    rw [hgh]
    exact hY.mul hX
  exact (hX.mul hY).rows_eq hS

private theorem check_CE_sound {q : ↥Max3.M} (hq : (q : J) ∈ Max3.Q)
    (hqt : q * tLetter = tLetter * q) (a : Fin 18)
    (h₀ : pre a * q * e₀ = e₀ * (pre a * q))
    (h₁ : pre a * q * e₁ = e₁ * (pre a * q)) :
    a = 0 ∧ ∃ l : Fin 8, q = e8 l := by
  obtain ⟨k, hk⟩ := Max3.InvRep.exists_nfAt_eq hq
  have hnf : IsRows (rowsNfTab[k]!) (q : J) := by
    change IsRows (rowsNfTab[k.val]!) (q : J)
    rw [rowsNfTab_get, ← hk]
    exact isRows_nfAt k
  have hqtJ : (q : J) * (tLetter : J) = (tLetter : J) * (q : J) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hqt
  have hcommT : commR (rowsNfTab[k]!) (rowsWJ 6) = true :=
    commR_of_commute hnf isRows_tLetter hqtJ
  have hCE := check_spec.2.2.2.1
  simp only [checkCE687011] at hCE
  have hkall := List.all_eq_true.mp hCE k (List.mem_finRange k)
  simp only [hcommT, Bool.not_true, Bool.false_or] at hkall
  have ha := List.all_eq_true.mp hkall a (List.mem_finRange a)
  set P : Array V4 := mulRows (rowsPreTM[a]!) (rowsNfTab[k]!) with hPdef
  have hP : IsRows P (((pre a : ↥Max3.M) : J) * (q : J)) := by
    rw [hPdef]
    exact (isRows_preTab a).mul hnf
  have h₀J : ((pre a : ↥Max3.M) : J) * (q : J) * (e₀ : J) =
      (e₀ : J) * (((pre a : ↥Max3.M) : J) * (q : J)) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val h₀
  have h₁J : ((pre a : ↥Max3.M) : J) * (q : J) * (e₁ : J) =
      (e₁ : J) * (((pre a : ↥Max3.M) : J) * (q : J)) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val h₁
  have hPE0 : commR P (rowsE0 (rowsWJ 2) (rowsWJ 3)) = true :=
    commR_of_commute hP isRows_e₀ h₀J
  have hPE1 : commR P (rowsE1 (rowsWJ 7) (rowsE0 (rowsWJ 2) (rowsWJ 3))
      (rowsUI (rowsWJ 7))) = true := commR_of_commute hP isRows_e₁ h₁J
  simp only [hPE0, hPE1, Bool.and_true, Bool.not_true, Bool.false_or] at ha
  rw [Bool.and_eq_true] at ha
  obtain ⟨ha0, hal⟩ := ha
  have ha0' : a = 0 := of_decide_eq_true ha0
  obtain ⟨l, -, hrows⟩ := List.any_eq_true.mp hal
  exact ⟨ha0', l, Subtype.ext (IsRows.eq_of_eqRows hnf (isRows_e8Tab l) hrows)⟩

private theorem check_A_first {q : ↥Max3.M} {k : Fin 512}
    (hnf : IsRows (rowsNfTab[k]!) (q : J))
    (h : (List.finRange 4).any (fun l : Fin 4 =>
      eqRows (rowsNfTab[k]!) (rowsE8TM[l]!)) = true) :
    ∃ l : Fin 8, l.val < 4 ∧ q = e8 l := by
  obtain ⟨l, -, hrows⟩ := List.any_eq_true.mp h
  let l8 : Fin 8 := ⟨l.val, by omega⟩
  exact ⟨l8, l.isLt, Subtype.ext (IsRows.eq_of_eqRows hnf (isRows_e8Tab l8) hrows)⟩

private theorem check_A_second {q : ↥Max3.M} {k : Fin 512}
    (hnf : IsRows (rowsNfTab[k]!) (q : J))
    (h : (List.finRange 6).any (fun j : Fin 6 =>
      !commR (mulRows (mulRows (rowsCNTM[j]!) (rowsNfTab[k]!)) (rowsCNITM[j]!))
        (rowsNfTab[k]!)) = true) :
    ∃ j : Fin 6, cN j * q * (cN j)⁻¹ * q ≠ q * (cN j * q * (cN j)⁻¹) := by
  obtain ⟨j, -, hnc⟩ := List.any_eq_true.mp h
  have hnc' : commR (mulRows (mulRows (rowsCNTM[j]!) (rowsNfTab[k]!))
      (rowsCNITM[j]!)) (rowsNfTab[k]!) = false := by
    simpa only [Bool.not_eq_true'] using hnc
  have hneJ : (((cN j : ↥Max3.M) : J) * (q : J) * ((cNI j : ↥Max3.M) : J)) *
      (q : J) ≠ (q : J) *
        (((cN j : ↥Max3.M) : J) * (q : J) * ((cNI j : ↥Max3.M) : J)) :=
    ne_of_commR (((isRows_cN j).mul hnf).mul (isRows_cNI j)) hnf hnc'
  have hcNIJ : ((cNI j : ↥Max3.M) : J) = (((cN j)⁻¹ : ↥Max3.M) : J) :=
    congrArg Subtype.val (cNI_eq_inv j)
  rw [hcNIJ] at hneJ
  refine ⟨j, ?_⟩
  intro hEq
  exact hneJ (by simpa only [Subgroup.coe_mul] using congrArg Subtype.val hEq)

private theorem check_A_third {q : ↥Max3.M} {k : Fin 512}
    (hnf : IsRows (rowsNfTab[k]!) (q : J))
    (h : (List.finRange 7).any (fun i : Fin 7 =>
      (List.finRange 4).any fun l : Fin 4 =>
        eqRows (mulRows (mulRows (rowsCETM[i]!) (rowsNfTab[k]!)) (rowsCEITM[i]!))
          ((Array.ofFn fun l : Fin 8 => mulRows rowsE1M (rowsE8TM[l.val]!))[l]!)) = true) :
    ∃ (i : Fin 7) (l : Fin 8), l.val < 4 ∧ cE i * q * (cE i)⁻¹ = e₁ * e8 l := by
  obtain ⟨i, -, hi⟩ := List.any_eq_true.mp h
  obtain ⟨l, -, hrows⟩ := List.any_eq_true.mp hi
  let l8 : Fin 8 := ⟨l.val, by omega⟩
  have hleft : IsRows (mulRows (mulRows (rowsCETM[i]!) (rowsNfTab[k]!))
      (rowsCEITM[i]!)) (((cE i : ↥Max3.M) : J) * (q : J) * ((cEI i : ↥Max3.M) : J)) :=
    ((isRows_cE i).mul hnf).mul (isRows_cEI i)
  have hright : IsRows ((Array.ofFn fun l : Fin 8 =>
      mulRows rowsE1M (rowsE8TM[l.val]!))[l]!)
      (((e₁ * e8 l8 : ↥Max3.M) : J)) := isRows_E1E8 l8
  have heqJ := IsRows.eq_of_eqRows hleft hright hrows
  have hcEIJ : ((cEI i : ↥Max3.M) : J) = (((cE i)⁻¹ : ↥Max3.M) : J) :=
    congrArg Subtype.val (cEI_eq_inv i)
  refine ⟨i, l8, l.isLt, ?_⟩
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, hcEIJ] using heqJ

private theorem check_A_sound {q : ↥Max3.M} (hq : (q : J) ∈ Max3.Q)
    (h : q * e₀ = e₀ * q) :
    (∃ l : Fin 8, l.val < 4 ∧ q = e8 l) ∨
      (∃ j : Fin 6, cN j * q * (cN j)⁻¹ * q ≠ q * (cN j * q * (cN j)⁻¹)) ∨
      ∃ (i : Fin 7) (l : Fin 8), l.val < 4 ∧ cE i * q * (cE i)⁻¹ = e₁ * e8 l := by
  obtain ⟨k, hk⟩ := Max3.InvRep.exists_nfAt_eq hq
  have hnf : IsRows (rowsNfTab[k]!) (q : J) := by
    change IsRows (rowsNfTab[k.val]!) (q : J)
    rw [rowsNfTab_get, ← hk]
    exact isRows_nfAt k
  have hJ : (q : J) * (e₀ : J) = (e₀ : J) * (q : J) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val h
  have hcommE0 : commR (rowsNfTab[k]!) rowsE0M = true :=
    commR_of_commute hnf isRows_e₀ hJ
  have hA := check_spec.2.2.2.2.2
  simp only [checkA687011] at hA
  have hkall := List.all_eq_true.mp hA k (List.mem_finRange k)
  simp only [hcommE0, Bool.not_true, Bool.false_or] at hkall
  simp only [Bool.or_eq_true] at hkall
  rcases hkall with h12 | hthird
  · rcases h12 with hfirst | hsecond
    · exact Or.inl (check_A_first hnf hfirst)
    · exact Or.inr (Or.inl (check_A_second hnf hsecond))
  · exact Or.inr (Or.inr (check_A_third hnf hthird))

theorem y₁_mul_x₁ : y₁ * x₁ = x₁ ^ 3 * y₁ := check_R_sound.1

theorem ω₁_mul_y₁ : ω₁ * y₁ = y₁ * x₁ * ω₁ := check_R_sound.2.1

theorem x₁_comm_x₂ : x₁ * x₂ = x₂ * x₁ := check_R_sound.2.2.1

theorem x₁_comm_ω₂ : x₁ * ω₂ = ω₂ * x₁ := check_R_sound.2.2.2.1

theorem ω₁_comm_x₂ : ω₁ * x₂ = x₂ * ω₁ := check_R_sound.2.2.2.2.1

theorem ω₁_comm_ω₂ : ω₁ * ω₂ = ω₂ * ω₁ := check_R_sound.2.2.2.2.2

theorem e₀_comm_e₁ : e₀ * e₁ = e₁ * e₀ := check_E_sound.1

theorem e8_injective : Function.Injective e8 := check_E_sound.2

theorem nE_comm_tLetter (i : Fin 5) : nE i * tLetter = tLetter * nE i :=
  (check_N_sound i).1

theorem nE_conj_e₀ (i : Fin 5) :
    nE i * e₀ * (nE i)⁻¹ = e8 (![3, 4, 5, 6, 7] i) :=
  (check_N_sound i).2.1

theorem nE_conj_e₁ (i : Fin 5) :
    nE i * e₁ * (nE i)⁻¹ = e8 (![5, 2, 3, 3, 2] i) :=
  (check_N_sound i).2.2

theorem eq_e8_of_commute_pre_mul {q : ↥Max3.M} (hq : (q : J) ∈ Max3.Q)
    (hqt : q * tLetter = tLetter * q) (a : Fin 18)
    (h₀ : pre a * q * e₀ = e₀ * (pre a * q)) (h₁ : pre a * q * e₁ = e₁ * (pre a * q)) :
    a = 0 ∧ ∃ l : Fin 8, q = e8 l :=
  check_CE_sound hq hqt a h₀ h₁

theorem cE_comm_e₀ (i : Fin 7) : cE i * e₀ = e₀ * cE i :=
  (check_C_spec.1 i).2

theorem cN_comm_e₀ (j : Fin 6) : cN j * e₀ = e₀ * cN j :=
  (check_C_spec.2 j).2

theorem of_commute_e₀ {q : ↥Max3.M} (hq : (q : J) ∈ Max3.Q) (h : q * e₀ = e₀ * q) :
    (∃ l : Fin 8, l.val < 4 ∧ q = e8 l) ∨
      (∃ j : Fin 6, cN j * q * (cN j)⁻¹ * q ≠ q * (cN j * q * (cN j)⁻¹)) ∨
      ∃ (i : Fin 7) (l : Fin 8), l.val < 4 ∧ cE i * q * (cE i)⁻¹ = e₁ * e8 l :=
  check_A_sound hq h

end CFSG.Sporadic.Th.Recog.MFactsB
