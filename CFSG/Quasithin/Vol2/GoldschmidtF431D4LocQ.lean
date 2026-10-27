module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocCt
public import CFSG.LargeExtraspecial.S63CD4AData
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocT

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem mul_eq_of_arr {X Y Z : Array ℕ} {x y z : D} (hx : RepE d4E X x) (hy : RepE d4E Y y)
    (hz : RepE d4E Z z) (h : mulR X Y = Z) : x * y = z := by
  refine eq_of_repE d4E_injective (repE_mul hx hy) ?_
  rw [h]
  exact hz

section Cert


theorem locQ_parts : gensOK qGens = true ∧
    enumOK qGens locEQ.El locEQ.P locEQ.K locEQ.idx = true ∧ locEQ.El.size = 512 ∧
    locET.invOK 4096 = true ∧
    (allLt locEQ.El.size fun i => (List.range qGens.size).all fun k =>
      mulR locEQ.El[i]! qGens[k]! == mulR qGens[k]! locEQ.El[i]! ||
        mulR locEQ.El[i]! qGens[k]! == mulR z0R (mulR qGens[k]! locEQ.El[i]!)) = true ∧
    (allLt locEQ.El.size fun i =>
      mulR locEQ.El[i]! locEQ.El[i]! == oneR || mulR locEQ.El[i]! locEQ.El[i]! == z0R) = true ∧
    (allLt locEQ.El.size fun i =>
      !((List.range qGens.size).all fun k => locComm locEQ.El[i]! qGens[k]!) ||
        locEQ.El[i]! == oneR || locEQ.El[i]! == z0R) = true ∧
    ((List.range qGens.size).all fun k => memR locET.El locET.idx qGens[k]!) = true ∧
    (allLt locET.El.size fun i => (List.range uGens.size).all fun k =>
      memR locEQ.El locEQ.idx
        (mulR (mulR locET.El[i]! uGens[k]!) (mulR locET.El[locET.inv[i]!]! uGens[k]!))) = true ∧
    (allLt locEQ.El.size fun i =>
      !(locIsInv locEQ.El[i]!) || memR locCz.T locCz.idx locEQ.El[i]! ||
        (List.range uGens.size).any fun k =>
          !(mulR (mulR uGens[k]! locEQ.El[i]!) (mulR uGens[k]! locEQ.El[i]!) == oneR) &&
            !(mulR (mulR uGens[k]! locEQ.El[i]!) (mulR uGens[k]! locEQ.El[i]!) == z0R)) = true ∧
    locPairWitOK locCz locEQ (locPairWit locCz locEQ) = true := by
  have h := loc_parts.2.2.2.2.2
  simp only [locQCheck, Bool.and_eq_true, EnumData.ok, beq_iff_eq, and_assoc] at h
  exact h

theorem validR_qGens {k : ℕ} (hk : k < qGens.size) : validR qGens[k]! = true := by
  rw [qGens_size] at hk
  rw [qGens_getElem hk]
  exact validR_d4Word (qWords_lt hk)

theorem qGens_hyp' : ∀ k < qGens.size, RepE d4E qGens[k]! (qGH k) ∧ qGH k * qGH k = 1 :=
  mul_self_of_gensOK (fun _ hk => repE_qGens hk) locQ_parts.1

theorem exists_mem_Q {x : D} (hx : x ∈ d4Q) : ∃ i < locEQ.El.size, RepE d4E locEQ.El[i]! x :=
  exists_mem_of_enumOK qGens_hyp' locQ_parts.2.1 hx

theorem exists_of_Q {i : ℕ} (hi : i < locEQ.El.size) : ∃ a ∈ d4Q, RepE d4E locEQ.El[i]! a :=
  exists_of_enumOK (fun _ hk => (qGens_hyp' _ hk).1) locQ_parts.2.1 i hi

theorem validR_Q {i : ℕ} (hi : i < locEQ.El.size) : validR locEQ.El[i]! = true :=
  ((enumOK_parts locQ_parts.2.1).2.2 i hi).1

theorem memR_of_mem_Q {y : Array ℕ} {x : D} (hv : validR y = true) (hy : RepE d4E y x)
    (hx : x ∈ d4Q) : memR locEQ.El locEQ.idx y = true := by
  obtain ⟨i, hi, hrep⟩ := exists_mem_Q hx
  have heq : locEQ.El[i]! = y := arr_eq_of_repE (validR_Q hi) hv hrep hy
  have hidx := ((enumOK_parts locQ_parts.2.1).2.2 i hi).2.1
  rw [← heq]
  unfold memR
  rw [hidx]
  simp [hi]

theorem mem_Q_of_memR {y : Array ℕ} (hm : memR locEQ.El locEQ.idx y = true) :
    ∃ x ∈ d4Q, RepE d4E y x := by
  obtain ⟨hlt, heq⟩ := memR_spec hm
  obtain ⟨a, ha, hrep⟩ := exists_of_Q hlt
  rw [heq] at hrep
  exact ⟨a, ha, hrep⟩

theorem qGH_mem_d4U {k : ℕ} (hk : k < qGens.size) : qGH k ∈ d4U := by
  obtain ⟨-, -, -, -, -, -, -, h7, -⟩ := locQ_parts
  have hm := List.all_eq_true.1 h7 k (List.mem_range.2 hk)
  obtain ⟨hlt, heq⟩ := memR_spec hm
  obtain ⟨a, ha, hrep⟩ := exists_of_T hlt
  rw [heq] at hrep
  rw [eq_of_repE d4E_injective (repE_qGens hk) hrep]
  exact ha

theorem d4Q_le_d4U : d4Q ≤ d4U := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact qGH_mem_d4U hk

theorem d4t_mem_d4Q : d4t ∈ d4Q := by
  obtain ⟨a, ha, hrep⟩ := mem_Q_of_memR locF_parts.2.2.2.1
  rw [eq_of_repE d4E_injective repE_t0R hrep]
  exact ha

end Cert

section Norm


theorem d4H_norm_Q : ∀ h ∈ d4H, ∀ q ∈ d4Q, h * q * h⁻¹ ∈ d4Q := by
  intro h hh q hq
  obtain ⟨q0, hq0, l, hl, rfl⟩ := exists_of_mem_centralizer_d4z hh
  have h1 := d4Q.mul_mem (d4Q.mul_mem hq0 (d4L_normalizes l hl q hq)) (d4Q.inv_mem hq0)
  rwa [show q0 * l * q * (q0 * l)⁻¹ = q0 * (l * q * l⁻¹) * q0⁻¹ by group]

end Norm

end CFSG.Quasithin.D4Hex
