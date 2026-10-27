module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocClass
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocQ

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

@[expose] def D4O (v : D) : Prop := v ∈ d4Q ∧ v * v = 1 ∧ v ≠ 1 ∧ ¬ IsConj d4z v

section Norm


theorem D4O.conj {h v : D} (hh : h ∈ d4H) (hv : D4O v) : D4O (h * v * h⁻¹) := by
  obtain ⟨hvQ, hv2, hv1, hvc⟩ := hv
  refine ⟨d4H_norm_Q h hh v hvQ, ?_, ?_, ?_⟩
  · calc h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  · intro h1
    apply hv1
    calc v = h⁻¹ * (h * v * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  · intro hc
    exact hvc (hc.trans (isConj_iff.2 ⟨h⁻¹, by group⟩))

end Norm

section Model


theorem D4O.exists_comm {v : D} (hv : D4O v) :
    ∃ t ∈ d4U, t * v * t⁻¹ * v⁻¹ ≠ 1 ∧ t * v * t⁻¹ * v⁻¹ ≠ d4z := by
  obtain ⟨hvQ, hv2, hv1, hvc⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, -, -, h9, -⟩ := locQ_parts
  obtain ⟨i, hi, hrep⟩ := exists_mem_Q hvQ
  have hval := validR_Q hi
  have hinv : locIsInv locEQ.El[i]! = true := (locIsInv_iff hval hrep).2 ⟨hv2, hv1⟩
  have hmem : memR locCz.T locCz.idx locEQ.El[i]! = false := by
    rw [locCz_eq, Bool.eq_false_iff]
    exact fun h => hvc ((memR_cz_iff hval hrep).1 h)
  have h := allLt_spec h9 hi
  simp only [hinv, hmem, Bool.not_true, Bool.false_or, Bool.or_false, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨k, hk, hs1, hs2⟩ := h
  have hg := repE_uGens hk
  have hu := validR_uGens hk
  have huy : validR (mulR uGens[k]! locEQ.El[i]!) = true := validR_mulR (size_of_validR hu) hval
  have hs : validR (mulR (mulR uGens[k]! locEQ.El[i]!) (mulR uGens[k]! locEQ.El[i]!)) = true :=
    validR_mulR (size_of_validR huy) huy
  have hrs := repE_mul (repE_mul hg hrep) (repE_mul hg hrep)
  have hginv : (uGH k)⁻¹ = uGH k := inv_eq_of_mul_eq_one_right (uGens_hyp' k hk).2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have e : uGH k * v * (uGH k)⁻¹ * v⁻¹ = uGH k * v * (uGH k * v) := by
    rw [hginv, hvinv, mul_assoc (uGH k * v) (uGH k) v]
  refine ⟨uGH k, gen_mem_U hk, ?_, ?_⟩ <;> rw [e]
  · exact fun h => hs1 ((eqOneR_iff hs hrs).2 h)
  · exact fun h => hs2 ((eq_iff_of_repE hs validR_z0R hrs repE_z0R).2 h)

theorem d4_hpair : ∃ v, D4O v ∧ ∃ a ∈ d4Q, ∃ b ∈ d4Q, a * v = v * a ∧ b * v = v * b ∧
    a * b * a⁻¹ * b⁻¹ = d4z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hW⟩ := locQ_parts
  generalize locPairWit locCz locEQ = w at hW
  obtain ⟨iv, ia, ib⟩ := w
  simp only [locPairWitOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true'] at hW
  obtain ⟨⟨⟨⟨⟨⟨⟨hiv, hia⟩, hib⟩, hinv⟩, hmem⟩, hca⟩, hcb⟩, hab⟩ := hW
  obtain ⟨v, hvQ, hvrep⟩ := exists_of_Q hiv
  obtain ⟨a, haQ, harep⟩ := exists_of_Q hia
  obtain ⟨b, hbQ, hbrep⟩ := exists_of_Q hib
  have hvval := validR_Q hiv
  have hinv' := (locIsInv_iff hvval hvrep).1 hinv
  refine ⟨v, ⟨hvQ, hinv'.1, hinv'.2, fun hc => ?_⟩, a, haQ, b, hbQ,
    (locComm_iff (validR_Q hia) hvval harep hvrep).1 hca,
    (locComm_iff (validR_Q hib) hvval hbrep hvrep).1 hcb, ?_⟩
  · have := (memR_cz_iff hvval hvrep).2 hc
    rw [← locCz_eq] at this
    rw [this] at hmem
    exact absurd hmem (by simp)
  · have e : a * b = d4z * (b * a) := eq_of_repE d4E_injective (repE_mul harep hbrep)
      (hab ▸ repE_mul repE_z0R (repE_mul hbrep harep))
    rw [e]
    group

end Model

end CFSG.Quasithin.D4Hex
