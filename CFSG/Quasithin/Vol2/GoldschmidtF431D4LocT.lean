module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocBase

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem validR_uGens {k : ℕ} (hk : k < uGens.size) : validR uGens[k]! = true := by
  rw [uGens_size] at hk
  rw [uGens_getElem hk]
  exact validR_d4Gens (uIdx_lt hk)

theorem gen_mem_U {k : ℕ} (hk : k < uGens.size) : uGH k ∈ d4U :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem d4GenG_mem_U {k : ℕ} (hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 6) : d4GenG k ∈ d4U := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact gen_mem_U (k := 0) (by rw [uGens_size]; decide)
  · exact gen_mem_U (k := 1) (by rw [uGens_size]; decide)
  · exact gen_mem_U (k := 2) (by rw [uGens_size]; decide)
  · exact gen_mem_U (k := 3) (by rw [uGens_size]; decide)

theorem d4Word_mem_U : ∀ w : List ℕ, (∀ k ∈ w, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 6) → d4Word w ∈ d4U
  | [], _ => by simp [d4Word]
  | k :: w, hw => by
    rw [d4Word_cons]
    exact d4U.mul_mem (d4GenG_mem_U (hw k List.mem_cons_self))
      (d4Word_mem_U w fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))

theorem d4z_mem_d4U : d4z ∈ d4U := d4Word_mem_U wordZ (by decide)

theorem d4t_mem_d4U : d4t ∈ d4U := d4Word_mem_U wordT (by decide)

section Cert


theorem locT_parts : gensOK uGens = true ∧
    (enumOK uGens locET.El locET.P locET.K locET.idx = true ∧ locET.El.size = 4096) ∧
    locIsInv z0R = true ∧ locIsInv t0R = true ∧
    (allLt locET.El.size fun i =>
      !((List.range uGens.size).all fun k => locComm locET.El[i]! uGens[k]!) ||
        locET.El[i]! == oneR || locET.El[i]! == z0R) = true ∧
    locInvChain locET = true := by
  have h := loc_parts.2.2.1
  simp only [locTCheck, Bool.and_eq_true, EnumData.ok, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem uGens_hyp' : ∀ k < uGens.size, RepE d4E uGens[k]! (uGH k) ∧ uGH k * uGH k = 1 :=
  mul_self_of_gensOK (fun _ hk => repE_uGens hk) locT_parts.1

theorem exists_mem_T {x : D} (hx : x ∈ d4U) : ∃ i < locET.El.size, RepE d4E locET.El[i]! x :=
  exists_mem_of_enumOK uGens_hyp' locT_parts.2.1.1 hx

theorem exists_of_T {i : ℕ} (hi : i < locET.El.size) : ∃ a ∈ d4U, RepE d4E locET.El[i]! a :=
  exists_of_enumOK (fun _ hk => (uGens_hyp' _ hk).1) locT_parts.2.1.1 i hi

theorem validR_T {i : ℕ} (hi : i < locET.El.size) : validR locET.El[i]! = true :=
  ((enumOK_parts locT_parts.2.1.1).2.2 i hi).1

theorem card_d4U' : Nat.card d4U = 4096 := by
  have := card_of_enumOK d4E_injective uGens_hyp' locT_parts.2.1.1
  rw [locT_parts.2.1.2] at this
  exact this

theorem d4z_sq : d4z * d4z = 1 ∧ d4z ≠ 1 :=
  (locIsInv_iff validR_z0R repE_z0R).1 locT_parts.2.2.1

theorem d4t_sq : d4t * d4t = 1 ∧ d4t ≠ 1 :=
  (locIsInv_iff validR_t0R repE_t0R).1 locT_parts.2.2.2.1

theorem orderOf_d4z : orderOf d4z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact d4z_sq.1) d4z_sq.2

theorem orderOf_d4t : orderOf d4t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact d4t_sq.1) d4t_sq.2

theorem center_T_spec {w : D} (hw : w ∈ d4U) (hc : ∀ y ∈ d4U, y * w = w * y) (hw1 : w ≠ 1) :
    w = d4z := by
  obtain ⟨i, hi, hrep⟩ := exists_mem_T hw
  have hval := validR_T hi
  have h5 := allLt_spec locT_parts.2.2.2.2.1 hi
  have hall : ((List.range uGens.size).all fun k => locComm locET.El[i]! uGens[k]!) = true := by
    simp only [List.all_eq_true, List.mem_range]
    intro k hk
    rw [locComm_iff hval (validR_uGens hk) hrep (repE_uGens hk)]
    exact (hc (uGH k) (gen_mem_U hk)).symm
  simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h5
  rcases h5 with h5 | h5
  · exact absurd ((eqOneR_iff hval hrep).1 h5) hw1
  · exact eq_of_repE d4E_injective hrep (h5 ▸ repE_z0R)

end Cert

section Model


theorem d4U_le_d4B : d4U ≤ d4B := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < 4 := by simpa [uGens_size] using hk
  apply gen_mem_B
  interval_cases k <;> simp [uIdx]

end Model

end CFSG.Quasithin.D4Hex
