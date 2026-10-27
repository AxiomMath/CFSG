module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocQ

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

abbrev pt1 : Fin 819 := ⟨1, by norm_num⟩

abbrev pt5 : Fin 819 := ⟨5, by norm_num⟩

section Model

@[expose] noncomputable def vB : D := zElt pt1

@[expose] noncomputable def vC : D := zElt pt5

theorem repE_vB : RepE d4E cz.T[1]! vB := repE_zElt pt1

theorem repE_vC : RepE d4E cz.T[5]! vC := repE_zElt pt5

theorem validR_vB : validR cz.T[1]! = true := validR_cz (by norm_num)

theorem validR_vC : validR cz.T[5]! = true := validR_cz (by norm_num)

section Cert

theorem vB_sq : vB * vB = 1 ∧ vB ≠ 1 := by
  have h := locV_parts.2.2.2.2.2.1
  rw [locCz_eq] at h
  exact (locIsInv_iff validR_vB repE_vB).1 h

theorem vC_sq : vC * vC = 1 ∧ vC ≠ 1 := by
  have h := locV_parts.2.2.2.2.2.2.1
  rw [locCz_eq] at h
  exact (locIsInv_iff validR_vC repE_vC).1 h

theorem d4V_rels : d4z * vB = vC ∧ vB * d4z = vC ∧ d4z * vC = vB ∧ vC * d4z = vB ∧
    vB * vC = d4z ∧ vC * vB = d4z := by
  obtain ⟨-, -, -, -, -, -, -, h1, h2, h3, h4, h5, h6, -⟩ := locV_parts
  simp only [locCz_eq] at h1 h2 h3 h4 h5 h6
  exact ⟨mul_eq_of_arr repE_z0R repE_vB repE_vC h1, mul_eq_of_arr repE_vB repE_z0R repE_vC h2,
    mul_eq_of_arr repE_z0R repE_vC repE_vB h3, mul_eq_of_arr repE_vC repE_z0R repE_vB h4,
    mul_eq_of_arr repE_vB repE_vC repE_z0R h5, mul_eq_of_arr repE_vC repE_vB repE_z0R h6⟩

@[expose] noncomputable def d4V : Subgroup D := Subgroup.closure ({d4z, vB, vC} : Set D)

theorem vA_ne_vB : d4z ≠ vB := by
  intro h
  have := zElt_injective (show zElt pt0 = zElt pt1 by rw [zElt_zero]; exact h)
  exact absurd (congrArg Fin.val this) (by norm_num)

theorem vA_ne_vC : d4z ≠ vC := by
  intro h
  have := zElt_injective (show zElt pt0 = zElt pt5 by rw [zElt_zero]; exact h)
  exact absurd (congrArg Fin.val this) (by norm_num)

theorem vB_ne_vC : vB ≠ vC := by
  intro h
  have := zElt_injective (show zElt pt1 = zElt pt5 from h)
  exact absurd (congrArg Fin.val this) (by norm_num)

theorem mem_d4V_iff {x : D} : x ∈ d4V ↔ x = 1 ∨ x = d4z ∨ x = vB ∨ x = vC := by
  obtain ⟨hAB, hBA, hAC, hCA, hBC, hCB⟩ := d4V_rels
  have hAA := d4z_sq.1
  have hBB := vB_sq.1
  have hCC := vC_sq.1
  let S : Subgroup D :=
    { carrier := {x | x = 1 ∨ x = d4z ∨ x = vB ∨ x = vC}
      mul_mem' := fun {a b} ha hb => by
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hAA, hBB, hCC, hAB, hBA, hAC, hCA, hBC, hCB]
      one_mem' := Or.inl rfl
      inv_mem' := fun {a} ha => by
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · simp [inv_eq_of_mul_eq_one_right hAA]
        · simp [inv_eq_of_mul_eq_one_right hBB]
        · simp [inv_eq_of_mul_eq_one_right hCC] }
  constructor
  · intro hx
    have hle : d4V ≤ S := (Subgroup.closure_le S).2 (by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl)))
    exact hle hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact d4V.one_mem
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
    · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem card_d4V : Nat.card d4V = 4 := by
  have h1 : d4z ≠ 1 := d4z_sq.2
  have h2 : vB ≠ 1 := vB_sq.2
  have h3 : vC ≠ 1 := vC_sq.2
  have hset : (d4V : Set D) = {1, d4z, vB, vC} := by
    ext x
    simp only [SetLike.mem_coe, mem_d4V_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  have e : Nat.card d4V = (d4V : Set D).ncard := Nat.card_coe_set_eq (d4V : Set D)
  rw [e, hset,
    Set.ncard_insert_of_notMem (by simp [h1.symm, h2.symm, h3.symm]) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by simp [vA_ne_vB, vA_ne_vC]) (Set.toFinite _),
    Set.ncard_pair vB_ne_vC]

theorem d4V_comm : ∀ a ∈ d4V, ∀ b ∈ d4V, a * b = b * a := by
  obtain ⟨hAB, hBA, hAC, hCA, hBC, hCB⟩ := d4V_rels
  intro a ha b hb
  rw [mem_d4V_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp [hAB, hBA, hAC, hCA, hBC, hCB]

theorem d4V_sq : ∀ a ∈ d4V, a ^ 2 = 1 := by
  intro a ha
  rw [mem_d4V_iff] at ha
  rw [pow_two]
  rcases ha with rfl | rfl | rfl | rfl
  · simp
  · exact d4z_sq.1
  · exact vB_sq.1
  · exact vC_sq.1

theorem d4V_le_centralizer : d4V ≤ Subgroup.centralizer ({d4t} : Set D) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ct0, ct1, ct5, -⟩ := locV_parts
  simp only [locCz_eq] at ct1 ct5
  intro x hx
  rw [mem_d4V_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · exact (locComm_of_eq repE_t0R repE_z0R ct0).symm
  · exact (locComm_of_eq repE_t0R repE_vB ct1).symm
  · exact (locComm_of_eq repE_t0R repE_vC ct5).symm

theorem conj_gen_mem_V {k : ℕ} (hk : k < cGens.size) :
    ∀ v ∈ d4V, cGH k * v * (cGH k)⁻¹ ∈ d4V := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnorm, -⟩ := locV_parts
  simp only [locCz_eq] at hnorm
  have hinv : (cGH k)⁻¹ = cGH k := inv_eq_of_mul_eq_one_right (cGens_hyp' k hk).2
  have hrep := repE_cGens hk
  have hrep' : RepE d4E cGens[k]! (cGH k)⁻¹ := by rw [hinv]; exact hrep
  have hz : cGH k * d4z * (cGH k)⁻¹ ∈ d4V := by
    have h := repE_conjI hrep hrep' repE_z0R
    rcases hnorm k hk z0R (by simp) with e | e | e <;> rw [e] at h
    · rw [eq_of_repE d4E_injective h repE_z0R]
      exact mem_d4V_iff.2 (Or.inr (Or.inl rfl))
    · rw [eq_of_repE d4E_injective h repE_vB]
      exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [eq_of_repE d4E_injective h repE_vC]
      exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl)))
  have hb : cGH k * vB * (cGH k)⁻¹ ∈ d4V := by
    have h := repE_conjI hrep hrep' repE_vB
    rcases hnorm k hk cz.T[1]! (by simp) with e | e | e <;> rw [e] at h
    · rw [eq_of_repE d4E_injective h repE_z0R]
      exact mem_d4V_iff.2 (Or.inr (Or.inl rfl))
    · rw [eq_of_repE d4E_injective h repE_vB]
      exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [eq_of_repE d4E_injective h repE_vC]
      exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl)))
  have hc : cGH k * vC * (cGH k)⁻¹ ∈ d4V := by
    have h := repE_conjI hrep hrep' repE_vC
    rcases hnorm k hk cz.T[5]! (by simp) with e | e | e <;> rw [e] at h
    · rw [eq_of_repE d4E_injective h repE_z0R]
      exact mem_d4V_iff.2 (Or.inr (Or.inl rfl))
    · rw [eq_of_repE d4E_injective h repE_vB]
      exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
    · rw [eq_of_repE d4E_injective h repE_vC]
      exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl)))
  intro v hv
  rw [mem_d4V_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · simp
  · exact hz
  · exact hb
  · exact hc

theorem d4Ct_norm_V : ∀ x ∈ d4Ct, ∀ v ∈ d4V, x * v * x⁻¹ ∈ d4V := by
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one => intro v hv; simpa using hv
  | mul_left g hg y _ ih =>
    obtain ⟨k, hk, rfl⟩ := hg
    intro v hv
    have := conj_gen_mem_V hk (y * v * y⁻¹) (ih v hv)
    rwa [show cGH k * (y * v * y⁻¹) * (cGH k)⁻¹ = cGH k * y * v * (cGH k * y)⁻¹ by group]
      at this
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨k, hk, rfl⟩ := hg
    intro v hv
    have hinv : (cGH k)⁻¹ = cGH k := inv_eq_of_mul_eq_one_right (cGens_hyp' k hk).2
    have := conj_gen_mem_V hk (y * v * y⁻¹) (ih v hv)
    rw [hinv]
    rwa [show cGH k * (y * v * y⁻¹) * (cGH k)⁻¹ = cGH k * y * v * (cGH k * y)⁻¹ by group]
      at this

theorem d4V_conj : ∀ v ∈ d4V, v ≠ 1 → ∃ x ∈ d4Ct, v = x * d4z * x⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hct, hm1, hm5, -⟩ := locV_parts
  simp only [locCz_eq] at hm1 hm5
  have key : ∀ (y : Array ℕ) (w : D), RepE d4E y w → memR locCzC.T locCzC.idx y = true →
      ∃ x ∈ d4Ct, w = x * d4z * x⁻¹ := by
    intro y w hy hm
    obtain ⟨hlt, heq⟩ := memR_spec hm
    obtain ⟨c, hc, hrep⟩ := exists_conj_mem_of_classTreeOK cGens_hyp' repE_z0R hct _ hlt
    rw [heq] at hrep
    exact ⟨c, hc, eq_of_repE d4E_injective hy hrep⟩
  intro v hv hv1
  rw [mem_d4V_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact absurd rfl hv1
  · exact ⟨1, d4Ct.one_mem, by simp⟩
  · exact key _ _ repE_vB hm1
  · exact key _ _ repE_vC hm5

theorem exists_q : ∃ q ∈ d4Ct, q * d4z = d4z * q ∧ q * vB = vB * q ∧ q * vC = vC * q ∧
    (q * q = d4z ∨ q * q = vB ∨ q * q = vC) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, i, hi, hq0, hq1, hq5, hsq⟩ :=
    locV_parts
  simp only [locCz_eq] at hq1 hq5 hsq
  obtain ⟨q, hqC, hqrep⟩ := exists_of_C hi
  refine ⟨q, hqC, locComm_of_eq hqrep repE_z0R hq0, locComm_of_eq hqrep repE_vB hq1,
    locComm_of_eq hqrep repE_vC hq5, ?_⟩
  rcases hsq with h | h | h
  · exact Or.inl (mul_eq_of_arr hqrep hqrep repE_z0R h)
  · exact Or.inr (Or.inl (mul_eq_of_arr hqrep hqrep repE_vB h))
  · exact Or.inr (Or.inr (mul_eq_of_arr hqrep hqrep repE_vC h))

end Cert

end Model

end CFSG.Quasithin.D4Hex
