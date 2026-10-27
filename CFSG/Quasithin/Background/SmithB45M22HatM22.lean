module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer

public section

namespace CFSG.Quasithin.HatM22

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Certificates
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem m22gA_mem : m22gA ∈ NativeSporadic.M22 := m22a.2

theorem m22gB_mem : m22gB ∈ NativeSporadic.M22 := m22b.2

theorem m22_evalCodes_mem (w : List ℤ) : evalCodes [m22gA, m22gB] w ∈ NativeSporadic.M22 :=
  evalCodes_mem _ (fun g hg => by
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact m22gA_mem
    · exact m22gB_mem) w

theorem m22gA_mul_self : m22gA * m22gA = 1 := by decide +kernel

theorem m22_inv_conj
    {u : Equiv.Perm (Fin 22)} (hu : u ∈ NativeSporadic.M22) (ho : orderOf u = 2) :
    ∃ c ∈ NativeSporadic.M22, u = c * m22gA * c⁻¹ := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok
  have hcov := (exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) [m22Rep1]
    (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok).1
  rw [m22Certificate_originalSubgroup] at hcov
  obtain ⟨r, hr, c, hc, huc⟩ := hcov u (by simpa using hu) ho
  simp only [List.mem_singleton] at hr
  subst hr
  have hrep : m22Rep1 = m22gA := by
    simp [m22Rep1, m22InvReps, m22InvRepWords, evalCodes]
  exact ⟨c, hc, by rw [huc, hrep]⟩

@[expose] def m22ConjC : Equiv.Perm (Fin 22) := m22gB * m22gA * m22gB

@[expose] def m22InvS : Equiv.Perm (Fin 22) := m22ConjC * m22gA * m22ConjC⁻¹

theorem m22ConjC_mem : m22ConjC ∈ NativeSporadic.M22 :=
  NativeSporadic.M22.mul_mem (NativeSporadic.M22.mul_mem m22gB_mem m22gA_mem) m22gB_mem

theorem m22InvS_mem : m22InvS ∈ NativeSporadic.M22 :=
  NativeSporadic.M22.mul_mem (NativeSporadic.M22.mul_mem m22ConjC_mem m22gA_mem)
    (NativeSporadic.M22.inv_mem m22ConjC_mem)

theorem m22InvS_mul_self : m22InvS * m22InvS = 1 := by
  rw [m22InvS]
  calc m22ConjC * m22gA * m22ConjC⁻¹ * (m22ConjC * m22gA * m22ConjC⁻¹)
      = m22ConjC * (m22gA * m22gA) * m22ConjC⁻¹ := by group
    _ = 1 := by rw [m22gA_mul_self, mul_one, mul_inv_cancel]

theorem m22gA_mul_m22InvS_pow : (m22gA * m22InvS) ^ 3 = 1 := by decide +kernel

theorem m22gA_mul_m22InvS_ne : m22gA * m22InvS ≠ 1 := by decide +kernel

theorem m22_exists_partner
    {u : Equiv.Perm (Fin 22)} (hu : u ∈ NativeSporadic.M22) (ho : orderOf u = 2) :
    ∃ v ∈ NativeSporadic.M22, v * v = 1 ∧ (u * v) ^ 3 = 1 ∧ u * v ≠ 1 := by
  obtain ⟨c, hc, rfl⟩ := m22_inv_conj hu ho
  refine ⟨c * m22InvS * c⁻¹, NativeSporadic.M22.mul_mem
    (NativeSporadic.M22.mul_mem hc m22InvS_mem) (NativeSporadic.M22.inv_mem hc), ?_, ?_, ?_⟩
  · calc c * m22InvS * c⁻¹ * (c * m22InvS * c⁻¹) = c * (m22InvS * m22InvS) * c⁻¹ := by group
      _ = 1 := by rw [m22InvS_mul_self, mul_one, mul_inv_cancel]
  · have e : c * m22gA * c⁻¹ * (c * m22InvS * c⁻¹) = c * (m22gA * m22InvS) * c⁻¹ := by group
    rw [e, conj_pow, m22gA_mul_m22InvS_pow, mul_one, mul_inv_cancel]
  · have e : c * m22gA * c⁻¹ * (c * m22InvS * c⁻¹) = c * (m22gA * m22InvS) * c⁻¹ := by group
    rw [e]
    intro h
    apply m22gA_mul_m22InvS_ne
    calc m22gA * m22InvS = c⁻¹ * (c * (m22gA * m22InvS) * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group

@[expose] def m22AbarWord : List ℤ :=
  [2, 2, 1, 2, 1, 2, 2, 1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1,
    -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 1, 2, 2, 1]

@[expose] def m22BbarWord : List ℤ :=
  [-1, 2, -1, -2, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -1, -1, -2, -1, -2, -1, -2, -1,
    2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, 2, 1]

@[expose] def m22SbarWord : List ℤ :=
  [-2, -2, -1, -2, -1, -2, -1, 2, -1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 2, 1, 2, 1, 2,
    2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2]

@[expose] def m22Abar : Equiv.Perm (Fin 22) := evalCodes [m22gA, m22gB] m22AbarWord

@[expose] def m22Bbar : Equiv.Perm (Fin 22) := evalCodes [m22gA, m22gB] m22BbarWord

@[expose] def m22Sbar : Equiv.Perm (Fin 22) := m22Delta * evalCodes [m22gA, m22gB] m22SbarWord

theorem m22Abar_mem : m22Abar ∈ NativeSporadic.M22 := m22_evalCodes_mem _

theorem m22Bbar_mem : m22Bbar ∈ NativeSporadic.M22 := m22_evalCodes_mem _

set_option maxRecDepth 100000 in
theorem m22AB_comm : m22Abar * m22Bbar = m22Bbar * m22Abar := by decide +kernel

set_option maxRecDepth 100000 in
theorem m22Abar_pow : m22Abar ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem m22Bbar_pow : m22Bbar ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem m22AB_distinct : m22Abar ≠ 1 ∧ m22Abar ^ 2 ≠ 1 ∧ m22Abar ≠ m22Abar ^ 2 ∧ m22Bbar ≠ 1 ∧
    m22Bbar ≠ m22Abar ∧ m22Bbar ≠ m22Abar ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem m22Sbar_conj_a : m22Sbar * m22Abar * m22Sbar⁻¹ = m22Abar := by decide +kernel

set_option maxRecDepth 100000 in
theorem m22Sbar_conj_b : m22Sbar * m22Bbar * m22Sbar⁻¹ = m22Bbar⁻¹ := by decide +kernel

@[expose] def m22A : ↥NativeSporadic.M22 := ⟨m22Abar, m22Abar_mem⟩

@[expose] def m22B : ↥NativeSporadic.M22 := ⟨m22Bbar, m22Bbar_mem⟩

@[expose] def m22Pbar : Subgroup ↥NativeSporadic.M22 := Subgroup.closure {m22A, m22B}

theorem m22A_mul_B : m22A * m22B = m22B * m22A := Subtype.ext m22AB_comm

theorem m22Pbar_comm {x y : ↥NativeSporadic.M22} (hx : x ∈ m22Pbar) (hy : y ∈ m22Pbar) :
    x * y = y * x := by
  have hpair : ({m22A, m22B} : Set ↥NativeSporadic.M22).Pairwise Commute := by
    intro p hp q hq _
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · exact Commute.refl _
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact m22A_mul_B
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact m22A_mul_B.symm
    · rw [Set.mem_singleton_iff] at hp hq
      subst hp hq
      exact Commute.refl _
  have h := (Subgroup.isMulCommutative_closure hpair).is_comm.comm (⟨x, hx⟩ : ↥m22Pbar) ⟨y, hy⟩
  exact congrArg Subtype.val h

theorem m22Pbar_pow_three {x : ↥NativeSporadic.M22} (hx : x ∈ m22Pbar) : x ^ 3 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Subtype.ext m22Abar_pow
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subtype.ext m22Bbar_pow
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from m22Pbar_comm hx hy).mul_pow, ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

theorem card_m22Pbar : Nat.card m22Pbar = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥m22Pbar := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h3 : g ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact m22Pbar_pow_three g.2)
    have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : 3 ^ n ∣ 443520 := by
    rw [← hn, ← card_M22]
    exact Subgroup.card_subgroup_dvd_card m22Pbar
  have hn2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 ^ 3 ∣ 443520 := (pow_dvd_pow 3 h).trans hdvd
    norm_num at this
  have h4 : 4 ≤ Nat.card m22Pbar := by
    obtain ⟨hA1, hA2, hA12, hB1, hBA, hBA2⟩ := m22AB_distinct
    have hAm : m22A ∈ m22Pbar := Subgroup.subset_closure (Set.mem_insert _ _)
    have hBm : m22B ∈ m22Pbar := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have hA2m : (⟨m22Abar ^ 2, NativeSporadic.M22.pow_mem m22Abar_mem 2⟩ :
        ↥NativeSporadic.M22) ∈ m22Pbar := by
      have : (⟨m22Abar ^ 2, NativeSporadic.M22.pow_mem m22Abar_mem 2⟩ : ↥NativeSporadic.M22) =
          m22A ^ 2 := Subtype.ext (by rw [SubgroupClass.coe_pow]; rfl)
      rw [this]
      exact m22Pbar.pow_mem hAm 2
    let f : Fin 4 → ↥m22Pbar := ![1, ⟨m22A, hAm⟩,
      ⟨⟨m22Abar ^ 2, NativeSporadic.M22.pow_mem m22Abar_mem 2⟩, hA2m⟩, ⟨m22B, hBm⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have hv := congrArg (fun x : ↥m22Pbar => ((x : ↥NativeSporadic.M22) :
        Equiv.Perm (Fin 22))) hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hv.symm hA1
      · exact absurd hv.symm hA2
      · exact absurd hv.symm hB1
      · exact absurd hv hA1
      · rfl
      · exact absurd hv hA12
      · exact absurd hv.symm hBA
      · exact absurd hv hA2
      · exact absurd hv.symm hA12
      · rfl
      · exact absurd hv.symm hBA2
      · exact absurd hv hB1
      · exact absurd hv hBA
      · exact absurd hv hBA2
      · rfl
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  interval_cases n
  · rw [hn] at h4
    norm_num at h4
  · rw [hn] at h4
    norm_num at h4
  · rw [hn]
    norm_num

theorem m22_outer_eq_conj
    (α : MulAut ↥NativeSporadic.M22) (hα : α ∉ inner ↥NativeSporadic.M22) :
    ∃ g ∈ NativeSporadic.M22, ∀ h : ↥NativeSporadic.M22,
      (α h : Equiv.Perm (Fin 22)) = g * m22Delta * h * (g * m22Delta)⁻¹ :=
  exists_eq_conj_of_outer NativeSporadic.M22 m22Delta m22_delta_normalizes m22_delta_sq
    m22_center_eq_bot' m22_delta_outer m22_mulAut_card α hα

end CFSG.Quasithin.HatM22
