module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D3Cent

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Data2


theorem memR_of_mem_T {y : Array ℕ} {x : D} (hv : validR y = true) (hy : RepE d4E y x)
    (hx : x ∈ d4U) : memR locET.El locET.idx y = true := by
  obtain ⟨i, hi, hrep⟩ := exists_mem_T hx
  have heq : locET.El[i]! = y := arr_eq_of_repE (validR_T hi) hv hrep hy
  have hidx := ((enumOK_parts locT_parts.2.1.1).2.2 i hi).2.1
  rw [← heq]
  unfold memR
  rw [hidx]
  simp [hi]

theorem qchar_data : ∀ x ∈ d4U, (d4Word autQWord)⁻¹ * x * d4Word autQWord ∈ d4U → x ∈ d4Q := by
  intro x hx hgx
  obtain ⟨hw, -, hall⟩ := autQ_parts
  obtain ⟨i, hi, hrep⟩ := exists_mem_T hx
  have hrg : RepE d4E (wordR d4Gens autQWord) (d4Word autQWord) := repE_d4Word hw
  have hrg' : RepE d4E (wordR d4Gens autQWord.reverse) (d4Word autQWord)⁻¹ :=
    repE_d4Word_reverse hw
  have hc := repE_conjI hrg' (by rw [inv_inv]; exact hrg) hrep
  rw [inv_inv] at hc
  have hv1 : validR (wordR d4Gens autQWord.reverse) = true :=
    validR_d4Word fun k hk => hw k (List.mem_reverse.1 hk)
  have hv2 : validR (wordR d4Gens autQWord) = true := validR_d4Word hw
  have hvc : validR (conjI (wordR d4Gens autQWord.reverse) (wordR d4Gens autQWord)
      locET.El[i]!) = true := by
    unfold conjI
    exact validR_mulR (size_of_validR (validR_mulR (size_of_validR hv1) (validR_T hi))) hv2
  have hm := memR_of_mem_T hvc hc hgx
  rcases hall i hi with h | h
  · rw [hm] at h
    exact absurd h (by simp)
  · obtain ⟨a, ha, harep⟩ := mem_Q_of_memR h
    rw [eq_of_repE d4E_injective hrep harep]
    exact ha

end Data2

section Char


theorem autQ_mem_d4H : d4Word autQWord ∈ d4H := by
  obtain ⟨hw, h0, -⟩ := autQ_parts
  exact mem_d4H_of_rep (rep_d4WordArr _ hw) (by simpa [locWordArr, d4WordArr] using h0)

theorem d4Q_char {α : MulAut D} (hα : α ∈ autStab d4H) : ∀ q ∈ d4Q, α q ∈ d4Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQH : d4Q ≤ d4H := d4Q_le_d4U.trans d4U_le_d4H
  set R : Subgroup D := d4Q.map (α : D →* D) with hR
  have hmemR : ∀ q ∈ d4Q, α q ∈ R := fun q hq => ⟨q, hq, rfl⟩
  have hRH : R ≤ d4H := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hα q).1 (hQH hq)
  have hRn : ∀ h ∈ d4H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    rintro h hh _ ⟨q, hq, rfl⟩
    have hh' : α⁻¹ h ∈ d4H := (hα (α⁻¹ h)).2 (by rw [MulAut.apply_inv_self]; exact hh)
    refine ⟨α⁻¹ h * q * (α⁻¹ h)⁻¹, d4H_norm_Q _ hh' _ hq, ?_⟩
    simp [map_mul, map_inv]
  have hRp : IsPGroup 2 R :=
    (IsPGroup.of_card (n := 9) card_d4Q).of_equiv
      (Subgroup.equivMapOfInjective d4Q (α : D →* D) α.injective)
  have hRp' : IsPGroup 2 (R.subgroupOf d4H) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  have hnorm : (R.subgroupOf d4H).Normal := ⟨fun r hr h => hRn h.1 h.2 r hr⟩
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow
    (F7.isSylowTwoOf_mono_right d4_sylow d4U_le_d4H le_top)
  have hle : R.subgroupOf d4H ≤ (S : Subgroup ↥d4H) := hRp'.le_sylow_of_normal S
  have hRT : ∀ r ∈ R, r ∈ d4U := by
    intro r hr
    have h1 := hle (show (⟨r, hRH hr⟩ : ↥d4H) ∈ R.subgroupOf d4H from hr)
    rw [hS] at h1
    exact h1
  intro q hq
  have hg := autQ_mem_d4H
  have h1 := hRn _ (d4H.inv_mem hg) _ (hmemR q hq)
  rw [inv_inv] at h1
  exact qchar_data _ (hRT _ (hmemR q hq)) (hRT _ h1)

end Char

end CFSG.Quasithin.D4Hex
