
module

public import CFSG.Quasithin.Vol2.KGFactC31RuScanBase

public import Certificates.Certificate7230
public import Certificates.Certificate7231
public import Certificates.Certificate7232
public import CFSG.Quasithin.Vol2.KGFactC31RuBase
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native

theorem cand_C {i : ℕ} (hi : i < 4)
    {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC)
    (hmv : cosetH i * c * ruZ * (cosetH i * c)⁻¹ ≠ ruZ) {es : List ℕ} {q : ℕ}
    (hes : (es, q) ∈ ruGroups) : CandConcl i (cosetH i * c) ruZ es q := by
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · exact Certificates.certificate7230 c hc hmv es q hes
  · exact Certificates.certificate7231 i hi1 hi c hc hmv es q hes

theorem cand_L {i : ℕ} (hi4 : 4 ≤ i) (hi : i < 9)
    {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruL)
    (hmv : cosetH i * c * ruA0 * (cosetH i * c)⁻¹ ≠ ruA0) {es : List ℕ} {q : ℕ}
    (hes : (es, q) ∈ ruGroups) : CandConcl i (cosetH i * c) ruA0 es q :=
  Certificates.certificate7232 i hi4 hi c hc hmv es q hes

section Classify

theorem classifyZ
    {y : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP) (hmove : y * ruZ * y⁻¹ ≠ ruZ)
    {es : List ℕ} {q : ℕ} (hes : (es, q) ∈ ruGroups)
    (he : ∃ e ∈ es, y ^ e = 1)
    (hcomm : ∀ j : ℕ, ruZ * (y ^ j * ruZ * (y ^ j)⁻¹) = y ^ j * ruZ * (y ^ j)⁻¹ * ruZ) :
    BadConcl y ruZ q := by
  set s := y * ruZ * y⁻¹ with hs
  have hsP : s ∈ ruP := ruP.mul_mem (ruP.mul_mem hy ruZ_mem) (ruP.inv_mem hy)
  have hsC : s ∈ ruC := by
    rw [ruC_eq_centralizer]
    refine ⟨hsP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hcomm 1
    rw [pow_one] at this
    exact this.symm
  have hs2 : s ^ 2 = 1 := by
    rw [hs, sq, show y * ruZ * y⁻¹ * (y * ruZ * y⁻¹) = y * (ruZ * ruZ) * y⁻¹ by group, ← sq,
      ruZ_sq, mul_one, mul_inv_cancel]
  have hs1 : s ≠ 1 := by
    intro h
    apply ruZ_ne_one
    calc ruZ = y⁻¹ * (y * ruZ * y⁻¹) * y := by group
      _ = 1 := by rw [← hs, h]; group
  obtain ⟨r, hr, c₁, hc₁, hc₁r⟩ := exists_conj_repZ hsC hs2 hs1 hmove
  have hc₁P : c₁ ∈ ruP := ruC_le hc₁
  have hc₁z : c₁ * ruZ = ruZ * c₁ := by
    rw [ruC_eq_centralizer] at hc₁
    exact Subgroup.mem_centralizer_singleton_iff.mp hc₁.2
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi4 : i < 4 := by rwa [hWordsZ_length] at hi
    have hH : cosetH i = abG hWordsZ[i] := by
      rw [cosetH_Z hi4]
      exact congrArg abG (List.getD_eq_getElem _ _ hi)
    have hc₁r' : c₁ * s * c₁⁻¹ = abG hWordsZ[i] * ruZ * (abG hWordsZ[i])⁻¹ := hc₁r
    set y' := c₁ * y * c₁⁻¹ with hy'
    have hy'z : y' * ruZ * y'⁻¹ = cosetH i * ruZ * (cosetH i)⁻¹ := by
      rw [hH, ← hc₁r', hs, hy']
      calc c₁ * y * c₁⁻¹ * ruZ * (c₁ * y * c₁⁻¹)⁻¹ = c₁ * y * (c₁⁻¹ * ruZ * c₁) * y⁻¹ * c₁⁻¹ := by
            group
        _ = c₁ * (y * ruZ * y⁻¹) * c₁⁻¹ := by
            rw [show c₁⁻¹ * ruZ * c₁ = ruZ by rw [mul_assoc, ← hc₁z]; group]
            group
    have hcc : (cosetH i)⁻¹ * y' ∈ ruC := by
      rw [ruC_eq_centralizer]
      refine ⟨ruP.mul_mem (ruP.inv_mem (abG_mem _))
        (ruP.mul_mem (ruP.mul_mem hc₁P hy) (ruP.inv_mem hc₁P)), ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have e : (cosetH i)⁻¹ * y' * ruZ * ((cosetH i)⁻¹ * y')⁻¹ = ruZ := by
        calc (cosetH i)⁻¹ * y' * ruZ * ((cosetH i)⁻¹ * y')⁻¹ =
            (cosetH i)⁻¹ * (y' * ruZ * y'⁻¹) * cosetH i := by group
          _ = ruZ := by rw [hy'z]; group
      symm
      calc ruZ * ((cosetH i)⁻¹ * y') =
          (cosetH i)⁻¹ * y' * ruZ * ((cosetH i)⁻¹ * y')⁻¹ * ((cosetH i)⁻¹ * y') := by rw [e]
        _ = (cosetH i)⁻¹ * y' * ruZ := by group
    have hprod : cosetH i * ((cosetH i)⁻¹ * y') = y' := by group
    have he' : ∃ e ∈ es, (cosetH i * ((cosetH i)⁻¹ * y')) ^ e = 1 := by
      obtain ⟨e, hes, hye⟩ := he
      exact ⟨e, hes, by rw [hprod, hy', conj_pow, hye]; group⟩
    have hcomm' := conj_comm_facts hc₁z hcomm
    rw [← hy'] at hcomm'
    have hmv : cosetH i * ((cosetH i)⁻¹ * y') * ruZ * (cosetH i * ((cosetH i)⁻¹ * y'))⁻¹ ≠ ruZ := by
      rw [hprod]
      exact move_conj hc₁z hmove
    obtain ⟨cg, hcg, h1, h2⟩ := cand_C hi4 hcc hmv hes he' (by rw [hprod]; exact hcomm')
    rw [hprod] at h1 h2
    exact badConcl_of_cand hc₁P hc₁z hcg h1 h2
  · exfalso
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    have h1 := ncard_fixSet_otherZ w hw
    rw [← hc₁r, ncard_fixSet_conj, hs, conj_ruZ_ncard] at h1
    exact absurd h1 (by norm_num)

theorem classifyA {y : Equiv.Perm (Fin 4060)} (hy : y ∈ ruP)
    (hmove : y * ruA0 * y⁻¹ ≠ ruA0) {es : List ℕ} {q : ℕ} (hes : (es, q) ∈ ruGroups)
    (he : ∃ e ∈ es, y ^ e = 1)
    (hcomm : ∀ j : ℕ, ruA0 * (y ^ j * ruA0 * (y ^ j)⁻¹) = y ^ j * ruA0 * (y ^ j)⁻¹ * ruA0) :
    BadConcl y ruA0 q := by
  set s := y * ruA0 * y⁻¹ with hs
  have hsP : s ∈ ruP := ruP.mul_mem (ruP.mul_mem hy ruA0_mem) (ruP.inv_mem hy)
  have hsL : s ∈ ruL := by
    rw [← ruCentralizer_a]
    refine ⟨hsP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hcomm 1
    rw [pow_one] at this
    exact this.symm
  have hs2 : s ^ 2 = 1 := by
    rw [hs, sq, show y * ruA0 * y⁻¹ * (y * ruA0 * y⁻¹) = y * (ruA0 * ruA0) * y⁻¹ by group,
      ruA0_sq, mul_one, mul_inv_cancel]
  have hs1 : s ≠ 1 := by
    intro h
    apply ruA0_ne_one
    calc ruA0 = y⁻¹ * (y * ruA0 * y⁻¹) * y := by group
      _ = 1 := by rw [← hs, h]; group
  obtain ⟨r, hr, c₁, hc₁, hc₁r⟩ := exists_conj_repA hsL hs2 hs1 hmove
  have hc₁P : c₁ ∈ ruP := ruL_le hc₁
  have hc₁a : c₁ * ruA0 = ruA0 * c₁ := by
    have := ruL_le_centralizer hc₁
    exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi5 : i < 5 := by rwa [hWordsA_length] at hi
    have hH : cosetH (i + 4) = abG hWordsA[i] := by
      rw [cosetH_A i]
      exact congrArg abG (List.getD_eq_getElem _ _ hi)
    have hc₁r' : c₁ * s * c₁⁻¹ = abG hWordsA[i] * ruA0 * (abG hWordsA[i])⁻¹ := hc₁r
    set y' := c₁ * y * c₁⁻¹ with hy'
    have hy'a : y' * ruA0 * y'⁻¹ = cosetH (i + 4) * ruA0 * (cosetH (i + 4))⁻¹ := by
      rw [hH, ← hc₁r', hs, hy']
      calc c₁ * y * c₁⁻¹ * ruA0 * (c₁ * y * c₁⁻¹)⁻¹ =
          c₁ * y * (c₁⁻¹ * ruA0 * c₁) * y⁻¹ * c₁⁻¹ := by group
        _ = c₁ * (y * ruA0 * y⁻¹) * c₁⁻¹ := by
            rw [show c₁⁻¹ * ruA0 * c₁ = ruA0 by rw [mul_assoc, ← hc₁a]; group]
            group
    have hcc : (cosetH (i + 4))⁻¹ * y' ∈ ruL := by
      rw [← ruCentralizer_a]
      refine ⟨ruP.mul_mem (ruP.inv_mem (abG_mem _))
        (ruP.mul_mem (ruP.mul_mem hc₁P hy) (ruP.inv_mem hc₁P)), ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have e : (cosetH (i + 4))⁻¹ * y' * ruA0 * ((cosetH (i + 4))⁻¹ * y')⁻¹ = ruA0 := by
        calc (cosetH (i + 4))⁻¹ * y' * ruA0 * ((cosetH (i + 4))⁻¹ * y')⁻¹ =
            (cosetH (i + 4))⁻¹ * (y' * ruA0 * y'⁻¹) * cosetH (i + 4) := by group
          _ = ruA0 := by rw [hy'a]; group
      symm
      calc ruA0 * ((cosetH (i + 4))⁻¹ * y') =
          (cosetH (i + 4))⁻¹ * y' * ruA0 * ((cosetH (i + 4))⁻¹ * y')⁻¹ *
            ((cosetH (i + 4))⁻¹ * y') := by rw [e]
        _ = (cosetH (i + 4))⁻¹ * y' * ruA0 := by group
    have hprod : cosetH (i + 4) * ((cosetH (i + 4))⁻¹ * y') = y' := by group
    have he' : ∃ e ∈ es, (cosetH (i + 4) * ((cosetH (i + 4))⁻¹ * y')) ^ e = 1 := by
      obtain ⟨e, hes, hye⟩ := he
      exact ⟨e, hes, by rw [hprod, hy', conj_pow, hye]; group⟩
    have hcomm' := conj_comm_facts hc₁a hcomm
    rw [← hy'] at hcomm'
    have hmv : cosetH (i + 4) * ((cosetH (i + 4))⁻¹ * y') * ruA0 *
        (cosetH (i + 4) * ((cosetH (i + 4))⁻¹ * y'))⁻¹ ≠ ruA0 := by
      rw [hprod]
      exact move_conj hc₁a hmove
    obtain ⟨cg, hcg, h1, h2⟩ := cand_L (by omega) (by omega) hcc hmv hes he'
      (by rw [hprod]; exact hcomm')
    rw [hprod] at h1 h2
    exact badConcl_of_cand hc₁P hc₁a hcg h1 h2
  · exfalso
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    have h1 := ncard_fixSet_otherA w hw
    rw [← hc₁r, ncard_fixSet_conj, hs, conj_ruA0_ncard] at h1
    exact absurd h1 (by norm_num)

end Classify

end CFSG.Quasithin.KGC31.Ru

end
