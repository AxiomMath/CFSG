module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.CharacterTheory.Semidihedral.AllPrimeSL2Sections
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem three_dvd_of_card_relations {N N₀ i g a : ℕ} (ha : 2 ≤ a) (hg : 0 < g) (hN : N = N₀ * i)
    (h1 : N * g = a ^ 3 * (a ^ 6 - 1)) (h0 : N₀ * g = a * (a ^ 2 - 1)) : 3 ∣ i := by
  obtain ⟨m, hm⟩ : ∃ m, a ^ 2 = m + 1 := ⟨a ^ 2 - 1, by have := Nat.one_le_pow 2 a (by omega); omega⟩
  have hm0 : 0 < m := by
    have : 4 ≤ a ^ 2 := by nlinarith
    omega
  have h6 : a ^ 6 - 1 = m * ((m + 1) ^ 2 + (m + 1) + 1) := by
    have : a ^ 6 = (a ^ 2) ^ 3 := by ring
    rw [this, hm]
    have : (m + 1) ^ 3 = m * ((m + 1) ^ 2 + (m + 1) + 1) + 1 := by ring
    omega
  have h0' : N₀ * g = a * m := by rw [h0, hm]; simp
  have h1' : N * g = a ^ 3 * (m * ((m + 1) ^ 2 + (m + 1) + 1)) := by rw [h1, h6]
  have key : (a * m) * i = (a * m) * (a ^ 2 * ((m + 1) ^ 2 + (m + 1) + 1)) := by
    have e1 : N * g = (N₀ * g) * i := by rw [hN]; ring
    rw [h0'] at e1
    calc (a * m) * i = N * g := e1.symm
      _ = a ^ 3 * (m * ((m + 1) ^ 2 + (m + 1) + 1)) := h1'
      _ = (a * m) * (a ^ 2 * ((m + 1) ^ 2 + (m + 1) + 1)) := by ring
  have hapos : 0 < a * m := Nat.mul_pos (by omega) hm0
  have hi : i = a ^ 2 * ((a ^ 2) ^ 2 + a ^ 2 + 1) := by
    rw [Nat.eq_of_mul_eq_mul_left hapos key, hm]
  rw [hi]
  have hr : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  apply Nat.dvd_of_mod_eq_zero
  rcases hr with hr | hr | hr <;> simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, hr]

open CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem card_psl2_mul_gcd (F : Type) [Field F] [Finite F] :
    Nat.card (PSL2 F) * Nat.gcd 2 (Nat.card F - 1) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  by_cases hodd : Odd (Nat.card F)
  · have h2 : Nat.gcd 2 (Nat.card F - 1) = 2 := by
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      simp
    rw [h2]
    exact CFSG.Semidihedral.AllPrime.SL2Sections.card_psl2_mul_two hodd
  · have : Fintype F := Fintype.ofFinite F
    set p := ringChar F with hp
    have hpr : p.Prime := CharP.char_is_prime F p
    obtain ⟨n, -, hn⟩ := FiniteField.card F p
    have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    have hp2 : p = 2 := by
      by_contra h
      apply hodd
      rw [hcard]
      exact Odd.pow (hpr.odd_of_ne_two h)
    have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hGF : Nat.card (GaloisField 2 n) = 2 ^ (n : ℕ) := GaloisField.card 2 n n.ne_zero
    have eF : F ≃+* GaloisField 2 n :=
      FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, hGF, hp2])
    have h1 : Nat.card (PSL2 F) = Nat.card (PSL2 (GaloisField 2 n)) :=
      Nat.card_congr (psl2RingEquiv eF).toEquiv
    have h2 : Nat.gcd 2 (Nat.card F - 1) = 1 := by
      have hpos : 1 ≤ Nat.card F := Nat.card_pos
      have hev : Nat.card F % 2 = 0 := by
        have := Nat.not_odd_iff.mp hodd
        omega
      have hodd1 : Odd (Nat.card F - 1) := by
        rw [Nat.odd_iff]
        omega
      exact Nat.coprime_two_left.mpr hodd1
    rw [h2, mul_one, h1, CFSG.Walter.psl2_even_card n.ne_zero, hcard, hp2]


section Outer

variable {K : Type} [Field K] [Finite K]

theorem isInnerAut_of_mem_range_pglAction {α : MulAut (PSL2 K)} (hD : α ∈ (pglAction K).range)
    (h3 : α ^ 3 = 1) : α ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range := by
  obtain ⟨g, rfl⟩ := hD
  have hg : g ^ 3 = 1 := pglAction_injective (by rw [map_pow, h3, map_one])
  obtain ⟨x, hx⟩ := exists_toPGL_eq_of_pow_odd (by decide : Odd 3) hg
  exact ⟨x, by rw [← hx, pglAction_toPGL]⟩

theorem outerRow_psl2 : OuterRow (PSL2 K) := by
  intro _ α hα3 hout hwc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := psl2_center_eq_bot K
  have hD : α ∉ (pglAction K).range := fun hD => hout (isInnerAut_of_mem_range_pglAction hD hα3)
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 fun h1 => hout ⟨1, by rw [h1]; simp⟩
  have hfield := isField_psl2_of_orderOf_prime Nat.prime_three hord hD
  obtain ⟨τ, hτ3, d, hd⟩ := exists_fixed_iff_of_isField hfield hα3
  have hnd := three_not_dvd_index_of_autWeaklyClosed hα3 hout hwc
  set Stab := Subgroup.comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K))
    (Subgroup.centralizer ({α} : Set (MulAut (PSL2 K)))) with hStab
  have hcardStab : Nat.card Stab = Nat.card (PSL2 (GH74.GLS.IVK.fixedField τ)) := by
    have h1 : Nat.card Stab = Nat.card (GH74.GLS.IVK.pslIncl τ).range :=
      Nat.card_congr (Equiv.subtypeEquiv (d⁻¹ : MulAut (PSL2 K)).toEquiv fun x => by
        rw [hStab, mem_comap_conj_centralizer_iff hZ, hd x]
        rfl)
    rw [h1]
    exact (Nat.card_congr (MonoidHom.ofInjective (GH74.GLS.IVK.pslIncl_injective τ)).toEquiv).symm
  have hq : Nat.card (GH74.GLS.IVK.fixedField τ) ^ 3 = Nat.card K := by
    have := GH74.GLS.IVK.fixedField_card_pow τ
    rwa [hτ3] at this
  set a := Nat.card (GH74.GLS.IVK.fixedField τ) with ha
  have ha2 : 2 ≤ a := by
    have : 1 < Nat.card (GH74.GLS.IVK.fixedField τ) := Finite.one_lt_card
    omega
  have hg : Nat.gcd 2 (Nat.card K - 1) = Nat.gcd 2 (a - 1) := by
    rw [← hq]
    rcases Nat.even_or_odd a with he | ho
    · have h1 : Even (a ^ 3) := Nat.even_pow.mpr ⟨he, by norm_num⟩
      have e1 : Nat.gcd 2 (a - 1) = 1 := Nat.coprime_two_left.mpr (by
        rw [Nat.odd_iff]; obtain ⟨k, hk⟩ := he; omega)
      have e2 : Nat.gcd 2 (a ^ 3 - 1) = 1 := Nat.coprime_two_left.mpr (by
        rw [Nat.odd_iff]; obtain ⟨k, hk⟩ := h1
        have : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
        omega)
      rw [e1, e2]
    · have h1 : Odd (a ^ 3) := Odd.pow ho
      have e1 : Nat.gcd 2 (a - 1) = 2 := by
        obtain ⟨k, hk⟩ := ho
        rw [hk]; simp
      have e2 : Nat.gcd 2 (a ^ 3 - 1) = 2 := by
        obtain ⟨k, hk⟩ := h1
        rw [hk]; simp
      rw [e1, e2]
  have hc1 := card_psl2_mul_gcd K
  have hc0 := card_psl2_mul_gcd (GH74.GLS.IVK.fixedField τ)
  rw [hg, ← hq] at hc1
  rw [← hcardStab] at hc0
  have hN : Nat.card (PSL2 K) = Nat.card Stab * Stab.index := (Subgroup.card_mul_index Stab).symm
  refine hnd (three_dvd_of_card_relations (N := Nat.card (PSL2 K)) (N₀ := Nat.card Stab)
    (g := Nat.gcd 2 (a - 1)) ha2 (Nat.gcd_pos_of_pos_left _ (by norm_num)) hN ?_ hc0)
  rw [hc1]
  ring_nf

end Outer

end CFSG.RankThree.PartTwo.Sec4.RonanK432
