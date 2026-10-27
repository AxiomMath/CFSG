module

public import CFSG.Quasithin.Vol2.Ch11SecA15Kind
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Matrix IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem kindSp4_of_modO2Surj (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) {F : Type} [Field F] [Fintype F] {m : ℕ} (hF : Fintype.card F = 2 ^ m)
    {α : ↥L →* ↥(StatedSp 2 F)} (hα : IsModO2Surj L α) : KindSp4 L (fsuV T I) n ∧ m = n := by
  have hn : 2 ≤ n := h.one_lt
  have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hF]
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have := Fintype.one_lt_card (α := F)
      rw [hF, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact hm
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ (4 * m) * oSp4 m := by
    rw [card_quot_of_modO2Surj hα, card_Sp4_oSp4 hF']
  rcases card_quot_cases hG2 h1102 h with ⟨-, hc'⟩ | ⟨hk, hc'⟩ | ⟨-, hc'⟩ <;> rw [hc] at hc'
  · have h1 := eq_of_two_pow_mul_odd (odd_oSp4 hm) (odd_oSL3 (by omega)) hc'
    rw [h1] at hc'
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    obtain ⟨k, rfl, rfl⟩ : ∃ k, m = 3 * k ∧ n = 4 * k := ⟨n - m, by omega, by omega⟩
    exact (not_dvd_oSp4_oSL3 (k := k) (by omega) (h2 ▸ dvd_rfl)).elim
  · have h1 := eq_of_two_pow_mul_odd (odd_oSp4 hm) (odd_oSp4 (by omega)) hc'
    exact ⟨hk, by omega⟩
  · have h1 := eq_of_two_pow_mul_odd (odd_oSp4 hm) (odd_oG2 (by omega)) hc'
    rw [h1] at hc'
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    obtain ⟨k, rfl, rfl⟩ : ∃ k, m = 3 * k ∧ n = 2 * k := ⟨m - n, by omega, by omega⟩
    exact (not_dvd_oSp4_oG2 (k := k) (by omega) (h2 ▸ dvd_rfl)).elim

theorem sp4_realization (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n) :
    ∃ _ : IsMulCommutative ↥(fsuV T I),
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))),
      Nat.card K = 2 ^ n ∧
      (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π := by
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨hc, -, -, -, hk'⟩ := h1102 G T L I n h
  refine ⟨hc, ?_⟩
  rcases hk' with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩
  · exact (kind_not_SL3_Sp4 (by omega) ⟨K, inferInstance, inferInstance, hK, he⟩ hk).elim
  · exact ⟨K, inferInstance, inferInstance, π, hK, hπ⟩
  · exact (kind_not_Sp4_G2 hG2 hn hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem commutator_eq_of_conjV_eq (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {z : G}
    (hz : ∀ k ∈ pCoreOf 2 L, k * z = z * k) {l l' : G} (hl : l ∈ L) (hl' : l' ∈ L)
    (hlV : l ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hl'V : l' ∈ Subgroup.normalizer (fsuV T I : Set G))
    (he : conjV (fsuV T I) l hlV = conjV (fsuV T I) l' hl'V) :
    l * z * l⁻¹ * z⁻¹ = l' * z * l'⁻¹ * z⁻¹ := by
  have hk : l⁻¹ * l' ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem hl) hl', Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) he
    simp only [conjV_apply_coe] at h1
    calc v * (l⁻¹ * l') = l⁻¹ * (l * v * l⁻¹) * l' := by group
      _ = l⁻¹ * (l' * v * l'⁻¹) * l' := by rw [h1]
      _ = l⁻¹ * l' * v := by group
  rw [centralizer_eq_pCoreOf h1102 h] at hk
  have hkz := hz _ hk
  have : l' = l * (l⁻¹ * l') := by group
  rw [this]
  calc l * z * l⁻¹ * z⁻¹ = l * ((l⁻¹ * l') * z * (l⁻¹ * l')⁻¹) * l⁻¹ * z⁻¹ := by
        rw [hkz, mul_inv_cancel_right]
    _ = l * (l⁻¹ * l') * z * (l * (l⁻¹ * l'))⁻¹ * z⁻¹ := by group

end CFSG.Quasithin.Vol2.Ch11.SecA
