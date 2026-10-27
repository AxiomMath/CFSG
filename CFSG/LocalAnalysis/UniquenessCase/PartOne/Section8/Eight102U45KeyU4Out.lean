module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixU4Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Adapters.LieModelUnitaryOuter
import CFSG.GroupTheory.SylowAutConj
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem burnsideF4m_U4_fieldAut_pow_eq_one_of_mem_range (h : UnitaryFieldData 2 n K)
    (hX : UC22.IsU4 (hypSU h 2 0) n) {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2) {k : ℕ}
    (hk : ASVolI.burnsideF4m_U4_fieldAut h σ ^ k ∈
      (MulAut.conj : hypSU h 2 0 →* MulAut (hypSU h 2 0)).range) :
    ASVolI.burnsideF4m_U4_fieldAut h σ ^ k = 1 := by
  let Φ : MulAut (hypSU h 2 0) := ASVolI.burnsideF4m_U4_fieldAut h σ
  let N : Subgroup (MulAut (hypSU h 2 0)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner (hypSU h 2 0)
  have hΦ : ∀ α : MulAut (hypSU h 2 0), ∃ y : hypSU h 2 0, ∃ j : ℕ,
      α = MulAut.conj y * Φ ^ j :=
    exists_conj_mul_burnsideF4m_U4_fieldAut_pow h hσ
  have hgen : ∀ x : MulAut (hypSU h 2 0) ⧸ N,
      x ∈ Subgroup.zpowers (QuotientGroup.mk' N Φ) := by
    intro x
    obtain ⟨j, hj⟩ := CFSG.exists_eq_quotient_mk'_pow (H := N) hΦ le_rfl x
    rw [hj]
    exact Subgroup.npow_mem_zpowers _ j
  have hord : orderOf (QuotientGroup.mk' N Φ) =
      Nat.card (MulAut (hypSU h 2 0) ⧸ N) :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have hgcd : Nat.gcd 4 (2 ^ n + 1) = 1 := by
    have h2dvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := h.one_le; omega)
    have h2 : Nat.Coprime 2 (2 ^ n + 1) :=
      Nat.coprime_two_left.mpr (even_iff_two_dvd.mpr h2dvd).add_one
    have h4 : Nat.Coprime 4 (2 ^ n + 1) := by simpa using h2.pow_left 2
    exact h4
  have hcard : Nat.card (MulAut (hypSU h 2 0) ⧸ N) = 2 * n := by
    have hout := CFSG.Blueprint.LieModel.card_outer_psu hX (by norm_num) (by norm_num)
    rw [hgcd, mul_one] at hout
    simpa [N, CFSG.ComponentClassification.OuterAutomorphisms.inner,
      CFSG.ComponentClassification.OuterAutomorphisms.Outer] using hout
  have hqk : (QuotientGroup.mk' N Φ) ^ k = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simpa [N, CFSG.ComponentClassification.OuterAutomorphisms.inner] using hk
  have hdiv : 2 * n ∣ k := by
    have h := orderOf_dvd_of_pow_eq_one hqk
    rwa [hord, hcard] at h
  obtain ⟨t, ht⟩ := hdiv
  rw [ht, pow_mul, burnsideF4m_U4_fieldAut_pow_two_mul_eq_one h hσ, one_pow]

theorem pRank_le_one_of_isU4 {Y : Type} [Group Y] [Finite Y] (hY : UC22.IsU4 Y n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n + 1) (hpn' : ¬ p ∣ 2 ^ n - 1) :
    Open.pRank p (⊤ : Subgroup Y) ≤ 1 := by
  rw [UC22.uc22s218_u4_pRank_eq_div hY hp hp2 hpn]
  set x : ZMod p := -((2 ^ n : ℕ) : ZMod p) with hx
  have hx1 : x ≠ 1 := by
    intro h1
    apply hpn
    have h0 : (((2 ^ n + 1 : ℕ)) : ZMod p) = 0 := by
      rw [hx] at h1
      rw [Nat.cast_add, Nat.cast_one]
      exact (neg_eq_iff_add_eq_zero).mp h1
    exact (ZMod.natCast_eq_zero_iff (2 ^ n + 1) p).mp h0
  have hx2 : x ^ 2 ≠ 1 := by
    intro h1
    have hA2 : (((2 ^ n : ℕ) : ZMod p)) ^ 2 = 1 := by
      rw [hx] at h1
      simpa [neg_sq] using h1
    have hcast : (((2 ^ (2 * n) : ℕ)) : ZMod p) =
        (((2 ^ n : ℕ) : ZMod p)) ^ 2 := by
      rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul, show 2 * n = n * 2 by omega]
    have hmod : 2 ^ (2 * n) ≡ 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff, hcast]
      simpa using hA2
    have hdvd : p ∣ 2 ^ (2 * n) - 1 :=
      (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
    have hsq : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [two_mul, pow_add, mul_self_tsub_one]
    rw [hsq] at hdvd
    exact (hp.dvd_mul.mp hdvd).elim hpn hpn'
  have hord1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hord2 : orderOf x ≠ 2 := by
    intro h2
    exact hx2 (by rw [← h2, pow_orderOf_eq_one])
  have h3or0 : orderOf x = 0 ∨ 3 ≤ orderOf x := by omega
  rcases h3or0 with h0 | h3
  · rw [h0, Nat.div_zero]
    exact Nat.zero_le 1
  · exact (Nat.div_le_iff_le_mul (by omega)).mpr (by omega)

theorem conj_injective_of_isU4 {Y : Type} [Group Y] (hY : UC22.IsU4 Y n) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  obtain ⟨K, instK, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  let : Field K := instK
  have hSimple : IsSimpleGroup (hypSU h 2 0) :=
    CFSG.Quasithin.H13.U4Par.isSimpleGroup_hypSU h
  have hYSimple : IsSimpleGroup Y := e.symm.isSimpleGroup
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    obtain ⟨a, -, b, -, hab⟩ := CFSG.Quasithin.H13.U4Par.exists_radQ_ne_comm h
    exact ⟨e a, e b, fun hc => hab (e.injective (by simpa only [map_mul] using hc))⟩
  have hcenter : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h0 | h0
    · exact h0
    · obtain ⟨a, b, hab⟩ := hnab
      exfalso
      exact hab (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top a) b).symm
  rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center]
  exact hcenter

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
