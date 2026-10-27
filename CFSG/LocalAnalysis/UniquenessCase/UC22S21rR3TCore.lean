module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TNorm
import CFSG.GroupTheory.CommuteOfCommutator

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem uc22r3t_commutator_mem_of_normalizers {K R H T : Subgroup G} {b z : G}
    (hbK : b ∈ K) (hzN : z ∈ normalizer (K : Set G)) (hzR : z ∈ R)
    (hbR : b ∈ normalizer (R : Set G)) (hbH : b ∈ H) (hzH : z ∈ H)
    (hbT : b ∈ normalizer (T : Set G)) (hzT : z ∈ normalizer (T : Set G)) :
    b * z * b⁻¹ * z⁻¹ ∈ K ∧ b * z * b⁻¹ * z⁻¹ ∈ R ∧ b * z * b⁻¹ * z⁻¹ ∈ H ∧
      b * z * b⁻¹ * z⁻¹ ∈ normalizer (T : Set G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : z * b⁻¹ * z⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hzN b⁻¹).1 (K.inv_mem hbK)
    rw [show b * z * b⁻¹ * z⁻¹ = b * (z * b⁻¹ * z⁻¹) from by group]
    exact K.mul_mem hbK h1
  · have h1 : b * z * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hbR z).1 hzR
    rw [show b * z * b⁻¹ * z⁻¹ = (b * z * b⁻¹) * z⁻¹ from by group]
    exact R.mul_mem h1 (R.inv_mem hzR)
  · exact H.mul_mem (H.mul_mem (H.mul_mem hbH hzH) (H.inv_mem hbH)) (H.inv_mem hzH)
  · exact (normalizer (T : Set G)).mul_mem
      ((normalizer (T : Set G)).mul_mem
        ((normalizer (T : Set G)).mul_mem hbT hzT) ((normalizer (T : Set G)).inv_mem hbT))
      ((normalizer (T : Set G)).inv_mem hzT)

theorem uc22r3t_commute_of_mem_inf {D : Data G} {Ch : Choice2011 G} (h205 : S20_5 D)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hL0H : c.L0 ≤ H) {R : Subgroup G} {r : ℕ} (hr : r.Prime) (hR : IsPGroup r R)
    (hRM : R ≤ D.M) (hRT : R ≤ normalizer (D.T : Set G)) {b : G} (hb : b ∈ c.B0)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbR : b ∈ normalizer (R : Set G))
    (hq7 : 7 ≤ q) (h2q : 2 * q < r) (he : CFSG.Open.evenRank G = 3)
    (hF : ∀ {K₁ : Subgroup G}, K₁ ∈ calL D.T D.M → ∀ {x y : G}, x ∈ K₁ → y ∈ K₁ →
      x ∈ normalizer (D.T : Set G) → y ∈ normalizer (D.T : Set G) → ∀ {r : ℕ}, r.Prime →
      7 < r → ∀ {k : ℕ}, orderOf y = r ^ k → x * y * x⁻¹ * y⁻¹ ∈ D.T) :
    ∀ z ∈ R ⊓ H, b * z = z * b := by
  have hq2le : 2 ≤ q := hq.two_le
  intro z hz
  obtain ⟨hzR, hzH⟩ := hz
  obtain ⟨n, hzn⟩ := IsPGroup.exists_orderOf_dvd_pow hR (⟨z, hzR⟩ : ↥R)
  obtain ⟨k, -, hzo⟩ := (Nat.dvd_prime_pow hr).mp
    ((Subgroup.orderOf_coe (⟨z, hzR⟩ : ↥R)).symm ▸ hzn)
  obtain ⟨hB0L, -, B, C, hBcal, -, -, -, -, -, hinv, -⟩ := c.hB0
  obtain ⟨t, htL0, -, -, htinv⟩ := hinv
  obtain ⟨K₁, hK₁, hL0K₁⟩ := h205 h1930 c.L0 c.hL0.1 H hH hL0H
  have hbK : b ∈ K₁ := hL0K₁ (hB0L hb)
  have hbH : b ∈ H := CFSG.Quasithin.A3.subnormal_le hK₁.2 hbK
  have hzN : z ∈ normalizer (K₁ : Set G) :=
    uc22r3t_mem_normalizer_of_calLOf D he hH.1 hK₁ hbK (c.hBM hb) hq hq2 hbo
      (hL0K₁ htL0) (htinv b hb) hzH (hRM hzR) (hRT hzR) hr (by omega) hzo
  set c' : G := b * z * b⁻¹ * z⁻¹ with hc'def
  obtain ⟨hc'K, hc'R, hc'H, hc'T⟩ :=
    uc22r3t_commutator_mem_of_normalizers hbK hzN hzR hbR hbH hzH hbT (hRT hzR)
  obtain ⟨m, hc'm⟩ := IsPGroup.exists_orderOf_dvd_pow hR (⟨c', hc'R⟩ : ↥R)
  obtain ⟨j, -, hc'o⟩ := (Nat.dvd_prime_pow hr).mp
    ((Subgroup.orderOf_coe (⟨c', hc'R⟩ : ↥R)).symm ▸ hc'm)
  have hTmem : b * c' * b⁻¹ * c'⁻¹ ∈ D.T :=
    hF hK₁.1 hbK hc'K hbT hc'T hr (by omega) hc'o
  have hRmem : b * c' * b⁻¹ * c'⁻¹ ∈ R := by
    have h1 : b * c' * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hbR c').1 hc'R
    exact R.mul_mem h1 (R.inv_mem hc'R)
  have hdisj : Disjoint D.T R :=
    IsPGroup.disjoint_of_coprime D.sylowM.isPGroup hR
      ((Nat.coprime_primes Nat.prime_two hr).mpr (by omega))
  have h1 : b * c' * b⁻¹ * c'⁻¹ = 1 := Subgroup.mem_bot.mp (hdisj.le_bot ⟨hTmem, hRmem⟩)
  have hcomm : Commute b c' :=
    commutatorElement_eq_one_iff_commute.mp (by simpa only [commutatorElement_def] using h1)
  have hcop : (orderOf b).Coprime (orderOf c') := by
    rw [hbo, hc'o]
    exact Nat.Coprime.pow_right j ((Nat.coprime_primes hq hr).mpr (by omega))
  exact (CFSG.GroupTheory.commute_of_commute_commutatorElement hcomm hcop).eq

end CFSG.LocalAnalysis.UniquenessCase.UC22
