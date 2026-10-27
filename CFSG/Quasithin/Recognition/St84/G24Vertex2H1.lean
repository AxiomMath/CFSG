module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2Frame
public import CFSG.Quasithin.Recognition.St84.Gen.CrossedHomPrincipal
import CFSG.GroupTheory.FixedPointFreeModCentral
import CFSG.Quasithin.Background.SpecialPGroupCenter

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

private theorem G24Frame2.mem_centerOf_of_fixed [Finite G]
    (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S) {q : G}
    (hq : q ∈ dsQ L2 L1 S)
    (h : F.k * q * F.k⁻¹ * q⁻¹ ∈ centerOf (dsQ L2 L1 S)) :
    q ∈ centerOf (dsQ L2 L1 S) := by
  let c : G := F.k * q * F.k⁻¹ * q⁻¹
  have hcZ : c ∈ centerOf (dsQ L2 L1 S) := h
  have hc2 : c ^ 2 = 1 := hD.sq_eq_one_of_mem_centerOf_right hcZ
  have hkc : F.k * c = c * F.k := F.cent_Z c hcZ
  have hkq : F.k * q * F.k⁻¹ = c * q := by
    show F.k * q * F.k⁻¹ = (F.k * q * F.k⁻¹ * q⁻¹) * q
    group
  have hk3 : F.k ^ 3 = 1 := by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k
  have hk_eq : F.k = (F.k ^ 2) ^ 2 := by
    have h4 : F.k ^ 4 = F.k := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hk3, one_mul, pow_one]
    rw [← pow_mul, show 2 * 2 = 4 by norm_num]
    exact h4.symm
  have hsq : F.k ^ 2 * q * (F.k ^ 2)⁻¹ = q := by
    have e : F.k ^ 2 * q * (F.k ^ 2)⁻¹ = F.k * (F.k * q * F.k⁻¹) * F.k⁻¹ := by
      rw [pow_two]
      group
    rw [e, hkq]
    have h1 : F.k * (c * q) * F.k⁻¹ = c * (F.k * q * F.k⁻¹) := by
      rw [show F.k * (c * q) * F.k⁻¹ = (F.k * c * F.k⁻¹) * (F.k * q * F.k⁻¹) from by
        group]
      rw [show F.k * c * F.k⁻¹ = c from by rw [hkc]; group]
    rw [h1, hkq]
    have h3 : c * c = 1 := by rw [← pow_two]; exact hc2
    rw [← mul_assoc, h3, one_mul]
  have hcomm2 : F.k ^ 2 * q = q * F.k ^ 2 := by
    have h := congrArg (fun t => t * F.k ^ 2) hsq
    rw [show F.k ^ 2 * q * (F.k ^ 2)⁻¹ * F.k ^ 2 = F.k ^ 2 * q from by group] at h
    exact h
  have hmul : (F.k ^ 2) ^ 2 * q = q * (F.k ^ 2) ^ 2 := by
    rw [pow_two (F.k ^ 2)]
    calc (F.k ^ 2 * F.k ^ 2) * q = F.k ^ 2 * (F.k ^ 2 * q) := by rw [mul_assoc]
      _ = F.k ^ 2 * (q * F.k ^ 2) := by rw [hcomm2]
      _ = (F.k ^ 2 * q) * F.k ^ 2 := by rw [mul_assoc]
      _ = (q * F.k ^ 2) * F.k ^ 2 := by rw [hcomm2]
      _ = q * (F.k ^ 2 * F.k ^ 2) := by rw [mul_assoc]
  have hcent : F.k * q = q * F.k := by
    rw [hk_eq]
    exact hmul
  refine F.inf_centralizer ▸ Subgroup.mem_inf.mpr ⟨hq, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hcent

theorem G24Frame2.crossedHomPrincipal [Finite G] {G' : Type} [Group G']
    (F : G24Frame2 L1 L2 S) (hD : G24LocalData L1 L2 S) {Z' R' : Subgroup G'}
    (e : ↥F.A ≃* ↥R')
    (hR'Z' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a)
    (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (hk : ∀ r : ↥F.A, (r : G) = F.k → ∀ z ∈ Z',
      (e r : G') * z * (e r : G')⁻¹ = z) :
    CrossedHomPrincipal (dsQ L2 L1 S) (centerOf (dsQ L2 L1 S)) F.A Z' R' e := by
  let N : Subgroup G := Subgroup.zpowers F.k
  have hspec := F.special_data hD
  have hNR : N ≤ F.A := Subgroup.zpowers_le.mpr F.k_mem_A
  have hNnorm : ∀ r ∈ F.A, ∀ n ∈ N, r * n * r⁻¹ ∈ N := by
    intro r hr n hn
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcr : r * F.k = F.k * r :=
      (Subgroup.mem_centralizer_iff.mp (F.A_le hr).2 F.k (by simp)).symm
    have hconj : r * F.k * r⁻¹ = F.k := by rw [hcr]; group
    rw [← conj_zpow, hconj]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by simp⟩
  have hodd : Odd (Nat.card N) := by
    have hcard : Nat.card N = 3 := by rw [Nat.card_zpowers, F.orderOf_k]
    rw [hcard]
    norm_num
  have hN : CrossedHomPrincipalOn (dsQ L2 L1 S) (centerOf (dsQ L2 L1 S)) F.A N Z' R' e :=
    crossedHomPrincipalOn_of_odd e hspec.1 hspec.2.2.2.2.2.2.1 hR'Z' hZ'c hZ'2 hNR hodd
  have hfix : ∀ φ : ↥(dsQ L2 L1 S) →* ↥Z',
      (∀ v : ↥(dsQ L2 L1 S), (v : G) ∈ centerOf (dsQ L2 L1 S) → φ v = 1) →
      (∀ n : ↥F.A, (n : G) ∈ N → ∀ (v w : ↥(dsQ L2 L1 S)),
        (w : G) = (n : G) * v * (n : G)⁻¹ →
        (φ w : G') = (e n : G') * (φ v : G') * (e n : G')⁻¹) → φ = 1 := by
    intro φ hφZ hφeq
    have hk3 : F.k ^ 3 = 1 := by rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k
    have hkQ : ∀ q ∈ dsQ L2 L1 S, F.k * q * F.k⁻¹ ∈ dsQ L2 L1 S := fun q hq =>
      (Subgroup.mem_normalizer_iff.mp
        (P_le_normalizer_dsQ_right L1 L2 S F.kP.2) q).mp hq
    have hZc : ∀ z ∈ centerOf (dsQ L2 L1 S), ∀ q ∈ dsQ L2 L1 S, z * q = q * z :=
      hspec.2.2.2.1
    have hsq : ∀ q ∈ dsQ L2 L1 S, q ^ 2 ∈ centerOf (dsQ L2 L1 S) :=
      hspec.2.2.2.2.2.1
    have hcm : ∀ q ∈ dsQ L2 L1 S, ∀ r ∈ dsQ L2 L1 S,
        ⁅q, r⁆ ∈ centerOf (dsQ L2 L1 S) := fun q hq r hr =>
      CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
        (Subgroup.commutator_mem_commutator hq hr)
    have hfixq : ∀ q ∈ dsQ L2 L1 S, F.k * q * F.k⁻¹ * q⁻¹ ∈
        centerOf (dsQ L2 L1 S) → q ∈ centerOf (dsQ L2 L1 S) :=
      fun q hq h => F.mem_centerOf_of_fixed hD hq h
    ext x
    have hxQ : (x : G) ∈ dsQ L2 L1 S := x.2
    let y : ↥(dsQ L2 L1 S) := ⟨F.k * (x : G) * F.k⁻¹, hkQ x x.2⟩
    let w : ↥(dsQ L2 L1 S) := ⟨F.k * (y : G) * F.k⁻¹, hkQ y y.2⟩
    have hky : (y : G) = F.k * (x : G) * F.k⁻¹ := rfl
    have hkw : (w : G) = F.k * (y : G) * F.k⁻¹ := rfl
    have hmemN : F.k ∈ N := Subgroup.mem_zpowers F.k
    have hφy : φ y = φ x := by
      have h := hφeq ⟨F.k, F.k_mem_A⟩ hmemN x y hky
      have hz : (e ⟨F.k, F.k_mem_A⟩ : G') * (φ x : G') *
          (e ⟨F.k, F.k_mem_A⟩ : G')⁻¹ = (φ x : G') := hk _ rfl (φ x : G') (φ x).2
      exact Subtype.ext (h.trans hz)
    have hφw : φ w = φ y := by
      have h := hφeq ⟨F.k, F.k_mem_A⟩ hmemN y w hkw
      have hz : (e ⟨F.k, F.k_mem_A⟩ : G') * (φ y : G') *
          (e ⟨F.k, F.k_mem_A⟩ : G')⁻¹ = (φ y : G') := hk _ rfl (φ y : G') (φ y).2
      exact Subtype.ext (h.trans hz)
    have hmemZ : (w : G) * ((x : G) * (y : G))⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
      have h := CFSG.GroupTheory.conj_conj_mul_inv_mem_of_pow_three_eq_one
        (Q := dsQ L2 L1 S) (Z := centerOf (dsQ L2 L1 S)) hk3 hkQ hZc hsq hcm hfixq hxQ
      simpa only [w, y, Subgroup.coe_mk] using h
    have hφone : φ (w * (x * y)⁻¹) = 1 := hφZ _ hmemZ
    have hsplit : φ w = φ x * φ y := by
      have h1 : φ w * (φ (x * y))⁻¹ = 1 := by
        rw [← map_inv, ← map_mul]
        exact hφone
      have h2 : φ w = φ (x * y) := by
        calc φ w = φ w * (φ (x * y))⁻¹ * φ (x * y) := by group
          _ = 1 * φ (x * y) := by rw [h1]
          _ = φ (x * y) := one_mul _
      rw [h2, map_mul]
    have hxx : φ x = φ x * φ x := by
      calc φ x = φ y := hφy.symm
        _ = φ w := hφw.symm
        _ = φ x * φ y := hsplit
        _ = φ x * φ x := by rw [hφy]
    have hone : φ x = 1 := by
      have h2 : φ x * 1 = φ x * φ x := by
        rw [mul_one]
        exact hxx
      exact (mul_left_cancel h2).symm
    simpa using hone
  exact crossedHomPrincipal_of_normal e hspec.1 hspec.2.2.2.2.2.2.1 hR'Z' hZ'c hNR hNnorm hN
    hfix

end CFSG.Quasithin.F112R.St84

end
