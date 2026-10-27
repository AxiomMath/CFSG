module

public import CFSG.RankThree.GF2n.Stroth80.Sec8SectionOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

theorem card_sup_mul_card_le_of_normalizes {G : Type} [Group G] [Finite G]
    (A B Q : Subgroup G) (hQA : Q ≤ A) (hQB : Q ≤ B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥Q ≤ Nat.card ↥A * Nat.card ↥B := by
  have hAN : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hAB a ha h hh, fun hh => ?_⟩
    simpa [mul_assoc] using hAB a⁻¹ (A.inv_mem ha) _ hh
  have hrel : B.relIndex A = B.relIndex (A ⊔ B) := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hAN
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAN).toEquiv
  have hC : B.relIndex (A ⊔ B) * Nat.card ↥B = Nat.card ↥(A ⊔ B) := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
    rwa [inf_of_le_left (le_sup_right : B ≤ A ⊔ B)] at h
  have hA : B.relIndex A * Nat.card ↥(B ⊓ A) = Nat.card ↥A :=
    Subgroup.relIndex_mul_card (H := B) (K := A)
  have key : Nat.card ↥(A ⊔ B) * Nat.card ↥(B ⊓ A) = Nat.card ↥A * Nat.card ↥B := by
    rw [← hrel] at hC
    rw [← hC, ← hA]
    exact Nat.mul_right_comm _ _ _
  have hq : Nat.card ↥Q ≤ Nat.card ↥(B ⊓ A) := Subgroup.card_le_of_le (le_inf hQB hQA)
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥Q ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(B ⊓ A) :=
        Nat.mul_le_mul le_rfl hq
    _ = Nat.card ↥A * Nat.card ↥B := key

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_exists_pts (hPts : Sec5NatPointsSpStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {m : ℕ} (hmSp : SpMNat hc t m) {r : G} (hr : Sec7A hc t r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
      Sec8Pts hc t r m K φ u u' := by
  obtain ⟨K, fK, finK, hK, m', hm', φ, u, u', hφ, hker, hact, huu', hL, hL'⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.spNat r hr.mem hr.plane
  have hpts : Sec8Pts hc t r m' K φ u u' := ⟨hm', hK, hφ, hker, hact, huu', hL, hL'⟩
  obtain rfl : m' = m := (hmSp.m_unique hpts.spMNat).symm
  exact ⟨K, fK, finK, φ, u, u', hpts⟩

theorem sec8_CN_commSec_lower (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hPts : Sec5NatPointsSpStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {m : ℕ}
    (hmSp : SpMNat hc t m) (hN : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ (2 ^ m))
    {x : G} (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t) :
    Nat.card ↥Z0 * Nat.card Z ^ (2 ^ (m - 2)) ≤ Nat.card ↥(CommSec (hc.CN t) Z0 x) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr, -, hopp, hIZ⟩ := sec8_Z0_data h51 hA hc hs hZ0
  obtain ⟨K, fK, finK, φ, u, u', hpts⟩ := sec8_exists_pts hPts hc hs hmSp hr
  haveI : CharP K 2 := hpts.charP
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := hc.LB_conj_le_Rt_of_mem ht hrR
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, ρ * y * ρ⁻¹ ∈ Z0 := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hnormQ hρ) y).mp hy
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  have hx1 : φ ⟨x, hLR hxL⟩ ≠ 1 := by
    intro h1
    apply hxN
    have : (⟨x, hLR hxL⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rw [hpts.ker] at this
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨hfix, ha2⟩ := sec8_section_commSec_card (R := Rt M (LB M Q B) t) (N := hc.CN t)
    (P := hc.CN t) (I := Z0) (L₁ := LB M Q B) (L₂ := LB M Q (conjSubgroup r B))
    (A₁ := LB M Q B ⊓ hc.CN t) (A₂ := LB M Q (conjSubgroup r B) ⊓ hc.CN t) φ hpts.range
    (by have := hpts.two_le; omega) hpts.ker (fun ρ hρ y hy => hc.CN_conj_mem ht hρ hy) hI
    (fun a ha b hb => hopp.2.2.2.2.2.2.1 a ha b hb) hopp hLR hLCR hpts.uu' hpts.hL hL2 hxL hx1
  have hm2 : 2 ≤ m := hpts.two_le
  have hq : 1 ≤ Nat.card Z := Nat.card_pos
  have hpow : 2 ^ m = 4 * 2 ^ (m - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hapos : 0 < Nat.card ↥Z0 := Nat.card_pos
  set c := Nat.card ↥(CommSec (hc.CN t) Z0 x) with hc'
  by_cases hna : SpNonA2 (φ ⟨x, hLR hxL⟩)
  · have h2 := hfix hna
    rw [hN] at h2
    have h3 : c ^ 2 = (Nat.card ↥Z0 * Nat.card Z ^ (2 ^ (m - 1))) ^ 2 := by
      rw [h2]
      have : 2 ^ m = 2 * 2 ^ (m - 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      rw [this]
      ring
    have h4 : c = Nat.card ↥Z0 * Nat.card Z ^ (2 ^ (m - 1)) :=
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) h3
    rw [h4]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq ?_)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h2 := ha2 hna
    rw [hN] at h2
    have h3 : (Nat.card ↥Z0 * Nat.card Z ^ (2 ^ (m - 2))) ^ 4 ≤ c ^ 4 := by
      calc (Nat.card ↥Z0 * Nat.card Z ^ (2 ^ (m - 2))) ^ 4
          = Nat.card ↥Z0 ^ 3 * (Nat.card ↥Z0 * Nat.card Z ^ (2 ^ m)) := by
            rw [hpow]; ring
        _ ≤ c ^ 4 := h2
    exact (Nat.pow_le_pow_iff_left (by norm_num : 4 ≠ 0)).mp h3

end CFSG.RankThree.GF2n.Stroth80
