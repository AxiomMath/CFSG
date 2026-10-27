module

public import CFSG.RankThree.PartOne.S9.QD32.GeoGroup
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.QD32Facts

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Torsion37
  CFSG.RankThree.PartOne.OddCore37 CFSG.RankThree.GroupTheory.SteinbergBY Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conjugate_one (Y : Subgroup G) : conjugate Y 1 = Y := by
  ext x
  simp [conjugate]

theorem case_abelian [Finite G] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {D B : Subgroup G}
    {r z : G} (hQD : IsQDShape q D) (hDel : IsElementaryAbelian q D)
    (hz_norm : z ∈ normalizer (D : Set G)) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hz_inv : ∀ d ∈ D, z * d * z⁻¹ = d⁻¹)
    (hB : ∀ b ∈ B, ∃ l : ℕ, ∀ d ∈ D, b * d * b⁻¹ = d ^ l)
    (hFcard : Nat.card ↥(D ⊓ centralizer ({r} : Set G)) = q ^ 2) :
    (IsElementaryAbelian q ↥(D ⊓ centralizer ({r} : Set G)) ∧
      Nat.card ↥(D ⊓ centralizer ({r} : Set G)) = q ^ 2) ∧
    ∀ Y : Subgroup G, Y ≤ D ⊓ centralizer ({r} : Set G) →
      3 ≤ CFSG.pRank q ↥(D ⊓ centralizer (Y : Set G)) ∧
      (z ∈ normalizer (Y : Set G) →
        D ⊓ centralizer (Y : Set G) = ⁅D ⊓ centralizer (Y : Set G), Subgroup.zpowers z⁆) ∧
      ∃ f ∈ D ⊓ centralizer ({r} : Set G), B ≤ normalizer (conjugate Y f : Set G) ∧
        z ∈ normalizer (conjugate Y f : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  have hDexp : ∀ x ∈ D, x ^ q = 1 := fun x hx => by
    have := hDel
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian hDel hx hy
  have hFD : ∀ x ∈ D ⊓ centralizer ({r} : Set G), x ∈ D := fun x hx => hx.1
  refine ⟨⟨isElementaryAbelian_of_forall (fun x hx y hy => hDcomm x (hFD x hx) y (hFD y hy))
    (fun x hx => hDexp x (hFD x hx)), hFcard⟩, fun Y hY => ?_⟩
  have hYD : ∀ x ∈ Y, x ∈ D := fun x hx => (hY hx).1
  have hPD : D ⊓ centralizer (Y : Set G) = D :=
    inf_eq_left.mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hDcomm y (hYD y hy) x hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hPD]
    exact three_le_pRank_of_isQDShape hq hQD
  · intro _
    rw [hPD]
    have hzo : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ hz1
      rw [pow_two]; exact hzz
    apply le_antisymm
    · intro d hd
      obtain ⟨k, hd'⟩ := exp_one_add_two_mul hq hq2 (hDexp d hd)
      have hcz : ⁅d, z⁆ ∈ ⁅D, Subgroup.zpowers z⁆ :=
        Subgroup.commutator_mem_commutator hd (Subgroup.mem_zpowers z)
      have hcz2 : ⁅d, z⁆ = d ^ 2 := by
        have : ⁅d, z⁆ = d * (z * d * z⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
        rw [this, hz_inv d hd, inv_inv, pow_two]
      rw [hd', ← hcz2]
      exact pow_mem hcz _
    · rw [Subgroup.commutator_le]
      intro d hd w hw
      rcases (mem_zpowers_of_orderOf_eq_two hzo).mp hw with hw1 | hw1
      · rw [hw1, commutatorElement_one_right]; exact one_mem D
      · rw [hw1]
        have : ⁅d, z⁆ = d * (z * d⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]
        exact mul_mem hd (conj_mem_of_normalizer hz_norm (inv_mem hd))
  · refine ⟨1, one_mem _, ?_, ?_⟩
    · rw [conjugate_one]
      apply le_normalizer_of_forall
      intro b hb y hy
      obtain ⟨l, hl⟩ := hB b hb
      rw [hl y (hYD y hy)]
      exact pow_mem hy l
    · rw [conjugate_one]
      apply mem_normalizer_of_involution hzz
      intro y hy
      rw [hz_inv y (hYD y hy)]
      exact inv_mem hy

end CFSG.RankThree.PartOne.QD32Facts
