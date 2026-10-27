module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ZpFacts
public import CFSG.GroupTheory.InvertingInvolutionRank
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicOrderThreeAutomorphism

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem three_le_rk_witness_of_card_three_rk_six
    {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (htA : t ∈ A) (hc : Conc4_136W A t L)
    (hL : Nat.card L = 3)
    (hrk : rk (commSub (⊤ : Subgroup W) L) = 6) :
    3 ≤ rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
  have h133 := s16h_conc4_133_of_prime_card Nat.prime_three hL hc
  obtain ⟨_, _, _, hLt, hind, _⟩ := h133
  by_cases htN : t ∈ normalizer (L : Set (MulAut W))
  ·
    have hcyc : IsCyclic ↥L :=
      isCyclic_of_prime_card (p := 3) (hp := ⟨Nat.prime_three⟩) hL
    let α : MulAut ↥L := L.normalizerMonoidHom ⟨t, htN⟩
    have hcoe : ∀ l : ↥L,
        ((α l : ↥L) : MulAut W) = t * (l : MulAut W) * t⁻¹ := fun l =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t, htN⟩ l
    rcases CFSG.GorensteinWalter.mulAut_eq_one_or_apply_eq_inv_of_card_eq_three hL α with
      hα | hα
    ·
      exfalso
      have hfix : ∀ l : ↥L,
          t * (l : MulAut W) * t⁻¹ = (l : MulAut W) := by
        intro l
        rw [← hcoe l, hα]
        rfl
      have hcomm : ∀ l ∈ L, t * l = l * t := by
        intro l hl
        have h1 : t * l * t⁻¹ = l := hfix ⟨l, hl⟩
        calc t * l = (t * l * t⁻¹) * t := by group
          _ = l * t := by rw [h1]
      have hbot : ⁅L, Subgroup.zpowers t⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
        exact (show Commute t l from hcomm l hl).zpow_left k |>.eq
      exact hLt hbot
    ·
      have hinv : ∀ l : ↥L,
          t * (l : MulAut W) * t⁻¹ = (l : MulAut W)⁻¹ := by
        intro l
        rw [← hcoe l, hα l]
        rfl
      obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top L).mp hcyc
      have hxL : x ∈ L := by
        rw [← hx]
        exact Subgroup.mem_zpowers x
      have hord : orderOf x = 3 := by
        rw [← Nat.card_zpowers, hx, hL]
      have hx3 : x ^ 3 = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one _
      have hx2 : x * x = x⁻¹ := by
        have h : x * x * x = 1 := by
          simpa [pow_succ, pow_two] using hx3
        calc x * x = (x * x * x) * x⁻¹ := by group
          _ = x⁻¹ := by rw [h, one_mul]
      have hxinv : x⁻¹ * x⁻¹ = x := by
        rw [← mul_inv_rev, hx2, inv_inv]
      have hxid : x = x⁻¹ * (t * x * t⁻¹) := by
        rw [hinv ⟨x, hxL⟩]
        exact hxinv.symm
      have hle := CFSG.GroupTheory.rk_commV_conj_comm_le (W := W) (φ := t)
        (x := x) (y := x) hxid
      have h1 : rk ↥(commV (Subgroup.zpowers x)) =
          rk ↥(commSub (⊤ : Subgroup W) L) := by
        rw [commV_eq_commSub, hx]
      have h2 : rk ↥(commV (Subgroup.zpowers t)) =
          rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
        rw [commV_eq_commSub]
      rw [h1, h2, hrk] at hle
      omega
  ·
    have hle := s16h_bl_rk_le_of_not_normalizes hc hind htA htN
    rw [hrk] at hle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
