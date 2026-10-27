module

public import CFSG.Quasithin.Vol2.Ch11SecHFacts
public import CFSG.Quasithin.Vol2.KGNatSL2

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_conj_utri_of_isSylowTwoOf {S : Subgroup SL(2, F)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ g : SL(2, F), CFSG.CGT.Timmesfeld75.conjSubgroup g (utri F) = S := by
  obtain ⟨-, hS2, hidx⟩ := hS
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hidx
  exact exists_conj_utri_eq_of_index hS2 hidx

theorem factSL2TwoSylow_holds : Ch11.SecH.FactSL2TwoSylow := by
  intro F _ _ n hn hF S₁ S₂ h₁ h₂ hne
  have : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨g₁, rfl⟩ := exists_conj_utri_of_isSylowTwoOf h₁
  obtain ⟨g₂, rfl⟩ := exists_conj_utri_of_isSylowTwoOf h₂
  have hb : g₁⁻¹ * g₂ ∉ borel F := by
    intro hb
    apply hne
    rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by group, ← conjSubgroup_conjSubgroup,
      conjSubgroup_eq_of_mem_normalizer (borel_le_normalizer_utri hb)]
  rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by group, ← conjSubgroup_conjSubgroup,
    ← conjSubgroup_sup_eq_sup, utri_sup_conj_eq_top hb, conjSubgroup_top]

omit [Finite F] [CharP F 2] in
theorem borel_conj_utriElt {b : SL(2, F)} (hb : b ∈ borel F) (t : F) :
    b * utriElt t * b⁻¹ = utriElt (b 0 0 ^ 2 * t) := by
  have h := conj_mem_utri_of_mem_borel hb (utriElt_mem_utri t)
  rw [eq_utriElt_of_mem_utri h, conj_utriElt_apply_01]

theorem factSL2BorelFPF_holds : Ch11.SecH.FactSL2BorelFPF := by
  intro F _ _ n hn hF S hS y hy hodd hy1 s hs hys
  have : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨g, rfl⟩ := exists_conj_utri_of_isSylowTwoOf hS
  have hb : g⁻¹ * y * g ∈ borel F := by
    rw [← normalizer_utri_eq_borel, ← mem_normalizer_conjSubgroup]
    exact hy
  have hu : g⁻¹ * s * g ∈ utri F := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hs
  obtain ⟨t, ht⟩ := mem_utri_iff.mp hu
  have hcomm : (g⁻¹ * y * g) * utriElt t * (g⁻¹ * y * g)⁻¹ = utriElt t := by
    rw [← ht, show g⁻¹ * y * g * (g⁻¹ * s * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * s * y⁻¹) * g by
      group, hys]
  rw [borel_conj_utriElt hb] at hcomm
  have ht' := utriElt_injective hcomm
  by_cases ht0 : t = 0
  · rw [ht0, utriElt_zero] at ht
    have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
    rw [this, ht, mul_one, mul_inv_cancel]
  · exfalso
    have h1 : (g⁻¹ * y * g) 0 0 ^ 2 = 1 := by
      have := mul_right_cancel₀ ht0 (ht'.trans (one_mul t).symm)
      exact this
    have h00 : (g⁻¹ * y * g) 0 0 = 1 := by
      have h2 : ((g⁻¹ * y * g) 0 0 + 1) ^ 2 = 0 := by
        have h2z : (2 : F) = 0 := CharP.cast_eq_zero F 2
        linear_combination h1 + ((g⁻¹ * y * g) 0 0) * h2z + h2z
      have h3 := pow_eq_zero_iff two_ne_zero |>.mp h2
      linear_combination h3 - CharP.cast_eq_zero F 2
    have hbu : g⁻¹ * y * g ∈ utri F := ⟨hb, h00⟩
    have hsq : (g⁻¹ * y * g) ^ 2 = 1 := isElemAbelian_utri.2 _ hbu
    have hord : orderOf (g⁻¹ * y * g) = orderOf y := by
      have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
        inv_inv] at h
      exact h
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [hord] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact hy1 (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd
      exact absurd hodd (by decide)

end CFSG.Quasithin.Vol2.KGNat
