
module


public import CFSG.Sporadic.Ly.Certificate

public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega MulAction

section

@[expose] def omegaE : orbit J opE := ⟨opE, mem_orbit_self _⟩


theorem card_omega : Nat.card (orbit J opE) = 8835156 := ly_certificate.2.2.2.2.1

instance finite_omega : Finite (orbit J opE) :=
  Nat.finite_of_card_ne_zero (by rw [card_omega]; norm_num)

open Classical in
@[expose] noncomputable def ptEquiv : Fin 8835156 ≃ orbit J opE :=
  (Finite.equivFinOfCardEq card_omega).symm.trans
    (Equiv.swap ((Finite.equivFinOfCardEq card_omega).symm 0) omegaE)

open Classical in
theorem ptEquiv_zero : ptEquiv 0 = omegaE := by
  simp only [ptEquiv, Equiv.trans_apply, Equiv.swap_apply_left]

noncomputable instance idxInst : MulAction J (Fin 8835156) := ptEquiv.mulAction J



theorem smul_def (g : J) (i : Fin 8835156) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem ptEquiv_smul (g : J) (i : Fin 8835156) : ptEquiv (g • i) = g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem smul_eq_iff (g : J) (i j : Fin 8835156) : g • i = j ↔ g • ptEquiv i = ptEquiv j := by
  rw [← ptEquiv_smul]
  exact ptEquiv.injective.eq_iff.symm

theorem stabilizer_omegaE : stabilizer J omegaE = lyH := by
  rw [← ly_certificate.2.2.1]
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  exact Subtype.ext_iff

theorem stabilizer_zero : stabilizer J (0 : Fin 8835156) = lyH := by
  rw [← stabilizer_omegaE]
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, smul_eq_iff, ptEquiv_zero]

instance faithful : FaithfulSMul J (Fin 8835156) := by
  have hs : IsSimpleGroup J := ly_certificate.2.1
  let N : Subgroup J := (MulAction.toPermHom J (Fin 8835156)).ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · refine ⟨fun {g₁ g₂} e => ?_⟩
    have hm : g₂⁻¹ * g₁ ∈ N := by
      rw [MonoidHom.mem_ker]
      refine Equiv.ext fun y => ?_
      change (g₂⁻¹ * g₁) • y = y
      rw [mul_smul, e, inv_smul_smul]
    rw [h, Subgroup.mem_bot] at hm
    exact (inv_mul_eq_one.1 hm).symm
  · exfalso
    have hle : (⊤ : Subgroup J) ≤ lyH := by
      rw [← h, ← stabilizer_zero]
      intro g hg
      rw [mem_stabilizer_iff]
      exact congrFun (congrArg DFunLike.coe (MonoidHom.mem_ker.1 hg)) 0
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, ly_certificate.1, ly_certificate.2.2.2.1] at h1
    omega

theorem eq_one_of_fix_all {g : J} (h : ∀ i : Fin 8835156, g • i = i) : g = 1 :=
  eq_of_smul_eq_smul fun i => by rw [h, one_smul]


instance isPretransitive : IsPretransitive J (Fin 8835156) := by
  refine ⟨fun i j => ?_⟩
  have key : ∀ k : Fin 8835156, ∃ h : J, h • omegaE = ptEquiv k := by
    intro k
    obtain ⟨h, hh⟩ := (ptEquiv k).2
    exact ⟨h, Subtype.ext hh⟩
  obtain ⟨u, hu⟩ := key i
  obtain ⟨v, hv⟩ := key j
  refine ⟨v * u⁻¹, ?_⟩
  rw [smul_eq_iff, mul_smul, ← hu, inv_smul_smul, hv]

end

end CFSG.Sporadic.Ly
