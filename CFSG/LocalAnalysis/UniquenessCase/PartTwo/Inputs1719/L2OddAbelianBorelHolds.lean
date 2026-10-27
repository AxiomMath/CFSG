module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenLevi
import CFSG.Dihedral.GorensteinWalter.PSL2EvenOuterOddSylow
import CFSG.Dihedral.GorensteinWalter.PSL2EvenSplitTorusSylow
import CFSG.GroupTheory.InnerNormalizedAutomorphisms
import CFSG.GroupTheory.SylowMulAutTransport
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.LocalAnalysis.UniquenessCase.UC6S846Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_L2_oddAbelianBorel_holds : K_L2_oddAbelianBorel := by
  intro G _ _ J B n hL2 hBN hcomm hodd hexp
  obtain ⟨hEv, -⟩ := P22fin.isL2Ev_of_isL2 hL2
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_psl2 hEv
  set φ : ↥B →* MulAut (Bar2 J) := (UC6S846.rhoL J).comp (Subgroup.inclusion hBN) with hφ
  set ψ : ↥B →* MulAut (CFSG.GorensteinWalter.PSL2 F) :=
    (MulAut.congr e).toMonoidHom.comp φ with hψ
  have hAodd : Odd (Nat.card ψ.range) := Odd.of_dvd_nat hodd (Subgroup.card_range_dvd ψ)
  suffices h : ∃ ω' : Sylow 2 (CFSG.GorensteinWalter.PSL2 F), ∀ a ∈ ψ.range, a • ω' = ω' by
    obtain ⟨ω', hω'⟩ := h
    obtain ⟨ω, hω⟩ := CFSG.GroupTheory.exists_sylow_forall_smul_eq_of_mulEquiv e φ.range ω'
      (by rintro _ ⟨b, rfl⟩; exact hω' _ ⟨b, rfl⟩)
    exact UC6S846.exists_isSylowOf_le_normalizer_of_rhoL hBN ω fun b => hω _ ⟨b, rfl⟩
  have hinj := P22y.conj_injective_of_center_eq_bot (CFSG.GorensteinWalter.psl2_center_eq_bot F)
  by_cases hinn : ψ.range ⊓ (MulAut.conj : CFSG.GorensteinWalter.PSL2 F →* _).range = ⊥
  · exact CFSG.GorensteinWalter.psl2_even_exists_sylow_fixed_of_inf_inner_eq_bot hF _ hAodd hinn
  obtain ⟨⟨a, ⟨b, rfl⟩, y, hy⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hinn
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact ha1 (Subtype.ext (by simpa using hy.symm))
  have hyq : y ^ (Nat.card F - 1) = 1 := by
    have hb : b ^ (2 ^ n - 1) = 1 := Subtype.ext (by simpa using hexp b b.2)
    apply hinj
    rw [map_pow, hy, ← map_pow, hF, hb, map_one, map_one]
  have hfix : ∀ a ∈ ψ.range, a y = y := by
    rintro _ ⟨b', rfl⟩
    apply hinj
    rw [← CFSG.InnerNormalizedAutomorphisms.mul_conj_mul_inv_eq, hy, ← map_mul, ← map_inv,
      ← map_mul, show b' * b * b'⁻¹ = b by
        rw [hcomm.is_comm.comm b' b, mul_inv_cancel_right]]
  obtain ⟨ω, -, hω⟩ :=
    CFSG.GorensteinWalter.psl2_even_exists_sylow_fixed_of_fixes _ hAodd hy1 hyq hfix
  exact ⟨ω, hω⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
