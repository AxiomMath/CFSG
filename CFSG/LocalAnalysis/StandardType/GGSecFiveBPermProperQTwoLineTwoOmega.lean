module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperOmExcl
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedOmega StatedQuadMinus StatedQuadPlus)

theorem GGConfig.false_of_qTwo_line_two_omega (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ 1 + 1) (hn : 5 ≤ n)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hBBs : B ≠ Bs) {K : Subgroup G} (hmark : GGInnerDiagOn Bs K)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {a a' : Fin n} (haa' : a ≠ a')
    (hAut : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bBlockOn n p ({a, a'} : Finset (Fin n))ᶜ)
    (hOm : (Even (n - 1) ∧ ∃ b c : GaloisField 2 1,
        (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (↥K ≃* StatedOmega (StatedQuadMinus (n - 1) (GaloisField 2 1) b c))) ∨
      (Odd (n - 1) ∧ Nonempty (↥K ≃* StatedOmega (StatedQuadPlus (n - 1) (GaloisField 2 1))))) :
    False := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega] at hOm
  have hUF : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
    ⟨Nat.prime_two, le_rfl, GaloisField.card 2 (2 * 1) (by omega)⟩
  let := galoisAlgebra hUF
  have E := galoisQuadExt hUF
  have hI : (({a, a'} : Finset (Fin (k + 2)))ᶜ).card = k := by
    rw [Finset.card_compl, Finset.card_pair haa', Fintype.card_fin, Nat.add_sub_cancel]
  have he : Nonempty (↥K ≃* normOmega E k) := by
    rcases hOm with ⟨hev, b, c, hirr, ⟨eK⟩⟩ | ⟨hodd, ⟨eK⟩⟩
    · obtain ⟨e'⟩ := nonempty_normOmega_mulEquiv_minus E
        (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hev)) hirr
      exact ⟨eK.trans e'.symm⟩
    · obtain ⟨e'⟩ := nonempty_normOmega_mulEquiv_plus E
        (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hodd))
      exact ⟨eK.trans e'.symm⟩
  obtain ⟨e⟩ := he
  exact hcfg.false_of_normOmega_bBlockOn hMp hp2 E hUF hpq (by omega)
    (lt_of_le_of_ne hcfg.2.1.1 hBBs) hmark e eta hI hAut

end CFSG.StandardType

end
