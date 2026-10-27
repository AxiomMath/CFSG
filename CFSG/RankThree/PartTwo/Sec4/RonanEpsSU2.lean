module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsGood
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)

theorem card_galoisField_two_mul_one (p : ℕ) [Fact p.Prime] :
    Nat.card (GaloisField p (2 * 1)) = (p ^ 1) ^ 2 := by
  rw [GaloisField.card p (2 * 1) (by norm_num)]
  ring

theorem exists_SUid_two_mulEquiv_sl2 (p : ℕ) [Fact p.Prime] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ∧
      Nonempty (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 2 ≃*
        Matrix.SpecialLinearGroup (Fin 2) F₀) := by
  have hF := card_galoisField_two_mul_one p
  obtain ⟨ι⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
    (K := GaloisField p (2 * 1)) (r := p) (f := 1) hF
  refine ⟨CFSG.LieType.Steinberg.fixedSubfield (GaloisField p (2 * 1)) p 1, inferInstance,
    inferInstance, by rw [CFSG.LieType.Steinberg.card_fixedSubfield hF, pow_one], ?_⟩
  exact ⟨(MulEquiv.subgroupCongr (SUid_eq_statedSU hF 2)).trans ι.symm⟩

theorem isQuasisimple_SUid_two {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) :
    IsQuasisimple (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 2) := by
  obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := exists_SUid_two_mulEquiv_sl2 p
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 (by omega))

theorem false_of_epsQuot_SUid_two {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {X : Type} [Group X]
    [Finite X] (e : X ≃* SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 2)
    (hT : EpsQuot X) : False := by
  obtain ⟨F₀, _, _, hF₀, ⟨e₀⟩⟩ := exists_SUid_two_mulEquiv_sl2 p
  exact false_of_epsQuot_sl2 Fact.out h5 hF₀ (e.trans e₀) hT

end CFSG.RankThree.PartTwo.Sec4.RonanEps
