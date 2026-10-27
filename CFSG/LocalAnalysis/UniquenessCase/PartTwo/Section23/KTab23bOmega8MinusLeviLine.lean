module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8MinusLeviFixed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8MinusLeviLeast
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8MinusLeviResidual

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Least

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem omegaMinus8Line_t3H (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) :
    OmegaMinus8Line (Multiplicative (T3V K)) (T3H K b c) m := by
  letI : MulDistribMulAction ↥(T3H K b c) (Multiplicative (T3V K)) :=
    MulDistribMulAction.compHom (Multiplicative (T3V K)) (T3H K b c).subtype
  letI : MulAction ↥(T3H K b c) (Multiplicative (T3V K)) :=
    MulAction.compHom (Multiplicative (T3V K)) (T3H K b c).subtype
  letI : MulAction ↥(T3H K b c) (Set (Multiplicative (T3V K))) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S (Multiplicative (T3V K)) :=
    MulDistribMulAction.compHom (Multiplicative (T3V K))
      ((T3H K b c).subtype.comp (S : Subgroup ↥(T3H K b c)).subtype)
  let ℓ : Subgroup (Multiplicative (T3V K)) :=
    fixedPointSubgroup ↥S (Multiplicative (T3V K))
  let Pℓ : Subgroup ↥(T3H K b c) :=
    MulAction.stabilizer ↥(T3H K b c) (ℓ : Set (Multiplicative (T3V K)))
  dsimp only
  intro Tstar hTH hT hST
  intro Pstar hmin
  obtain ⟨h, hS⟩ := exists_map_conj_eq_of_sylow (K := K) (b := b) (c := c) hirr S
  have hPℓ : Pℓ = t3PℓH K b c h :=
    stabilizer_fixedPointSubgroup_eq_t3PℓH (K := K) (b := b) (c := c) hirr S h hS
  have hPℓ_fix : ∀ t ∈ Tstar,
      (Pℓ.map (T3H K b c).subtype).map (MulAut.conj t).toMonoidHom =
        Pℓ.map (T3H K b c).subtype :=
    KAdjE.map_conj_stabilizer_fixedPoint_eq (T3H K b c) S Tstar hTH hT hST
  let Pα : Subgroup ↥(T3H K b c) := (t3P0H K b c).map (MulAut.conj h).toMonoidHom
  have hpar : IsParabolicTwo ↥(T3H K b c) Pα :=
    t3P0H_map_conj_isParabolicTwo (K := K) (b := b) (c := c) hirr h
  have hSP : (S : Subgroup ↥(T3H K b c)) ≤ Pα := by
    rw [hS]
    exact map_conj_t3UH_le_map_conj_t3P0H (K := K) (b := b) (c := c) hirr h
  have hnot : ¬ Pα ≤ Pℓ := by
    rw [hPℓ]
    exact t3P0H_map_conj_not_le_t3PℓH (K := K) (b := b) (c := c) hirr h
  have hle : ∀ P : Subgroup ↥(T3H K b c), IsParabolicTwo ↥(T3H K b c) P →
      (S : Subgroup ↥(T3H K b c)) ≤ P → ¬ P ≤ Pℓ → Pα ≤ P := by
    intro P hP hSP' hnot'
    exact t3P0H_map_conj_le_of_parabolic (K := K) (b := b) (c := c) hirr S h hS hP hSP'
      (hPℓ ▸ hnot')
  have hPeq : Pstar = Pα :=
    KAdjE.minimal_good_eq_of_least_parabolic (T3H K b c) S Pℓ Tstar hTH hT hST hPℓ_fix
      hpar hSP hnot hle hmin
  rw [hPeq]
  exact ⟨t3P0H_map_conj_ne_top (K := K) (b := b) (c := c) hirr h,
    t3P0H_map_conj_residual (K := K) (b := b) (c := c) hirr hK h⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi
