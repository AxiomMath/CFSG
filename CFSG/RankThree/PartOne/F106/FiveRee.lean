module

import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.N143X.ReeRank

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC
  CFSG.RankThree.PartOne.N143X CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne.BRANCH

theorem card_le_ree_three
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f)
    {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 ^ 3 := by
  classical
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_gamma_of_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv X e.toEquiv
  have hE3 : ∀ x ∈ E.map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE y hy, map_one]
  have hcard' : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK'
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have horder := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK').1
  have hmod3 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rcases BRANCH.two_pow_mod_three (2 * a + 1) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (by simp)
    · exact h
  have hQ2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb := card_le_of_sector_three D (odd_mPhi2' a) (torusParam_phi2 D.isFrob)
    (fun i hi => not_nine_dvd_ree_twisted hQ2 hmod3 (by
      rw [mPhi2] at hi
      rw [horder] at hi
      rw [mul_comm] at hi
      exact hi)) hE3
  rw [hcard'] at hb
  simpa using hb

theorem false_ree_three_five
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ReeTitsModel X .twistedF4 2 f)
    {E : Subgroup X} (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 5) : False := by
  have hb := card_le_ree_three hX
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) x hx)
  rw [hcard] at hb
  norm_num at hb

end CFSG.RankThree.PartOne.F106
