module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.RankThree.PartTwo.Sec4

theorem ys03_N06_exists_primitiveRoot_three (K : Type) [Field K] [Finite K]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 4 ^ m) : ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h4mod : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h4le : 4 ≤ 4 ^ m :=
    calc (4 : ℕ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hdvd : 3 ∣ 4 ^ m - 1 := by omega
  have hunits : Nat.card Kˣ = 4 ^ m - 1 := by
    rw [Nat.card_units, hK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hprim : IsPrimitiveRoot (g : K) (Nat.card Kˣ) :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hord)
  rw [hunits] at hprim
  have hk0 : (4 ^ m - 1) / 3 ≠ 0 := by omega
  have hdiv : (4 ^ m - 1) / ((4 ^ m - 1) / 3) = 3 :=
    Nat.div_div_self hdvd (by omega)
  refine ⟨(g : K) ^ ((4 ^ m - 1) / 3), ?_⟩
  have h := hprim.pow_of_dvd hk0 (Nat.div_dvd_of_dvd hdvd)
  rwa [hdiv] at h

theorem ys03_N06_card_center_SL {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * m))) :
    Nat.card (Subgroup.center X) = 3 := by
  have hcard : Nat.card (GaloisField 2 (2 * m)) = 4 ^ m := by
    rw [GaloisField.card 2 (2 * m) (by omega), pow_mul]
    norm_num
  obtain ⟨ζ, hζ⟩ := ys03_N06_exists_primitiveRoot_three (GaloisField 2 (2 * m)) hm hcard
  have hX : Nat.card (Subgroup.center X) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * m)))) := by
    rw [← Subgroup.map_center_eq e]
    exact Nat.card_congr (MulEquiv.subgroupMap e (Subgroup.center X)).toEquiv
  rw [hX, Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    Fintype.card_fin]
  exact hζ.card_rootsOfUnity

end CFSG.RankThree.PartTwo.Sec4

end
