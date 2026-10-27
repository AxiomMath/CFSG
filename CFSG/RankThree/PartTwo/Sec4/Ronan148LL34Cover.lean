module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LL34Facts
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open (StatedSL StatedScalars StatedProj)

theorem l34_cover
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL 3 K)) :
    Nat.card (Subgroup.center L) ∣ 3 ∧ ∀ x : L, x ^ 3 ∈ Subgroup.center L → x ^ 3 = 1 := by
  have hoddZ : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨φ, hφs, hker, hDmap⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map (by norm_num : 2 ≤ 3) hoddZ e
  set D : Subgroup (StatedSL 3 K) := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) with hD
  have hD3 : Nat.card D ∣ 3 := by
    refine CFSG.SectionRank.OddCover.card_scalars_dvd (by norm_num) _ fun x c hc => ?_
    have hdet := CFSG.SectionRank.OddCover.det_of_mem_statedSL x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  refine ⟨?_, ?_⟩
  · rw [← hDmap]
    exact (D.card_map_dvd φ).trans hD3
  intro x hx
  by_cases hZ : Subgroup.center L = ⊥
  · rw [hZ, Subgroup.mem_bot] at hx
    exact hx
  have hkerbot : φ.ker = ⊥ := by
    have hd : Nat.card φ.ker ∣ Nat.card D := Subgroup.card_dvd_of_le hker
    rcases (Nat.dvd_prime Nat.prime_three).mp (hd.trans hD3) with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hDc : Nat.card D = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hD3 with h | h
        · rw [h, h3] at hd
          norm_num at hd
        · exact h
      have hkD : φ.ker = D := Subgroup.eq_of_le_of_card_ge hker (by rw [hDc, h3])
      apply hZ
      rw [← hDmap, ← hkD]
      exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  let eφ : StatedSL 3 K ≃* L := MulEquiv.ofBijective φ ⟨hinj, hφs⟩
  let s : Matrix.SpecialLinearGroup (Fin 3) K ≃* StatedSL 3 K :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 K).symm)
  let ψ : Matrix.SpecialLinearGroup (Fin 3) K ≃* L := s.trans eφ
  set M := ψ.symm x with hM
  have hM3 : M ^ 3 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply ψ.injective
    rw [map_mul, map_mul, map_pow, hM, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (ψ g)
  have hp : proj 3 K M ^ 3 = 1 := by
    rw [← map_pow, proj_eq_one_iff, scalars_eq_center]
    exact hM3
  have h := sl34_pow_three hK hp
  have hxM : x = ψ M := by rw [hM, MulEquiv.apply_symm_apply]
  rw [hxM, ← map_pow, h, map_one]

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
