module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3Modules
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.RankThree.GF2n.Smith81.SubConfigOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_SU3MinDegree_holds : K_SU3MinDegree := by
  intro X _ _ n hX hn2
  have : Nontrivial (X ⧸ Subgroup.center X) := hX.1.2.toNontrivial
  have : Nontrivial X :=
    (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  obtain ⟨f, hf⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.exists_nontrivial_repr_dMinDeg X
  have hker : f.ker ≤ Subgroup.center X := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX.1
      f.ker with h | h
    · exact h
    · exfalso
      apply hf
      apply MonoidHom.ext
      intro x
      simpa using MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
  have hcardX : Nat.card (X ⧸ Subgroup.center X) = CFSG.Open.ordTwistedA 2 (2 ^ n) := by
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : (3 : ℕ) ≠ 0) hX.2]
    rfl
  obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * n)
    (by omega) (by omega)
  have hzU : CFSG.Timmesfeld.Orders.zU 2 n (6 * n) := by
    have h := CFSG.Timmesfeld.Orders.zU_top (n := 2) (g := n) (t := 1)
      (Or.inl (by norm_num)) (by norm_num) (by omega)
    rwa [show 2 * (n * (2 * 1 + 1)) = 6 * n by ring] at h
  have hdvdOrder : r ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [hcardX]
    exact ((CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := n)
      (by norm_num) (by omega)).prim r (6 * n) hr (by omega)).mpr hzU
  have hrange : Nat.card f.range = Nat.card (X ⧸ f.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
  have hcard1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hker
  have hdiv : Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card f.range := by
    refine ⟨m, ?_⟩
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    have heq : Nat.card (X ⧸ Subgroup.center X) * m = Nat.card f.range := by
      apply Nat.eq_of_mul_eq_mul_right hkpos
      calc (Nat.card (X ⧸ Subgroup.center X) * m) * Nat.card f.ker
          = Nat.card (X ⧸ Subgroup.center X) * (Nat.card f.ker * m) := by ring
        _ = Nat.card (X ⧸ Subgroup.center X) * Nat.card (Subgroup.center X) := by rw [← hm]
        _ = Nat.card X := hcard1.symm
        _ = Nat.card (X ⧸ f.ker) * Nat.card f.ker := hcard2
        _ = Nat.card f.range * Nat.card f.ker := by rw [← hrange]
    exact heq.symm
  have hGLdvd : r ∣ Nat.card (Matrix.GeneralLinearGroup (Fin (dMinDeg X)) (ZMod 2)) := by
    have h := (hdvdOrder.trans hdiv).trans
      (Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤))
    simpa using h
  have hprod : r ∣ ∏ i : Fin (dMinDeg X), (2 ^ dMinDeg X - 2 ^ (i : ℕ)) := by
    rw [Matrix.card_GL_field (𝔽 := ZMod 2) (dMinDeg X), ZMod.card] at hGLdvd
    exact hGLdvd
  obtain ⟨j, hj1, hjd, hdvdj⟩ :=
    CFSG.RankThree.GF2n.Smith81.SubCfg.exists_dvd_of_ppd_dvd_prod_GL
      (g := 1) (n := dMinDeg X) hr (by omega) (by simpa using hprod)
  have hdvdnj : 6 * n ∣ j := by simpa using hdvdj
  have hle : 6 * n ≤ j := Nat.le_of_dvd (by omega) hdvdnj
  exact hle.trans hjd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
