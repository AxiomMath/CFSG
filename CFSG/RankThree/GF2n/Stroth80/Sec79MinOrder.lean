module

public import CFSG.RankThree.GF2n.Stroth80.Sec79Split
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSecOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal
public import CFSG.RankThree.GF2n.Stroth80.OppDecompSplit

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix


theorem sec79MinOrder_of (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) : Sec79MinOrderStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 A hZA hAN hAR hAne m hm2
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hnormQ : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hNnorm : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, g * y * g⁻¹ ∈ hc.CN t := by
    intro g hg y hy
    refine mem_CN_conj_of_normalizes hc (hRM hg) ?_ ?_ hy
    · exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
    · exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hg)
  have hZ0n : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, g * y * g⁻¹ ∈ Z0 := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer (fun ρ hρ y hy => hnormQ ρ (hRM hρ) y hy) hg) y).mp hy
  have hAn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ A, x * y * x⁻¹ ∈ A := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ ∈ conjSubgroup x A := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hy
    rwa [hAR x hx] at h1
  have hNcomm : ∀ x ∈ hc.CN t, ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 := hopp.2.2.2.2.2.2.1
  have hcomm : ∀ x ∈ hc.CN t, ∀ y ∈ A, ⁅x, y⁆ ∈ Z0 := fun x hx y hy => hNcomm x hx y (hAN hy)
  have hVP : Z0 < A := lt_of_le_of_ne hZA (Ne.symm hAne)
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  refine ⟨fun hMinus => ?_, fun hPlus hm3 => ?_⟩
  · have hMinus' := hMinus
    obtain ⟨K₀, _, _, hK₀, b₀, c₀, hirr₀, hrep₀⟩ := hMinus
    have hcard₀ := card_of_naturalRep hrep₀ sec39_Z_le_Vt hK₀
    have hι₀ : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι₀] at hcard₀
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
    · exfalso
      have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      exact omegaSignStatement_holds G M Q Z B hc t m' hm2 ⟨K, hKf, hKfin, hKZ, hnat⟩ hMinus'
    · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      have hLu₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.minus hm' hirr).LomGL u := by
        rw [ElemMatrixIso.LomGL_minus hm' hirr]
        exact hLu
      have hLu₂ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.minus hm' hirr).LomGL u' := by
        rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]
        exact hLu'
      have hsplit := sec79_split_of_hom (ElemMatrixIso.minus hm' hirr)
        (nondegenerate_polarBilin_quadMinus_of_finite m' K hirr) (by omega) φ hrange hker
        hNnorm hZ0n hNcomm hopp hLR hL2R hu hu' huu' hLu₁ hLu₂ hZA hAN hAR
      have hdA := isOppDecomp_of_split hopp hZA hAN hsplit
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaMinus (ElemMatrixIso.minus hm' hirr) hm'
        (isMinus_quadMinus (by omega) hirr) φ hrange hker hAn hZ0n hcomm hdA hLR hL2R hu hu'
        huu' hLu₁ hLu₂
      rw [hKZ] at hk
      exact sec7_secOrder_ge hVP hq (Nat.one_le_two_pow) hk
  · have hPlus' := hPlus
    obtain ⟨K₀, _, _, hK₀, hrep₀⟩ := hPlus
    have hcard₀ := card_of_naturalRep hrep₀ sec39_Z_le_Vt hK₀
    have hι₀ : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι₀] at hcard₀
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
    · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      have hLu₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.plus hm').LomGL u := by
        rw [ElemMatrixIso.LomGL_plus hm']
        exact hLu
      have hLu₂ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
          (ElemMatrixIso.plus hm').LomGL u' := by
        rw [hLA, ElemMatrixIso.LomGL_plus hm']
        exact hLu'
      have hsplit := sec79_split_of_hom (ElemMatrixIso.plus hm')
        (nondegenerate_polarBilin_quadPlus m' K) (by omega) φ hrange hker
        hNnorm hZ0n hNcomm hopp hLR hL2R hu hu' huu' hLu₁ hLu₂ hZA hAN hAR
      have hdA := isOppDecomp_of_split hopp hZA hAN hsplit
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaPlus (ElemMatrixIso.plus hm') hm'
        (isPlus_quadPlus m') φ hrange hker hAn hZ0n hcomm hdA hLR hL2R hu hu' huu' hLu₁ hLu₂
      rw [hKZ] at hk
      exact sec7_secOrder_ge hVP hq (Nat.one_le_two_pow) hk
    · exfalso
      have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      obtain rfl : m' = m := sec7_pin_dim hq (by rw [← hcard, ← hcard₀])
      exact omegaSignStatement_holds G M Q Z B hc t m' hm2 hPlus'
        ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩

end CFSG.RankThree.GF2n.Stroth80
