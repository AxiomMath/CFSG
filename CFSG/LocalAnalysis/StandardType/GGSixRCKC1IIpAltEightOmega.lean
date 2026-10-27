module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpSLOrder
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightSU
import CFSG.RankThree.GF2n.Smith81.InspKOmegaCard
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusModel
import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
import CFSG.LieType.Universal.Spin
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusConj
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlus

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType

theorem rckIIp_false_of_alt_eight_POmegaPlus
    {X : Type} [Group X] {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f)
    (π : (ggU .POmegaPlus r f).K →* X)
    (hker : π.ker ≤ Subgroup.center (ggU .POmegaPlus r f).K)
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    False := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 4 := ⟨r - 4, by omega⟩
  let F := GaloisField 2 f
  have hcardF : Nat.card F = 2 ^ f :=
    GaloisField.card (p := 2) (n := f) (by omega)
  have hcenter : Subgroup.center (ggU .POmegaPlus (k + 4) f).K = ⊥ :=
    CFSG.SeitzReduction.OmegaPilot.center_spinGroup_quadPlus_eq_bot'
      (F := F) (n := k + 4) (by omega)
  have hkerbot : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Subgroup.center (ggU .POmegaPlus (k + 4) f).K := hker hx
    rwa [hcenter] at hx'
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hkerbot
  have hbij : Function.Bijective π.rangeRestrict := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  let e : (ggU .POmegaPlus (k + 4) f).K ≃* ↥π.range :=
    MulEquiv.ofBijective π.rangeRestrict hbij
  have hZJbot : Subgroup.center ↥π.range = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hcenter, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hcardZJ : Nat.card (Subgroup.center ↥π.range) = 1 := by
    rw [hZJbot, Subgroup.card_bot]
  have hcardJ : Nat.card ↥π.range = 20160 * Nat.card (Subgroup.center ↥π.range) :=
    rckIIp_card_range_of_alt_eight π hA8
  have hJ20160 : Nat.card ↥π.range = 20160 := by rw [hcardJ, hcardZJ, mul_one]
  have hGJ : Nat.card (ggU .POmegaPlus (k + 4) f).K = Nat.card ↥π.range :=
    Nat.card_congr e.toEquiv
  have hcardG : Nat.card (ggU .POmegaPlus (k + 4) f).K = 20160 := by
    rw [hGJ, hJ20160]
  have hcardord : Nat.card (ggU .POmegaPlus (k + 4) f).K
      = CFSG.Open.ordD (k + 4) (2 ^ f) :=
    CFSG.RankThree.GF2n.Smith81.Insp.KFact.card_spinGroup_quadPlus
      (K := F) (n := k + 4) (by omega) hf hcardF
  obtain ⟨u, -, hord⟩ :=
    CFSG.RankThree.GF2n.Smith81.Insp.KFact.exists_ordD_eq
      (n := k + 4) (f := f) (by omega) hf
  have hprod : 12 ≤ (k + 4) * ((k + 4) - 1) := by
    have h1 : 4 ≤ k + 4 := by omega
    have h2 : 3 ≤ (k + 4) - 1 := by omega
    calc 12 = 4 * 3 := by norm_num
      _ ≤ (k + 4) * ((k + 4) - 1) := Nat.mul_le_mul h1 h2
  have h12 : 12 ≤ f * ((k + 4) * ((k + 4) - 1)) := by
    calc 12 = 1 * 12 := (one_mul 12).symm
      _ ≤ f * ((k + 4) * ((k + 4) - 1)) := Nat.mul_le_mul hf hprod
  have hdvd : 2 ^ 12 ∣ Nat.card (ggU .POmegaPlus (k + 4) f).K := by
    rw [hcardord, hord]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 h12) u
  rw [hcardG] at hdvd
  exact (by norm_num : ¬ (2 ^ 12 ∣ 20160)) hdvd

theorem rckIIp_eq_one_of_alt_eight_POmegaPlus_three
    {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f) (π : (ggU .POmegaPlus 3 f).K →* X)
    (hker : π.ker ≤ Subgroup.center (ggU .POmegaPlus 3 f).K)
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    f = 1 := by
  classical
  let F := GaloisField 2 f
  let e : (ggU .POmegaPlus 3 f).K ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv (F := F)
  let π' : Matrix.SpecialLinearGroup (Fin 4) F →* X := π.comp e.symm.toMonoidHom
  have hrange : π'.range = π.range := by
    change (π.comp e.symm.toMonoidHom).range = π.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective, Subgroup.map_top]
  have hker' : π'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) := by
    have h1 : π'.ker = π.ker.map e.toMonoidHom :=
      MonoidHom.ker_comp_mulEquiv π e.symm
    rw [h1]
    exact (Subgroup.map_mono hker).trans (le_of_eq (Subgroup.map_center_eq e))
  have hodd' : Odd (Nat.card (Subgroup.center ↥π'.range)) := by
    rw [hrange]
    exact hodd
  have hA8' : Nonempty ((↥π'.range ⧸ Subgroup.center ↥π'.range) ≃*
      alternatingGroup (Fin 8)) := by
    rw [hrange]
    exact hA8
  exact (rckIIp_eq_three_one_of_alt_eight (k := 3) (h := f) hf π' hker' hodd' hA8').2

theorem rckIIp_false_of_alt_eight_POmegaMinus
    {X : Type} [Group X] {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f)
    (π : (ggU .POmegaMinus r f).K →* X)
    (hker : π.ker ≤ Subgroup.center (ggU .POmegaMinus r f).K)
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    False := by
  classical
  let F := GaloisField 2 f
  have hoddZ : Odd (Nat.card (Subgroup.center ↥π.range)) := hodd
  have hcardF : Nat.card F = 2 ^ f :=
    GaloisField.card (p := 2) (n := f) (by omega)
  have hirr : ∀ s : F, s ^ 2 +
      (CFSG.LieType.Universal.minusCoeffs 2 f).1 * s +
        (CFSG.LieType.Universal.minusCoeffs 2 f).2 ≠ 0 :=
    CFSG.LieType.Universal.minusCoeffs_irr 2 f
  have hcenter : Subgroup.center (ggU .POmegaMinus r f).K = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (n := r) hr (b := (CFSG.LieType.Universal.minusCoeffs 2 f).1)
      (c := (CFSG.LieType.Universal.minusCoeffs 2 f).2) hirr
  have hkerbot : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ Subgroup.center (ggU .POmegaMinus r f).K := hker hx
    rwa [hcenter] at hx'
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hkerbot
  have hbij : Function.Bijective π.rangeRestrict := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  let e : (ggU .POmegaMinus r f).K ≃* ↥π.range :=
    MulEquiv.ofBijective π.rangeRestrict hbij
  have hZJbot : Subgroup.center ↥π.range = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hcenter, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hcardZJ : Nat.card (Subgroup.center ↥π.range) = 1 := by
    rw [hZJbot, Subgroup.card_bot]
  have hcardJ : Nat.card ↥π.range = 20160 * Nat.card (Subgroup.center ↥π.range) :=
    rckIIp_card_range_of_alt_eight π hA8
  have hJ20160 : Nat.card ↥π.range = 20160 := by rw [hcardJ, hcardZJ, mul_one]
  have hGJ : Nat.card (ggU .POmegaMinus r f).K = Nat.card ↥π.range :=
    Nat.card_congr e.toEquiv
  have hcardG : Nat.card (ggU .POmegaMinus r f).K = 20160 := by
    rw [hGJ, hJ20160]
  have hcardord : Nat.card (ggU .POmegaMinus r f).K
      = CFSG.Open.ordTwistedD r (2 ^ f) :=
    CFSG.RankThree.GF2n.Smith81.Insp.KFact.card_spinGroup_quadMinus
      (K := F) (n := r) (b := (CFSG.LieType.Universal.minusCoeffs 2 f).1)
      (c := (CFSG.LieType.Universal.minusCoeffs 2 f).2) hirr hr hf hcardF
  obtain ⟨u, -, hord⟩ :=
    CFSG.RankThree.GF2n.Smith81.Insp.KFact.exists_ordTwistedD_eq
      (n := r) (f := f) (by omega) hf
  have hprod : 12 ≤ r * (r - 1) := by
    have h1 : 4 ≤ r := hr
    have h2 : 3 ≤ r - 1 := by omega
    calc 12 = 4 * 3 := by norm_num
      _ ≤ r * (r - 1) := Nat.mul_le_mul h1 h2
  have h12 : 12 ≤ f * (r * (r - 1)) := by
    calc 12 = 1 * 12 := (one_mul 12).symm
      _ ≤ f * (r * (r - 1)) := Nat.mul_le_mul hf hprod
  have hdvd : 2 ^ 12 ∣ Nat.card (ggU .POmegaMinus r f).K := by
    rw [hcardord, hord]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 h12) u
  rw [hcardG] at hdvd
  exact (by norm_num : ¬ (2 ^ 12 ∣ 20160)) hdvd

theorem rckIIp_false_of_alt_eight_POmegaMinus_three
    {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f) (π : (ggU .POmegaMinus 3 f).K →* X)
    (hker : π.ker ≤ Subgroup.center (ggU .POmegaMinus 3 f).K)
    (hodd : Odd (Nat.card (Subgroup.center ↥π.range)))
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    False := by
  classical
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  let F := GaloisField 2 (g + 1)
  let K := GaloisField 2 (2 * (g + 1))
  have hcardF : Nat.card F = 2 ^ (g + 1) :=
    GaloisField.card (p := 2) (n := g + 1) (by omega)
  have hcardK : Nat.card K = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hirr : ∀ s : F, s ^ 2 +
      (CFSG.LieType.Universal.minusCoeffs 2 (g + 1)).1 * s +
        (CFSG.LieType.Universal.minusCoeffs 2 (g + 1)).2 ≠ 0 :=
    CFSG.LieType.Universal.minusCoeffs_irr 2 (g + 1)
  obtain ⟨_, e, -⟩ :=
    CFSG.RankThree.PartOne.CTP.SU4Even.exists_equiv_su_four_even
      (F := F) (K := K) (f := g + 1)
      (b := (CFSG.LieType.Universal.minusCoeffs 2 (g + 1)).1)
      (c := (CFSG.LieType.Universal.minusCoeffs 2 (g + 1)).2)
      hcardF hcardK hirr
  let e' : (ggU .POmegaMinus 3 (g + 1)).K ≃* (ggU .PSU 4 (g + 1)).K := e
  let π' : (ggU .PSU 4 (g + 1)).K →* X := π.comp e'.symm.toMonoidHom
  have hrange : π'.range = π.range := by
    change (π.comp e'.symm.toMonoidHom).range = π.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e'.symm.surjective, Subgroup.map_top]
  have hker' : π'.ker ≤ Subgroup.center (ggU .PSU 4 (g + 1)).K := by
    have h1 : π'.ker = π.ker.map e'.toMonoidHom :=
      MonoidHom.ker_comp_mulEquiv π e'.symm
    rw [h1]
    exact (Subgroup.map_mono hker).trans (le_of_eq (Subgroup.map_center_eq e'))
  have hodd' : Odd (Nat.card (Subgroup.center ↥π'.range)) := by
    rw [hrange]
    exact hodd
  have hA8' : Nonempty ((↥π'.range ⧸ Subgroup.center ↥π'.range) ≃*
      alternatingGroup (Fin 8)) := by
    rw [hrange]
    exact hA8
  exact rckIIp_false_of_alt_eight_PSU (r := 4) (h := g + 1) (by omega) π' hker' hodd' hA8'

end CFSG.StandardType.RCKC1
