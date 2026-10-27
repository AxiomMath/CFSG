module

public import CFSG.Sporadic.Co1Patterson.IndexNineBase

public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupSylow
public import Certificates.Certificate744110

public section

namespace CFSG.Sporadic.Co1Patterson.IndexNine

open Subgroup CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.Native
open CFSG.Sporadic.Co1Patterson.TwistNative
open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.QuasithinUnique CFSG.Blueprint

theorem co1_index_nine_package :
    IndexNinePackage (CFSG.Blueprint.NativeSporadic.Co1) := by
  classical
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Co1) :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  haveI : Finite ↥L₀ := Nat.finite_of_card_ne_zero (by rw [card_L₀]; norm_num)
  have hΔ : InnerIndexNinePackage L₀ := Certificates.certificate744110
  obtain ⟨Ubar, -, -, hUbar, -⟩ := id hΔ
  have hcardUbar : Nat.card Ubar = 2 ^ 12 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hU2, hidx⟩ := hUbar
    rw [show (Ubar.subgroupOf ⊤).index = Ubar.index from Subgroup.relIndex_top_right _] at hidx
    obtain ⟨j, hj⟩ := hU2.exists_card_eq
    have h1 := Subgroup.card_mul_index Ubar
    rw [hj, card_L₀] at h1
    have hi0 : Ubar.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 := congrArg (padicValNat 2) h1
    rw [padicValNat.mul (by positivity) hi0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hidx,
      show (174182400 : ℕ) = 2 ^ 12 * 42525 by norm_num, padicValNat.mul (by positivity)
        (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 42525)] at h2
    rw [hj, show j = 12 by omega]
  set C : Subgroup (CFSG.Blueprint.NativeSporadic.Co1) :=
    centralizer ({aNC} : Set CFSG.Blueprint.NativeSporadic.Co1) with hC
  set φ : ↥C →* L₀ := typeSystemC.φ with hφ
  set UC : Subgroup C := Ubar.comap φ with hUC
  set U : Subgroup (CFSG.Blueprint.NativeSporadic.Co1) := UC.map C.subtype with hUdef
  have hφsurj : Function.Surjective φ := by rw [hφ]; exact typeSystemC.φ_surj
  have hcardC : Nat.card C = 89181388800 := by rw [hC]; exact card_centralizer_aNC
  have hker_card : Nat.card φ.ker = 2 ^ 9 := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := φ) hφsurj
    rw [hcardC, card_L₀] at h
    omega
  have hkerP : IsPGroup 2 φ.ker := IsPGroup.of_card (n := 9) hker_card
  have hcardUC : Nat.card UC = 2 ^ 21 := by
    rw [hUC]
    have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card φ hφsurj Ubar
    rw [hker_card, hcardUbar] at h
    norm_num at h ⊢
    exact h
  have hcardU : Nat.card U = 2 ^ 21 := by
    rw [hUdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact hcardUC
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 21) hcardU, ?_⟩
    rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U,
      Subgroup.index_eq_card_div, CFSG.Sporadic.Co1.card_Co1, hcardU]
    norm_num
  have hNC : Subgroup.normalizer (U : Set (CFSG.Blueprint.NativeSporadic.Co1)) ≤ C := by
    let z : C := typeSystemC.z
    have hzU : (z : CFSG.Blueprint.NativeSporadic.Co1) ∈ U := by
      rw [hUdef]
      refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
      rw [hUC, Subgroup.mem_comap]
      change typeSystemC.φ typeSystemC.z ∈ Ubar
      rw [typeSystemC.φ_z]
      exact Ubar.one_mem
    have hz1 : (z : CFSG.Blueprint.NativeSporadic.Co1) ≠ 1 := by
      intro h
      exact typeSystemC.z_ne_one (Subtype.ext h)
    have hzcentral : ∀ y ∈ U,
        (z : CFSG.Blueprint.NativeSporadic.Co1) * y =
          y * (z : CFSG.Blueprint.NativeSporadic.Co1) := by
      intro y hy
      rw [hUdef] at hy
      obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hy
      simpa using congrArg Subtype.val (typeSystemC.z_comm c).symm
    have hcenter : ∀ x ∈ U,
        (∀ y ∈ U, x * y = y * x) → x = 1 ∨ x = (z : CFSG.Blueprint.NativeSporadic.Co1) := by
      intro x hx hxc
      rw [hUdef] at hx
      obtain ⟨c, hcUC, rfl⟩ := Subgroup.mem_map.mp hx
      have hcentQ : ∀ q ∈ twoAQC, c * q = q * c := by
        intro q hq
        have hqUC : q ∈ UC := by
          rw [hUC, Subgroup.mem_comap]
          rw [co1Phi_eq_one_iff.2 hq]
          exact Ubar.one_mem
        have hqU : (q : CFSG.Blueprint.NativeSporadic.Co1) ∈ U := by
          rw [hUdef]
          exact Subgroup.mem_map.mpr ⟨q, hqUC, rfl⟩
        exact Subtype.ext (hxc (q : CFSG.Blueprint.NativeSporadic.Co1) hqU)
      have hcQ : c ∈ twoAQC :=
        twoAQC_centralizer_le (Subgroup.mem_centralizer_iff.mpr
          (fun q hq => (hcentQ q hq).symm))
      have hφc : typeSystemC.φ c = 1 := co1Phi_eq_one_iff.2 hcQ
      have hcomm : ∀ p : C, typeSystemC.φ p = 1 → p * c = c * p := by
        intro p hp
        exact (hcentQ p (co1Phi_eq_one_iff.1 hp)).symm
      rcases typeSystemC.center_eq c hφc hcomm with h | h
      · exact Or.inl (by simpa using congrArg Subtype.val h)
      · exact Or.inr (by simpa using congrArg Subtype.val h)
    have hN := CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.normalizer_le_centralizer_of_center
      hzU hz1 hzcentral hcenter
    have hCeq : Subgroup.centralizer ({(z : CFSG.Blueprint.NativeSporadic.Co1)} :
        Set (CFSG.Blueprint.NativeSporadic.Co1)) = C := by
      rw [show (z : CFSG.Blueprint.NativeSporadic.Co1) = aNC from rfl, hC]
    exact hN.trans (le_of_eq hCeq)
  refine indexNinePackage_of_quotient (Γ := CFSG.Blueprint.NativeSporadic.Co1) (Δ := L₀)
    (U := U) (C := C) (fun α => ?_) hU hNC φ hφsurj hkerP hΔ
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.SPOR.allInner_Co1 α
  refine ⟨g, fun x => ?_⟩
  rw [hg]
  exact MulAut.conj_apply g x

end CFSG.Sporadic.Co1Patterson.IndexNine
