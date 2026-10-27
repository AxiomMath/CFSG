module

public import CFSG.Quasithin.Background.F7TwoInvBenderInner
public import CFSG.Quasithin.Background.F7TwoInvU3TwoOuter
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.GH74.Bender
public import CFSG.CGT.Timmesfeld75.BenderInputsBasic

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Assembly.LowTwoRank CFSG.GH74.Uniqueness.Bender
open CFSG.GH74.Uniqueness (isSimpleGroup_of_isBenderGroup exists_not_commute_of_isBenderGroup)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

theorem invAutGen_of_statedPSU_two {S : Type} [Group S] {f : ℕ}
    (hf : 2 ≤ f) (h : StatedClassicalModel S .PSU 3 2 f) :
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ := by
  intro φ hφ2 hφ1
  have hB : CFSG.BenderSuzuki.IsBenderGroup S :=
    CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup
      (CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_stated_psu_three hf h)
  obtain ⟨n, i, e, hT⟩ := isBenderGroup_iff_exists_benderType.mp hB
  have : Finite S := CFSG.CGT.Timmesfeld75.finite_of_isBenderGroup hB
  by_cases hin : ∃ g : S, ∀ x : S, φ x = g * x * g⁻¹
  · obtain ⟨g, hg⟩ := hin
    have hφ : φ = MulAut.conj g := MulEquiv.ext hg
    have hZ := center_eq_bot_of_isSimpleGroup (isSimpleGroup_of_isBenderGroup hB)
      (exists_not_commute_of_isBenderGroup hB)
    have hg2 : g * g = 1 := by
      have hc : g * g ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h1 := MulEquiv.congr_fun hφ2 y
        rw [hφ] at h1
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
        calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
          _ = (g * g) * y := by group
      rwa [hZ, Subgroup.mem_bot] at hc
    have hg1 : g ≠ 1 := fun h1 => hφ1 (by rw [hφ, h1, map_one])
    rw [hφ]
    exact invAutGen_conj_of_benderType hT hg2 hg1
  · have hord : orderOf φ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφ2) hφ1
    have hout : φ ∉ (MulAut.conj : S →* MulAut S).range := by
      rintro ⟨g, hg⟩
      exact hin ⟨g, fun x => by rw [← hg]; rfl⟩
    obtain ⟨K, _, _, hU, ζ, hζ⟩ :=
      CFSG.LocalAnalysis.even_unitary_three_outer_involution_bar_conjugate hf h φ hord hout
    have : CharP K 2 := hU.charP
    have hP := InvAutGen.congr ζ (invAutGen_primeFormFieldAut_bar hU hf)
    have e : (ζ.symm.trans (primeFormFieldAut hU isPrimeFormGram_one
        (fieldDataHermitianForm hU).conj)).trans ζ = φ :=
      MulEquiv.ext fun y => by
        obtain ⟨x, rfl⟩ := ζ.surjective y
        simp [hζ]
    rwa [e] at hP

end CFSG.Quasithin.F7Two
