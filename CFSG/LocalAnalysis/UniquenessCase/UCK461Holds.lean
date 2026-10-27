module

public import CFSG.LocalAnalysis.UniquenessCase.UCKAsc82Q64Fix
public import CFSG.LocalAnalysis.UniquenessCase.UC6K46Main
public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanMain
public import CFSG.LocalAnalysis.UniquenessCase.UCInspJ1
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Main
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Main
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.FFModules (fixSub)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open scoped MatrixGroups

theorem k461_of_inputsFix (h46 : K46List) (hJ1 : InspJ1) (hL3 : InspL3) (hL2 : InspL2)
    (hex : L2Exceptional) (hQ : Asc82Q64Fix) (hH : HigmanNatSL2) (hK42 : K42) : K461 := by
  intro G _ _ hK V _ _ _ ρ hρ hirr D hD hDG hfix h3 hperf
  haveI : ρ.IsIrreducible := hirr
  have hfixV : fixV ρ D = ⊥ := by
    rw [← hfix]
    exact Submodule.ext fun v => Iff.rfl
  have hno : ∀ (ℓ : ℕ) (R : Subgroup G), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → IsPGroup ℓ R →
      IsMulCommutative ↥R → R ≠ ⊥ → D ≤ normalizer (R : Set G) → ⁅D, R⁆ = R → False := by
    intro ℓ R hℓ hℓ2 hℓ3 hRp hRab hRne hDR hRcomm
    exact (hK42 2 Nat.prime_two G hK V ρ hρ ℓ 3 hℓ Nat.prime_three hℓ2 (by norm_num) hℓ3 D hD
      hfixV R hRp hRne hDR hRcomm).1 hRab
  have hL3case : ((∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel G .PSU 3 p f)) → False := by
    intro h
    obtain ⟨ℓ, R, hℓ, hℓ2, hℓ3, hRp, hRab, hRne, hDR, hRcomm⟩ := hL3 G h D hD
    exact hno ℓ R hℓ hℓ2 hℓ3 hRp hRab hRne hDR hRcomm
  rcases h46 G hK V ρ hρ hirr D hD hDG hfix h3 hperf with
    ⟨p, f, hmodel⟩ | ⟨p, f, hmod, hmodel⟩ | ⟨p, f, hmod, hmodel⟩ | hspor |
    ⟨F, _, _, hFodd, ⟨φ⟩⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact ⟨f, hH G f hmodel V ρ hρ hirr D hD hfix⟩
    · obtain ⟨hpp, hf1, -, -, hne3⟩ := hmodel.admissible
      have hodd : Odd (p ^ f) := (hpp.odd_of_ne_two hp2).pow
      have hp3 : 3 ≤ p := by
        have := hpp.two_le
        have := hpp.odd_of_ne_two hp2
        obtain ⟨k, hk⟩ := this
        omega
      have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
      have hq3' : p ^ f ≠ 3 := fun h => hne3 (by rw [h])
      obtain ⟨q, hq⟩ : ∃ q, q = p ^ f := ⟨_, rfl⟩
      rw [← hq] at hodd hq3 hq3'
      obtain ⟨k, hk⟩ := hodd
      by_cases h5 : q = 5
      · have := (hex G p f hp2 hmodel).1 (hq ▸ h5)
        exact ⟨2, hH G 2 this V ρ hρ hirr D hD hfix⟩
      by_cases h7 : q = 7
      · have := (hex G p f hp2 hmodel).2.1 (hq ▸ h7)
        exact (hL3case (Or.inl ⟨2, 1, by norm_num, this⟩)).elim
      by_cases h9 : q = 9
      · have := (hex G p f hp2 hmodel).2.2 (hq ▸ h9)
        omega
      exfalso
      have hbig : 9 < p ^ f := by
        rw [← hq]
        omega
      obtain ⟨S, hSel, hS4, hDS, hSc⟩ := hL2 G p f hp2 hmodel h3 D hD
      exact hQ G p f hp2 hbig hmodel V ρ hρ hirr D hD hfix S hSel hS4 hDS hSc
        (quadratic_of_fixSub_bot_uc6 ρ hD hfix hSel hS4 hDS hSc)
  · exact (hL3case (Or.inl ⟨p, f, hmod, hmodel⟩)).elim
  · exact (hL3case (Or.inr ⟨p, f, hmod, hmodel⟩)).elim
  · exfalso
    obtain ⟨R, hR7, hRab, hRne, hDR, hRcomm⟩ := hJ1 G hspor D hD
    exact hno 7 R (by norm_num) (by norm_num) (by norm_num) hR7 hRab hRne hDR hRcomm
  · exfalso
    obtain ⟨z, hzc, hz2, hz1⟩ := exists_central_involution_sl2_uc6 hFodd
    have hzc' : φ.symm z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (Subgroup.mem_center_iff.1 hzc (φ g)).symm ▸ rfl
    have hz2' : φ.symm z ^ 2 = 1 := by
      apply φ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hz2, map_one]
    have := central_involution_false_uc6 ρ hρ hzc' hz2'
    apply hz1
    rw [← MulEquiv.apply_symm_apply φ z, this, map_one]

section


theorem k461_of_asc82q64Fix
    (hQ : Asc82Q64Fix) : K461 :=
  k461_of_inputsFix k46List_holds inspJ1_holds inspL3_holds inspL2_holds l2Exceptional_holds hQ
    higmanNatSL2_holds UC6.k42_uc6

theorem k461_holds
    : K461 :=
  k461_of_asc82q64Fix asc82Q64Fix_holds

end

end CFSG.LocalAnalysis.UniquenessCase.UCK
