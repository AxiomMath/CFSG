module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Induction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.L3Conj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.L3Step

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Subgroup

theorem l3_stepConcl_model {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 2) (h9 : ¬ 9 ∣ Nat.card (projectiveSL 3 K))
    (h7 : ¬ 7 ∣ Nat.card (projectiveSL 3 K)) (W : Subgroup (MulAut (projectiveSL 3 K)))
    (hW7 : Nat.card W = 7) (Z : Subgroup (projectiveSL 3 K))
    (hZ3 : Nat.card Z = 3) (hZ : ∀ w ∈ W, ∀ z ∈ Z, w z = z) : StepConcl GoodL3 W Z := by
  have hq3 : ¬ 3 ∣ Nat.card K - 1 := by
    intro hdvd
    have hmod : (Nat.card K - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hpos : 0 < Nat.card K := Nat.card_pos
    have h : Nat.card K % 3 = ((Nat.card K - 1) % 3 + 1) % 3 := by
      have hK : Nat.card K = (Nat.card K - 1) + 1 := by omega
      rw [hK, Nat.add_mod]
      norm_num
    rw [hmod] at h
    norm_num at h
    omega
  obtain ⟨h, σ, hσ, hK, hW⟩ := exists_conj_zpowers_fieldAut_of_card_seven hq3 h7 W hW7
  have hWmap : W.map (MulAut.congr h.symm).toMonoidHom =
      Subgroup.zpowers (fieldAut 3 K σ) := by
    rw [hW]
    have hcomp : (MulAut.congr h.symm).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id (MulAut (projectiveSL 3 K)) := by
      ext φ x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.congr_apply, MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
        MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply,
        MulEquiv.apply_symm_apply]
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hZfix : ∀ w ∈ W.map (MulAut.congr h.symm).toMonoidHom,
      ∀ z ∈ Z.map h.symm.toMonoidHom, w z = z := by
    rintro w ⟨u, hu, rfl⟩ z ⟨z', hz', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
      hZ u hu z' hz']
  apply stepConcl_of_mulEquiv GoodL3 goodL3_of_mulEquiv h.symm W Z
  rw [hWmap]
  refine l3_stepConcl_zpowers hq h9 h7 σ hσ hK (Z.map h.symm.toMonoidHom) ?_ ?_
  · rw [Subgroup.card_map_of_injective h.symm.injective, hZ3]
  · intro w hw z hz
    rw [← hWmap] at hw
    exact hZfix w hw z hz

theorem l3_stepConcl {J : Type} [Group J] [Finite J] (hJ : GoodL3 J)
    (W : Subgroup (MulAut J)) (hW7 : Nat.card W = 7) (Z : Sylow 3 J)
    (hZ : ∀ w ∈ W, ∀ z ∈ (Z : Subgroup J), w z = z) : StepConcl GoodL3 W (Z : Subgroup J) := by
  obtain ⟨-, h3, h9, h7, ⟨K, hKfield, hKfin, hq, ⟨e⟩⟩⟩ := hJ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card J = Nat.card (projectiveSL 3 K) := Nat.card_congr e.toEquiv
  have h9K : ¬ 9 ∣ Nat.card (projectiveSL 3 K) := by rwa [← hcard]
  have h7K : ¬ 7 ∣ Nat.card (projectiveSL 3 K) := by rwa [← hcard]
  have hcardZ : Nat.card Z = 3 := by
    rw [Sylow.card_eq_multiplicity]
    have hfac : (Nat.card J).factorization 3 = 1 := by
      have h1 : 1 ≤ (Nat.card J).factorization 3 :=
        (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
      have h2 : (Nat.card J).factorization 3 < 2 := by
        by_contra hcon
        have hle : 2 ≤ (Nat.card J).factorization 3 := by omega
        have h9' : ¬ 3 ^ 2 ∣ Nat.card J := by simpa using h9
        exact h9' ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
          Nat.card_pos.ne').mpr hle)
      omega
    rw [hfac, pow_one]
  apply stepConcl_of_mulEquiv GoodL3 goodL3_of_mulEquiv e W (Z : Subgroup J)
  have hW' : Nat.card (W.map (MulAut.congr e).toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hW7]
  have hZ3' : Nat.card ((Z : Subgroup J).map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcardZ]
  have hZfix' : ∀ w ∈ W.map (MulAut.congr e).toMonoidHom,
      ∀ z ∈ (Z : Subgroup J).map e.toMonoidHom, w z = z := by
    rintro w ⟨u, hu, rfl⟩ z ⟨z', hz', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, hZ u hu z' hz']
  exact l3_stepConcl_model hq h9K h7K (W.map (MulAut.congr e).toMonoidHom) hW'
    ((Z : Subgroup J).map e.toMonoidHom) hZ3' hZfix'

theorem sevenFree_of_goodL3 {J : Type} [Group J] (hJ : GoodL3 J) :
    SevenFree J :=
  sevenFree_of_prime_step GoodL3 (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun _ _ _ hJ W _ hW7 Z hZ => l3_stepConcl hJ W hW7 Z hZ) J hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
