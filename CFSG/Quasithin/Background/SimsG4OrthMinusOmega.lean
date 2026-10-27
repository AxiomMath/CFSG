module

public import CFSG.Quasithin.Background.SimsG4OrthMinusModel
import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.Quasithin.SimsG4.OrthMinus

open Module Matrix QuadraticMap CFSG.Quasithin.SimsG4
open scoped commutatorElement

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem natCard_orthogonalGroup [Finite K] [CharP K 2] (Q : QuadraticForm K W)
    (hdim : finrank K W = 4) (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hminus : ∀ U : Submodule K W, (∀ u ∈ U, Q u = 0) → finrank K U ≤ 1) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * ((Nat.card K ^ 2) * ((Nat.card K ^ 2) ^ 2 - 1)) := by
  obtain ⟨c, hc⟩ := exists_irred_quadratic (K := K)
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have hQminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    rintro ⟨U, hU, hUs⟩
    have := hminus U hUs
    omega
  obtain ⟨α⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType
    (polarBilin_nondegenerate Q hnd) (n := 2) (by norm_num) (by rw [hdim]) hQminus hc
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hc 1
  rw [← CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr α] at h
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have h4 : 1 ≤ (Nat.card K ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [h4]
  rw [h]
  simp
  ring

variable [Finite K] [CharP K 2]

theorem range_eq_commutator (Q : QuadraticForm K W) (hdim : finrank K W = 4)
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hminus : ∀ U : Submodule K W, (∀ u ∈ U, Q u = 0) → finrank K U ≤ 1)
    {L : Type} [Field L] [Finite L] (hL : Nat.card L = Nat.card K ^ 2)
    (ρ : SpecialLinearGroup (Fin 2) L →* (W ≃ₗ[K] W)) (hρ : Function.Injective ρ)
    (hρQ : ∀ g x, Q (ρ g x) = Q x) :
    ρ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      ((⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set P := ρ.range with hP
  have hle : P ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (hρQ g)
  have hcardP : Nat.card P = Nat.card (SpecialLinearGroup (Fin 2) L) :=
    (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) L) =
      (Nat.card K ^ 2) * ((Nat.card K ^ 2) ^ 2 - 1) := by
    rw [CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup, hL]
  have hOcard := natCard_orthogonalGroup Q hdim hnd hminus
  have : Finite (W ≃ₗ[K] W) := by
    have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
    have : Finite W := Module.finite_of_finite K
    exact Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W)) DFunLike.coe_injective
  have hidx := Subgroup.card_mul_index (P.subgroupOf O)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardP, hSL, hOcard] at hidx
  have hpos : 0 < (Nat.card K ^ 2) * ((Nat.card K ^ 2) ^ 2 - 1) := by
    rw [← hSL]
    exact Nat.card_pos
  have hidx2 : (P.subgroupOf O).index = 2 := by
    have := Nat.eq_of_mul_eq_mul_left hpos (hidx.trans (mul_comm _ _))
    exact this
  have hcomm : ⁅O, O⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have key : ⁅(⟨a, ha⟩ : O), (⟨b, hb⟩ : O)⁆ ∈ P.subgroupOf O := by
      rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx2,
        Subgroup.mul_mem_iff_of_index_two hidx2, Subgroup.mul_mem_iff_of_index_two hidx2,
        inv_mem_iff, inv_mem_iff]
      tauto
    exact (Subgroup.mem_subgroupOf).1 key
  have hperf : P ≤ ⁅O, O⁆ := by
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    have hL4 : 4 ≤ Nat.card L := by rw [hL]; nlinarith
    have hperfK := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card L hL4
    rw [hP, MonoidHom.range_eq_map, ← hperfK.commutator_eq_top, commutator_def,
      Subgroup.map_commutator]
    have hmap : Subgroup.map ρ ⊤ ≤ O := by
      rw [← MonoidHom.range_eq_map]
      exact hle
    exact Subgroup.commutator_mono hmap hmap
  have hrange : P = ⁅O, O⁆ := le_antisymm hperf hcomm
  exact ⟨hrange, hrange ▸ hidx2⟩

theorem reflK_not_mem_commutator (Q : QuadraticForm K W) (hdim : finrank K W = 4)
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) {r : W} (hr : r ≠ 0) :
    reflK Q r ∉
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hQ := polarBilin_nondegenerate Q hnd
  have hle : ⁅O, O⁆ ≤ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hker : ⁅(⟨a, ha⟩ : O), (⟨b, hb⟩ : O)⁆ ∈
        (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Commute.all _ _
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  intro hmem
  have h := (hle hmem).2
  have hc : CFSG.RankThree.OrthogonalInvolutions.commSpace (reflK Q r) = Submodule.span K {r} :=
    commSpace_reflK Q hnd hr
  rw [hc, finrank_span_singleton hr] at h
  exact Nat.not_even_one h

theorem reflK_mul_mem_commutator (Q : QuadraticForm K W) (hdim : finrank K W = 4)
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hidx : ((⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2)
    {r s : W} (hr : Q r = 1) (hs : Q s = 1) :
    reflK Q r * reflK Q s ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hr0 : r ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hr; exact zero_ne_one hr
  have hs0 : s ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hs; exact zero_ne_one hs
  have hrO : reflK Q r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (reflK_isometry Q hr)
  have hsO : reflK Q s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (reflK_isometry Q hs)
  have key : (⟨reflK Q r, hrO⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) * ⟨reflK Q s, hsO⟩ ∈
      (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    exact iff_of_false (reflK_not_mem_commutator Q hdim hnd hr0)
      (reflK_not_mem_commutator Q hdim hnd hs0)
  exact (Subgroup.mem_subgroupOf).1 key

end CFSG.Quasithin.SimsG4.OrthMinus
