module

public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate3143
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGNsq2U62Lift
import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Cover
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotActs
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LieType.Multipliers.U62Sylow

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

theorem lieModel_of_u62_cover {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (π : X →* Y) (ψ₀ : Su K 2 1 6 →* Y) (hX : Group.IsPerfect X) (hπ : Function.Surjective π)
    (hπZ : ∀ x ∈ π.ker, ∀ x' : X, x' * x = x * x') (hψ : Function.Surjective ψ₀)
    (hψZ : ψ₀.ker ≤ Subgroup.center (Su K 2 1 6)) :
    CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 6 2 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerπ : π.ker ≤ Subgroup.center X := fun x hx => Subgroup.mem_center_iff.2 (hπZ x hx)
  have hperfSU : Group.IsPerfect (Su K 2 1 6) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK)
      (by norm_num) (fun h3 => absurd h3 (by omega))
  let eπ : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        CFSG.LocalCores.comap_center_eq_of_perfect hX π hπ hkerπ])).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (φ := (QuotientGroup.mk' (Subgroup.center Y)).comp π)
        ((QuotientGroup.mk'_surjective _).comp hπ))
  let eψ : Su K 2 1 6 ⧸ Subgroup.center (Su K 2 1 6) ≃* Y ⧸ Subgroup.center Y :=
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
        CFSG.LocalCores.comap_center_eq_of_perfect hperfSU ψ₀ hψ hψZ])).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (φ := (QuotientGroup.mk' (Subgroup.center Y)).comp ψ₀)
        ((QuotientGroup.mk'_surjective _).comp hψ))
  let eXS : X ⧸ Subgroup.center X ≃* Su K 2 1 6 ⧸ Subgroup.center (Su K 2 1 6) :=
    eπ.trans eψ.symm
  have hZ : Subgroup.center ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) =
      (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := by
    change Subgroup.center ↥(CFSG.Open.StatedSU 6 (2 ^ 1) K) =
      (CFSG.Open.StatedScalars (Fin 6) K).subgroupOf (CFSG.Open.StatedSU 6 (2 ^ 1) K)
    exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := 1)
      (F := K) (n := 6) hK (by norm_num) (by simp)).2
  let eSC : Su K 2 1 6 ⧸ Subgroup.center (Su K 2 1 6) ≃*
      ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    QuotientGroup.congr (Subgroup.center (Su K 2 1 6))
      (Subgroup.center ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (MulEquiv.subgroupCongr (su_eq_largeEven hK)) (Subgroup.map_center_eq _)
  let e3 : Su K 2 1 6 ⧸ Subgroup.center (Su K 2 1 6) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    eSC.trans (QuotientGroup.quotientMulEquivOfEq hZ)
  have hmodel : CFSG.Blueprint.LieModel
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) .PSU 6 2 1 :=
    Or.inl ⟨by decide, statedClassicalModel_unitary 6 1 hK
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩⟩
  exact CFSG.Blueprint.LieModel.of_mulEquiv eXS.symm
    (CFSG.Blueprint.LieModel.of_mulEquiv e3.symm hmodel)

theorem fixed_eq_one_of_pow_three {X : Type} [Group X] (α : MulAut X) (hα3 : α ^ 3 = 1)
    {T : Subgroup X} (hT : Nat.card T = 4) (hαT : ∀ t ∈ T, α t ∈ T) (hmv : ∃ t ∈ T, α t ≠ t) :
    ∀ t ∈ T, α t = t → t = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have : Fintype T := Fintype.ofFinite T
  let f : Function.End T := fun t => ⟨α t, hαT t t.2⟩
  have hα3' : ∀ x : X, α (α (α x)) = x := fun x => by
    have h := congrArg (fun β : MulAut X => β x) hα3
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.one_apply] at h
    exact h
  have hf3 : f ^ 3 ^ 1 = 1 := by
    have h3 : f ^ 3 ^ 1 = f * f * f := by
      rw [pow_one, pow_succ, pow_succ, pow_one]
    rw [h3]
    funext t
    apply Subtype.ext
    exact hα3' (t : X)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf3
  have hT4 : Fintype.card T = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hT
  have hlt : Fintype.card (Function.fixedPoints f) < 4 := by
    have hns : ¬ Function.Surjective (fun x : Function.fixedPoints f => (x : T)) := by
      rintro hsurj
      obtain ⟨t, htT, hαt⟩ := hmv
      obtain ⟨x, hx⟩ := hsurj ⟨t, htT⟩
      have hx' : (x : T) = ⟨t, htT⟩ := hx
      have h2 : α ((x : T) : X) = ((x : T) : X) := congrArg Subtype.val x.2
      rw [hx'] at h2
      exact hαt (by simpa [f] using h2)
    have := Fintype.card_lt_of_injective_not_surjective
      (fun x : Function.fixedPoints f => (x : T)) Subtype.val_injective hns
    rwa [hT4] at this
  have hcard1 : Fintype.card (Function.fixedPoints f) = 1 := by
    set k := Fintype.card (Function.fixedPoints f) with hk
    have hkmod : k % 3 = 1 := by
      rw [hk]
      have h := hmod
      rw [hT4] at h
      exact h.symm
    have hklt : k < 4 := by rw [hk]; exact hlt
    interval_cases k
    · norm_num at hkmod
    · rfl
    · norm_num at hkmod
    · norm_num at hkmod
  have hsub : Subsingleton (Function.fixedPoints f) :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [hcard1])
  intro t htT hαt
  have hmem : (⟨t, htT⟩ : T) ∈ Function.fixedPoints f := by
    show f ⟨t, htT⟩ = ⟨t, htT⟩
    exact Subtype.ext (by simpa [f] using hαt)
  have h1 : (⟨1, T.one_mem⟩ : T) ∈ Function.fixedPoints f := by
    show f ⟨1, T.one_mem⟩ = ⟨1, T.one_mem⟩
    exact Subtype.ext (by simp [f])
  have hEq : (⟨t, htT⟩ : T) = ⟨1, T.one_mem⟩ :=
    congrArg (fun u : Function.fixedPoints f => (u : T))
      (Subsingleton.elim (⟨⟨t, htT⟩, hmem⟩ : Function.fixedPoints f)
        ⟨⟨1, T.one_mem⟩, h1⟩)
  exact congrArg Subtype.val hEq

theorem ggU62OuterDiagInput_holds :
    GGU62OuterDiagInput := by
  intro K _ _ _ hK X Y _ _ _ _ π ψ₀ σ τ g hX hπ hπZ hπ2 hψ hψZ hστ hg hdet hτ x hx hσx
  by_cases hx1 : x = 1
  · exact hx1
  have hxZ : x ∈ Subgroup.center X := Subgroup.mem_center_iff.2 (hπZ x hx)
  have hev : ¬ Odd (Nat.card (Subgroup.center X)) := by
    rw [Nat.not_odd_iff_even, even_iff_two_dvd]
    obtain ⟨k, hk⟩ := hπ2 x hx
    obtain ⟨j, -, hxj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one hk)
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero] at hxj
        exact absurd (orderOf_eq_one_iff.mp hxj) hx1
      · exact hpos
    have h2dvd : 2 ∣ orderOf x := by
      rw [hxj]
      simpa only [pow_one] using pow_dvd_pow 2 hj1
    have h2dvd' : 2 ∣ Nat.card (Subgroup.zpowers x) := by
      rwa [Nat.card_zpowers]
    have hle : Subgroup.zpowers x ≤ Subgroup.center X := by
      rw [Subgroup.zpowers_le]
      exact hxZ
    exact h2dvd'.trans (Subgroup.card_dvd_of_le hle)
  have hQ : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 6 2 1 :=
    lieModel_of_u62_cover hK π ψ₀ hX hπ hπZ hψ hψZ
  obtain ⟨α, hα3, hout, hασ⟩ :=
    exists_outer_order_three_of_u62 hK π ψ₀ σ τ g hX hπ hπZ hψ hψZ hστ hg hdet hτ
  have hnot : ¬ (∀ z ∈ Subgroup.center X,
      (∃ k : ℕ, z ^ 2 ^ k = 1) → α z = z) := by
    intro hfix
    exact hout ((CFSG.GGQ2Prime.fix_two_iff_inner hev hQ α hα3).1 hfix)
  push Not at hnot
  obtain ⟨z, hzZ, hz2, hzα⟩ := hnot
  let T : Subgroup X := twoCentral (⊤ : Subgroup X)
  have hKle : T ≤ Subgroup.center X := fun z hz =>
    Subgroup.mem_center_iff.2 fun l => twoCentral_central hz l (Subgroup.mem_top l)
  have hK2 : IsPGroup 2 T := by
    intro t
    obtain ⟨k, hk⟩ := twoCentral_two t.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hKall : ∀ z ∈ Subgroup.center X, (∃ k : ℕ, z ^ 2 ^ k = 1) → z ∈ T := by
    intro z hz hz2
    exact ⟨Subgroup.mem_top z, fun l _ => Subgroup.mem_center_iff.1 hz l, hz2⟩
  have hTcard : Nat.card T = 4 :=
    CFSG.GGQ2Prime.card_two_part_eq_four hev hQ α hα3 hout T hKle hK2 hKall
  have hαT : ∀ t ∈ T, α t ∈ T := by
    intro t ht
    obtain ⟨-, hc, k, hk⟩ := ht
    refine ⟨Subgroup.mem_top _, fun l _ => ?_, k, ?_⟩
    · obtain ⟨l', rfl⟩ := α.surjective l
      rw [← map_mul, ← map_mul, hc l' (Subgroup.mem_top l')]
    · rw [← map_pow, hk, map_one]
  have hmv : ∃ t ∈ T, α t ≠ t := ⟨z, hKall z hzZ hz2, hzα⟩
  refine fixed_eq_one_of_pow_three α hα3 hTcard hαT hmv x ?_ ?_
  · exact hKall x hxZ (hπ2 x hx)
  · exact (hασ x hxZ).trans hσx

end CFSG.StandardType

end
