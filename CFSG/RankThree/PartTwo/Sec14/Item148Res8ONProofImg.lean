module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Res8ON

theorem isTripleCover_congr148 {X X' Y : Type*} [Group X] [Group X'] [Group Y] (e : X ≃* X')
    (h : Sec4.IsTripleCover X Y) : Sec4.IsTripleCover X' Y := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).symm.trans φ⟩⟩
  rw [← hc, Subgroup.card_map_of_injective e.injective, hcard]

theorem commute_of_card_eq_three {Γ : Type*} [Group Γ] {Z : Subgroup Γ} (hZ : Nat.card Z = 3)
    {g : Γ} (hg : ∀ x ∈ Z, g * x * g⁻¹ ∈ Z) (hg3 : g ^ 3 = 1) {z : Γ} (hz : z ∈ Z) :
    g * z = z * g := by
  have : Finite ↥Z := Nat.finite_of_card_ne_zero (by omega)
  have hz3 : z ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzp : Subgroup.zpowers z = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
    rw [hZ, Nat.card_zpowers, hoz]
  have hw : g * z * g⁻¹ ∈ Subgroup.zpowers z := hzp ▸ hg z hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hmod := zpow_mod_orderOf z k
  rw [hoz, Nat.cast_ofNat, hk] at hmod
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero] at hmod
    exact absurd (conj_eq_one_iff.mp hmod.symm) hz1
  · rw [h1, zpow_one] at hmod
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [← hmod]
  · exfalso
    rw [h2, zpow_two] at hmod
    have e1 : g * z * g⁻¹ = z ^ 2 := by rw [← hmod, pow_two]
    have e2 : g * z ^ 2 * g⁻¹ = z := by
      rw [← conj_pow, e1, ← pow_mul,
        show z ^ (2 * 2) = z ^ 3 * z by rw [← pow_succ], hz3, one_mul]
    have hg3' : g * (g * g) = 1 := by rw [← pow_three]; exact hg3
    have e3 : z = z ^ 2 := by
      calc z = g * (g * g) * z * (g * (g * g))⁻¹ := by rw [hg3', one_mul, inv_one, mul_one]
        _ = g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ := by group
        _ = z ^ 2 := by rw [e1, e2, e1]
    apply hz1
    calc z = z * z * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [← pow_two, ← e3]
      _ = 1 := mul_inv_cancel z

theorem three_dvd_card_of_isTripleCover {X Y : Type*} [Group X] [Group Y]
    (h : Sec4.IsTripleCover X Y) : 3 ∣ Nat.card X := by
  have h1 := Subgroup.card_subgroup_dvd_card (Subgroup.center X)
  rwa [h.1] at h1

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem ker_phi148_le_theta {K : Subgroup G} (hKM : K ≤ Y ⊔ A)
    (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (h3 : 3 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K)) :
    (Main148.phi148 (A := A) (Y := Y) hKM).ker ≤ aschbacherSolvableCore 3 ↥K := by
  set φ := Main148.phi148 (A := A) (Y := Y) hKM with hφ
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  set T := φ.ker.map (QuotientGroup.mk' θK) with hT
  have hTn : T.Normal := (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective _)
  have hT3 : ¬ 3 ∣ Nat.card ↥T := fun h3' =>
    Main148.not_three_dvd_card_ker_phi148 hKM (h3'.trans (Subgroup.card_map_dvd _ _))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hTn with htop | hcen
  · exfalso
    apply hT3
    rw [htop, Subgroup.card_top]
    exact h3
  · have hTs : Group.IsSolvable ↥T := by
      refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
      exact (Subgroup.mem_center_iff.mp (hcen b.2) a)
    have hle := (solvable_prime_complement_core_characterization (H := ↥K ⧸ θK)
      Nat.prime_three).2.2.2.1 T hTn hTs hT3
    rw [(theta_quotient_core_and_ranks (G := ↥K)).1, le_bot_iff, hT, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hle
    exact hle

theorem nonempty_img148_equiv_theta_of_quasisimple {K : Subgroup G} (hKM : K ≤ Y ⊔ A)
    (hθ : inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y)
    (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (h3 : 3 ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K)) :
    Nonempty (↥(img148 A Y K) ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  set φ := Main148.phi148 (A := A) (Y := Y) hKM with hφ
  have hker : φ.ker = aschbacherSolvableCore 3 ↥K := by
    refine le_antisymm (ker_phi148_le_theta hKM hKq h3) fun k hk => ?_
    rw [MonoidHom.mem_ker, hφ, Main148.phi148_eq_one_iff]
    exact hθ ⟨k, hk, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans
      (MulEquiv.subgroupCongr (Main148.range_phi148 hKM)))).symm⟩

theorem isTripleCover_img148_of_theta {K : Subgroup G} (hKM : K ≤ Y ⊔ A)
    (hθ : inSubgroup (aschbacherSolvableCore 3) K ≤ pPrimeCoreOf 3 Y)
    (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K)) {X : Type*} [Group X]
    (htc : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) X) :
    Sec4.IsTripleCover ↥(img148 A Y K) X := by
  obtain ⟨ψ⟩ := nonempty_img148_equiv_theta_of_quasisimple hKM hθ hKq
    (three_dvd_card_of_isTripleCover htc)
  exact isTripleCover_congr148 ψ.symm htc

end Quot

end Res8ON

end CFSG.RankThree.PartTwo.Sec14
