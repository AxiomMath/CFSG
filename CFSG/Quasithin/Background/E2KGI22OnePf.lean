module

public import CFSG.Quasithin.Background.E2TenKG3
public import CFSG.Alternating.Multipliers.Small
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.Quasithin.E2

open CFSG.RankThree.PerfectCover
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open scoped MatrixGroups

theorem nonempty_mulEquiv_of_isCyclic_hopfMultiplier {X E₁ E₂ : Type} [Group X] [Group E₁]
    [Group E₂] [Finite X] [Finite E₁] [Finite E₂] [Group.IsPerfect X] [Group.IsPerfect E₁]
    [Group.IsPerfect E₂] (hM : IsCyclic (hopfMultiplier X)) {q₁ : E₁ →* X}
    (hq₁ : Function.Surjective q₁) (hk₁ : q₁.ker ≤ Subgroup.center E₁) {q₂ : E₂ →* X}
    (hq₂ : Function.Surjective q₂) (hk₂ : q₂.ker ≤ Subgroup.center E₂)
    (hc : Nat.card E₁ = Nat.card E₂) : Nonempty (E₁ ≃* E₂) := by
  have : Finite (HopfCover X) := finite_hopfCover inferInstance
  set h₁ := hopfLift q₁ hq₁ hk₁ with hh₁
  set h₂ := hopfLift q₂ hq₂ hk₂ with hh₂
  have hs₁ : Function.Surjective h₁ := hopfLift_surjective q₁ hq₁ hk₁
  have hs₂ : Function.Surjective h₂ := hopfLift_surjective q₂ hq₂ hk₂
  have hle₁ : h₁.ker ≤ hopfMultiplier X := fun u hu => by
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [← comp_hopfLift q₁ hq₁ hk₁, MonoidHom.comp_apply, ← hh₁, hu, map_one]
  have hle₂ : h₂.ker ≤ hopfMultiplier X := fun u hu => by
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [← comp_hopfLift q₂ hq₂ hk₂, MonoidHom.comp_apply, ← hh₂, hu, map_one]
  have hc₁ := card_eq_card_mul_card_ker h₁ hs₁
  have hc₂ := card_eq_card_mul_card_ker h₂ hs₂
  have hpos : 0 < Nat.card E₂ := Nat.card_pos
  have hck : Nat.card h₁.ker = Nat.card h₂.ker := by
    rw [hc] at hc₁
    exact Nat.eq_of_mul_eq_mul_left hpos (hc₁.symm.trans hc₂)
  have hsub : h₁.ker.subgroupOf (hopfMultiplier X) = h₂.ker.subgroupOf (hopfMultiplier X) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv, hck]
  have hker : h₁.ker = h₂.ker := by
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hle₁, inf_eq_left.mpr hle₂] at hsub
    exact hsub
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective h₁ hs₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective h₂ hs₂))⟩

theorem card_center_eq_two_of_multiplier {K X : Type} [Group K] [Group X] [Finite K]
    (hq : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) (e : K ⧸ Subgroup.center K ≃* X)
    (hm : Nat.card (hopfMultiplier X) ∣ 6) : Nat.card (Subgroup.center K) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect K := hq.1
  have hker : (centralQuotientMap e).ker ≤ Subgroup.center K := (centralQuotientMap_ker e).le
  have hmap := map_hopfMultiplier_hopfLift (centralQuotientMap e)
    (centralQuotientMap_surjective e) hker
  rw [centralQuotientMap_ker] at hmap
  have hdvd : Nat.card (Subgroup.center K) ∣ 6 := by
    rw [← hmap]
    exact (Subgroup.card_map_dvd _ _).trans hm
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have h1 : Nat.card (Subgroup.center K) ≠ 1 := fun h => hZ (Subgroup.card_eq_one.mp h)
  rw [hk] at hdvd h1 ⊢
  rcases k with _ | _ | k
  · exact absurd (pow_zero 2) h1
  · rfl
  · exfalso
    have h4 : 4 ∣ 2 ^ (k + 2) := by
      rw [pow_add]
      exact Dvd.intro_left _ rfl
    have := h4.trans hdvd
    omega

theorem card_center_specialLinearGroup_two {k : Type} [Field k] [Fintype k]
    (hk : Odd (Fintype.card k)) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) = 2 := by
  have hroots : rootsOfUnity (max (Fintype.card (Fin 2)) 1) k = rootsOfUnity 2 k := by simp
  let e : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) ≃* rootsOfUnity 2 k :=
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).trans (MulEquiv.subgroupCongr hroots)
  rw [Nat.card_congr e.toEquiv, LieType.Steinberg.CentralExt.SL2Closed.card_rootsOfUnity_two]
  have : Even (Fintype.card k - 1) := by
    obtain ⟨j, hj⟩ := hk
    rw [hj]
    exact ⟨j, by omega⟩
  exact Nat.gcd_eq_left (even_iff_two_dvd.mp this)

theorem nonempty_mulEquiv_sl_two {K X k : Type} [Group K] [Group X] [Finite K] [Finite X]
    [Field k] [Fintype k] (hq : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) (e : K ⧸ Subgroup.center K ≃* X)
    (hM : IsCyclic (hopfMultiplier X)) (hm : Nat.card (hopfMultiplier X) ∣ 6)
    (hk5 : 5 ≤ Fintype.card k) (hkodd : Odd (Fintype.card k))
    (f : Matrix.ProjectiveSpecialLinearGroup (Fin 2) k ≃* X) :
    Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) k) := by
  have : Group.IsPerfect K := hq.1
  have : Group.IsPerfect X := isPerfect_of_quasisimple_quotient hq e
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k) :=
    LinearGroups.special_linear_dimension_two_perfect
      (LieType.Steinberg.CentralExt.SL2Closed.exists_four_of_five_le
        (by rwa [← Fintype.card_eq_nat_card]))
  have hcK := card_eq_card_mul_card_ker (centralQuotientMap e) (centralQuotientMap_surjective e)
  have hcS := card_eq_card_mul_card_ker (centralQuotientMap f) (centralQuotientMap_surjective f)
  rw [centralQuotientMap_ker, card_center_eq_two_of_multiplier hq hZ hZ2 e hm] at hcK
  rw [centralQuotientMap_ker, card_center_specialLinearGroup_two hkodd] at hcS
  exact nonempty_mulEquiv_of_isCyclic_hopfMultiplier hM (centralQuotientMap_surjective e)
    (centralQuotientMap_ker e).le (centralQuotientMap_surjective f) (centralQuotientMap_ker f).le
    (hcK.trans hcS.symm)

theorem kgI22One_holds :
    KGI22One := by
  intro K _ _ hq hZ hZ2
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨hM, hc⟩ := Alternating.Multipliers.hopfMultiplier_alternatingGroup_five
    obtain ⟨f⟩ := SectionRank.Ccomm.projective_five_alternating
    exact nonempty_mulEquiv_sl_two hq hZ hZ2 e hM (by rw [hc]; norm_num)
      (by rw [ZMod.card]) (by rw [ZMod.card]; decide) f
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 3 2) = 9 := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
      norm_num
    obtain ⟨hM, hc⟩ := Alternating.Multipliers.hopfMultiplier_alternatingGroup_six
    obtain ⟨f⟩ :=
      unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
    exact nonempty_mulEquiv_sl_two hq hZ hZ2 e hM (by rw [hc]) (by rw [hcard]; norm_num)
      (by rw [hcard]; decide) f

end CFSG.Quasithin.E2
