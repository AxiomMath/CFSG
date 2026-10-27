module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Shape
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312KG
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt OInf)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor
  lieSylowExponent)

variable {G : Type} [Group G] [Finite G]

private theorem w183K3ShapeSN_nonab_of_simple_not_prime {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hn : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hnab
  have hcomm : IsMulCommutative X := IsMulCommutative.of_comm (fun a b => by
    by_contra hab
    exact hnab ⟨a, b, hab⟩)
  letI : IsMulCommutative X := hcomm
  exact hn (CommGroup.is_simple_iff_prime_card.mp hs)

private theorem w183K3ShapeSN_card_alt6 {X : Type} [Group X] (h : IsAlt X 6) :
    Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem w183K3ShapeSN_card_psl_2_2_2 {X : Type} [Group X] (h : IsL2 X 2) :
    Nat.card X = 60 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem w183K3ShapeSN_card_psu_3_2_2 {X : Type} [Group X] (h : IsU3 X 2) :
    Nat.card X = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem w183K3ShapeSN_card_PSL_3_2_1 {X : Type} [Group X] (h : IsL3 X 1) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem w183K3ShapeSN_card_PSL_3_2_2 {X : Type} [Group X] (h : IsL3 X 2) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem w183K3ShapeSN_card_PSp_2_2_2 {X : Type} [Group X] (hO : LieOrderFormulasInput)
    (h : IsSp4 X 2) : Nat.card X = 979200 := by
  obtain ⟨-, hM, -⟩ := hO X .PSp 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]

private lemma w183K3ShapeSN_three_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    3 ∣ p ^ 2 - 1 ∨ p = 3 := by
  by_cases h3 : p = 3
  · exact Or.inr h3
  · refine Or.inl ?_
    have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
      have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
      have hne0 : p % 3 ≠ 0 := by
        intro h0
        have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        exact h3 ((hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp hdvd)
      omega
    have hcong : p ^ 2 ≡ 1 [MOD 3] := by
      rcases hmod with h1 | h2
      · have hp1 : p ≡ 1 [MOD 3] := by
          rw [Nat.ModEq]
          simp [h1]
        simpa using Nat.ModEq.pow 2 hp1
      · have hp2 : p ≡ 2 [MOD 3] := by
          rw [Nat.ModEq]
          simp [h2]
        exact (Nat.ModEq.pow 2 hp2).trans (by decide : (4 : ℕ) ≡ 1 [MOD 3])
    exact (Nat.modEq_iff_dvd' (show 1 ≤ p ^ 2 by nlinarith [hp.two_le])).mp hcong.symm

private lemma w183K3ShapeSN_three_dvd_PSp_num {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    3 ∣ lieOrderNumerator .PSp 2 (p ^ 1) := by
  rcases w183K3ShapeSN_three_dvd_sq_sub_one hp hne with h3 | rfl
  · have hprod : 3 ∣ ((p ^ 1) ^ (2 * 1) - 1) * ((p ^ 1) ^ (2 * 2) - 1) := by
      have h : 3 ∣ (p ^ 1) ^ (2 * 1) - 1 := by simpa [pow_one] using h3
      exact dvd_mul_of_dvd_left h _
    rw [show lieOrderNumerator .PSp 2 (p ^ 1) =
        (p ^ 1) ^ (2 ^ 2) * (((p ^ 1) ^ (2 * 1) - 1) * ((p ^ 1) ^ (2 * 2) - 1)) by
      simp [lieOrderNumerator, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
        Finset.prod_pair]]
    exact dvd_mul_of_dvd_right hprod _
  · norm_num [lieOrderNumerator, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
      Finset.prod_pair]

private lemma w183K3ShapeSN_not_prime_of_PSp {X : Type} [Group X] (hO : LieOrderFormulasInput)
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) (h : LieModel X .PSp 2 p 1) :
    ¬ (Nat.card X).Prime := by
  obtain ⟨-, -, hfact⟩ := hO X .PSp 2 p 1 h.admissible h
  have hfac : (Nat.card X).factorization p = 4 := by
    simpa [lieSylowExponent] using hfact
  intro hpr
  have hne0 : (Nat.card X).factorization p ≠ 0 := by rw [hfac]; norm_num
  have heq : Nat.card X = p := Nat.Prime.eq_of_factorization_pos hpr hne0
  have h1 : (Nat.card X).factorization p = 1 := by
    rw [← heq]
    exact hpr.factorization_self
  rw [hfac] at h1
  norm_num at h1

theorem kshape_simple_nonab (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : KShapeList X) : IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  unfold KShapeList at h
  rcases h with hL2 | hU3 | hAlt | hL31 | hL32 | hSp4 | ⟨p, e', hp, hne, hgt, hF⟩ |
    ⟨p, hp, hne, hInner⟩ | ⟨p, hp, hne, hSp⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    exact ⟨hs, w183K3ShapeSN_nonab_of_simple_not_prime hs
      (by rw [w183K3ShapeSN_card_psl_2_2_2 hL2]; norm_num)⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
    exact ⟨hs, w183K3ShapeSN_nonab_of_simple_not_prime hs
      (by rw [w183K3ShapeSN_card_psu_3_2_2 hU3]; norm_num)⟩
  · obtain ⟨e⟩ := hAlt
    have hs : IsSimpleGroup X :=
      (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
    exact ⟨hs, w183K3ShapeSN_nonab_of_simple_not_prime hs
      (by rw [w183K3ShapeSN_card_alt6 ⟨e⟩]; norm_num)⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL31
    exact ⟨hs, w183K3ShapeSN_nonab_of_simple_not_prime hs
      (by rw [w183K3ShapeSN_card_PSL_3_2_1 hL31]; norm_num)⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL32
    exact ⟨hs, w183K3ShapeSN_nonab_of_simple_not_prime hs
      (by rw [w183K3ShapeSN_card_PSL_3_2_2 hL32]; norm_num)⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp4
    exact ⟨hs, w183K3ShapeSN_nonab_of_simple_not_prime hs
      (by rw [w183K3ShapeSN_card_PSp_2_2_2 hO hSp4]; norm_num)⟩
  · exact ⟨CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSL hF,
      CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSL hF⟩
  · rcases hInner with ⟨h4, hL3⟩ | ⟨h4, hU3p⟩
    · exact ⟨CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSL
          (hL3.statedClassicalModel (by decide)),
        CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSL
          (hL3.statedClassicalModel (by decide))⟩
    · exact ⟨CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSU
          (hU3p.statedClassicalModel (by decide)),
        CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSU
          (hU3p.statedClassicalModel (by decide))⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
    exact ⟨hs, w183K3ShapeSN_nonab_of_simple_not_prime hs
      (w183K3ShapeSN_not_prime_of_PSp hO hp hne hSp)⟩

theorem kshape_three_dvd (hO : LieOrderFormulasInput) {K L : Subgroup G}
    (h : HasQuotShape L (K : Set G) (fun X _ => KShapeList X)) : 3 ∣ K.relIndex L := by
  obtain ⟨X, hXg, φ, hs, hk, hP⟩ := h
  have hker : φ.ker = K.subgroupOf L := by
    ext k
    rw [MonoidHom.mem_ker, hk k, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hs,
    Subgroup.card_top]
  unfold KShapeList at hP
  rcases hP with hL2 | hU3 | hAlt | hL31 | hL32 | hSp4 | ⟨p, e', hp, hne, hgt, hF⟩ |
    ⟨p, hp, hne, hInner⟩ | ⟨p, hp, hne, hSp⟩
  · rw [w183K3ShapeSN_card_psl_2_2_2 hL2]
    norm_num
  · rw [w183K3ShapeSN_card_psu_3_2_2 hU3]
    norm_num
  · rw [w183K3ShapeSN_card_alt6 hAlt]
    norm_num
  · rw [w183K3ShapeSN_card_PSL_3_2_1 hL31]
    norm_num
  · rw [w183K3ShapeSN_card_PSL_3_2_2 hL32]
    norm_num
  · rw [w183K3ShapeSN_card_PSp_2_2_2 hO hSp4]
    norm_num
  · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_two hF
  · rcases hInner with ⟨h4, hL3⟩ | ⟨h4, hU3p⟩
    · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_three
        (hL3.statedClassicalModel (by decide))
    · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSU_three
        (hU3p.statedClassicalModel (by decide))
  · obtain ⟨-, hmul, -⟩ := hO X .PSp 2 p 1 hSp.admissible hSp
    have hgcd : lieOrderDivisor .PSp 2 (p ^ 1) = 2 := by
      simp only [lieOrderDivisor, pow_one]
      exact Nat.gcd_eq_left (by
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two hne
        exact ⟨k, by omega⟩)
    have hnum : 3 ∣ lieOrderNumerator .PSp 2 (p ^ 1) :=
      w183K3ShapeSN_three_dvd_PSp_num hp hne
    have hdvd : 3 ∣ Nat.card X * lieOrderDivisor .PSp 2 (p ^ 1) := by
      rw [hmul]
      exact hnum
    have hcop : Nat.Coprime 3 (lieOrderDivisor .PSp 2 (p ^ 1)) := by
      rw [hgcd]
      decide
    exact (Nat.Coprime.dvd_mul_right hcop).mp hdvd

theorem hasQuotShape_kshape_of_shape54 {H T L : Subgroup G} (hsh : Shape54 H T L) :
    HasQuotShape L (OInf H : Set G) (fun X _ => KShapeList X) := by
  unfold Shape54 at hsh
  rcases hsh with h12 | hAlt31 | ⟨hL32sp4, ht⟩ | ⟨p, e', hp, hne, hgt, hQ⟩ |
    ⟨p, hp, hne, hInner⟩ | ⟨p, hp, hne, hSpQ⟩
  · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := h12
    refine ⟨X, hXg, φ, hs, hk, ?_⟩
    unfold KShapeList
    rcases hP with h2 | h3
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
  · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hAlt31
    refine ⟨X, hXg, φ, hs, hk, ?_⟩
    unfold KShapeList
    rcases hP with hAlt | hL31
    · exact Or.inr (Or.inr (Or.inl hAlt))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hL31)))
  · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hL32sp4
    refine ⟨X, hXg, φ, hs, hk, ?_⟩
    unfold KShapeList
    rcases hP with hL32 | hSp4
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL32))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSp4)))))
  · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hQ
    refine ⟨X, hXg, φ, hs, hk, ?_⟩
    unfold KShapeList
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨p, e', hp, hne, hgt, hP⟩))))))
  · rcases hInner with ⟨h4, hQ3⟩ | ⟨h4, hUp⟩
    · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hQ3
      refine ⟨X, hXg, φ, hs, hk, ?_⟩
      unfold KShapeList
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p, hp, hne, Or.inl ⟨h4, hP⟩⟩)))))))
    · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hUp
      refine ⟨X, hXg, φ, hs, hk, ?_⟩
      unfold KShapeList
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p, hp, hne, Or.inr ⟨h4, hP⟩⟩)))))))
  · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hSpQ
    refine ⟨X, hXg, φ, hs, hk, ?_⟩
    unfold KShapeList
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨p, hp, hne, hP⟩)))))))

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
