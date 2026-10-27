module

public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneQuotient
import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartOne.S8

open CFSG CFSG.RankThree.LocalRank

theorem fittingSubgroup_le_pCore_of_theta_eq_bot {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hθ : aschbacherSolvableCore p Q = ⊥) : fittingSubgroup Q ≤ pCore p Q := by
  rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  by_cases hq : (q : ℕ) = p
  · rw [hq]
  · exact ((solvable_prime_complement_core_characterization hp).2.2.2.2.2.2 q
      (Nat.prime_of_mem_primeFactors q.2) hq).trans (hθ ▸ bot_le)

theorem fittingSubgroup_eq_pCore_of_theta_eq_bot {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hθ : aschbacherSolvableCore p Q = ⊥) : fittingSubgroup Q = pCore p Q := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (fittingSubgroup_le_pCore_of_theta_eq_bot hp hθ) ?_
  exact LocalCores.fitting_characteristic.2.2 _ pCore_normal pCore_isPGroup.isNilpotent

theorem isPGroup_center_layer_of_theta_eq_bot {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hθ : aschbacherSolvableCore p Q = ⊥) :
    IsPGroup p (Subgroup.center (layer Q)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : (layer Q).Characteristic := LocalCores.layer_characteristic
  set Z : Subgroup Q := layer Q ⊓ Subgroup.centralizer (layer Q : Set Q) with hZ
  have hZn : Z.Normal := by rw [hZ]; infer_instance
  have hZc : IsMulCommutative Z := Subgroup.le_centralizer_iff_isMulCommutative.mp
    fun y hy h hh => Subgroup.mem_centralizer_iff.mp hy.2 h hh.1
  have hZle : Z ≤ pCore p Q := by
    rw [← fittingSubgroup_eq_pCore_of_theta_eq_bot hp hθ]
    exact LocalCores.fitting_characteristic.2.2 Z hZn inferInstance
  intro z
  have hz : ((z : layer Q) : Q) ∈ Z := Subgroup.mem_inf.mpr ⟨(z : layer Q).2,
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨h, hh⟩)⟩
  obtain ⟨k, hk⟩ := pCore_isPGroup ⟨((z : layer Q) : Q), hZle hz⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

theorem localCoreProduct_facts {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {E : Subgroup Q} (hE : IsElementaryAbelian p E) {t : Q} (ht : t ∈ E) (ht1 : t ≠ 1)
    (hθ : aschbacherSolvableCore p Q = ⊥) :
    Group.IsSolvable
        (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
          thetaT p E : Subgroup Q) ∧
      ¬ p ∣ Nat.card
        (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
          thetaT p E : Subgroup Q) ∧
      (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
          thetaT p E : Subgroup Q) ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)) ∧
      (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
          thetaT p E : Subgroup Q) ≤
        Subgroup.centralizer (fittingSubgroup Q : Set Q) ∧
      Nat.Coprime
        (Nat.card
          (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
            thetaT p E : Subgroup Q))
        (Nat.card (fittingSubgroup Q)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEab : IsMulCommutative E := hE.toIsMulCommutative
  have hFit := fittingSubgroup_eq_pCore_of_theta_eq_bot hp hθ
  have hcore := solvable_prime_complement_core_characterization
    (H := Subgroup.centralizer ({t} : Set Q)) hp
  set S := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)) with hS
  set D : Subgroup Q := ⁅S, E⁆ ⊔ thetaT p E
  have hSt : S ≤ Subgroup.centralizer ({t} : Set Q) := Subgroup.map_subtype_le _
  have hSp : ¬ p ∣ Nat.card S := by
    rw [hS, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hcore.2.2.1
  have hSsolv : Group.IsSolvable S := by
    have := hcore.1
    let e : aschbacherSolvableCore p ↥(Subgroup.centralizer ({t} : Set Q)) ≃* S :=
      Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hXS : ⁅S, E⁆ ≤ S := by
    rw [hS, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact CFSG.RankThreeEvenClassification.Helpers.thetaPlaneCommutator_le_element_theta
      p hp E hEab t ht
  have hTS : thetaT p E ≤ S := iInf_le_of_le t (iInf_le_of_le ht (iInf_le_of_le ht1 le_rfl))
  have hDS : D ≤ S := sup_le hXS hTS
  have hDsolv : Group.IsSolvable D := by
    have := hSsolv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hDS)
  have hDp : ¬ p ∣ Nat.card D := fun h => hSp (h.trans (Subgroup.card_dvd_of_le hDS))
  have hA : IsPGroup p (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,
        orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) t ht) ht1, pow_one])
  have hCent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup Q) : Set Q) =
      Subgroup.centralizer ({t} : Set Q) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hsub : S.subgroupOf (Subgroup.centralizer ({t} : Set Q)) =
      aschbacherSolvableCore p ↥(Subgroup.centralizer ({t} : Set Q)) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hSnormal : (S.subgroupOf (Subgroup.centralizer
      ((Subgroup.zpowers t : Subgroup Q) : Set Q))).Normal := by
    rw [hCent, hsub]
    infer_instance
  have hSF : ⁅S, pCore p Q⁆ = ⊥ :=
    local_prime_complement_centralizes_normal_prime_group hp pCore_isPGroup hA
      (hCent ▸ hSt) hSnormal hSp
  have hDF : D ≤ Subgroup.centralizer (fittingSubgroup Q : Set Q) := by
    rw [hFit]
    exact hDS.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSF)
  have hcop : Nat.Coprime (Nat.card D) (Nat.card (fittingSubgroup Q)) := by
    rw [hFit]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := p) (G := Q))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hDp).symm
  exact ⟨hDsolv, hDp, hDS, hDF, hcop⟩

end CFSG.RankThree.PartOne.S8
