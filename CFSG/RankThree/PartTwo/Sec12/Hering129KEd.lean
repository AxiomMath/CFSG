module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HLift
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.GroupTheory.CentralizerSup
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Hering129KEd

theorem subgroupOf_theta_le {H : Type*} [Group H] [Finite H] (X : Subgroup H) :
    (aschbacherSolvableCore 3 H).subgroupOf X ≤ aschbacherSolvableCore 3 X := by
  have hH := solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have hX := solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  haveI : Group.IsSolvable (aschbacherSolvableCore 3 H) := hH.1
  let ι : ↥((aschbacherSolvableCore 3 H).subgroupOf X) →* ↥(aschbacherSolvableCore 3 H) :=
    (X.subtype.comp ((aschbacherSolvableCore 3 H).subgroupOf X).subtype).codRestrict
      (aschbacherSolvableCore 3 H) fun x => Subgroup.mem_subgroupOf.mp x.2
  have hι : Function.Injective ι := fun x y hxy => by
    have h : ((ι x : ↥(aschbacherSolvableCore 3 H)) : H) =
        ((ι y : ↥(aschbacherSolvableCore 3 H)) : H) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hsolv : Group.IsSolvable ↥((aschbacherSolvableCore 3 H).subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective hι
  have hdvd : Nat.card ↥((aschbacherSolvableCore 3 H).subgroupOf X) ∣
      Nat.card ↥(aschbacherSolvableCore 3 H) :=
    Subgroup.card_dvd_of_injective ι hι
  have hnp : ¬ 3 ∣ Nat.card ↥((aschbacherSolvableCore 3 H).subgroupOf X) :=
    fun h => hH.2.2.1 (h.trans hdvd)
  exact hX.2.2.2.1 _ inferInstance hsolv hnp

theorem exists_surjective_hom_map {H : Type*} [Group H] [Finite H] (X : Subgroup H) {p n : ℕ}
    [Fact p.Prime] (e : X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n)) :
    ∃ φ : ↥(X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) →*
      projSL 2 (GaloisField p n), Function.Surjective φ := by
  let f : X →* ↥(X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 H)).subgroupMap X
  let g : X →* projSL 2 (GaloisField p n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 X))
  have hf : Function.Surjective f :=
    MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) X
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨z, hz⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 X) z
    exact ⟨x, hz⟩
  have hker : f.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 H) (x : H) = 1 :=
      congrArg Subtype.val hx
    have h2 : (x : H) ∈ aschbacherSolvableCore 3 H :=
      (QuotientGroup.eq_one_iff (x : H)).mp h1
    have h3 : x ∈ aschbacherSolvableCore 3 X :=
      subgroupOf_theta_le X (Subgroup.mem_subgroupOf.mpr h2)
    have h4 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr h3
    change e (QuotientGroup.mk' (aschbacherSolvableCore 3 X) x) = 1
    rw [h4, map_one]
  refine ⟨f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
    ⟨g, hker⟩, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hg y
  exact ⟨f x, (f.liftOfRightInverse_comp_apply (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨g, hker⟩ x).trans hx⟩

theorem isSubnormal_map_inf_centralizer {H : Type*} [Group H] [Finite H] {Y X : Subgroup H}
    {b : H} (hb3 : b ^ 3 = 1) (hT : aschbacherSolvableCore 3 H ≤ Y)
    (hXM : X ≤ Y ⊓ Subgroup.centralizer ({b} : Set H))
    (hX : (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set H))).IsSubnormal) :
    ((X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))).subgroupOf
      ((Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) ⊓
        Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 H) b} :
          Set (H ⧸ aschbacherSolvableCore 3 H)))).IsSubnormal := by
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 H) :=
    (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
  have hA : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hb3)
  have hC : (Subgroup.centralizer ({b} : Set H)).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) =
      Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 H) b} :
        Set (H ⧸ aschbacherSolvableCore 3 H)) := by
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3
      (aschbacherSolvableCore 3 H) hN3 (Subgroup.zpowers b) hA
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton, MonoidHom.map_zpowers,
      CFSG.centralizer_zpowers_eq_centralizer_singleton] at h
    exact h
  have hM : (Y ⊓ Subgroup.centralizer ({b} : Set H)).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) =
      (Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) ⊓
        Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 H) b} :
          Set (H ⧸ aschbacherSolvableCore 3 H)) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mp hm).1, ?_⟩
      rw [← hC]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mp hm).2
    · intro z hz
      obtain ⟨hzY, hzC⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hzY
      have hyC : QuotientGroup.mk' (aschbacherSolvableCore 3 H) y ∈
          (Subgroup.centralizer ({b} : Set H)).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) := by
        rw [hC]
        exact hzC
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hyC
      have hmem : m⁻¹ * y ∈ aschbacherSolvableCore 3 H := by
        have h := hmy
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
        exact h
      have h1 : y⁻¹ * m ∈ aschbacherSolvableCore 3 H := by
        simpa using (aschbacherSolvableCore 3 H).inv_mem hmem
      have hmY : m ∈ Y := by
        simpa using Y.mul_mem hy (hT h1)
      rw [← hmy]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr ⟨hmY, hm⟩)
  have hf : Function.Surjective ((QuotientGroup.mk' (aschbacherSolvableCore 3 H)).subgroupMap
      (Y ⊓ Subgroup.centralizer ({b} : Set H))) :=
    MonoidHom.subgroupMap_surjective _ _
  have hmap : (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set H))).map
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 H)).subgroupMap
        (Y ⊓ Subgroup.centralizer ({b} : Set H))) =
      (X.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))).subgroupOf
        ((Y ⊓ Subgroup.centralizer ({b} : Set H)).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hu))
    · intro hz
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hz)
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hXM hx⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext hxz⟩
  have key := hX.map hf
  rw [hmap] at key
  rw [← hM]
  exact key

end Hering129KEd

end CFSG.RankThree.PartTwo.Sec12
