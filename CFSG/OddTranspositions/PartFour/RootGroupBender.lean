module

public import CFSG.OddTranspositions.PartTwoSec6
import CFSG.CGT.T75A.RootAbs
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.Closure.Bender
import CFSG.LocalAnalysis.ComponentClassification.Asc76L26BenderAux

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.BenderSuzuki CFSG.Timmesfeld.Bridge.Asc72
open CFSG.ComponentClassification.AschbacherToolkit.Bender (map_center_eq_sylowCenter
  mem_sylowCenter)

variable {X : Type*} [Group X] [Finite X]

private theorem mem_conjClass_iff_orderOf_eq_two (hX : IsBenderGroup X) {s : X}
    (hs : orderOf s = 2) {y : X} :
    y ∈ {z | IsConj s z} ↔ orderOf y = 2 := by
  constructor
  · intro hy
    change IsConj s y at hy
    rw [isConj_iff] at hy
    obtain ⟨g, rfl⟩ := hy
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
  · intro hy
    exact IsBenderGroup.isConj_of_orderOf_eq_two hX hs hy

omit [Finite X] in
private theorem exists_sylow_mem_of_orderOf_eq_two {x : X} (hx : orderOf x = 2) :
    ∃ Q : Sylow 2 X, x ∈ (Q : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  exact ⟨Q, hQ (Subgroup.mem_zpowers x)⟩

private theorem mem_sylow_of_commute_of_involution (hX : IsBenderGroup X) (Q : Sylow 2 X)
    {x y : X} (hxQ : x ∈ (Q : Subgroup X)) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : Commute y x) : y ∈ (Q : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, m, hB, -⟩ := IsBenderGroup.exists_fusionBenderBorel hX
  have hM := (hB Q).1
  have hyM : y ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X) :=
    CFSG.Timmesfeld.Connectivity.mem_of_commute_of_stronglyEmbedded hM
      (Subgroup.le_normalizer hxQ) hx hxy
  have hyp : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have h2 : IsPGroup 2 ((Q : Subgroup X) ⊔ Subgroup.zpowers y : Subgroup X) :=
    (Q.isPGroup').to_sup_of_normal_left' hyp (Subgroup.zpowers_le.mpr hyM)
  have heq := Q.is_maximal' h2 le_sup_left
  show y ∈ (Q : Subgroup X)
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

private theorem exists_mem_center_map_ne_one (hX : IsBenderGroup X) (Q : Sylow 2 X) :
    ∃ z : X,
      z ∈ (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype ∧ z ≠ 1 := by
  have hcard : 4 ≤ Nat.card
      ((Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact IsBenderGroup.four_le_card_center hX Q
  have hne : ((Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨(z : X), z.2, fun h => hz1 (Subtype.ext h)⟩

private theorem perpMem_eq_center_map_diff_one (hX : IsBenderGroup X) {s : X}
    (hs : orderOf s = 2) {E : Set X} (hE : E = {y | IsConj s y}) (Q : Sylow 2 X) {x : X}
    (hxE : x ∈ E) (hxQ : x ∈ (Q : Subgroup X)) :
    perpMem E x =
      {y | y ∈ (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype ∧ y ≠ 1} := by
  have hxE' : x ∈ {y | IsConj s y} := hE ▸ hxE
  have hx2 : orderOf x = 2 := (mem_conjClass_iff_orderOf_eq_two hX hs).mp hxE'
  ext y
  rw [mem_perpMem]
  constructor
  · rintro ⟨hyE, hyx⟩
    have hyE' : y ∈ {z | IsConj s z} := hE ▸ hyE
    have hy2 : orderOf y = 2 := (mem_conjClass_iff_orderOf_eq_two hX hs).mp hyE'
    have hyQ : y ∈ (Q : Subgroup X) :=
      mem_sylow_of_commute_of_involution hX Q hxQ hx2 hy2 hyx
    have hy2' : y * y = 1 := by rw [← pow_two, ← hy2, pow_orderOf_eq_one]
    refine ⟨(map_center_eq_sylowCenter (Q : Subgroup X)).ge
      (mem_sylowCenter.mpr ⟨hyQ, fun z hz => ?_⟩), ?_⟩
    · exact (IsBenderGroup.commute_of_mul_self_eq_one hX Q hyQ hy2' z hz).symm.eq
    · intro h
      rw [h, orderOf_one] at hy2
      omega
  · rintro ⟨hyZ, hy1⟩
    obtain ⟨z, hzcent, hzy⟩ := Subgroup.mem_map.mp hyZ
    have hzcomm : ∀ w ∈ (Q : Subgroup X), Commute (z : X) w := by
      intro w hw
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcent ⟨w, hw⟩)).symm
    have hz2 : (z : X) * (z : X) = 1 :=
      IsBenderGroup.mul_self_eq_one_of_commute hX Q z.2 hzcomm
    have hy2eq : y * y = 1 := by rw [← hzy]; exact hz2
    have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2eq) hy1
    have hyQ : y ∈ (Q : Subgroup X) := by rw [← hzy]; exact z.2
    have hyE' : y ∈ {z | IsConj s z} :=
      (mem_conjClass_iff_orderOf_eq_two hX hs).mpr hy2
    refine ⟨?_, ?_⟩
    · rw [hE]; exact hyE'
    · exact IsBenderGroup.commute_of_mul_self_eq_one hX Q hyQ hy2eq x hxQ

private theorem Vmem_eq_perpMem (hX : IsBenderGroup X) {s : X} (hs : orderOf s = 2)
    {E : Set X} (hE : E = {y | IsConj s y}) {x : X} (hx : x ∈ E) :
    Vmem E x = perpMem E x := by
  apply Set.Subset.antisymm
  · intro v hv
    have hvV := mem_Vmem.mp hv
    have hvperp : v ∈ perpMem E v := mem_perpMem_self hvV.1
    rwa [hvV.2] at hvperp
  · intro v hv
    have hvE : v ∈ E := (mem_perpMem.mp hv).1
    have hv' : v ∈ {y | IsConj s y} := hE ▸ hvE
    have hx' : x ∈ {y | IsConj s y} := hE ▸ hx
    have hv2 : orderOf v = 2 := (mem_conjClass_iff_orderOf_eq_two hX hs).mp hv'
    have hx2 : orderOf x = 2 := (mem_conjClass_iff_orderOf_eq_two hX hs).mp hx'
    obtain ⟨Q, hxQ⟩ := exists_sylow_mem_of_orderOf_eq_two hx2
    have hQ := perpMem_eq_center_map_diff_one hX hs hE Q hx hxQ
    have hvQ : v ∈ (Q : Subgroup X) := by
      have hv' := hv
      rw [hQ] at hv'
      obtain ⟨w, -, hw⟩ := Subgroup.mem_map.mp hv'.1
      rw [← hw]
      exact w.2
    have hQv := perpMem_eq_center_map_diff_one hX hs hE Q hvE hvQ
    rw [mem_Vmem]
    exact ⟨hvE, hQv.trans hQ.symm⟩

theorem mem_Vmem_of_commute_of_isBenderGroup (hX : IsBenderGroup X) {s : X} (hs : orderOf s = 2)
    {x y : X} (hx : x ∈ {z | IsConj s z}) (hy : y ∈ {z | IsConj s z}) (hxy : Commute x y) :
    y ∈ Vmem {z | IsConj s z} x := by
  rw [Vmem_eq_perpMem hX hs rfl hx]
  exact mem_perpMem.mpr ⟨hy, hxy.symm⟩

private theorem injective_centerMap_punctured (hX : IsBenderGroup X) :
    Function.Injective fun Q : Sylow 2 X =>
      {y : X | y ∈ (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype ∧
        y ≠ 1} := by
  intro Q₁ Q₂ h
  obtain ⟨q, k, hB, hq, -⟩ := IsBenderGroup.exists_fusionBenderBorel hX
  refine (CFSG.CGT.T75A.sylow_eq_of_center_eq (S := Q₁) (S' := Q₂) (by omega) hB ?_).symm
  let H₁ : Subgroup X := (Subgroup.center (Q₁ : Subgroup X)).map (Q₁ : Subgroup X).subtype
  let H₂ : Subgroup X := (Subgroup.center (Q₂ : Subgroup X)).map (Q₂ : Subgroup X).subtype
  have hH : ({y : X | y ∈ H₁ ∧ y ≠ 1} : Set X) = {y : X | y ∈ H₂ ∧ y ≠ 1} := h
  apply Subgroup.ext
  intro y
  constructor
  · intro hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.one_mem H₂
    · have hmem : y ∈ {y : X | y ∈ H₂ ∧ y ≠ 1} := by
        rw [← hH]
        exact ⟨hy, hy1⟩
      exact hmem.1
  · intro hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact Subgroup.one_mem H₁
    · have hmem : y ∈ {y : X | y ∈ H₁ ∧ y ≠ 1} := by
        rw [hH]
        exact ⟨hy, hy1⟩
      exact hmem.1

private theorem image_Vmem_eq_range_centerMap (hX : IsBenderGroup X) {s : X}
    (hs : orderOf s = 2) {E : Set X} (hE : E = {y | IsConj s y}) :
    Vmem E '' E = Set.range (fun Q : Sylow 2 X =>
      {y : X | y ∈ (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype ∧
        y ≠ 1}) := by
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ {y | IsConj s y} := hE ▸ hx
    have hx2 : orderOf x = 2 := (mem_conjClass_iff_orderOf_eq_two hX hs).mp hx'
    obtain ⟨Q, hxQ⟩ := exists_sylow_mem_of_orderOf_eq_two hx2
    refine ⟨Q, ?_⟩
    rw [Vmem_eq_perpMem hX hs hE hx, perpMem_eq_center_map_diff_one hX hs hE Q hx hxQ]
  · rintro ⟨Q, rfl⟩
    obtain ⟨z, hzH, hz1⟩ := exists_mem_center_map_ne_one hX Q
    obtain ⟨w, hwcent, hw⟩ := Subgroup.mem_map.mp hzH
    have hzQ : z ∈ (Q : Subgroup X) := by
      rw [← hw]
      exact w.2
    have hzsq : z * z = 1 := by
      rw [← hw]
      exact IsBenderGroup.mul_self_eq_one_of_commute hX Q w.2 fun u hu =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hwcent ⟨u, hu⟩)).symm
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
    have hzE' : z ∈ {y | IsConj s y} := (mem_conjClass_iff_orderOf_eq_two hX hs).mpr hz2
    have hzE : z ∈ E := by rw [hE]; exact hzE'
    refine ⟨z, hzE, ?_⟩
    rw [Vmem_eq_perpMem hX hs hE hzE, perpMem_eq_center_map_diff_one hX hs hE Q hzE hzQ]

theorem exists_subgroup_eq_insert_Vmem_of_isBenderGroup (hX : IsBenderGroup X) {s : X}
    (hs : orderOf s = 2) {x : X} (hx : x ∈ {y | IsConj s y}) :
    ∃ R : Subgroup X, (R : Set X) = insert 1 (Vmem {y | IsConj s y} x) := by
  let E : Set X := {y | IsConj s y}
  have hE : E = {y | IsConj s y} := rfl
  have hx' : x ∈ {y | IsConj s y} := hx
  have hx2 : orderOf x = 2 := (mem_conjClass_iff_orderOf_eq_two hX hs).mp hx'
  obtain ⟨Q, hxQ⟩ := exists_sylow_mem_of_orderOf_eq_two hx2
  refine ⟨(Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype, ?_⟩
  have hV : Vmem E x = perpMem E x := Vmem_eq_perpMem hX hs hE hx
  have hP : perpMem E x =
      {y | y ∈ (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype ∧ y ≠ 1} :=
    perpMem_eq_center_map_diff_one hX hs hE Q hx hxQ
  change ((Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype : Set X) =
    insert 1 (Vmem E x)
  rw [hV, hP]
  ext y
  constructor
  · intro hy
    rw [Set.mem_insert_iff]
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr ⟨hy, hy1⟩
  · rw [Set.mem_insert_iff]
    rintro (rfl | ⟨hy, -⟩)
    · exact Subgroup.one_mem _
    · exact hy

theorem ncard_image_Vmem_of_isBenderGroup (hX : IsBenderGroup X)
    {s : X} (hs : orderOf s = 2) (S : Sylow 2 X) :
    (Vmem {y | IsConj s y} '' {y | IsConj s y}).ncard = Nat.card S + 1 := by
  let E : Set X := {y | IsConj s y}
  have hE : E = {y | IsConj s y} := rfl
  have hbridge : CFSG.Open.fusionIsBenderGroup X :=
    CFSG.Open.fusionIsBenderGroup_of_isBenderGroup hX
  have hcount : Nat.card (Sylow 2 X) = Nat.card S + 1 :=
    CFSG.ComponentClassification.Asc76.L26.card_sylow_of_isBender hbridge S
  change (Vmem E '' E).ncard = Nat.card S + 1
  rw [image_Vmem_eq_range_centerMap hX hs hE,
    Set.ncard_range_of_injective (injective_centerMap_punctured hX)]
  exact hcount

end CFSG.OddTranspositions.PartFour
