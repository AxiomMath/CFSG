module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
public import CFSG.RankThree.PartTwo.Sec16.Item166ThetaCompY

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem lB_le_of_eq_sup {d : G} {X : Subgroup G}
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) X) :
    lB A (Subgroup.closure {c, d}) ≤ X := by
  rw [hXL]
  exact le_sup_left

private theorem lB_le_centralizer_d (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    lB A (Subgroup.closure {c, d}) ≤ Subgroup.centralizer ({d} : Set G) := by
  rw [Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
  exact Item148HJ.residual_le_centralizer_singleton L d

private theorem isPerfect_lB (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    Group.IsPerfect ↥(lB A (Subgroup.closure {c, d})) := by
  rw [Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
  exact Item148HJ.residual_isPerfect L d

private theorem isTripleCover_lB_closure (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    Sec4.IsTripleCover
      (↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2
        ↥(lB A (Subgroup.closure {c, d})))
      (alternatingGroup (Fin 6)) :=
  Ctr166.isTripleCover_lB h.toSec14Std
    (Ctr166.isHyperplane_closure_cd h hJ hdA hd1 hdc)
    (Ctr166.isLBConfig_closure_cd_of_threeCentral h hJ hdc)

private theorem theta_lB_eq_pCore_two (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    aschbacherSolvableCore 3 ↥(lB A (Subgroup.closure {c, d})) =
      CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d})) := by
  set J := lB A (Subgroup.closure {c, d}) with hJdef
  haveI : Group.IsPerfect ↥J := by
    rw [hJdef]
    exact isPerfect_lB h hJ hdA hd1 hdc
  have htc := isTripleCover_lB_closure h hJ hdA hd1 hdc
  rw [← hJdef] at htc
  obtain ⟨-, -, hθ3, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
  set Q := CFSG.pCore 2 ↥J with hQ
  haveI : Q.Normal := CFSG.pCore_normal
  have hO2θ : Q ≤ aschbacherSolvableCore 3 ↥J :=
    hθO 2 Nat.prime_two (by norm_num)
  have hθn : (aschbacherSolvableCore 3 ↥J).Normal :=
    aschbacherSolvableCore_normal 3 ↥J
  let f := QuotientGroup.mk' Q
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective Q
  have hZn : ((aschbacherSolvableCore 3 ↥J).map f).Normal := hθn.map f hf
  have hZ3 : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥J).map f) := fun h3 =>
    hθ3 (h3.trans (Subgroup.card_map_dvd _ f))
  have hZbot : (aschbacherSolvableCore 3 ↥J).map f = ⊥ :=
    ThetaCompY.eq_bot_of_normal_of_not_three_dvd (T := ↥J ⧸ Q)
      (N := (aschbacherSolvableCore 3 ↥J).map f) htc hZ3
  have hθle : aschbacherSolvableCore 3 ↥J ≤ Q := by
    rw [← QuotientGroup.ker_mk' Q]
    exact (Subgroup.map_eq_bot_iff (f := f) _).mp hZbot
  exact le_antisymm hθle hO2θ

private noncomputable def quotHom {J X : Subgroup G} (hJX : J ≤ X) :
    ↥J →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)).comp (Subgroup.inclusion hJX)

private theorem subgroupOf_sup_theta_eq_top {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    J.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X = ⊤ := by
  refine Subgroup.map_injective (f := X.subtype) X.subtype_injective ?_
  have h1 : (J.subgroupOf X).map X.subtype ⊔
      (aschbacherSolvableCore 3 ↥X).map X.subtype = X := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJX]
    exact hX.symm
  rw [Subgroup.map_sup, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem quotHom_surjective {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    Function.Surjective (quotHom hJX) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) q
  have hx : x ∈ J.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X := by
    rw [subgroupOf_sup_theta_eq_top hJX hX]
    exact Subgroup.mem_top x
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
  have hzone : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) z = 1 :=
    (QuotientGroup.eq_one_iff z).mpr hz
  calc quotHom hJX ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
      = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y := rfl
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y *
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) z := by rw [hzone, mul_one]
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (y * z) := (map_mul _ _ _).symm
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x := by rw [hyz]

private theorem quotHom_ker (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {X : Subgroup G}
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) X) :
    (quotHom (lB_le_of_eq_sup hXL)).ker =
      CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d})) := by
  set J := lB A (Subgroup.closure {c, d}) with hJdef
  have hJX : J ≤ X := lB_le_of_eq_sup hXL
  have hinf := inf_theta_eq_of_eq_sup hJX hXL
  have hθ : aschbacherSolvableCore 3 ↥J = CFSG.pCore 2 ↥J := by
    rw [hJdef]
    exact theta_lB_eq_pCore_two h hJ hdA hd1 hdc
  ext j
  rw [MonoidHom.mem_ker]
  constructor
  · intro hj
    have hjθ : Subgroup.inclusion hJX j ∈ aschbacherSolvableCore 3 ↥X :=
      (QuotientGroup.eq_one_iff _).mp hj
    have hjG : (j : G) ∈ J ⊓ inSubgroup (aschbacherSolvableCore 3) X :=
      ⟨j.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJX j, hjθ, rfl⟩⟩
    rw [hinf] at hjG
    change (j : G) ∈ (aschbacherSolvableCore 3 ↥J).map J.subtype at hjG
    rw [hθ] at hjG
    obtain ⟨t, ht, htj⟩ := Subgroup.mem_map.mp hjG
    have htj' : t = j := Subtype.ext htj
    rwa [htj'] at ht
  · intro hj
    have hjθ : (j : G) ∈
        (aschbacherSolvableCore 3 ↥J).map J.subtype := by
      rw [hθ]
      exact Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
    have hjG : (j : G) ∈ J ⊓ inSubgroup (aschbacherSolvableCore 3) X := by
      rw [hinf]
      exact hjθ
    have hj' : Subgroup.inclusion hJX j ∈ aschbacherSolvableCore 3 ↥X :=
      (Subgroup.mem_map_iff_mem X.subtype_injective).mp hjG.2
    exact (QuotientGroup.eq_one_iff _).mpr hj'

theorem mem_of_eq_lB_sup (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {X : Subgroup G}
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) X) :
    d ∈ X :=
  (lB_le_of_eq_sup hXL) (Ctr166.mem_lB_closure h hJ hdA hd1 hdc)

theorem isTripleCover_quot (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {X : Subgroup G}
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) X) :
    Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) := by
  have hJX : lB A (Subgroup.closure {c, d}) ≤ X := lB_le_of_eq_sup hXL
  have hker := quotHom_ker h hJ hdA hd1 hdc hXL
  let e : (↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2
        ↥(lB A (Subgroup.closure {c, d}))) ≃*
      (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (quotHom hJX)
        (quotHom_surjective hJX hXL))
  exact KFacts.KS14.isTripleCover_congr e (isTripleCover_lB_closure h hJ hdA hd1 hdc)

theorem mk_mem_center (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {X : Subgroup G}
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) X) :
    ((⟨d, mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL⟩ : ↥X) : ↥X ⧸
        aschbacherSolvableCore 3 ↥X) ∈
      Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
  have hJX : lB A (Subgroup.closure {c, d}) ≤ X := lB_le_of_eq_sup hXL
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := quotHom_surjective hJX hXL y
  have hcomm : Subgroup.inclusion hJX x *
        (⟨d, mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL⟩ : ↥X) =
      (⟨d, mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL⟩ : ↥X) *
        Subgroup.inclusion hJX x := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (lB_le_centralizer_d h hJ hdA hd1 hdc x.2)
  change (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) (Subgroup.inclusion hJX x) *
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
        (⟨d, mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL⟩ : ↥X) =
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
        (⟨d, mem_of_eq_lB_sup h hJ hdA hd1 hdc hXL⟩ : ↥X) *
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) (Subgroup.inclusion hJX x)
  rw [← map_mul, ← map_mul, hcomm]

end CFSG.RankThree.PartTwo.Sec16.Kcd166
