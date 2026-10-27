module

public import CFSG.OddTranspositions.PartThree.LocalBenderCenter

import CFSG.CGT.Timmesfeld75.SimpleAssembly
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.OddTranspositions.PartThree.LocalBenderInvolutions
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

section Abstract

variable {H : Type*} [Group H]

theorem sup_zpowers_eq_top_of_index_two {N : Subgroup H} (hN : N.index = 2) {z : H}
    (hz : z ∉ N) : N ⊔ Subgroup.zpowers z = ⊤ := by
  rw [eq_top_iff]
  intro h _
  by_cases hh : h ∈ N
  · exact Subgroup.mem_sup_left hh
  · have hhz : h * z ∈ N := (Subgroup.mul_mem_iff_of_index_two hN).mpr (iff_of_false hh hz)
    have hzp : z⁻¹ ∈ Subgroup.zpowers z := inv_mem (Subgroup.mem_zpowers z)
    simpa using mul_mem (Subgroup.mem_sup_left hhz) (Subgroup.mem_sup_right hzp)

theorem commutator_self_eq_of_sup_center {N Z : Subgroup H} [N.Normal]
    (hZ : Z ≤ Subgroup.center H) (hsup : N ⊔ Z = ⊤) : ⁅N, N⁆ = commutator H := by
  have hZt : ⁅Z, (⊤ : Subgroup H)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hZ
  have hNZ : ⁅N, Z⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono le_top le_rfl).trans
      (Subgroup.commutator_top_left_eq_bot_iff_le_center.mpr hZ).le)
  calc ⁅N, N⁆ = ⁅N, N⁆ ⊔ ⁅N, Z⁆ := by rw [hNZ, sup_bot_eq]
    _ = ⁅N, N ⊔ Z⁆ := (Subgroup.commutator_sup_left N N Z).symm
    _ = ⁅N, ⊤⁆ := by rw [hsup]
    _ = ⁅N, ⊤⁆ ⊔ ⁅Z, ⊤⁆ := by rw [hZt, sup_bot_eq]
    _ = ⁅N ⊔ Z, ⊤⁆ := (Subgroup.commutator_sup_right N Z ⊤).symm
    _ = commutator H := by rw [hsup, commutator_def]

theorem isPerfect_commutator_of_sup_center {Z : Subgroup H} (hZ : Z ≤ Subgroup.center H)
    (hsup : commutator H ⊔ Z = ⊤) : Group.IsPerfect (commutator H) := by
  rw [Subgroup.isPerfect_iff]
  exact commutator_self_eq_of_sup_center hZ hsup

theorem center_eq_comap_of_sup_center {N Z : Subgroup H} (hZ : Z ≤ Subgroup.center H)
    (hsup : N ⊔ Z = ⊤) : Subgroup.center N = (Subgroup.center H).comap N.subtype := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hx g
    have hC : (⊤ : Subgroup H) ≤ Subgroup.centralizer {(x : H)} := by
      rw [← hsup]
      refine sup_le (fun n hn => ?_) (fun c hc => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hx ⟨n, hn⟩)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp (hZ hc) x).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC (Subgroup.mem_top g))
  · intro hx g
    exact Subtype.ext (hx g)

theorem nonempty_quotientCenter_mulEquiv {N Z : Subgroup H} (hZ : Z ≤ Subgroup.center H)
    (hsup : N ⊔ Z = ⊤) : Nonempty ((N ⧸ Subgroup.center N) ≃* (H ⧸ Subgroup.center H)) := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  let φ : N →* H ⧸ Subgroup.center H := (QuotientGroup.mk' (Subgroup.center H)).comp N.subtype
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨n, hn, c, hc, hnc⟩ :=
      Subgroup.mem_sup_of_normal_right.mp (hsup ▸ Subgroup.mem_top h)
    refine ⟨⟨n, hn⟩, ?_⟩
    show QuotientGroup.mk n = QuotientGroup.mk h
    rw [← hnc, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).mpr (hZ hc), mul_one]
  have hker : φ.ker = Subgroup.center N := by
    rw [center_eq_comap_of_sup_center hZ hsup]
    ext x
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem derived_structure_abstract [Finite H] {z : H} (hzc : z ∈ Subgroup.center H)
    (hzN : z ∉ commutator H) (hidx : (commutator H).index = 2)
    (hO : Subgroup.center H ⊓ commutator H ≤ CFSG.oddCore H)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (H ⧸ Subgroup.center H)) :
    commutator H ⊔ Subgroup.zpowers z = ⊤ ∧ Group.IsPerfect (commutator H) ∧
      Odd (Nat.card (Subgroup.center (commutator H))) ∧
      CFSG.BenderSuzuki.IsBenderGroup (commutator H ⧸ Subgroup.center (commutator H)) := by
  have hsup := sup_zpowers_eq_top_of_index_two hidx hzN
  have hZ : Subgroup.zpowers z ≤ Subgroup.center H := Subgroup.zpowers_le.mpr hzc
  refine ⟨hsup, isPerfect_commutator_of_sup_center hZ hsup, ?_, ?_⟩
  · have hle : (Subgroup.center (commutator H)).map (commutator H).subtype ≤ CFSG.oddCore H := by
      rintro _ ⟨x, hx, rfl⟩
      have hxc : (x : H) ∈ Subgroup.center H := by
        rw [center_eq_comap_of_sup_center hZ hsup] at hx
        exact hx
      exact hO ⟨hxc, x.2⟩
    have hdvd : Nat.card (Subgroup.center (commutator H)) ∣ Nat.card (CFSG.oddCore H) := by
      rw [← Subgroup.card_subtype (commutator H) (Subgroup.center (commutator H))]
      exact Subgroup.card_dvd_of_le hle
    exact CFSG.ABGLocalTools.odd_card_oddCore.of_dvd_nat hdvd
  · obtain ⟨e⟩ := nonempty_quotientCenter_mulEquiv hZ hsup
    exact CFSG.CGT.Timmesfeld75.isBenderGroup_of_mulEquiv e hB

theorem structure_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hperf : Group.IsPerfect A) (hodd : Odd (Nat.card (Subgroup.center A)))
    (hB : CFSG.BenderSuzuki.IsBenderGroup (A ⧸ Subgroup.center A)) :
    commutator B = ⊤ ∧ Odd (Nat.card (Subgroup.center B)) ∧
      CFSG.BenderSuzuki.IsBenderGroup (B ⧸ Subgroup.center B) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  · rwa [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  · exact CFSG.CGT.Timmesfeld75.isBenderGroup_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
        (Subgroup.map_center_eq e)).symm hB

end Abstract

section Local

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def derivedLocal (D : Set G) (z : G) : Subgroup G :=
  (commutator (localGroup D z)).map (localGroup D z).subtype

theorem center_localGroup_eq_solvableRadical (hS : Setup G D) {z u v : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z)) :
    Subgroup.center (localGroup D z) = CFSG.solvableRadical (localGroup D z) :=
  le_antisymm otg2_center_le_solvableRadical
    (solvableRadical_le_center_localGroup hS hu hv huv hc huvz htrans hQ)

theorem center_inf_commutator_le_oddCore (hS : Setup G D)
    {z u v : G} (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    Subgroup.center (localGroup D z) ⊓ commutator (localGroup D z) ≤
      CFSG.oddCore (localGroup D z) := by
  classical
  set H := localGroup D z with hH
  set O := CFSG.oddCore H with hO
  have hinf := oddCore_quotient_inf_commutator_eq_bot hS hu hv huv hc huvz htrans hQ hB
  have hmap : (commutator H).map (QuotientGroup.mk' O) = commutator (H ⧸ O) := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)]
  rintro y ⟨hyc, hyN⟩
  have hmem : QuotientGroup.mk' O y ∈
      (CFSG.solvableRadical H).map (QuotientGroup.mk' O) ⊓ commutator (H ⧸ O) :=
    ⟨Subgroup.mem_map_of_mem _ (otg2_center_le_solvableRadical hyc),
      hmap ▸ Subgroup.mem_map_of_mem _ hyN⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff y).mp hmem

theorem self_not_mem_commutator_localGroup (hS : Setup G D)
    {z u v : G} (hz1 : z ≠ 1) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    (⟨z, self_mem_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz⟩ : localGroup D z) ∉
      commutator (localGroup D z) := by
  classical
  have hzH := self_mem_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  intro hz'N
  let z' : localGroup D z := ⟨z, hzH⟩
  have hz'c : z' ∈ Subgroup.center (localGroup D z) :=
    self_mem_center_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  have hz'2 : z' * z' = 1 :=
    Subtype.ext (mul_self_eq_one_of_mul_mul_mem hS.oddT hu hv hc huvz)
  have hz'ne : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzO := center_inf_commutator_le_oddCore hS hu hv huv hc huvz htrans hQ hB ⟨hz'c, hz'N⟩
  have hord2 : orderOf z' = 2 :=
    @orderOf_eq_prime _ _ z' 2 ⟨Nat.prime_two⟩ (by rwa [pow_two]) hz'ne
  exact CFSG.Timmesfeld.Connectivity.not_mem_of_odd_card CFSG.ABGLocalTools.odd_card_oddCore
    hord2 hzO

theorem index_commutator_localGroup (hS : Setup G D)
    {z u v : G} (hz1 : z ≠ 1) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    (commutator (localGroup D z)).index = 2 := by
  have hle := (setup_localGroup_of_transitive hS hu htrans).index_commutator_le_two
  have hne : (commutator (localGroup D z)).index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one]
    intro htop
    exact self_not_mem_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB
      (htop ▸ Subgroup.mem_top _)
  have hpos : (commutator (localGroup D z)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem derivedLocal_structure (hS : Setup G D) {z u v : G}
    (hz1 : z ≠ 1) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    localGroup D z = derivedLocal D z ⊔ Subgroup.zpowers z ∧ z ∉ derivedLocal D z ∧
      (∀ x ∈ centSet D z, z * x ∈ derivedLocal D z) ∧
      commutator (derivedLocal D z) = ⊤ ∧
      Odd (Nat.card (Subgroup.center (derivedLocal D z))) ∧
      CFSG.BenderSuzuki.IsBenderGroup (derivedLocal D z ⧸ Subgroup.center (derivedLocal D z)) := by
  classical
  have hzH : z ∈ localGroup D z := self_mem_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  have hz'c := self_mem_center_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  have hz'N := self_not_mem_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB
  have hidx := index_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB
  have hB' : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ Subgroup.center (localGroup D z)) :=
    CFSG.CGT.Timmesfeld75.isBenderGroup_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq
      (center_localGroup_eq_solvableRadical hS hu hv huv hc huvz htrans hQ)) hB
  obtain ⟨hsup, hperf, hodd, hBen⟩ := derived_structure_abstract hz'c hz'N hidx
    (center_inf_commutator_le_oddCore hS hu hv huv hc huvz htrans hQ hB) hB'
  obtain ⟨h4, h5, h6⟩ := structure_of_mulEquiv
    (Subgroup.equivMapOfInjective (commutator (localGroup D z)) (localGroup D z).subtype
      (localGroup D z).subtype_injective) hperf hodd hBen
  refine ⟨?_, ?_, ?_, h4, h5, h6⟩
  · calc localGroup D z = (⊤ : Subgroup (localGroup D z)).map (localGroup D z).subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (commutator (localGroup D z) ⊔ Subgroup.zpowers ⟨z, hzH⟩).map
            (localGroup D z).subtype := by rw [hsup]
      _ = derivedLocal D z ⊔ Subgroup.zpowers z := by
          rw [Subgroup.map_sup, MonoidHom.map_zpowers]
          rfl
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    exact hz'N (by rwa [show y = ⟨z, hzH⟩ from Subtype.ext hyz] at hy)
  · intro x hx
    have hxH : x ∈ localGroup D z := mem_localGroup_of_mem hx
    have hxN : (⟨x, hxH⟩ : localGroup D z) ∉ commutator (localGroup D z) :=
      not_mem_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB ⟨x, hxH⟩ hx
    exact Subgroup.mem_map.mpr
      ⟨_, (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hz'N hxN), rfl⟩

theorem mul_mem_centSet_of_mem_derivedLocal (hS : Setup G D)
    {z u v : G} (hz1 : z ≠ 1) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ∀ t ∈ derivedLocal D z, t * t = 1 → t ≠ 1 → z * t ∈ centSet D z := by
  classical
  intro t ht htt ht1
  obtain ⟨t', ht'N, rfl⟩ := Subgroup.mem_map.mp ht
  have hzH := self_mem_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  have hR := solvableRadical_le_center_localGroup hS hu hv huv hc huvz htrans hQ
  have hZ2 := eq_one_or_eq_of_mem_center_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB
  rcases localGroup_involution_cases_of_isBenderGroup hS hu hv huv htrans hR hZ2 hB t'.2 htt
    with h | h | h | h
  · exact absurd h ht1
  · exact absurd (by rwa [show t' = ⟨z, hzH⟩ from Subtype.ext h] at ht'N)
      (self_not_mem_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB)
  · exact absurd ht'N (not_mem_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB t' h)
  · have hcom : z * (t' : G) = (t' : G) * z := (commute_of_mem_localGroup t'.2).eq.symm
    show z * (t' : G) ∈ centSet D z
    rwa [hcom]

end Local

end CFSG.OddTranspositions.PartThree
