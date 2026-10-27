module

import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem eq_oPrimeResidualOf_of_j2 {L : Subgroup G}
    (hLp : Group.IsPerfect ↥L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    L = oPrimeResidualOf 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_j2 hJ
  obtain ⟨φJ⟩ := hJ
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set N := oPrimeResidual 3 ↥L with hNdef
  have hNn : N.Normal := oPrimeResidual_normal 3 ↥L
  have hsimp : IsSimpleGroup (↥L ⧸ θ) := by
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact φJ.isSimpleGroup
  have hmapn : (N.map (QuotientGroup.mk' θ)).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective θ)
  have hsup : N ⊔ θ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' θ)) with
      hbot | htop
    · exfalso
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
      have hxN : x ∈ N := Subgroup.subset_closure ⟨1, by rw [pow_one]; exact hx3⟩
      have hxθ : x ∈ θ := by
        have hmem : QuotientGroup.mk' θ x ∈ N.map (QuotientGroup.mk' θ) :=
          Subgroup.mem_map_of_mem _ hxN
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
        exact hmem
      rw [eq_one_of_mem_aschbacherSolvableCore hxθ hx3, orderOf_one] at hx
      omega
    · have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp θ.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ N ⊔ θ := hsup ▸ Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨n, hn, t, ht, rfl⟩ := hx
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have : Group.IsSolvable θ := hθ.1
  have hsolv : Group.IsSolvable (↥L ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (↥L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ N) hsolv
  rw [oPrimeResidualOf, ← hNdef, hNtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_delta_of_j2
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A)) (hLY : L ≤ Y)
    (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) : L = delta A (lB A) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  set D := delta A (lB A) L with hDdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hLH : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hmem : ∀ R : Subgroup G, R ≤ L → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ≤ D := fun R hRL hR3 hAR =>
    le_delta (mem_scriptQ_of_hj_point h.toSec14Std hJ ⟨hRL.trans hLH,
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩).1 hRL
  have hDL : D ≤ L := delta_le L
  have hQ : ∀ Q ∈ collectionIn (scriptQ A (lB A)) Y, Q ≤ D ⊔ O := by
    rintro Q ⟨hQ, hQY⟩
    have hQO : IsPiSubgroup (piCompl 3) (Q ⊔ O) := isPiSubgroup_piCompl_sup hQ.1.2.1
      ((isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3) (hQY.trans hYO)
    have hR : (Q ⊔ O) ⊓ L ≤ D := hmem _ inf_le_right
      (fun h3 => (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hQO
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
      ((le_inf (le_normalizer_sup hQ.1.2.2 hAO) hD.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
    intro q hq
    have hqY : q ∈ ((L ⊔ O : Subgroup G) : Set G) := hcov (hQY hq)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L O (hLY.trans hYO)] at hqY
    obtain ⟨l, hl, o, ho, rfl⟩ := hqY
    have hlR : l ∈ (Q ⊔ O) ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, hl⟩
      have hlo : l = (l * o) * o⁻¹ := by group
      rw [hlo]
      exact mul_mem (Subgroup.mem_sup_left hq) (inv_mem (Subgroup.mem_sup_right ho))
    exact mul_mem (Subgroup.mem_sup_left (hR hlR)) (Subgroup.mem_sup_right ho)
  have hYle : Y ≤ D ⊔ O :=
    hY.2.2.1.le.trans (show delta A (lB A) Y ≤ D ⊔ O from sSup_le hQ)
  have hLO : L ⊓ O ≤ D := hmem _ inf_le_left
    (fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right)))
    ((le_inf hD.le_normalizer hAO).trans Subgroup.inf_normalizer_le_normalizer_inf)
  refine le_antisymm (fun l hl => ?_) hDL
  have hl' : l ∈ ((D ⊔ O : Subgroup G) : Set G) := hYle (hLY hl)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D O (hDL.trans (hLY.trans hYO))] at hl'
  obtain ⟨d, hd, o, ho, rfl⟩ := hl'
  have hoL : o ∈ L := by
    have := mul_mem (inv_mem (hDL hd)) hl
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hd (hLO ⟨hoL, ho⟩)

theorem isQuasisimple_of_cover {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {L Y : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hLY : L ≤ Y)
    (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) (h3 : 3 ∣ Nat.card L) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := CFSG.pCore 2 ↥Y with hP
  set K := CFSG.pCore 2 ↥L with hK
  set f : ↥L →* ↥Y ⧸ P := (QuotientGroup.mk' P).comp (Subgroup.inclusion hLY) with hf
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
    have hy : (y : G) ∈ ((L ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := hcov y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L _
      (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))] at hy
    obtain ⟨l, hl, o, ho, hlo⟩ := hy
    obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp
      (show o ∈ (CFSG.Open.pCore 2 ↥Y).map Y.subtype from ho)
    have ho'P : o' ∈ P := by rwa [hP]
    have hy' : y = Subgroup.inclusion hLY ⟨l, hl⟩ * o' := Subtype.ext hlo.symm
    have h1 : QuotientGroup.mk' P o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'P
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hy', hf, MonoidHom.comp_apply, map_mul, h1, mul_one]
  have hker : f.ker ≤ K := by
    have hp : IsPGroup 2 f.ker := by
      intro x
      have hx : Subgroup.inclusion hLY (x : ↥L) ∈ P := by
        have hx1 : QuotientGroup.mk' P (Subgroup.inclusion hLY (x : ↥L)) = 1 :=
          MonoidHom.mem_ker.mp x.2
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨_, hx⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun z : ↥P => ((z : ↥Y) : G)) hn
      simpa using this
    exact le_sSup (show f.ker ∈ {N : Subgroup ↥L | N.Normal ∧ IsPGroup 2 N} from
      ⟨inferInstance, hp⟩)
  have hq : CFSG.IsQuasisimple (↥L ⧸ f.ker) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm hY.2.2.2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (φ := QuotientGroup.map f.ker K (MonoidHom.id ↥L) (fun y hy => hker hy)) hq ?_
    ⟨QuotientGroup.mk x, ?_⟩
  · intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact ⟨QuotientGroup.mk y, rfl⟩
  · intro h1
    have h1' : (QuotientGroup.mk x : ↥L ⧸ K) = 1 := h1
    have hxK : x ∈ K := (QuotientGroup.eq_one_iff x).mp h1'
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨x, hxK⟩
    have hxn : x ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hdvd : 3 ∣ 2 ^ n := hx ▸ orderOf_dvd_of_pow_eq_one hxn
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega

theorem mem_scriptY4_of_j2
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523 A (lB A) L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hLY : L ≤ Y) : L ∈ scriptY4 A (lB A) := by
  have hD := h.toSec13Data
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y := by
    have hc := (h1523 hJ Y hY).1
    rw [inf_eq_right.mpr hLY] at hc
    exact hc.le
  exact ⟨⟨fun hL => hY4.1.1 (top_le_iff.mp (hL ▸ hLY)), hD.le_normalizer⟩,
    eq_oPrimeResidualOf_of_j2
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ,
    eq_delta_of_j2 h hJ hY4 hLY hcov,
    isQuasisimple_of_cover hY4 hLY hcov (three_dvd_card_of_j2 hJ)⟩

theorem meetsY4_of_j2
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523 A (lB A) L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hLY : L ≤ Y) : MeetsY4 A (lB A) L Y :=
  ⟨L, mem_scriptY4_of_j2 h hJ h1523 hY hLY, le_inf le_rfl hLY⟩

end CFSG.RankThree.PartTwo.Sec16
