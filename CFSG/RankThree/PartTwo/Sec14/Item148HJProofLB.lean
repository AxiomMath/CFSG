module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

noncomputable def rangeEquivOfKerEq {K X₁ X₂ : Type*} [Group K] [Group X₁] [Group X₂]
    (ψ₁ : K →* X₁) (ψ₂ : K →* X₂) (h : ψ₁.ker = ψ₂.ker) : ψ₁.range ≃* ψ₂.range :=
  (QuotientGroup.quotientKerEquivRange ψ₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange ψ₂))

theorem commutator_le_of_mem_thetaComponents_of_ne {H : Type*} [Group H] [Finite H]
    {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents 3 H) (h₂ : L₂ ∈ thetaComponents 3 H)
    (hne : L₁ ≠ L₂) : ⁅L₁, L₂⁆ ≤ aschbacherSolvableCore 3 H := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H)
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hK₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₁
  have hK₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₂
  have hKne : L₁.map π ≠ L₂.map π := fun h => hne (hbij.injOn h₁ h₂ h)
  have hcomm := (CFSG.LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hcomm
  exact hcomm

theorem eq_bot_of_normal_of_quasisimple {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hZ : Nat.card (Subgroup.center Q) = 3) {M : Subgroup Q} (hM : M.Normal)
    (hM3 : ¬ 3 ∣ Nat.card M) : M = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hM with h | h
  · exfalso
    apply hM3
    rw [h, Subgroup.card_top]
    exact hZ ▸ Subgroup.card_subgroup_dvd_card _
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 M :=
      (IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])).to_le h
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rcases n with _ | n
    · exact Subgroup.eq_bot_of_card_eq M (by rw [hn, pow_zero])
    · exact absurd (hn ▸ dvd_pow_self 3 (Nat.succ_ne_zero n)) hM3

theorem le_ker_of_normal {K Y : Type*} [Group K] [Group Y] [Finite K] [Finite Y] (φ : K →* Y)
    (hq : IsQuasisimple φ.range) (hZ : Nat.card (Subgroup.center φ.range) = 3)
    {M : Subgroup K} (hM : M.Normal) (hM3 : ¬ 3 ∣ Nat.card M) : M ≤ φ.ker := by
  have hn : (M.map φ.rangeRestrict).Normal := hM.map _ φ.rangeRestrict_surjective
  have h3 : ¬ 3 ∣ Nat.card (M.map φ.rangeRestrict) := fun h =>
    hM3 (h.trans (Subgroup.card_map_dvd M _))
  have hb := eq_bot_of_normal_of_quasisimple hq hZ hn h3
  intro m hm
  have : φ.rangeRestrict m ∈ M.map φ.rangeRestrict := Subgroup.mem_map_of_mem _ hm
  rw [hb, Subgroup.mem_bot] at this
  rw [MonoidHom.mem_ker]
  exact congrArg Subtype.val this

section J2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem residual_le (L : Subgroup G) (d : G) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ L :=
  (Subgroup.map_subtype_le _).trans inf_le_left

omit [Finite G] in
theorem residual_le_centralizer_singleton (L : Subgroup G) (d : G) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      Subgroup.centralizer ({d} : Set G) :=
  (Subgroup.map_subtype_le _).trans inf_le_right

theorem residual_isPerfect (L : Subgroup G) (d : G) :
    Group.IsPerfect ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) := by
  have h := (perfect_residual_characterization
    (G := ↥(L ⊓ Subgroup.centralizer ({d} : Set G)))).2.2.1
  exact Group.IsPerfect.ofSurjective
    (f := ((perfectResidual ↥(L ⊓ Subgroup.centralizer ({d} : Set G))).equivMapOfInjective _
      (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)

noncomputable def resProj (L : Subgroup G) (d : G) :
    ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) →*
      (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp (Subgroup.inclusion (residual_le L d))

omit [Finite G] in
theorem mem_ker_resProj {L : Subgroup G} {d : G}
    (j : ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))) :
    j ∈ (resProj L d).ker ↔ (j : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [MonoidHom.mem_ker, resProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  change _ ↔ (j : G) ∈ (aschbacherSolvableCore 3 ↥L).map L.subtype
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨x, hx, hxj⟩
    have : x = Subgroup.inclusion (residual_le L d) j := Subtype.ext hxj
    exact this ▸ hx

theorem exists_sylow_quot {L : Subgroup G} {d : G} (hdL : d ∈ L)
    (hc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)}) :
    ∃ P : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ ∈ (P : Subgroup _) ∧
        (P : Subgroup _) ≤ Subgroup.centralizer
          {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} := by
  obtain ⟨S, hdS, hSd⟩ := hc
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem _ hdS
  · rw [Sylow.coe_mapSurjective]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hSd hy)]


theorem resProj_range {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdL : d ∈ L) (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1)
    (hbc : ∃ P : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ ∈ (P : Subgroup _) ∧
        (P : Subgroup _) ≤ Subgroup.centralizer
          {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩}) :
    (resProj L d).range = Subgroup.centralizer
      {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set π := QuotientGroup.mk' θ with hπ
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  set CL := Subgroup.centralizer ({d'} : Set ↥L) with hCL
  set J' := inSubgroup perfectResidual CL with hJ'
  have hJeq : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) =
      J'.map L.subtype := by
    rw [hJ', CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      L.subtype L.subtype_injective, hCL,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton]
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hd3p : IsPGroup 3 (Subgroup.zpowers d') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hd'3 hd'1, pow_one])
  have hCmap : CL.map π = Subgroup.centralizer ({π d'} : Set (↥L ⧸ θ)) := by
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 θ hθ3
      (Subgroup.zpowers d') hd3p
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
    exact h
  set Cbar := Subgroup.centralizer ({π d'} : Set (↥L ⧸ θ)) with hCbar
  have hJQ : J'.map π = inSubgroup perfectResidual Cbar := by
    let ψ : ↥CL →* ↥Cbar := (π.comp CL.subtype).codRestrict Cbar fun x =>
      hCmap ▸ Subgroup.mem_map_of_mem π x.2
    have hψ : Function.Surjective ψ := by
      rintro ⟨q, hq⟩
      rw [← hCmap] at hq
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    have h : (perfectResidual ↥CL).map ψ = perfectResidual ↥Cbar :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψ
    rw [hJ', inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hπd1 : π d' ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd'1 (eq_one_of_mem_aschbacherSolvableCore h1 hd'3)
  have htop : perfectResidual ↥Cbar = ⊤ :=
    KFacts.KS14.j2_perfectResidual_centralizer_eq_top h415 hJ hπd1 hbc
  have hJQ' : J'.map π = Cbar := by
    rw [hJQ, inSubgroup, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [resProj, MonoidHom.range_comp, Subgroup.inclusion_range, hJeq, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  exact hJQ'

theorem centralizer_facts {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {z : ↥L ⧸ aschbacherSolvableCore 3 ↥L} (hz1 : z ≠ 1)
    (hz : ∃ P : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L), z ∈ (P : Subgroup _) ∧
      (P : Subgroup _) ≤ Subgroup.centralizer {z}) :
    IsQuasisimple ↥(Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) ∧
      Group.IsPerfect ↥(Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) ∧
      Sec4.IsTripleCover ↥(Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
        (alternatingGroup (Fin 6)) ∧
      Subgroup.center ↥(Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) =
        (Subgroup.zpowers z).subgroupOf
          (Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hperf := KFacts.KS14.j2_centralizer_isPerfect h415 hJ hz1 hz
  have htc := KFacts.KS14.j2_centralizer_isTripleCover h415 hJ hz1 hz
  have hq :
      IsQuasisimple ↥(Subgroup.centralizer ({z} : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
    have h := j2_centralizer_residual_quasisimple h415 hJ hz1 hz
    have htop := KFacts.KS14.j2_perfectResidual_centralizer_eq_top h415 hJ hz1 hz
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) h
  exact ⟨hq, hperf, htc, KFacts.KS14.j2_center_centralizer h415 hJ hz1 hz⟩

end J2

section Config

variable {G : Type} [Group G] [Finite G]

theorem residual_le_lB {A B Lb : Subgroup G} {b d : G} (hc : IsLBConfig A B b d Lb) :
    inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) ≤ lB A B :=
  le_iSup_of_le b (le_iSup_of_le d (le_iSup_of_le Lb (le_iSup_of_le hc le_rfl)))

theorem residual_le_centralizer {A B Lb : Subgroup G} {b d : G} (hc : IsLBConfig A B b d Lb) :
    inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      Subgroup.centralizer (B : Set G) :=
  (residual_le_lB hc).trans (lB_le_centralizer A B)

theorem sec14Std_of_isLBConfig {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hc : IsLBConfig A B b d Lb) : Sec14Std G A b Lb :=
  { h with zpowers_mem_omegaA := hc.2.1, mem_lA := hc.2.2.1 ▸ Set.mem_singleton Lb }


theorem j2_of_isLBConfig {A B Lb : Subgroup G} {b d : G} (hc : IsLBConfig A B b d Lb) :
    Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨-, -, -, ⟨φ⟩, -⟩ := hc
  have hJ2s := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJ2c := KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15
  have hc0 : Subgroup.center (↥Lb ⧸ CFSG.pCore 2 ↥Lb) = ⊥ := by
    have hmap := Subgroup.map_center_eq φ
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  have hq := isQuasisimple_of_mulEquiv_nativeJ2 hJ2s hJ2c φ
  have hθ := aschbacherSolvableCore_eq_pCore_two hq hc0
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans φ⟩

theorem centralizer_le_normalizer_residual {A L B Lb : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hc : IsLBConfig A B b d Lb) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer
      ((inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) : Subgroup G) :
        Set G) := by
  have hS := sec14Std_of_isLBConfig h hc
  have hN := centralizer_le_normalizer_of_j2 hS (j2_of_isLBConfig hc)
  obtain ⟨hBbd, -⟩ := hc
  have hCb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d})))
  have hCd : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)))
  exact (Late.le_normalizer_inf (hCb.trans hN) (hCd.trans Subgroup.le_normalizer)).trans
    (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _)

theorem inf_le_residual {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    A ⊓ Lb ≤ inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) := by
  obtain ⟨-, hd1⟩ := hc.ne_one hB h.isE27
  have hJ := j2_of_isLBConfig hc
  obtain ⟨hBbd, -, -, -, hdL, S, hdS, hSd⟩ := hc
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  exact inf_le_residual_of_central h.toSec13Data.isElemAbelian hJ hdA hdL hd1
    (exists_sylow_quot hdL ⟨S, hdS, hSd⟩)

theorem residual_mem_thetaComponentsIn {A L B Lb : Subgroup G} {c b d : G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) ∈
      thetaComponentsIn (Subgroup.centralizer (B : Set G)) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  set C := Subgroup.centralizer (B : Set G) with hCdef
  have hJC : J ≤ C := residual_le_centralizer hc
  have hJN := centralizer_le_normalizer_residual h hc
  obtain ⟨-, hd1⟩ := hc.ne_one hB h.isE27
  obtain ⟨-, -, -, hJ2, hdL, S, hdS, hSd⟩ := hc
  let e : ↥(J.subgroupOf C) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  refine mem_thetaComponentsIn_iff.mpr ⟨hJC, ?_, ?_, ?_⟩
  · have := residual_isPerfect Lb d
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hJN).isSubnormal
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotThetaEquiv e.symm)
      (residual_inf_centralizer_quasisimple h415 hJ2 hdL hd1 ⟨S, hdS, hSd⟩)

theorem resProj_facts {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    ∃ hdL : d ∈ Lb,
      (resProj Lb d).range = Subgroup.centralizer
        {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb) ⟨d, hdL⟩} ∧
      IsQuasisimple (resProj Lb d).range ∧ Nat.card (Subgroup.center (resProj Lb d).range) = 3 ∧
      Group.IsPerfect (resProj Lb d).range ∧
      Sec4.IsTripleCover (resProj Lb d).range (alternatingGroup (Fin 6)) ∧
      Subgroup.center ↥(Subgroup.centralizer
          ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb) ⟨d, hdL⟩} : Set (↥Lb ⧸ _))) =
        (Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb) ⟨d, hdL⟩)).subgroupOf
          (Subgroup.centralizer
            ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb) ⟨d, hdL⟩} : Set (↥Lb ⧸ _))) := by
  have hJ := j2_of_isLBConfig hc
  obtain ⟨-, hd1⟩ := hc.ne_one hB h.isE27
  obtain ⟨hBbd, -, -, -, hdL, S, hdS, hSd⟩ := hc
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hd3 : d ^ 3 = 1 := h.toSec13Data.isElemAbelian.2 d hdA
  have hbc := exists_sylow_quot hdL ⟨S, hdS, hSd⟩
  set θ := aschbacherSolvableCore 3 ↥Lb
  set z := QuotientGroup.mk' θ ⟨d, hdL⟩ with hzdef
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hzdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd3))))
  obtain ⟨hq, hperf, htc, hcen⟩ := centralizer_facts hJ hz1 hbc
  have hrange := resProj_range hJ hdL hd1 hd3 hbc
  let e : ↥(resProj Lb d).range ≃* ↥(Subgroup.centralizer ({z} : Set (↥Lb ⧸ θ))) :=
    MulEquiv.subgroupCongr hrange
  refine ⟨hdL, hrange, CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    KFacts.KS14.isTripleCover_congr e.symm htc, hcen⟩
  calc Nat.card (Subgroup.center (resProj Lb d).range)
      = Nat.card (Subgroup.center ↥(Subgroup.centralizer ({z} : Set (↥Lb ⧸ θ)))) := by
        rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
    _ = 3 := htc.1

theorem exists_mem_not_mem_zpowers {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    ∃ a₀ ∈ A ⊓ Lb, a₀ ∉ Subgroup.zpowers d ∧ a₀ ∉ B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := sec14Std_of_isLBConfig h hc
  obtain ⟨hbL, h9, -⟩ := j2_point_facts hS.toSec13Data (j2_of_isLBConfig hc)
  obtain ⟨-, hd1⟩ := hc.ne_one hB h.isE27
  obtain ⟨hBbd, -, -, -, hdL, -⟩ := hc
  have hbB : b ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := hB.1 hdB
  have hd3 : orderOf d = 3 := orderOf_eq_prime (h.toSec13Data.isElemAbelian.2 d hdA) hd1
  have hzd : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd3]
  have hdAL : Subgroup.zpowers d ≤ A ⊓ Lb := Subgroup.zpowers_le.mpr ⟨hdA, hdL⟩
  have hlt : Subgroup.zpowers d < A ⊓ Lb := lt_of_le_of_ne hdAL fun heq => by
    have h' := congrArg (fun K : Subgroup G => Nat.card K) heq
    simp only [hzd, h9] at h'
    omega
  obtain ⟨a₀, ha₀, ha₀d⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨a₀, ha₀, ha₀d, fun ha₀B => ha₀d ?_⟩
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [h.isE27.2] at this
    omega
  have hBL : Nat.card (B ⊓ Lb : Subgroup G) ≤ 3 := by
    have hdvd : Nat.card (B ⊓ Lb : Subgroup G) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hB9]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases i
    · rw [hik]; norm_num
    · rw [hik]; norm_num
    · exfalso
      apply hbL
      have heqB : B ⊓ Lb = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hik, hB9]; norm_num)
      have hb' : b ∈ B ⊓ Lb := by rw [heqB]; exact hbB
      exact hb'.2
  have heq : Subgroup.zpowers d = B ⊓ Lb :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hdB, hdL⟩) (by rw [hzd]; exact hBL)
  exact heq ▸ (⟨ha₀B, ha₀.2⟩ : a₀ ∈ B ⊓ Lb)

theorem exists_commutator_not_mem {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {a₀ : G} (ha₀ : a₀ ∈ A ⊓ Lb)
    (ha₀d : a₀ ∉ Subgroup.zpowers d) :
    ∃ j ∈ inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)),
      ⁅j, a₀⁆ ∉ inSubgroup (aschbacherSolvableCore 3) Lb := by
  obtain ⟨hdL, hrange, -, -, -, -, hcen⟩ := resProj_facts h hB hc
  have hJA := inf_le_residual h hB hc
  have ha₀J := hJA ha₀
  by_contra hall
  push Not at hall
  set φ := resProj Lb d with hφ
  set a' : ↥(inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G))) :=
    ⟨a₀, ha₀J⟩ with ha'
  set θ := aschbacherSolvableCore 3 ↥Lb with hθ
  set z := QuotientGroup.mk' θ ⟨d, hdL⟩ with hz
  have hcomm : ∀ j, φ j * φ a' = φ a' * φ j := by
    intro j
    have hk : ⁅j, a'⁆ ∈ φ.ker := (mem_ker_resProj _).mpr (hall j j.2)
    rwa [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hk
  have hφa : φ a' ∈ Subgroup.centralizer ({z} : Set (↥Lb ⧸ θ)) :=
    hrange ▸ MonoidHom.mem_range.mpr ⟨a', rfl⟩
  have hcen' : (⟨φ a', hφa⟩ : ↥(Subgroup.centralizer ({z} : Set (↥Lb ⧸ θ)))) ∈
      Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨w, hw⟩
    rw [← hrange] at hw
    obtain ⟨j, rfl⟩ := hw
    exact Subtype.ext (hcomm j)
  rw [hcen, Subgroup.mem_subgroupOf] at hcen'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcen'
  have hk' : z ^ k = φ a' := hk
  have hθmem : (⟨a₀, ha₀.2⟩ : ↥Lb) * (⟨d, hdL⟩ : ↥Lb) ^ (-k) ∈ θ := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_zpow]
    change φ a' * z ^ (-k) = 1
    rw [← hk', ← zpow_add, add_neg_cancel, zpow_zero]
  have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have h3 : ((⟨a₀, ha₀.2⟩ : ↥Lb) * (⟨d, hdL⟩ : ↥Lb) ^ (-k)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using h.toSec13Data.isElemAbelian.2 _ (mul_mem ha₀.1 (zpow_mem hdA (-k)))
  have h1 := congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore hθmem h3)
  simp only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one] at h1
  apply ha₀d
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [mul_eq_one_iff_eq_inv, zpow_neg, inv_inv] at h1
  exact h1.symm

theorem residual_eq_of_isLBConfig {A L B Lb Lb' : Subgroup G} {c b d b' d' : G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hc' : IsLBConfig A B b' d' Lb') :
    inSubgroup perfectResidual (Lb' ⊓ Subgroup.centralizer ({d'} : Set G)) =
      inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  set J' := inSubgroup perfectResidual (Lb' ⊓ Subgroup.centralizer ({d'} : Set G)) with hJ'def
  set C := Subgroup.centralizer (B : Set G) with hCdef
  by_contra hne
  obtain ⟨hJC, hJm⟩ := mem_thetaComponentsIn_iff.mp (residual_mem_thetaComponentsIn h hB hc)
  obtain ⟨hJ'C, hJ'm⟩ := mem_thetaComponentsIn_iff.mp (residual_mem_thetaComponentsIn h hB hc')
  rw [← hJdef] at hJC hJm
  rw [← hJ'def] at hJ'C hJ'm
  have hneH : J.subgroupOf C ≠ J'.subgroupOf C := fun heq => hne (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hJC, ← Subgroup.map_subgroupOf_eq_of_le hJ'C, heq])
  have hcomm := commutator_le_of_mem_thetaComponents_of_ne hJm hJ'm hneH
  set Θ := (aschbacherSolvableCore 3 ↥C).map C.subtype with hΘdef
  have hcommG : ∀ j ∈ J, ∀ y ∈ J', ⁅j, y⁆ ∈ Θ := fun j hj y hy =>
    ⟨_, hcomm (Subgroup.commutator_mem_commutator
      (show (⟨j, hJC hj⟩ : ↥C) ∈ J.subgroupOf C from hj)
      (show (⟨y, hJ'C hy⟩ : ↥C) ∈ J'.subgroupOf C from hy)), rfl⟩
  obtain ⟨-, -, hq, hZ, -⟩ := resProj_facts h hB hc
  have hJN := centralizer_le_normalizer_residual h hc
  rw [← hJdef] at hJN
  have hCΘ : C ≤ Subgroup.normalizer (Θ : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map C _
        inferInstance)
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  have hMn : (Θ.subgroupOf J).Normal :=
    Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mpr
      (Late.le_normalizer_inf (hJC.trans hCΘ) Subgroup.le_normalizer)
  have hM3 : ¬ 3 ∣ Nat.card (Θ.subgroupOf J) := fun h3 => hθ3 (h3.trans (by
    rw [← Subgroup.card_map_of_injective J.subtype_injective, Subgroup.subgroupOf_map_subtype]
    refine (Subgroup.card_dvd_of_le inf_le_left).trans ?_
    rw [hΘdef, Subgroup.card_map_of_injective C.subtype_injective]))
  have hker := le_ker_of_normal (resProj Lb d) hq hZ hMn hM3
  have hΘ : ∀ x ∈ J, x ∈ Θ → x ∈ inSubgroup (aschbacherSolvableCore 3) Lb := fun x hxJ hxΘ =>
    (mem_ker_resProj ⟨x, hxJ⟩).mp (hker (Subgroup.mem_subgroupOf.mpr hxΘ))
  obtain ⟨a₀, ha₀, ha₀d, -⟩ := exists_mem_not_mem_zpowers h hB hc
  obtain ⟨j₀, hj₀J, hj₀⟩ := exists_commutator_not_mem h hB hc ha₀ ha₀d
  rw [← hJdef] at hj₀J
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => h.toSec13Data.commute hx hy
  have hAC : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAab y (hB.1 hy) x hx
  have hJ'A := inf_le_residual h hB hc'
  rw [← hJ'def] at hJ'A
  have hle : A ⊓ Lb' ≤ B := by
    intro y hy
    by_contra hyB
    have hAle : A ≤ Subgroup.zpowers y ⊔ B :=
      sup_comm B (Subgroup.zpowers y) ▸ le_sup_zpowers_of_not_mem h.isE27 hB hy.1 hyB
    have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (B : Set G) := by
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
      constructor
      · intro hx
        rw [hAab y hy.1 x (hB.1 hx), mul_inv_cancel_right]
        exact hx
      · intro hx
        have hx' : y * x * y⁻¹ ∈ A := hB.1 hx
        have e : x = y * x * y⁻¹ := by
          have := hAab y hy.1 x (by
            have : x = y⁻¹ * (y * x * y⁻¹) * y := by group
            rw [this]
            exact mul_mem (mul_mem (inv_mem hy.1) hx') hy.1)
          rw [this, mul_inv_cancel_right]
        rw [e]
        exact hx
    have ha₀' : a₀ ∈ ((Subgroup.zpowers y ⊔ B : Subgroup G) : Set G) := hAle ha₀.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hyN] at ha₀'
    obtain ⟨z, hz, β, hβ, hzβ⟩ := Set.mem_mul.mp ha₀'
    have hzA : z ∈ A := (Subgroup.zpowers_le.mpr hy.1) hz
    have hj₀β : β * j₀ = j₀ * β := Subgroup.mem_centralizer_iff.mp (hJC hj₀J) β hβ
    have hcz : ⁅j₀, a₀⁆ = ⁅j₀, z⁆ := by
      rw [← hzβ, commutatorElement_def, commutatorElement_def]
      have e : β * j₀⁻¹ = j₀⁻¹ * β := by
        calc β * j₀⁻¹ = j₀⁻¹ * (j₀ * β) * j₀⁻¹ := by group
          _ = j₀⁻¹ * (β * j₀) * j₀⁻¹ := by rw [hj₀β]
          _ = j₀⁻¹ * β := by group
      calc j₀ * (z * β) * j₀⁻¹ * (z * β)⁻¹ = j₀ * z * (β * j₀⁻¹) * β⁻¹ * z⁻¹ := by group
        _ = j₀ * z * (j₀⁻¹ * β) * β⁻¹ * z⁻¹ := by rw [e]
        _ = j₀ * z * j₀⁻¹ * z⁻¹ := by group
    have hzJ' : z ∈ J' := (Subgroup.zpowers_le.mpr (hJ'A hy)) hz
    have hzJ : ⁅j₀, z⁆ ∈ J := by
      rw [show ⁅j₀, z⁆ = j₀ * (z * j₀⁻¹ * z⁻¹) by rw [commutatorElement_def]; group]
      exact mul_mem hj₀J
        ((Subgroup.mem_normalizer_iff.mp (hJN (hAC hzA)) _).mp (inv_mem hj₀J))
    exact hj₀ (hcz ▸ hΘ _ hzJ (hcommG j₀ hj₀J z hzJ'))
  have hS' := sec14Std_of_isLBConfig h hc'
  obtain ⟨hb'L, h9', -⟩ := j2_point_facts hS'.toSec13Data (j2_of_isLBConfig hc')
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [h.isE27.2] at this
    omega
  have heq : A ⊓ Lb' = B := Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, h9'])
  have hb'B : b' ∈ B := hc'.1 ▸ Subgroup.subset_closure (Set.mem_insert b' {d'})
  have hb' : b' ∈ A ⊓ Lb' := by rw [heq]; exact hb'B
  exact hb'L hb'.2

theorem lB_eq_residual {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    lB A B = inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) :=
  lB_eq_of_unique hc fun _ _ _ hc' => residual_eq_of_isLBConfig h hB hc hc'

end Config




end CFSG.RankThree.PartTwo.Sec14.Item148HJ
