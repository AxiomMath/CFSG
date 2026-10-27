module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.Sporadic.ON
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item14J2
public import CFSG.RankThree.PartTwo.Sec15.Item1523Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof15Res11

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem map_residual_eq_centralizer
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L)
    (hdc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)}) :
    ((inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))).subgroupOf L).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have hd3 : d ^ 3 = 1 := h.toSec13Data.isElemAbelian.2 d hdA
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set C := Subgroup.centralizer ({π ⟨d, hdL⟩} : Set (↥L ⧸ θ)) with hC
  have h1 : ((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map π = C := by
    rw [Proof15Res7.map_inf_centralizer_eq_inf le_rfl (Subgroup.le_normalizer hdL) hdL hd3,
      Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective θ), top_inf_eq]
  have hzc := Item148HJ.exists_sylow_quot hdL hdc
  have hz1 : π ⟨d, hdL⟩ ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd3))))
  have htop : perfectResidual ↥C = ⊤ :=
    KFacts.KS14.Native.j2_perfectResidual_centralizer_eq_top hJ hz1 hzc
  rw [Proof15Res7.map_inSubgroup_perfectResidual_subgroupOf inf_le_left, h1, inSubgroup, htop,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem isLBConfig_of
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdZ : IsZCentral L d) : IsLBConfig A (Subgroup.closure {c, d}) c d L := by
  have hD := h.toSec13Data
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hD.le_centralizer))
  have hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
  exact ⟨rfl, hD.zpowers_mem_omegaA, lA_eq_singleton_of_j2_point hD hJ, hJ2,
    Proof15Res7.exists_sylow_of_isZCentral hdZ⟩

theorem isHyperplane_of
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdL : d ∈ L) :
    IsHyperplane A (Subgroup.closure {c, d}) := by
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcL : c ∉ L := (j2_point_facts hD hJ).1
  refine Main148.isHyperplane_closure_pair148 hA hD.mem_A hdA hD.ne_one fun hdc => ?_
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
  have heq : Subgroup.zpowers d = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hd3, hD.orderOf_eq])
  exact hcL ((Subgroup.zpowers_le.mpr hdL) (heq ▸ Subgroup.mem_zpowers c))

theorem residual_le_k1523
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ k1523 A d := by
  have hD := h.toSec13Data
  have hS := h.toSec14Std
  set X₀ := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hX₀
  obtain ⟨hdL, S3, hdS, hSd⟩ := Proof15Res7.exists_sylow_of_isZCentral hdZ
  have hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set G) := by
    have hAC : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) := fun a ha =>
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hdA))
    exact (Late.le_normalizer_inf hD.le_normalizer hAC).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _)
  have hΔ := Proof15Res7.le_delta_of_map_eq_centralizer hS hJ hdA hd1 hdL ⟨S3, hdS, hSd⟩
    (Item148HJ.residual_le L d) hAX₀ (map_residual_eq_centralizer hS hJ hdA hd1 hdL ⟨S3, hdS, hSd⟩)
  have hX₀Δ : X₀ ≤ delta A (lB A) (Subgroup.centralizer ({d} : Set G)) :=
    hΔ.trans (delta_mono (Item148HJ.residual_le_centralizer_singleton L d))
  have hX₀3 : X₀ = oPrimeResidualOf 3 X₀ := Sec17.Proof171Steps.residual_eq_oPrimeResidualOf hS
    (isHyperplane_of h hJ hdA hd1 hdL) (isLBConfig_of h hJ hdZ)
  rw [hX₀3]
  exact Sec17.Proof171Steps.oPrimeResidualOf_mono_three hX₀Δ

omit [Finite G] in
theorem not_eightyOne_dvd_of_typeA6 [Finite G] {K' : Subgroup G}
    (h : Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6))) :
    ¬ 81 ∣ Nat.card K' := by
  intro h81
  have hθ3 := (solvable_prime_complement_core_characterization (H := ↥K') Nat.prime_three).2.2.1
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥K')
  rw [card_of_isTripleCover_a6 h] at hcard
  rw [hcard] at h81
  have hcop : Nat.Coprime 81 (Nat.card (aschbacherSolvableCore 3 ↥K')) :=
    Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
  have := hcop.dvd_of_dvd_mul_right h81
  norm_num at this

theorem false_of_typeA6 {d : G} {K' : Subgroup G}
    (hK' : K' ∈ thetaComponentsAt 3 d)
    (hK'A6 : Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6)))
    {A : Subgroup G} (htype : Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
      CFSG.Blueprint.NativeSporadic.ON)
    {X₀ : Subgroup G} (hX₀K' : X₀ ≤ K') (hX₀K : X₀ ≤ k1523 A d) (hX₀p : Group.IsPerfect ↥X₀)
    (hdX₀ : d ∈ X₀) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set K := k1523 A d with hKdef
  have hKC : K ≤ C := (oPrimeResidualOf_le_self 3 _).trans (delta_le _)
  obtain ⟨K'', hK''θ, rfl⟩ := hK'
  have hK''sn : K''.IsSubnormal := hK''θ.2.1
  set incl : ↥K →* ↥C := Subgroup.inclusion hKC with hincl
  set N₀ : Subgroup ↥K := K''.comap incl with hN₀
  have hN₀sn : N₀.IsSubnormal := hK''sn.comap incl
  obtain ⟨-, ⟨φ⟩⟩ := htype
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hρ
  set Γ := ↥K ⧸ CFSG.pCore 2 ↥K with hΓ
  set ζ := QuotientGroup.mk' (Subgroup.center Γ) with hζ
  set ψ : ↥K →* CFSG.Blueprint.NativeSporadic.ON := φ.toMonoidHom.comp (ζ.comp ρ) with hψ
  have hψs : Function.Surjective ψ :=
    φ.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  obtain ⟨-, -, hON⟩ := CFSG.Sporadic.ON.fam_on_simplicity
  have hX₀N₀ : X₀.subgroupOf K ≤ N₀ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hX₀K' hx
    change incl x ∈ K''
    have : incl x = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  rcases (hN₀sn.map hψs).eq_bot_or_top_of_isSimpleGroup hON with hbot | htop
  ·
    have hX₀ker : X₀.subgroupOf K ≤ ψ.ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact le_bot_iff.mp (hbot ▸ Subgroup.map_mono hX₀N₀)
    have hcen : (X₀.subgroupOf K).map ρ ≤ Subgroup.center Γ := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : ψ x = 1 := hX₀ker hx
      rw [hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ φ.injective, hζ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hperf : Group.IsPerfect ↥((X₀.subgroupOf K).map ρ) := by
      have : Group.IsPerfect ↥(X₀.subgroupOf K) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hX₀K).symm.toMonoidHom)
          (MulEquiv.surjective _)
      exact Group.IsPerfect.map ρ
    have hcomm : IsMulCommutative ↥((X₀.subgroupOf K).map ρ) := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have hb := Subgroup.mem_center_iff.mp (hcen b.2) (a : Γ)
      exact hb
    have hbot' : (X₀.subgroupOf K).map ρ = ⊥ := by
      have : Subsingleton ↥((X₀.subgroupOf K).map ρ) :=
        Group.IsPerfect.subsingleton_of_isMulCommutative
      exact Subgroup.eq_bot_of_subsingleton _
    have hdK : (⟨d, hX₀K hdX₀⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      have hm : ρ ⟨d, hX₀K hdX₀⟩ ∈ (X₀.subgroupOf K).map ρ :=
        Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hdX₀)
      rw [hbot', Subgroup.mem_bot, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
      exact hm
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hdK⟩
    have hdk : d ^ (2 ^ k) = 1 := by
      have := congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => ((x : ↥K) : G)) hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have hord : orderOf d = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdk)
        (orderOf_dvd_of_pow_eq_one hd3))
    exact hd1 (orderOf_eq_one_iff.mp hord)
  ·
    have h1 : Nat.card CFSG.Blueprint.NativeSporadic.ON ∣ Nat.card N₀ := by
      have := Subgroup.card_map_dvd N₀ ψ
      rwa [htop, Subgroup.card_top] at this
    have h2 : Nat.card N₀ ∣ Nat.card K'' := by
      have hle : N₀.map incl ≤ K'' := Subgroup.map_comap_le _ _
      have := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKC)] at this
    have h3 : Nat.card K'' = Nat.card (K''.map C.subtype) :=
      (Subgroup.card_map_of_injective C.subtype_injective).symm
    have h81 : 81 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
      rw [CFSG.Sporadic.ON.card_ON]
      norm_num
    exact not_eightyOne_dvd_of_typeA6 hK'A6 (h3 ▸ h81.trans (h1.trans h2))

theorem omega_of_ncard_twelve (hA : Late.IsE27 A) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdΩ : Subgroup.zpowers d ∉ omegaA A) (h12 : (omegaA A).ncard = 12) :
    ∀ b ∈ A, b ∉ Subgroup.zpowers d → Subgroup.zpowers b ∈ omegaA A := by
  classical
  intro b hbA hbd
  by_contra hno
  have hb1 : b ≠ 1 := fun h1 => hbd (h1 ▸ Subgroup.one_mem _)
  have hdb : d ∉ Subgroup.zpowers b := Proof152ResW.not_mem_zpowers_symm hA hd1 hbA hbd
  set F := Subgroup.zpowers b with hF
  set D := Subgroup.zpowers d with hD
  set E := F ⊔ D with hE
  have hE9 : Nat.card E = 9 := Proof152ResW.card_sup_eq_nine hA hbA hb1 hdA hd1 hdb
  have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr hdA)
  obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, a ∉ E := by
    by_contra h'
    push Not at h'
    have h1 := Subgroup.card_le_of_le (show A ≤ E from h')
    rw [hA.2, hE9] at h1
    omega
  have hAa := Proof152ResW.eq_sup_of_not_mem hA hbA hb1 hdA hd1 hdb haA haE
  have hpA : (Sec13.pointsOff A E).ncard = 9 := Sec13.ncard_pointsOff hA.1 haA hAa haE hE9
  have hpE : (Sec13.pointsOff E D).ncard = 3 :=
    Holds134.ncard_pointsOff_zpowers hA.1 hdA hd1 hbA hbd
  have hmemE : F ∈ Sec13.pointsOff E D := by
    have h := (Sec13.mem_pointsOff_iff (Proof152ResW.isElemAbelian_sup hA hbA hdA)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)) rfl hbd).mpr ⟨1, Subgroup.one_mem _, rfl⟩
    rwa [mul_one] at h
  have hd3 : Nat.card D = 3 := Sec13.card_zpowers_of_pow_three (hA.1.2 d hdA) hd1
  have hsub : omegaA A ⊆ Sec13.pointsOff A E ∪ (Sec13.pointsOff E D \ {F}) := by
    intro F' hF'
    obtain ⟨hF'A, hF'3, -⟩ := mem_omegaA_iff.mp hF'
    by_cases hF'E : F' ≤ E
    · right
      refine ⟨⟨hF'E, hF'3, fun hle => ?_⟩, fun h' => hno (h' ▸ hF')⟩
      have hF'D : F' = D := Subgroup.eq_of_le_of_card_ge hle (by rw [hF'3, hd3])
      exact hdΩ (hF'D ▸ hF')
    · left
      exact ⟨hF'A, hF'3, hF'E⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (Sec13.pointsOff A E) (Sec13.pointsOff E D \ {F})
  have h3 := Set.ncard_sdiff_singleton_of_mem hmemE
  rw [hpE] at h3
  omega

theorem onType_facts
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    (htype : Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
      CFSG.Blueprint.NativeSporadic.ON) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
      (omegaA A).ncard = 12 ∧
      ∀ b ∈ A, b ∉ Subgroup.zpowers d → Subgroup.zpowers b ∈ omegaA A ∧
        ∃ w ∈ Subgroup.normalizer (A : Set G),
          Subgroup.zpowers b = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA := hD.mem_A
  have hc1 := hD.ne_one
  have hcL : c ∉ L := (j2_point_facts hD hJ).1
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  obtain ⟨hdL, S3, hdS, hSd⟩ := hdc
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hdZ : IsZCentral L d := by
    obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S3 hdS hSd
    exact ⟨_, hSy, hZ⟩
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL (Subgroup.zpowers_le.mpr hdL h)
  have hdc' : d ∉ Subgroup.zpowers c := Proof152ResW.not_mem_zpowers_symm hA hd1 hcA hcd
  set X₀ := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hX₀
  have hX₀K : X₀ ≤ k1523 A d := residual_le_k1523 h hJ hdA hd1 hdZ
  have hX₀p : Group.IsPerfect ↥X₀ := Item148HJ.residual_isPerfect L d
  have hdX₀ : d ∈ X₀ := Item148HJ.inf_le_residual h.toSec14Std (isHyperplane_of h hJ hdA hd1 hdL)
    (isLBConfig_of h hJ hdZ) ⟨hdA, hdL⟩
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hD.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S3, hdS, hSd⟩
  obtain ⟨K', hK', hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hD.mem_lA.1 hJq
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K' hK' hJK with
    ⟨-, hK'A6, -⟩ | ⟨-, hK'A6, -⟩ | ⟨-, hWd, hΩ', h12⟩
  · exact (false_of_typeA6 hK' hK'A6 htype hJK hX₀K hX₀p hdX₀ hd3 hd1).elim
  · exact (false_of_typeA6 hK' hK'A6 htype hJK hX₀K hX₀p hdX₀ hd3 hd1).elim
  · obtain ⟨hdΩ, -⟩ := Proof152ResW.omegaA_facts_of_case3 hA hcA hc1 hdA hd1 hdc' hWd hΩ' h12
    refine ⟨hWd, h12, fun b hbA hbd => ?_⟩
    have hbΩ := omega_of_ncard_twelve hA hdA hd1 hdΩ h12 b hbA hbd
    refine ⟨hbΩ, ?_⟩
    rw [hΩ'] at hbΩ
    obtain ⟨w, hw, hwb⟩ := hbΩ
    exact ⟨w, hw, hwb⟩

theorem omega_of_onType
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    (htype : Sec4.IsTripleCover (↥(k1523 A d) ⧸ CFSG.pCore 2 ↥(k1523 A d))
      CFSG.Blueprint.NativeSporadic.ON) :
    ∀ b ∈ A, b ∉ Subgroup.zpowers d → Subgroup.zpowers b ∈ omegaA A := fun b hbA hbd =>
  ((onType_facts h134 h48 h hJ hdA hd1 hdc htype).2.2 b hbA hbd).1

end Proof15Res11

open Proof15Res11

end CFSG.RankThree.PartTwo.Sec15
