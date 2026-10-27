module

public import CFSG.RankThree.PartTwo.Sec17.N172Theta
public import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofKMd
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofGen
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
public import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
public import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolNumbers
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

@[expose] def Step166ThetaLdTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ b ∈ ({c * d, c * d ^ 2} : Set G),
    ∀ X ∈ thetaComponentsAt 3 b,
      X = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) X →
      CFSG.Open.pCoreOf 2 X = ⊥ → inSubgroup (aschbacherSolvableCore 3) X = ⊥

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem thetaSubgroupOf_sup_eq_top {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    J.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X = ⊤ := by
  apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJX]
  change J ⊔ inSubgroup (aschbacherSolvableCore 3) X = (⊤ : Subgroup ↥X).map X.subtype
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, ← hX]

private noncomputable def thetaQuotHom {J X : Subgroup G} (hJX : J ≤ X) :
    ↥J →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)).comp (Subgroup.inclusion hJX)

private theorem thetaQuotHom_surjective {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    Function.Surjective (thetaQuotHom hJX) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) q
  have hx : x ∈ J.subgroupOf X ⊔ aschbacherSolvableCore 3 ↥X := by
    rw [thetaSubgroupOf_sup_eq_top hJX hX]
    exact Subgroup.mem_top x
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
  have hincl : Subgroup.inclusion hJX ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩ = y :=
    Subtype.ext rfl
  show QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
      (Subgroup.inclusion hJX ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩) =
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x
  rw [hincl]
  have hzone : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) z = 1 :=
    (QuotientGroup.eq_one_iff z).mpr hz
  calc QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) y
      = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (y * z) := by
        rw [map_mul, hzone, mul_one]
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x := by rw [hyz]

private theorem thetaQuotHom_ker {J X : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    (thetaQuotHom hJX).ker = aschbacherSolvableCore 3 ↥J := by
  have hinf := inf_theta_eq_of_eq_sup hJX hX
  ext j
  rw [MonoidHom.mem_ker]
  constructor
  · intro hj
    have hjθ : Subgroup.inclusion hJX j ∈ aschbacherSolvableCore 3 ↥X :=
      (QuotientGroup.eq_one_iff _).mp hj
    have hjG : (j : G) ∈ J ⊓ inSubgroup (aschbacherSolvableCore 3) X :=
      ⟨j.2, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJX j, hjθ, rfl⟩⟩
    have hjJ : (j : G) ∈ inSubgroup (aschbacherSolvableCore 3) J := by
      rwa [hinf] at hjG
    obtain ⟨t, ht, htj⟩ := Subgroup.mem_map.mp hjJ
    have htj' : t = j := Subtype.ext htj
    rwa [htj'] at ht
  · intro hj
    have hjJ : (j : G) ∈ inSubgroup (aschbacherSolvableCore 3) J :=
      Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
    have hjG' : (j : G) ∈ J ⊓ inSubgroup (aschbacherSolvableCore 3) X := hinf ▸ hjJ
    have hjθ : Subgroup.inclusion hJX j ∈ aschbacherSolvableCore 3 ↥X :=
      (Subgroup.mem_map_iff_mem X.subtype_injective).mp hjG'.2
    exact (QuotientGroup.eq_one_iff _).mpr hjθ

theorem nonempty_thetaQuot_mulEquiv_of_eq_sup {J X₁ X₂ : Subgroup G} (h₁ : J ≤ X₁)
    (hX₁ : X₁ = J ⊔ inSubgroup (aschbacherSolvableCore 3) X₁) (h₂ : J ≤ X₂)
    (hX₂ : X₂ = J ⊔ inSubgroup (aschbacherSolvableCore 3) X₂) :
    Nonempty (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁ ≃*
      ↥X₂ ⧸ aschbacherSolvableCore 3 ↥X₂) := by
  let E₁ : (↥J ⧸ aschbacherSolvableCore 3 ↥J) ≃*
      (↥X₁ ⧸ aschbacherSolvableCore 3 ↥X₁) :=
    (QuotientGroup.quotientMulEquivOfEq (thetaQuotHom_ker h₁ hX₁).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (thetaQuotHom h₁)
        (thetaQuotHom_surjective h₁ hX₁))
  let E₂ : (↥J ⧸ aschbacherSolvableCore 3 ↥J) ≃*
      (↥X₂ ⧸ aschbacherSolvableCore 3 ↥X₂) :=
    (QuotientGroup.quotientMulEquivOfEq (thetaQuotHom_ker h₂ hX₂).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (thetaQuotHom h₂)
        (thetaQuotHom_surjective h₂ hX₂))
  exact ⟨E₁.symm.trans E₂⟩

private lemma mem_of_pow_mem {d : G} (hd3 : d ^ 3 = 1) {k : ℕ} (hk : k = 1 ∨ k = 2)
    {H : Subgroup G} (h : d ^ k ∈ H) : d ∈ H := by
  rcases hk with rfl | rfl
  · simpa using h
  · have h4 : (d ^ 2) ^ 2 = d := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hd3, one_mul]
    simpa [h4] using Subgroup.pow_mem H h 2

theorem mem_ld_of_threeCentral (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    d ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨hdL, S, hdS, hSd⟩ := id hdc
  have hd3 : d ^ 3 = 1 := h.toSec14Std.isE27.1.2 d hdA
  exact Sec13.mem_residual_of_pow_three h415 hJ hdL hd1 ⟨S, hdS, hSd⟩ hdL
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) (k := 1) (by simpa using hd3)

theorem isLBConfig_closure_cd_of_threeCentral (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdc : IsThreeCentralIn L d) :
    IsLBConfig A (Subgroup.closure {c, d}) c d L := by
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hc1 : c ≠ 1 := hD13.ne_one
  have hLtop : L ≠ ⊤ := by
    intro htop
    exact Sec14.centralizer_singleton_ne_top hD13.isSimpleGroup hD13.nonabelian hc1
      (top_le_iff.mp (htop ▸ hD13.le_centralizer))
  have hperfL : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt hD13.mem_lA.1
  have hJ2L : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    Sec12.gap128OTwoHJ ↥L (hD13.toTheoremFourHyp.sectionFourHyp hLtop) hperfL hJ
  exact ⟨rfl, hD13.zpowers_mem_omegaA, Sec14.lA_eq_singleton_of_j2_point hD13 hJ, hJ2L, hdc⟩

private lemma lB_closure_eq_ld_of_threeCentral (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    lB A (Subgroup.closure {c, d}) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hc3 : orderOf c = 3 := hD13.orderOf_eq
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts hD13 hJ
  obtain ⟨hdL, -⟩ := id hdc
  have hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    isLBConfig_closure_cd_of_threeCentral h hJ hdc
  have hLdle : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      lB A (Subgroup.closure {c, d}) := by
    unfold lB
    exact le_iSup_of_le c (le_iSup_of_le d (le_iSup_of_le L (le_iSup_of_le hcfg le_rfl)))
  have hmem := mem_ld_of_threeCentral h hJ hdA hd1 hdc
  have hLD : lB A (Subgroup.closure {c, d}) ≠ ⊥ := by
    intro hbot
    have hbot' : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ ⊥ :=
      hbot ▸ hLdle
    exact hd1 (by simpa using hbot' hmem)
  exact lB_closure_eq_ld h hΩ hcL hdA hdL hd1 hLD

theorem isHyperplane_closure_cd (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    IsHyperplane A (Subgroup.closure {c, d}) := by
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := hD13.mem_A
  have hc1 : c ≠ 1 := hD13.ne_one
  have hc3 : orderOf c = 3 := hD13.orderOf_eq
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts hD13 hJ
  obtain ⟨hdL, -⟩ := id hdc
  have hd_c : d ∉ Subgroup.zpowers c := by
    intro hdz
    have hmem : d ∈ L ⊓ Subgroup.zpowers c := ⟨hdL, hdz⟩
    rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcL,
      Subgroup.mem_bot] at hmem
    exact hd1 hmem
  exact isHyperplane_closure_pair hA hcA hdA hc1 hd_c

lemma closure_pair_cd_pow {c d : G} (hd3 : d ^ 3 = 1)
    {k : ℕ} (hk : k = 1 ∨ k = 2) :
    Subgroup.closure {c * d ^ k, c} = Subgroup.closure {c, d} := by
  have hc : c ∈ Subgroup.closure ({c * d ^ k, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem (c * d ^ k) (Set.mem_singleton c))
  have hb : c * d ^ k ∈ Subgroup.closure ({c * d ^ k, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert (c * d ^ k) (Set.singleton c))
  have hdk : d ^ k ∈ Subgroup.closure ({c * d ^ k, c} : Set G) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hb
    have heq : c⁻¹ * (c * d ^ k) = d ^ k := by group
    simpa [heq] using h
  have hd_mem : d ∈ Subgroup.closure ({c * d ^ k, c} : Set G) :=
    mem_of_pow_mem hd3 hk hdk
  have hcD : c ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert c (Set.singleton d))
  have hdD : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  apply le_antisymm
  · refine (Subgroup.closure_le (Subgroup.closure {c, d})).mpr ?_
    intro w hw
    rcases Set.mem_insert_iff.mp hw with hw' | hw'
    · rw [hw']
      exact Subgroup.mul_mem _ hcD (Subgroup.pow_mem _ hdD k)
    · rw [Set.mem_singleton_iff.mp hw']
      exact hcD
  · refine (Subgroup.closure_le (Subgroup.closure {c * d ^ k, c})).mpr ?_
    intro w hw
    rcases Set.mem_insert_iff.mp hw with hw' | hw'
    · rw [hw']
      exact Subgroup.subset_closure (Set.mem_insert_of_mem (c * d ^ k) (Set.mem_singleton c))
    · rw [Set.mem_singleton_iff.mp hw']
      exact hd_mem

lemma b_facts (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    c * d ^ k ∈ A ∧ c * d ^ k ≠ 1 ∧ c * d ^ k ∉ Subgroup.zpowers c ∧
      Subgroup.zpowers (c * d ^ k) ∉ omegaA A ∧
      c * d ^ k ∈ Subgroup.closure {c, d} := by
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := hD13.mem_A
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts hD13 hJ
  obtain ⟨hdL, -⟩ := id hdc
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hbA : c * d ^ k ∈ A := A.mul_mem hcA (A.pow_mem hdA k)
  have hb1 : c * d ^ k ≠ 1 := by
    intro hh
    have hc : c = (d ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hh
    exact hcL (by rw [hc]; exact L.inv_mem (L.pow_mem hdL k))
  have hbc : c * d ^ k ∉ Subgroup.zpowers c := by
    intro hbzp
    have hdk : d ^ k ∈ Subgroup.zpowers c := by
      have h1 : c⁻¹ * (c * d ^ k) ∈ Subgroup.zpowers c :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) hbzp
      have h2 : c⁻¹ * (c * d ^ k) = d ^ k := by group
      rwa [h2] at h1
    have hd_mem : d ∈ Subgroup.zpowers c := mem_of_pow_mem hd3 hk hdk
    have hmem : d ∈ L ⊓ Subgroup.zpowers c := ⟨hdL, hd_mem⟩
    rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD13.orderOf_eq hcL,
      Subgroup.mem_bot] at hmem
    exact hd1 hmem
  have hbΩ : Subgroup.zpowers (c * d ^ k) ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    intro hz
    exact hbc (hz ▸ Subgroup.mem_zpowers (c * d ^ k))
  have hbD : c * d ^ k ∈ Subgroup.closure {c, d} :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert c (Set.singleton d)))
      (Subgroup.pow_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem c (Set.mem_singleton d))) k)
  exact ⟨hbA, hb1, hbc, hbΩ, hbD⟩

private lemma false_of_delta_eq_pPrimeCoreOf (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d b : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    (hbA : b ∈ A) (hbD : b ∈ Subgroup.closure {c, d})
    (hΔ1 : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hLdEq : lB A (Subgroup.closure {c, d}) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))
    (h3Ld : 3 ∣ Nat.card
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))) : False := by
  have hD := isHyperplane_closure_cd h hJ hdA hd1 hdc
  have hcfg := isLBConfig_closure_cd_of_threeCentral h hJ hdc
  have hLBΔ : lB A (Subgroup.closure {c, d}) ≤
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) :=
    Desc143X.lB_le_delta h.toSec14Std hD hcfg hbD
  have hO3 : IsPiSubgroup (piCompl 3)
      (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
  have hU3 : IsPiSubgroup (piCompl 3)
      (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
  have hUNO : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA))).trans
        (le_normalizer_pPrimeCoreOf 3 _)
  have hOU3 : IsPiSubgroup (piCompl 3)
      (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
    (by rw [sup_comm]; exact isPiSubgroup_piCompl_sup hU3 hO3 hUNO)
  have h3lB : 3 ∣ Nat.card (lB A (Subgroup.closure {c, d})) := by
    rw [hLdEq]
    exact h3Ld
  have hle : lB A (Subgroup.closure {c, d}) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    rw [hΔ1] at hLBΔ
    exact hLBΔ
  exact absurd (h3lB.trans (Subgroup.card_dvd_of_le hle))
    ((isPiSubgroup_piCompl_iff Nat.prime_three _).mp hOU3)

private lemma false_of_zpowers_eq_at_cd {d d' : G} {k : ℕ} (hdL : d ∈ L) (hcL : c ∉ L)
    (hd'L : d' ∈ L) (heq : Subgroup.zpowers (c * d ^ k) = Subgroup.zpowers d') : False := by
  have hbL : c * d ^ k ∈ L := by
    have hbzp : c * d ^ k ∈ Subgroup.zpowers d' := by
      rw [← heq]
      exact Subgroup.mem_zpowers (c * d ^ k)
    exact Subgroup.zpowers_le.mpr hd'L hbzp
  have hc_eq : c = (c * d ^ k) * (d ^ k)⁻¹ := by group
  have hcL' : c ∈ L := by
    rw [hc_eq]
    exact L.mul_mem hbL (L.inv_mem (L.pow_mem hdL k))
  exact hcL hcL'

private lemma exists_Kd_data (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h134 : Item134) (h48 : Sec4.Item4_8) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) :
    ∃ Kd : Subgroup G,
      Kd ∈ thetaComponentsAt 3 d ∧
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Kd ∧
      Kd = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
        inSubgroup (aschbacherSolvableCore 3) Kd ∧
      lB A (Subgroup.closure {c, d}) =
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      3 ∣ Nat.card
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ∧
      3 ∣ Nat.card L := by
  obtain ⟨Kd, hKd, hLdKd, hKdeq, hKdc⟩ :=
    exists_component_at_d h134 h48 h hΩ hJ hdA hd1 hdc
  have hLdEq : lB A (Subgroup.closure {c, d}) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    lB_closure_eq_ld_of_threeCentral h hΩ hJ hdA hd1 hdc
  set Ld : Subgroup G :=
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hLddef
  have hsup : Ld = Ld ⊔ inSubgroup (aschbacherSolvableCore 3) Ld :=
    (sup_eq_left.mpr (Subgroup.map_subtype_le _)).symm
  have hcard := card_center_theta_quot_eq_of_eq_sup (J := Ld) (X₁ := Ld) (X₂ := Kd)
    le_rfl hsup hLdKd hKdeq
  have hcenter : Nat.card (Subgroup.center (↥Ld ⧸ aschbacherSolvableCore 3 ↥Ld)) = 3 := by
    rw [hcard]
    exact hKdc
  have hdvd : 3 ∣ Nat.card (Subgroup.center (↥Ld ⧸ aschbacherSolvableCore 3 ↥Ld)) := by
    simpa [hcenter] using dvd_refl 3
  have h3Ld : 3 ∣ Nat.card Ld :=
    hdvd.trans ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))
  obtain ⟨-, h9, -⟩ := Sec14.j2_point_facts h.toSec13Data hJ
  have h3L : 3 ∣ Nat.card L := by
    have hdvd' : Nat.card (A ⊓ L : Subgroup G) ∣ Nat.card L :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [h9] at hdvd'
    exact dvd_trans (by norm_num) hdvd'
  exact ⟨Kd, hKd, hLdKd, hKdeq, hLdEq, h3Ld, h3L⟩

private lemma isTripleCover_thetaQuot_at_cd (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h134 : Item134) (hΩ : omegaA A = {Subgroup.zpowers c}) {d : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d)
    (hLdEq : lB A (Subgroup.closure {c, d}) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))
    {k : ℕ} {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 (c * d ^ k))
    (hXL : X = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) X)
    {Kd : Subgroup G} (hKd : Kd ∈ thetaComponentsAt 3 d)
    (hLdKd : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Kd)
    (hKdeq : Kd = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) Kd) :
    Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hD13 : Sec13Data G A c L := h.toSec13Data
  obtain ⟨hdL, S, hdS, hSd⟩ := id hdc
  have hmemLd : d ∈
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    mem_ld_of_threeCentral h hJ hdA hd1 hdc
  have hXeq : X = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) X := by
    rw [← hLdEq]
    exact hXL
  have hLd_le_X : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ X := by
    rw [hXeq]
    exact le_sup_left
  obtain ⟨-, -, hθ3L, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hS' := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3L hJ hdL hd1 S hdS hSd
  have hA6K : Sec4.IsTripleCover (↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd)
      (alternatingGroup (Fin 6)) := by
    rcases h134 G A c L hD13 hJ d hdA hd1 ⟨_, hS'⟩ Kd hKd hLdKd with
      ⟨-, hA6, -⟩ | ⟨-, hA6, -⟩ | ⟨-, -, -, h12⟩
    · exact hA6
    · exact hA6
    · exfalso
      rw [hΩ, Set.ncard_singleton] at h12
      omega
  have hiso : Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃*
      ↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd) :=
    nonempty_thetaQuot_mulEquiv_of_eq_sup hLd_le_X hXeq hLdKd hKdeq
  exact KFacts.KS14.isTripleCover_congr hiso.some.symm hA6K

theorem exists_thetaComponent_at_cd (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h143 : Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    ∃ X ∈ thetaComponentsAt 3 (c * d ^ k),
      delta A (lB A) (Subgroup.centralizer ({c * d ^ k} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({c * d ^ k} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X ∧
      X = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
      Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) := by
  classical
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Proof17Res10.omegaA_eq_of_j2 h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h)
      hD13.zpowers_mem_omegaA hD13.mem_lA hJ
  obtain ⟨hcL, -, -⟩ := Sec14.j2_point_facts hD13 hJ
  obtain ⟨hdL, -⟩ := id hdc
  obtain ⟨Kd, hKd, hLdKd, hKdeq, hLdEq, h3Ld, h3L⟩ :=
    exists_Kd_data h hΩ hJ h134 h48 hdA hd1 hdc
  obtain ⟨hbA, hb1, -, hbΩ, hbD⟩ := b_facts h hJ hΩ hdA hd1 hdc hk
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({c * d ^ k} : Set G))) A (piCompl 3)
  obtain ⟨-, hcase⟩ := h143 G A c L h.toSec14Std (c * d ^ k) hbA hb1 hbΩ Q hQ
  rcases hcase with hΔ1 | ⟨b', d', Lb', hb'Ω, hLb', -, -, -, hd'c, -, X, hΔX, -, hcase2⟩
  · exact (false_of_delta_eq_pPrimeCoreOf h hJ hdA hd1 hdc hbA hbD hΔ1 hLdEq h3Ld).elim
  · have hb'c : Subgroup.zpowers b' = Subgroup.zpowers c := by
      rw [hΩ] at hb'Ω
      exact hb'Ω
    rcases hcase2 with ⟨hXθ, hXeq, -⟩ | ⟨heq, -, -⟩
    · have hclos : Subgroup.closure {c * d ^ k, b'} = Subgroup.closure {c, d} :=
        (Item1119Sym.closure_pair_eq_of_zpowers_eq (c * d ^ k) b' c hb'c).trans
          (closure_pair_cd_pow (hA.1.2 d hdA) hk)
      have hXL : X = lB A (Subgroup.closure {c, d}) ⊔
          inSubgroup (aschbacherSolvableCore 3) X := by
        rw [← hclos]
        exact hXeq
      exact ⟨X, hXθ, hΔX, hXL, isTripleCover_thetaQuot_at_cd h hJ h134 hΩ hdA hd1 hdc
        hLdEq hXθ hXL hKd hLdKd hKdeq⟩
    · obtain ⟨hd'L, -⟩ := id hd'c
      have hLb'L : Lb' = L :=
        Proof1515.eq_of_mem_lA_of_zpowers_eq h.toSec14Std h3L hb'c hLb'
      have hd'L' : d' ∈ L := by rwa [hLb'L] at hd'L
      exact (false_of_zpowers_eq_at_cd hdL hcL hd'L' heq).elim

lemma inf_centralizer_le_delta {P : Subgroup G} {b : G}
    (hPQ : P ∈ scriptQ A (lB A)) (hbA : b ∈ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    P ⊓ Subgroup.centralizer ({b} : Set G) ≤
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := by
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := (mem_scriptQ_iff.mp hPQ).2.1
  have hAQ : A ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact hAP
    · intro x hx
      exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm x hx b hbA))
  exact le_delta (mem_scriptQ_of_le hPQ inf_le_left hAQ) inf_le_right

end CFSG.RankThree.PartTwo.Sec16.Ctr166
