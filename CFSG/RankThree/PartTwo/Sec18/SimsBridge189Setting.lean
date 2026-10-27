module

public import CFSG.RankThree.PartTwo.Sec18.Item189Glue
public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2
import CFSG.RankThree.PartTwo.Sec18.Item189KType
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofTools
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev kSK189 (M H : Subgroup G) (c : G) : Subgroup ↥(sk189 M H c) :=
  (normalClosureIn M c).subgroupOf (sk189 M H c)

noncomputable abbrev sSK189 (M H : Subgroup G) (c : G) : Subgroup ↥(sk189 M H c) :=
  (s189 M H).subgroupOf (sk189 M H c)

omit [Finite G] in
theorem mem_sk189_self (M H : Subgroup G) (c : G) : c ∈ sk189 M H c :=
  (le_sup_right : normalClosureIn M c ≤ sk189 M H c) (Sec20.self_mem_normalClosureIn M c)

noncomputable abbrev cSK189 (M H : Subgroup G) (c : G) : ↥(sk189 M H c) :=
  ⟨c, mem_sk189_self M H c⟩

variable {A M H : Subgroup G} {c : G}

theorem pCoreOf_le_s189_of189 (hmax : s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (h : Sec18H G A M H c) : CFSG.Open.pCoreOf 2 M ≤ s189 M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 M
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hPS : IsPGroup 2 ↥(s189 M H ⊔ P) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_s189 M H)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ((s189_le M H).trans hMP)
  have hAN : A ≤ Subgroup.normalizer ((s189 M H ⊔ P : Subgroup G) : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨le_normalizer_s189 h ha, hMP (sec18Std_le h.toSec18Std ha)⟩
  have hmem : s189 M H ⊔ P ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hPS, hAN⟩
  have heq := (mem_maxInvariantPiSubgroups_iff.mp hmax).2 _ hmem le_sup_left
  rw [← heq]
  exact le_sup_right

theorem aschbacherSolvableCore_eq_pCore_of_pPrimeCore_eq {Y : Type*} [Group Y] [Finite Y]
    (hY : CFSG.pPrimeCore 3 Y = CFSG.pCore 2 Y) : aschbacherSolvableCore 3 Y = CFSG.pCore 2 Y := by
  obtain ⟨-, -, h3, -, -, -, hr⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  refine le_antisymm ?_ (hr 2 Nat.prime_two (by norm_num))
  rw [← hY]
  exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩

private theorem isPGroup_quotient_of_sup_eq_top189 {X : Type*} [Group X] {Kb Sb : Subgroup X}
    [Kb.Normal] (hsup : Kb ⊔ Sb = ⊤) (hS : IsPGroup 2 Sb) : IsPGroup 2 (X ⧸ Kb) := by
  refine hS.of_surjective ((QuotientGroup.mk' Kb).comp Sb.subtype) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Kb q
  have hx : x ∈ ((Kb ⊔ Sb : Subgroup X) : Set X) := by rw [hsup]; trivial
  rw [Subgroup.normal_mul] at hx
  obtain ⟨k, hk, s, hs, rfl⟩ := hx
  refine ⟨⟨s, hs⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  have := (inferInstance : Kb.Normal).conj_mem k hk s⁻¹
  simpa [mul_assoc] using this

theorem pPrimeCore_sk189_eq_of
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := normalClosureIn M c
  set SK := sk189 M H c
  set P := CFSG.pPrimeCore 3 ↥SK
  have hKSK : K ≤ SK := le_sup_right
  have hKn : (K.subgroupOf SK).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKSK).mpr (sk189_le_normalizer_k M H c)
  have hsup : K.subgroupOf SK ⊔ (s189 M H).subgroupOf SK = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKSK le_sup_left, sup_comm, Subgroup.subgroupOf_self]
  have hQ2 : IsPGroup 2 (↥SK ⧸ K.subgroupOf SK) :=
    isPGroup_quotient_of_sup_eq_top189 hsup (isPGroup_s189 M H).comap_subtype
  have hPK : (P ⊓ K.subgroupOf SK).map SK.subtype ≤ CFSG.Open.pCoreOf 2 K := by
    rw [← hK3]
    refine Late.le_inSubgroup_pPrimeCore_of ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective SK.subtype_injective]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        CFSG.pPrimeCore_coprime_card
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro k hk
      have hn : (P ⊓ K.subgroupOf SK).Normal := inferInstance
      have hk' : (⟨k, hKSK hk⟩ : ↥SK) ∈
          Subgroup.normalizer ((P ⊓ K.subgroupOf SK : Subgroup ↥SK) : Set ↥SK) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hn]
        exact Subgroup.mem_top _
      exact Subgroup.le_normalizer_map SK.subtype (Subgroup.mem_map_of_mem SK.subtype hk')
  have hP2 : IsPGroup 2 P := by
    intro x
    obtain ⟨n, hn⟩ := hQ2 (QuotientGroup.mk (x : ↥SK))
    have hxn : (x : ↥SK) ^ (2 ^ n) ∈ K.subgroupOf SK := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn
      exact hn
    have hxP : (x : ↥SK) ^ (2 ^ n) ∈ P := P.pow_mem x.2 _
    have hG : (((x : ↥SK) ^ (2 ^ n) : ↥SK) : G) ∈ CFSG.Open.pCoreOf 2 K :=
      hPK ⟨_, ⟨hxP, hxn⟩, rfl⟩
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hG⟩
    refine ⟨n + m, ?_⟩
    have hm' := congrArg (fun y : ↥(CFSG.Open.pCoreOf 2 K) => (y : G)) hm
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hm'
    apply Subtype.ext
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul]
    exact hm'
  refine le_antisymm (le_sSup ⟨inferInstance, hP2⟩) (le_sSup ⟨CFSG.pCore_normal, ?_⟩)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥SK))
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem aschbacherSolvableCore_sk189_eq
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c)) :
    aschbacherSolvableCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c) :=
  aschbacherSolvableCore_eq_pCore_of_pPrimeCore_eq hSK

theorem isSylowOf_s189_of_mem (hmax : s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (h : Sec18H G A M H c) :
    CFSG.ABGLocalTools.IsSylowOf 2 (s189 M H) (s189 M H ⊔ theta189 M H c) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hAO : A ≤ Subgroup.normalizer ((s189 M H ⊔ theta189 M H c : Subgroup G) : Set G) :=
    fun _ ha => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨le_normalizer_s189 h ha, ((le_normalizer_sk189 h).trans (normalizer_sk189_le M H c)) ha⟩
  obtain ⟨T, hT, hST, hAT⟩ := exists_isSylowOf_le_of_coprime189 hA.isPGroup hAO
    (not_three_dvd_card_s189_sup_theta189 M H c) le_sup_left (isPGroup_s189 M H)
    (le_normalizer_s189 h)
  have hTmem : T ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hT.isPGroup, hAT⟩
  have hTS : T = s189 M H := (mem_maxInvariantPiSubgroups_iff.mp hmax).2 T hTmem hST
  rwa [hTS] at hT

theorem theta189_le_s189 (hmax : s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (h : Sec18H G A M H c)
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c)) :
    theta189 M H c ≤ s189 M H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := theta189 M H c with hT
  set Y := s189 M H ⊔ T
  have hT2 : IsPGroup 2 T := by
    rw [hT, theta189, inSubgroup, aschbacherSolvableCore_sk189_eq hSK]
    exact CFSG.pCore_isPGroup.map _
  have hTn : (T.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le ((le_sup_left : s189 M H ≤ sk189 M H c).trans (sk189_le_normalizer_theta189 M H c))
        Subgroup.le_normalizer)
  have hT2' : IsPGroup 2 (T.subgroupOf Y) := hT2.comap_subtype
  obtain ⟨Q, hQ⟩ := isSylowOf_s189_of_mem hmax h
  have hle := hT2'.le_sylow_of_normal Q
  intro t ht
  rw [← hQ]
  exact ⟨⟨t, (le_sup_right : T ≤ Y) ht⟩, hle (Subgroup.mem_subgroupOf.mpr ht), rfl⟩

@[expose] noncomputable def quotEquivSKAlpha189
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c)) :
    ↥(sk189 M H c) ⧸ CFSG.pPrimeCore 3 ↥(sk189 M H c) ≃* SKAlpha189 M H c :=
  QuotientGroup.quotientMulEquivOfEq (hSK.trans (aschbacherSolvableCore_sk189_eq hSK).symm)

theorem quotEquivSKAlpha189_mk
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c))
    (x : ↥(sk189 M H c)) :
    quotEquivSKAlpha189 hSK (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)) x) =
      alpha189 M H c x :=
  rfl

theorem map_quotEquivSKAlpha189
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c))
    (Y : Subgroup ↥(sk189 M H c)) :
    (Y.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)))).map
        (quotEquivSKAlpha189 hSK).toMonoidHom = Y.map (alpha189 M H c) := by
  rw [Subgroup.map_map]
  rfl

private noncomputable def mapEquiv189
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c))
    (Y : Subgroup ↥(sk189 M H c)) :
    ↥(Y.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)))) ≃*
      ↥(Y.map (alpha189 M H c)) :=
  (Subgroup.equivMapOfInjective _ _ (quotEquivSKAlpha189 hSK).injective).trans
    (MulEquiv.subgroupCongr (map_quotEquivSKAlpha189 hSK Y))

omit [Finite G] in
private theorem pPrimeCore_k189_eq
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    CFSG.pPrimeCore 3 ↥(normalClosureIn M c) = CFSG.pCore 2 ↥(normalClosureIn M c) :=
  Subgroup.map_injective (normalClosureIn M c).subtype_injective hK3

private noncomputable def kAlphaEquivTheta189
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    ↥(kAlpha189 M H c) ≃*
      ↥(normalClosureIn M c) ⧸ aschbacherSolvableCore 3 ↥(normalClosureIn M c) :=
  (kQuotEquiv189 (inf_theta189_eq_of_pPrimeCore_eq M H c hK3)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (aschbacherSolvableCore_eq_pCore_of_pPrimeCore_eq (pPrimeCore_k189_eq hK3)).symm)

theorem isSimpleGroup_kAlpha189 (hset : Setting189 G A M H c)
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    IsSimpleGroup ↥(kAlpha189 M H c) := by
  have := ktype_simple hset.mem_thetaComponentsIn hset.pRank_eq
  exact (kAlphaEquivTheta189 hK3).isSimpleGroup

theorem exists_mul_ne_mul_kAlpha189 (hset : Setting189 G A M H c)
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    ∃ a b : ↥(kAlpha189 M H c), a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := quasisimple_of_mem_thetaComponentsIn hset.mem_thetaComponentsIn
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  set e := kAlphaEquivTheta189 (H := H) hK3
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h' : a * b = b * a := by
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']

theorem centralizer_kAlpha189_eq_bot (hset : Setting189 G A M H c)
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) :
    Subgroup.centralizer (kAlpha189 M H c : Set (SKAlpha189 M H c)) = ⊥ := by
  have := kAlpha189_normal M H c
  have := isSimpleGroup_kAlpha189 hset hK3
  have hZ : Subgroup.center ↥(kAlpha189 M H c) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(kAlpha189 M H c))
      with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_kAlpha189 hset hK3
      have ha : a ∈ Subgroup.center ↥(kAlpha189 M H c) := by
        rw [h]
        exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  exact centralizer_eq_bot_of_sup189 (kAlpha189_sup_sAlpha189 M H c) (isPGroup_sAlpha189 M H c)
    (aschbacherSolvableCore_sKAlpha189 M H c) hZ

theorem sAlpha189_inf_kAlpha189_eq_bot_of_innerFree (hset : Setting189 G A M H c)
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c)) (hin : InnerFree189 M H c) :
    sAlpha189 M H c ⊓ kAlpha189 M H c = ⊥ := by
  have hin' := hin
  unfold InnerFree189 at hin'
  rw [centralizer_kAlpha189_eq_bot hset hK3, sup_bot_eq] at hin'
  exact le_bot_iff.mp hin'

theorem hyp1411_sk189 (hmax : s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (hset : Setting189 G A M H c)
    (hK3 : inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c))
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c)) :
    Sec20.Hyp1411 ↥(sk189 M H c) (kSK189 M H c) (sSK189 M H c) := by
  have h := hset.toSec18H
  have hKSK : normalClosureIn M c ≤ sk189 M H c := le_sup_right
  have hKn : (kSK189 M H c).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKSK).mpr (sk189_le_normalizer_k M H c)
  refine ⟨?_, hKn, ?_, ?_, (isPGroup_s189 M H).comap_subtype, ?_, ?_, ?_⟩
  ·
    have hM2 : CFSG.Open.IsTwoLocal M := (mem_scriptM_iff.mp h.mem_scriptM).1.1
    exact Item183NMProof.generalizedFitting_eq_of_pCoreOf_le h.charTwoType hM2
      (sup_le (s189_le M H) (normalClosureIn_le_of_sec18H189 h))
      ((pCoreOf_le_s189_of189 hmax h).trans le_sup_left)
  ·
    have := isPerfect_of_mem_thetaComponentsIn189 hset.mem_thetaComponentsIn
    have : Group.IsPerfect ↥(kSK189 M H c) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKSK).symm.toMonoidHom)
        (MulEquiv.surjective _)
    exact Subgroup.commutator_eq_self
  ·
    set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)) with hπ
    set e := quotEquivSKAlpha189 hSK
    have : ((kSK189 M H c).map π).Normal := hKn.map π (QuotientGroup.mk'_surjective _)
    have := isSimpleGroup_kAlpha189 hset hK3
    set f := mapEquiv189 hSK (kSK189 M H c)
    have : IsSimpleGroup ↥((kSK189 M H c).map π) := f.isSimpleGroup
    have hnc : ∃ x y : ↥((kSK189 M H c).map π), x * y ≠ y * x := by
      obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_kAlpha189 hset hK3
      refine ⟨f.symm a, f.symm b, fun h => hab ?_⟩
      simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg f h
    have hC : Subgroup.centralizer
        (((kSK189 M H c).map π : Subgroup _) : Set (↥(sk189 M H c) ⧸
          CFSG.pPrimeCore 3 ↥(sk189 M H c))) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e z ∈ Subgroup.centralizer (kAlpha189 M H c : Set (SKAlpha189 M H c)) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨y, hy, rfl⟩
        have h1 := Subgroup.mem_centralizer_iff.mp hz (π y) ⟨y, hy, rfl⟩
        rw [← quotEquivSKAlpha189_mk hSK y, ← map_mul, ← map_mul, ← hπ, h1]
      rw [centralizer_kAlpha189_eq_bot hset hK3, Subgroup.mem_bot] at hz'
      rw [Subgroup.mem_bot]
      exact e.injective (hz'.trans (map_one e).symm)
    exact CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot _ hnc hC
  ·
    intro x hx
    have hx' : x ∈ aschbacherSolvableCore 3 ↥(sk189 M H c) := by
      rw [aschbacherSolvableCore_sk189_eq hSK]
      exact hx
    exact Subgroup.mem_subgroupOf.mpr (theta189_le_s189 hmax h hSK ⟨x, hx', rfl⟩)
  ·
    rw [sSK189, kSK189, ← Subgroup.subgroupOf_sup le_sup_left hKSK, Subgroup.subgroupOf_self]
  ·
    intro H' hH' htop
    rw [hSK, sup_eq_left.mpr hH'] at htop
    exact htop

theorem nonempty_mulEquiv_map_kSK189
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c))
    {T : Type*} [Group T] (he : Nonempty (↥(kAlpha189 M H c) ≃* T)) :
    Nonempty (↥((kSK189 M H c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)))) ≃*
      T) :=
  he.map fun e => (mapEquiv189 hSK (kSK189 M H c)).trans e

theorem map_sSK189_inf_map_kSK189_eq_bot
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c))
    (hSK' : sAlpha189 M H c ⊓ kAlpha189 M H c = ⊥) :
    (sSK189 M H c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c))) ⊓
      (kSK189 M H c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c))) = ⊥ := by
  have hinj : Function.Injective (quotEquivSKAlpha189 hSK).toMonoidHom :=
    (quotEquivSKAlpha189 hSK).injective
  apply (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp
  rw [Subgroup.map_inf _ _ _ hinj, map_quotEquivSKAlpha189, map_quotEquivSKAlpha189]
  exact hSK'

theorem card_map_sSK189
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c)) :
    Nat.card ↥((sSK189 M H c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)))) =
      Nat.card ↥(sAlpha189 M H c) :=
  Nat.card_congr (mapEquiv189 hSK (sSK189 M H c)).toEquiv

end CFSG.RankThree.PartTwo.Sec18
