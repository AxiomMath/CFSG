module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow1523KType
public import CFSG.RankThree.PartTwo.Sec15.Sylow1523KSolv
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec15.Sylow1523KTools
import CFSG.RankThree.PartTwo.Sec15.Sylow1523ThetaON
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofMem
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofLocal
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
public import CFSG.RankThree.PartTwo.Sec15.Sylow1523KStruct
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec17.Proof171Steps

section K

variable {G : Type} [Group G] [Finite G]

open Sylow1523K

theorem k1523_casesQ
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h143 : Ronan148Q.Item143Q A (lB A)) {d : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdΩ : Subgroup.zpowers d ∉ omegaA A) :
    k1523 A d = ⊥ ∨
      ∃ X : Subgroup G, Group.IsPerfect ↥X ∧ X ≤ k1523 A d ∧
        k1523 A d = X ⊔ (k1523 A d ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) ∧
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ≤
          Subgroup.normalizer (k1523 A d : Set G) ∧
        (Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (k1523 A d : Set G) ∨
          Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6))) ∧
        (X ∈ thetaComponentsAt 3 d ∨
          Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
            CFSG.Blueprint.NativeSporadic.ON ∨
          Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
          IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set D := delta A (lB A) C with hDdef
  set K := k1523 A d with hKdef
  set M := pPrimeCoreOf 3 C with hM
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hKD : K = oPrimeResidualOf 3 D := rfl
  have hO'C : O' ≤ C :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA))
  have hO'M : O' ≤ Subgroup.normalizer (M : Set G) := hO'C.trans (le_normalizer_pPrimeCoreOf 3 C)
  have hO'cop : Nat.Coprime 3 (Nat.card O') := coprime_card_pPrimeCoreOf 3 _
  have hMcop : Nat.Coprime 3 (Nat.card M) := coprime_card_pPrimeCoreOf 3 _
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty D A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 d hdA hd1 hdΩ Qs hQs
  rcases halt with h1 | ⟨b', d', Lb', hb'Ω, -, -, -, -, -, -, X, hDX, hinv, hcase⟩
  ·
    left
    have hKM : K ≤ M :=
      Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hO'cop hO'M h1.le
    rw [eq_bot_iff]
    refine (k1523_eq_oPrimeResidualOf A d).le.trans ?_
    refine Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hMcop ?_ (by rwa [bot_sup_eq])
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  right
  have hDX' : D = M ⊔ O' ⊔ X := hDX
  have hMMX : M ≤ Subgroup.normalizer ((M ⊔ X : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hXD : X ≤ D := le_sup_right.trans hDX.ge
  have hXC : X ≤ C := hXD.trans (delta_le _)
  obtain ⟨hXp, hXK, htype⟩ : Group.IsPerfect ↥X ∧ X ≤ K ∧
      (X ∈ thetaComponentsAt 3 d ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
          CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) := by
    rcases hcase with ⟨hXθ, hXeq, hne⟩ | ⟨-, ⟨𝒳, h𝒳, -, hX𝒳⟩, htypes⟩
    ·
      obtain ⟨hb'A, hb'3, -⟩ := zpowers_mem_omegaA_iff.mp hb'Ω
      have hb'1 : b' ≠ 1 := by
        rintro rfl
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hb'3
        norm_num at hb'3
      have hne' : Subgroup.zpowers d ≠ Subgroup.zpowers b' := fun heq => hdΩ (heq ▸ hb'Ω)
      have hB := isHyperplane_closure_pair h.isE27' hdA hb'A hd1 hb'1 hne'
      have hLBX : lB A (Subgroup.closure {d, b'}) ≤ X := by
        rw [hXeq]
        exact le_sup_left
      have hLBK := lB_le_oPrimeResidualOf h hB (hLBX.trans hXD)
      have hXp : Group.IsPerfect ↥X := Sec6.isPerfect_of_mem_thetaComponentsAt hXθ
      refine ⟨hXp, ?_, Or.inl hXθ⟩
      refine le_of_isPerfect_of_le_sup hXp hLBX (le_normalizer_theta X) (isSolvable_theta X)
        (theta_le X) hXeq.le hLBK ?_
      exact hXD.trans (Proof1515Res.le_normalizer_oRes3 Subgroup.le_normalizer)
    ·
      have hXp : Group.IsPerfect ↥X := by
        rw [hX𝒳]
        exact isPerfect_sSup fun M hM => Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hM)
      have hX3 := eq_oPrimeResidualOf_of_quot hXp (oPrimeResidual_eq_top_of_types143 htypes)
      refine ⟨hXp, ?_, Or.inr htypes⟩
      rw [hX3]
      exact oPrimeResidualOf_mono_three hXD
  refine ⟨X, hXp, hXK, ?_⟩
  have hO'MX : O' ≤ Subgroup.normalizer ((M ⊔ X : Subgroup G) : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (hinv.centralizer_le hdA)
  have hDMX : D ≤ (M ⊔ X) ⊔ O' := by
    rw [hDX']
    exact sup_le (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
      (le_sup_of_le_left le_sup_right)
  have hKMX : K ≤ M ⊔ X := Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hO'cop hO'MX hDMX
  have hMXD : M ⊔ X ≤ D := by
    rw [hDX']
    exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  have hKeq : K = oPrimeResidualOf 3 (M ⊔ X) := by
    refine le_antisymm ?_ (oPrimeResidualOf_mono_three hMXD)
    exact (k1523_eq_oPrimeResidualOf A d).le.trans (oPrimeResidualOf_mono_three hKMX)
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Proof1515Res.le_normalizer_oRes3 hMMX
  have hKn : C ≤ Subgroup.normalizer (K : Set G) ∨
      Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) := by
    rcases hinv with hnorm | ⟨-, -, hA6, -⟩
    · left
      rw [hKeq]
      exact Proof1515Res.le_normalizer_oRes3 hnorm
    · exact Or.inr hA6
  refine ⟨?_, hMK, hKn, htype⟩
  refine le_antisymm ?_ (sup_le hXK inf_le_left)
  have hXM : X ≤ Subgroup.normalizer (M : Set G) := hXC.trans (le_normalizer_pPrimeCoreOf 3 C)
  intro k hk
  have hkXM : k ∈ ((X ⊔ M : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hKMX hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X M hXM] at hkXM
  obtain ⟨x, hx, m, hm, rfl⟩ := hkXM
  have hmK : m ∈ K := by
    have : x⁻¹ * (x * m) ∈ K := K.mul_mem (K.inv_mem (hXK hx)) hk
    simpa using this
  exact Subgroup.mul_mem_sup hx ⟨hmK, hm⟩

end K

section Steps

variable {G : Type} [Group G] [Finite G]

open Sylow1523K

theorem isSolvable_k1523_infQ
    (h45 : Sec4.Item4_5) (hSz : KFacts.KPSz)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h143 : Ronan148Q.Item143Q A (lB A)) {d : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdΩ : Subgroup.zpowers d ∉ omegaA A) :
    Group.IsSolvable ↥(k1523 A d ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 := not_three_dvd_card_k1523_inf A d
  rcases k1523_casesQ h h143 hdA hd1 hdΩ with hK0 | ⟨X, hXp, hXK, hKX, hMK, -, -⟩
  · rw [hK0, bot_inf_eq]
    infer_instance
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set K := k1523 A d with hKdef
  set N := K ⊓ pPrimeCoreOf 3 C with hN
  have hNcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  have hKp : Group.IsPerfect ↥K :=
    isPerfect_of_le_sup_coprime (k1523_eq_oPrimeResidualOf A d) hXp hXK inf_le_left hNcop hKX.le
  by_contra hs
  obtain ⟨J', hJ'⟩ := Proof1423.exists_mem_thetaComponents_of_not_isSolvable hN3 hs
  set J := J'.map N.subtype with hJdef
  have hJN : J ∈ thetaComponentsIn N := ⟨J', hJ', rfl⟩
  have hJNle : J ≤ N := le_of_mem_thetaComponentsIn hJN
  have hJ3 : ¬ 3 ∣ Nat.card J := fun h3 => hN3 (h3.trans (Subgroup.card_dvd_of_le hJNle))
  have hKC : K ≤ C := k1523_le_centralizer A d
  have hNC : N ≤ C := inf_le_left.trans hKC
  have hNM : N ≤ pPrimeCoreOf 3 C := inf_le_right
  have hMN : pPrimeCoreOf 3 C ≤ Subgroup.normalizer (N : Set G) :=
    Late.le_normalizer_inf hMK Subgroup.le_normalizer
  have hNnorm : (N.subgroupOf (pPrimeCoreOf 3 C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  have hMC : pPrimeCoreOf 3 C ≤ C := pPrimeCoreOf_le 3 C
  have hMnorm : ((pPrimeCoreOf 3 C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMC).mpr (le_normalizer_pPrimeCoreOf 3 C)
  have hJC : J ∈ thetaComponentsIn C :=
    Proof1423.mem_thetaComponentsIn_of_isSubnormal hJN hNC
      (Proof1423.isSubnormal_subgroupOf_trans1423 hNM hMC hNnorm.isSubnormal hMnorm.isSubnormal)
  have hT := h.toTheoremFourHyp
  have hCtop : C ≠ ⊤ := Sec14.centralizer_singleton_ne_top hT.isSimpleGroup hT.nonabelian hd1
  have hC4 : SectionFourHyp C := hT.sectionFourHyp hCtop
  have hd3 : d ^ 3 = 1 := h.toSec13Data.isElemAbelian.2 d hdA
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hO3 : CFSG.pCore 3 ↥C ≠ ⊥ := by
    set d' : ↥C := ⟨d, hdC⟩
    have hd'3 : orderOf d' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hd3 hd1
    have hZn : (Subgroup.zpowers d').Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hgc : g * d' = d' * g := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
      have : g * d' ^ k * g⁻¹ = d' ^ k := by
        rw [(Commute.zpow_right hgc k).eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.zpow_mem_zpowers d' k
    have hZ3 : IsPGroup 3 (Subgroup.zpowers d') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd'3, pow_one])
    have hZle : Subgroup.zpowers d' ≤ CFSG.pCore 3 ↥C := le_sSup ⟨hZn, hZ3⟩
    intro hbot
    have hd'1 : d' = 1 := by
      have := hZle (Subgroup.mem_zpowers d')
      rwa [hbot, Subgroup.mem_bot] at this
    exact hd1 (congrArg Subtype.val hd'1)
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) := by
    obtain ⟨J'', hJ'', hJeq⟩ := hJC
    refine (k1523_eq_oPrimeResidualOf A d).le.trans ?_
    rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hyK, k, hk⟩
    set y' : ↥C := ⟨y, hKC hyK⟩
    have hy'k : y' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    have hP : IsPGroup 3 (Subgroup.zpowers y') := by
      obtain ⟨j, -, hj⟩ :=
        (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy'k)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have h1 := h45 C hC4 (Subgroup.zpowers y') hP (Or.inl hO3) J'' hJ''
    rw [← hJeq]
    exact Subgroup.le_normalizer_map C.subtype ⟨y', h1 (Subgroup.mem_zpowers y'), rfl⟩
  obtain ⟨f, hf⟩ := Proof1423.suzukiModel_thetaQuot hSz hC4 hNC hN3 hJN
  have hKc := le_thetaQuotCentralizer_of_isPerfect (k1523_eq_oPrimeResidualOf A d) hKp hKJ hJ3
    (KFacts.commutator_le_inner_of_suzukiModel hf)
  exact Proof1423.not_le_thetaQuotCentralizer_self hJN (hJNle.trans (inf_le_left.trans hKc))

theorem step1523KSolv_ofQ
    (h45 : Sec4.Item4_5) (hSz : KFacts.KPSz)
    (h143 : Ronan148Q.Item143QS14) : Step1523KSolv := by
  intro G _ _ A c L h _ _ _ _ _ d hdA hd1 _ hdΩ _ _
  exact isSolvable_k1523_infQ h45 hSz h.toSec14Std (h143 G A c L h.toSec14Std) hdA hd1 hdΩ

theorem step1523KTypeY4_of_solvQ
    (h134 : Item134) (h143 : Ronan148Q.Item143QS14) (h149 : Sec16.Item149S14)
    (hsolv : Step1523KSolv) :
    Step1523KTypeY4 := by
  intro G _ _ A c L h hJ Y hY hm hYtype d hdA hd1 hdc hdΩ hΔ0 hYK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN := hsolv G A c L h hJ Y hY hm hYtype d hdA hd1 hdc hdΩ hΔ0 hYK
  have hD := h.toSec13Data
  have hS := h.toSec14Std
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨hdL, S3, hdS, hSd⟩ := hdc
  obtain ⟨-, -, hθ3L, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hdZ : IsZCentral L d := by
    obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3L hJ hdL hd1 S3 hdS hSd
    exact ⟨_, hSy, hZ⟩
  have hX₀K := Proof15Res11.residual_le_k1523 h hJ hdA hd1 hdZ
  obtain ⟨hTs, hT3, hT7⟩ := facts_of_l37_or_a7 hYtype
  have h7 : 7 ∣ Nat.card (↥(k1523 A d) ⧸ aschbacherSolvableCore 3 ↥(k1523 A d)) :=
    hT7.trans (card_dvd_card_theta_quot inf_le_right _ (surjective_inf_quot hYK) hT3)
  rcases k1523_casesQ hS (h143 G A c L hS) hdA hd1 hdΩ with
    hK0 | ⟨X, hXp, hXK, hKX, -, hKn', htype⟩
  ·
    exfalso
    have h1 : Nat.card ↥(k1523 A d) = 1 := by rw [hK0, Subgroup.card_bot]
    have h2 := h7.trans (Subgroup.card_quotient_dvd_card _)
    rw [h1] at h2
    norm_num at h2
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set K := k1523 A d with hKdef
  set M := pPrimeCoreOf 3 C with hM
  have hKC : K ≤ C := k1523_le_centralizer A d
  have hNθ : K ⊓ M ≤ inSubgroup (aschbacherSolvableCore 3) K :=
    le_inSubgroup_theta inf_le_left (le_normalizer_k1523_inf A d) hsN
      (not_three_dvd_card_k1523_inf A d)
  obtain ⟨eXK⟩ := nonempty_theta_quot_equiv hXK (hKX.le.trans (sup_le_sup_left hNθ X))
  have hNcop : Nat.Coprime 3 (Nat.card ↥(K ⊓ M)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_card_k1523_inf A d)
  have hKp : Group.IsPerfect ↥K :=
    isPerfect_of_le_sup_coprime (k1523_eq_oPrimeResidualOf A d) hXp hXK inf_le_left hNcop hKX.le
  have h7X : 7 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rwa [Nat.card_congr eXK.toEquiv]
  have hKn : C ≤ Subgroup.normalizer (K : Set G) := by
    rcases hKn' with hKn | hA6
    · exact hKn
    · exfalso
      rw [Proof15Res11.card_of_isTripleCover_a6 hA6] at h7X
      norm_num at h7X
  have hsub : (K.subgroupOf C).IsSubnormal :=
    Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr hKn)
  have hON : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K)
      CFSG.Blueprint.NativeSporadic.ON := by
    rcases htype with hXθ | hXON | hXA6 | hXA6A6
    ·
      have hKθ : K ∈ thetaComponentsAt 3 d := Sec6.mem_thetaComponentsIn_of hKC hKp hsub
        (LocalCores.isQuasisimple_of_mulEquiv eXK (Sec6.isQuasisimple_of_mem_thetaComponentsAt hXθ))
      rcases h134 G A c L hD hJ d hdA hd1 hdZ K hKθ hX₀K with
        ⟨-, hA6, -⟩ | ⟨-, hA6, -⟩ | ⟨hON, -⟩
      · rw [Proof15Res11.card_of_isTripleCover_a6 hA6] at h7
        norm_num at h7
      · rw [Proof15Res11.card_of_isTripleCover_a6 hA6] at h7
        norm_num at h7
      · exact hON
    · exact Sec13.isTripleCover_of_mulEquiv eXK hXON
    · rw [Proof15Res11.card_of_isTripleCover_a6 hXA6] at h7X
      norm_num at h7X
    · obtain ⟨U, V, -, hV, hUV, -, -, hUc, hVc⟩ := hXA6A6
      have hUN : U ≤ Subgroup.normalizer (V : Set (↥X ⧸ aschbacherSolvableCore 3 ↥X)) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hV]
        exact le_top
      have h1 := card_sup_dvd_card_mul hUN
      rw [hUV, Subgroup.card_top, Proof15Res11.card_of_isTripleCover_a6 hUc,
        Proof15Res11.card_of_isTripleCover_a6 hVc] at h1
      have h2 := h7X.trans h1
      norm_num at h2
  have hO2 : CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K := by
    obtain ⟨-, ⟨eON⟩⟩ := hON
    exact Sylow1523Theta.pCore_two_eq_of_ON eON fun q hq hq3 Q _ u hu hu2 =>
      Sec16.Steps166.pRank_inf_centralizer_le_two h.toTheoremFourHyp K hq hq3 Q u hu hu2
  have hONs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  have hQp : Group.IsPerfect (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hQq : CFSG.IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    isQuasisimple_of_isTripleCover hON
  have hAC : A ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hdA)
  have hKY : K ∈ scriptY A :=
    ⟨fun htop => centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hd1
      (top_le_iff.mp (htop ▸ hKC)), hAC.trans hKn⟩
  have hKθC : K ∈ thetaComponentsIn C := Sec6.mem_thetaComponentsIn_of hKC hKp hsub hQq
  have hnsol : ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A (lB A) K)) := by
    set X₀ := inSubgroup perfectResidual (L ⊓ C) with hX₀
    have hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set G) := by
      have hAC' : A ≤ Subgroup.normalizer ((C : Subgroup G) : Set G) :=
        hAC.trans Subgroup.le_normalizer
      exact (Late.le_normalizer_inf hD.le_normalizer hAC').trans
        (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
          _)
    have hΔ := Proof15Res7.le_delta_of_map_eq_centralizer hS hJ hdA hd1 hdL ⟨S3, hdS, hSd⟩
      (Item148HJ.residual_le L d) hAX₀
      (Proof15Res11.map_residual_eq_centralizer hS hJ hdA hd1 hdL ⟨S3, hdS, hSd⟩)
    have hX₀3 : X₀ = oPrimeResidualOf 3 X₀ := Sec17.Proof171Steps.residual_eq_oPrimeResidualOf hS
      (Proof15Res11.isHyperplane_of h hJ hdA hd1 hdL) (Proof15Res11.isLBConfig_of h hJ hdZ)
    have hX₀le : X₀ ≤ oPrimeResidualOf 3 (delta A (lB A) K) := by
      rw [hX₀3]
      exact Sec17.Proof171Steps.oPrimeResidualOf_mono_three (hΔ.trans (delta_mono hX₀K))
    have hX₀p : Group.IsPerfect ↥X₀ := Item148HJ.residual_isPerfect L d
    have hdX₀ : d ∈ X₀ := Item148HJ.inf_le_residual hS
      (Proof15Res11.isHyperplane_of h hJ hdA hd1 hdL) (Proof15Res11.isLBConfig_of h hJ hdZ)
      ⟨hdA, hdL⟩
    have : Nontrivial ↥X₀ := ⟨⟨⟨d, hdX₀⟩, 1, fun h1 => hd1 (congrArg Subtype.val h1)⟩⟩
    intro hsol
    exact Group.IsPerfect.not_isSolvable (G := ↥X₀)
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hX₀le))
  have hKΔ : K = delta A (lB A) K :=
    Y4Core.eq_delta_of_not_isSolvable (h149 G A c L hS) hKθC hKY hnsol
  have eO2 : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
    QuotientGroup.quotientMulEquivOfEq hO2
  refine ⟨⟨hKY, k1523_eq_oPrimeResidualOf A d, hKΔ, CFSG.IsQuasisimple.of_mulEquiv eO2 hQq⟩, ?_⟩
  exact Sec13.isTripleCover_of_mulEquiv eO2.symm hON

end Steps

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
