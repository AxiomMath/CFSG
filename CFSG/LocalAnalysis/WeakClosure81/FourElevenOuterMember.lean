module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenBasic
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenOuter
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalQuasisimple
public import CFSG.LocalAnalysis.WeakClosure81.PGLTwoPrimePrintedRelativeGeneration
public import CFSG.Quasithin.Vol2.Ch11SecE42S2d
public import CFSG.Quasithin.EmptyFaithful.E22RSyl
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.RankThree.PartOne.LIT.FiveRecords

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin

variable {Q : Type} [Group Q] [Finite Q]

open scoped commutatorElement

theorem exists_conj_isSylowIn_centralizer {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : UniquenessCase.PartTwo.IsOmegaColl Ω) {A : Subgroup Q}
    (hAΩ : A ∈ Ω) (_hAT : A ≤ T) {b : Q} (hbA : b ∈ A) :
    ∃ g : Q, conjSubgroup A g ∈ Ω ∧ conjSubgroup A g ≤ T ∧
      IsSylowIn 2 (T ⊓ centralizer ({g⁻¹ * b * g} : Set Q))
        (centralizer ({g⁻¹ * b * g} : Set Q)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup Q := centralizer ({b} : Set Q)
  have hAea := hΩ.elemAbelian A hAΩ
  have hAC : A ≤ C := by
    have h1 : A ≤ Subgroup.centralizer (A : Set Q) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hAea.1
    refine h1.trans (Subgroup.centralizer_le ?_)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hbA
  obtain ⟨S, hS, hAS⟩ := exists_isSylowIn_ge 2 hAC hAea.isPGroup
  obtain ⟨c, -, hc⟩ := CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn hT le_top hS.isPGroup
  have hSconjT : conjSubgroup S c⁻¹ ≤ T := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxs : c⁻¹ * x * c ∈ S := by simpa using hx
    have hmem := hc hxs
    rw [mem_conjSubgroup_iff] at hmem
    simpa [mul_assoc] using hmem
  have hCconj : conjSubgroup C c⁻¹ = Subgroup.centralizer ({c * b * c⁻¹} : Set Q) := by
    ext x
    rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hx' : (c⁻¹ * x * c) * b = b * (c⁻¹ * x * c) := by simpa using hx
      calc x * (c * b * c⁻¹) = c * ((c⁻¹ * x * c) * b) * c⁻¹ := by group
        _ = c * (b * (c⁻¹ * x * c)) * c⁻¹ := by rw [hx']
        _ = (c * b * c⁻¹) * x := by group
    · intro hx
      have hx' : x * (c * b * c⁻¹) = (c * b * c⁻¹) * x := hx
      simp only [inv_inv] at hx' ⊢
      calc (c⁻¹ * x * c) * b = c⁻¹ * (x * (c * b * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * b * c⁻¹) * x) * c := by rw [hx']
        _ = b * (c⁻¹ * x * c) := by group
  have hSylconj : IsSylowIn 2 (conjSubgroup S c⁻¹) (conjSubgroup C c⁻¹) := by
    have h := (E1.isSylowIn_map_mulEquiv (p := 2) (MulAut.conj c)).mpr hS
    simpa [CFSG.Quasithin.conjSubgroup] using h
  have hSCconj : conjSubgroup S c⁻¹ ≤ conjSubgroup C c⁻¹ := by
    simpa [CFSG.Quasithin.conjSubgroup] using
      Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom) hS.le
  have hAconj' : conjSubgroup A c⁻¹ ≤ conjSubgroup S c⁻¹ := by
    simpa [CFSG.Quasithin.conjSubgroup] using
      Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom) hAS
  have hAconj : conjSubgroup A c⁻¹ ≤ T := hAconj'.trans hSconjT
  have hSylFinal : IsSylowIn 2 (T ⊓ Subgroup.centralizer ({c * b * c⁻¹} : Set Q))
      (Subgroup.centralizer ({c * b * c⁻¹} : Set Q)) := by
    rw [← hCconj]
    refine CFSG.Quasithin.E22L2.e22r_isSylowIn_of_le hSylconj (le_inf hSconjT hSCconj)
      inf_le_right (hT.isPGroup.to_le inf_le_left)
  refine ⟨c⁻¹, hΩ.conj A hAΩ c⁻¹, ?_, ?_⟩
  · simpa [CFSG.Quasithin.conjSubgroup] using hAconj
  · simpa [CFSG.Quasithin.conjSubgroup, inv_inv] using hSylFinal

theorem OuterData.centralizer_le_sup_iSup_calEi
    {L : Subgroup Q} [L.Normal] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (hidx : L.index ≤ 2) (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) {T A : Subgroup Q}
    {b : Q} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hbA : b ∈ A)
    (hbL : b ∉ L)
    (hSyl : IsSylowIn 2 (T ⊓ centralizer ({b} : Set Q)) (centralizer ({b} : Set Q)))
    (hb : OuterData L p b) (hAL : A ⊓ L ≠ ⊥) :
    centralizer ({b} : Set Q) ≤
      T ⊔ ⨆ J ∈ {J : Subgroup Q | UniquenessCase.PartTwo.InCalEi 1 T A J}, J := by
  classical
  let K : Subgroup Q := centralizer ({b} : Set Q)
  have hb1 : b ≠ 1 := by
    intro h
    exact hbL (by simp [h])
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hA.2 b hbA) hb1
  obtain ⟨π, hπ, hker, hkerL⟩ := OuterData.exists_hom_pgl2 hb hidx hbL hb2
  have hTau : E1.tauOf ⊤ T A ≤ T ⊓ K := by
    have htau : E1.tauOf ⊤ T A = T ⊓ centralizer (A : Set Q) := by
      simpa [UniquenessCase.PartTwo.tA] using tA_eq_inf_centralizer hO2 T A
    rw [htau]
    refine inf_le_inf_left T (Subgroup.centralizer_le ?_)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hbA
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAL
  let a0 : Q := a
  have ha0A : a0 ∈ A := a.2.1
  have ha0L : a0 ∈ L := a.2.2
  have ha0K : a0 ∈ K := by
    have h1 : a0 ∈ Subgroup.centralizer (A : Set Q) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).mpr hA.1 ha0A
    exact Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hbA) h1
  have ha0ne : a0 ≠ 1 := by
    intro h
    exact ha1 (Subtype.ext h)
  have hne : (A.subgroupOf K).map π ≠ ⊥ := by
    intro hbot
    have hmemA : (⟨a0, ha0K⟩ : ↥K) ∈ A.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr ha0A
    have hmem : π ⟨a0, ha0K⟩ ∈ (A.subgroupOf K).map π :=
      Subgroup.mem_map.mpr ⟨_, hmemA, rfl⟩
    have hone : π ⟨a0, ha0K⟩ = 1 := by
      have h1 : π ⟨a0, ha0K⟩ ∈
          (⊥ : Subgroup (CFSG.GorensteinWalter.PGL2 (ZMod p))) := by
        simpa [hbot] using hmem
      exact Subgroup.mem_bot.mp h1
    have hker' : (⟨a0, ha0K⟩ : ↥K) ∈ π.ker := MonoidHom.mem_ker.mpr hone
    have hx1 : (⟨a0, ha0K⟩ : ↥K) = 1 := hkerL ⟨a0, ha0K⟩ hker' ha0L
    exact ha0ne (congrArg Subtype.val hx1)
  have hF : Nat.card (ZMod p) = p := by rw [Nat.card_zmod]
  have hp5 : 5 < p := by omega
  exact CFSG.LocalAnalysis.WeakClosure81.relative_generation_printed_of_pgl2_prime
    hF hp5 hT hAT hA hTau hSyl π hπ hker hne

theorem OuterData.inCalEi_two_centralizer_five {L : Subgroup Q} [L.Normal]
    (h2 : IsPGroup 2 (Q ⧸ L)) (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) {T A : Subgroup Q}
    {b : Q} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hbA : b ∈ A) (hbL : b ∉ L)
    (hSyl : IsSylowIn 2 (T ⊓ centralizer ({b} : Set Q)) (centralizer ({b} : Set Q)))
    (hb : OuterData L 5 b) (hAL : A ⊓ L ≠ ⊥) :
    UniquenessCase.PartTwo.InCalEi 2 T A (centralizer ({b} : Set Q)) := by
  classical
  let K : Subgroup Q := centralizer ({b} : Set Q)
  let H : Subgroup Q := L ⊓ K
  let J : Subgroup Q := ⁅H, H⁆
  have hb1 : b ≠ 1 := by
    intro h
    exact hbL (by simp [h])
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hA.2 b hbA) hb1
  have hHK : H ≤ K := inf_le_right
  have hHL : H ≤ L := inf_le_left
  have hJH : J ≤ H := Subgroup.commutator_le_self H
  have hJK : J ≤ K := hJH.trans hHK
  have hJL : J ≤ L := hJH.trans hHL
  have hJsubNorm : (J.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mpr (by
      simpa [K, H, J] using hb.centralizer_le_normalizer)
  have hJnormH : (J.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mpr (hHK.trans (by
      simpa [K, H, J] using hb.centralizer_le_normalizer))
  obtain ⟨eH⟩ := hb.pgl2
  obtain ⟨eJ⟩ := hb.psl2
  have hPSLsimple : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    CFSG.Quasithin.Vol2.Ch11.SecE.isSimpleGroup_psl (p := 5) (by norm_num)
  have hJsimple : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hJqRoot : CFSG.IsQuasisimple ↥J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm
      (CFSG.Quasithin.Vol2.Ch11.SecE.isQuasisimple_psl (p := 5) (by norm_num))
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    ⟨hJqRoot.1.commutator_eq_top, hJqRoot.2.1⟩
  have hJperf : Group.IsPerfect ↥J := hJqRoot.1
  have hJnontriv : Nontrivial ↥J :=
    CFSG.LocalCores.isQuasisimple_nontrivial hJqRoot
  have hJsubSimple : IsSimpleGroup ↥(J.subgroupOf K) :=
    MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hJK)
  have hOddZ5 : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 5)) := by
    rw [Nat.card_zmod]
    exact ⟨5, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hcommPGLindex : (commutator (CFSG.GorensteinWalter.PGL2 (ZMod 5))).index = 2 := by
    rw [CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three
      (ZMod 5) hOddZ5 (by rw [Nat.card_zmod]; norm_num)]
    exact CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two (ZMod 5) hOddZ5
  have hJsubEq : J.subgroupOf H = commutator ↥H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJH,
      Subgroup.map_subtype_commutator]
  have hJmap : (J.subgroupOf H).map eH.toMonoidHom =
      commutator (CFSG.GorensteinWalter.PGL2 (ZMod 5)) := by
    rw [hJsubEq, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eH.surjective]
    rfl
  have hJindexH : (J.subgroupOf H).index = 2 := by
    have h := Subgroup.index_map_equiv (H := J.subgroupOf H) eH
    change ((J.subgroupOf H).map eH.toMonoidHom).index =
      (J.subgroupOf H).index at h
    rw [hJmap] at h
    rw [← h]
    exact hcommPGLindex
  have hTau : E1.tauOf ⊤ T A ≤ T ⊓ K := by
    have htau : E1.tauOf ⊤ T A = T ⊓ centralizer (A : Set Q) := by
      simpa [UniquenessCase.PartTwo.tA] using tA_eq_inf_centralizer hO2 T A
    rw [htau]
    refine inf_le_inf_left T (Subgroup.centralizer_le ?_)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hbA
  have hAtau : A ≤ E1.tauOf ⊤ T A := by
    simpa [hO2] using E1.le_tauOf hT hAT hA
  have hAK : A ≤ K := hAtau.trans (hTau.trans inf_le_right)
  have hSylOf : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hSyl
  have key (N : Subgroup ↥K) (hNn : N.Normal)
      (hNnotTop : ¬ J ≤ N.map K.subtype) :
      N.map K.subtype ⊓ J = ⊥ ∧ N.map K.subtype ⊓ L = ⊥ := by
    have : N.Normal := hNn
    have : (J.subgroupOf K).Normal := hJsubNorm
    have hNJsub : N ⊓ J.subgroupOf K = ⊥ := by
      have hnormal : ((N ⊓ J.subgroupOf K).subgroupOf (J.subgroupOf K)).Normal :=
        inferInstance
      rcases hJsubSimple.eq_bot_or_eq_top_of_normal
        ((N ⊓ J.subgroupOf K).subgroupOf (J.subgroupOf K)) with hbot | htop
      · have hdisj : Disjoint (N ⊓ J.subgroupOf K) (J.subgroupOf K) :=
          Subgroup.subgroupOf_eq_bot.mp hbot
        have hbot' : (N ⊓ J.subgroupOf K) ⊓ J.subgroupOf K = ⊥ := hdisj.eq_bot
        simpa [inf_assoc, inf_idem] using hbot'
      · have hle : J.subgroupOf K ≤ N :=
          (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left
        apply absurd ?_ hNnotTop
        calc J = (J.subgroupOf K).map K.subtype :=
              ((Subgroup.subgroupOf_map_subtype J K).trans
                (inf_eq_left.mpr hJK)).symm
          _ ≤ N.map K.subtype := Subgroup.map_mono hle
    have hNJ : N.map K.subtype ⊓ J = ⊥ := by
      have hJmapSub : (J.subgroupOf K).map K.subtype = J :=
        (Subgroup.subgroupOf_map_subtype J K).trans (inf_eq_left.mpr hJK)
      calc N.map K.subtype ⊓ J
          = N.map K.subtype ⊓ (J.subgroupOf K).map K.subtype := by rw [hJmapSub]
        _ = (N ⊓ J.subgroupOf K).map K.subtype :=
            (Subgroup.map_inf N (J.subgroupOf K) K.subtype K.subtype_injective).symm
        _ = ⊥ := by rw [hNJsub, Subgroup.map_bot]
    refine ⟨hNJ, le_antisymm ?_ bot_le⟩
    intro z hz
    have hzN : z ∈ N.map K.subtype := hz.1
    have hzL : z ∈ L := hz.2
    obtain ⟨n, hnN, hnz⟩ := Subgroup.mem_map.mp hzN
    have hzK : z ∈ K := by
      rw [← hnz]
      exact n.2
    have hzH : z ∈ H := ⟨hzL, hzK⟩
    have hzC : z ∈ Subgroup.centralizer (J : Set Q) := by
      rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
      intro x hxJ
      have hxK : x ∈ K := hJK hxJ
      have hxH : x ∈ H := hJH hxJ
      have hcommN : ⁅n, (⟨x, hxK⟩ : ↥K)⁆ ∈ N := by
        have hmem := Subgroup.commutator_mem_commutator hnN
          (Subgroup.mem_top (⟨x, hxK⟩ : ↥K))
        exact (Subgroup.commutator_le_left N (⊤ : Subgroup ↥K)) hmem
      have hzNcomm : ⁅z, x⁆ ∈ N.map K.subtype := by
        refine ⟨⁅n, (⟨x, hxK⟩ : ↥K)⁆, hcommN, ?_⟩
        rw [map_commutatorElement, hnz]
        rfl
      have hzj : ⁅z, x⁆ ∈ J := Subgroup.commutator_mem_commutator hzH hxH
      have hone : ⁅z, x⁆ = 1 := by
        have hmem : ⁅z, x⁆ ∈ N.map K.subtype ⊓ J := ⟨hzNcomm, hzj⟩
        rw [hNJ] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact hone
    have hzbot : z ∈ L ⊓ Subgroup.centralizer (J : Set Q) := ⟨hzL, hzC⟩
    rw [hb.inf_centralizer_eq_bot] at hzbot
    exact Subgroup.mem_bot.mp hzbot
  let R : Subgroup ↥K := CFSG.solvableRadical ↥K
  have hRnotTop : ¬ J ≤ R.map K.subtype := by
    intro hle
    have hRsolv : Group.IsSolvable ↥R :=
      CFSG.Quasithin.A3.solvableRadical_isSolvable
    let eR : ↥R ≃* ↥(R.map K.subtype) :=
      Subgroup.equivMapOfInjective R K.subtype K.subtype_injective
    have hRbarsolv : Group.IsSolvable ↥(R.map K.subtype) :=
      Group.isSolvable_of_isSolvable_injective (f := eR.symm.toMonoidHom) eR.symm.injective
    have hJsolv : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥J hJsolv
  obtain ⟨hRJ, hRL⟩ := key R inferInstance hRnotTop
  have hRp : IsPGroup 2 R := by
    let eR : ↥R ≃* ↥(R.map K.subtype) :=
      Subgroup.equivMapOfInjective R K.subtype K.subtype_injective
    let f : ↥(R.map K.subtype) →* Q ⧸ L :=
      (QuotientGroup.mk' L).comp (R.map K.subtype).subtype
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      refine le_antisymm ?_ bot_le
      intro z hz
      rw [MonoidHom.mem_ker] at hz
      have hzL : (z : Q) ∈ L := (QuotientGroup.eq_one_iff (z : Q)).mp hz
      have hzR : (z : Q) ∈ R.map K.subtype := z.2
      have hmem : (z : Q) ∈ R.map K.subtype ⊓ L := ⟨hzR, hzL⟩
      rw [hRL] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    have hRbar2 : IsPGroup 2 ↥(R.map K.subtype) := h2.of_injective f hf
    exact hRbar2.of_equiv eR.symm
  have hRclosed : E1.IsTwoClosed R := by
    refine ⟨R, ⟨le_rfl, hRp, ?_⟩, ?_⟩
    · rw [Subgroup.relIndex_self]
      norm_num
    · rw [Subgroup.subgroupOf_self]
      infer_instance
  have hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J := by
    intro x hxK
    obtain ⟨k, hk⟩ := h2 ((QuotientGroup.mk' L) x)
    have hxL : x ^ 2 ^ k ∈ L := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [map_pow] using hk
    have hyH : x ^ 2 ^ k ∈ H := ⟨hxL, K.pow_mem hxK _⟩
    have hpow := (J.subgroupOf H).pow_index_mem (⟨x ^ 2 ^ k, hyH⟩ : ↥H)
    rw [hJindexH] at hpow
    refine ⟨k + 1, ?_⟩
    have hsq : x ^ 2 ^ (k + 1) = (x ^ 2 ^ k) ^ 2 := by
      rw [pow_succ, pow_mul]
    rw [hsq]
    exact hpow
  let P : Subgroup ↥K := CFSG.Open.pCore 2 ↥K
  have hPnotTop : ¬ J ≤ P.map K.subtype := by
    intro hle
    let eP : ↥P ≃* ↥(P.map K.subtype) :=
      Subgroup.equivMapOfInjective P K.subtype K.subtype_injective
    have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
    have hPbar2 : IsPGroup 2 ↥(P.map K.subtype) := hP2.of_equiv eP
    have hJ2 : IsPGroup 2 ↥J :=
      hPbar2.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hJnil : Group.IsNilpotent ↥J := hJ2.isNilpotent
    have hJsolv : Group.IsSolvable ↥J := inferInstance
    exact Group.IsPerfect.not_isSolvable ↥J hJsolv
  obtain ⟨hPJ, hPL⟩ := key P inferInstance hPnotTop
  have hNotLe : ¬ A ≤ pCoreOf 2 K := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAL
    intro hAle
    have haP : (a : Q) ∈ pCoreOf 2 K := hAle a.2.1
    have hmem : (a : Q) ∈ pCoreOf 2 K ⊓ L := ⟨haP, a.2.2⟩
    rw [show pCoreOf 2 K = P.map K.subtype from rfl, hPL] at hmem
    exact ha1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hAJ : ∃ a ∈ A, ∃ x ∈ J,
      ⁅a, x⁆ ∉ (CFSG.solvableRadical ↥K).map K.subtype := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAL
    let a0 : Q := a
    have ha0A : a0 ∈ A := a.2.1
    have ha0L : a0 ∈ L := a.2.2
    have ha0K : a0 ∈ K := hAK ha0A
    have ha0H : a0 ∈ H := ⟨ha0L, ha0K⟩
    have hnotcent : ¬ a0 ∈ Subgroup.centralizer (J : Set Q) := by
      intro hc
      have hmem : a0 ∈ L ⊓ Subgroup.centralizer (J : Set Q) := ⟨ha0L, hc⟩
      rw [hb.inf_centralizer_eq_bot] at hmem
      exact ha1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one'] at hnotcent
    push Not at hnotcent
    obtain ⟨x, hxJ, hxne⟩ := hnotcent
    refine ⟨a0, ha0A, x, hxJ, ?_⟩
    intro hmemR
    have hxH : x ∈ H := hJH hxJ
    have hcommJ : ⁅a0, x⁆ ∈ J := Subgroup.commutator_mem_commutator ha0H hxH
    have hmem : ⁅a0, x⁆ ∈ (CFSG.solvableRadical ↥K).map K.subtype ⊓ J :=
      ⟨hmemR, hcommJ⟩
    rw [show (CFSG.solvableRadical ↥K).map K.subtype ⊓ J = ⊥ from hRJ] at hmem
    exact hxne (Subgroup.mem_bot.mp hmem)
  have hII : UniquenessCase.PartTwo.ECaseII T A K :=
    CFSG.LocalAnalysis.WeakClosure81.eCaseII_of_normal_quasisimple hJK hJsubNorm hJq
      hK2 hRclosed hAK hAJ
  have hbK : b ∈ K := hAK hbA
  have hbPcore : b ∈ pCoreOf 2 K := by
    let x : ↥K := ⟨b, hbK⟩
    have hxc : ∀ m : ↥K, Commute m x := fun m =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp m.2)
    have hord : orderOf x = 2 := by
      rw [← orderOf_injective K.subtype K.subtype_injective x]
      exact hb2
    have hxnorm : (Subgroup.zpowers x).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc : Commute g (x ^ k) := (hxc g).zpow_right k
      rw [hc.eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hle : Subgroup.zpowers x ≤ CFSG.Open.pCore 2 ↥K :=
      le_sSup ⟨hxnorm, hxp⟩
    exact Subgroup.mem_map.mpr ⟨x, hle (Subgroup.mem_zpowers x), rfl⟩
  have hmQuot : E3.mQuot A (pCoreOf 2 K) ≤ 2 := by
    refine mQuot_le_of_card_le (n := 2) hA ?_ hbA hbPcore hb1
    rw [hcard]
    norm_num
  exact ⟨⟨by simpa [UniquenessCase.PartTwo.tA] using hTau, hSylOf, hNotLe,
    Or.inr hII⟩, hmQuot⟩

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
