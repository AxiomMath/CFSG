module

public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec11.Item116
public import CFSG.RankThree.PartTwo.Sec11.Item119

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne.EmbeddingFixedResidual

variable {G : Type} [Group G] [Finite G]

theorem c_mem_of_hyp91 {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R : Subgroup G}
    (h : Sec9.Hyp91 G A c L a R) : c ∈ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  obtain ⟨Q, hQ⟩ := h.isSylowOf
  have hcH : c ∈ H := Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hZ : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc3, pow_one])
  have hN : (Subgroup.comap H.subtype (Subgroup.zpowers c)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.zpowers_le.mpr hcH)).mpr le_rfl
  have hle := @IsPGroup.le_sylow_of_normal 3 H _ _ hN (hZ.comap_subtype (K := H)) Q
  rw [← hQ]
  exact ⟨⟨c, hcH⟩, hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c)), rfl⟩

theorem c_mem_thetaQuotCentralizer {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c) :
    c ∈ Sec4.thetaQuotCentralizer L := by
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcN, fun l hl => ?_⟩
  rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLc hl), mul_inv_cancel_right,
    inv_mul_cancel]
  exact Subgroup.one_mem _

theorem Sec11Data.c_mem_zpowers_s {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g) :
    c ∈ Subgroup.zpowers s := by
  rw [← h.inf_centralizer_eq]
  exact ⟨c_mem_of_hyp91 h.toHyp91, c_mem_thetaQuotCentralizer h.mem_thetaComponentsAt⟩

theorem Sec11Std.a_facts {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    (h : Sec11Std G A c L a R Y) :
    ∃ haN : a ∈ Subgroup.normalizer (L : Set G), a ^ 3 = 1 ∧
      Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥ ∧
      IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) := by
  have haN := h.toHyp81.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hτ3 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨hZ, hQ, -⟩ := fixedPoints_facts_of_isList1016 h.isList1016 hτ3
    h.toHyp81.not_isInnerAut_induced
  exact ⟨haN, ha3, hZ, hQ⟩

theorem Sec11Std.d_mem_sec11K {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) :
    d ∈ sec11K L a := by
  obtain ⟨haN, ha3, -, hQ⟩ := h.a_facts
  have hAe := h.mem_partTwoF.1
  have hdAL : d ∈ A ⊓ L := by
    rw [hdL]
    exact Subgroup.mem_zpowers d
  exact mem_sec11K_of_pow_eq_one haN ha3 hQ.1
    ⟨hdAL.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨d, hdAL.1⟩ ⟨a, h.a_mem⟩))⟩
    (k := 1) (by rw [pow_one]; exact hAe.2 d hdAL.1)

theorem Sec11Std.mem_normalizer_Y {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) (hK1 : sec11K L a ≠ ⊥) {t : G}
    (htN : t ∈ Subgroup.normalizer (L : Set G)) (hta : t * a = a * t) :
    t ∈ Subgroup.normalizer (Y : Set G) := by
  have htC : t ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hta)
  have htM : t ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp htN y).mp hy1,
        (Subgroup.mem_normalizer_iff.mp htC y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp htN y).mpr hy1,
        (Subgroup.mem_normalizer_iff.mp htC y).mpr hy2⟩
  have htK : t ∈ Subgroup.normalizer (sec11K L a : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ htM
  have hYt : Y.map (MulAut.conj t).toMonoidHom ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj t) h.mem_thetaComponentsAt_Y
    have h2 : (MulAut.conj t) a = a := by
      rw [MulAut.conj_apply, hta, mul_inv_cancel_right]
    rwa [h2] at h1
  have hKYt : sec11K L a ≤ Y.map (MulAut.conj t).toMonoidHom := by
    intro k hk
    have h1 : t⁻¹ * k * t ∈ sec11K L a := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htK) k).mp hk
      rwa [inv_inv] at this
    refine ⟨t⁻¹ * k * t, h.sec11K_le h1, ?_⟩
    change t * (t⁻¹ * k * t) * t⁻¹ = k
    group
  have hYeq := eq_of_perfect_le_of_mem_thetaComponentsAt Nat.prime_three hYt
    h.mem_thetaComponentsAt_Y hK1 (Sec6.isPerfect_inSubgroup_perfectResidual _) hKYt h.sec11K_le
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hYeq

theorem mem_thetaComponentsIn_sec11K_inf {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} (h : Sec11Std G A c L a R Y) :
    sec11K L a ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
  set K := sec11K L a with hK
  obtain ⟨haN, ha3, hZ, hQ⟩ := h.a_facts
  obtain ⟨hLc, hL'⟩ := mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt
  set Z := Y ⊓ Subgroup.centralizer ({c} : Set G) with hZdef
  have hKZ : K ≤ Z := le_inf h.sec11K_le ((sec11K_le L a).trans hLc)
  set T := K.subgroupOf Z with hT
  set e : T ≃* K := Subgroup.subgroupOfEquivOfLe hKZ with he
  refine mem_thetaComponentsIn_iff.mpr ⟨hKZ, ?_, ?_, ?_⟩
  · have hKp : Group.IsPerfect K := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · set ι : Z →* Subgroup.centralizer ({c} : Set G) :=
      Z.subtype.codRestrict _ (fun z => z.2.2) with hι
    set MD := (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap ι with hMD
    have hMDsn : MD.IsSubnormal := hL'.2.1.comap ι
    have hTMD : T ≤ MD := by
      intro t ht
      rw [hT, Subgroup.mem_subgroupOf] at ht
      rw [hMD, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact sec11K_le L a ht
    have hTn : (T.subgroupOf MD).Normal := by
      constructor
      intro t ht m
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
      have hmL : ((m : Z) : G) ∈ L := m.2
      have hmM : ((m : Z) : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) :=
        ⟨hmL, Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
          (m : Z).2.1⟩
      have := GroupTheory.conj_mem_inSubgroup_perfectResidual hmM ht
      simpa [hK, sec11K] using this
    exact Subgroup.IsSubnormal.trans hTMD hTn.isSubnormal hMDsn
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three e)).symm (isQuasisimple_sec11K_quotient haN ha3 hQ hZ)

@[expose] def FieldCentRigid : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c t : G),
    KFacts.InducesStdKind Y c .field → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    t ∈ Subgroup.normalizer (Y : Set G) → (∃ k : ℕ, t ^ 3 ^ k = 1) → t * c = c * t →
    (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) →
      ∃ i : ℕ, t * c ^ i ∈ Sec4.thetaQuotCentralizer Y

theorem eq_one_of_mem_zpowers_s {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R Y : Subgroup G} {d x s r g : G} (h : Sec11Data G A c L a R Y d x s r g)
    (hf : KFacts.InducesStdKind Y c .field) {u : G} (hus : u ∈ Subgroup.zpowers s)
    (huY : u ∈ Sec4.thetaQuotCentralizer Y) : u = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcs := h.c_mem_zpowers_s
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one
  have hsR : s ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  set S := Subgroup.zpowers s with hS
  set Z := (S ⊓ Sec4.thetaQuotCentralizer Y).subgroupOf S with hZ
  set C' := (Subgroup.zpowers c).subgroupOf S with hC'
  have hS3 : IsPGroup 3 S := h.isSylowOf.isPGroup.to_le (Subgroup.zpowers_le.mpr hsR)
  by_contra hu1
  have hZ3 : IsPGroup 3 Z := hS3.to_subgroup _
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have : (⟨u, hus⟩ : S) ∈ Z := Subgroup.mem_subgroupOf.mpr ⟨hus, huY⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hu1 (congrArg Subtype.val this)
  have h3 : 3 ∣ Nat.card Z := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ3
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hZne
      rw [pow_zero] at hn
      exact Subgroup.eq_bot_of_card_eq Z hn
    rw [hn]
    exact dvd_pow_self 3 hn0
  have hC'3 : Nat.card C' = 3 := by
    rw [hC', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcs)).toEquiv,
      Nat.card_zpowers, hc3]
  have hle : C' ≤ Z := (IsCyclic.subgroup_le_iff_card_dvd).mpr (hC'3 ▸ h3)
  have hcZ : (⟨c, hcs⟩ : S) ∈ Z := hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c))
  have hcY : c ∈ Sec4.thetaQuotCentralizer Y := (Subgroup.mem_subgroupOf.mp hcZ).2
  obtain ⟨hcN, hout⟩ := KFacts.InducesStdKind.inducesOuterTheta Y hf (by decide)
  apply hout
  obtain ⟨⟨c', hc'N⟩, hc'1, hc'c⟩ := hcY
  have hcc' : (⟨c', hc'N⟩ : Subgroup.normalizer (Y : Set G)) = ⟨c, hcN⟩ := Subtype.ext hc'c
  rw [hcc'] at hc'1
  exact ⟨1, by rw [map_one]; exact hc'1.symm⟩

theorem commutator_mem_thetaQuotCentralizer_of_commute {L : Subgroup G} {y z : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hyz : (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) ⟨y, hy⟩ *
        (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) ⟨z, hz⟩ =
      (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) ⟨z, hz⟩ *
        (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) ⟨y, hy⟩) :
    y * z * y⁻¹ * z⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
  refine ⟨⟨y, hy⟩ * ⟨z, hz⟩ * (⟨y, hy⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
    (⟨z, hz⟩ : Subgroup.normalizer (L : Set G))⁻¹, MonoidHom.mem_ker.mpr ?_, rfl⟩
  change (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L)
    (⟨y, hy⟩ * ⟨z, hz⟩ * (⟨y, hy⟩ : Subgroup.normalizer (L : Set G))⁻¹ *
      (⟨z, hz⟩ : Subgroup.normalizer (L : Set G))⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyz]
  group

theorem Sec11Data.closure_rs_le_normalizer (h45 : Sec4.Item4_5) (h113 : Item113)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({r, s} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G) := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcA := h.mem_A
  have haA := h.a_mem
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) h.ne_one
  have hRc := le_centralizer_of_le_normalizer_zpowers hc3 h.isSylowOf.isPGroup h.isSylowOf.le
  have hRL := le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp (hexp c hcA)
    h.ne_one h.isSylowOf.isPGroup hRc L h.mem_thetaComponentsAt
  have hRA : R ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_eq_closure (h113 G A c L a R Y h.toSec11Std).1
  have hrR : r ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  have hsR : s ∈ R := by
    rw [h.R_eq]
    exact Subgroup.subset_closure (by simp)
  have haR : a ∈ R := by
    have : Subgroup.closure ({r, s} : Set G) ≤ R := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      exacts [hrR, hsR]
    exact this h.a_mem_closure
  set ρ := (Sec4.thetaQuotMulAut L).comp (Sec4.compAction L) with hρ
  have hsC : s ∈ Sec4.thetaQuotCentralizer L := by
    have h1 : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    rw [← h.inf_centralizer_eq] at h1
    exact h1.2
  have hρs : ρ ⟨s, hRL hsR⟩ = 1 := by
    obtain ⟨⟨s', hs'N⟩, hs'1, hs's⟩ := hsC
    have : (⟨s', hs'N⟩ : Subgroup.normalizer (L : Set G)) = ⟨s, hRL hsR⟩ := Subtype.ext hs's
    rw [this] at hs'1
    exact hs'1
  set M : Subgroup G := ((Subgroup.centralizer ({ρ ⟨r, hRL hrR⟩} : Set _)).comap ρ).map
    (Subgroup.normalizer (L : Set G)).subtype with hM
  have hrM : r ∈ M := ⟨⟨r, hRL hrR⟩, Subgroup.mem_centralizer_singleton_iff.mpr rfl, rfl⟩
  have hsM : s ∈ M := ⟨⟨s, hRL hsR⟩, Subgroup.mem_centralizer_singleton_iff.mpr (by
    rw [hρs, one_mul, mul_one]), rfl⟩
  have haM : a ∈ M := by
    have : Subgroup.closure ({r, s} : Set G) ≤ M := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      exacts [hrM, hsM]
    exact this h.a_mem_closure
  obtain ⟨⟨a', ha'N⟩, ha'M, ha'a⟩ := haM
  have ha'eq : (⟨a', ha'N⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, hRL haR⟩ := Subtype.ext ha'a
  rw [ha'eq] at ha'M
  have hra : ρ ⟨r, hRL hrR⟩ * ρ ⟨a, hRL haR⟩ = ρ ⟨a, hRL haR⟩ * ρ ⟨r, hRL hrR⟩ :=
    (Subgroup.mem_centralizer_singleton_iff.mp ha'M).symm
  have hsa : ρ ⟨s, hRL hsR⟩ * ρ ⟨a, hRL haR⟩ = ρ ⟨a, hRL haR⟩ * ρ ⟨s, hRL hsR⟩ := by
    rw [hρs, one_mul, mul_one]
  have key : ∀ y ∈ ({r, s} : Set G), y * a * y⁻¹ ∈ Subgroup.closure ({c, a} : Set G) := by
    intro y hy
    have hyR : y ∈ R := by
      rcases hy with rfl | rfl
      exacts [hrR, hsR]
    have hya : ρ ⟨y, hRL hyR⟩ * ρ ⟨a, hRL haR⟩ = ρ ⟨a, hRL haR⟩ * ρ ⟨y, hRL hyR⟩ := by
      rcases hy with rfl | rfl
      exacts [hra, hsa]
    have h1 := commutator_mem_thetaQuotCentralizer_of_commute (hRL hyR) (hRL haR) hya
    have h2 : y * a * y⁻¹ * a⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRA hyR) a).mp haA) (A.inv_mem haA)
    have h3 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer h2 h1
    rw [h.sectionCentralizer_eq] at h3
    have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h3)
      (Subgroup.subset_closure (by simp))
  rw [Subgroup.closure_le]
  intro y hy
  have hyR : y ∈ R := by
    rcases hy with rfl | rfl
    exacts [hrR, hsR]
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hle : Subgroup.closure ({c, a} : Set G) ≤
      (Subgroup.closure ({c, a} : Set G)).comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    rcases hw with hw | hw <;> rw [hw]
    · change y * c * y⁻¹ ∈ _
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hRc hyR), mul_inv_cancel_right]
      exact Subgroup.subset_closure (by simp)
    · exact key y hy
  exact hle hz

end CFSG.RankThree.PartTwo.Sec11
