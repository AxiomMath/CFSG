module

public import CFSG.Quasithin.H13.NQBlockOriginalSupplements
public import CFSG.Quasithin.H13.NQBlockPrimeResidualCenter
public import CFSG.Quasithin.SteinbergBQLocalReducedModule
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped Pointwise
open CFSG.Quasithin.BlueprintB2 (centerTorsion mem_centerTorsion_iff)

section General

variable {G : Type*} [Group G]

theorem map_subtype_centralizer_eq (B : Subgroup G) (X : Subgroup B) :
    (centralizer (X : Set B)).map B.subtype =
      B ⊓ centralizer ((X.map B.subtype : Subgroup G) : Set G) := by
  ext g
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine mem_inf.mpr ⟨b.2, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hb
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hb x hx)
  · intro hg
    obtain ⟨hgB, hgC⟩ := mem_inf.mp hg
    refine ⟨⟨g, hgB⟩, ?_, rfl⟩
    rw [mem_centralizer_iff] at hgC
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (hgC _ ⟨x, hx, rfl⟩)

theorem map_omegaOneCenterOf (B : Subgroup G) (p : ℕ) (Y : Subgroup B) :
    (omegaOneCenterOf p Y).map B.subtype = omegaOneCenterOf p (Y.map B.subtype) := by
  unfold omegaOneCenterOf
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨y, ⟨hyYC, hyp⟩, rfl⟩
    obtain ⟨hyY, hyC⟩ := mem_inf.mp hyYC
    refine ⟨mem_inf.mpr ⟨mem_map_of_mem _ hyY, ?_⟩, ?_⟩
    · rw [mem_centralizer_iff] at hyC ⊢
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hyC x hx)
    · simpa using congrArg Subtype.val hyp
  · rintro ⟨hgYC, hgp⟩
    obtain ⟨hgY, hgC⟩ := mem_inf.mp hgYC
    obtain ⟨y, hy, rfl⟩ := hgY
    refine ⟨y, ⟨mem_inf.mpr ⟨hy, ?_⟩, Subtype.ext (by simpa using hgp)⟩, rfl⟩
    rw [mem_centralizer_iff] at hgC ⊢
    intro x hx
    exact Subtype.ext (hgC _ ⟨x, hx, rfl⟩)

theorem commutator_eq_bot_iff_map_subtype (B : Subgroup G) (X Y : Subgroup B) :
    ⁅X, Y⁆ = ⊥ ↔ ⁅X.map B.subtype, Y.map B.subtype⁆ = ⊥ := by
  rw [← map_commutator, map_eq_bot_iff_of_injective _ B.subtype_injective]

theorem mem_normalizer_sup [Finite G] {A C : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hC : g ∈ normalizer (C : Set G)) :
    g ∈ normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
  have h1 : A ⊔ C ≤ (A ⊔ C).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => mem_comap.mpr (mem_sup_left ((mem_normalizer_iff.mp hA a).mp ha)))
      (fun c hc => mem_comap.mpr (mem_sup_right ((mem_normalizer_iff.mp hC c).mp hc)))
  exact h1 hk

theorem mem_omegaOneCenterOf_iff {p : ℕ} {Q : Subgroup G} {x : G} :
    x ∈ omegaOneCenterOf p Q ↔ x ∈ Q ∧ (∀ r ∈ Q, x * r = r * x) ∧ x ^ p = 1 := by
  constructor
  · intro hx
    obtain ⟨hxQ, hxC⟩ := mem_inf.mp (omegaOneCenterOf_le p Q hx)
    exact ⟨hxQ, fun r hr => (mem_centralizer_iff.mp hxC r hr).symm,
      pow_eq_one_of_mem_omegaOneCenterOf hx⟩
  · rintro ⟨hxQ, hxC, hxp⟩
    exact subset_omegaOneCenterOf hxQ (mem_centralizer_iff.mpr fun r hr => (hxC r hr).symm) hxp

end General

section ReducedModule

variable {G : Type} [Group G] [Finite G]

theorem reduced_module_of_normal_perfect {K T R : Subgroup G}
    (hTK : T ≤ normalizer (K : Set G)) (hT2 : IsPGroup 2 T) (hKp : ⁅K, K⁆ = K)
    (hsimp : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (hnab : ∃ a b : K ⧸ CFSG.pCore 2 K, a * b ≠ b * a)
    (hR : R = pCoreOf 2 (K ⊔ T)) (hUL : ⁅omegaOneCenterOf 2 (pCoreOf 2 K), K⁆ ≠ ⊥)
    (VK : Subgroup G) (hVK : VK = ⁅omegaOneCenterOf 2 (pCoreOf 2 K) ⊓ centralizer (R : Set G), K⁆) :
    VK ≠ ⊥ ∧ VK ≤ K ⊔ T ∧ VK ≤ (primeReducedAggregate ↥(K ⊔ T) 2).map (K ⊔ T).subtype ∧
      IsPrimeReduced 2 (VK.subgroupOf (K ⊔ T)) ∧ ⁅VK, K⁆ = VK ∧
      K ⊓ centralizer (VK : Set G) = pCoreOf 2 K ∧ (K ⊔ T) ⊓ centralizer (VK : Set G) = R ∧
      IsPrimeReduced 2 (primeReducedAggregate ↥(K ⊔ T) 2) ∧
      ⁅(primeReducedAggregate ↥(K ⊔ T) 2).map (K ⊔ T).subtype, K⁆ ≠ ⊥ ∧
      (K ⊔ T) ⊓ centralizer
        (((primeReducedAggregate ↥(K ⊔ T) 2).map (K ⊔ T).subtype : Subgroup G) : Set G) = R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKE : K ≤ K ⊔ T := le_sup_left
  have hTE : T ≤ K ⊔ T := le_sup_right
  have hKn : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKE).mpr (sup_le le_normalizer hTK)
  have hKmap : (K.subgroupOf (K ⊔ T)).map (K ⊔ T).subtype = K := map_subgroupOf_eq_of_le hKE
  have hKp' : ⁅K.subgroupOf (K ⊔ T), K.subgroupOf (K ⊔ T)⁆ = K.subgroupOf (K ⊔ T) := by
    apply map_injective (K ⊔ T).subtype_injective
    rw [map_commutator, hKmap, hKp]
  let eK : K.subgroupOf (K ⊔ T) ≃* K := subgroupOfEquivOfLe hKE
  let qK : (K.subgroupOf (K ⊔ T) ⧸ CFSG.pCore 2 (K.subgroupOf (K ⊔ T))) ≃*
      (K ⧸ CFSG.pCore 2 K) :=
    QuotientGroup.congr _ _ eK (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eK)
  have hsimp' : IsSimpleGroup (K.subgroupOf (K ⊔ T) ⧸ CFSG.pCore 2 (K.subgroupOf (K ⊔ T))) :=
    MulEquiv.isSimpleGroup qK
  have hnab' : ∃ a b : K.subgroupOf (K ⊔ T) ⧸ CFSG.pCore 2 (K.subgroupOf (K ⊔ T)),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨qK.symm a, qK.symm b, fun h => hab ?_⟩
    have h1 := congrArg qK h
    simpa using h1
  have hXL : IsPGroup 2 (↥(K ⊔ T) ⧸ K.subgroupOf (K ⊔ T)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (x : G) ∈ ((K ⊔ T : Subgroup G) : Set G) := x.2
    rw [coe_mul_of_right_le_normalizer_left K T hTK, Set.mem_mul] at hx
    obtain ⟨k, hk, t, ht, hkt⟩ := hx
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    have hxt : (QuotientGroup.mk x : ↥(K ⊔ T) ⧸ K.subgroupOf (K ⊔ T)) =
        QuotientGroup.mk ⟨t, hTE ht⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      have e : ((x⁻¹ * ⟨t, hTE ht⟩ : ↥(K ⊔ T)) : G) = t⁻¹ * k⁻¹ * t := by
        simp only [coe_mul, coe_inv]
        rw [← hkt]
        group
      rw [e]
      have h1 := (mem_normalizer_iff.mp (hTK (inv_mem ht)) k⁻¹).mp (inv_mem hk)
      rwa [inv_inv] at h1
    refine ⟨n, ?_⟩
    rw [hxt, ← QuotientGroup.mk_pow]
    have ht' : (⟨t, hTE ht⟩ : ↥(K ⊔ T)) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [ht', QuotientGroup.mk_one]
  have hU : ∀ x : ↥(K ⊔ T), x ∈ omegaOneCenterOf 2
      ((CFSG.pCore 2 ↥(K.subgroupOf (K ⊔ T))).map (K.subgroupOf (K ⊔ T)).subtype) ↔
      x ∈ (CFSG.pCore 2 ↥(K.subgroupOf (K ⊔ T))).map (K.subgroupOf (K ⊔ T)).subtype ∧
        (∀ r ∈ (CFSG.pCore 2 ↥(K.subgroupOf (K ⊔ T))).map (K.subgroupOf (K ⊔ T)).subtype,
          x * r = r * x) ∧ x ^ 2 = 1 := fun x => mem_omegaOneCenterOf_iff
  have hRQ : ((CFSG.pCore 2 ↥(K.subgroupOf (K ⊔ T))).map (K.subgroupOf (K ⊔ T)).subtype).map
      (K ⊔ T).subtype = pCoreOf 2 K := by
    have h1 := map_inSubgroup_pCore (K.subgroupOf (K ⊔ T)) 2
    rwa [hKmap] at h1
  have hPmap : (CFSG.pCore 2 ↥(K ⊔ T)).map (K ⊔ T).subtype = R := by
    rw [hR]
    rfl
  have hUL' : ⁅omegaOneCenterOf 2 ((CFSG.pCore 2 ↥(K.subgroupOf (K ⊔ T))).map
      (K.subgroupOf (K ⊔ T)).subtype), K.subgroupOf (K ⊔ T)⁆ ≠ ⊥ := by
    rw [Ne, commutator_eq_bot_iff_map_subtype, map_omegaOneCenterOf, hRQ, hKmap]
    exact hUL
  obtain ⟨V', hV'⟩ : ∃ V' : Subgroup ↥(K ⊔ T), V' = ⁅omegaOneCenterOf 2
      ((CFSG.pCore 2 ↥(K.subgroupOf (K ⊔ T))).map (K.subgroupOf (K ⊔ T)).subtype) ⊓
        centralizer ((CFSG.pCore 2 ↥(K ⊔ T) : Subgroup _) : Set ↥(K ⊔ T)),
      K.subgroupOf (K ⊔ T)⁆ := ⟨_, rfl⟩
  obtain ⟨hV1, hVe, hVn, -, hVL, hLCV, hCV⟩ :=
    SteinbergBQ.linear_normal_perfect_local_reduced_module (K.subgroupOf (K ⊔ T)) hKp' hnab' hXL
      rfl rfl hU rfl hV' hUL'
  have hOQ : omegaOneCenterOf 2 (pCoreOf 2 K) ≤ K ⊔ T :=
    ((omegaOneCenterOf_le 2 _).trans inf_le_left).trans ((map_subtype_le _).trans hKE)
  have hWmap : (omegaOneCenterOf 2 ((CFSG.pCore 2 ↥(K.subgroupOf (K ⊔ T))).map
      (K.subgroupOf (K ⊔ T)).subtype) ⊓ centralizer ((CFSG.pCore 2 ↥(K ⊔ T) : Subgroup _) :
        Set ↥(K ⊔ T))).map (K ⊔ T).subtype =
      omegaOneCenterOf 2 (pCoreOf 2 K) ⊓ centralizer (R : Set G) := by
    rw [map_inf_eq _ _ _ (K ⊔ T).subtype_injective, map_omegaOneCenterOf, hRQ,
      map_subtype_centralizer_eq, hPmap, ← inf_assoc, inf_eq_left.mpr hOQ]
  have hVmap : V'.map (K ⊔ T).subtype = VK := by
    rw [hV', map_commutator, hWmap, hKmap, hVK]
  have hVsub : VK.subgroupOf (K ⊔ T) = V' := by
    rw [← hVmap]
    exact comap_map_eq_self_of_injective (K ⊔ T).subtype_injective V'
  have hVKle : VK ≤ K ⊔ T := by
    rw [← hVmap]
    exact map_subtype_le _
  have hVred : IsPrimeReduced 2 V' := by
    refine ⟨hVn, hVe, ?_⟩
    let e1 : (↥(K ⊔ T) ⧸ centralizer (V' : Set ↥(K ⊔ T))) ≃*
        (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T)) := QuotientGroup.quotientMulEquivOfEq hCV
    have h1 := CFSG.LieType.SteinbergBR.pCore_map_equiv 2 e1
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at h1
    exact (map_eq_bot_iff_of_injective _ e1.injective).mp h1
  have hV0red := isPrimeReduced_primeReducedAggregate (E := ↥(K ⊔ T)) 2
  have hVV0 : V' ≤ primeReducedAggregate ↥(K ⊔ T) 2 := le_primeReducedAggregate hVred
  have hCV0 : centralizer ((primeReducedAggregate ↥(K ⊔ T) 2 : Subgroup _) : Set ↥(K ⊔ T)) =
      CFSG.pCore 2 ↥(K ⊔ T) := by
    refine le_antisymm ((centralizer_le hVV0).trans hCV.le) fun k hk => ?_
    rw [mem_centralizer_iff]
    intro v hv
    exact ((mem_centerTorsion_iff.mp (isPrimeReduced_le_centerTorsion_pCore hV0red hv)).2.1 k
      hk).symm
  have hVKV0 : VK ≤ (primeReducedAggregate ↥(K ⊔ T) 2).map (K ⊔ T).subtype := by
    rw [← hVmap]
    exact map_mono hVV0
  have hVKK : ⁅VK, K⁆ = VK := by
    have h1 := congrArg (Subgroup.map (K ⊔ T).subtype) hVL
    rwa [map_commutator, hVmap, hKmap] at h1
  refine ⟨?_, hVKle, hVKV0, by rw [hVsub]; exact hVred, hVKK, ?_, ?_, hV0red, ?_, ?_⟩
  · rw [← hVmap]
    exact fun h0 => hV1 ((map_eq_bot_iff_of_injective _ (K ⊔ T).subtype_injective).mp h0)
  · have h1 := congrArg (Subgroup.map (K ⊔ T).subtype) hLCV
    rw [map_inf_eq _ _ _ (K ⊔ T).subtype_injective, hKmap, map_subtype_centralizer_eq, hVmap,
      ← inf_assoc, inf_eq_left.mpr hKE, hRQ] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map (K ⊔ T).subtype) hCV
    rwa [map_subtype_centralizer_eq, hVmap, hPmap] at h1
  · intro h0
    apply hV1
    have h1 : ⁅VK, K⁆ ≤ ⁅(primeReducedAggregate ↥(K ⊔ T) 2).map (K ⊔ T).subtype, K⁆ :=
      commutator_mono hVKV0 le_rfl
    rw [h0, hVKK, le_bot_iff, ← hVmap] at h1
    exact (map_eq_bot_iff_of_injective _ (K ⊔ T).subtype_injective).mp h1
  · have h1 := congrArg (Subgroup.map (K ⊔ T).subtype) hCV0
    rwa [map_subtype_centralizer_eq, hPmap] at h1

end ReducedModule

variable {G : Type} [Group G] [Finite G]

theorem original_K_charTwo {T L M : Subgroup G} (h : QTNQ T L M) :
    QuasithinUnique.CharTwo (nqOriginalK T L ⊔ T) ∧ QuasithinUnique.CharTwo (nqOriginalK T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.eq_normalizer ▸ h.t_le)
  obtain ⟨-, hTK, -⟩ := original_K_supplement h
  have hRO := (original_radical_normalizer_centralizer_is_two_core h hR).1
  have hRne := (original_radical_normalizer_local_and_Thompson_failure h hR).1
  have hT : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [relIndex_top_right]
    exact h.sylow.2
  have hM0 := QuasithinUnique.charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot h.qtke.2.1 hT
    le_sup_right (hRO ▸ hRne)
  have hKn : ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hTK)
  exact ⟨hM0, QuasithinUnique.CharTwo.of_normal hM0 le_sup_left hKn⟩

theorem original_K_center_action
    {T L M : Subgroup G} (h : QTNQ T L M) :
    ⁅omegaOneCenterOf 2 (pCoreOf 2 (nqOriginalK T L)), nqOriginalK T L⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.eq_normalizer ▸ h.t_le)
  obtain ⟨hKL, hTK, -⟩ := original_K_supplement h
  obtain ⟨-, -, -, hKN, -, -, hVcK, hU1, -, -, -⟩ :=
    original_radical_supplements_share_simple_residual_and_internal_module h hR
  have hKp := (original_radical_supplement h.sylow.1 h.maximal_local.1.2.2.1
    (h.eq_normalizer ▸ h.t_le) h.maximal_local.1.2.1 hR).2.2.2.2.2.2.2.1
  have hKM : nqOriginalK T L ≤ M := hKL.trans h.l_le
  have hM0M : nqOriginalK T L ⊔ T ≤ M := sup_le hKM h.t_le
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  let T' : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hT' : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
  have hOT : pCoreOf 2 M ≤ T := by
    have h1 := T'.is_maximal' (T'.isPGroup'.to_sup_of_normal_right' hO2
      (hT' ▸ h.t_le.trans hMO)) le_sup_left
    rw [← hT', ← h1]
    exact le_sup_right
  have hQ2 : IsPGroup 2 (pCoreOf 2 (nqOriginalK T L)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  have hQK : pCoreOf 2 (nqOriginalK T L) ≤ nqOriginalK T L := map_subtype_le _
  have hP2 : IsPGroup 2 (pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L) : Subgroup G) := by
    have h1 := hQ2.to_sup_of_normal_right' hO2 ((hQK.trans hKM).trans hMO)
    rwa [sup_comm] at h1
  have hPM0 : pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L) ≤ nqOriginalK T L ⊔ T :=
    sup_le (hOT.trans le_sup_right) (hQK.trans le_sup_left)
  have hKQ : normalizer (nqOriginalK T L : Set G) ≤
      normalizer (pCoreOf 2 (nqOriginalK T L) : Set G) := by
    unfold pCoreOf
    exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hM0P : nqOriginalK T L ⊔ T ≤
      normalizer ((pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_sup (hMO (hM0M hg))
      (hKQ ((sup_le le_normalizer hTK) hg))
  have hVcO : ∀ v ∈ qtnqVc M, v ∈ pCoreOf 2 M ∧
      (∀ k ∈ pCoreOf 2 M, k * v = v * k) ∧ v ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxO, hxC, hxp⟩ := mem_centerTorsion_iff.mp (isPrimeReduced_le_centerTorsion_pCore
      (isPrimeReduced_primeReducedAggregate (E := ↥M) 2) hx)
    have hxO' : (x : G) ∈ pCoreOf 2 M := by
      unfold pCoreOf
      exact mem_map_of_mem _ hxO
    refine ⟨hxO', ?_, by simpa using congrArg Subtype.val hxp⟩
    intro k hk
    unfold pCoreOf at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact congrArg Subtype.val (hxC k' hk')
  have hQC : pCoreOf 2 (nqOriginalK T L) ≤ centralizer (qtnqVc M : Set G) := by
    rw [← hKN]
    refine inf_le_right.trans ?_
    rw [← h.centralizer_eq_radical]
    exact inf_le_right
  have hVcP : qtnqVc M ≤ omegaOneCenterOf 2 (pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L)) := by
    intro v hv
    obtain ⟨hvO, hvC, hvp⟩ := hVcO v hv
    refine subset_omegaOneCenterOf (mem_sup_left hvO) ?_ hvp
    have hPC : pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L) ≤ centralizer ({v} : Set G) := by
      refine sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hvC k hk)) ?_
      intro q hq
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (hQC hq) v hv).symm
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hPC hk)
  have hPK : ⁅omegaOneCenterOf 2 (pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L)),
      nqOriginalK T L⁆ ≠ ⊥ := by
    intro h0
    apply hU1
    rw [← hVcK, eq_bot_iff, ← h0]
    exact commutator_mono hVcP le_rfl
  have hKn : ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hTK)
  have hKmap : ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T)).map
      (nqOriginalK T L ⊔ T).subtype = nqOriginalK T L := map_subgroupOf_eq_of_le le_sup_left
  have hKp' : Group.IsPerfect ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T)) := by
    refine Subgroup.isPerfect_iff.mpr ?_
    apply map_injective (nqOriginalK T L ⊔ T).subtype_injective
    rw [map_commutator, hKmap, hKp]
  have hPn : ((pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L)).subgroupOf
      (nqOriginalK T L ⊔ T)).Normal := (normal_subgroupOf_iff_le_normalizer hPM0).mpr hM0P
  have hPmap : ((pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L)).subgroupOf
      (nqOriginalK T L ⊔ T)).map (nqOriginalK T L ⊔ T).subtype =
      pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L) := map_subgroupOf_eq_of_le hPM0
  have hQmap : ((CFSG.pCore 2 ↥((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T))).map
      ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T)).subtype).map
        (nqOriginalK T L ⊔ T).subtype = pCoreOf 2 (nqOriginalK T L) := by
    have h1 := map_inSubgroup_pCore ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T)) 2
    rwa [hKmap] at h1
  have hQP : (CFSG.pCore 2 ↥((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T))).map
      ((nqOriginalK T L).subgroupOf (nqOriginalK T L ⊔ T)).subtype ≤
      (pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L)).subgroupOf (nqOriginalK T L ⊔ T) := by
    intro y hy
    rw [mem_subgroupOf]
    have h1 : (y : G) ∈ pCoreOf 2 (nqOriginalK T L) := by
      rw [← hQmap]
      exact mem_map_of_mem _ hy
    exact mem_sup_right h1
  have hiff := prime_residual_subnormal_core_center_action
    (R := (pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L)).subgroupOf (nqOriginalK T L ⊔ T))
    hKn.isSubnormal (CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_isPerfect hKp')
    (hP2.comap_subtype : IsPGroup 2 ((pCoreOf 2 M ⊔ pCoreOf 2 (nqOriginalK T L)).subgroupOf
      (nqOriginalK T L ⊔ T))) hQP
  rw [commutator_eq_bot_iff_map_subtype, commutator_eq_bot_iff_map_subtype,
    map_omegaOneCenterOf, map_omegaOneCenterOf, hQmap, hPmap, hKmap] at hiff
  exact fun h0 => hPK (hiff.mp h0)

theorem original_K_faithful {T L M : Subgroup G} (h : QTNQ T L M) :
    quasithinIsFaithfulLocal T (nqOriginalK T L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.eq_normalizer ▸ h.t_le)
  have hloc := (original_radical_normalizer_local_and_Thompson_failure h hR).2.2.2.2.2.1
  have hKp := (original_radical_supplement h.sylow.1 h.maximal_local.1.2.2.1
    (h.eq_normalizer ▸ h.t_le) h.maximal_local.1.2.1 hR).2.2.2.2.2.2.2.1
  have hKc := (original_K_charTwo h).2
  have hKperf : Group.IsPerfect (nqOriginalK T L) := Subgroup.isPerfect_iff.mpr hKp
  have hno := CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_isPerfect (p := 2) hKperf
  refine ⟨hloc, fun N hNK hNn hN => ?_, (quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr hKc,
    original_K_center_action h⟩
  have hq : IsPGroup 2 (nqOriginalK T L ⧸ N.subgroupOf (nqOriginalK T L)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hN x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using hk
  have h1 := hno _ hq
  refine le_antisymm hNK fun x hx => ?_
  have h2 : (⟨x, hx⟩ : nqOriginalK T L) ∈ N.subgroupOf (nqOriginalK T L) := by
    rw [h1]
    exact mem_top _
  exact h2

theorem original_common_residual_is_faithful_and_has_exact_reduced_action_kernel
    {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) :
    quasithinIsFaithfulLocal T (nqOriginalK T L) ∧
      CFSG.IsCharacteristicP 2 ↥(nqOriginalK T L ⊔ T) ∧
      quasithinGenFitting (nqOriginalK T L) = pCoreOf 2 (nqOriginalK T L) ∧
      ⁅omegaOneCenterOf 2 (pCoreOf 2 (nqOriginalK T L)), nqOriginalK T L⁆ ≠ ⊥ ∧
      (∀ VK : Subgroup G, VK = ⁅omegaOneCenterOf 2 (pCoreOf 2 (nqOriginalK T L)) ⊓
          centralizer (R : Set G), nqOriginalK T L⁆ →
        VK ≠ ⊥ ∧
          VK ≤ (primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map
            (nqOriginalK T L ⊔ T).subtype ∧
          VK ≤ nqOriginalK T L ⊔ T ∧ IsPrimeReduced 2 (VK.subgroupOf (nqOriginalK T L ⊔ T)) ∧
          ⁅VK, nqOriginalK T L⁆ = VK ∧
          nqOriginalK T L ⊓ centralizer (VK : Set G) = pCoreOf 2 (nqOriginalK T L) ∧
          (nqOriginalK T L ⊔ T) ⊓ centralizer (VK : Set G) = R) ∧
      IsPrimeReduced 2 (primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2) ∧
      ⁅(primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map (nqOriginalK T L ⊔ T).subtype,
        nqOriginalK T L⁆ ≠ ⊥ ∧
      (nqOriginalK T L ⊔ T) ⊓ centralizer
        (((primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map
          (nqOriginalK T L ⊔ T).subtype : Subgroup G) : Set G) = R ∧
      T ⊓ centralizer
        (((primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map
          (nqOriginalK T L ⊔ T).subtype : Subgroup G) : Set G) = R ∧
      R = pCoreOf 2 (nqOriginalK T L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM0c, hKc⟩ := original_K_charTwo h
  have hV2 := original_K_center_action h
  have hRO := (original_radical_normalizer_centralizer_is_two_core h hR).1
  obtain ⟨-, hTK, -⟩ := original_K_supplement h
  obtain ⟨hRT, -, -, -, -, -, -, hKp, -⟩ := original_radical_supplement h.sylow.1
    h.maximal_local.1.2.2.1 (h.eq_normalizer ▸ h.t_le) h.maximal_local.1.2.1 hR
  obtain ⟨-, -, -, -, ⟨e, -⟩, -⟩ :=
    original_radical_supplements_share_simple_residual_and_internal_module h hR
  have hLtop : CFSG.IsCComponent (⊤ : Subgroup L) := by
    have h1 := subgroupOf_mem_cComp (cComp_mem_of_le h.maximal_local.1.2.1 le_rfl le_sup_left)
    rw [subgroupOf_self] at h1
    exact mem_cComp_top_iff_isCComponent.mp h1
  obtain ⟨hLs, a, b, hab⟩ := simple_radical_quotient_of_isCComponent_top hLtop
  have hKs : IsSimpleGroup (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) :=
    MulEquiv.isSimpleGroup e
  have hKnab : ∃ a b : nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L), a * b ≠ b * a := by
    refine ⟨e.symm a, e.symm b, fun h0 => hab ?_⟩
    have h1 := congrArg e h0
    simpa using h1
  have hred := reduced_module_of_normal_perfect hTK h.sylow.1 hKp hKs hKnab hRO hV2
  obtain ⟨-, -, -, -, -, -, -, hV0red, hV0K, hCV0⟩ := hred _ rfl
  refine ⟨original_K_faithful h, QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hM0c,
    (quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr hKc, hV2, fun VK hVK => ?_, hV0red, hV0K,
    hCV0, ?_, hRO⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hred VK hVK
    exact ⟨h1, h3, h2, h4, h5, h6, h7⟩
  · calc T ⊓ centralizer (((primeReducedAggregate ↥(nqOriginalK T L ⊔ T) 2).map
          (nqOriginalK T L ⊔ T).subtype : Subgroup G) : Set G) =
        T ⊓ ((nqOriginalK T L ⊔ T) ⊓ centralizer (((primeReducedAggregate
          ↥(nqOriginalK T L ⊔ T) 2).map (nqOriginalK T L ⊔ T).subtype : Subgroup G) : Set G)) := by
          rw [← inf_assoc, inf_eq_left.mpr (le_sup_right : T ≤ nqOriginalK T L ⊔ T)]
      _ = R := by rw [hCV0, inf_eq_right.mpr hRT]

end CFSG.Quasithin.H13.NQBlock
