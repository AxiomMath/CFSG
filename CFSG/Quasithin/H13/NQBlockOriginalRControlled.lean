module

public import CFSG.Quasithin.H13.NQBlockWitnessScalar
public import CFSG.Quasithin.H13.NQBlockThompsonTransport
public import CFSG.Quasithin.H13.NQBlockControlledThompson
public import CFSG.Quasithin.H13.NQCoreRadicalEscape
public import CFSG.Quasithin.H13.NQBlockFiveModelRigidity
public import CFSG.Quasithin.H13.NQBlockCharNormalizerEscape
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_R {T L M : Subgroup G} (h : QTNQ T L M)
    {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L) : 3 ≤ CFSG.pRank 2 R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := nqOriginalK T L with hKdef
  obtain ⟨-, -, -, -, hVK, -⟩ :=
    original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  set Ω := omegaOneCenterOf 2 (pCoreOf 2 K) with hΩdef
  set VK := ⁅Ω ⊓ centralizer (R : Set G), K⁆ with hVKdef
  obtain ⟨-, -, -, -, -, hKC, -⟩ := hVK VK rfl
  obtain ⟨hTK, -, -, -⟩ :=
    normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
  obtain ⟨-, hRKT, -⟩ := original_radical_supplements_share_simple_residual_and_internal_module h hR
  have hKTQ : K ⊔ T ≤ normalizer (pCoreOf 2 K : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hQKR : pCoreOf 2 K ≤ R := by
    rw [hRKT]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) hKTQ
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hKΩ : ∀ k ∈ K, ∀ w ∈ Ω, k * w * k⁻¹ ∈ Ω := fun k hk w hw =>
    conj_mem_omegaOneCenterOf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) hw
  have hVKΩ : VK ≤ Ω := by
    rw [hVKdef, Subgroup.commutator_le]
    intro w hw k hk
    have e : ⁅w, k⁆ = w * (k * w * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mem_inf.mp hw).1 (inv_mem (hKΩ k hk w (mem_inf.mp hw).1))
  have hVKel : CFSG.IsElementaryAbelian 2 ↥VK := isElementaryAbelian_of_le_omegaOneCenterOf hVKΩ
  have hVKR : VK ≤ R :=
    hVKΩ.trans (((omegaOneCenterOf_le 2 _).trans inf_le_left).trans hQKR)
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hKR : K ≤ normalizer (R : Set G) := by
    rw [hRKT]
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hKVK : K ≤ normalizer (VK : Set G) := by
    intro k hk
    have hkΩ : k ∈ normalizer (Ω : Set G) :=
      mem_normalizer_of_conj_mem (hKΩ k hk) fun w hw => by
        have := hKΩ k⁻¹ (K.inv_mem hk) w hw
        rwa [inv_inv] at this
    have hkC : k ∈ normalizer (centralizer (R : Set G) : Set G) :=
      mem_normalizer_of_conj_mem (fun c hc => conj_mem_centralizer_of_normalizer (hKR hk) hc)
        fun c hc => by
          have := conj_mem_centralizer_of_normalizer (hKR (K.inv_mem hk)) hc
          rwa [inv_inv] at this
    exact mem_normalizer_commutator (mem_normalizer_inf hkΩ hkC) (le_normalizer hk)
  set φ : ↥K →* MulAut ↥VK := VK.normalizerMonoidHom.comp (Subgroup.inclusion hKVK) with hφdef
  have hker : φ.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [MonoidHom.mem_ker, mem_pCore_iff_mem_pCoreOf, ← hKC]
    constructor
    · intro h1
      refine mem_inf.mpr ⟨k.2, mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h2 := congrArg (fun f : MulAut ↥VK => ((f ⟨v, hv⟩ : ↥VK) : G)) h1
      change (k : G) * v * (k : G)⁻¹ = v at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro h1
      ext v
      change (k : G) * v * (k : G)⁻¹ = v
      rw [← (mem_centralizer_iff.mp (mem_inf.mp h1).2) v v.2, mul_inv_cancel_right]
  have hcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≤ (Nat.card ↥VK).factorial := by
    rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← Nat.card_perm (α := ↥VK)]
    calc Nat.card ↥φ.range ≤ Nat.card (MulAut ↥VK) := Subgroup.card_le_card_group _
      _ ≤ Nat.card (Equiv.Perm ↥VK) :=
        Nat.card_le_card_of_injective (fun f : MulAut ↥VK => f.toEquiv)
          fun f g hfg => MulEquiv.ext fun x => congrFun (congrArg Equiv.toFun hfg) x
  obtain ⟨-, -, -, -, -, s, hs, hs5, -, hKcard⟩ := original_K_quotient_facts h
  have h60 : 60 ≤ s * (s ^ 2 - 1) / 2 := by
    have h1 : 24 ≤ s ^ 2 - 1 := by
      have : 25 ≤ s ^ 2 := by nlinarith
      omega
    have h2 : 120 ≤ s * (s ^ 2 - 1) := by nlinarith
    omega
  obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥VK).exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    rw [hKcard, hk] at hcard
    have hfac : (2 ^ k).factorial ≤ 24 := by
      interval_cases k <;> decide
    omega
  have hsub : CFSG.IsElementaryAbelian 2 ↥(VK.subgroupOf R) :=
    CFSG.IsElementaryAbelian.subgroupOf hVKR
  have hcardsub : Nat.card ↥(VK.subgroupOf R) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVKR).toEquiv, hk]
  exact hk3.trans (CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two _ hsub hcardsub)

omit [Finite G] in
theorem normalizer_le_normalizer_omegaOneCenter {R : Subgroup G} (J : Subgroup ↥R) :
    normalizer (J.map R.subtype : Set G) ≤
      normalizer ((CFSG.omegaOneCenter J).map R.subtype : Set G) := by
  have hfwd : ∀ g ∈ normalizer (J.map R.subtype : Set G),
      ∀ z ∈ (CFSG.omegaOneCenter J).map R.subtype, g * z * g⁻¹ ∈
        (CFSG.omegaOneCenter J).map R.subtype := by
    rintro g hg _ ⟨y, hy, rfl⟩
    obtain ⟨hyJ, hyc, hy2⟩ := mem_omegaOneCenter_iff'.mp hy
    obtain ⟨y', hy'J, hy'e⟩ := (mem_normalizer_iff.mp hg _).mp (mem_map_of_mem R.subtype hyJ)
    have hy'e' : (y' : G) = g * y * g⁻¹ := hy'e
    refine ⟨y', mem_omegaOneCenter_iff'.mpr ⟨hy'J, fun x hx => ?_, ?_⟩, hy'e⟩
    · obtain ⟨x', hx'J, hx'e⟩ := (mem_normalizer_iff''.mp hg _).mp (mem_map_of_mem R.subtype hx)
      have hx'e' : (x' : G) = g⁻¹ * x * g := hx'e
      apply Subtype.ext
      change (x : G) * y' = y' * x
      rw [hy'e']
      have h1 := congrArg Subtype.val (hyc x' hx'J)
      change (x' : G) * y = y * x' at h1
      rw [hx'e'] at h1
      calc (x : G) * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * x := by group
    · apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hy'e', conj_pow]
      have := congrArg Subtype.val hy2
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      change g * (y : G) ^ 2 * g⁻¹ = 1
      rw [this, mul_one, mul_inv_cancel]
  intro g hg
  refine mem_normalizer_of_conj_mem (hfwd g hg) fun z hz => ?_
  have := hfwd g⁻¹ (inv_mem hg) z hz
  rwa [inv_inv] at this

omit [Finite G] in
theorem le_normalizer_map_of_normal {V : Subgroup G} {D : Subgroup ↥V} (hD : D.Normal) :
    V ≤ normalizer (D.map V.subtype : Set G) := by
  have hfwd : ∀ v ∈ V, ∀ z ∈ D.map V.subtype, v * z * v⁻¹ ∈ D.map V.subtype := by
    rintro v hv _ ⟨d, hd, rfl⟩
    exact ⟨⟨v, hv⟩ * d * ⟨v, hv⟩⁻¹, hD.conj_mem d hd ⟨v, hv⟩, rfl⟩
  intro v hv
  refine mem_normalizer_of_conj_mem (hfwd v hv) fun z hz => ?_
  have := hfwd v⁻¹ (inv_mem hv) z hz
  rwa [inv_inv] at this

theorem originalRControlledThompson_of
    (hsing : NQCore.StmtOriginalWitnessSingleton) : OriginalRControlledThompson := by
  intro G _ _ T L M h R hR
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm := three_le_pRank_R h hR
  refine ⟨hm, ?_⟩
  obtain ⟨p, hp, hp5, X, -, hXc, hXN, hXno, hexp, hrk, hX2, -, hW, hirr, -, -⟩ :=
    NQRigid.configuration_centralizer_conjugate_rigidity_witness h
  have : Fact p.Prime := ⟨hp⟩
  have hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X) := fun g =>
    ⟨1, by rw [pow_one, ← hexp]; exact Monoid.pow_exponent_eq_one g⟩
  have hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1 := by
    obtain ⟨f, ⟨l, hlL, rfl⟩, hf⟩ := NQCore.exists_ne_one_of_irreducible hp
      (fun w => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
        rw [← QuotientGroup.mk_pow, ← hexp, Monoid.pow_exponent_eq_one, QuotientGroup.mk_one])
      hW {f | ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l = f}
      (fun Y hY => hirr Y fun l hl y hy => hY _ ⟨l, hl, rfl⟩ y hy)
    exact ⟨l, hlL, hf⟩
  have hU := hsing G T L M h p X hp hp5 hXN hXc hX2 hXno hXA hexp hrk hW hLW
    (fun Y hY => hirr Y hY)
  obtain ⟨-, -, hR2, -, -, -, hVs, -, h3, hSyl, -, hVc⟩ :=
    radical_witness_product h hR hp hp5 hXN hXc hXA
  have : Group.IsSolvable ↥(X ⊔ R) := hVs
  set V := X ⊔ R with hVdef
  set Q := pCoreOf 2 V with hQdef
  have hRV : R ≤ V := le_sup_right
  have hQR : Q ≤ R := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
  obtain ⟨-, -, -, -, -, -, hKTR, -⟩ := original_radical_normalizer_local_and_Thompson_failure h hR
  have hTR : T ≤ normalizer (R : Set G) := le_sup_right.trans hKTR
  have hctrl : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → V ≤ normalizer (C : Set G) →
      T ≤ normalizer (C : Set G) → normalizer (C : Set G) ≤ M := by
    intro C hCR hC1 hVC hTC
    have hloc : IsTwoLocal (normalizer (C : Set G)) := ⟨C, hC1, hR2.to_le hCR, rfl⟩
    obtain ⟨M', hM'⟩ := Set.Finite.exists_maximal
      (s := {Y : Subgroup G | IsTwoLocal Y ∧ normalizer (C : Set G) ≤ Y}) (Set.toFinite _)
      ⟨_, hloc, le_rfl⟩
    have hM'max : quasithinIsMaxTwoLocal M' :=
      ⟨hM'.1.1, fun Y hY hMY => le_antisymm (hM'.2 ⟨hY, hM'.1.2.trans hMY⟩ hMY) hMY⟩
    have hXT : X ⊔ T ≤ M' := (sup_le (le_sup_left.trans hVC) hTC).trans hM'.1.2
    rw [← hU.2.2 M' hM'max hXT]
    exact hM'.1.2
  obtain ⟨hchar, hlow, hint⟩ :=
    CFSG.Quasithin.SteinbergBK.higher_elementary_thompson_intersections_and_central_involutions
      (S := ↥R) hR2
  have hcharT : ∀ C : Subgroup ↥R, C.Characteristic → T ≤ normalizer (C.map R.subtype : Set G) :=
    fun C _ => hTR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic C)
  by_cases hJQ : nqHigherThompson R 0 ≤ Q
  ·
    refine ⟨0, Nat.zero_le _, hctrl _ (map_subtype_le _) ?_ ?_ (hcharT _ (hchar 0).1)⟩
    · intro h0
      apply (hlow 0 0 le_rfl (by omega)).1
      rwa [nqHigherThompson, Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective] at h0
    · set R' : Subgroup ↥R := Q.subgroupOf R with hR'def
      have hJR' : CFSG.higherElemThompson (↥R) 0 ≤ R' := fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hJQ (mem_map_of_mem R.subtype hx))
      obtain ⟨-, -, heq, -⟩ := hint 0 (by omega) R' hJR'
      have hR'2 : IsPGroup 2 ↥R' := hR2.to_subgroup R'
      obtain ⟨hchar', -, -⟩ :=
        CFSG.Quasithin.SteinbergBK.higher_elementary_thompson_intersections_and_central_involutions
          (S := ↥R') hR'2
      set e := Subgroup.subgroupOfEquivOfLe hQR with hedef
      have : ((CFSG.higherElemThompson (↥R') 0).map e.toMonoidHom).Characteristic :=
        characteristic_map_mulEquiv e (hchar' 0).1
      have hJeq : ((CFSG.higherElemThompson (↥R') 0).map e.toMonoidHom).map Q.subtype =
          nqHigherThompson R 0 := by
        rw [nqHigherThompson, ← heq, Subgroup.map_map, Subgroup.map_map]
        rfl
      rw [← hJeq]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 V).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  ·
    obtain ⟨A, hA, hAQ⟩ : ∃ A ∈ CFSG.higherElemThompsonFamily (↥R) 0, ¬ A.map R.subtype ≤ Q := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      apply hJQ
      rw [nqHigherThompson, CFSG.higherElemThompson, (Subgroup.gc_map_comap R.subtype).l_sSup]
      exact iSup₂_le fun A hA => hall A hA
    obtain ⟨hAel, hAcard⟩ := (CFSG.mem_higherElemThompsonFamily_iff 0 A).mp hA
    set A' := A.map R.subtype with hA'def
    have hA'R : A' ≤ R := map_subtype_le A
    have hA'el : CFSG.IsElementaryAbelian 2 ↥A' := CFSG.IsElementaryAbelian.map R.subtype
    have hA'2 : ∀ a ∈ A', a ^ 2 = 1 := fun a ha =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A') a ha
    obtain ⟨hidx, hgen⟩ := witness_elementary h hR hp hp5 hXN hXc hXA hW hLW hA'R hA'2 hAQ
    have hR2V : IsPGroup 2 ↥(R.subgroupOf V) :=
      hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRV).symm
    have hRodd : ¬ 2 ∣ (R.subgroupOf V).index := hSyl.2.2
    set S : Sylow 2 ↥V := hR2V.toSylow hRodd with hSdef
    have hScoe : (S : Subgroup ↥V) = R.subgroupOf V := IsPGroup.toSylow_coe hR2V hRodd
    set e' : ↥(S : Subgroup ↥V) ≃* ↥R :=
      (MulEquiv.subgroupCongr hScoe).trans (Subgroup.subgroupOfEquivOfLe hRV) with he'def
    have he' : ∀ x : ↥(S : Subgroup ↥V), ((e' x : ↥R) : G) = ((x : ↥V) : G) := fun _ => rfl
    have hcharV : IsCharacteristicP 2 ↥V :=
      QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hVc
    have hmS : CFSG.pRank 2 ↥(S : Subgroup ↥V) = CFSG.pRank 2 ↥R := pRank_mulEquiv e' 2
    set A'' : Subgroup ↥V := A'.subgroupOf V with hA''def
    have hA'V : A' ≤ V := hA'R.trans hRV
    have hA''el : CFSG.IsElementaryAbelian 2 ↥A'' := CFSG.IsElementaryAbelian.subgroupOf hA'V
    have hA''m : Nat.card ↥A'' = 2 ^ CFSG.pRank 2 ↥(S : Subgroup ↥V) := by
      rw [hmS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'V).toEquiv, hA'def,
        Subgroup.card_map_of_injective R.subtype_injective, hAcard, Nat.sub_zero]
    have hpc : CFSG.pCore 2 ↥V = Q.subgroupOf V := by
      ext v
      rw [Subgroup.mem_subgroupOf, hQdef, ← mem_pCore_iff_mem_pCoreOf]
    have hA''Q : (A'' ⊓ CFSG.pCore 2 ↥V).relIndex A'' = 2 := by
      have e1 : A'' ⊓ CFSG.pCore 2 ↥V = (A' ⊓ Q).subgroupOf V := by
        rw [hpc]
        ext v
        simp only [hA''def, mem_inf, Subgroup.mem_subgroupOf]
      rw [e1, hA''def, Subgroup.relIndex_subgroupOf hA'V]
      exact hidx
    have hgen' : normalClosure (A'' : Set ↥V) ⊔ (S : Subgroup ↥V) = ⊤ := by
      set N' := normalClosure (A'' : Set ↥V) ⊔ (S : Subgroup ↥V) with hN'def
      have hNC : closure {g | ∃ v ∈ V, ∃ a ∈ A', g = v * a * v⁻¹} ≤ N'.map V.subtype := by
        rw [closure_le]
        rintro _ ⟨v, hv, a, ha, rfl⟩
        refine ⟨⟨v, hv⟩ * ⟨a, hA'V ha⟩ * ⟨v, hv⟩⁻¹, mem_sup_left ?_, rfl⟩
        exact (normalClosure_normal (s := (A'' : Set ↥V))).conj_mem _
          (subset_normalClosure (Subgroup.mem_subgroupOf.mpr ha)) _
      have hRN : R ≤ N'.map V.subtype := fun r hr =>
        ⟨⟨r, hRV hr⟩, mem_sup_right (by rw [hScoe]; exact Subgroup.mem_subgroupOf.mpr hr), rfl⟩
      have hVN : V ≤ N'.map V.subtype := sup_le (hgen.trans (sup_le hNC hRN)) hRN
      rw [eq_top_iff]
      intro v _
      obtain ⟨v', hv', hvv'⟩ := hVN v.2
      rwa [show v = v' from Subtype.ext hvv'.symm]
    obtain ⟨-, -, -, -, -, -, -, hDn, -⟩ :=
      QRC.three_free_solvable_rank_one_step_normalizes_near_maximal_Thompson_center hcharV h3 S
        (by rw [hmS]; omega) A'' hA''el hA''m hA''Q hgen'
    set E1 := (CFSG.higherElemThompsonOmega (↥R) 1).map R.subtype with hE1def
    have hE1eq : ((CFSG.higherElemThompsonOmega (↥(S : Subgroup ↥V)) 1).map
        (S : Subgroup ↥V).subtype).map V.subtype = E1 := by
      rw [hE1def, ← map_higherElemThompsonOmega e' 1, Subgroup.map_map, Subgroup.map_map]
      rfl
    have hVE1 : V ≤ normalizer (E1 : Set G) := by
      rw [← hE1eq]
      exact le_normalizer_map_of_normal hDn
    have hE1ne : E1 ≠ ⊥ := by
      intro h0
      apply (hlow 1 1 le_rfl (by omega)).2.2.2.2.2.2.2
      rwa [hE1def, Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective] at h0
    refine ⟨1, le_rfl, (normalizer_le_normalizer_omegaOneCenter _).trans
      (hctrl E1 (map_subtype_le _) hE1ne hVE1 (hcharT _ (hchar 1).2))⟩

end CFSG.Quasithin.H13.NQBlock
