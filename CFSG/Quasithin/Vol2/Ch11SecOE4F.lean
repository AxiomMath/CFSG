module

public import CFSG.Quasithin.Vol2.Ch11SecOE4B
public import CFSG.Quasithin.Vol2.Ch11SecOE4E
public import CFSG.Quasithin.Vol2.GoldschmidtCor332
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Aut

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE4

open Subgroup CFSG.Quasithin
open CFSG.Open (pCoreOf quasithinIsSylowTwo quasithinIsMaxTwoLocal quasithinIsMaximalLocal
  quasithinIsFaithfulLocal)
open CFSG.Quasithin.H13 (reducedAggregate)
open CFSG.LieType.BorelTits (pCoreOf_le)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_five_of_homocyclic {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hA : QuasithinUnique.Vol2Native.A36CoreCat L) (hq : ¬ CFSG.IsQuasisimple ↥L)
    {D : Subgroup G} (eL : (↥D ⧸ CFSG.pCore 2 ↥D) ≃* ↥L) {p e : ℕ} (he : 1 < e)
    (φ : ↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) ≃*
      (Multiplicative (ZMod (p ^ e)) × Multiplicative (ZMod (p ^ e)))) : p ≠ 5 := by
  rintro rfl
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPe := CFSG.LieType.SteinbergBR.pCore_map_equiv 5 eL
  let φ' : ↥(CFSG.pCore 5 ↥L) ≃*
      (Multiplicative (ZMod (5 ^ e)) × Multiplicative (ZMod (5 ^ e))) :=
    ((MulEquiv.subgroupCongr hPe).symm.trans
      ((CFSG.pCore 5 (↥D ⧸ CFSG.pCore 2 ↥D)).equivMapOfInjective eL.toMonoidHom
        eL.injective).symm).trans φ
  obtain ⟨hcases, -, hext⟩ := hA
  rcases hcases with hc | h3 | h4
  · exact hq hc.1
  ·
    obtain ⟨q, hq', -, -, ⟨ψ⟩, -⟩ := h3
    have : NeZero q := ⟨hq'.ne_zero⟩
    have hcardP : Nat.card ↥(CFSG.pCore 5 ↥L) = 5 ^ e * 5 ^ e := by
      rw [Nat.card_congr φ'.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card]
    have hcardF : Nat.card ↥(CFSG.fittingSubgroup ↥L) = q ^ 2 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hdvd : 5 ^ e * 5 ^ e ∣ q ^ 2 :=
      hcardP ▸ hcardF ▸ Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting ↥L 5)
    have h5q : 5 ∣ q := h5.out.dvd_of_dvd_pow
      ((dvd_pow_self 5 (by omega : e ≠ 0)).mul_right _ |>.trans hdvd)
    have hq5 : q = 5 := ((Nat.prime_dvd_prime_iff_eq h5.out hq').mp h5q).symm
    rw [hq5, ← pow_add] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 5)).mp hdvd
    omega
  · exact false_of_isSL2_five_of_homocyclic h4.2.2.1 (hext (Or.inr h4)) he φ'

theorem exists_isHStar_of_perfect
    (h211 : H13.U3.UniqueThreeCaseModelReduction)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : QuasithinUnique.quasithinIsQTKECat G) {T M L : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) (hTM : T ≤ M) (hLM : L ≤ M)
    (hL1 : L ≠ ⊥) (hLperf : ⁅L, L⁆ = L) : ∃ H : Subgroup G, IsHStar T M H := by
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  have huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → T ≤ M' → M' = M := by
    intro M' hM' hTM'
    by_contra hne
    exact hno (H13.exists_isHStar_of hM hM' hTM' hne)
  have hset : QuasithinUnique.UniqueSetting G T M :=
    { simple := hs
      nonabelian := hnab
      qtke := QuasithinUnique.qtkeCore_of_cat hnab hK
      sylow := H13.U3.isSylowTwoOf_top_of_quasithin hT
      maxLocal := hM
      le := hTM
      unique := huniq }
  have hsolvG : H13.Cor332.TwoLocalsSolvable G := by
    rcases h211 G T M hset with hB | hS
    · exact H13.Cor332.twoLocalsSolvable_of_fusionIsBenderGroup hB
    · exact H13.Cor332.twoLocalsSolvable_of_uniqueSmallModel hS
  obtain ⟨P, hP1, hP2, hMP⟩ := hM.1
  have hMsolv : Group.IsSolvable M := hsolvG P M hP1 hP2 (le_of_eq hMP)
  have hLsolv : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLM)
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
  have : Group.IsPerfect L := (Subgroup.isPerfect_iff (H := L)).mpr hLperf
  exact Group.IsPerfect.not_isSolvable L hLsolv

theorem autOn_vIP_facts {T D : Subgroup G} {p e : ℕ} (h : HomData T D p e) :
    autOn (iP D p) (vIP T D p) ≤ autOn (iP D p ⊔ T) (vIP T D p) ∧
      autOn (iP D p ⊔ T) (vIP T D p) ≤
        normalizer (autOn (iP D p) (vIP T D p) : Set (MulAut ↥(vIP T D p))) ∧
      IsPGroup p (autOn (iP D p) (vIP T D p)) ∧
      ∀ g ∈ autOn (iP D p ⊔ T) (vIP T D p), ∃ k : ℕ, g ^ 2 ^ k ∈ autOn (iP D p) (vIP T D p) := by
  set V := vIP T D p with hVdef
  set X := iP D p with hXdef
  have hTX : T ≤ normalizer (X : Set G) := h.le_normalizer.trans (normalizer_le_normalizer_iP D p)
  have hXTV : X ⊔ T ≤ normalizer (V : Set G) := sup_le_normalizer_vOf_iP h.le_normalizer
  have hXVN : X ≤ normalizer (V : Set G) := le_sup_left.trans hXTV
  have hTVN : T ≤ normalizer (V : Set G) := le_sup_right.trans hXTV
  have hconj : ∀ g k : normalizer (V : Set G), conjAct V g * conjAct V k *
      (conjAct V g)⁻¹ = conjAct V (g * k * g⁻¹) := fun g k => by simp
  have hXbN : autOn (X ⊔ T) V ≤ normalizer (autOn X V : Set (MulAut V)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine mem_normalizer_fintype fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := ha
    rw [hconj]
    refine ⟨g * x * g⁻¹, mem_subgroupOf.mpr ?_, rfl⟩
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (sup_le_normalizer_iP h.le_normalizer
      (mem_subgroupOf.mp hg)) x).mp (mem_subgroupOf.mp hx)
  refine ⟨A4.autOn_mono le_sup_left, hXbN, ?_, ?_⟩
  · have hXsp : ∀ y ∈ autOn X V, y ^ p ^ e = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      refine A4.conjAct_eq_one_iff.mpr ?_
      have hxp := pCoreOf_iP_le_centralizer_vOf h.le_normalizer
        (h.pow_mem_pCoreOf (mem_subgroupOf.mp hx))
      simpa using hxp
    exact fun y => ⟨e, Subtype.ext (by simpa using hXsp y y.2)⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ ((X ⊔ T : Subgroup G) : Set G) := mem_subgroupOf.mp hg
    rw [coe_mul_of_right_le_normalizer_left X T hTX] at hg'
    obtain ⟨x, hx, t, ht, he⟩ := hg'
    have hgxt : g = ⟨x, hXVN hx⟩ * ⟨t, hTVN ht⟩ := Subtype.ext he.symm
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, ht⟩
    have hk' : (⟨t, hTVN ht⟩ : normalizer (V : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have htX : conjAct V ⟨t, hTVN ht⟩ ∈ normalizer (autOn X V : Set (MulAut V)) :=
      hXbN ⟨⟨t, hTVN ht⟩, mem_subgroupOf.mpr (le_sup_right (a := X) ht), rfl⟩
    obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq
      (⟨⟨x, hXVN hx⟩, mem_subgroupOf.mpr hx, rfl⟩ : conjAct V ⟨x, hXVN hx⟩ ∈ autOn X V)
      htX (2 ^ k)
    refine ⟨k, ?_⟩
    rw [hgxt, map_mul, hxe, ← map_pow, hk', map_one, mul_one]
    exact hx'

theorem lemma3_2_14HomocyclicConsumed_of
    (h316 : Theorem316Statement) (h211 : H13.U3.UniqueThreeCaseModelReduction) :
    H13.NQBlock.Lemma3_2_14HomocyclicConsumed := by
  intro G _ _ T D hs hnab hQ hT hDm hDf hTD hDq p hp hp5 e he ⟨φ⟩
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  change iP D p ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)
  by_contra hI
  obtain ⟨-, hamb, hcan⟩ :=
    H13.NQCore.sylow_normalized_maximal_nonquasisimple_canonical_residual_structure
      H13.NQCore.sylowNormalizedMaximalLocalUniqueNormalizer_holds
      H13.NQBlock.sylowNormalizedLocalNormalComponent_proved hnab hQ hT hDm hDf hTD hDq
  have hCp : CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥ := by
    intro h0
    have hc : Nat.card ↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) = 1 := by
      rw [h0, Subgroup.card_bot]
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card] at hc
    have h1 : p ^ e = 1 := Nat.eq_one_of_mul_eq_one_right hc
    rw [Nat.pow_eq_one] at h1
    rcases h1 with h1 | h1
    · exact hp.one_lt.ne' h1
    · omega
  have hcanp := hcan p hp hp5 hCp
  have hDc : D ∈ cComp (D ⊔ T) := cComp_of_isLocal hDm.1
  have hO2 : pCoreOf 2 (D ⊔ T) ≠ ⊥ := hDm.1.2.2.2
  have hloc : QuasithinUnique.LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hQs := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hO2
  have hA := QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved _ hQs _
    (modO2Image_mem_cComp hDc)
  obtain ⟨eL, -⟩ := H13.NQBlock.exists_modO2_equiv hDc
  have hDbq : ¬ CFSG.IsQuasisimple ↥(modO2Image (D ⊔ T) D) := fun h =>
    hDq (CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm h)
  have hp5' : p ≠ 5 := ne_five_of_homocyclic hA hDbq eL he φ
  have hp2 : p ≠ 2 := by omega
  have hperf : ⁅D, D⁆ = D := perfect_of_mem_cComp hamb.cComp_self
  have hdata : HomData T D p e :=
    { sylow := hT
      le_normalizer := hTD
      perfect := hperf
      prime := hp
      five_le := hp5
      one_le := by omega
      iso := ⟨φ⟩
      canonical := hcanp
      mapsTo := fun x hx hxD => mk_mem_pCore_of_mem_iP hA hDbq eL hp hp2 hx hxD
      charTwo := hamb.charTwo_sup }
  have hSC : H13.NQCore.SCSetup T D (H13.nqPrimeResidualX D p) p :=
    { simple := hs
      nonabelian := hnab
      qtke := hQ
      sylow := hT
      maximal_local := hDm
      faithful_local := hDf
      le_normalizer := hTD
      not_quasisimple := hDq
      prime := hp
      five_le := hp5
      ambient := hamb
      canonical := hcanp }
  have hUX := H13.NQCore.unique_maximal_overgroup_of H13.NQCore.stmtSCComponentOrbits_holds
    H13.NQCore.stmtSCNormalExclusion_holds H13.NQCore.stmtSCPairedExclusion_holds hSC
  have hO2DT : pCoreOf 2 D ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hDc)).trans
      (pCoreOf_le_of_quasithinIsSylowTwo hT (le_sup_right.trans le_normalizer))
  have hXIT : H13.nqPrimeResidualX D p ⊔ T ≤ iP D p ⊔ T := by
    refine sup_le (fun x hx => ?_) le_sup_right
    have hxD : x ∈ D := hcanp.le hx
    have hxP : QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨x, hxD⟩ ∈
        CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥D) ⟨x, hxD⟩ ∈
          closure {c | c ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ∧ c ^ p = 1} := by
        rw [← hcanp.image]
        exact ⟨⟨x, hxD⟩, mem_subgroupOf.mpr hx, rfl⟩
      exact (closure_le _).mpr (fun c hc => hc.1) h1
    obtain ⟨r, hr, hrI⟩ := exists_mem_iP_of_mem_pCore hp hxP
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hr
    have h2 : (r : G)⁻¹ * x ∈ pCoreOf 2 D := (H13.NQBlock.mem_pCore_iff_mem_pCoreOf _).mp hr
    have e' : x = (r : G) * ((r : G)⁻¹ * x) := by group
    rw [e']
    exact mul_mem (mem_sup_left hrI) (mem_sup_right (hO2DT h2))
  have hITM : iP D p ⊔ T ≤ normalizer (D : Set G) := sup_le ((iP_le D p).trans le_normalizer) hTD
  have hU : IsUniqueM (iP D p ⊔ T) (normalizer (D : Set G)) :=
    ⟨⟨hUX.1, hITM⟩, fun M' hM' => hUX.2.2 M' hM'.1 (hXIT.trans hM'.2)⟩
  obtain ⟨H, hH⟩ := exists_isHStar_of_perfect h211 hs hnab hQ hT hUX.1 hTD le_normalizer
    (ne_bot_of_mem_cComp hDc) hperf
  have hyp : Hyp318 T (normalizer (D : Set G)) (iP D p) (vIP T D p) :=
    { inM := ⟨hUX.1, hTD⟩
      nonempty := ⟨H, hH⟩
      perfect := iP_eq_oTwoUpper D hp hp2
      le_M := (iP_le D p).trans le_normalizer
      normal := normalizer_le_normalizer_iP D p
      unique := hU
      reduced := isTwoReducedIn_vIP hdata hI
      centralizer := pCoreOf_sup_eq_inf_centralizer hdata hI }
  have hq : qhatInt (iP D p ⊔ T) (vIP T D p) hyp.reduced.2.2.1 ≤ 2 := by
    rcases h316 G T hs hnab hQ hT _ (iP D p ⊔ T) H (vIP T D p) hyp.inM (hyp.hyp315 hT hH) with
      h1 | ⟨-, h2, -⟩ | h3
    · exact absurd h1 (hyp.not_exists_normal hH)
    · exact h2
    · exact (qhatInt_le_qInt _ _ _).trans h3
  obtain ⟨h1, h2, h3, h5⟩ := autOn_vIP_facts hdata
  have hV := hyp.reduced.2.2.1
  have hO := pCoreOf_autOn_vIP_eq_bot hdata hI
  let _ := commGroupOfElemAbelian hV
  have hVsq : ∀ v : ↥(vIP T D p), v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  rcases (EmptyFaithfulMultiple.L3213.d2_13_data hVsq hp2 hq hO h1 h2 h3 h5).1 with h | h <;>
    omega

end CFSG.Quasithin.Vol2.Ch11.OE4
