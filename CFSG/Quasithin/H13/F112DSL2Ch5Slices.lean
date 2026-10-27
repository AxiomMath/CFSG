module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518Canon
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Canon
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Am
public import CFSG.Quasithin.H13.F112DSL2Slices
public import CFSG.Quasithin.Background.C2PushY
public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518DL
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518DLO
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Components

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem not_D_le_slices
    (h5114 : Stmt5_1_14_first) (h331 : Stmt3_3_1) (hE9 : L34ElemNineFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact)
    (hSzA : SzTwoAutInnerFact) (hL2 : L2PerfectThreePrimeFact) (hDS : DSSzL2Statement)
    {Kp : Subgroup G} (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    ¬ D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  intro hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  set Mp := Subgroup.normalizer (K : Set G) with hMpdef
  have hNKp := h.normalizer_cComp_eq h5114 hE9 h36 h37 h39 hSz hKp
  have hKpMp : Kp ∈ cComp Mp := mem_cComp_normalizer_of_mem_cComp hKp
  obtain ⟨hsimp, k, hk⟩ := h.suzuki_cComp h5114 hE9 h36 hSz hKp
  have hnotM := h.not_le_M h5114 h331 hE9 h36 h37 h39 hSz hL2 hKp
  have hTMp : IsSylowTwoOf T Mp := hh.isSylowTwoOf h.T_le_Mp
  have hTKp : IsSylowTwoOf (T ⊓ Kp) Kp :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKpMp) hTMp
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have hTNKp : T ≤ Subgroup.normalizer (Kp : Set G) := hNKp ▸ h.T_le_Mp
  have hOT : pCoreOf 2 Kp ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKpMp)).trans
      (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTMp)
  have hZKp : Subgroup.center (O2Q Kp) = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_not_prime (five_dvd_card_of_suzukiModel hk).2
  have hBp : borelOf Kp T ≤ Subgroup.normalizer (T : Set G) :=
    borelOf_le_normalizer_of_suzuki hSzA hh.sylow.1 hTNKp hTKp hOT hZKp hk
  have hNT : Subgroup.normalizer (T : Set G) ≤ M :=
    (h331 G T hh.simple hh.nonabelian hh.qtke hh.sylow).1 M L hh.maxTwoLocal hh.T_le hh.maximal
      hh.L_le hh.isQuasisimple
  have hBpL : borelOf Kp T ≤ Subgroup.normalizer (L : Set G) := hBp.trans (hNT.trans hh.normal)
  have hBL : borelOf L T ≤ Subgroup.normalizer (Kp : Set G) := by
    have e : borelOf L T = borelL T L := rfl
    rw [e, ← hh.borelL_eq_sup h.notation59.2.1, hNKp]
    exact sup_le hD (inf_le_left.trans h.T_le_Mp)
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
  have hEven := hh.qtke.2.1
  have hMO : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
  have hc1 : CharTwo (L ⊔ T ⊔ borelOf Kp T) := by
    have hle : L ⊔ T ⊔ borelOf Kp T ≤ M := sup_le (hh.sup_le_M) (hBp.trans hNT)
    have hTS : (S : Subgroup G) ≤ L ⊔ T ⊔ borelOf Kp T := by
      rw [hS]; exact le_sup_right.trans le_sup_left
    have hSM : (S : Subgroup G) ≤ M := by rw [hS]; exact hh.T_le
    exact charTwo_of_le hEven S hTS hle ⟨hSM, hMO⟩
  have hc2 : CharTwo (Kp ⊔ T ⊔ borelOf L T) := by
    have hle : Kp ⊔ T ⊔ borelOf L T ≤ Mp :=
      sup_le (sup_le (le_of_mem_cComp hKpMp) h.T_le_Mp) (hBL.trans hNKp.le)
    have hTS : (S : Subgroup G) ≤ Kp ⊔ T ⊔ borelOf L T := by
      rw [hS]; exact le_sup_right.trans le_sup_left
    have hSM : (S : Subgroup G) ≤ Mp := by rw [hS]; exact h.T_le_Mp
    exact charTwo_of_le hEven S hTS hle ⟨hSM, h.pCoreOf_Mp_ne_bot h5114⟩
  obtain ⟨a, ha, ⟨eSz⟩⟩ := exists_mulEquiv_sz_of_suzukiModel hk
  have eKp : O2Q Kp ≃* oTwoQuot ↥Kp :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥Kp 2)
  have eL : O2Q L ≃* oTwoQuot ↥L := QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥L 2)
  have hlistKp : IsRankOneListed (oTwoQuot ↥Kp) := Or.inr (Or.inl ⟨a, ⟨eKp.symm.trans eSz⟩⟩)
  have hlistL : IsRankOneListed (oTwoQuot ↥L) :=
    (isRankOneListed_of_lieModel (by have := hh.two_le; omega) hh.lie).of_mulEquiv eL
  have hO2 : pCoreOf 2 (Kp ⊔ L ⊔ T) = ⊥ := by
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (Kp ⊔ L ⊔ T) : Set G)) :=
      ⟨_, hne, pCoreOf_isPGroup 2 _, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hsup : Kp ⊔ L ⊔ T ≤ M' := (le_normalizer_pCoreOf 2 _).trans hle
    have hM'eq : M' = M := (hh.isUniqueM h331).2 M'
      ⟨hM', sup_le (le_sup_right.trans (le_sup_left.trans hsup)) (le_sup_right.trans hsup)⟩
    exact hnotM (hM'eq ▸ (le_sup_left.trans (le_sup_left.trans hsup)))
  have hhyp : Hyp111 Kp L T := by
    refine ⟨⟨inferInstance, hh.sylow.1, hTNKp, hTKp, hlistKp, hBL, hc2⟩,
      ⟨inferInstance, hh.sylow.1, hh.T_le_normalizer, hTL, hlistL, hBpL, hc1⟩, hO2⟩
  have hqt : IsQuasithinSub (Kp ⊔ L ⊔ T) := by
    intro p hp hp2 R _ hR hR2
    exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
      (pRank_le_two_of_isTwoLocal hh.qtke hp hp2 ⟨R, hR, hR2, rfl⟩)
  have hnorm : (T.subgroupOf (T ⊔ borelOf Kp T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hBp)
  have hLns : ¬ Group.IsSolvable ↥L := by
    rw [isSolvable_iff_perfectCore_eq_bot, perfectCore_eq_self_of_perfect hh.commutator_eq]
    intro hL
    have := hh.isSimple
    have hnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := IsSimpleGroup.toNontrivial
    obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
    apply hxy
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        have hall : ∀ z : ↥L, z = 1 := fun z => Subtype.ext (by
          have h1 : (z : G) ∈ (⊥ : Subgroup G) := by rw [← hL]; exact z.2
          exact Subgroup.mem_bot.mp h1)
        rw [hall x, hall y]
  have hLL2 : IsL2Quot n (oTwoQuot ↥L) :=
    isL2Quot_oTwoQuot_of_lieModel (by have := hh.two_le; omega) hh.lie
  obtain ⟨hTKp', -⟩ := hDS G Kp L T hhyp hqt (Or.inl hnorm) ⟨a, ha, ⟨eKp.symm.trans eSz⟩⟩ hLns
    ⟨n, hLL2⟩
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTMp Subgroup.le_normalizer le_rfl
  have hZ := h.center_K hE9
  have hTKO : T ⊓ K ≤ pCoreOf 2 K := fun x hx =>
    mem_pCoreOf_of_mem_centralizerModO2 hZ hx.2 (le_of_mem_cComp hKp (hTKp' hx.1))
  have hdvd : (CFSG.pCore 2 ↥K).index ∣ ((T ⊓ K).subgroupOf K).index := by
    apply Subgroup.index_dvd_of_le
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨z, hz, hzx⟩ := hTKO hx
    have : z = x := Subtype.ext hzx
    rw [← this]
    exact hz
  have hcard : (CFSG.pCore 2 ↥K).index = 20160 := by
    rw [Subgroup.index, ← card_of_lieModel_L34 h.l34]
  rw [hcard] at hdvd
  exact hTK.2.2 ((show (2 : ℕ) ∣ 20160 by norm_num).trans hdvd)

end Hyp5_1_14

end Components

theorem stmt5_1_16_of_inputs_slices
    (h5114 : Stmt5_1_14_first) (h331 : Stmt3_3_1) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE9 : L34ElemNineFact)
    (hSz : SimpleThreePrimeSuzukiFact) (hSzA : SzTwoAutInnerFact) (hL2 : L2PerfectThreePrimeFact)
    (hDS : DSSzL2Statement) : Stmt5_1_16 := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  refine ⟨h.not_three_dvd h5114 hE9, fun hns => ?_⟩
  obtain ⟨Kp, hKp⟩ := exists_mem_cComp_of_not_isSolvable' hns
  have hPC := h.perfectCore_eq h5114 hE9 h36 h37 h39 hSz hKp
  obtain ⟨-, k, hk⟩ := h.suzuki_cComp h5114 hE9 h36 hSz hKp
  refine ⟨⟨k, hPC ▸ hk⟩, hPC ▸ h.not_le_M h5114 h331 hE9 h36 h37 h39 hSz hL2 hKp,
    h.not_D_le_slices h5114 h331 hE9 h36 h37 h39 hSz hSzA hL2 hDS hKp⟩

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem false_of_outer_corrected_slices (hPF : L34ParabolicFact) (hTA : L34TwoAutFact)
    (h5114 : Stmt5_1_14_first) (h432 : Stmt4_3_2) (h331 : Stmt3_3_1) (h510 : Stmt5_1_10)
    (hR : L2RankOneSylowFact) (hDSA : DSAL2Statement) (hF : F112L2FourChiefFactC)
    (hPC : L34ParabolicChiefFact) (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G))
    {d₀ : G} (hd₀D : d₀ ∈ D) (hd₀3 : d₀ ^ 3 = 1)
    (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hST, hTLS, hTKS, hOMS, hOMpS, hSN⟩ := h.S_facts h510 h331 hR hD
  have hS2 : IsPGroup 2 (pCoreOf 2 (D ⊔ B ⊔ T)) := pCoreOf_isPGroup 2 _
  have hTK := h.isSylowTwoOf_inf_K
  have hTMp := h.T_le_Mp
  have hBK : B ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    h.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hSMp : pCoreOf 2 (D ⊔ B ⊔ T) ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hST.trans hTMp
  obtain ⟨U, hOU, hUTK, hUcomm, hUsq, hUcard, hUN, φ, hφs, hφk⟩ :=
    h.exists_parabolic hPF hTA h510 h331 hR hD hd₀D hd₀3 hd₀
  have hUK : U ≤ oTwoUpper H := hUTK.trans inf_le_right
  have hTKN : T ⊓ oTwoUpper H ≤ Subgroup.normalizer (U : Set G) :=
    hTKS.trans (le_sup_right.trans hUN)
  obtain ⟨hL2K₂, hnsK₂, h5K₂, hTK₂, hBorK₂⟩ :=
    oTwoUpper_parabolic_facts rfl hTK hUTK hTKN φ hφs hφk
  set K₂ := oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  have hK₂K : K₂ ≤ oTwoUpper H := (oTwoUpper_le _).trans inf_le_left
  have hDK₂ : D ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx =>
    mem_normalizer_oTwoUpper_inf (hD hx) (hUN (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
  have hSK₂ : pCoreOf 2 (D ⊔ B ⊔ T) ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx =>
    mem_normalizer_oTwoUpper_inf (hSMp hx) (hUN (Subgroup.mem_sup_right hx))
  have hSK₂eq : pCoreOf 2 (D ⊔ B ⊔ T) ⊓ K₂ = T ⊓ K₂ :=
    le_antisymm (inf_le_inf_right _ hST)
      (le_inf ((inf_le_inf_left T hK₂K).trans hTKS) inf_le_right)
  have hSLeq : pCoreOf 2 (D ⊔ B ⊔ T) ⊓ L = T ⊓ L :=
    le_antisymm (inf_le_inf_right _ hST) (le_inf hTLS inf_le_right)
  have hBorL : borelOf L (pCoreOf 2 (D ⊔ B ⊔ T)) = D ⊔ (T ⊓ L) := by
    rw [hh.borelL_eq_sup h.notation59.2.1]
    show L ⊓ Subgroup.normalizer ((pCoreOf 2 (D ⊔ B ⊔ T) ⊓ L : Subgroup G) : Set G) = _
    rw [hSLeq]
  obtain ⟨-, -, hBorel, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hBorK₂M : borelOf K₂ (pCoreOf 2 (D ⊔ B ⊔ T)) ≤ M := by
    intro x hx
    have hx' : x ∈ K₂ ⊓ Subgroup.normalizer ((T ⊓ K₂ : Subgroup G) : Set G) := by
      have hx2 := hx.2
      rw [hSK₂eq] at hx2
      exact ⟨hx.1, hx2⟩
    have hxMK : x ∈ M ⊓ oTwoUpper H := by
      rw [hMK]
      exact ⟨hK₂K hx.1, hBorK₂ hx'⟩
    exact hxMK.1
  have hcharM : CharTwo M :=
    charTwo_of_inH' hh.qtke hh.sylow ⟨hh.T_le, pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1⟩
  have hcharMp := h.charTwo_Mp h5114
  have hDMp : D ⊔ (T ⊓ L) ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le hD (inf_le_left.trans hTMp)
  have hc1 : CharTwo (K₂ ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ⊔ borelOf L (pCoreOf 2 (D ⊔ B ⊔ T))) := by
    refine C2Push.charTwo_of_pCoreOf_le hcharMp (hOMpS.trans (le_sup_right.trans le_sup_left)) ?_
    rw [hBorL]
    exact sup_le (sup_le (hK₂K.trans Subgroup.le_normalizer) hSMp) hDMp
  have hc2 : CharTwo (L ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ⊔ borelOf K₂ (pCoreOf 2 (D ⊔ B ⊔ T))) :=
    C2Push.charTwo_of_pCoreOf_le hcharM (hOMS.trans (le_sup_right.trans le_sup_left))
      (sup_le (sup_le hh.L_le (hST.trans hh.T_le)) hBorK₂M)
  have hK₂M : ¬ K₂ ≤ M := by
    intro hle
    have hMH : K₂ ≤ M ⊓ H := le_inf hle (hK₂K.trans (oTwoUpper_le H))
    have h1 : 5 ∣ Nat.card ↥(M ⊓ H) := h5K₂.trans (Subgroup.card_dvd_of_le hMH)
    rw [h.hyp.card_inf_eq h.notation59, h.card_B_eq_three h510] at h1
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hh.sylow.1
    rw [hm] at h1
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h1 with h2 | h2
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h2) (by norm_num)
    · exact absurd h2 (by norm_num)
  have hO2 : pCoreOf 2 (K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T)) = ⊥ := by
    by_contra hne
    have hloc : IsTwoLocal (Subgroup.normalizer
        (pCoreOf 2 (K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T)) : Set G)) :=
      ⟨_, hne, pCoreOf_isPGroup 2 _, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hsup : K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ≤ M' := (le_normalizer_pCoreOf 2 _).trans hle
    have hM'eq : M' = M :=
      (h432 G T M L hh.simple hh.nonabelian hh.qtke hh.sylow hh.maxTwoLocal hh.T_le hh.maximal
        hh.faithful hh.L_le hh.normal ⟨n, hh.two_le, hh.lie⟩).1 M' hM'
        (le_sup_right.trans (le_sup_left.trans hsup))
    exact hK₂M (hM'eq ▸ le_sup_left.trans (le_sup_left.trans hsup))
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf le_sup_right) le_sup_left hh.sup_le_normalizer
  have eL : O2Q L ≃* oTwoQuot ↥L := QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥L 2)
  have hlistL : IsRankOneListed (oTwoQuot ↥L) :=
    (isRankOneListed_of_lieModel (by have := hh.two_le; omega) hh.lie).of_mulEquiv eL
  have hlistK₂ : IsRankOneListed (oTwoQuot ↥K₂) := Or.inl ⟨2, by norm_num, hL2K₂⟩
  have hhyp : Hyp111 K₂ L (pCoreOf 2 (D ⊔ B ⊔ T)) := by
    refine ⟨⟨inferInstance, hS2, hSK₂, by rw [hSK₂eq]; exact hTK₂, hlistK₂, ?_, hc1⟩,
      ⟨inferInstance, hS2, hST.trans (hh.T_le.trans hh.normal), by rw [hSLeq]; exact hTL,
        hlistL, hBorK₂M.trans hh.normal, hc2⟩, hO2⟩
    rw [hBorL]
    exact sup_le hDK₂ (hTLS.trans hSK₂)
  have hqt : IsQuasithinSub (K₂ ⊔ L ⊔ pCoreOf 2 (D ⊔ B ⊔ T)) := by
    intro p hp hp2 R _ hR' hR2
    exact (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans
      (pRank_le_two_of_isTwoLocal hh.qtke hp hp2 ⟨R, hR', hR2, rfl⟩)
  have hnorm : ((pCoreOf 2 (D ⊔ B ⊔ T)).subgroupOf
      (pCoreOf 2 (D ⊔ B ⊔ T) ⊔ borelOf L (pCoreOf 2 (D ⊔ B ⊔ T)))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr ?_
    rw [hBorL]
    exact sup_le Subgroup.le_normalizer
      (sup_le (fun x hx => hSN (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
        (hTLS.trans Subgroup.le_normalizer))
  have hLns : ¬ Group.IsSolvable ↥L := by
    rw [isSolvable_iff_perfectCore_eq_bot, perfectCore_eq_self_of_perfect hh.commutator_eq]
    intro hL
    have := hh.isSimple
    have hnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) := IsSimpleGroup.toNontrivial
    obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
    apply hxy
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        have hall : ∀ z : ↥L, z = 1 := fun z => Subtype.ext (by
          have h1 : (z : G) ∈ (⊥ : Subgroup G) := by rw [← hL]; exact z.2
          exact Subgroup.mem_bot.mp h1)
        rw [hall x, hall y]
  have hLL2 : IsL2Quot n (oTwoQuot ↥L) :=
    isL2Quot_oTwoQuot_of_lieModel (by have := hh.two_le; omega) hh.lie
  obtain ⟨L1, L2, hperm, -, hlist, -⟩ :=
    hDSA G K₂ L (pCoreOf 2 (D ⊔ B ⊔ T)) hhyp hqt (Or.inr hnorm) hnsK₂ hLns (Or.inr ⟨n, hLL2⟩)
  have hhyp' : Hyp111 L1 L2 (pCoreOf 2 (D ⊔ B ⊔ T)) := by
    rcases hperm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hhyp
    · rw [h1, h2]
      refine ⟨hhyp.h2, hhyp.h1, ?_⟩
      rw [sup_comm L K₂]
      exact hhyp.o2
  have hK₂mem : K₂ = L1 ∨ K₂ = L2 := by
    rcases hperm with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  have hZne : quasithinOmegaOneCenter T ≠ ⊥ :=
    CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot hh.sylow.1 hh.T_ne_bot
  have hZT := quasithinOmegaOneCenter_le_inf T
  have hZS : quasithinOmegaOneCenter T ≤ centerOf (pCoreOf 2 (D ⊔ B ⊔ T)) := by
    have hOMT : pCoreOf 2 M ≤ T := F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf hh.T_le)
    intro z hz
    have hzT := hZT hz
    refine ⟨hOMS (hcharM ⟨hh.T_le hzT.1, ?_⟩), ?_⟩
    · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOMT) hzT.2
    · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hST) hzT.2
  have hZK₂ : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (K₂ : Set G) := by
    have hZH := (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).2.1.1
    have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
    exact hZC.trans (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (hK₂K.trans (oTwoUpper_le H))))
  obtain ⟨m, hm⟩ := D15Proof.exists_isChiefSeriesFrom (H := K₂) (U := pCoreOf 2 K₂)
    (pCoreOf 2 K₂) ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K₂ hg) x).mp hx⟩
  have hle2 := hF G L1 L2 (pCoreOf 2 (D ⊔ B ⊔ T)) hhyp' hlist K₂ hK₂mem hL2K₂ _ hZne hZS hZK₂ m hm
  have hcharK : CharTwo (oTwoUpper H) :=
    CharTwo.of_normal (charTwo_of_inH' hh.qtke hh.sylow h.hyp.hStar.1) (oTwoUpper_le H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H))
  have hge3 := hPC G (oTwoUpper H) U h.l34 hcharK hOU hUK hUcomm hUsq hUcard m hm
  omega

end Hyp5_1_14

end Setting

theorem stmt5_1_18_DL_outer_of_inputs_corrected_slices (hPF : L34ParabolicFact) (hTA : L34TwoAutFact)
    (h5114 : Stmt5_1_14_first) (h432 : Stmt4_3_2) (h331 : Stmt3_3_1) (h510 : Stmt5_1_10)
    (hR : L2RankOneSylowFact) (hDSA : DSAL2Statement) (hF : F112L2FourChiefFactC)
    (hPC : L34ParabolicChiefFact) : Stmt5_1_18_DL_outer := by
  intro G _ _ T M L V H B D n h _ D₃ hD₃ h3 _ hout hD
  obtain ⟨d, hd, hdout⟩ := hout
  have hd3 : d ^ 3 = 1 := by
    have h' := pow_card_eq_one' (G := ↥D₃) (x := ⟨d, hd⟩)
    rw [h3] at h'
    exact congrArg Subtype.val h'
  exact h.false_of_outer_corrected_slices hPF hTA h5114 h432 h331 h510 hR hDSA hF hPC hD (hD₃ hd) hd3 hdout

theorem stmt5_1_18_DL_outer_of_corrected_slices (h5114 : Stmt5_1_14_first) (h432 : Stmt4_3_2)
    (h331 : Stmt3_3_1) (h510 : Stmt5_1_10) (hR : L2RankOneSylowFact) (hDSA : DSAL2Statement)
    (hF : F112L2FourChiefFactC) (hPC : L34ParabolicChiefFact) : Stmt5_1_18_DL_outer :=
  stmt5_1_18_DL_outer_of_inputs_corrected_slices l34ParabolicFact l34TwoAutFact h5114 h432 h331 h510 hR hDSA hF hPC

theorem stmt5_1_18_of_reduced_outer_corrected_slices (hT : L2TorusFact) (h510 : Stmt5_1_10)
    (h515 : Stmt5_1_15) (h516 : Stmt5_1_16) (h5114 : Stmt5_1_14_first) (h517 : Stmt5_1_17)
    (h432 : Stmt4_3_2) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hDSA : DSAL2Statement)
    (hF : F112L2FourChiefFactC) (hPC : L34ParabolicChiefFact) (hD5 : Stmt5_1_18_D5) :
    Stmt5_1_18 :=
  stmt5_1_18_of_reduced hT h510 h515 h516 h5114 h517
    (stmt5_1_18_DL_outer_of_corrected_slices h5114 h432 h331 h510 hR hDSA hF hPC) hD5

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stmt5_2_6_of_corrected_slices (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hF : RankOneListedFacts.{0})
    (hF11 : StmtF11_5_2) (hDSA : DSAL2Statement) (h524 : Stmt5_2_4) (hbor : Stmt5_2_6_borel)
    (htr : Stmt5_2_6_trC) : Stmt5_2_6 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  have h111 := hF11 G T M L V H B D L₂ n hyp
  obtain ⟨-, hweak, -, -⟩ := prop_F19_of_listed hF h111
  have hbor2 : S ⊔ borelOf L₂ S = S ⊔ (B ⊓ L₂) := hbor G T M L V H B D L₂ n hyp
  obtain ⟨-, -, ⟨hBS, -, -⟩, -⟩ := h524 G T M L V H B D L₂ n hyp
  obtain ⟨hG1, hG2, -⟩ := hyp.parabolics_eq h331 hR hbor2
  have hSn : (S.subgroupOf (S ⊔ borelOf L₂ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left, hbor2]
    exact sup_le Subgroup.le_normalizer (inf_le_left.trans hBS)
  have hLns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_perfect h.commutator_eq h.maximal.1.2.1.1
  have hL₂ns : ¬ Group.IsSolvable ↥L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact not_isSolvable_of_perfect hK₁.2.1 hK₁.1
    · exact not_isSolvable_of_perfect hL₂P.2.1 hL₂P.1
  have hLL2 : IsL2Quot n (oTwoQuot ↥L) :=
    isL2Quot_oTwoQuot_of_lieModel (by have := h.two_le; omega) h.lie
  have hds := hDSA G L L₂ S h111 (CFSG.Quasithin.isQuasithinSub_of_qtke h.qtke _) (Or.inr hSn)
    hLns hL₂ns (Or.inl ⟨n, hLL2⟩)
  refine ⟨?_, htr G T M L V H B D L₂ n hyp hds⟩
  rw [hG1, hG2]
  exact hweak

end CFSG.Quasithin.H13
