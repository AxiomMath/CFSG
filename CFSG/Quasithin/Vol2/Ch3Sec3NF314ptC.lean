module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptAssembly
public import CFSG.Quasithin.Vol2.Ch3Sec3L2qCore
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124L2PClass
public import CFSG.Quasithin.Background.C124Star
public import CFSG.Quasithin.Background.C124Z3Class
public import CFSG.Quasithin.Background.C129NativeMain
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.E6TwentyThreeC
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FLc3Out
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.Background.HL3WrBlock
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMaxBase
public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146F17
public import CFSG.Quasithin.EmptyFaithful.S146F20
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S146P1
public import CFSG.Quasithin.EmptyFaithful.S146P3
public import CFSG.Quasithin.EmptyFaithful.S152He10A
public import CFSG.Quasithin.EmptyFaithful.S152He9N
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SzN15Top
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314L
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316Q
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2D
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptK
public import CFSG.Quasithin.Vol2.Ch3Sec3NFSite
public import CFSG.Quasithin.Vol2.Ch3T325D
public import CFSG.Quasithin.Vol2.Ch3T325J
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.Ins314
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3319
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G}

theorem exists_sylow_three_oTwoUpper (c : NFConfig G T M L D H K) :
    ∃ P₃ : Subgroup G, P₃ ≤ oTwoUpper H ∧ Nat.card P₃ = 9 ∧ ∀ p ∈ P₃, p ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow c.inH.1
  obtain ⟨e⟩ := c.wreath
  have hXi := Der6D.xi_of_iso hTsyl c.inH.2 (oTwoQuotEquiv e)
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper (oTwoQuotEquiv e)
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P₃, hP₃⟩ := CFSG.Quasithin.Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  refine ⟨P₃, hP₃.le, by rw [hXi.card_sylow (by norm_num) h3 hP₃, hrel], fun p hp => ?_⟩
  have hdisj : P₃ ⊓ pCoreOf 2 H = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P₃ (pCoreOf 2 H) hP₃.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)).eq_bot
  have h1 : p ^ 3 ∈ P₃ ⊓ pCoreOf 2 H :=
    ⟨P₃.pow_mem hp 3, C1Pack12.pow_three_mem_pCoreOf (oTwoQuotEquiv e) (hP₃.le hp)⟩
  rw [hdisj, Subgroup.mem_bot] at h1
  exact h1

theorem eq_one_of_three_of_conjOf_eq_one {t : G} (e : Sett T M L t)
    {x : G} (hx : x ∈ L ⊔ T) (h3 : x ^ 3 = 1)
    (hC : conjOf (vPlus L T) (L ⊔ T) e.hX ⟨x, hx⟩ = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := e.exists_pow_eq_one ⟨x, hx⟩ hC
  have hn' : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hg : Nat.gcd 3 (2 ^ n) = 1 :=
    Nat.Coprime.gcd_eq_one ((by norm_num : Nat.Coprime 3 2).pow_right n)
  have h1 : x ^ Nat.gcd 3 (2 ^ n) = 1 := pow_gcd_eq_one.mpr ⟨h3, hn'⟩
  rwa [hg, pow_one] at h1

theorem conjugate_eq_of_not_mem_normalizer {t t₀ : G} (e : Sett T M L t₀)
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate L t = CFSG.conjugate L t₀ := by
  have hs : t * t₀⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have e1 : (CFSG.conjugate L t₀).map (MulAut.conj t).toMonoidHom =
        L.map (MulAut.conj (t * t₀⁻¹)).toMonoidHom := by
      unfold CFSG.conjugate
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    exact e1.symm.trans (e.swap_conj ht htn).2
  have key : ∀ s ∈ Subgroup.normalizer (L : Set G), ∀ g : G,
      CFSG.conjugate L (s * g) = CFSG.conjugate L g := by
    intro s hs' g
    have hsL : L.map (MulAut.conj s⁻¹).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hs')
    calc CFSG.conjugate L (s * g)
        = (L.map (MulAut.conj s⁻¹).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
          unfold CFSG.conjugate
          rw [Subgroup.map_map]
          congr 1
          ext x
          simp [mul_assoc]
      _ = CFSG.conjugate L g := by
          unfold CFSG.conjugate
          rw [hsL]
  have h := key _ hs t₀
  rwa [inv_mul_cancel_right] at h

theorem cyclic_of_order_168_three {Q : Type} [Group Q] [Finite Q] (hQ : Nat.card Q = 168)
    (H' : Subgroup Q) (hH' : IsPGroup 3 H') : IsCyclic H' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH'
  have hdvd : Nat.card H' ∣ 168 := by
    have := Subgroup.card_subgroup_dvd_card H'
    rwa [hQ] at this
  rw [hk] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h9.trans hdvd
    norm_num at this
  interval_cases k
  · rw [pow_zero] at hk
    exact isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨1, by rw [orderOf_one, hk]⟩
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

theorem exists_three_split {t : G} (e : Sett T M L t)
    (hPSL : IsPSL 3 2 1 ↥(autOn L (vPlus L T))) {P₃ : Subgroup G} (hPM : P₃ ≤ mPlus L T)
    (hPc : Nat.card P₃ = 9) (hP3 : ∀ p ∈ P₃, p ^ 3 = 1) :
    ∃ x : ↥(L ⊔ T), (x : G) ∈ P₃ ∧ conjOf (vPlus L T) (L ⊔ T) e.hX x ≠ 1 ∧
      ∃ l : ↥(L ⊔ T), (l : G) ∈ L ∧
        conjOf (vPlus L T) (L ⊔ T) e.hX l = conjOf (vPlus L T) (L ⊔ T) e.hX x := by
  have hMLT : mPlus L T ≤ L ⊔ T := by
    rw [e.hM]
    exact sup_le le_sup_left e.L2_le
  have hPLT : P₃ ≤ L ⊔ T := hPM.trans hMLT
  obtain ⟨f, hf⟩ : ∃ f : (P₃.subgroupOf (L ⊔ T)) →* MulAut ↥(vPlus L T),
      ∀ y, f y = conjOf (vPlus L T) (L ⊔ T) e.hX (y : ↥(L ⊔ T)) :=
    ⟨(conjOf (vPlus L T) (L ⊔ T) e.hX).comp (P₃.subgroupOf (L ⊔ T)).subtype, fun y => rfl⟩
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hf] at hy
    have hyP : ((y : ↥(L ⊔ T)) : G) ∈ P₃ := Subgroup.mem_subgroupOf.mp y.2
    have h1 : ((y : ↥(L ⊔ T)) : G) = 1 :=
      eq_one_of_three_of_conjOf_eq_one e (y : ↥(L ⊔ T)).2 (hP3 _ hyP) hy
    exact Subtype.ext (Subtype.ext h1)
  have hcardf : Nat.card f.range = 9 := by
    have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have h2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPLT).toEquiv
    rw [← h1, h2, hPc]
  have hle : f.range ≤ autOn L (vPlus L T) ⊔ autOn (CFSG.conjugate L t) (vPlus L T) := by
    rintro _ ⟨y, rfl⟩
    have hyM : ((y : ↥(L ⊔ T)) : G) ∈ (mPlus L T : Set G) :=
      hPM (Subgroup.mem_subgroupOf.mp y.2)
    rw [e.coe_mPlus] at hyM
    obtain ⟨l₂, hl₂, l, hl, hll⟩ := hyM
    have hl₂X : l₂ ∈ L ⊔ T := e.L2_le hl₂
    have hlX : l ∈ L ⊔ T := Subgroup.mem_sup_left hl
    have hyl : (y : ↥(L ⊔ T)) = (⟨l₂, hl₂X⟩ : ↥(L ⊔ T)) * ⟨l, hlX⟩ :=
      Subtype.ext hll.symm
    rw [hf, hyl, map_mul]
    exact mul_mem (Subgroup.mem_sup_right (conjOf_mem_autOn (x := ⟨l₂, hl₂X⟩) e.hX hl₂))
      (Subgroup.mem_sup_left (conjOf_mem_autOn (x := ⟨l, hlX⟩) e.hX hl))
  have hcard2 : Nat.card ↥(autOn (CFSG.conjugate L t) (vPlus L T)) = 168 :=
    CFSG.Quasithin.SBc11.card_of_isPSL_three_two (e.isPSL_autOn_L2 hPSL)
  haveI : Finite ↥(autOn (CFSG.conjugate L t) (vPlus L T)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; norm_num)
  have hcyc : ∀ H' : Subgroup ↥(autOn (CFSG.conjugate L t) (vPlus L T)),
      IsPGroup 3 H' → IsCyclic H' :=
    fun H' hH' => cyclic_of_order_168_three hcard2 H' hH'
  have hpow : ∀ p ∈ f.range, p ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    have hy3 : ((y : ↥(L ⊔ T)) : G) ^ 3 = 1 := hP3 _ (Subgroup.mem_subgroupOf.mp y.2)
    have hy : y ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hy3
    rw [← map_pow, hy, map_one]
  have hbot := L2qC.inf_ne_bot e.comm e.hbot hle hcardf hpow hcyc
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hgne : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  obtain ⟨y, hy⟩ := hg.1
  obtain ⟨l, hlL, hl⟩ := exists_conjOf_eq e.hX le_sup_left hg.2
  refine ⟨(y : ↥(L ⊔ T)), Subgroup.mem_subgroupOf.mp y.2, ?_, l, hlL, ?_⟩
  · intro h
    apply hgne
    rw [← hy, hf]
    exact h
  · exact hl.trans (hy.symm.trans (hf y))

theorem leafYsplit_holds
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : LeafYsplit := by
  intro G _ _ T M L D H K hcfg t ht htn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hP, -⟩ := hcfg
  obtain ⟨⟨hTL, hcomm, hcase, hPSL⟩, hfix⟩ := hP
  obtain ⟨t₀, ht₀, ht₀n, hM, hcommA, hbot, -, htc, htcI, hmod⟩ := hcase
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 168 := by
    obtain ⟨e⟩ := nonempty_equiv_of_isPSL hPSL
    rw [Nat.card_congr e.toEquiv, card_L3Γ]
  have sett : Sett T M L t₀ :=
    ⟨c.hyp.toSetup331, ht₀, ht₀n, hM, hcommA, hbot, h37, h38, hcard⟩
  have hred := Hyp331.vPlus_reduced c.hyp.toSetup331
  have hV2 : ∀ x ∈ vPlus L T, x ^ 2 = 1 := hred.2.1.2
  have hTsylLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow le_sup_right
  have hVO : vPlus L T ≤ pCoreOf 2 (L ⊔ T) := hred.1.trans inf_le_left
  have hVT : vPlus L T ≤ T := hVO.trans (pCoreOf_le_of_isSylowTwoOf hTsylLT)
  have hC0 := c.inf_centralizer_mPlus_eq_bot h36 h5 h128 h37 h38 h39
  have h74 : vPlus L T = ⁅vPlus L T, mPlus L T⁆ := by
    have := (h7 G T M L D c.hyp).2.2.2.2
    rwa [hC0, sup_bot_eq] at this
  have hCV := inf_centralizer_mPlus_vPlus_eq_bot c.hyp.sylow.1 hVT hV2 hC0
  have hI := sett.V1_inf_V2 htcI hCV
  have hVs := sett.V_eq_sup h74
  obtain ⟨P₃, hP₃L, hP₃c, hP₃e⟩ := exists_sylow_three_oTwoUpper c
  have hPM : P₃ ≤ mPlus L T := hP₃L.trans (oTwoUpper_le_mPlus sett c.HLT)
  obtain ⟨x, hxP, hx1, l, hlL, hlx⟩ := exists_three_split sett hPSL hPM hP₃c hP₃e
  rw [conjugate_eq_of_not_mem_normalizer sett ht htn]
  have hcent : conjOf (vPlus L T) (L ⊔ T) sett.hX (l⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hlx, inv_mul_cancel]
  have hcent' : (l : G)⁻¹ * (x : G) ∈ Subgroup.centralizer ((vPlus L T : Subgroup G) : Set G) :=
    (conjOf_eq_one_iff sett.hX (l⁻¹ * x)).mp hcent
  have hC2 : (x : G) ∈
      Subgroup.centralizer ((⁅vPlus L T, CFSG.conjugate L t₀⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvV : v ∈ vPlus L T :=
      commutator_le_of_le_normalizer (fun y hy => sett.hX (sett.L2_le hy)) hv
    have hlv : (l : G) * v = v * (l : G) := sett.L_centralizes_V2 hI hlL hv
    have hcv : v * ((l : G)⁻¹ * (x : G)) = ((l : G)⁻¹ * (x : G)) * v :=
      Subgroup.mem_centralizer_iff.mp hcent' v hvV
    calc v * (x : G) = (v * (l : G)) * ((l : G)⁻¹ * (x : G)) := by group
      _ = ((l : G) * v) * ((l : G)⁻¹ * (x : G)) := by rw [← hlv]
      _ = (l : G) * (v * ((l : G)⁻¹ * (x : G))) := by group
      _ = (l : G) * (((l : G)⁻¹ * (x : G)) * v) := by rw [hcv]
      _ = (x : G) * v := by group
  have hnotC1 : (x : G) ∉ Subgroup.centralizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := by
    intro hC1
    have hle : vPlus L T ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [hVs]
      refine sup_le (fun v hv => ?_) (fun v hv => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (Subgroup.mem_centralizer_iff.mp hC1 v hv).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (Subgroup.mem_centralizer_iff.mp hC2 v hv).symm
    have hxV : (x : G) ∈ Subgroup.centralizer ((vPlus L T : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hle hv) (x : G) (Set.mem_singleton _)).symm
    exact hx1 ((conjOf_eq_one_iff sett.hX x).mpr hxV)
  have hodd : Odd (orderOf (x : G)) := by
    have hd : orderOf (x : G) ∣ 3 := orderOf_dvd_of_pow_eq_one (hP₃e _ hxP)
    exact Odd.of_dvd_nat ⟨1, by norm_num⟩ hd
  exact ⟨(x : G), hP₃L hxP, hodd, hP₃e _ hxP, hC2, hnotC1⟩

end CFSG.Quasithin.H13.NF314pt
