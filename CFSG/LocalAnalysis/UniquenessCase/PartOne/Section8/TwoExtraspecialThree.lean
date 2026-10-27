module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Q8108
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OppNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.GLTheoremA.Lemma48
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralProductExtraspecial
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.L34SylowExtraspecial
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four R8_108)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure TwoExtraThree (P R R' : Subgroup G) : Prop where
  extra : CFSG.IsExtraspecial 3 R
  extra' : CFSG.IsExtraspecial 3 R'
  card : Nat.card R = 27
  card' : Nat.card R' = 27
  exp : ∀ r : R, r ^ 3 = 1
  exp' : ∀ r : R', r ^ 3 = 1
  comm : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a
  cen : R ⊓ R' = (Subgroup.center R).map R.subtype
  cen' : R ⊓ R' = (Subgroup.center R').map R'.subtype
  le : R ⊔ R' ≤ P
  norm : P ≤ normalizer (R : Set G)
  norm' : P ≤ normalizer (R' : Set G)

namespace TwoExtraThree

variable {P R R' : Subgroup G}

theorem isExtraspecial_sup (hT : TwoExtraThree P R R') :
    CFSG.IsExtraspecial 3 ↥(R ⊔ R') ∧ Nat.card ↥(R ⊔ R') = 3 ^ 5 :=
  isExtraspecial_sup_of_two_extraspecial_27 hT.extra hT.extra' hT.card hT.card' hT.exp hT.exp'
    hT.comm hT.cen hT.cen'

theorem card_inf (hT : TwoExtraThree P R R') : Nat.card ↥(R ⊓ R') = 3 := by
  rw [hT.cen, Subgroup.card_map_of_injective R.subtype_injective]
  exact hT.extra.center_order_p

theorem upperCentralSeries_two_map (hT : TwoExtraThree P R R') :
    (Subgroup.upperCentralSeries ↥(R ⊔ R') 2).map (R ⊔ R').subtype = R ⊔ R' := by
  have hext := hT.isExtraspecial_sup.1
  have hcommQ : _root_.commutator ↥(R ⊔ R') ≤ Subgroup.center ↥(R ⊔ R') :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      hext.quotient_elementary_abelian.toIsMulCommutative
  have htop : Subgroup.upperCentralSeries ↥(R ⊔ R') 2 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    have hxy : ⁅x, y⁆ ∈ _root_.commutator ↥(R ⊔ R') := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    simpa [commutatorElement_def] using hcommQ hxy
  rw [htop, Subgroup.map_top, Subgroup.range_subtype]

theorem center_map (hT : TwoExtraThree P R R') :
    (Subgroup.center ↥(R ⊔ R')).map (R ⊔ R').subtype = R ⊓ R' := by
  have hext := hT.isExtraspecial_sup.1
  have hle : R ⊓ R' ≤ (Subgroup.center ↥(R ⊔ R')).map (R ⊔ R').subtype := by
    intro z hz
    have hzQ : z ∈ R ⊔ R' := Subgroup.mem_sup_left hz.1
    have hzR : z ∈ (Subgroup.center R).map R.subtype := hT.cen ▸ hz
    have hQC : R ⊔ R' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le ?_ ?_
      · intro r hr
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzR
        have h' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨r, hr⟩)
        rw [← hwz]
        exact h'.symm
      · intro r' hr'
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hT.comm z hz.1 r' hr'
    refine Subgroup.mem_map.mpr ⟨⟨z, hzQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hQC q.2) z (Set.mem_singleton z)).symm
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (R ⊔ R').subtype_injective, hext.center_order_p,
    hT.card_inf]

theorem le_centralizer_inf (hT : TwoExtraThree P R R') (hP : IsPGroup 3 P) :
    P ≤ Subgroup.centralizer ((R ⊓ R' : Subgroup G) : Set G) :=
  CFSG.LocalAnalysis.GLTheoremA.le_centralizer_of_isPGroup_of_card_eq Nat.prime_three hP
    hT.card_inf fun _ hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hT.norm hx, hT.norm' hx⟩

end TwoExtraThree

theorem twoExtraThree_of_isSL3Four
    {M L L' P : Subgroup G} (hL : L ∈ calC M) (hset : conjSetOf M L = {L, L'}) (hLL' : L ≠ L')
    (hSL : IsSL3Four (Bar2 L)) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3) :
    TwoExtraThree P (P ⊓ L) (P ⊓ L') := by
  classical
  set R : Subgroup G := P ⊓ L with hRdef
  set R' : Subgroup G := P ⊓ L' with hR'def
  set Q : Subgroup G := R ⊔ R' with hQdef
  have hL'conj : L' ∈ conjSetOf M L := by
    rw [hset]
    simp
  have hL'calC : L' ∈ calC M := by
    obtain ⟨g, hgM, hL'map⟩ := hL'conj
    rw [hL'map]
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map M (MulAut.conj g)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.1
        (Subgroup.le_normalizer hgM)) hL
  have hSL' : IsSL3Four (Bar2 L') := by
    obtain ⟨g, -, hL'map⟩ := hL'conj
    obtain ⟨eBar⟩ := uc22p20d_bar2_conj g L
    have hL'map' : L' = uc22p20bCj g L := by
      simpa [uc22p20bCj] using hL'map
    have e : Bar2 L ≃* Bar2 L' := by
      rw [hL'map']
      exact eBar
    exact isSL3Four_of_mulEquiv e hSL
  have hLM : L ≤ M := hL.1.le
  have hL'M : L' ≤ M := hL'calC.1.le
  have hRP : R ≤ P := by rw [hRdef]; exact inf_le_left
  have hR'P : R' ≤ P := by rw [hR'def]; exact inf_le_left
  have hRL : R ≤ L := by rw [hRdef]; exact inf_le_right
  have hR'L' : R' ≤ L' := by rw [hR'def]; exact inf_le_right
  have hRM : R ≤ M := hRP.trans hP.le
  have hR'M : R' ≤ M := hR'P.trans hP.le
  have hR_sylow : CFSG.ABGLocalTools.IsSylowOf 3 R L := by
    rw [hRdef]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hLM hL.1.subgroupOf
  have hR'_sylow : CFSG.ABGLocalTools.IsSylowOf 3 R' L' := by
    rw [hR'def]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hL'M hL'calC.1.subgroupOf
  set A_bar : Subgroup (Bar2 M) := barImage M L with hAdef
  set B_bar : Subgroup (Bar2 M) := barImage M L' with hBdef
  set PA : Subgroup (Bar2 M) := barImage M R with hPAdef
  set PB : Subgroup (Bar2 M) := barImage M R' with hPBdef
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv (L := M) (K := L) hL
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv (L := M) (K := L') hL'calC
  have hSL_A : IsSL3Four ↥A_bar := isSL3Four_of_mulEquiv eA hSL
  have hSL_B : IsSL3Four ↥B_bar := isSL3Four_of_mulEquiv eB hSL'
  have hPA_sylow : CFSG.ABGLocalTools.IsSylowOf 3 PA A_bar := by
    rw [hPAdef, hAdef]
    exact isSylowOf_barImage_of_isSylowOf hLM hR_sylow eA
  have hPB_sylow : CFSG.ABGLocalTools.IsSylowOf 3 PB B_bar := by
    rw [hPBdef, hBdef]
    exact isSylowOf_barImage_of_isSylowOf hL'M hR'_sylow eB
  have hPA_le : PA ≤ A_bar := hPA_sylow.le
  have hPB_le : PB ≤ B_bar := hPB_sylow.le
  have hPA_abs : CFSG.ABGLocalTools.IsSylowOf 3 (PA.subgroupOf A_bar) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) A_bar
      (A := PA.subgroupOf A_bar) (B := ⊤)]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr hPA_le] using hPA_sylow
  have hPB_abs : CFSG.ABGLocalTools.IsSylowOf 3 (PB.subgroupOf B_bar) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) B_bar
      (A := PB.subgroupOf B_bar) (B := ⊤)]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr hPB_le] using hPB_sylow
  obtain ⟨hPA_ext, hPA_card⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hSL_A hPA_abs
  obtain ⟨hPB_ext, hPB_card⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hSL_B hPB_abs
  have hPAexp_abs : ∀ x : PA.subgroupOf A_bar, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hSL_A hPA_abs
  have hPBexp_abs : ∀ x : PB.subgroupOf B_bar, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hSL_B hPB_abs
  have hPAexp : ∀ x : PA, x ^ 3 = 1 := by
    intro x
    have h := hPAexp_abs ((Subgroup.subgroupOfEquivOfLe hPA_le).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hPA_le) h
    simpa using h'
  have hPBexp : ∀ x : PB, x ^ 3 = 1 := by
    intro x
    have h := hPBexp_abs ((Subgroup.subgroupOfEquivOfLe hPB_le).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hPB_le) h
    simpa using h'
  have hPA_ext' : CFSG.IsExtraspecial 3 ↥PA := by
    have : CFSG.IsExtraspecial 3 ↥(PA.subgroupOf A_bar) := hPA_ext
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPA_le).symm
  have hPB_ext' : CFSG.IsExtraspecial 3 ↥PB := by
    have : CFSG.IsExtraspecial 3 ↥(PB.subgroupOf B_bar) := hPB_ext
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPB_le).symm
  have hPA_card' : Nat.card PA = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA_le).toEquiv, hPA_card]
  have hPB_card' : Nat.card PB = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPB_le).toEquiv, hPB_card]
  have hR_iso : ↥R ≃* ↥PA :=
    equiv_barImage_of_isPGroup (hRP.trans hP.le) hR_sylow.isPGroup
  have hR'_iso : ↥R' ≃* ↥PB :=
    equiv_barImage_of_isPGroup (hR'P.trans hP.le) hR'_sylow.isPGroup
  have hR_ext : CFSG.IsExtraspecial 3 R := by
    have : CFSG.IsExtraspecial 3 ↥PA := hPA_ext'
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv hR_iso
  have hR'_ext : CFSG.IsExtraspecial 3 R' := by
    have : CFSG.IsExtraspecial 3 ↥PB := hPB_ext'
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv hR'_iso
  have hRcard : Nat.card R = 27 := by
    rw [Nat.card_congr hR_iso.toEquiv, hPA_card']
  have hR'card : Nat.card R' = 27 := by
    rw [Nat.card_congr hR'_iso.toEquiv, hPB_card']
  have hRexp : ∀ x : R, x ^ 3 = 1 := by
    intro x
    have h := hPAexp (hR_iso x)
    exact hR_iso.injective (by simpa [map_pow] using h)
  have hR'exp : ∀ x : R', x ^ 3 = 1 := by
    intro x
    have h := hPBexp (hR'_iso x)
    exact hR'_iso.injective (by simpa [map_pow] using h)
  have hcomm_bar : ∀ a ∈ barImage M L, ∀ b ∈ barImage M L', a * b = b * a :=
    uc22p22l_barImage_commute (L := M) hL hL'calC hLL'
  have hcomm : ∀ r ∈ R, ∀ r' ∈ R', r * r' = r' * r := by
    intro r hr r' hr'
    have hrM : r ∈ M := hRM hr
    have hr'M : r' ∈ M := hR'M hr'
    have hbar : uc22p21cPi M ⟨r, hrM⟩ * uc22p21cPi M ⟨r', hr'M⟩ =
        uc22p21cPi M ⟨r', hr'M⟩ * uc22p21cPi M ⟨r, hrM⟩ :=
      hcomm_bar _ (uc22p21c_mem_barImage.2 ⟨⟨r, hrM⟩, hRL hr, rfl⟩)
        _ (uc22p21c_mem_barImage.2 ⟨⟨r', hr'M⟩, hR'L' hr', rfl⟩)
    have hmem : ⁅r, r'⁆ ∈ CFSG.Open.pCoreOf 2 M :=
      uc22p22u_commutator_mem_pCoreOf (X := M) hrM hr'M hbar
    have hPcomm : ⁅r, r'⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem (hRP hr) (hR'P hr')) (P.inv_mem (hRP hr)))
        (P.inv_mem (hR'P hr'))
    have hdisj : Disjoint P (CFSG.Open.pCoreOf 2 M) :=
      IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (CFSG.Open.pCoreOf 2 M) hP.isPGroup
        ((CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype)
    have hone : ⁅r, r'⁆ = 1 := by
      have hbot : ⁅r, r'⁆ ∈ (⊥ : Subgroup G) := hdisj.le_bot ⟨hPcomm, hmem⟩
      exact Subgroup.mem_bot.mp hbot
    rw [commutatorElement_eq_one_iff_mul_comm] at hone
    exact hone
  have hRinfR'_le_Z : R ⊓ R' ≤ (Subgroup.center ↥R).map R.subtype := by
    intro y hy
    have hycent : (⟨y, hy.1⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      show (s : G) * y = y * (s : G)
      exact hcomm (s : G) s.property y hy.2
    exact Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, hycent, rfl⟩
  have hRinfR'_le_Z' : R ⊓ R' ≤ (Subgroup.center ↥R').map R'.subtype := by
    intro y hy
    have hycent : (⟨y, hy.2⟩ : ↥R') ∈ Subgroup.center ↥R' := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      show (s : G) * y = y * (s : G)
      exact (hcomm y hy.1 (s : G) s.property).symm
    exact Subgroup.mem_map.mpr ⟨⟨y, hy.2⟩, hycent, rfl⟩
  have hZcard : Nat.card ↥((Subgroup.center ↥R).map R.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact hR_ext.center_order_p
  have hZ'card : Nat.card ↥((Subgroup.center ↥R').map R'.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective R'.subtype_injective]
    exact hR'_ext.center_order_p
  have hRinfR'_ne_bot : R ⊓ R' ≠ ⊥ := by
    intro hbot
    obtain ⟨ER, -, hERle, hERea, hERcard⟩ :=
      exists_elemAbelian_nine_of_isExtraspecial_of_pow_three hR_ext hRexp
        (x := (1 : G)) R.one_mem
    obtain ⟨ER', -, hER'le, hER'ea, hER'card⟩ :=
      exists_elemAbelian_nine_of_isExtraspecial_of_pow_three hR'_ext hR'exp
        (x := (1 : G)) R'.one_mem
    have hEcomm : ∀ a ∈ ER, ∀ b ∈ ER', a * b = b * a :=
      fun a ha b hb => hcomm a (hERle ha) b (hER'le hb)
    have hEinf : ER ⊓ ER' = ⊥ := by
      apply le_antisymm _ bot_le
      calc ER ⊓ ER' ≤ R ⊓ R' := inf_le_inf hERle hER'le
        _ = ⊥ := hbot
    have hE81card : Nat.card ↥(ER ⊔ ER') = 81 := by
      have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute
        (A := ER) (B := ER') hEcomm
      rw [hEinf, Subgroup.card_bot, hERcard, hER'card] at h
      omega
    have hE81ea : CFSG.Open.IsElemAbelian 3 (ER ⊔ ER') :=
      CFSG.Open.IsElemAbelian.sup_of_commute hERea hER'ea hEcomm
    have hE81M : ER ⊔ ER' ≤ M :=
      sup_le (hERle.trans hRM) (hER'le.trans hR'M)
    have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
      CFSG.SectionRank.le_pRank (p := 3) (H := M) (k := 4)
        (by norm_num) hE81M hE81ea (by rw [hE81card]; norm_num)
    have hbound : CFSG.Open.pRank 3 M ≤ 3 := hm3
    omega
  have hRinfR'_card : Nat.card ↥(R ⊓ R') = 3 := by
    have hdvd : Nat.card ↥(R ⊓ R') ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le hRinfR'_le_Z
    have hne1 : Nat.card ↥(R ⊓ R') ≠ 1 := by
      intro h1
      exact hRinfR'_ne_bot (Subgroup.eq_bot_of_card_eq (R ⊓ R') h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hRinfR'_eq_Z : R ⊓ R' = (Subgroup.center ↥R).map R.subtype :=
    Subgroup.eq_of_le_of_card_ge hRinfR'_le_Z (by rw [hZcard, hRinfR'_card])
  have hRinfR'_eq_Z' : R ⊓ R' = (Subgroup.center ↥R').map R'.subtype :=
    Subgroup.eq_of_le_of_card_ge hRinfR'_le_Z' (by rw [hZ'card, hRinfR'_card])
  have hZeq : (Subgroup.center ↥R).map R.subtype =
      (Subgroup.center ↥R').map R'.subtype := hRinfR'_eq_Z.symm.trans hRinfR'_eq_Z'
  have h2 : (conjSetOf M L).ncard ≤ 2 := by
    rw [hset, Set.ncard_pair hLL']
  have h2' : (conjSetOf M L').ncard ≤ 2 := by
    rwa [uc22p2214_conjSetOf_eq hL'conj]
  have hPNL : P ≤ Subgroup.normalizer (L : Set G) := by
    intro p hp
    have hpM : p ∈ M := hP.le hp
    have hpodd : Odd (orderOf p) := by
      obtain ⟨k, hk⟩ := hP.isPGroup.exists_orderOf_eq_pow (⟨p, hp⟩ : ↥P)
      have hkG : orderOf p = 3 ^ k := by
        simpa using (Subgroup.orderOf_coe (⟨p, hp⟩ : ↥P)).trans hk
      rw [hkG]
      exact Odd.pow (by norm_num : Odd 3)
    exact mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order h2 hpM hpodd
  have hPNL' : P ≤ Subgroup.normalizer (L' : Set G) := by
    intro p hp
    have hpM : p ∈ M := hP.le hp
    have hpodd : Odd (orderOf p) := by
      obtain ⟨k, hk⟩ := hP.isPGroup.exists_orderOf_eq_pow (⟨p, hp⟩ : ↥P)
      have hkG : orderOf p = 3 ^ k := by
        simpa using (Subgroup.orderOf_coe (⟨p, hp⟩ : ↥P)).trans hk
      rw [hkG]
      exact Odd.pow (by norm_num : Odd 3)
    exact mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order h2' hpM hpodd
  have hPNR : P ≤ Subgroup.normalizer (R : Set G) := by
    intro p hp
    rw [hRdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := L)
      ⟨Subgroup.le_normalizer hp, hPNL hp⟩
  have hPNR' : P ≤ Subgroup.normalizer (R' : Set G) := by
    intro p hp
    rw [hR'def]
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := L')
      ⟨Subgroup.le_normalizer hp, hPNL' hp⟩
  exact ⟨hR_ext, hR'_ext, hRcard, hR'card, hRexp, hR'exp, hcomm, hRinfR'_eq_Z, hRinfR'_eq_Z',
    sup_le hRP hR'P, hPNR, hPNR'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
