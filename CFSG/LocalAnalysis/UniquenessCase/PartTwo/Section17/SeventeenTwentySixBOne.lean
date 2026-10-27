module

public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.GroupTheory.OddAutomorphismTwoGroup
public import CFSG.GroupTheory.OddOrderPGroup
public import CFSG.Permutation.FiveTransitive.TwoGroupFiveAutomorphism
public import CFSG.Quasithin.Vol2.Ch10SecB3GL4
public import CFSG.RankThree.PartTwo.Sec15.F153A10KAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveH2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNineProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qr
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviGeneric
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.GroupTheory

open Subgroup

theorem le_centralizer_of_perfect_of_isSimple_quotient_twentyfive
    {G : Type} [Group G] [Finite G] {V L : Subgroup G} (P : Subgroup ↥L) [P.Normal]
    (hLperf : ⁅L, L⁆ = L) (hP2 : IsPGroup 2 P)
    (hLsimple : IsSimpleGroup (↥L ⧸ P)) (h25 : 25 ∣ Nat.card (↥L ⧸ P))
    (hLN : L ≤ normalizer (V : Set G)) (hV : CFSG.Open.IsElemAbelian 2 V)
    (h16 : Nat.card V ≤ 16) :
    L ≤ centralizer (V : Set G) := by
  intro l hl
  let φ : ↥L →* MulAut ↥V := (CFSG.Quasithin.conjAct V).comp (Subgroup.inclusion hLN)
  haveI hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
  have hQ25 : ¬ 25 ∣ Nat.card ↥φ.range := by
    letI : CommGroup ↥V := CFSG.Quasithin.commGroupOfElemAbelian hV
    have hsq : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
    have hd : (CFSG.Quasithin.fixV φ.range).index ≤ 2 ^ 6 :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)).trans (h16.trans (by norm_num))
    exact CFSG.RankThree.PartTwo.Sec15.F153A10K.not_twentyfive_dvd_card hsq φ.range hd
  have hφ1 : φ = 1 :=
    eq_one_of_perfect_of_simple_quotient_of_dvd P hP2 hLsimple h25 φ hQ25
  have hconj : CFSG.Quasithin.conjAct V ⟨l, hLN hl⟩ = 1 := by
    have := congrArg (fun f : ↥L →* MulAut ↥V => f ⟨l, hl⟩) hφ1
    simpa [φ, Subgroup.inclusion] using this
  exact (CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).mp hconj

end CFSG.GroupTheory

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem barSub_ne_bot_of_ctx17 {D : Data G} {V₀ V : Subgroup G}
    (h25 : R17_25At D V₀ V) {L : Subgroup G} (c : Ctx17_17 D V₀ V L) :
    barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ := by
  have hV := c.hyp125.isElemAbelian
  have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcardW : Nat.card (Vtil V₀ V hV) = 2 ^ 12 := by
    rw [← Subgroup.card_top (G := Vtil V₀ V hV),
      CFSG.Quasithin.card_eq_two_pow hsq ⊤, CFSG.Quasithin.rk_top, (h25 L c).2.1]
  exact ne_bot_of_isIrrOn_of_two_lt_card hsq (h25 L c).1 (by rw [hcardW]; norm_num)

theorem isSimpleGroup_bar2_of_J2 {L : Subgroup G}
    (hJ2 : IsSpor (Bar2 L) .J2) : IsSimpleGroup (Bar2 L) := by
  obtain ⟨e⟩ := hJ2
  exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2

theorem cTilde_le_centSection {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hNL : D.M ≤ normalizer (L : Set G))
    (hsimple : IsSimpleGroup (Bar2 L)) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    F11.CTilde D.M V₀ V ≤ centSection D.M L (pCoreOf 2 L) := by
  intro c hc
  have hV := h.isElemAbelian
  have hMnorm := h.pairFacts.le_normalizer
  have hMnorm₀ := h.pairFacts.le_normalizer₀
  have hcM : c ∈ D.M := cTilde_le_M D.M V₀ V hc
  have hLM : L ≤ D.M := hL.1.le
  have hCtN : D.M ≤ normalizer (F11.CTilde D.M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M D.M V₀ V)).mp
      (cTilde_subgroupOf_normal hV hMnorm hMnorm₀)
  refine ⟨hcM, hNL hcM, UC6S846.normalizer_le_normalizer_pCoreOf L (hNL hcM), fun a ha => ?_⟩
  have haL : c * a * c⁻¹ * a⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNL hcM) a).1 ha) (L.inv_mem ha)
  have h1 : a * c⁻¹ * a⁻¹ ∈ F11.CTilde D.M V₀ V :=
    (Subgroup.mem_normalizer_iff.mp (hCtN (hLM ha)) c⁻¹).1 (inv_mem hc)
  have hC : c * a * c⁻¹ * a⁻¹ ∈ F11.CTilde D.M V₀ V := by
    have h2 : c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) := by group
    rw [h2]
    exact mul_mem hc h1
  obtain ⟨-, hs, hact⟩ := (mem_cTilde_iff hV hMnorm).1 hC
  exact mem_pCoreOf_of_actTil_eq_one h hL.1 hsimple hL1 haL hs hact

theorem exists_five_mem_centralizer_inf_cTilde
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L) (hx : DataExt D)
    (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V) (h25 : R17_25At D V₀ V)
    (h26a : R17_26aAt D V₀ V) (hHJ : K_HJData)
    {v : G} (hv : v ∈ V) (hvV₀ : v ∉ V₀) :
    ∃ y ∈ (D.M ⊓ centralizer ({v} : Set G)) ⊓ F11.CTilde D.M V₀ V, orderOf y = 5 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := c.hyp125
  have hV := h.isElemAbelian
  have hpair := h.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpair.le_normalizer hpair.le_normalizer₀
  have h5 : 5 ∈ D.sig := by rw [sig_eq_five_of_J2_ctx D h22 h23 c]; exact Set.mem_singleton 5
  obtain ⟨-, -, hSpor, -, -, hdvd0⟩ := hjSetup_of_ctx17 D h22 h23 h25 hHJ c
  obtain ⟨e⟩ := hSpor
  have hcardL : Nat.card ↥(barSub V₀ V hV L) = 604800 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hnot : ¬ 5 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    intro h125
    have := h125.trans hdvd0
    rw [hcardL] at this
    norm_num at this
  obtain ⟨y, hyC, hyord⟩ := PartTwo.Sixteen21.exists_mem_cTilde_of_not_dvd hV hMs
    Nat.prime_five (hx.three_le 5 h5) hnot
  have hCiff := fun m : G =>
    mem_cTilde_iff_centralizes (m := m) hV hpair.le_normalizer hpair.le_normalizer₀
  have hyCM := (hCiff y).1 hyC
  have hyM : y ∈ D.M := hyCM.1
  have hy5 : y ^ 5 = 1 := hyord ▸ pow_orderOf_eq_one y
  have hV₀2 : IsPGroup 2 ↥V₀ := hpair.elemAbelian₀.isPGroup
  by_cases hyV₀ : y ∈ centralizer (V₀ : Set G)
  · have hyV : y ∈ centralizer (V : Set G) :=
      CFSG.mem_centralizer_of_odd_pow_eq_one hV₀2 (by decide : Odd 5) hy5 hyV₀
        (fun p hp => by rw [commutatorElement_def]; exact hyCM.2 p hp)
    exact ⟨y, ⟨⟨hyM, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv) hyV⟩, hyC⟩,
      hyord⟩
  · have hyN : y ∈ normalizer (V₀ : Set G) := hpair.le_normalizer₀ hyM
    have hV₀ne : V₀ ≠ ⊥ := by
      intro hb
      apply hyV₀
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hb, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
      rw [hx, one_mul, mul_one]
    set a : MulAut ↥V₀ := CFSG.Quasithin.conjAct V₀ ⟨y, hyN⟩ with ha
    have ha1 : a ≠ 1 := fun h1 => hyV₀ ((CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).1 h1)
    have ha5 : a ^ 5 = 1 := by
      have : (⟨y, hyN⟩ : ↥(normalizer (V₀ : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
      rw [ha, ← map_pow, this, map_one]
    have haord : orderOf a = 5 := orderOf_eq_prime ha5 ha1
    have hcard16 : Nat.card ↥V₀ = 16 := by
      have hle : Nat.card ↥V₀ ≤ 16 := by
        rw [card_eq_two_pow_mSub hV₀2]
        calc 2 ^ mSub V₀ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (h26a L c)
          _ = 16 := by norm_num
      exact CFSG.FiveTransitive.TwoGroupFiveAutomorphism.card_eq_sixteen_of_order_five
        ↥V₀ hV₀2 hle a haord
    have hfpf : ∀ w : ↥V₀, a w = w → w = 1 := fun w hw =>
      CFSG.Quasithin.Vol2.Ch10.SecB.fixedPoints_trivial_of_orderOf_five hcard16 haord hw
    have hirr : ∀ U : Subgroup G, U ≤ V₀ → F11.CTilde D.M V₀ V ≤ normalizer (U : Set G) →
        U = ⊥ ∨ U = V₀ := by
      intro U hUV₀ hCU
      by_cases hU : U = ⊥
      · exact Or.inl hU
      right
      have hyNU : y ∈ normalizer (U : Set G) := hCU hyC
      set b : MulAut ↥U := CFSG.Quasithin.conjAct U ⟨y, hyNU⟩ with hb
      have hb5 : b ^ 5 = 1 := by
        have : (⟨y, hyNU⟩ : ↥(normalizer (U : Set G))) ^ 5 = 1 :=
          Subtype.ext (by simpa using hy5)
        rw [hb, ← map_pow, this, map_one]
      have hb1 : b ≠ 1 := by
        intro h1
        obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hU
        have hyu : y ∈ centralizer (U : Set G) :=
          (CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).1 h1
        have hfix : a ⟨(u : G), hUV₀ u.2⟩ = ⟨(u : G), hUV₀ u.2⟩ := by
          apply Subtype.ext
          rw [ha, CFSG.Quasithin.AutOn.coe_conjAct_apply]
          have := Subgroup.mem_centralizer_iff.1 hyu (u : G) u.2
          change y * (u : G) * y⁻¹ = (u : G)
          rw [← this, mul_inv_cancel_right]
        have := hfpf _ hfix
        exact hu1 (Subtype.ext (by simpa using congrArg Subtype.val this))
      have hbord : orderOf b = 5 := orderOf_eq_prime hb5 hb1
      have hU2 : IsPGroup 2 ↥U := hV₀2.to_le hUV₀
      have hUle : Nat.card ↥U ≤ 16 := hcard16 ▸ Subgroup.card_le_of_le hUV₀
      have hU16 := CFSG.FiveTransitive.TwoGroupFiveAutomorphism.card_eq_sixteen_of_order_five
        ↥U hU2 hUle b hbord
      exact Subgroup.eq_of_le_of_card_ge hUV₀ (by rw [hU16, hcard16])
    letI : CommGroup ↥V₀ := CFSG.Quasithin.commGroupOfElemAbelian hpair.elemAbelian₀
    let ψ : ↥V₀ → ↥V₀ := fun w => a w / w
    have hψinj : Function.Injective ψ := by
      intro w₁ w₂ hw
      have h1 : a w₁ * w₂ = a w₂ * w₁ := div_eq_div_iff_mul_eq_mul.1 hw
      have hfix : a (w₁ / w₂) = w₁ / w₂ := by
        rw [map_div]
        exact div_eq_div_iff_mul_eq_mul.2 (h1.trans (mul_comm _ _))
      exact div_eq_one.1 (hfpf _ hfix)
    let e : ↥V₀ := ⟨y * v * y⁻¹ * v⁻¹, hyCM.2 v hv⟩
    obtain ⟨d, hd⟩ := (Finite.injective_iff_surjective.1 hψinj) e⁻¹
    have had : a d = e⁻¹ * d := by
      rw [← hd]
      exact (div_mul_cancel (a d) d).symm
    have hyd : y * (d : G) * y⁻¹ = (e : G)⁻¹ * (d : G) := by
      have := congrArg Subtype.val had
      rw [ha, CFSG.Quasithin.AutOn.coe_conjAct_apply] at this
      simpa using this
    have hdV : (d : G) ∈ V := hpair.le d.2
    have heV : (e : G) ∈ V := hpair.le e.2
    have hev : (e : G) * v = v * (e : G) := B2F.isElemAbelian_comm hV heV hv
    have hc : y * (v * (d : G)) * y⁻¹ = v * (d : G) := by
      have hyv : y * v * y⁻¹ = (e : G) * v := by
        show y * v * y⁻¹ = y * v * y⁻¹ * v⁻¹ * v
        group
      calc y * (v * (d : G)) * y⁻¹ = (y * v * y⁻¹) * (y * (d : G) * y⁻¹) := by group
        _ = ((e : G) * v) * ((e : G)⁻¹ * (d : G)) := by rw [hyv, hyd]
        _ = v * (d : G) := by
          rw [hev]
          group
    have hcV : v * (d : G) ∈ V := V.mul_mem hv hdV
    have hcV₀ : v * (d : G) ∉ V₀ := by
      intro hmem
      apply hvV₀
      have := V₀.mul_mem hmem (V₀.inv_mem d.2)
      simpa using this
    obtain ⟨x, hx, hxc⟩ := exists_conj_eq_mul_of_inCalV0 (S19.inCalV0_of_hyp125 h hV₀ne)
      hCiff hirr hcV hcV₀ (V₀.inv_mem d.2)
    have hxC : x ∈ F11.CTilde D.M V₀ V := hx.1
    have hxv : x * (v * (d : G)) * x⁻¹ = v := by rw [hxc]; group
    have hy'C : x * y * x⁻¹ ∈ F11.CTilde D.M V₀ V := mul_mem (mul_mem hxC hyC) (inv_mem hxC)
    have hy'v : x * y * x⁻¹ ∈ centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have hcy : (v * (d : G)) * y = y * (v * (d : G)) := by
        calc (v * (d : G)) * y = (y * (v * (d : G)) * y⁻¹) * y := by rw [hc]
          _ = y * (v * (d : G)) := by group
      calc v * (x * y * x⁻¹) = x * (v * (d : G)) * x⁻¹ * (x * y * x⁻¹) := by rw [hxv]
        _ = x * ((v * (d : G)) * y) * x⁻¹ := by group
        _ = x * (y * (v * (d : G))) * x⁻¹ := by rw [hcy]
        _ = (x * y * x⁻¹) * (x * (v * (d : G)) * x⁻¹) := by group
        _ = (x * y * x⁻¹) * v := by rw [hxv]
    refine ⟨x * y * x⁻¹, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨((hCiff _).1 hy'C).1, hy'v⟩, hy'C⟩, ?_⟩
    have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective y
    rw [← hyord, ← this]
    simp [MulAut.conj_apply]

theorem seventeen_twentysix_b_one
    (D : Data G) (V₀ V : Subgroup G) (hx : DataExt D) (h880 : F08.R880 D)
    (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V) (h25 : R17_25At D V₀ V)
    (h26a : R17_26aAt D V₀ V) :
    R17_26b_1At D V₀ V := by
  have hHJ : K_HJData := k_HJData_holds
  intro L c v _hv1 hvV₀
  have h := c.hyp125
  have hJ2 := h23 L c
  have hNL : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (normal_of_J2_ctx D h22 h23 c)
  have hle := cTilde_le_centSection h c.mem_calC hNL (isSimpleGroup_bar2_of_J2 hJ2)
    (barSub_ne_bot_of_ctx17 h25 c)
  have hup : CFSG.Open.pRank 5 ((D.M ⊓ centralizer ({(v : G)} : Set G)) ⊓ F11.CTilde D.M V₀ V :
      Subgroup G) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (inf_le_right.trans hle)).trans
      (pRank_five_centSection_le_one hNL hJ2 h880 h22 h23 c)
  obtain ⟨y, hy, hyord⟩ :=
    exists_five_mem_centralizer_inf_cTilde c hx h22 h23 h25 h26a hHJ v.2 hvV₀
  have hcard : Nat.card (Subgroup.zpowers y) = 5 := by rw [Nat.card_zpowers, hyord]
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hlow : 1 ≤ CFSG.Open.pRank 5 ((D.M ⊓ centralizer ({(v : G)} : Set G)) ⊓
      F11.CTilde D.M V₀ V : Subgroup G) :=
    CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.zpowers_le.mpr hy)
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hcard) (hcard.trans (pow_one 5).symm)
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact le_antisymm hup hlow

theorem exists_lift_five {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hsimple : IsSimpleGroup (Bar2 L))
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {xb : MulAut (Vtil V₀ V h.isElemAbelian)} (hxb : xb ∈ barSub V₀ V h.isElemAbelian L)
    (hxo : orderOf xb = 5) :
    ∃ x : stabTil V₀ V, (x : G) ∈ L ∧ orderOf (x : G) = 5 ∧
      ∃ b : ℕ, actTil V₀ V h.isElemAbelian x = xb ^ (2 ^ b) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hgL, hgx⟩ := (mem_barSub V₀ V h.isElemAbelian L xb).1 hxb
  have hg5act : actTil V₀ V h.isElemAbelian (g ^ 5) = 1 := by
    rw [map_pow, hgx, ← hxo, pow_orderOf_eq_one]
  have hg5L : ((g ^ 5 : stabTil V₀ V) : G) ∈ L := by
    rw [Subgroup.coe_pow]; exact L.pow_mem hgL 5
  have hg5O : ((g ^ 5 : stabTil V₀ V) : G) ∈ pCoreOf 2 L :=
    mem_pCoreOf_of_actTil_eq_one h hL.1 hsimple hL1 hg5L (g ^ 5).2 hg5act
  obtain ⟨b, hb⟩ := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 L ⟨_, hg5O⟩
  have hb' : ((g : G) ^ 5) ^ (2 ^ b) = 1 := by
    have := congrArg Subtype.val hb
    simpa [Subgroup.coe_pow] using this
  refine ⟨g ^ (2 ^ b), ?_, ?_, b, by rw [map_pow, hgx]⟩
  · rw [Subgroup.coe_pow]; exact L.pow_mem hgL _
  · have hx5 : ((g ^ (2 ^ b) : stabTil V₀ V) : G) ^ 5 = 1 := by
      rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul]
      exact hb'
    have hx1 : ((g ^ (2 ^ b) : stabTil V₀ V) : G) ≠ 1 := by
      intro h1
      have hg1 : g ^ (2 ^ b) = 1 := Subtype.ext h1
      have h1' : xb ^ (2 ^ b) = 1 := by rw [← hgx, ← map_pow, hg1, map_one]
      have h5 : 5 ∣ 2 ^ b := hxo ▸ orderOf_dvd_of_pow_eq_one h1'
      have := Nat.prime_five.dvd_of_dvd_pow h5
      omega
    exact orderOf_eq_prime hx5 hx1

theorem seventeen_twentysix_b_two
    (D : Data G) (V₀ V : Subgroup G) (hx : DataExt D)
    (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V) (h25 : R17_25At D V₀ V)
    (h26a : R17_26aAt D V₀ V) :
    R17_26b_2At D V₀ V := by
  have hHJ : K_HJData := k_HJData_holds
  classical
  intro L c v hvV₀ h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := c.hyp125
  have hV := h.isElemAbelian
  have hpair := h.pairFacts
  have hLM : L ≤ D.M := c.mem_calC.1.le
  obtain ⟨hLMb, hnorm, -, -, -, hdvd⟩ := hjSetup_of_ctx17 D h22 h23 h25 hHJ c
  have hJ2 := h23 L c
  have hsimple := isSimpleGroup_bar2_of_J2 hJ2
  have hL1 := barSub_ne_bot_of_ctx17 h25 c
  obtain ⟨xs, hxs⟩ := exists_prime_orderOf_dvd_card' 5 h5
  set xb : MulAut (Vtil V₀ V hV) := (xs : MulAut (Vtil V₀ V hV)) with hxbdef
  have hxo : orderOf xb = 5 := by rw [hxbdef, Subgroup.orderOf_coe, hxs]
  have hxstab := (Subgroup.mem_inf.1 xs.2).1
  have hxM := (Subgroup.mem_inf.1 xs.2).2
  have hidx : ¬ 5 ∣ (barSub V₀ V hV L).relIndex (Mbar D.M V₀ V hV) := by
    intro h5i
    have hmul := Subgroup.relIndex_mul_card (H := barSub V₀ V hV L) (K := Mbar D.M V₀ V hV)
    rw [inf_of_le_left hLMb] at hmul
    have hpos : 0 < Nat.card ↥(barSub V₀ V hV L) := Nat.card_pos
    have h2 : (barSub V₀ V hV L).relIndex (Mbar D.M V₀ V hV) * Nat.card ↥(barSub V₀ V hV L) ∣
        6 * Nat.card ↥(barSub V₀ V hV L) := by
      rw [hmul]; exact hdvd
    have h3 := Nat.dvd_of_mul_dvd_mul_right hpos ((Nat.mul_dvd_mul_right h5i _).trans h2)
    omega
  have hxL : xb ∈ barSub V₀ V hV L :=
    FongLevi.mem_of_orderOf_prime_of_coprime_relIndex hLMb hnorm Nat.prime_five hidx hxM hxo
  obtain ⟨x, hxL', hxo', b, hxact⟩ := exists_lift_five h c.mem_calC hsimple hL1 hxL hxo
  have hx1 : actTil V₀ V hV x ≠ 1 := by
    rw [hxact]
    intro h1
    have h5 : 5 ∣ 2 ^ b := hxo ▸ orderOf_dvd_of_pow_eq_one h1
    have := Nat.prime_five.dvd_of_dvd_pow h5
    omega
  have hxv0 : (x : G) * v * (x : G)⁻¹ * (v : G)⁻¹ ∈ V₀ := by
    have hst : xb ^ (2 ^ b) ∈ MulAction.stabilizer (MulAut (Vtil V₀ V hV))
        (mkTil V₀ V hV (IntMod.mk hV v)) := Subgroup.pow_mem _ hxstab _
    rw [← hxact, MulAction.mem_stabilizer_iff, MulAut.smul_def, actTil_mk, mkTil_eq_iff,
      actStab_apply_val] at hst
    exact hst
  have hV₀2 : IsPGroup 2 ↥V₀ := hpair.elemAbelian₀.isPGroup
  have h16 : Nat.card ↥V₀ ≤ 16 := by
    rw [card_eq_two_pow_mSub hV₀2]
    calc 2 ^ mSub V₀ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (h26a L c)
      _ = 16 := by norm_num
  have h25d : 25 ∣ Nat.card (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2]
    norm_num
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hLC : L ≤ centralizer (V₀ : Set G) :=
    CFSG.GroupTheory.le_centralizer_of_perfect_of_isSimple_quotient_twentyfive
      (CFSG.pCore 2 ↥L) c.mem_calC.2.1 CFSG.pCore_isPGroup hsimple h25d
      (hLM.trans hpair.le_normalizer₀) hpair.elemAbelian₀ h16
  have hx5 : (x : G) ^ 5 = 1 := hxo' ▸ pow_orderOf_eq_one (x : G)
  have hxv : (x : G) * v * (x : G)⁻¹ = v :=
    uc22p22q_conj_eq_of_trivial_action Nat.prime_five (by norm_num)
      (fun d hd => hpair.elemAbelian₀.2 d hd) hx5
      (fun d hd => by
        have := Subgroup.mem_centralizer_iff.1 (hLC hxL') d hd
        rw [← this, mul_inv_cancel_right]) hxv0
  have hxCv : (x : G) ∈ D.M ⊓ centralizer ({(v : G)} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hLM hxL', ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc (v : G) * (x : G) = ((x : G) * v * (x : G)⁻¹) * (x : G) := by rw [hxv]
      _ = (x : G) * v := by group
  obtain ⟨y, hy, hyord⟩ :=
    exists_five_mem_centralizer_inf_cTilde c hx h22 h23 h25 h26a hHJ v.2 hvV₀
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  by_contra hle
  push Not at hle
  have hcy : Nat.card (Subgroup.zpowers y) = 5 := by rw [Nat.card_zpowers, hyord]
  have hcx : Nat.card (Subgroup.zpowers (x : G)) = 5 := by rw [Nat.card_zpowers, hxo']
  obtain ⟨k, hk, hkmap⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime (p := 5) hle
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.1 hy).1) (Subgroup.zpowers_le.mpr hxCv) hcy hcx
  have hxmem : (x : G) ∈ (Subgroup.zpowers y).map (MulAut.conj k).toMonoidHom := by
    rw [hkmap]; exact Subgroup.mem_zpowers _
  obtain ⟨y', hy', hy'x⟩ := hxmem
  have hCtN : D.M ≤ normalizer (F11.CTilde D.M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M D.M V₀ V)).mp
      (cTilde_subgroupOf_normal hV hpair.le_normalizer hpair.le_normalizer₀)
  have hy'C : y' ∈ F11.CTilde D.M V₀ V :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.1 hy).2) hy'
  have hxC : (x : G) ∈ F11.CTilde D.M V₀ V := by
    rw [← hy'x]
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp (hCtN (Subgroup.mem_inf.1 hk).1) y').1 hy'C
  obtain ⟨-, hs, hact⟩ := (mem_cTilde_iff hV hpair.le_normalizer).1 hxC
  exact hx1 hact

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
