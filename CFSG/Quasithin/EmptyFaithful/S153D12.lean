module

public import CFSG.Quasithin.EmptyFaithful.S153DDefs
public import CFSG.Quasithin.EmptyFaithful.S153DGen
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.C2Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem oTwoUpper_eq (h : Hyp15310 G T Mc M V₁ V₂ Yp t) : oTwoUpper Yp = Yp := by
  rcases h.cases with hY | ⟨-, hY⟩
  · rw [hY]; exact A4.oTwoUpper_oTwoUpper _
  · rw [hY]; exact A4.oTwoUpper_oTwoUpper _

end Hyp15310

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem Yp_le_normalizer (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hL : L ∈ cComp I) :
    Yp ≤ Subgroup.normalizer (L : Set G) := by
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hH : pCoreOf 2 I ≠ ⊥ := hI.1.2
  have hq := h.hyp.qtfe
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hH hL with hn | ⟨h2, -⟩
  · exact hYI.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hL)).mp hn)
  · exact le_normalizer_of_oTwoUpper_eq (le_of_mem_cComp hL) hYI h.oTwoUpper_eq (Or.inr h2)

theorem YL153_ne_bot (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (h3 : CFSG.Open.pRank 3 Yp = 2) (hL : L ∈ cComp I) (hL3 : 1 ≤ CFSG.Open.pRank 3 L) :
    YL153 Yp L ≠ ⊥ := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYN := Yp_le_normalizer h37 h38 h hI hL
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hLI := le_of_mem_cComp hL
  obtain ⟨E, hEY, hE, hE9⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Yp
  rw [h3] at hE9
  have hEL : E ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxL⟩
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx3)
    have : x ∈ YL153 Yp L := mem_oTwoUpper_of_odd ⟨hEY hxE, hxL⟩ hodd
    rw [hbot] at this
    exact this
  obtain ⟨EL, hELL, hELe, hELc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 3) hL3
  have h3L : 3 ∣ Nat.card L := by
    have : Nat.card EL ∣ Nat.card L := Subgroup.card_dvd_of_le hELL
    rw [hELc] at this
    simpa using this
  set X : Subgroup G := L ⊔ Yp with hX
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := sup_le hLN hYN
  have hn : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXN
  have h3X : 3 ≤ CFSG.Open.pRank 3 X := three_le_pRank_of_acts le_sup_left hn (hEY.trans le_sup_right) hE
    (by rw [hE9]; norm_num) hEL h3L
  have hXI : X ≤ I := sup_le hLI hYI
  have h2 := pRank_le_two_of_pCoreOf_ne_bot h.hyp.qtfe.qtke hI.1.2 Nat.prime_three (by norm_num)
  have h4 := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hXI
  omega

omit [Finite G] in
theorem mem_of_commutators_mem {X : Subgroup G} (hperf : ⁅X, X⁆ = X) (N : Subgroup ↥X)
    [N.Normal] [IsSimpleGroup (↥X ⧸ N)] {y : ↥X}
    (hy : ∀ l : ↥X, l * y * l⁻¹ * y⁻¹ ∈ N) : y ∈ N := by
  have hcen : (QuotientGroup.mk y : ↥X ⧸ N) ∈ Subgroup.center (↥X ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have := hy l
    rw [← QuotientGroup.eq_one_iff] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    calc (QuotientGroup.mk l : ↥X ⧸ N) * QuotientGroup.mk y
        = (QuotientGroup.mk l * QuotientGroup.mk y * (QuotientGroup.mk l)⁻¹ *
            (QuotientGroup.mk y)⁻¹) * (QuotientGroup.mk y * QuotientGroup.mk l) := by group
      _ = QuotientGroup.mk y * QuotientGroup.mk l := by rw [this, one_mul]
  rcases (Subgroup.center (↥X ⧸ N)).normal_of_characteristic.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
    exact hcen
  · exfalso
    have hcomm : ∀ a b : ↥X, a * b * a⁻¹ * b⁻¹ ∈ N := by
      intro a b
      rw [← QuotientGroup.eq_one_iff]
      have hb : (QuotientGroup.mk b : ↥X ⧸ N) ∈ Subgroup.center (↥X ⧸ N) := by rw [ht]; trivial
      have := Subgroup.mem_center_iff.mp hb (QuotientGroup.mk a)
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      calc (QuotientGroup.mk a * QuotientGroup.mk b * (QuotientGroup.mk a)⁻¹ *
            (QuotientGroup.mk b)⁻¹ : ↥X ⧸ N)
          = (QuotientGroup.mk b * QuotientGroup.mk a) * (QuotientGroup.mk a)⁻¹ *
              (QuotientGroup.mk b)⁻¹ := by rw [this]
        _ = 1 := by group
    have h1 : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⊤ := by
      have e := Subgroup.map_commutator (⊤ : Subgroup ↥X) (⊤ : Subgroup ↥X) X.subtype
      have e2 : (⊤ : Subgroup ↥X).map X.subtype = X := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [e2, hperf] at e
      exact Subgroup.map_injective X.subtype_injective (e.trans e2.symm)
    have htop : (⊤ : Subgroup ↥X) ≤ N := by
      rw [← h1, Subgroup.commutator_le]
      intro a _ b _
      exact hcomm a b
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥X ⧸ N)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by
      rw [(QuotientGroup.eq_one_iff a').mpr (htop trivial),
        (QuotientGroup.eq_one_iff b').mpr (htop trivial)])

omit [Finite G] in
theorem mem_pCore_iff {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff x).symm

omit [Finite G] in
theorem mem_pCoreOf_of_commutators {I L : Subgroup G} (hL : L ∈ cComp I)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {y : G} (hyL : y ∈ L)
    (hy : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L) : y ∈ pCoreOf 2 L := by
  have hN : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have := hsimple
  have h1 := mem_of_commutators_mem hL.2.1 (CFSG.pCore 2 ↥L) (y := ⟨y, hyL⟩) (fun l =>
    (mem_pCore_iff _).mpr (hy l l.2))
  exact (mem_pCore_iff _).mp h1

theorem sup_Sgp153_le_normalizer_Yp (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hF : Facts15311 T M V₁ Yp I) :
    Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
  refine sup_le Subgroup.le_normalizer fun s hs => ?_
  have hsI : s ∈ I := hI.1.1 (Subgroup.mem_sup_right hs)
  have hsM : s ∈ M ⊓ I := ⟨h.hyp.T_le hs.1, hsI⟩
  rw [← hF.norm_eq] at hsM
  exact hsM.2

theorem R153_le_normalizer (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15311 T M V₁ Yp I) (h3 : CFSG.Open.pRank 3 Yp = 2) (hL : L ∈ cComp I)
    (hL3 : 1 ≤ CFSG.Open.pRank 3 L) : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := by
  have hq := h.hyp.qtfe
  have hLI := le_of_mem_cComp hL
  have hYSI : Yp ⊔ Sgp153 T V₁ ≤ I := hI.1.1
  have hYI : Yp ≤ I := le_sup_left.trans hYSI
  have hRI : R153 T V₁ Yp ≤ I := (pCoreOf_le 2 _).trans hYSI
  have hRn : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (R153 T V₁ Yp : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hRp : IsPGroup 2 (R153 T V₁ Yp) := pCoreOf_isPGroup 2 _
  have hYSn : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) :=
    sup_Sgp153_le_normalizer_Yp h hI hF
  intro r hr
  by_contra hrn
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hI.1.2 hL with
    hnorm | ⟨-, htypes⟩
  · exact hrn ((Subgroup.normal_subgroupOf_iff_le_normalizer hLI).mp hnorm (hRI hr))
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
  set L' := L.map (MulAut.conj r).toMonoidHom with hL'
  have hL'c : L' ∈ cComp I := map_conj_mem_cComp hL (hRI hr)
  have hne : L ≠ L' := fun h' => hrn (A38.map_conj_eq_iff.mp h'.symm)
  obtain ⟨hc1, hc2⟩ := lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 hI.1.2 hL hL'c hne
  have key : ∀ y ∈ Yp ⊓ L, Odd (orderOf y) → y = 1 := by
    rintro y ⟨hyY, hyL⟩ hodd
    have hyI : y ∈ I := hYI hyY
    have hyYS : y ∈ Yp ⊔ Sgp153 T V₁ := Subgroup.mem_sup_left hyY
    have hr' : r ∈ Yp ⊔ Sgp153 T V₁ := pCoreOf_le 2 _ hr
    have hy'Y : r * y * r⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp (hYSn hr') y).mp hyY
    have hy'L' : r * y * r⁻¹ ∈ L' := by
      rw [hL', A38.mem_map_conj]
      simpa [mul_assoc] using hyL
    have hy'I : r * y * r⁻¹ ∈ I := hYI hy'Y
    have hcomm : y * (r * y * r⁻¹) * y⁻¹ * (r * y * r⁻¹)⁻¹ ∈ pCoreOf 2 I :=
      hc2 (hc1 (Subgroup.commutator_mem_commutator hyL hy'L'))
    have huR : y⁻¹ * (r * y * r⁻¹) ∈ R153 T V₁ Yp := by
      have h1 : y⁻¹ * r * y ∈ R153 T V₁ Yp := by
        have := (Subgroup.mem_normalizer_iff.mp (hRn ((Yp ⊔ Sgp153 T V₁).inv_mem hyYS)) r).mp hr
        simpa using this
      have : y⁻¹ * (r * y * r⁻¹) = (y⁻¹ * r * y) * r⁻¹ := by group
      rw [this]
      exact (R153 T V₁ Yp).mul_mem h1 ((R153 T V₁ Yp).inv_mem hr)
    set a : ↥I := ⟨y, hyI⟩ with ha
    set b : ↥I := ⟨r * y * r⁻¹, hy'I⟩ with hb
    have hcomm' : (QuotientGroup.mk a : OTwoQuot I) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := by
      rw [mk_commute_iff]
      exact hcomm
    have hbm : b ^ orderOf y = 1 := by
      apply Subtype.ext
      change (r * y * r⁻¹) ^ orderOf y = 1
      rw [conj_pow, pow_orderOf_eq_one]
      group
    have ham : a ^ orderOf y = 1 := Subtype.ext (by
      change y ^ orderOf y = 1
      exact pow_orderOf_eq_one y)
    have hcm : ((QuotientGroup.mk a : OTwoQuot I)⁻¹ * QuotientGroup.mk b) ^ orderOf y = 1 := by
      rw [(Commute.inv_left hcomm').mul_pow, inv_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
        ham, hbm]
      simp
    obtain ⟨k, hk⟩ := hRp ⟨_, huR⟩
    have hc2k : ((QuotientGroup.mk a : OTwoQuot I)⁻¹ * QuotientGroup.mk b) ^ 2 ^ k = 1 := by
      have hk' : (y⁻¹ * (r * y * r⁻¹)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have : a⁻¹ * b = ⟨y⁻¹ * (r * y * r⁻¹), I.mul_mem (I.inv_mem hyI) hy'I⟩ := rfl
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, this,
        (Subtype.ext hk' : (⟨y⁻¹ * (r * y * r⁻¹), _⟩ : ↥I) ^ 2 ^ k = 1), QuotientGroup.mk_one]
    have hcop : Nat.Coprime (orderOf y) (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
    have hc1' : (QuotientGroup.mk a : OTwoQuot I)⁻¹ * QuotientGroup.mk b = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hcm
      have h2 := orderOf_dvd_of_pow_eq_one hc2k
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    have hmab : (QuotientGroup.mk a : OTwoQuot I) = QuotientGroup.mk b := inv_mul_eq_one.mp hc1'
    have hLO : L ⊓ pCoreOf 2 I ≤ pCoreOf 2 L :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 I (hLI hg)⟩)
        ((pCoreOf_isPGroup 2 I).to_le inf_le_right)
    have hy : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
      intro l hl
      have hlI : l ∈ I := hLI hl
      have hlb : l * (r * y * r⁻¹) * l⁻¹ * (r * y * r⁻¹)⁻¹ ∈ pCoreOf 2 I :=
        hc2 (hc1 (Subgroup.commutator_mem_commutator hl hy'L'))
      have hcl : (QuotientGroup.mk (⟨l, hlI⟩ : ↥I) : OTwoQuot I) * QuotientGroup.mk a =
          QuotientGroup.mk a * QuotientGroup.mk ⟨l, hlI⟩ := by
        rw [hmab, mk_commute_iff]
        exact hlb
      have hly : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 I := (mk_commute_iff ⟨l, hlI⟩ a).mp hcl
      have hlyL : l * y * l⁻¹ * y⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem hl hyL) (L.inv_mem hl)) (L.inv_mem hyL)
      exact hLO ⟨hlyL, hly⟩
    have hyO : y ∈ pCoreOf 2 L := mem_pCoreOf_of_commutators hL hsimple hyL hy
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨y, hyO⟩
    have hy2 : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_right.mpr hodd).pow_right j) dvd_rfl (orderOf_dvd_of_pow_eq_one hy2))
  have hYL : YL153 Yp L = ⊥ := by
    show oTwoUpper (Yp ⊓ L) = ⊥
    rw [eq_bot_iff, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hx, hxodd⟩
    exact Subgroup.mem_bot.mpr (key x hx hxodd)
  exact YL153_ne_bot h37 h38 h hI h3 hL hL3 hYL

theorem pCoreOf_sup_le_R153 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15311 T M V₁ Yp I) (hL : L ∈ cComp I) :
    pCoreOf 2 L ⊔ pCoreOf 2 (YL153 Yp L) ≤ R153 T V₁ Yp := by
  have hYN := Yp_le_normalizer h37 h38 h hI hL
  have hYSn := sup_Sgp153_le_normalizer_Yp h hI hF
  refine sup_le ?_ ?_
  · exact (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL)).trans
      (c2_1_pCore_le hF.radical)
  ·
    have hYLN : Yp ≤ Subgroup.normalizer (YL153 Yp L : Set G) := fun g hg =>
      normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, hYN hg⟩)
    have h1 : pCoreOf 2 (YL153 Yp L) ≤ pCoreOf 2 Yp :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans ((oTwoUpper_le _).trans inf_le_left))
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 _ (hYLN hg)) (pCoreOf_isPGroup 2 _)
    have h2 : pCoreOf 2 Yp ≤ R153 T V₁ Yp :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 _ (hYSn hg)) (pCoreOf_isPGroup 2 _)
    exact h1.trans h2

theorem lemma_15_3_12_one (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15311 T M V₁ Yp I) (h3 : CFSG.Open.pRank 3 Yp = 2) (hL : L ∈ cComp I)
    (hL3 : 1 ≤ CFSG.Open.pRank 3 L) :
    YL153 Yp L ≠ ⊥ ∧ R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) ∧
      pCoreOf 2 L ⊔ pCoreOf 2 (YL153 Yp L) ≤ R153 T V₁ Yp :=
  ⟨YL153_ne_bot h37 h38 h hI h3 hL hL3, R153_le_normalizer h37 h38 h hI hF h3 hL hL3,
    pCoreOf_sup_le_R153 h37 h38 h hI hF hL⟩

end S153D

end CFSG.Quasithin
