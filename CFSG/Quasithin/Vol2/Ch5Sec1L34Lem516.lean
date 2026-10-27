module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Comp
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.Quasithin.Vol2.Ch5Sec1Borel
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2
public import CFSG.Quasithin.Background.A3Structure312Embed
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.BorelTits.Suzuki
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
import CFSG.Adapters.LieModelSmallOrders
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5115
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall_conj_mem' {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ Subgroup.normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have heq : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨k, hk, hkx⟩ := hx
  have hkx' : g * k * g⁻¹ = g * x * g⁻¹ := hkx
  have : k = x := by simpa using hkx'
  rw [← this]
  exact hk

theorem center_eq_bot_of_isSimpleGroup_of_not_prime {X : Type} [Group X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact hc
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b) a)
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcomm }
    exact h IsSimpleGroup.prime_card

theorem pCoreOf_ne_bot_of_subnormal {Y M : Subgroup G} (hYM : IsSubnormal Y M) (hM : CharTwo M)
    (hY : Y ≠ ⊥) : pCoreOf 2 Y ≠ ⊥ := by
  intro hbot
  apply hY
  have hc := A4.charTwo_of_subnormal hYM hM
  rw [CharTwo, hbot] at hc
  have hY' : Y ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := fun y _ => by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hz
    rw [hz, one_mul, mul_one]
  exact le_bot_iff.mp ((le_inf le_rfl hY').trans hc)

theorem mem_of_pow_eq_one_of_mem_normalizer {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (S : Sylow p X) {q : X} (hq : q ∈ Subgroup.normalizer (S : Set X))
    {m : ℕ} (hqm : q ^ p ^ m = 1) : q ∈ (S : Subgroup X) := by
  have hle : (S : Subgroup X) ≤ (S : Subgroup X) ⊔ Subgroup.zpowers q := le_sup_left
  have hP : IsPGroup p ↥((S : Subgroup X) ⊔ Subgroup.zpowers q) := by
    have hzN : Subgroup.zpowers q ≤ Subgroup.normalizer (S : Set X) :=
      Subgroup.zpowers_le.mpr hq
    have hzp : IsPGroup p (Subgroup.zpowers q) :=
      IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hqm)
    exact (S.isPGroup').to_sup_of_normal_left' hzp hzN
  have heq := S.is_maximal' hP hle
  have : q ∈ (S : Subgroup X) ⊔ Subgroup.zpowers q :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers q)
  rwa [heq] at this

theorem card_of_lieModel_L34 {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Blueprint.LieModel.card_psl_three_four h

theorem card_of_suzukiModel
    {X : Type} [Group X] {f : ℕ} (h : SuzukiModel X 2 f) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧
      Nat.card X = (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  refine ⟨a, ha, hf, ?_⟩
  rw [Nat.card_congr e.toEquiv, hf, CFSG.LieType.Ree.suzuki_order (hf ▸ hK)]

theorem five_dvd_card_of_suzukiModel
    {X : Type} [Group X] {f : ℕ} (h : SuzukiModel X 2 f) :
    5 ∣ Nat.card X ∧ ¬ (Nat.card X).Prime := by
  obtain ⟨a, ha, hf, hc⟩ := card_of_suzukiModel h
  rw [hc]
  constructor
  · apply Dvd.dvd.mul_left
    have e : (2 ^ f) ^ 2 = 4 * 16 ^ a := by
      rw [hf, ← pow_mul, show (2 * a + 1) * 2 = 4 * a + 2 by ring, pow_add, pow_mul]
      norm_num
      ring
    have h16 : 16 ^ a % 5 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [e]
    omega
  · intro hp
    have h4 : 4 ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
      apply Dvd.dvd.mul_right
      apply Dvd.dvd.mul_right
      rw [← pow_mul]
      exact (pow_dvd_pow 2 (by omega : 2 ≤ f * 2))
    have h2 : (2 : ℕ) ∣ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) :=
      (show (2 : ℕ) ∣ 4 by norm_num).trans h4
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · rw [← h] at h4
      norm_num at h4

theorem exists_mulEquiv_sz_of_suzukiModel {X : Type} [Group X] {f : ℕ}
    (h : SuzukiModel X 2 f) : ∃ a : ℕ, 1 ≤ a ∧ Nonempty (X ≃* CFSG.Open.Sz a) := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  refine ⟨a, ha, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha (hf ▸ hK)))⟩⟩

theorem borelOf_le_normalizer_of_suzuki (hSzA : SzTwoAutInnerFact) {Kp T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (Kp : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ Kp) Kp) (hOT : pCoreOf 2 Kp ≤ T)
    (hZ : Subgroup.center (O2Q Kp) = ⊥) {k : ℕ} (hk : SuzukiModel (O2Q Kp) 2 k) :
    borelOf Kp T ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro b hb
  obtain ⟨hbK, hbN⟩ := hb
  apply mem_normalizer_of_forall_conj_mem'
  intro t ht
  set α := quotConjAut Kp ⟨t, hTN ht⟩ with hαdef
  obtain ⟨m, hm⟩ := hT2 ⟨t, ht⟩
  have hαm : α ^ 2 ^ m = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨t, hTN ht⟩ : ↥(Subgroup.normalizer (Kp : Set G))) ^ 2 ^ m = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hm)
    rw [this, map_one]
  obtain ⟨q, hq⟩ := hSzA _ k hk α ⟨m, hαm⟩
  have hq2 : q ^ 2 ^ m = 1 := by
    have h1 : MulAut.conj (q ^ 2 ^ m) = 1 := by rw [map_pow, ← hq, hαm]
    have h2 : q ^ 2 ^ m ∈ Subgroup.center (O2Q Kp) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun β : MulAut (O2Q Kp) => β z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  set S0 : Sylow 2 ↥Kp :=
    (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).toSylow hsyl.2.2 with hS0
  set Sb : Sylow 2 (O2Q Kp) := S0.mapSurjective (QuotientGroup.mk'_surjective _) with hSb
  have hmemS0 : ∀ s : ↥Kp, s ∈ (S0 : Subgroup ↥Kp) ↔ (s : G) ∈ T ⊓ Kp := fun s => by
    rw [hS0, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf]
  have hqN : q ∈ Subgroup.normalizer (Sb : Set (O2Q Kp)) := by
    apply mem_normalizer_of_forall_conj_mem'
    intro z hz
    rw [hSb, Sylow.coe_mapSurjective] at hz ⊢
    obtain ⟨s, hs, rfl⟩ := hz
    have e : q * QuotientGroup.mk' (CFSG.pCore 2 ↥Kp) s * q⁻¹ =
        α (QuotientGroup.mk s) := by
      rw [hq, MulAut.conj_apply]
      rfl
    rw [e, hαdef, quotConjAut_mk]
    have hts : t * s * t⁻¹ ∈ Kp := (Subgroup.mem_normalizer_iff.mp (hTN ht) s).mp s.2
    refine ⟨⟨t * s * t⁻¹, hts⟩, ?_, rfl⟩
    have hsTK := (hmemS0 s).mp hs
    exact (hmemS0 _).mpr ⟨T.mul_mem (T.mul_mem ht hsTK.1) (T.inv_mem ht), hts⟩
  have hqS : q ∈ (Sb : Subgroup (O2Q Kp)) := mem_of_pow_eq_one_of_mem_normalizer Sb hqN hq2
  rw [hSb, Sylow.coe_mapSurjective] at hqS
  obtain ⟨s₀, hs₀, hs₀q⟩ := hqS
  have hs₀TK := (hmemS0 s₀).mp hs₀
  set c : G := (s₀ : G)⁻¹ * t with hc
  have hcT : c ∈ T := T.mul_mem (T.inv_mem hs₀TK.1) ht
  have hc1 : quotConjAut Kp ⟨c, hTN hcT⟩ = 1 := by
    have e1 : (⟨c, hTN hcT⟩ : ↥(Subgroup.normalizer (Kp : Set G))) =
        (⟨s₀, Subgroup.le_normalizer s₀.2⟩)⁻¹ * ⟨t, hTN ht⟩ := Subtype.ext rfl
    have e2 : quotConjAut Kp ⟨s₀, Subgroup.le_normalizer s₀.2⟩ =
        MulAut.conj (QuotientGroup.mk s₀ : O2Q Kp) := by
      ext z
      induction z using QuotientGroup.induction_on with
      | H z =>
        rw [quotConjAut_mk, MulAut.conj_apply]
        rfl
    rw [e1, map_mul, map_inv, e2, ← hαdef, hq]
    have : (QuotientGroup.mk s₀ : O2Q Kp) = q := hs₀q
    rw [this, inv_mul_cancel]
  have hcomm := commutator_mem_of_quotConjAut_eq_one hc1 ⟨b, hbK⟩
  have e3 : b * t * b⁻¹ = (b * s₀ * b⁻¹) * ((c * b * c⁻¹ * b⁻¹)⁻¹ * c) := by
    rw [hc]
    group
  rw [e3]
  refine T.mul_mem ?_ (T.mul_mem (hOT (inv_mem hcomm)) hcT)
  exact ((Subgroup.mem_normalizer_iff.mp hbN _).mp hs₀TK).1

omit [Finite G] in
theorem centralizerModO2_le_normalizer (K : Subgroup G) :
    centralizerModO2 K ≤ Subgroup.normalizer (K : Set G) :=
  centralizerMod_le_left _ _ _

omit [Finite G] in
theorem normalizer_le_normalizer_centralizerModO2 (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (centralizerModO2 K : Set G) :=
  le_normalizer_centralizerMod (normalizer_le_normalizer_pCoreOf 2 _) Subgroup.le_normalizer le_rfl

omit [Finite G] in
theorem subnormal_centralizerModO2' (K : Subgroup G) :
    IsSubnormal (centralizerModO2 K) (Subgroup.normalizer (K : Set G)) :=
  A3.subnormal_of_normal (centralizerModO2_le_normalizer K)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (centralizerModO2_le_normalizer K)).mpr
      (normalizer_le_normalizer_centralizerModO2 K))

omit [Finite G] in
theorem subnormal_normalizer (K : Subgroup G) :
    IsSubnormal K (Subgroup.normalizer (K : Set G)) :=
  A3.subnormal_of_normal Subgroup.le_normalizer
    ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)

omit [Finite G] in
theorem pCoreOf_le_centralizerModO2 (K : Subgroup G) : pCoreOf 2 K ≤ centralizerModO2 K := by
  intro x hx
  have hxK : x ∈ K := pCoreOf_le 2 _ hx
  refine ⟨Subgroup.le_normalizer hxK, le_normalizer_pCoreOf 2 _ hxK, fun u hu => ?_⟩
  have hu' : u * x⁻¹ * u⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hu) _).mp (inv_mem hx)
  have := (pCoreOf 2 K).mul_mem hx hu'
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_cComp_normalizer_of_mem_cComp {K Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 K)) : Kp ∈ cComp (Subgroup.normalizer (K : Set G)) :=
  cComp_mem_of_subnormal (subnormal_centralizerModO2' _) hKp

end General

section Setting

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem isUniqueM (h5114 : Stmt5_1_14_first) :
    IsUniqueM H (Subgroup.normalizer (oTwoUpper H : Set G)) :=
  (h5114 G T M L V H B D n h.hyp h.notation59 h.module h.l34).1.2.1

theorem isMaxTwoLocal (h5114 : Stmt5_1_14_first) :
    quasithinIsMaxTwoLocal (Subgroup.normalizer (oTwoUpper H : Set G)) :=
  (h.isUniqueM h5114).1.1

theorem T_le_Mp : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  h.hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)

theorem pCoreOf_Mp_ne_bot (h5114 : Stmt5_1_14_first) :
    pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≠ ⊥ :=
  pCoreOf_ne_bot_of_isTwoLocal (h.isMaxTwoLocal h5114).1

theorem charTwo_Mp (h5114 : Stmt5_1_14_first) :
    CharTwo (Subgroup.normalizer (oTwoUpper H : Set G)) := by
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.hyp.sylow
  have hT : (S : Subgroup G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [hS]; exact h.T_le_Mp
  exact charTwo_of_le h.hyp.qtke.2.1 S hT le_rfl ⟨hT, h.pCoreOf_Mp_ne_bot h5114⟩

theorem pRank_Mp_le_two (h5114 : Stmt5_1_14_first) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ 2 :=
  pRank_le_two_of_isTwoLocal h.hyp.qtke hp hp2 (h.isMaxTwoLocal h5114).1

theorem isSimple_K
    : IsSimpleGroup (O2Q (oTwoUpper H)) :=
  CFSG.Timmesfeld.isSimpleGroup_of_lieModel h.l34

theorem center_K
    (hE9 : L34ElemNineFact) : Subgroup.center (O2Q (oTwoUpper H)) = ⊥ := by
  have := h.isSimple_K
  obtain ⟨E, hE, -, -⟩ := hE9 _ h.l34
  exact center_eq_bot_of_isSimpleGroup_of_card_nine hE

theorem not_three_dvd
    (h5114 : Stmt5_1_14_first) (hE9 : L34ElemNineFact) :
    ¬ 3 ∣ Nat.card (centralizerModO2 (oTwoUpper H)) :=
  not_three_dvd_card_centralizerModO2 hE9 h.l34
    (h.pRank_Mp_le_two h5114 Nat.prime_three (by norm_num))

theorem K_ne_bot
    : oTwoUpper H ≠ ⊥ := by
  intro hK
  have := h.isSimple_K
  have hnt : Nontrivial (O2Q (oTwoUpper H)) := IsSimpleGroup.toNontrivial
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have hall : ∀ x : ↥(oTwoUpper H), x = 1 := fun x => Subtype.ext (by
        have h1 : (x : G) ∈ (⊥ : Subgroup G) := by rw [← hK]; exact x.2
        exact Subgroup.mem_bot.mp h1)
      rw [hall a, hall b]

theorem pCoreOf_K_ne_bot
    (h5114 : Stmt5_1_14_first) : pCoreOf 2 (oTwoUpper H) ≠ ⊥ :=
  pCoreOf_ne_bot_of_subnormal (subnormal_normalizer _) (h.charTwo_Mp h5114) h.K_ne_bot

theorem pCoreOf_centralizerModO2_ne_bot
    (h5114 : Stmt5_1_14_first) :
    pCoreOf 2 (centralizerModO2 (oTwoUpper H)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  apply h.pCoreOf_K_ne_bot h5114
  have hle : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 (centralizerModO2 (oTwoUpper H)) :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_centralizerModO2 _)
      (centralizerMod_le_normalizer _ _ _) (pCoreOf_isPGroup 2 _)
  rw [hbot] at hle
  exact le_bot_iff.mp hle

end Hyp5_1_14

end Setting

section Components

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem not_three_dvd_cComp
    (h5114 : Stmt5_1_14_first) (hE9 : L34ElemNineFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) : ¬ 3 ∣ Nat.card Kp := fun h3 =>
  h.not_three_dvd h5114 hE9 (h3.trans (Subgroup.card_dvd_of_le (le_of_mem_cComp hKp)))

theorem suzuki_cComp
    (h5114 : Stmt5_1_14_first) (hE9 : L34ElemNineFact) (h36 : A36ForSQTK)
    (hSz : SimpleThreePrimeSuzukiFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    IsSimpleGroup (O2Q Kp) ∧ ∃ k : ℕ, SuzukiModel (O2Q Kp) 2 k :=
  isSimpleGroup_and_suzukiModel_of_cComp h.hyp.qtke h.hyp.simple h.hyp.nonabelian h36 hSz
    (h.pCoreOf_Mp_ne_bot h5114) (mem_cComp_normalizer_of_mem_cComp hKp)
    (h.not_three_dvd_cComp h5114 hE9 hKp)

theorem pCoreOf_cComp_ne_bot (h5114 : Stmt5_1_14_first) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) : pCoreOf 2 Kp ≠ ⊥ :=
  pCoreOf_ne_bot_of_subnormal (subnormal_of_mem_cComp (mem_cComp_normalizer_of_mem_cComp hKp))
    (h.charTwo_Mp h5114)
    (ne_bot_of_mem_cComp hKp)

theorem cComp_unique
    (h5114 : Stmt5_1_14_first) (hE9 : L34ElemNineFact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (hSz : SimpleThreePrimeSuzukiFact) {Kp Kp' : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H)))
    (hKp' : Kp' ∈ cComp (centralizerModO2 (oTwoUpper H))) : Kp = Kp' := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K := oTwoUpper H with hKdef
  set Mp := Subgroup.normalizer (K : Set G) with hMpdef
  have hO := h.pCoreOf_Mp_ne_bot h5114
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot h.hyp.qtke h.hyp.simple h.hyp.nonabelian hO
  have hA37 := h37 _ hQ
  have hKpM := mem_cComp_normalizer_of_mem_cComp hKp
  have hKpM' := mem_cComp_normalizer_of_mem_cComp hKp'
  have hAc := modO2Image_mem_cComp hKpM
  have hAc' := modO2Image_mem_cComp hKpM'
  set A := modO2Image Mp Kp with hAdef
  set A' := modO2Image Mp Kp' with hA'def
  have hAA' : A ≠ A' := fun e => hne (modO2Image_injOn Mp hKpM hKpM' e)
  have hcomm1 : ⁅A, A'⁆ = ⊥ := hA37 A hAc A' hAc' hAA'
  obtain ⟨hs1, k1, hk1⟩ := h.suzuki_cComp h5114 hE9 h36 hSz hKp
  obtain ⟨hs2, k2, hk2⟩ := h.suzuki_cComp h5114 hE9 h36 hSz hKp'
  obtain ⟨e1⟩ := modO2_mulEquiv hKpM
  obtain ⟨e2⟩ := modO2_mulEquiv hKpM'
  have hA5 : 5 ∣ Nat.card A ∧ ¬ (Nat.card A).Prime := by
    rw [← Nat.card_congr e1.toEquiv]; exact five_dvd_card_of_suzukiModel hk1
  have hA5' : 5 ∣ Nat.card A' ∧ ¬ (Nat.card A').Prime := by
    rw [← Nat.card_congr e2.toEquiv]; exact five_dvd_card_of_suzukiModel hk2
  have hsA : IsSimpleGroup ↥A := e1.symm.isSimpleGroup
  have hsA' : IsSimpleGroup ↥A' := e2.symm.isSimpleGroup
  have hZA : Subgroup.center ↥A = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_prime hA5.2
  have hZA' : Subgroup.center ↥A' = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_prime hA5'.2
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hA5.1
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 5 hA5'.1
  have hK5 : 5 ∣ Nat.card (O2Q K) := by
    rw [card_of_lieModel_L34 h.l34]; norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 hK5
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hKMp : K ≤ Mp := Subgroup.le_normalizer
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Mp) with hπ
  set c := π (Subgroup.inclusion hKMp k₀) with hcdef
  have hOKM : pCoreOf 2 K ≤ pCoreOf 2 Mp := A4.pCoreOf_le_of_subnormal 2 (subnormal_normalizer _)
  have hmemO : ∀ x : ↥Mp, (x : G) ∈ pCoreOf 2 Mp → π x = 1 := by
    intro x hx
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := Subtype.ext hzx
    rw [← this]
    exact hz
  have hc5 : c ^ 5 = 1 := by
    rw [hcdef, ← map_pow, ← map_pow]
    apply hmemO
    apply hOKM
    have h1 : (QuotientGroup.mk (k₀ ^ 5) : O2Q K) = 1 := by
      rw [QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, by simp⟩
  have hc1 : c ≠ 1 := by
    intro hc
    rw [hcdef, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    have hk₀ : (k₀ : G) ∈ pCoreOf 2 Mp := ⟨_, hc, rfl⟩
    have hk₀K : (k₀ : G) ∈ pCoreOf 2 K := by
      refine le_pCoreOf_of_le_normalizer 2 (inf_le_left : K ⊓ pCoreOf 2 Mp ≤ K) ?_
        ((pCoreOf_isPGroup 2 Mp).to_le inf_le_right) ⟨k₀.2, hk₀⟩
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) x
      have h2 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mp (hKMp hk)) x
      simp only [Subgroup.mem_inf]
      exact and_congr h1 h2
    have : (QuotientGroup.mk k₀ : O2Q K) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      obtain ⟨z, hz, hzx⟩ := hk₀K
      have : z = k₀ := Subtype.ext hzx
      rw [← this]
      exact hz
    rw [this, orderOf_one] at hy
    norm_num at hy
  have hcord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hcomm_c : ∀ {X : Subgroup G}, X ≤ centralizerModO2 K → ∀ x ∈ modO2Image Mp X,
      x * c = c * x := by
    intro X hX x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    replace hx₀ : (x₀ : G) ∈ X := Subgroup.mem_subgroupOf.mp hx₀
    rw [hcdef, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hmem := commutator_mem_of_mem_centralizerModO2 (hX hx₀) k₀.2
    have hn : ((x₀ : G) * k₀)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
      le_normalizer_pCoreOf 2 Mp (Mp.inv_mem (Mp.mul_mem x₀.2 (hKMp k₀.2)))
    have hmem' := (Subgroup.mem_normalizer_iff.mp hn _).mp (hOKM (inv_mem hmem))
    obtain ⟨z, hz, hzx⟩ := hmem'
    have hz' : (x₀ * Subgroup.inclusion hKMp k₀)⁻¹ * (Subgroup.inclusion hKMp k₀ * x₀) = z := by
      apply Subtype.ext
      rw [show (z : G) = _ from hzx]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      group
    rw [hz']
    exact hz
  have hcA : ∀ x ∈ A, x * c = c * x :=
    hcomm_c (le_of_mem_cComp hKp)
  have hcA' : ∀ x ∈ A', x * c = c * x :=
    hcomm_c (le_of_mem_cComp hKp')
  have hAA'c : ∀ x ∈ A, ∀ x' ∈ A', x * x' = x' * x := by
    intro x hx x' hx'
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm1 hx
    exact (Subgroup.mem_centralizer_iff.mp this x' hx').symm
  have haA : (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ∈ A := a.2
  have hbA' : (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ∈ A' := b.2
  have hza : ∀ u ∈ Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp), u ∈ A := fun u hu => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact A.zpow_mem haA i
  have hzb : ∀ u ∈ Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp), u ∈ A' := fun u hu => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact A'.zpow_mem hbA' i
  have hzc : ∀ u ∈ Subgroup.zpowers c, ∀ x ∈ A, x * u = u * x := fun u hu x hx => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_right (hcA x hx) i).eq
  have hzc' : ∀ u ∈ Subgroup.zpowers c, ∀ x ∈ A', x * u = u * x := fun u hu x hx => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_right (hcA' x hx) i).eq
  have hbc : ∀ (v : ↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp))) (w : ↥(Subgroup.zpowers c)),
      Commute ((Subgroup.zpowers _).subtype v) ((Subgroup.zpowers c).subtype w) := fun v w =>
    show Commute (v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) (w : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) from
      hzc' w w.2 v (hzb v v.2)
  set g := MonoidHom.noncommCoprod (Subgroup.zpowers _).subtype (Subgroup.zpowers c).subtype hbc
    with hg
  have hag : ∀ (u : ↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)))
      (vw : ↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c)),
      Commute ((Subgroup.zpowers _).subtype u) (g vw) := by
    rintro u ⟨v, w⟩
    rw [hg, MonoidHom.noncommCoprod_apply]
    simp only [Subgroup.coe_subtype]
    have h1 : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * v = v * u := hAA'c _ (hza u u.2) _ (hzb v v.2)
    have h2 : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * w = w * u := hzc w w.2 _ (hza u u.2)
    exact ((Commute.mul_right h1 h2))
  set f := MonoidHom.noncommCoprod (Subgroup.zpowers _).subtype g hag with hf
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, ⟨v, w⟩⟩ hfu
    rw [hf, MonoidHom.noncommCoprod_apply, hg, MonoidHom.noncommCoprod_apply] at hfu
    simp only [Subgroup.coe_subtype] at hfu
    have huA := hza u u.2
    have hvA' := hzb v v.2
    have hu1 : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = 1 := by
      have hu : (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = ((v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * w)⁻¹ :=
        eq_inv_of_mul_eq_one_left hfu
      have hcen : (⟨u, huA⟩ : ↥A) ∈ Subgroup.center ↥A := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hu]
        have h1 := hAA'c _ x.2 _ hvA'
        have h2 := hzc w w.2 _ x.2
        have h3 : Commute (x : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) (v * w) := by
          show (x : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * (v * w) = (v * w) * x
          rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
        exact (Commute.inv_right h3).eq
      rw [hZA, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    rw [hu1, one_mul] at hfu
    have hv1 : (v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = 1 := by
      have hv : (v : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) = (w : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)⁻¹ :=
        eq_inv_of_mul_eq_one_left hfu
      have hcen : (⟨v, hvA'⟩ : ↥A') ∈ Subgroup.center ↥A' := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hv]
        have h2 : Commute (x : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) w := hzc' w w.2 _ x.2
        exact (Commute.inv_right h2).eq
      rw [hZA', Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    rw [hv1, one_mul] at hfu
    exact Prod.ext (Subtype.ext hu1) (Prod.ext (Subtype.ext hv1) (Subtype.ext hfu))
  have hpow5 : ∀ (z : ↥Mp ⧸ CFSG.pCore 2 ↥Mp), z ^ 5 = 1 →
      ∀ u : ↥(Subgroup.zpowers z), u ^ 5 = 1 := by
    intro z hz u
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    apply Subtype.ext
    show (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ^ 5 = 1
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show z ^ ((5 : ℕ) : ℤ) = 1 by
      exact_mod_cast hz, one_zpow]
  have ha5 : (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← ha, pow_orderOf_eq_one, Subgroup.coe_one]
  have hb5 : (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← hb, pow_orderOf_eq_one, Subgroup.coe_one]
  have hcommz : ∀ (z : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) (u v : ↥(Subgroup.zpowers z)), u * v = v * u := by
    intro z u v
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    apply Subtype.ext
    show (u : ↥Mp ⧸ CFSG.pCore 2 ↥Mp) * v = v * u
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hEcomm : ∀ x y : ↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) ×
      (↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c)),
      x * y = y * x := by
    rintro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩
    exact Prod.ext (hcommz _ x1 y1) (Prod.ext (hcommz _ x2 y2) (hcommz _ x3 y3))
  have hEpow : ∀ x : ↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) ×
      (↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c)), x ^ 5 = 1 := by
    rintro ⟨x1, x2, x3⟩
    exact Prod.ext (by rw [Prod.pow_fst]; exact hpow5 _ ha5 x1)
      (Prod.ext (by rw [Prod.pow_snd, Prod.pow_fst]; exact hpow5 _ hb5 x2)
        (by rw [Prod.pow_snd, Prod.pow_snd]; exact hpow5 _ hc5 x3))
  have hEcard : Nat.card (↥(Subgroup.zpowers (a : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) ×
      (↥(Subgroup.zpowers (b : ↥Mp ⧸ CFSG.pCore 2 ↥Mp)) × ↥(Subgroup.zpowers c))) = 5 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers,
      hcord, Subgroup.orderOf_coe, ha, Subgroup.orderOf_coe, hb]
    norm_num
  have h125 : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (↥Mp ⧸ CFSG.pCore 2 ↥Mp)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hEcomm hEpow hEcard f hf_inj le_top
  have hQcard : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥Mp) := by
    intro h5
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Mp)).exists_card_eq
    rw [hm] at h5
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : (5 : ℕ).Prime) h5) (by norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq _ hQcard] at h125
  have h5' : CFSG.Open.pRank 5 (⊤ : Subgroup ↥Mp) ≤ CFSG.Open.pRank 5 Mp := by
    have := CFSG.SectionRank.pRank_le_map (p := 5) (by norm_num) Mp.subtype
      Mp.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have := h125.trans (h5'.trans (h.pRank_Mp_le_two h5114 (by norm_num) (by norm_num)))
  omega

theorem perfectCore_eq
    (h5114 : Stmt5_1_14_first) (hE9 : L34ElemNineFact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    perfectCore (centralizerModO2 (oTwoUpper H)) = Kp := by
  rw [← lemma_1_2_1_one h.hyp.qtke h.hyp.simple h.hyp.nonabelian h39
    (h.pCoreOf_centralizerModO2_ne_bot h5114)]
  refine le_antisymm (sSup_le fun K' hK' => ?_) (le_cCompSpan hKp)
  rw [← h.cComp_unique h5114 hE9 h36 h37 hSz hKp hK']

theorem normalizer_cComp_eq
    (h5114 : Stmt5_1_14_first) (hE9 : L34ElemNineFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact)
    {Kp : Subgroup G} (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) :
    Subgroup.normalizer (Kp : Set G) = Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC := h.perfectCore_eq h5114 hE9 h36 h37 h39 hSz hKp
  have hMpN : Subgroup.normalizer (oTwoUpper H : Set G) ≤ Subgroup.normalizer (Kp : Set G) := by
    rw [← hPC]
    exact (normalizer_le_normalizer_centralizerModO2 _).trans
      (normalizer_le_normalizer_perfectCore _)
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Kp : Set G)) :=
    ⟨pCoreOf 2 Kp, h.pCoreOf_cComp_ne_bot h5114 hKp, pCoreOf_isPGroup 2 Kp, rfl⟩
  have hle : Subgroup.normalizer (Kp : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Kp : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Kp
  have heq := (h.isMaxTwoLocal h5114).2 _ hloc (hMpN.trans hle)
  exact le_antisymm (heq ▸ hle) hMpN

theorem not_le_M
    (h5114 : Stmt5_1_14_first) (h331 : Stmt3_3_1) (hE9 : L34ElemNineFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hSz : SimpleThreePrimeSuzukiFact)
    (hL2 : L2PerfectThreePrimeFact) {Kp : Subgroup G}
    (hKp : Kp ∈ cComp (centralizerModO2 (oTwoUpper H))) : ¬ Kp ≤ M := by
  intro hKpM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  have hKpN : Kp ≤ Subgroup.normalizer (L : Set G) := hKpM.trans hh.normal
  set φ := (quotConjAut L).comp (Subgroup.inclusion hKpN) with hφ
  have hperf : commutator ↥Kp = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKp))
  have hφ1 : φ = 1 := hL2 _ n hh.lie ↥Kp φ hperf (h.not_three_dvd_cComp h5114 hE9 hKp)
  have hcomm : ∀ k ∈ Kp, ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro k hk l hl
    have h1 : quotConjAut L ⟨k, hKpN hk⟩ = 1 := by
      have := congrArg (fun ψ : ↥Kp →* MulAut (O2Q L) => ψ ⟨k, hk⟩) hφ1
      simp only [hφ, MonoidHom.comp_apply, MonoidHom.one_apply] at this
      exact this
    exact commutator_mem_of_quotConjAut_eq_one h1 ⟨l, hl⟩
  set Q := pCoreOf 2 L with hQdef
  set Y := Kp ⊔ Q with hYdef
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    apply mem_normalizer_of_forall_conj_mem'
    intro y hy
    have hle : Y ≤ Y.comap (MulAut.conj l).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun q hq => ?_)
      · show l * k * l⁻¹ ∈ Y
        have e : l * k * l⁻¹ = (k * l * k⁻¹ * l⁻¹)⁻¹ * k := by group
        rw [e]
        exact Y.mul_mem (Subgroup.mem_sup_right (inv_mem (hcomm k hk l hl)))
          (Subgroup.mem_sup_left hk)
      · show l * q * l⁻¹ ∈ Y
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pCoreOf 2 L hl) q).mp hq)
    exact hle hy
  have hNKp := h.normalizer_cComp_eq h5114 hE9 h36 h37 h39 hSz hKp
  have hLT : IsSylowTwoOf T (L ⊔ T) := hh.isSylowTwoOf le_sup_right
  have hLsub : IsSubnormal L (L ⊔ T) :=
    A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hh.sup_le_normalizer)
  have hQT : Q ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 hLsub).trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hLT)
  have hYN : Y ≤ Subgroup.normalizer (Kp : Set G) :=
    sup_le Subgroup.le_normalizer (hQT.trans (hNKp ▸ h.T_le_Mp))
  have hKpn : (Kp.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hYN
  have hQs : Group.IsSolvable ↥Q := by
    have := (pCoreOf_isPGroup 2 L).isNilpotent
    infer_instance
  have hPY : perfectCore Y = Kp :=
    le_antisymm (perfectCore_le_of_sup_solvable le_sup_left hKpn rfl hQs)
      (le_perfectCore_of_perfect le_sup_left (perfect_of_mem_cComp hKp))
  have hLN : L ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [← hNKp, ← hPY]
    exact hLY.trans (normalizer_le_normalizer_perfectCore Y)
  have hU := hh.isUniqueM h331
  have heq := hU.2 _ ⟨h.isMaxTwoLocal h5114, sup_le hLN h.T_le_Mp⟩
  exact h.hyp.hStar.2.1 (heq ▸ le_normalizer_oTwoUpper H)

end Hyp5_1_14

end Components

end CFSG.Quasithin.H13
