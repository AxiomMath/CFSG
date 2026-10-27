module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8213D
public import CFSG.Quasithin.Vol2.Ch8Sec2L8213E
public import CFSG.Quasithin.Vol2.Ch8Sec2Step13
public import CFSG.Quasithin.Background.HM22Out
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212F
public import CFSG.Quasithin.Vol2.Ch8Sec2L8213B
public import CFSG.Quasithin.Vol2.Ch8Sec2L8213C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8213F

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_eq_map_pCore_82 (C : Subgroup G) :
    pCoreOf 2 C = (CFSG.pCore 2 ↥C).map C.subtype := CFSG.openPCoreOf_eq_map_pCore 2 C

theorem card_inf_eq_82 {T L V : Subgroup G} [IsMulCommutative ↥V]
    (hVT : V ≤ T) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCLV : L ⊓ Subgroup.centralizer (V : Set G) = V) (hVc : Nat.card ↥V = 2 ^ 11)
    (hLc : Nat.card ↥(autOn L V) = 244823040)
    (hSc : Nat.card ↥(autOn (T ⊓ L) V) = 2 ^ (Nat.card ↥(autOn L V)).factorization 2) :
    Nat.card ↥(T ⊓ L) = 2 ^ 21 := by
  have hVL : V ≤ L := hCLV ▸ inf_le_left
  have hVC : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have h1 := card_autOn_mul_82 (V := V) (X := T ⊓ L) (inf_le_right.trans hLV)
  have h2 : T ⊓ L ⊓ Subgroup.centralizer (V : Set G) = V := by
    apply le_antisymm
    · intro x hx
      rw [← hCLV]
      exact ⟨hx.1.2, hx.2⟩
    · intro x hx
      exact ⟨⟨hVT hx, hVL hx⟩, hVC hx⟩
  have h3 : (Nat.card ↥(autOn L V)).factorization 2 = 10 := by
    rw [hLc, show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  rw [h2, hVc, hSc, h3] at h1
  rw [← h1]
  norm_num

theorem le_and_isAutTripleM22_82
    (hT12 : KG82HatM22Twelve) (hOut : KG82HatM22Out) {T L : Subgroup G} {z : G}
    (hEven : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hTLc : Nat.card ↥(T ⊓ L) = 2 ^ 21)
    (hz : orderOf z = 2) (hzT : z ∈ Subgroup.centralizer (T : Set G))
    (hJ4 : J4.IsTypeJ4Core ↥(Subgroup.centralizer ({z} : Set G)) (J4.selfC z))
    (K : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hCK : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hKq : CFSG.Open.IsQuasisimple ↥(ch8Kstar K z))
    (hKZ : Nat.card ↥(Subgroup.center ↥(ch8Kstar K z)) = 3)
    (hKM : IsSporadic .M22 (↥(ch8Kstar K z) ⧸ Subgroup.center ↥(ch8Kstar K z))) :
    T ≤ L ∧ J4.IsAutTripleM22 (↥(Subgroup.centralizer ({z} : Set G)) ⧸
      CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set P := CFSG.pCore 2 ↥C with hPdef
  obtain ⟨-, hext, hPc, hPZ, -⟩ := hJ4
  obtain ⟨hPp, hcommP, hfrat, -⟩ := hext
  set zC : ↥C := J4.selfC z with hzCdef
  have hz2 : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    norm_num at hz
  have hzCc : zC ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hzC1 : zC ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzC2 : zC ^ 2 = 1 := Subtype.ext hz2
  have hZP : ∀ x : ↥P, (x : ↥C) ∈ Subgroup.zpowers zC ↔ x ∈ Subgroup.center ↥P := by
    intro x
    rw [← hPZ]
    constructor
    · rintro ⟨c, hc, hcx⟩
      have hcx' : c = x := Subtype.ext hcx
      rw [← hcx']
      exact hc
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hzE : zC ∈ P := by
    have h1 : zC ∈ (Subgroup.center ↥P).map P.subtype := by
      rw [hPZ]
      exact Subgroup.mem_zpowers zC
    exact Subgroup.map_subtype_le _ h1
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Subgroup.zpowers zC := by
    intro x hx y hy
    have h1 : ⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆ ∈ Subgroup.center ↥P := by
      rw [← hcommP, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact (hZP _).mpr h1
  have hsq : ∀ x ∈ P, x ^ 2 ∈ Subgroup.zpowers zC := by
    intro x hx
    have : Fact (IsPGroup 2 ↥P) := ⟨hPp⟩
    have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x, hx⟩ : ↥P)
    rw [hfrat] at h1
    exact (hZP _).mpr h1
  have hA18 : ∀ c : ↥C, (∀ e ∈ P, ⁅c, e⁆ ∈ Subgroup.zpowers zC) → c ∈ P := by
    intro c hc
    have hchar := charTwo_centralizer_82 hEven hT hz hzT
    have hzCm : ∀ g ∈ C, g * z = z * g := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mp hg
    have h1 : (c : G) ∈ pCoreOf 2 C := by
      refine mem_pCoreOf_of_commutator_82 hz2 hzCm hchar c.2 fun q hq => ?_
      rw [pCoreOf_eq_map_pCore_82] at hq
      obtain ⟨e, he, rfl⟩ := hq
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc e he)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h2 := congrArg Subtype.val hk
      rw [Subgroup.coe_zpow] at h2
      exact h2
    rw [pCoreOf_eq_map_pCore_82] at h1
    obtain ⟨c', hc', hcc'⟩ := h1
    have hcc : c' = c := Subtype.ext hcc'
    rw [← hcc]
    exact hc'
  have hKn : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr hCK
  have : (ch8Kstar K z).Normal := hKn.map (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have : ((Subgroup.zpowers zC).subgroupOf P).Normal := normal_zpowers_subgroupOf_82 hzCc
  have hcen := centralizer_eq_center_82 hT12 hzCc hzC1 hzC2 hzE hcomm hsq hPc hA18 (ch8Kstar K z)
    hKq hKZ hKM
  have hX2 := card_le_two_mul_82 (ch8Kstar K z) hKq hKZ hKM hcen
  have hKc := card_of_hatM22_82 hKZ hKM
  have hTC : T ≤ C := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT t ht)
  have hSc : Nat.card ↥(T.subgroupOf C) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
  have hSp : IsPGroup 2 ↥(T.subgroupOf C) := hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have hTge : 2 ^ 21 ≤ Nat.card ↥T := by
    rw [← hTLc]
    exact Subgroup.card_le_of_le inf_le_left
  obtain ⟨hS21, hXeq⟩ := card_two_part_82 P hPc (ch8Kstar K z) hKc hX2 (T.subgroupOf C) hSp
    (by rw [hSc]; exact hTge)
  have hTL : T ⊓ L = T := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [hTLc, ← hSc, hS21]
  exact ⟨inf_eq_left.mp hTL, isAutTripleM22_82 hOut (ch8Kstar K z) hKq hKZ hKM hcen hXeq⟩

theorem stmt8_2_13_of
    (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12) (h8293 : Stmt8_2_9_three)
    (h8210 : Stmt8_2_10) (h8212 : Stmt8_2_12) (hins : Step8_2_13_insp)
    (hm24 : SchurMult2M24) : Stmt8_2_13 := by
  have hcovL : KG82CoverL34 := kg82CoverL34_holds
  have hcovM : KG82CoverM22 := kg82CoverM22_holds
  have hsimp : HSimple82 := hSimple82_holds
  have hcent : HCent82 := hCent82_holds
  have htype : HType82 := hType82_holds
  have hpar : HParab82 := hParab82_holds
  have hT12 : KG82HatM22Twelve := CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Twelve_holds
  have hOut : KG82HatM22Out := CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Out_holds
  intro G _ _ T L I hyp h731 h821 hc hrow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hTL, hLN, hTV, hVT, hVL, hCLV, hTCL, hL0, -, -⟩ :=
    setup_82 h3228 h3109 h37 h38 h39 h711n h822 h825 h828 h829 hsimp hcent htype hpar hcovL
      hcovM hm24 hyp h731 h821 hrow
  obtain ⟨-, hVQ, z₀, hz₀, hz₀V⟩ := h8210 G T L I hyp h731 h821 hc hrow
  have hnot24 : ¬ Row711M24Code T L I := h8293 G T L I hyp h731 h821 hc hrow
  set V := fsuV T I with hVdef
  have hEven := hyp.fsu.qtke.2.1
  have hT := hyp.fsu.sylow
  have hSc := card_autOn_inf_of_sylow (isSylowIn_top_of_fsu hyp.fsu) hTL hTV
  have key : ∀ z : G, orderOf z = 2 →
      V ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      Row711M24Cocode T L I ∧ T ≤ L ∧
        J4.IsAutTripleM22 (↥(Subgroup.centralizer ({z} : Set G)) ⧸
          CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set G))) := by
    intro z hz hzV
    obtain ⟨hco, K, hKC, hCK, -, -, hKq, hKZ, hKM⟩ :=
      hins G T L I hyp h731 h821 hc hrow hnot24 z hz hzV
    obtain ⟨-, ⟨-, -, h24⟩, -, -, -⟩ := h8212 G T L I hyp h731 h821 hc hrow z hz hzV
    obtain ⟨-, hJ4⟩ := h24 hco
    have hM : MathieuCocode24 (V := ↥V) (autOn L V) ⊤ ⊥ := by
      rw [← hL0]
      exact hco
    have hzT : z ∈ Subgroup.centralizer (T : Set G) := by
      have h1 : z ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
        rw [hzV]
        exact Subgroup.mem_zpowers z
      exact h1.2
    have hTLc := card_inf_eq_82 hVT hLN hCLV (card_V_of_cocode24_82 hM) (card_of_cocode24_82 hM)
      hSc
    obtain ⟨hTL', hX⟩ := le_and_isAutTripleM22_82 hT12 hOut hEven hT hTLc hz hzT hJ4 K hKC hCK
      hKq hKZ hKM
    exact ⟨hco, hTL', hX⟩
  obtain ⟨hco, hTL', -⟩ := key z₀ hz₀ hz₀V
  have hM : MathieuCocode24 (V := ↥V) (autOn L V) ⊤ ⊥ := by
    rw [← hL0]
    exact hco
  have hT1 : T ≠ ⊥ := by
    have hz₀V' : z₀ ∈ V := by
      have h1 : z₀ ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
        rw [hz₀V]
        exact Subgroup.mem_zpowers z₀
      exact h1.1
    intro hbot
    have h1 := hVT hz₀V'
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hz₀
    norm_num at hz₀
  have hNV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVQ]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hML : Subgroup.normalizer (L : Set G) = L :=
    normalizer_eq_of_82 hEven hT hT1 hV hTL' hLN hCLV hTCL hNV (normalizer_of_cocode24_82 hM)
  refine ⟨⟨hco, hVL, hLN, hCLV, card_V_of_cocode24_82 hM, nativeCocode24_of_82 hM⟩, ?_,
    fun z hz hzV => (key z hz hzV).2.2⟩
  show L = Subgroup.normalizer (fsuL0 T L : Set G)
  rw [hL0, hML]

end L8213F

end CFSG.Quasithin.H13
