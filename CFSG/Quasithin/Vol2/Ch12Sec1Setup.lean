module

public import CFSG.Quasithin.Vol2.Ch12Sec1Orth
public import CFSG.Quasithin.Vol2.Ch12Sec1Cent
public import CFSG.Quasithin.Vol2.Ch12Sec1Conj
public import CFSG.Quasithin.Vol2.Ch12Sec1Aut
public import CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch7Rows325
public import CFSG.Quasithin.Background.HL42Aut
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.H13.VolIAutSLFive
public import CFSG.LieType.BorelTits.Basic
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate43
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3084
public import Certificates.Certificate3086
public import Certificates.Certificate3119
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3172
public import Certificates.Certificate7022
public import Certificates.Certificate8010
public import Certificates.Certificate8011
public import Certificates.Certificate8012
public import Certificates.Certificate8013
public import Certificates.Certificate8014
public import Certificates.Certificate8015
public import Certificates.Certificate8016
public import Certificates.Certificate8017
public import Certificates.Certificate8018
public import Certificates.Certificate8019
public import Certificates.Certificate8020
public import Certificates.Certificate8022
public import Certificates.Certificate8024
public import Certificates.Certificate8025
public import Certificates.Certificate8026
public import Certificates.Certificate8027
public import Certificates.Certificate8028
public import Certificates.Certificate8029
public import Certificates.Certificate8030
public import Certificates.Certificate8031
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate7067
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.Fischer.Pairs
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped IsMulCommutative

namespace Sec121

variable {G : Type} [Group G] [Finite G]

theorem setup_of_linear
    {T L V₀ : Subgroup G} (hfsu : FSU G T L V₀) (hL : L = conjClosure L T)
    (hC : V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) {t : G} (ht : t ∈ T)
    (htN : t ∉ Subgroup.normalizer (V₀ : Set G))
    (hVM : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) = conjClosure V₀ T)
    (hVsum : conjClosure V₀ T = V₀ ⊔ CFSG.conjugate V₀ t)
    (hVinf : V₀ ⊓ CFSG.conjugate V₀ t = ⊥)
    (hniso : ¬ IsXSectionIso₂ L V₀ ⊥ (CFSG.conjugate V₀ t) ⊥)
    [IsMulCommutative ↥(conjClosure V₀ T)] (hVel : IsElemAbelian 2 (conjClosure V₀ T))
    (hN : conjClosure L T ⊔ T ≤ Subgroup.normalizer (conjClosure V₀ T : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : ↥(autOn L (conjClosure V₀ T)) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    [IsMulCommutative ↥V₀] (hnat₀ : BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n 1)
    (hAut : Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ≤
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
      IsPrimeReduced 2 ((conjClosure V₀ T).subgroupOf (Subgroup.normalizer (L : Set G))) ∧
      Nonempty (↥(autOn (Subgroup.normalizer (L : Set G)) (conjClosure V₀ T)) ≃*
        MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
      L ≤ Subgroup.normalizer (CFSG.conjugate V₀ t : Set G) ∧
      (∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n 1) ∧
      ∃ _ : IsMulCommutative ↥(CFSG.conjugate V₀ t),
        BinaryNaturalSL (V := ↥(CFSG.conjugate V₀ t)) (autOn L (CFSG.conjugate V₀ t)) ⊤ ⊥ n 1 := by
  set V := conjClosure V₀ T with hVdef
  set W := CFSG.conjugate V₀ t with hWdef
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ M := by
    have h := le_normalizer_conjClosure L T
    rwa [← hL] at h
  have htL : t ∈ M := hTL ht
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := by
    have h := (le_sup_left : conjClosure L T ≤ conjClosure L T ⊔ T).trans hN
    rwa [← hL] at h
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hN
  have hL₀ : L ≤ Subgroup.normalizer (V₀ : Set G) := by
    have h := hfsu.irrPlus.2.2.1
    rwa [← hL] at h
  have hV₀V : V₀ ≤ V := hVsum ▸ le_sup_left
  have hWV : W ≤ V := hVsum ▸ le_sup_right
  have hV₀ne : V₀ ≠ ⊥ := hfsu.irrPlus.2.1
  have hirr₀ : ∀ J : Subgroup G, J ≤ V₀ → L ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = V₀ := by
    intro J hJ hLJ
    have h := hfsu.irrPlus.2.2.2.2.2.1 J (by rw [← hL, hC]; exact bot_le) hJ
      (by rw [← hL]; exact hLJ)
    rwa [← hL, hC] at h
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjugate htL hL₀
  have : IsMulCommutative ↥W := isMulCommutative_conjugate V₀ t
  have hnatW : BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ n 1 :=
    binaryNaturalSL_conjugate htL hL₀ hnat₀
  have hirrW := irr_conjugate htL hirr₀
  have hWne : W ≠ ⊥ := by
    intro h
    apply hV₀ne
    rw [eq_bot_iff]
    intro v hv
    have h1 : t⁻¹ * v * t ∈ W := mem_conjugate_iff.mpr (by
      rw [show t * (t⁻¹ * v * t) * t⁻¹ = v by group]
      exact hv)
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    calc v = t * (t⁻¹ * v * t) * t⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hcent : ∀ c : MulAut ↥V, (∀ y ∈ autOn L V, c * y = y * c) → c = 1 := fun c hc =>
    eq_one_of_commute_autOn (n := n) (by omega) hV₀V hWV hVsum.symm hVinf hLV hL₀ hLW hV₀ne
      hWne hirr₀ hirrW hnat₀ hnatW hniso hc
  have h3228 := stmt3_2_2_eight_proved G T L V₀ hfsu
  rw [← hL] at h3228
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
    have hE : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      (sup_le Subgroup.le_normalizer hTL).trans
        (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Subgroup.map_subtype_le _).trans le_sup_left) hE
        (LieType.BorelTits.pCoreOf_isPGroup 2 L)
    rw [h3228.2.2] at hle
    exact hle.trans inf_le_right
  obtain ⟨eQ⟩ := nonempty_quot_mulEquiv_sl_of_autOn hLV hO2 hfsu.quasisimple (K := ZMod 2)
    (by omega) e
  have hVLT : V ≤ L ⊔ T := h3228.1
  have hVMle : V ≤ M := hVLT.trans (sup_le Subgroup.le_normalizer hTL)
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := by
    have h := le_normalizer_conjClosure V M
    rwa [hVM] at h
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two (by omega)
  have hsimp : IsSimpleGroup ↥(autOn L V) := e.isSimpleGroup
  have h3 : 3 ∣ Nat.card (autOn L V) := by
    rw [Nat.card_congr e.toEquiv]
    rcases hn with rfl | rfl
    · rw [card_SL_four_two]
      norm_num
    · rw [CFSG.Quasithin.Vol2.Ch11.SecA.card_SL_five_two]
      norm_num
  have hred : IsTwoReducedIn M V :=
    isTwoReducedIn_of_cent hVMle hMV hVel Subgroup.le_normalizer le_rfl hsimp h3 hcent
  have hne : autOn L V ≠ autOn M V := by
    intro h
    have htM : conjAct V ⟨t, hTV ht⟩ ∈ autOn M V :=
      Setup.mem_autOn_iff.mpr ⟨⟨t, hTV ht⟩, htL, rfl⟩
    rw [← h] at htM
    obtain ⟨g, hgL, hg⟩ := Setup.mem_autOn_iff.mp htM
    have hgt : ∀ v ∈ V, t * v * t⁻¹ = (g : G) * v * (g : G)⁻¹ := fun v hv => by
      have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hg
      simp only [Setup.coe_conjAct_apply] at this
      exact this.symm
    have hgt' : ∀ v ∈ V, t⁻¹ * v * t = (g : G)⁻¹ * v * g := fun v hv => by
      have hg' : conjAct V g⁻¹ = conjAct V ⟨t, hTV ht⟩⁻¹ := by rw [map_inv, map_inv, hg]
      have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hg'
      simp only [Setup.coe_conjAct_apply, Subgroup.coe_inv, inv_inv] at this
      exact this.symm
    apply htN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hgt x (hV₀V hx)]
      exact (Subgroup.mem_normalizer_iff.mp (hL₀ hgL) x).mp hx
    · intro hx
      have h1 := hgt' _ (hV₀V hx)
      rw [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at h1
      rw [h1]
      have h2 := (Subgroup.mem_normalizer_iff.mp (hL₀ (L.inv_mem hgL)) _).mp hx
      rwa [inv_inv] at h2
  obtain ⟨eM⟩ := nonempty_autOn_mulEquiv_mulAut Subgroup.le_normalizer le_rfl hcent hne eQ e hAut
  exact ⟨⟨eQ⟩, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hred).2, ⟨eM⟩, hLW,
    ⟨inferInstance, hnat₀⟩, ⟨inferInstance, hnatW⟩⟩

end Sec121

open Sec121

theorem stmt12_1_setup_of
    (h323 : Stmt3_2_3) (h325 : Stmt3_2_5) (h701 : Stmt7_0_1) :
    ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
      L = conjClosure L T → V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G) →
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) = conjClosure V₀ T →
        conjClosure V₀ T = V₀ ⊔ CFSG.conjugate V₀ t → V₀ ⊓ CFSG.conjugate V₀ t = ⊥ →
        ¬ IsXSectionIso₂ L V₀ ⊥ (CFSG.conjugate V₀ t) ⊥ →
          Nonempty (G ≃* NativeSporadic.J4) ∨
          ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
            Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
            IsPrimeReduced 2 ((conjClosure V₀ T).subgroupOf (Subgroup.normalizer (L : Set G))) ∧
            Nonempty (↥(autOn (Subgroup.normalizer (L : Set G)) (conjClosure V₀ T)) ≃*
              MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
            L ≤ Subgroup.normalizer (CFSG.conjugate V₀ t : Set G) ∧
            (∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n 1) ∧
            ∃ _ : IsMulCommutative ↥(CFSG.conjugate V₀ t),
              BinaryNaturalSL (V := ↥(CFSG.conjugate V₀ t)) (autOn L (CFSG.conjugate V₀ t)) ⊤ ⊥ n 1 := by
  intro G _ _ T L V₀ hfsu hL hC t ht htN hVM hVsum hVinf hniso
  have hL0 : fsuL0 T L = L := hL.symm
  have htV₀ : ¬ T ≤ Subgroup.normalizer (V₀ : Set G) := fun h => htN (h ht)
  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hL
  have hnot : ¬ V₀ = conjClosure V₀ T := fun h1 => htV₀ (by
    have h := le_normalizer_conjClosure V₀ T
    rwa [← h1] at h)
  have h3 := (hcases.resolve_left fun h => hnot h.1).resolve_left fun h => hnot h.1
  obtain ⟨hab, hVel, hN, h7⟩ := h701 G T L V₀ hfsu
  rcases h7 with hFF | hJ4 | ⟨a, ha, hO⟩ | hFour
  ·
    have hNM : Subgroup.normalizer (fsuV T V₀ : Set G) ≤ fsuM T L := by
      obtain ⟨⟨-, -⟩, ⟨-, huniq⟩, -⟩ := h323 G T L hfsu.simple hfsu.nonabelian hfsu.qtke
        hfsu.sylow hfsu.maximal hfsu.faithful hfsu.quasisimple
      have hVne : fsuV T V₀ ≠ ⊥ := fun h => hfsu.irrPlus.2.1 (le_bot_iff.mp
        (h ▸ le_conjClosure V₀ T))
      have hV2 : IsPGroup 2 ↥(fsuV T V₀) := fun x => ⟨1, Subtype.ext (by
        simpa using hVel.2 x x.2)⟩
      obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
        (⟨fsuV T V₀, hVne, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (fsuV T V₀ : Set G)))
      have hM'eq := huniq M' hM' (hN.trans hle)
      rw [hM'eq] at hle
      exact hle
    rcases not_concl701FF_or_325 hfsu hL hVel hN hNM h3 with hnot | ⟨-, hlin⟩
    · exact absurd hFF hnot
    · right
      rcases hlin with ⟨⟨e⟩, hab₀, hnat₀⟩ | ⟨⟨e⟩, hab₀, hnat₀⟩
      · exact ⟨4, Or.inl rfl, setup_of_linear hfsu hL hC ht htN hVM hVsum hVinf hniso hVel hN
          (Or.inl rfl) e hnat₀ CFSG.Quasithin.H.L4.card_mulAut_SL_four⟩
      · exact ⟨5, Or.inr rfl, setup_of_linear hfsu hL hC ht htN hVM hVsum hVinf hniso hVel hN
          (Or.inr rfl) e hnat₀ VolI.autSLFiveTwo_holds⟩
  ·
    exact Or.inl hJ4.2.2.2.2.2
  ·
    exfalso
    rw [hL0] at hO
    refine not_binaryOrthogonalFour ha hO ?_
    rcases h3.2.1 with ⟨n, K, hK, hf, hc, he, -⟩ | ⟨n, K, hK, hf, hc, he, -⟩ | ⟨he, -⟩ |
      ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl ⟨n, K, hK, hf, hc, he⟩
    · exact Or.inr (Or.inl ⟨n, K, hK, hf, hc, he⟩)
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he))))
  ·
    have h1 := hFour.1
    rw [hL0] at h1
    exact (lt_irrefl L h1).elim

end CFSG.Quasithin.H13
