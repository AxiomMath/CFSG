module

public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
public import CFSG.LocalAnalysis.StandardType.GGSporKM7Gmat
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM7
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.RankThree.PartOne.SPOR.OuterM
import CFSG.LocalAnalysis.StandardType.GGSporKBMBridgeZ
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
import CFSG.LocalAnalysis.StandardType.GGSporKF1F4Conj
import CFSG.LocalAnalysis.StandardType.GGSporKCompConj
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Primitive
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenRec
import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.A6Leaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.PartOne.KS.HeSevenCheck
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import Certificates.Certificate16005
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
import CFSG.Assembly.OpenBridges

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabMSeven
  _root_.Timmesfeld.Mon7

private theorem m7w_component_of_simple {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {k : G} (hk : orderOf k = p) {H : Subgroup G}
    (hHk : H ≤ Subgroup.centralizer ({k} : Set G)) (hs : IsSimpleGroup ↥H)
    (hnab : ∃ a b : ↥H, a * b ≠ b * a) (hpH : p ∣ Nat.card ↥H)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ p * Nat.card ↥H) :
    ∃ J : Subgroup G, CFSG.Open.GLAPComponent p (Subgroup.centralizer ({k} : Set G)) J := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hs
  set X : Subgroup G := Subgroup.centralizer ({k} : Set G) with hX
  have hkX : k ∈ X := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hZ : Subgroup.center ↥H = ⊥ := center_eq_bot_of_simple_nonab hnab
  have hKH : ∀ g ∈ Subgroup.zpowers k, g ∈ H → g = 1 := fun _ hg hgH =>
    eq_one_of_mem_zpowers_of_center hHk hZ hg hgH
  have hdec : ∀ x ∈ X, ∃ (i : ℕ) (h : G), h ∈ H ∧ x = k ^ i * h :=
    eq_prod_of_card_le' hk hKH hkX hHk hbound
  have hcomm : ∀ (i : ℕ) (y : G), y ∈ H → k ^ i * y * (k ^ i)⁻¹ = y := by
    intro i y hy
    have hyk : Commute y k := Subgroup.mem_centralizer_singleton_iff.1 (hHk hy)
    have h1 : y * k ^ i = k ^ i * y := (hyk.pow_right i).eq
    rw [← h1]
    simp
  have hLn : ∀ g ∈ X, ∀ l ∈ H, g * l * g⁻¹ ∈ H := by
    intro g hg l hl
    obtain ⟨i, h, hh, rfl⟩ := hdec g hg
    have hmem : h * l * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hl) (H.inv_mem hh)
    have e1 : k ^ i * h * l * (k ^ i * h)⁻¹ = k ^ i * (h * l * h⁻¹) * (k ^ i)⁻¹ := by
      group
    rw [e1, hcomm i _ hmem]
    exact hmem
  have hcentle : X ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.zpowers k := by
    rintro c ⟨hcX, hcH⟩
    obtain ⟨i, h, hh, rfl⟩ := hdec c hcX
    have hh1 : h = 1 := by
      have hcomm' : ∀ y ∈ H, y * h = h * y := by
        intro y hy
        have h1 := Subgroup.mem_centralizer_iff.1 hcH y hy
        have hyk : Commute y k := Subgroup.mem_centralizer_singleton_iff.1 (hHk hy)
        have h2 : y * k ^ i = k ^ i * y := (hyk.pow_right i).eq
        have h3 : k ^ i * (y * h) = k ^ i * (h * y) := by
          calc k ^ i * (y * h) = (k ^ i * y) * h := by rw [mul_assoc]
            _ = (y * k ^ i) * h := by rw [h2]
            _ = y * (k ^ i * h) := by rw [mul_assoc]
            _ = (k ^ i * h) * y := h1
            _ = k ^ i * (h * y) := by rw [mul_assoc]
        exact mul_left_cancel h3
      have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.center ↥H :=
        Subgroup.mem_center_iff.2 fun b => Subtype.ext (hcomm' b b.2)
      rw [hZ, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    rw [hh1, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _
  have hKp : IsPGroup p ↥(Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk, pow_one])
  have hcent : IsPGroup p ↥(X ⊓ Subgroup.centralizer (H : Set G)) := hKp.to_le hcentle
  have hLq : CFSG.Open.IsQuasisimple ↥H := tabMFive_quasisimple_of_simple_nonab hnab
  exact ⟨H, glaPComponent_of_normal_quasisimple hHk hLn hLq
    (glaPPrimeCore_eq_bot_of_normal_quasisimple hp hHk hLn hLq hpH hcent)⟩

private theorem m7w_component_dG :
    ∃ J : Subgroup Gmat, LargeEvenPComponent 7 (Subgroup.centralizer ({dG} : Set Gmat)) J := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨hcls, h2A, h2B, hG5⟩ := gmat_seven_bounds
  obtain ⟨hHk, ⟨e⟩⟩ := tabMSeven_he_le_cent_dG
  set H : Subgroup Gmat := Subgroup.closure ({heAG, heBG} : Set Gmat) with hH
  have hE8 : HePE8 := hePE8
  have hbound : Nat.card ↥(Subgroup.centralizer ({dG} : Set Gmat)) ≤ 7 * 4030387200 :=
    centSevenA_of_bounds hE8 hcls h2A h2B hG5 orderOf_dG hHk e
  have hcard : Nat.card ↥H = 4030387200 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HeldB.card_heP
  have hZ : Subgroup.center ↥H = ⊥ := center_eq_bot_of_equiv_heP e
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have htop : Subgroup.center ↥H = ⊤ :=
      eq_top_iff.2 fun z _ => Subgroup.mem_center_iff.2 fun g => hc g z
    have h1 : Nat.card ↥H = 1 := by
      rw [← Subgroup.card_top (G := ↥H), ← htop, hZ, Subgroup.card_bot]
    rw [hcard] at h1
    norm_num at h1
  haveI : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP := CFSG.Sporadic.HeldB.heP_simple
  have hs : IsSimpleGroup ↥H := MulEquiv.isSimpleGroup e
  obtain ⟨J, hJ⟩ := m7w_component_of_simple Nat.prime_seven orderOf_dG hHk hs hnab
    (by rw [hcard]; norm_num) (by rw [hcard]; exact hbound)
  exact ⟨J, (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 7 _ J).2 hJ⟩

private theorem m7w_q5_isConj :
    IsConj (gq 5) zG := by
  have h0 := orb_conj (k := 0) (by norm_num)
  have e : gw (Wrho orbWord[0]!) = gq 5 := by
    have : orbWord[0]! = [5] := by decide +kernel
    rw [this, gw_Wrho]
    simp [gq]
  have hk : orbKind[0]! = true := by decide +kernel
  rw [e, hk] at h0
  simpa using h0

theorem ggSporK_bmPCentralF1F4_gmat_seven :
    BMPCentralF1 7 Gmat ∧ BMPCentralF4 7 Gmat := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have hzo : orderOf (gq 5) = 7 := gq_commData.orderOf_z
  have key : ∀ s : Gmat, orderOf s = 7 →
      (∀ C : Subgroup Gmat,
        ¬ LargeEvenPComponent 7 (Subgroup.centralizer ({s} : Set Gmat)) C) →
      BMPCentralF1At 7 s ∧ BMPCentralF4At 7 s := by
    intro s hs hno
    rcases monsterSevenClasses s hs with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      have hc' : c * s * c⁻¹ = dG ^ 1 := by simpa using hc
      obtain ⟨J, hJ⟩ := bmPComponent_of_conj_pow Nat.prime_seven orderOf_dG
        (by norm_num) hc' m7w_component_dG
      exact (hno J hJ).elim
    · obtain ⟨c, hc⟩ := isConj_iff.1 (h.trans m7w_q5_isConj.symm)
      have hc' : c * s * c⁻¹ = gq 5 ^ 1 := by simpa using hc
      have hno' : ∀ C : Subgroup Gmat,
          ¬ LargeEvenPComponent 7 (Subgroup.centralizer ({gq 5} : Set Gmat)) C := by
        intro C hC
        obtain ⟨C', hC'⟩ :=
          bmPComponent_of_conj_pow Nat.prime_seven hzo (by norm_num) hc' ⟨C, hC⟩
        exact hno C' hC'
      exact bmPCentralF1At_F4At_of_conj_pow Nat.prime_seven hzo (by norm_num) hc'
        (gmat_bmPCentralF1At_F4At_q5 hno')
  exact ⟨fun s hs hno => (key s hs hno).1, fun s hs hno => (key s hs hno).2⟩

theorem ggSporK_bmPCentralF1F4_M_seven_of_simple
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMPCentralF1 7 (TauCeti.CFSGIndex.sporadic .M).Group ∧
      BMPCentralF4 7 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  haveI := hS
  let e' : (TauCeti.CFSGIndex.sporadic .M).Group ≃* CFSG.Blueprint.NativeSporadic.Carrier .M :=
    e.symm.trans (MulEquiv.refl _)
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := (TauCeti.CFSGIndex.sporadic .M).Group) e'
  haveI : Finite CFSG.Monster.Generated.Gmat := CFSG.Monster.Generated.finite_Gmat
  exact ⟨bmPCentralF1_of_mulEquiv 7 f.symm ggSporK_bmPCentralF1F4_gmat_seven.1,
    bmPCentralF4_of_mulEquiv 7 f.symm ggSporK_bmPCentralF1F4_gmat_seven.2⟩

theorem ggSporK_bmCentreZ_M_seven_of_simple
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMCentreZ 7 (TauCeti.CFSGIndex.sporadic .M).Group :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  bmCentreZ_of_F1_F4 7 _ (ggSporK_bmPCentralF1F4_M_seven_of_simple hS).1
    (ggSporK_bmPCentralF1F4_M_seven_of_simple hS).2

end CFSG.StandardType.SporadicShape
