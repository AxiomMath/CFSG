module

public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
public import CFSG.HardMathSupport.Dickson.BMRows.M13Rows
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.RankThree.PartOne.SPOR.OuterM
import CFSG.LocalAnalysis.StandardType.GGSporKBMBridgeZ
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
import CFSG.LocalAnalysis.StandardType.GGSporKF1F4Conj
import CFSG.LocalAnalysis.StandardType.GGSporKM13Gmat
import CFSG.HardMathSupport.Dickson.BMRows.M13Shape
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Primitive
import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMNo65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMNo65Monster
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.CentralizerCFive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass
public import Certificates.Certificate17632Base
import CFSG.Assembly.OpenBridges

public section


namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Dickson.BMRows CFSG.HardMathSupport.Dickson.BMRows.M13L33
  CFSG.HardMathSupport.Dickson.I271 CFSG.Yardstones.Md0ec50421ce4

private theorem gkw_component_of_l33
    {G : Type} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 13) {Q : Subgroup G} (hQC : Q ≤ Subgroup.centralizer ({x} : Set G))
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))
    (hC : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) ≤ 451 * 936)
    (hI : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 936) :
    ∃ J : Subgroup G, CFSG.Open.GLAPComponent 13 (Subgroup.centralizer ({x} : Set G)) J := by
  haveI hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI hsQ : IsSimpleGroup ↥Q := isSimple_of_equiv_sl e
  have hnab : ∃ a b : ↥Q, a * b ≠ b * a := noncomm_of_equiv_sl e
  have hQcard : Nat.card ↥Q = 5616 := card_of_equiv_sl e
  have hxcard : Nat.card ↥(Subgroup.zpowers x) = 13 := by rw [Nat.card_zpowers, hx]
  have hZ : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) → z = 1 := M13Normal.eq_one_of_central hnab
  have hconj : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ l ∈ Q, g * l * g⁻¹ ∈ Q :=
    M13Normal.conj_mem_of_small_index hnab hQC (by omega) (by rw [hxcard, hQcard]; omega)
  obtain ⟨u, hu2, hu1, hu48⟩ := exists_involution_cent_ge e
  have hcm := M13Normal.card_mul_cent_le hQC hZ u
  have hu2' : (u : G) * u = 1 := by simpa using congrArg Subtype.val hu2
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hux : (u : G) * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 (hQC u.2)
  have h936 := hI u hu2' hu1' hux
  have hxZ : x ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
      Subgroup.mem_centralizer_iff.2 fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)⟩
  have hle : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G)) *
      48 ≤ 936 :=
    calc _ ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G)) *
          Nat.card ↥(Subgroup.centralizer ({u} : Set ↥Q)) := Nat.mul_le_mul_left _ hu48
      _ ≤ Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G) ⊓
          Subgroup.centralizer ({x} : Set G)) := hcm
      _ ≤ 936 := h936
  have hcent : IsPGroup 13 ↥(Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer (Q : Set G)) :=
    M13Normal.isPGroup_of_card_lt hxZ hx (m := 48) (N := 936) (by norm_num) hle (by norm_num)
  have hpQ : 13 ∣ Nat.card ↥Q := by rw [hQcard]; norm_num
  have hZ' : Subgroup.center ↥Q = ⊥ := M13Normal.center_eq_bot_of_simple_nonab hnab
  have hLq : CFSG.Open.IsQuasisimple ↥Q :=
    ⟨M13Normal.commutator_eq_top_of_simple_nonab hnab,
      ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).isSimpleGroup⟩
  exact ⟨Q, glaPComponent_of_normal_quasisimple hQC hconj hLq
    (glaPPrimeCore_eq_bot_of_normal_quasisimple hp.out hQC hconj hLq hpQ hcent)⟩

private theorem gkw_component_conj_xE
    (φ : Gmat ≃* MGriess) {s m : Gmat} {k : ℕ}
    (hk : k % 13 ≠ 0) (h : m * s * m⁻¹ = gw thirteenX ^ k) :
    ∃ J : Subgroup Gmat, CFSG.Open.GLAPComponent 13 (Subgroup.centralizer ({s} : Set Gmat)) J := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hk1 : gw thirteenX ^ k ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_xE] at this
    exact hk (Nat.mod_eq_zero_of_dvd this)
  obtain ⟨Q, hQC, ⟨e⟩⟩ := exists_l33_xE
  obtain ⟨J, hJ⟩ := gkw_component_of_l33 orderOf_xE hQC e (card_centralizer_xE_le φ)
    fun u hu2 hu1 hux => card_cent_inf_xE_le φ hu2 hu1 hux
  have h1 : CFSG.Open.GLAPComponent 13
      (Subgroup.centralizer ({gw thirteenX ^ k} : Set Gmat)) J := by
    rwa [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime orderOf_xE
      hk1]
  have h2 := glaPComponent_map_equiv (by norm_num : Nat.Prime 13) (MulAut.conj m⁻¹) h1
  have hs : (MulAut.conj m⁻¹) (gw thirteenX ^ k) = s := by
    rw [← h]
    simp [MulAut.conj_apply, mul_assoc]
  rw [map_centralizer_singleton, hs] at h2
  exact ⟨_, h2⟩

theorem ggSporK_bmPCentralF1F4_gmat_thirteen
    : BMPCentralF1 13 Gmat ∧ BMPCentralF4 13 Gmat := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨⟨φ, -⟩⟩ := exists_M_equivs
  have key : ∀ s : Gmat, orderOf s = 13 →
      (∀ C : Subgroup Gmat, ¬ LargeEvenPComponent 13 (Subgroup.centralizer ({s} : Set Gmat)) C) →
      BMPCentralF1At 13 s ∧ BMPCentralF4At 13 s := by
    intro s hs hno
    obtain ⟨m, k, hk, h | h⟩ := census_thirteen s hs
    · exact bmPCentralF1At_F4At_of_conj_pow (by norm_num) orderOf_c13 hk h
        gmat_bmPCentralF1At_F4At_c13
    · obtain ⟨J, hJ⟩ := gkw_component_conj_xE φ hk h
      exact (hno J
        ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 13 _ J).2 hJ)).elim
  exact ⟨fun s hs hno => (key s hs hno).1, fun s hs hno => (key s hs hno).2⟩

theorem ggSporK_bmPCentralF1F4_M_thirteen_of_simple
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMPCentralF1 13 (TauCeti.CFSGIndex.sporadic .M).Group ∧
      BMPCentralF4 13 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  haveI := hS
  let e' : (TauCeti.CFSGIndex.sporadic .M).Group ≃* CFSG.Blueprint.NativeSporadic.Carrier .M :=
    e.symm.trans (MulEquiv.refl _)
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := (TauCeti.CFSGIndex.sporadic .M).Group) e'
  haveI : Finite CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.2
  exact ⟨bmPCentralF1_of_mulEquiv 13 f.symm ggSporK_bmPCentralF1F4_gmat_thirteen.1,
    bmPCentralF4_of_mulEquiv 13 f.symm ggSporK_bmPCentralF1F4_gmat_thirteen.2⟩

theorem ggSporK_bmCentreZ_M_thirteen_of_simple
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMCentreZ 13 (TauCeti.CFSGIndex.sporadic .M).Group :=
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  bmCentreZ_of_F1_F4 13 _ (ggSporK_bmPCentralF1F4_M_thirteen_of_simple hS).1
    (ggSporK_bmPCentralF1F4_M_thirteen_of_simple hS).2

end CFSG.StandardType.SporadicShape
