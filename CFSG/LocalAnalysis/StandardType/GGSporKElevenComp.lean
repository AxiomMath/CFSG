module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportB
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.StandardType.GGSporKPSubquot
public import CFSG.HardMathSupport.Dickson.BMRows.M11Holds
public import CFSG.HardMathSupport.Dickson.BMRows.M11Shape
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement
open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen11
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
  CFSG.HardMathSupport.Dickson.BMRows.M11

private def gke_P (p : ℕ) {K : Type} [Group K] (X C : Subgroup K) : Prop :=
  LargeEvenPComponent p X C ∧
    ¬ StandardType.LargeEvenMarking ↥((C.subgroupOf X).map
      (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X))) (fun _ _ _ _ _ _ => True)

private theorem gke_at_x11
    (h : CentElevenBound) :
    ∃ C : Subgroup Gmat, gke_P 11 (Subgroup.centralizer {gw gen11W0}) C := by
  have := isSimpleGroup_m12K
  have hnab := m12K_noncomm
  have hp : Nat.Prime 11 := by norm_num
  have hpK : 11 ∣ Nat.card m12K := by rw [card_m12K]; norm_num
  have hZ : Subgroup.center m12K = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnab
  have hLq : CFSG.Open.IsQuasisimple m12K := by
    refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator m12K) with h' | h'
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h']
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h'
  have hcoreK : CFSG.Open.GLAPPrimeCore 11 m12K = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_simple hp hpK
  have hcoreX := CFSG.HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_normal_quasisimple hp
    m12K_le_centralizer (conj_mem_m12K_of_bound h) hLq hpK (isPGroup_inf_centralizer_m12K h)
  have hC : LargeEvenPComponent 11 (Subgroup.centralizer {gw gen11W0}) m12K :=
    (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 11 _ _).2
      (CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal_quasisimple
        m12K_le_centralizer (conj_mem_m12K_of_bound h) hLq hcoreX)
  refine ⟨m12K, hC, fun hmark => ?_⟩
  obtain ⟨ψ⟩ := bmPSubquot_centerQuot_equiv_pSimple hp hC
  have hcard : Nat.card (BMPSubquot 11 (gw gen11W0) m12K ⧸
      Subgroup.center (BMPSubquot 11 (gw gen11W0) m12K)) = 95040 := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_congr
      (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf m12K hcoreK hZ).toEquiv, card_m12K]
  exact largeEvenMarking_not_card_of_mem_bmCompOrders (by simp [bmCompOrders]) hcard hmark

private theorem gke_map_at {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (e : K ≃* K') (y : K)
    (h : ∃ C : Subgroup K, gke_P 11 (Subgroup.centralizer {y}) C) :
    ∃ C' : Subgroup K', gke_P 11 (Subgroup.centralizer {e y}) C' := by
  obtain ⟨C, hC, hnot⟩ := h
  refine ⟨C.map e.toMonoidHom, ?_, ?_⟩
  · have h1 := (largeEvenPComponent_map_mulEquiv 11 e (Subgroup.centralizer {y}) C).mpr hC
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e y] at h1
  · intro hmark'
    obtain ⟨iso⟩ := bmPSubquot_mulEquiv 11 e (x := y) (x' := e y) rfl
      (C := C) (C' := C.map e.toMonoidHom) rfl
    exact hnot (largeEvenMarking_true_of_mulEquiv iso.symm hmark')

private theorem gke_conj_pow
    {k : Gmat} (hk : orderOf k = 11) :
    ∃ g : Gmat, ∃ j : ℕ, k = g * gw gen11W0 ^ j * g⁻¹ ∧ gw gen11W0 ^ j ≠ 1 :=
  exists_conj_pow_x11 hk

private theorem gke_bound
    : CentElevenBound := centElevenBound_holds

private theorem gke_cen
    {j : ℕ} (hj1 : gw gen11W0 ^ j ≠ 1) :
    Subgroup.centralizer ({gw gen11W0 ^ j} : Set Gmat) =
      Subgroup.centralizer ({gw gen11W0} : Set Gmat) := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact centralizer_pow_eq_of_prime orderOf_x11 hj1

private theorem gke_main
    [Finite Gmat] (k : Gmat) (hk : orderOf k = 11) :
    ∃ C : Subgroup Gmat, gke_P 11 (Subgroup.centralizer {k}) C := by
  obtain ⟨g, j, hgj, hj1⟩ := gke_conj_pow hk
  have h0 := gke_at_x11 gke_bound
  have h1 : ∃ C : Subgroup Gmat, gke_P 11 (Subgroup.centralizer {gw gen11W0 ^ j}) C := by
    rw [gke_cen hj1]; exact h0
  have h2 := gke_map_at (MulAut.conj g) _ h1
  rw [MulAut.conj_apply, ← hgj] at h2
  exact h2

theorem ggSporK_bmElevenComp_gmat
    : BMElevenComp CFSG.Monster.Generated.Gmat :=
  fun k hk => gke_main k hk

theorem ggSporK_bmElevenComp_M_of_simple [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMElevenComp (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  haveI := hS
  let e' : (TauCeti.CFSGIndex.sporadic .M).Group ≃* CFSG.Blueprint.NativeSporadic.Carrier .M :=
    e.symm.trans (MulEquiv.refl _)
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := (TauCeti.CFSGIndex.sporadic .M).Group) e'
  haveI : Finite CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.2
  exact bmElevenComp_of_mulEquiv f.symm ggSporK_bmElevenComp_gmat

end CFSG.StandardType.SporadicShape
