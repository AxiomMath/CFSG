module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
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
public import Certificates.Certificate1005
public import Certificates.Certificate3009
public import Certificates.Certificate3039
public import Certificates.Certificate3147
public import Certificates.Certificate3152
public import Certificates.Certificate8124
public import Certificates.Certificate9107
public import Certificates.Certificate9108
public import Certificates.Certificate9109
public import Certificates.Certificate9110
public import Certificates.Certificate9205
public import Certificates.Certificate13506
public import Certificates.Certificate13507
public import Certificates.Certificate1023301
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
import CFSG.LocalAnalysis.StandardType.GGSporKRestTransport
import CFSG.Monster.B.Fischer.Fi22OmegaMax
import CFSG.Sporadic.Bridge.Fi22Surj
import CFSG.Timmesfeld.Final.Simple
public import CFSG.Certificates.CosetTableOrders
public import CFSG.Certificates.CosetTableShort
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.RankThree.Native.Fi22FiveCheckInputs
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Fi22Exact
public import CFSG.Sporadic.Presentation.Fi22ExactCover
public import CFSG.Sporadic.Presentation.Fi22ExactTop
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.SuborbitCoatom

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Certificates.SetOrbit CFSG.EvenSmallLie.OmegaEight
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Group

variable {G : Type*} [Group G] [Finite G]

private theorem ggSporKRestFi22_normal_of_index {D M : Subgroup G} (hDM : D ≤ M)
    (hD : IsSimpleGroup ↥D) {k : ℕ} (hidx : (D.subgroupOf M).index = k)
    (hcard : k.factorial < Nat.card M) : (D.subgroupOf M).Normal := by
  set D' := D.subgroupOf M with hD'
  haveI := hD
  haveI : IsSimpleGroup ↥D' := (Subgroup.subgroupOfEquivOfLe hDM).isSimpleGroup
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index D'
  rw [hidx] at hdvd
  set N := D'.normalCore
  have hNle : N ≤ D' := Subgroup.normalCore_le D'
  have hN : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot] at hdvd
    exact absurd (Nat.le_of_dvd (Nat.factorial_pos k) hdvd) (by omega)
  have hNn : (N.subgroupOf D').Normal := (Subgroup.normalCore_normal D').subgroupOf D'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf D') with h | h
  · exfalso
    apply hN
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hNle
  · rw [Subgroup.subgroupOf_eq_top] at h
    have : N = D' := le_antisymm hNle h
    rw [← this]
    exact Subgroup.normalCore_normal D'

private theorem ggSporKRestFi22_le_of_not_dvd_index {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] {D' P : Subgroup M} [D'.Normal] (hP : IsPGroup p P) (hcop : ¬ p ∣ D'.index) :
    P ≤ D' := by
  have h1 : IsPGroup p ↥(P.map (QuotientGroup.mk' D')) := hP.map _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h1
  have h2 : Nat.card ↥(P.map (QuotientGroup.mk' D')) ∣ D'.index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hn0 : n = 0 := by
    by_contra h
    exact hcop (dvd_trans (dvd_pow_self p h) (hn ▸ h2))
  rw [hn0, pow_zero] at hn
  have hbot : P.map (QuotientGroup.mk' D') = ⊥ := Subgroup.eq_bot_of_card_eq _ hn
  intro x hx
  have hmem : QuotientGroup.mk' D' x ∈ P.map (QuotientGroup.mk' D') := ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

private theorem ggSporKRestFi22_le_sup_normalizer {p : ℕ} [Fact p.Prime] {D M : Subgroup G}
    (S : Sylow p G) (hSD : (S : Subgroup G) ≤ D) (hDM : D ≤ M) (hDn : (D.subgroupOf M).Normal) :
    M ≤ D ⊔ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  intro m hm
  have hSM : (S : Subgroup G) ≤ M := hSD.trans hDM
  let P : Sylow p ↥M := S.subtype hSM
  have hPD : (P : Subgroup ↥M) ≤ D.subgroupOf M := by
    rw [Sylow.coe_subtype]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hSD (Subgroup.mem_subgroupOf.1 hx))
  haveI := hDn
  have hF := Sylow.normalizer_sup_eq_top' P hPD
  have hmem : (⟨m, hm⟩ : ↥M) ∈ Subgroup.normalizer ((P : Subgroup ↥M) : Set ↥M) ⊔
      D.subgroupOf M := hF ▸ Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem M.subtype hmem
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDM] at hmap
  refine (sup_le ?_ le_sup_left : _ ≤ D ⊔ _) hmap
  rintro _ ⟨n, hn, rfl⟩
  refine le_sup_right (a := D) ?_
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff] at hn
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have := (hn ⟨s, hSM hs⟩).1 (by rw [Sylow.coe_subtype]; exact Subgroup.mem_subgroupOf.2 hs)
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hs
    have hsM : s ∈ M := by
      have h := M.mul_mem (M.mul_mem (M.inv_mem n.2) (hSM hs)) n.2
      simpa [mul_assoc] using h
    have := (hn ⟨s, hsM⟩).2 (by
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
      simpa using hs)
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at this
    simpa using this

private theorem ggSporKRestFi22_component_eq {D M C : Subgroup G} (hDM : D ≤ M)
    (hD : IsSimpleGroup ↥D) (hDn : (D.subgroupOf M).Normal)
    (hsolv : Group.IsSolvable (↥M ⧸ D.subgroupOf M)) (hC : IsComponentOf C M) : C = D := by
  obtain ⟨hCM, hsub, hq⟩ := hC
  haveI := hDn
  have hCD : C ≤ D := by
    set C' := C.subgroupOf M
    have hperf : Group.IsPerfect ↥C' :=
      ⟨by
        have h := hq.1
        have e := (Subgroup.subgroupOfEquivOfLe hCM)
        have hp : Group.IsPerfect ↥C := ⟨h⟩
        exact (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).1⟩
    let f : ↥C' →* ↥M ⧸ D.subgroupOf M := (QuotientGroup.mk' (D.subgroupOf M)).comp C'.subtype
    haveI : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
    haveI : Group.IsSolvable ↥f.range := inferInstance
    have hsub1 : Subsingleton ↥f.range := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance
    intro c hc
    have hc' : (⟨⟨c, hCM hc⟩, Subgroup.mem_subgroupOf.2 hc⟩ : ↥C') ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨f ⟨⟨c, hCM hc⟩, Subgroup.mem_subgroupOf.2 hc⟩, ⟨_, rfl⟩⟩ : ↥f.range) = 1 :=
        Subsingleton.elim _ _
      exact congrArg Subtype.val this
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hc'
    exact Subgroup.mem_subgroupOf.1 hc'
  have hsubD : IsSubnormal C D := by
    have h := hsub.inf_of_le hDM
    rwa [inf_eq_left.2 hCD] at h
  rcases hsubD.eq_bot_or_eq_of_isSimpleGroup hD with h | h
  · exfalso
    subst h
    have hns := hq.2.toNontrivial
    obtain ⟨a, b, hab⟩ := hns.exists_pair_ne
    apply hab
    have : Subsingleton (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := inferInstance
    exact Subsingleton.elim a b
  · exact h

end Group

private theorem ggSporKRestFi22_map {K : Type} [Group K] (e : K ≃* K) {Q : Subgroup K}
    (h : ∀ Y : Subgroup K, Y ≠ ⊤ → (∃ S : Sylow 5 K, (S : Subgroup K) ≤ Y) →
      SporKRestControls Q Y → ∀ C : Subgroup K, IsComponentOf C Y →
        LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1)
    {Y' : Subgroup K} (hY' : Y' ≠ ⊤) (hS' : ∃ S : Sylow 5 K, (S : Subgroup K) ≤ Y')
    (hctl' : SporKRestControls (Q.map e.toMonoidHom) Y') {C' : Subgroup K}
    (hC' : IsComponentOf C' Y') : LieModel (↥C' ⧸ Subgroup.center ↥C') .POmegaPlus 4 2 1 := by
  have hinj : Function.Injective e.toMonoidHom := fun a b h => e.injective (by simpa using h)
  have hsurj : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, by simp⟩
  have hcomap : ∀ A : Subgroup K, A.comap e.toMonoidHom = A.map e.symm.toMonoidHom := by
    intro A
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    exact ⟨fun hx => ⟨e x, hx, by simp⟩, fun ⟨y, hy, hyx⟩ => by rw [← hyx]; simpa using hy⟩
  have hY : Y'.comap e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hY'
    have hmap : (Y'.comap e.toMonoidHom).map e.toMonoidHom = Y' :=
      Subgroup.map_comap_eq_self_of_surjective hsurj Y'
    rw [← hmap, htop, Subgroup.map_top_of_surjective e.toMonoidHom hsurj]
  have hS : ∃ S : Sylow 5 K, (S : Subgroup K) ≤ Y'.comap e.toMonoidHom := by
    obtain ⟨S', hS'Y⟩ := hS'
    have hrange : (S' : Subgroup K) ≤ e.toMonoidHom.range := by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact le_top
    refine ⟨S'.comapOfInjective e.toMonoidHom hinj hrange, ?_⟩
    rw [Sylow.coe_comapOfInjective]
    exact Subgroup.comap_mono hS'Y
  have hctl : SporKRestControls Q (Y'.comap e.toMonoidHom) := by
    intro x hx hx1 g hg
    show e g ∈ Y'
    refine hctl' (e x) ⟨x, hx, rfl⟩ (fun h1 => hx1 (e.injective (by simpa using h1))) (e g) ?_
    have hconj : e (g⁻¹ * x * g) = (e g)⁻¹ * e x * e g := by simp
    rw [← hconj]
    exact hg
  have hC : IsComponentOf (C'.comap e.toMonoidHom) (Y'.comap e.toMonoidHom) := by
    rw [hcomap, hcomap]
    exact isComponentOf_map_mulEquiv' e.symm hC'
  have hLie := h _ hY hS hctl _ hC
  let φ : ↥(C'.comap e.toMonoidHom) ≃* ↥C' :=
    (MulEquiv.subgroupMap e (C'.comap e.toMonoidHom)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective hsurj C'))
  exact LieModel.of_mulEquiv (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)) hLie

section Model


private noncomputable def ggSporKRestFi22_x (i : Fin 6) : ↥fi22P :=
  ⟨fi22FiveLine i, fi22FiveLine_mem_P i⟩

private theorem ggSporKRestFi22_D_le_M :
    i242Y.subgroupOf fi22P ≤ MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) := by
  intro d hd
  rw [Subgroup.mem_subgroupOf] at hd
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  exact MulAction.mem_stabilizer_iff.1 (i242Y_le_stabilizer_U0 hd)

private theorem ggSporKRestFi22_Q_le_M :
    fi22FiveQ.subgroupOf fi22P ≤ MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) := by
  intro q hq
  rw [Subgroup.mem_subgroupOf] at hq
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  exact MulAction.mem_stabilizer_iff.1 (fi22FiveQ_le_stabilizer_U0 hq)

private theorem ggSporKRestFi22_index :
    ((i242Y.subgroupOf fi22P).subgroupOf
      (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))).index = 6 := by
  have h := ((i242Y.subgroupOf fi22P).subgroupOf
    (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ggSporKRestFi22_D_le_M).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe i242Y_le_fi22P).toEquiv, i242_card_Y,
    fi22Omega_card_stabilizer,
    show (1045094400 : ℕ) = 174182400 * 6 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

private noncomputable def ggSporKRestFi22_equiv : ↥(i242Y.subgroupOf fi22P) ≃* ↥omegaT :=
  (Subgroup.subgroupOfEquivOfLe i242Y_le_fi22P).trans (i242YEquiv.trans omegaRestrictEquiv.symm)

private theorem ggSporKRestFi22_simple : IsSimpleGroup ↥(i242Y.subgroupOf fi22P) := by
  haveI : IsSimpleGroup ↥omegaT := CFSG.Timmesfeld.isSimpleGroup_of_lieModel lieModel_omegaT
  exact ggSporKRestFi22_equiv.isSimpleGroup

private theorem ggSporKRestFi22_normal :
    ((i242Y.subgroupOf fi22P).subgroupOf
      (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))).Normal :=
  ggSporKRestFi22_normal_of_index ggSporKRestFi22_D_le_M ggSporKRestFi22_simple
    ggSporKRestFi22_index (by rw [fi22Omega_card_stabilizer]; decide)

private theorem ggSporKRestFi22_solvable :
    haveI := ggSporKRestFi22_normal
    Group.IsSolvable (↥(MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0)) ⧸
      (i242Y.subgroupOf fi22P).subgroupOf
        (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))) := by
  haveI := ggSporKRestFi22_normal
  refine isSolvable_of_card_primeFactors_le_two ?_
  have h : Nat.card (↥(MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0)) ⧸
      (i242Y.subgroupOf fi22P).subgroupOf
        (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))) = 6 :=
    ggSporKRestFi22_index
  rw [h, show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem ggSporKRestFi22_lieModel :
    LieModel (↥(i242Y.subgroupOf fi22P) ⧸ Subgroup.center ↥(i242Y.subgroupOf fi22P))
      .POmegaPlus 4 2 1 := by
  have hc : (Subgroup.center ↥(i242Y.subgroupOf fi22P)).map
      ggSporKRestFi22_equiv.toMonoidHom = ⊥ :=
    (Subgroup.map_center_eq ggSporKRestFi22_equiv).trans center_omegaT
  let q : (↥(i242Y.subgroupOf fi22P) ⧸ Subgroup.center ↥(i242Y.subgroupOf fi22P)) ≃* ↥omegaT :=
    (QuotientGroup.congr _ ⊥ ggSporKRestFi22_equiv hc).trans QuotientGroup.quotientBot
  exact LieModel.of_mulEquiv q.symm lieModel_omegaT

private theorem ggSporKRestFi22_D_le_iSup :
    i242Y.subgroupOf fi22P ≤ ⨆ i : Fin 6, Subgroup.centralizer {ggSporKRestFi22_x i} := by
  have h1 : ∀ i : Fin 6, fi22FiveD i ≤
      (Subgroup.centralizer {ggSporKRestFi22_x i}).map fi22P.subtype := by
    intro i g hg
    refine ⟨⟨g, fi22FiveD_le_P i hg⟩, ?_, rfl⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.1
      (fi22FiveC_le_centralizer_line i (fi22FiveD_le_C i hg))
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hc
  have h2 : i242Y ≤
      (⨆ i : Fin 6, Subgroup.centralizer {ggSporKRestFi22_x i}).map fi22P.subtype := by
    refine i242Y_le_J.trans ?_
    rw [Subgroup.map_iSup]
    exact iSup_mono h1
  intro d hd
  rw [Subgroup.mem_subgroupOf] at hd
  obtain ⟨y, hy, hyd⟩ := h2 hd
  have : y = d := Subtype.ext hyd
  rw [← this]
  exact hy

private theorem ggSporKRestFi22_atQ :
    ∀ Y : Subgroup ↥fi22P, Y ≠ ⊤ → (∃ S : Sylow 5 ↥fi22P, (S : Subgroup ↥fi22P) ≤ Y) →
      SporKRestControls (fi22FiveQ.subgroupOf fi22P) Y → ∀ C : Subgroup ↥fi22P,
        IsComponentOf C Y → LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1 := by
  intro Y hY ⟨S, hSY⟩ hctl C hC
  obtain ⟨Q, hQ⟩ := fi22FiveQ_sylow
  have hx : ∀ i : Fin 6, ggSporKRestFi22_x i ∈ (Q : Subgroup ↥fi22P) := fun i => by
    rw [hQ, Subgroup.mem_subgroupOf]
    exact fi22FiveLine_mem_Q i
  have hx1 : ∀ i : Fin 6, ggSporKRestFi22_x i ≠ 1 := fun i h =>
    fi22FiveLine_ne_one i (congrArg Subtype.val h)
  rw [← hQ] at hctl
  have hQY : (Q : Subgroup ↥fi22P) ≤ Y := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥fi22P) S Q
    have hmem : ∀ y ∈ (Q : Subgroup ↥fi22P), g⁻¹ * y * g ∈ (S : Subgroup ↥fi22P) := by
      intro y hy
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
      simpa [MulAut.smul_def, map_inv, MulAut.conj_apply, mul_assoc] using hy
    have hgY : g ∈ Y := hctl _ (hx 0) (hx1 0) g (hSY (hmem _ (hx 0)))
    intro y hy
    have h := Y.mul_mem (Y.mul_mem hgY (hSY (hmem y hy))) (Y.inv_mem hgY)
    simpa [mul_assoc] using h
  have hNY : Subgroup.normalizer ((Q : Subgroup ↥fi22P) : Set ↥fi22P) ≤ Y := by
    intro n hn
    exact hctl _ (hx 0) (hx1 0) n (hQY ((Subgroup.mem_normalizer_iff''.1 hn _).1 (hx 0)))
  have hDY : i242Y.subgroupOf fi22P ≤ Y := by
    refine ggSporKRestFi22_D_le_iSup.trans (iSup_le fun i c hc => ?_)
    refine hctl _ (hx i) (hx1 i) c (hQY ?_)
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
    exact hx i
  have hQM : (Q : Subgroup ↥fi22P) ≤ MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) :=
    hQ ▸ ggSporKRestFi22_Q_le_M
  have hQD : (Q : Subgroup ↥fi22P) ≤ i242Y.subgroupOf fi22P := by
    haveI := ggSporKRestFi22_normal
    have h := ggSporKRestFi22_le_of_not_dvd_index (p := 5)
      (P := (Q : Subgroup ↥fi22P).subgroupOf
        (MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0)))
      (Q.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm)
      (by rw [ggSporKRestFi22_index]; decide)
    intro q hq
    exact Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_subgroupOf.2 (show q ∈ (Q : Subgroup _) from
      hq) : (⟨q, hQM hq⟩ : ↥(MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0))) ∈ _))
  have hMY : MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) ≤ Y :=
    (ggSporKRestFi22_le_sup_normalizer Q hQD ggSporKRestFi22_D_le_M ggSporKRestFi22_normal).trans
      (sup_le hDY hNY)
  have hYM : Y = MulAction.stabilizer (↥fi22P) (ptSet 3510 fi22OmegaU0) :=
    ((fi22Omega_isCoatom).le_iff.1 hMY).resolve_left hY
  rw [hYM] at hC
  rw [ggSporKRestFi22_component_eq ggSporKRestFi22_D_le_M ggSporKRestFi22_simple
    ggSporKRestFi22_normal ggSporKRestFi22_solvable hC]
  exact ggSporKRestFi22_lieModel

private theorem ggSporKRestFi22_P : SporKRestFi22Exc ↥fi22P := by
  intro E _ hcard Y hY hS hctl C hC
  obtain ⟨Q, hQ⟩ := fi22FiveQ_sylow
  have hcardE : Nat.card E = 5 ^ (Nat.card ↥fi22P).factorization 5 := by
    rw [hcard, factorization_card_fi22P_five]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥fi22P) Q (Sylow.ofCard E hcardE)
  have hEQ : E = (fi22FiveQ.subgroupOf fi22P).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun S : Sylow 5 ↥fi22P => (S : Subgroup ↥fi22P)) hg
    simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h
    rw [← h, hQ, Subgroup.pointwise_smul_def]
    rfl
  rw [hEQ] at hctl
  exact ggSporKRestFi22_map (MulAut.conj g) ggSporKRestFi22_atQ hY hS hctl hC

theorem sporKRest_fi22_exc_Fi22_5 : SporKRestFi22Exc (TauCeti.CFSGIndex.sporadic .Fi22).Group :=
  SporKRestFi22Exc.of_mulEquiv
    (fi22PermEquiv.symm.trans (Classical.choice CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv))
    ggSporKRestFi22_P

end Model

end CFSG.StandardType.SporadicShape
