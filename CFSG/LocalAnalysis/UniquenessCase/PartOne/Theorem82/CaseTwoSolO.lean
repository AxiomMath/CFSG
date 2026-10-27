module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.SignalizerFunctorTheorem.McBride.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.GroupTheory.SteinbergCBFTHall
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoOStar
public import CFSG.Adapters.QiuzhenLegacy.Compat.G6.CentralizerControl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

attribute [local instance] CFSG.pCore_normal

private noncomputable abbrev solOn (t : CaseTwoTransitive c) (N : Subgroup G) : Subgroup G :=
  CFSG.SignalizerFunctorTheorem.McBride.sol (t.On N)

private lemma pCore_two_sol (N : Subgroup G) :
    CFSG.Open.pCoreOf 2 (t.solOn N) = CFSG.Open.pCoreOf 2 (t.Dn N) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := t.Dn N
  let O : Subgroup G := t.On N
  let S : Subgroup G := t.solOn N
  let Q0 : Subgroup G := CFSG.Open.pCoreOf 2 D
  change CFSG.Open.pCoreOf 2 S = Q0
  have hOD : O ≤ D := t.On_le_Dn N
  have hSD : S ≤ D := (CFSG.SignalizerFunctorTheorem.McBride.sol_le O).trans hOD
  have hDS : D ≤ Subgroup.normalizer (S : Set G) :=
    (t.Dn_le N).trans (t.le_normalizer_sol_on N)
  have hQ0_2 : IsPGroup 2 Q0 :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥D)).map D.subtype
  have hQ0_cop3 : Nat.Coprime 3 (Nat.card Q0) := by
    obtain ⟨n, hn⟩ := hQ0_2.exists_card_eq
    rw [hn]
    exact (Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num) |>.pow_right n
  have hQ0n : (Q0.subgroupOf D).Normal := by
    rw [show Q0.subgroupOf D = CFSG.pCore 2 ↥D from
      CFSG.openPCoreOf_subgroupOf (p := 2) (H := D)]
    exact CFSG.pCore_normal
  haveI : (Q0.subgroupOf D).Normal := hQ0n
  have hNQ0 : N ≤ Subgroup.normalizer (Q0 : Set G) :=
    (t.le_normalizer_Dn N).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        D (CFSG.pCore 2 ↥D) CFSG.pCore_characteristic)
  have hQ0D : Q0 ≤ D := CFSG.openPCoreOf_le 2 D
  have hQ0O : Q0 ≤ O := CFSG.subgroupOf_le_pPrimeCore_map (p := 3) hQ0D hQ0_cop3
  have hQ0S : Q0 ≤ S := by
    have hnormal : (Q0.subgroupOf O).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0O).mpr
        (hOD.trans ((t.Dn_le N).trans hNQ0))
    have hsolv : Group.IsSolvable ↥(Q0.subgroupOf O) :=
      @IsNilpotent.to_isSolvable ↥(Q0.subgroupOf O) _
        (hQ0_2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ0O).symm).isNilpotent
    have h := Subgroup.map_mono (f := O.subtype)
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hnormal hsolv)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ0O] at h
  refine le_antisymm (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hSD hDS) ?_
  have hn : (Q0.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ0S]
    intro x s hx hs
    exact (Subgroup.normal_subgroupOf_iff hQ0D).mp hQ0n x s hx (hSD hs)
  have h2 : IsPGroup 2 ↥(Q0.subgroupOf S) :=
    hQ0_2.of_equiv (Subgroup.subgroupOfEquivOfLe hQ0S).symm
  have hle : Q0.subgroupOf S ≤ CFSG.pCore 2 ↥S := le_sSup ⟨hn, h2⟩
  have h := Subgroup.map_mono (f := S.subtype) hle
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ0S] at h
  simpa [CFSG.openPCoreOf_eq_map_pCore] using h

private lemma coprime_six_relIndex (N : Subgroup G)
    (hO2S : CFSG.Open.pCoreOf 2 (t.solOn N) = CFSG.Open.pCoreOf 2 (t.Dn N))
    (hcop3 : Nat.Coprime 3 (Nat.card (t.solOn N))) :
    Nat.Coprime 6 ((CFSG.Open.pCoreOf 2 (t.Dn N)).relIndex
      (CFSG.Quasithin.oTwoFIn (t.solOn N))) := by
  classical
  let S : Subgroup G := t.solOn N
  let Q0 : Subgroup G := CFSG.Open.pCoreOf 2 (t.Dn N)
  let QS : Subgroup ↥S := CFSG.pCore 2 ↥S
  let Fbar : Subgroup (↥S ⧸ QS) := CFSG.fittingSubgroup (↥S ⧸ QS)
  let F1S : Subgroup ↥S := Fbar.comap (QuotientGroup.mk' QS)
  let F1 : Subgroup G := F1S.map S.subtype
  change Nat.Coprime 6 (Q0.relIndex F1)
  have hO2S' : CFSG.Open.pCoreOf 2 S = Q0 := hO2S
  have hF1_le : F1 ≤ S := Subgroup.map_subtype_le _
  have hQ0subS : Q0.subgroupOf S = QS := by
    rw [← hO2S', CFSG.openPCoreOf_subgroupOf]
  have hF1subS : F1.subgroupOf S = F1S := by
    rw [show F1 = F1S.map S.subtype from rfl]
    exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective F1S
  have hcoreS : CFSG.pCore 2 (↥S ⧸ CFSG.pCore 2 ↥S) = ⊥ :=
    CFSG.Quasithin.pCore_two_quotient_pCore_two ↥S
  have hoddFbar : Odd (Nat.card Fbar) := CFSG.Quasithin.B1.fitting_card_odd hcoreS
  have h3quot : Nat.Coprime 3 (Nat.card (↥S ⧸ CFSG.pCore 2 ↥S)) := by
    rw [← Subgroup.index_eq_card]
    exact hcop3.of_dvd_right (Subgroup.index_dvd_card (H := CFSG.pCore 2 ↥S))
  have hcopFbar : Nat.Coprime 6 (Nat.card Fbar) := by
    have h2 : Nat.Coprime 2 (Nat.card Fbar) := hoddFbar.coprime_two_left
    have h3 : Nat.Coprime 3 (Nat.card Fbar) :=
      h3quot.of_dvd_right (Subgroup.card_subgroup_dvd_card Fbar)
    simpa using Nat.Coprime.mul_left h2 h3
  have hQ0rel : (Q0.subgroupOf F1).index = Nat.card Fbar := by
    calc (Q0.subgroupOf F1).index = Q0.relIndex F1 := rfl
      _ = (Q0.subgroupOf S).relIndex (F1.subgroupOf S) :=
          (Subgroup.relIndex_subgroupOf hF1_le).symm
      _ = QS.relIndex F1S := by rw [hQ0subS, hF1subS]
      _ = (QuotientGroup.mk' QS).ker.relIndex F1S := by rw [QuotientGroup.ker_mk']
      _ = Nat.card ↥(Subgroup.map (QuotientGroup.mk' QS) F1S) := Subgroup.relIndex_ker F1S _
      _ = Nat.card Fbar := by
          rw [show F1S = Fbar.comap (QuotientGroup.mk' QS) from rfl,
            Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective QS) Fbar]
  rw [show Q0.relIndex F1 = (Q0.subgroupOf F1).index from rfl, hQ0rel]
  exact hcopFbar

private lemma le_M_of_coprime_index (N H : Subgroup G) {F1 : Subgroup G}
    (hF1_le : F1 ≤ t.solOn N) (hNF1 : N ≤ Subgroup.normalizer (F1 : Set G))
    (hcop : Nat.Coprime 6 ((CFSG.Open.pCoreOf 2 (t.Dn N)).relIndex F1))
    (hDH : t.Dn N ≤ H) (hHN : H ≤ N)
    (h528 : ∀ X : Subgroup G, CFSG.Open.pCoreOf 2 H ≤ X → X ≤ H →
      H ≤ Subgroup.normalizer (X : Set G) → ¬ 2 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index →
      ¬ 3 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index → X ≤ c.S.M) :
    F1 ≤ c.S.M := by
  classical
  let D : Subgroup G := t.Dn N
  let Q0 : Subgroup G := CFSG.Open.pCoreOf 2 D
  let QH : Subgroup G := CFSG.Open.pCoreOf 2 H
  have hQHn : (QH.subgroupOf H).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_normal
  have hH_QH : H ≤ Subgroup.normalizer (QH : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.openPCoreOf_le 2 H)).mp hQHn
  have hHD : H ≤ Subgroup.normalizer (D : Set G) := hHN.trans (t.le_normalizer_Dn N)
  have hQ0QH : Q0 ≤ QH :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hDH hHD
  have hH_F1 : H ≤ Subgroup.normalizer (F1 : Set G) := hHN.trans hNF1
  let X : Subgroup G := F1 ⊔ QH
  have hQHX : QH ≤ X := le_sup_right
  have hXH : X ≤ H :=
    sup_le (hF1_le.trans (((CFSG.SignalizerFunctorTheorem.McBride.sol_le (t.On N)).trans
      (t.On_le_Dn N)).trans hDH)) (CFSG.openPCoreOf_le 2 H)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hH_F1 hH_QH).trans (Subgroup.inf_normalizer_le_normalizer_sup F1 QH)
  have hQH_le_normF1 : QH ≤ Subgroup.normalizer (F1 : Set G) :=
    (CFSG.openPCoreOf_le 2 H).trans hH_F1
  have hrelX : (QH.subgroupOf X).index = (QH.subgroupOf F1).index := by
    change QH.relIndex X = QH.relIndex F1
    have h := CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer
      (H := QH) (K := F1) hQH_le_normF1
    rw [show X = QH ⊔ F1 by rw [show X = F1 ⊔ QH from rfl, sup_comm]]
    exact h.symm
  have hdiv : (QH.subgroupOf X).index ∣ (Q0.subgroupOf F1).index := by
    rw [hrelX]
    exact Subgroup.index_dvd_of_le (fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hQ0QH (Subgroup.mem_subgroupOf.mp hx)))
  have hcopIdx : Nat.Coprime 6 ((QH.subgroupOf X).index) :=
    Nat.Coprime.of_dvd_right hdiv (by
      show Nat.Coprime 6 ((Q0.subgroupOf F1).index)
      exact hcop)
  have h2idx : ¬ 2 ∣ (QH.subgroupOf X).index :=
    (Nat.prime_two.coprime_iff_not_dvd).mp
      (Nat.Coprime.of_dvd_left (by norm_num : 2 ∣ 6) hcopIdx)
  have h3idx : ¬ 3 ∣ (QH.subgroupOf X).index :=
    (Nat.prime_three.coprime_iff_not_dvd).mp
      (Nat.Coprime.of_dvd_left (by norm_num : 3 ∣ 6) hcopIdx)
  exact (le_sup_left : F1 ≤ X).trans (h528 X hQHX hXH hHX h2idx h3idx)

private lemma commutator_Z_le_pCore (N : Subgroup G) {F1 : Subgroup G}
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hF1M : F1 ≤ c.S.M) (hNF1 : N ≤ Subgroup.normalizer (F1 : Set G)) (hKN : t.Ky ≤ N)
    (hF1_le : F1 ≤ t.solOn N) (hcop3 : Nat.Coprime 3 (Nat.card (t.solOn N))) :
    ⁅F1, t.Z⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N) := by
  classical
  let D : Subgroup G := t.Dn N
  let Q0 : Subgroup G := CFSG.Open.pCoreOf 2 D
  let Q : Subgroup G := c.L ⊓ t.d.N
  change ⁅F1, t.Z⁆ ≤ Q0
  have h3F1 : ¬ 3 ∣ Nat.card F1 :=
    (Nat.prime_three.coprime_iff_not_dvd).mp
      (hcop3.of_dvd_right (Subgroup.card_dvd_of_le hF1_le))
  have hKyF1 : t.Ky ≤ Subgroup.normalizer (F1 : Set G) := hKN.trans hNF1
  have hcomm1 : ⁅F1, t.Ky⁆ ≤ F1 ⊓ Q :=
    t.commutator_Ky_le_inf_N hK32 hGA hSp hF1M hKyF1 h3F1
  have hM_Q : c.S.M ≤ Subgroup.normalizer (Q : Set G) := by
    have hN_norm : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
      simpa [t.hdM] using SylowThreeData.N_normal t.d
    exact (le_inf c.le_normalizer_L hN_norm).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQ_2 : IsPGroup 2 Q :=
    (SylowThreeData.N_isPGroup t.d).to_le inf_le_right
  have hF1Q_le : F1 ⊓ Q ≤ CFSG.Open.pCoreOf 2 F1 := by
    have hQF1 : F1 ≤ Subgroup.normalizer (Q : Set G) := hF1M.trans hM_Q
    have hnormal : ((F1 ⊓ Q).subgroupOf F1).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        ((le_inf Subgroup.le_normalizer hQF1).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
    have h2' : IsPGroup 2 ↥(F1 ⊓ Q) := hQ_2.to_le inf_le_right
    have h2 : IsPGroup 2 ↥((F1 ⊓ Q).subgroupOf F1) :=
      h2'.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    have hle : (F1 ⊓ Q).subgroupOf F1 ≤ CFSG.pCore 2 ↥F1 := le_sSup ⟨hnormal, h2⟩
    have h := Subgroup.map_mono (f := F1.subtype) hle
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at h
    simpa [CFSG.openPCoreOf_eq_map_pCore] using h
  have hDF1 : D ≤ Subgroup.normalizer (F1 : Set G) := (t.Dn_le N).trans hNF1
  have hpcF1_le : CFSG.Open.pCoreOf 2 F1 ≤ Q0 :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (hF1_le.trans
      ((CFSG.SignalizerFunctorTheorem.McBride.sol_le (t.On N)).trans (t.On_le_Dn N))) hDF1
  have hcommQ0 : ⁅F1, t.Ky⁆ ≤ Q0 := hcomm1.trans (hF1Q_le.trans hpcF1_le)
  exact (Subgroup.commutator_mono le_rfl t.Z_le_Ky).trans hcommQ0

private lemma commutator_Dn_le_pCore (N : Subgroup G) {F1 : Subgroup G}
    (hcommZ : ⁅F1, t.Z⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N))
    (hNF1 : N ≤ Subgroup.normalizer (F1 : Set G)) (hF1_le : F1 ≤ t.solOn N) :
    ⁅t.Dn N, F1⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N) := by
  classical
  let D : Subgroup G := t.Dn N
  let Q0 : Subgroup G := CFSG.Open.pCoreOf 2 D
  change ⁅D, F1⁆ ≤ Q0
  have hF1N : F1 ≤ N := (hF1_le.trans ((CFSG.SignalizerFunctorTheorem.McBride.sol_le
    (t.On N)).trans (t.On_le_Dn N))).trans (t.Dn_le N)
  let QN : Subgroup ↥N := Q0.subgroupOf N
  have hQ0N : Q0 ≤ N := (CFSG.openPCoreOf_le 2 D).trans (t.Dn_le N)
  have hNQ0 : N ≤ Subgroup.normalizer (Q0 : Set G) :=
    (t.le_normalizer_Dn N).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        D (CFSG.pCore 2 ↥D) CFSG.pCore_characteristic)
  haveI : QN.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0N).mpr hNQ0
  let FN : Subgroup (↥N ⧸ QN) := (F1.subgroupOf N).map (QuotientGroup.mk' QN)
  have hFNn : FN.Normal := by
    refine Subgroup.Normal.map ?_ (QuotientGroup.mk' QN) (QuotientGroup.mk'_surjective QN)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hF1N).mpr hNF1
  haveI : FN.Normal := hFNn
  let CN : Subgroup ↥N := (Subgroup.centralizer (FN : Set (↥N ⧸ QN))).comap
    (QuotientGroup.mk' QN)
  have hZ_le_CN : t.Z.subgroupOf N ≤ CN := by
    intro z hz
    rw [show CN = (Subgroup.centralizer (FN : Set (↥N ⧸ QN))).comap
      (QuotientGroup.mk' QN) from rfl, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hy
    have hmem : ⁅(f : ↥N), z⁆ ∈ QN := by
      rw [show QN = Q0.subgroupOf N from rfl]
      exact Subgroup.mem_subgroupOf.mpr (by
        change ⁅(f : G), (z : G)⁆ ∈ Q0
        exact hcommZ (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hf)
          (Subgroup.mem_subgroupOf.mp hz)))
    have hq : (QuotientGroup.mk' QN) ⁅(f : ↥N), z⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_commutatorElement] at hq
    exact commutatorElement_eq_one_iff_mul_comm.mp hq
  have hD_le_CN : D ≤ CN.map N.subtype :=
    Subgroup.map_mono (Subgroup.normalClosure_le_normal hZ_le_CN)
  rw [Subgroup.commutator_le]
  intro d hd f hf
  obtain ⟨n, hnCN, rfl⟩ := Subgroup.mem_map.mp (hD_le_CN hd)
  have hfN : (⟨f, hF1N hf⟩ : ↥N) ∈ F1.subgroupOf N := Subgroup.mem_subgroupOf.mpr hf
  have hfFN : (QuotientGroup.mk' QN) ⟨f, hF1N hf⟩ ∈ FN :=
    Subgroup.mem_map.mpr ⟨⟨f, hF1N hf⟩, hfN, rfl⟩
  have hcen := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hnCN)) _ hfFN
  have hq : (QuotientGroup.mk' QN) ⁅n, (⟨f, hF1N hf⟩ : ↥N)⁆ = 1 := by
    simpa [map_commutatorElement] using
      commutatorElement_eq_one_iff_mul_comm.mpr hcen.symm
  have hmemQ0 : N.subtype ⁅n, (⟨f, hF1N hf⟩ : ↥N)⁆ ∈ Q0 :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)
  simpa [map_commutatorElement] using hmemQ0

private lemma eq_sol (N : Subgroup G)
    (hO2S : CFSG.Open.pCoreOf 2 (t.solOn N) = CFSG.Open.pCoreOf 2 (t.Dn N))
    (hcommD_F1 : ⁅t.Dn N, CFSG.Quasithin.oTwoFIn (t.solOn N)⁆ ≤
      CFSG.Open.pCoreOf 2 (t.Dn N)) :
    CFSG.Quasithin.oTwoFIn (t.solOn N) = t.solOn N := by
  classical
  let D : Subgroup G := t.Dn N
  let S : Subgroup G := t.solOn N
  let Q0 : Subgroup G := CFSG.Open.pCoreOf 2 D
  let QS : Subgroup ↥S := CFSG.pCore 2 ↥S
  let Fbar : Subgroup (↥S ⧸ QS) := CFSG.fittingSubgroup (↥S ⧸ QS)
  let F1S : Subgroup ↥S := Fbar.comap (QuotientGroup.mk' QS)
  let F1 : Subgroup G := F1S.map S.subtype
  change F1 = S
  have hO2S' : CFSG.Open.pCoreOf 2 S = Q0 := hO2S
  have hSD : S ≤ D := (CFSG.SignalizerFunctorTheorem.McBride.sol_le (t.On N)).trans
    (t.On_le_Dn N)
  have hQ0QS : Q0 = (CFSG.pCore 2 ↥S).map S.subtype := by
    rw [← hO2S', CFSG.openPCoreOf_eq_map_pCore]
  have hS_solv : Group.IsSolvable ↥S :=
    CFSG.SignalizerFunctorTheorem.McBride.isSolvable_sol (t.On N)
  have hquot_solv : Group.IsSolvable (↥S ⧸ QS) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' QS)
      (QuotientGroup.mk'_surjective QS)
  have hcommS : ⁅(⊤ : Subgroup ↥S), F1S⁆ ≤ QS := by
    rw [Subgroup.commutator_le]
    intro a _ f hf
    have hfG : (f : G) ∈ F1 := Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
    have hg : S.subtype ⁅a, f⁆ ∈ Q0 := by
      simpa [map_commutatorElement] using
        hcommD_F1 (Subgroup.commutator_mem_commutator (hSD a.2) hfG)
    rw [hQ0QS] at hg
    exact (Subgroup.mem_map_iff_mem S.subtype_injective).mp hg
  have hcommSbar : ⁅(⊤ : Subgroup (↥S ⧸ QS)), Fbar⁆ = ⊥ := by
    have hmap : Subgroup.map (QuotientGroup.mk' QS) ⁅(⊤ : Subgroup ↥S), F1S⁆ =
        ⁅(⊤ : Subgroup (↥S ⧸ QS)), Fbar⁆ := by
      rw [Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective QS),
        show F1S = Fbar.comap (QuotientGroup.mk' QS) from rfl,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective QS) Fbar]
    rw [← hmap]
    have hzero : Subgroup.map (QuotientGroup.mk' QS) QS = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact le_bot_iff.mp ((Subgroup.map_mono hcommS).trans (le_of_eq hzero))
  have hcent : Subgroup.centralizer (Fbar : Set (↥S ⧸ QS)) ≤ Fbar :=
    CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hquot_solv
  have hFbar_top : Fbar = ⊤ :=
    eq_top_iff.mpr (((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⊤)
      (H₂ := Fbar)).mp hcommSbar).trans hcent)
  rw [show F1 = F1S.map S.subtype from rfl,
    show F1S = Fbar.comap (QuotientGroup.mk' QS) from rfl, hFbar_top, Subgroup.comap_top,
    Subgroup.map_top, Subgroup.range_subtype]

theorem sol_On_le (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N H : Subgroup G}
    (hKN : t.Ky ≤ N) (hDH : t.Dn N ≤ H) (hHN : H ≤ N)
    (h528 : ∀ X : Subgroup G, CFSG.Open.pCoreOf 2 H ≤ X → X ≤ H →
      H ≤ Subgroup.normalizer (X : Set G) →
      ¬ 2 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index →
      ¬ 3 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index → X ≤ c.S.M) :
    CFSG.SignalizerFunctorTheorem.McBride.sol (t.On N) ≤ c.S.M ∧
      ⁅t.Dn N, CFSG.SignalizerFunctorTheorem.McBride.sol (t.On N)⁆ ≤
        CFSG.Open.pCoreOf 2 (t.Dn N) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := t.Dn N
  let O : Subgroup G := t.On N
  let S : Subgroup G := t.solOn N
  let Q0 : Subgroup G := CFSG.Open.pCoreOf 2 D
  let QS : Subgroup ↥S := CFSG.pCore 2 ↥S
  let Fbar : Subgroup (↥S ⧸ QS) := CFSG.fittingSubgroup (↥S ⧸ QS)
  let F1S : Subgroup ↥S := Fbar.comap (QuotientGroup.mk' QS)
  let F1 : Subgroup G := F1S.map S.subtype
  have hNS : N ≤ Subgroup.normalizer (S : Set G) := t.le_normalizer_sol_on N
  have hO2S : CFSG.Open.pCoreOf 2 S = Q0 := t.pCore_two_sol N
  have hcop3 : Nat.Coprime 3 (Nat.card S) := by
    have hO3 : Nat.Coprime 3 (Nat.card O) := by
      rw [show O = (CFSG.pPrimeCore 3 ↥D).map D.subtype from rfl,
        Subgroup.card_map_of_injective D.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact hO3.of_dvd_right
      (Subgroup.card_dvd_of_le (CFSG.SignalizerFunctorTheorem.McBride.sol_le O))
  have hcopQ0 : Nat.Coprime 6 (Q0.relIndex F1) := t.coprime_six_relIndex N hO2S hcop3
  have hNF1 : N ≤ Subgroup.normalizer (F1 : Set G) :=
    hNS.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        S F1S (Subgroup.Characteristic.comap_quotient_mk (H := QS) (K := Fbar)
          CFSG.fittingSubgroup_characteristic))
  have hF1_le : F1 ≤ S := Subgroup.map_subtype_le _
  have hF1M : F1 ≤ c.S.M :=
    t.le_M_of_coprime_index N H hF1_le hNF1 hcopQ0 hDH hHN h528
  have hcommZ : ⁅F1, t.Z⁆ ≤ Q0 :=
    t.commutator_Z_le_pCore N hK32 hGA hSp hF1M hNF1 hKN hF1_le hcop3
  have hcommD_F1 : ⁅D, F1⁆ ≤ Q0 := t.commutator_Dn_le_pCore N hcommZ hNF1 hF1_le
  have hF1_eq_S : F1 = S := t.eq_sol N hO2S hcommD_F1
  constructor
  · show S ≤ c.S.M
    rw [← hF1_eq_S]
    exact hF1M
  · show ⁅D, S⁆ ≤ Q0
    rw [← hF1_eq_S]
    exact hcommD_F1

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
