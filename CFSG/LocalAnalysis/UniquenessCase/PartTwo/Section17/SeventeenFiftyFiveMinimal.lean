module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338One
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen68Close
public import CFSG.GroupTheory.NormalizerInfCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTen
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_Z_ne_bot_of_uc2_10_9 {D : Data G} (h109 : Inputs1719.UC2_10_9 D)
    {K B : Subgroup G} {s p : ℕ} (hs : Odd s) (hp : p.Prime) (hdvd : p ∣ 2 ^ s - 1)
    (hBK : B ≤ K) (hKM : K ≤ D.M) (hBT : B ≤ Subgroup.normalizer (D.T : Set G))
    (hcard : Nat.card B = p) (hBU : UC6.InU D.M B) (hUT : UniqueMax D.M (K ⊔ D.T)) :
    ⁅K, D.Z⁆ ≠ ⊥ := by
  intro hKZ
  have hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKZ
  have hBCZ : B ≤ Subgroup.centralizer (D.Z : Set G) := hBK.trans hKCZ
  have hnotle : ¬ Subgroup.centralizer (D.Z : Set G) ≤ D.M :=
    (h109 s p B hs hp hdvd (le_inf (hBK.trans hKM) hBT) hcard hBU).2.2.1 hBCZ
  have hloc : IsTwoLocal (Subgroup.normalizer (D.Z : Set G)) :=
    ⟨D.Z, uc22main1_Z_ne_bot D, D.sylowM.isPGroup.to_le (uc22main1_Z_le_T D), rfl⟩
  have hKT : K ⊔ D.T ≤ Subgroup.normalizer (D.Z : Set G) :=
    sup_le (hKCZ.trans (Subgroup.centralizer_le_normalizer _))
      ((uc22main1_T_le_centralizer D).trans (Subgroup.centralizer_le_normalizer _))
  exact hnotle ((Subgroup.centralizer_le_normalizer _).trans
    (uc22p22p_le_of_uniqueMax hUT hloc hKT))

theorem o2Trivial_mbar_of_twoReduced {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hred : TwoReduced M V) :
    O2Trivial (Mbar M (⊥ : Subgroup G) V hV) := by
  intro P hPM hPN hP2
  have hMs : M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  set K : Subgroup G := preBarSub M (⊥ : Subgroup G) V hV P
  have hKM : K ≤ M := inf_le_left
  have hKleN : K ≤ Subgroup.normalizer (V : Set G) := hKM.trans hMV
  have hKnormal : (K.subgroupOf M).Normal := by
    refine Subgroup.Normal.mk ?_
    intro m hm k
    obtain ⟨hmK, hmS, hmP⟩ := (mem_preBarSub M (⊥ : Subgroup G) V hV P).1 hm
    have hkS : (k : G) ∈ stabTil (⊥ : Subgroup G) V := hMs k.2
    have hconjS : (k : G) * (m : G) * (k : G)⁻¹ ∈ stabTil (⊥ : Subgroup G) V :=
      (stabTil (⊥ : Subgroup G) V).mul_mem
        ((stabTil (⊥ : Subgroup G) V).mul_mem hkS hmS)
        ((stabTil (⊥ : Subgroup G) V).inv_mem hkS)
    change ((k : G) * (m : G) * (k : G)⁻¹) ∈ K
    refine (mem_preBarSub M (⊥ : Subgroup G) V hV P).2
      ⟨M.mul_mem (M.mul_mem k.2 hmK) (M.inv_mem k.2), hconjS, ?_⟩
    have hφ : actTil (⊥ : Subgroup G) V hV ⟨(k : G) * (m : G) * (k : G)⁻¹, hconjS⟩ =
        actTil (⊥ : Subgroup G) V hV ⟨(k : G), hkS⟩ *
          actTil (⊥ : Subgroup G) V hV ⟨(m : G), hmS⟩ *
          (actTil (⊥ : Subgroup G) V hV ⟨(k : G), hkS⟩)⁻¹ := by
      rw [show (⟨(k : G) * (m : G) * (k : G)⁻¹, hconjS⟩ : ↥(stabTil (⊥ : Subgroup G) V)) =
        ⟨(k : G), hkS⟩ * ⟨(m : G), hmS⟩ * ⟨(k : G), hkS⟩⁻¹ from Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc])]
      rw [map_mul, map_mul, map_inv]
    rw [hφ]
    have hmMbar : actTil (⊥ : Subgroup G) V hV ⟨(m : G), hmS⟩ ∈ Mbar M (⊥ : Subgroup G) V hV :=
      actTil_mem_barSub (⊥ : Subgroup G) V hV hmK hmS
    have hkMbar : actTil (⊥ : Subgroup G) V hV ⟨(k : G), hkS⟩ ∈ Mbar M (⊥ : Subgroup G) V hV :=
      actTil_mem_barSub (⊥ : Subgroup G) V hV k.2 hkS
    have hconj := hPN.conj_mem ⟨actTil (⊥ : Subgroup G) V hV ⟨(m : G), hmS⟩, hmMbar⟩ hmP
      ⟨actTil (⊥ : Subgroup G) V hV ⟨(k : G), hkS⟩, hkMbar⟩
    simpa using (Subgroup.mem_subgroupOf.mp hconj)
  have hMN : M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hKnormal
  have hCK : M ⊓ Subgroup.centralizer (V : Set G) ≤ K := by
    rintro m ⟨hmM, hmC⟩
    refine (mem_preBarSub M (⊥ : Subgroup G) V hV P).2 ⟨hmM, hMs hmM, ?_⟩
    have h1 : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM⟩ = 1 := by
      rw [actTil_eq_one_iff]
      intro v hv
      rw [Subgroup.mem_bot]
      have hcomm := Subgroup.mem_centralizer_iff.1 hmC v hv
      rw [← hcomm]
      group
    rw [h1]
    exact Subgroup.one_mem P
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
  have hidx : ((Subgroup.centralizer (V : Set G)).subgroupOf K).index = 2 ^ n := by
    have hcard : Nat.card (barSub (⊥ : Subgroup G) V hV K) =
        ((Subgroup.centralizer (V : Set G)).subgroupOf K).index :=
      s1668_card_barSub_bot hV hKleN
    rw [barSub_preBarSub, inf_eq_left.mpr hPM, hn] at hcard
    exact hcard.symm
  have hKcent : K ≤ Subgroup.centralizer (V : Set G) := hred K hKM hMN hCK ⟨n, hidx⟩
  refine le_bot_iff.1 ?_
  intro p hp
  obtain ⟨m, hmM, hmp⟩ := (mem_barSub (⊥ : Subgroup G) V hV M p).1 (hPM hp)
  have hmK : (m : G) ∈ K := by
    refine (mem_preBarSub M (⊥ : Subgroup G) V hV P).2 ⟨hmM, m.2, ?_⟩
    rwa [hmp]
  have hmC : (m : G) ∈ Subgroup.centralizer (V : Set G) := hKcent hmK
  rw [Subgroup.mem_bot, ← hmp, actTil_eq_one_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hcomm := Subgroup.mem_centralizer_iff.1 hmC v hv
  rw [← hcomm]
  group

theorem seventeen_fiftyfive_min_base {D : Data G} {K : Subgroup G}
    (hKZ : ⁅K, D.Z⁆ ≠ ⊥) :
    ∃ V' : Subgroup G, V' ≤ D.U ∧ D.M ≤ Subgroup.normalizer (V' : Set G) ∧
      ⁅K, V'⁆ ≠ ⊥ ∧
      ∀ W : Subgroup G, W ≤ D.U → D.M ≤ Subgroup.normalizer (W : Set G) → W ≤ V' →
        ⁅K, W⁆ ≠ ⊥ → W = V' := by
  classical
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  have hUmem : D.U ∈ {W : Subgroup G | W ≤ D.U ∧
      D.M ≤ Subgroup.normalizer (W : Set G) ∧ ⁅K, W⁆ ≠ ⊥} := by
    refine ⟨le_rfl, CFSG.LocalAnalysis.RankThreeUC.le_normalizer_uCore D.M D.T, ?_⟩
    intro hKU
    apply hKZ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hKU ⊢
    exact hKU.trans (Subgroup.centralizer_le (uc22main1_Z_le_U D))
  obtain ⟨V', hV'mem, hmin⟩ := Set.exists_min_image
    {W : Subgroup G | W ≤ D.U ∧ D.M ≤ Subgroup.normalizer (W : Set G) ∧ ⁅K, W⁆ ≠ ⊥}
    (fun W => Nat.card W) (Set.toFinite _) ⟨D.U, hUmem⟩
  refine ⟨V', hV'mem.1, hV'mem.2.1, hV'mem.2.2, ?_⟩
  intro W hWU hWM hWV hKW
  exact Subgroup.eq_of_le_of_card_ge hWV (hmin W ⟨hWU, hWM, hKW⟩)

theorem seventeen_fiftyfive_min_commutator_eq {D : Data G} {K V' : Subgroup G}
    (hK : K ∈ calC D.M) (hV'U : V' ≤ D.U)
    (hKN : D.M ≤ Subgroup.normalizer (K : Set G))
    (hMV : D.M ≤ Subgroup.normalizer (V' : Set G)) (hKV' : ⁅K, V'⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ Subgroup.normalizer (W : Set G) → W ≤ V' →
      ⁅K, W⁆ ≠ ⊥ → W = V') :
    ⁅K, V'⁆ = V' := by
  have hKNV : K ≤ Subgroup.normalizer (V' : Set G) := hK.1.le.trans hMV
  have hcomm_le : ⁅K, V'⁆ ≤ V' := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hKNV
  by_contra hne
  have hWU : ⁅K, V'⁆ ≤ D.U := hcomm_le.trans hV'U
  have hWM : D.M ≤ Subgroup.normalizer ((⁅K, V'⁆ : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKN hm),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMV hm)]
  have hWne : ⁅K, ⁅K, V'⁆⁆ ≠ ⊥ := by
    intro hbot
    have h1 : ⁅⁅K, V'⁆, K⁆ ≤ (⊥ : Subgroup G) := by
      rw [Subgroup.commutator_comm]
      exact le_of_eq hbot
    have h2 : ⁅⁅V', K⁆, K⁆ ≤ (⊥ : Subgroup G) := by
      rw [Subgroup.commutator_comm V' K]
      exact h1
    have h3 := CFSG.GroupTheory.commutator_commutator_le_of_rotate_normal
      (M := ⊤) (A := K) (B := V') (N := ⊥) le_top le_top bot_le
      (by rw [Subgroup.normalizer_eq_top]) h1 h2
    rw [hK.2.1] at h3
    exact hKV' (le_bot_iff.mp h3)
  exact hne (hmin ⁅K, V'⁆ hWU hWM hcomm_le hWne)

theorem seventeen_fiftyfive_min_pCore_le_centralizer {D : Data G} {K V' : Subgroup G}
    (hK : K ∈ calC D.M) (hV'U : V' ≤ D.U) :
    pCoreOf 2 K ≤ Subgroup.centralizer (V' : Set G) := by
  have hPK : pCoreOf 2 K ≤ pCoreOf 2 D.M := uc22p22r_pCoreOf_le_of_isSubnormal hK.1
  have hU : D.U ≤ pCoreOf 2 D.M ⊓
      Subgroup.centralizer (pCoreOf 2 D.M : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian
      D.standing.charTwo D.maxLocal.1 D.sylowM).1
  have hPMU : pCoreOf 2 D.M ≤ Subgroup.centralizer (D.U : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.1 (hU hu).2 x hx).symm
  exact hPK.trans (hPMU.trans (Subgroup.centralizer_le hV'U))

theorem seventeen_fiftyfive_min_centralizer_inf_eq_pCore {K V' : Subgroup G}
    (hsimple : IsSimpleGroup (Bar2 K))
    (hKVN : K ≤ Subgroup.normalizer (V' : Set G)) (hKV' : ⁅K, V'⁆ ≠ ⊥)
    (hOV : pCoreOf 2 K ≤ Subgroup.centralizer (V' : Set G)) :
    K ⊓ Subgroup.centralizer (V' : Set G) = pCoreOf 2 K := by
  set C : Subgroup G := Subgroup.centralizer (V' : Set G)
  let L : Subgroup ↥K := (K ⊓ C).subgroupOf K
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hKleNC : K ≤ Subgroup.normalizer (C : Set G) :=
    hKVN.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V')
  have hLnormal : L.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (TwelveFifteen.le_normalizer_inf Subgroup.le_normalizer hKleNC)
  have hLbar_normal : (L.map π).Normal := hLnormal.map π (QuotientGroup.mk'_surjective _)
  have hproper : L.map π ≠ ⊤ := by
    intro htop
    have hKle : K ≤ (K ⊓ C) ⊔ pCoreOf 2 K := by
      intro x hx
      have hxbar : π ⟨x, hx⟩ ∈ L.map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hxbar
      have hkKC : (k : G) ∈ K ⊓ C := Subgroup.mem_subgroupOf.1 hk
      have hkx' : (k : ↥K)⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥K := by
        rw [← QuotientGroup.eq_one_iff]
        change π ((k : ↥K)⁻¹ * ⟨x, hx⟩) = 1
        rw [map_mul, map_inv, hkx, inv_mul_cancel]
      have hmem : (((k : ↥K)⁻¹ * ⟨x, hx⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
        rw [CFSG.openPCoreOf_eq_map_pCore]
        exact Subgroup.mem_map_of_mem _ hkx'
      have hsup := ((K ⊓ C) ⊔ pCoreOf 2 K).mul_mem (Subgroup.mem_sup_left hkKC)
        (Subgroup.mem_sup_right hmem)
      rwa [show (k : G) * (((k : ↥K)⁻¹ * ⟨x, hx⟩ : ↥K) : G) = x from by simp] at hsup
    have hKcent : K ≤ C := hKle.trans (sup_le inf_le_right hOV)
    exact hKV' (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKcent)
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hOV)
  rcases hLbar_normal.eq_bot_or_eq_top with hbot | htop
  · intro x hx
    have hxK : x ∈ K := hx.1
    have hxL : (⟨x, hxK⟩ : ↥K) ∈ L := Subgroup.mem_subgroupOf.mpr hx
    have hxbar : π ⟨x, hxK⟩ ∈ L.map π := Subgroup.mem_map_of_mem _ hxL
    rw [hbot, Subgroup.mem_bot] at hxbar
    have hxker : (⟨x, hxK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K)]
      exact MonoidHom.mem_ker.mpr hxbar
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.mem_map_of_mem _ hxker
  · exact absurd htop hproper

theorem seventeen_fiftyfive_min_inf_le_pCore {M K R V' : Subgroup G}
    (hKM : K ≤ M) (hRM : R ≤ M) (hMV : M ≤ Subgroup.normalizer (V' : Set G))
    (hMR : M ≤ Subgroup.normalizer (R : Set G))
    (hCR : M ⊓ Subgroup.centralizer (V' : Set G) ≤ R)
    (hCK : K ⊓ Subgroup.centralizer (V' : Set G) = pCoreOf 2 K)
    (hIdx : ∃ n : ℕ,
      ((Subgroup.centralizer (V' : Set G)).subgroupOf R).index = 2 ^ n) :
    K ⊓ R ≤ pCoreOf 2 K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer (V' : Set G)
  have hRNC : R ≤ Subgroup.normalizer (C : Set G) :=
    (hRM.trans hMV).trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V')
  haveI : (C.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hRNC
  have hpR : pCoreOf 2 K ≤ R := by
    rw [← hCK]
    exact (inf_le_inf_right C hKM).trans hCR
  have hpKR : pCoreOf 2 K ≤ K ⊓ R := le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hpR
  let f : ↥(K ⊓ R) →* ↥R ⧸ C.subgroupOf R :=
    (QuotientGroup.mk' (C.subgroupOf R)).comp
      (Subgroup.inclusion (inf_le_right : K ⊓ R ≤ R))
  obtain ⟨n, hn⟩ := hIdx
  have htarget : IsPGroup 2 (↥R ⧸ C.subgroupOf R) := by
    apply IsPGroup.of_card (n := n)
    rw [← Subgroup.index_eq_card]
    exact hn
  have hkereq : f.ker = C.subgroupOf (K ⊓ R) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ((QuotientGroup.mk ((Subgroup.inclusion (inf_le_right : K ⊓ R ≤ R)) y) :
      ↥R ⧸ C.subgroupOf R) = 1) ↔ (y : G) ∈ C
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hker : IsPGroup 2 f.ker := by
    have hEq : f.ker = (pCoreOf 2 K).subgroupOf (K ⊓ R) := by
      rw [hkereq]
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hxC
        have hxKC : (x : G) ∈ K ⊓ C := ⟨x.2.1, hxC⟩
        rwa [hCK] at hxKC
      · intro hxP
        have hxKC : (x : G) ∈ K ⊓ C := by rw [hCK]; exact hxP
        exact hxKC.2
    rw [hEq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).of_equiv
      (Subgroup.subgroupOfEquivOfLe hpKR).symm
  have hDom : IsPGroup 2 ↥(K ⊓ R) := by
    have htop : IsPGroup 2 (⊤ : Subgroup (↥R ⧸ C.subgroupOf R)) :=
      htarget.of_equiv (Subgroup.topEquiv (G := ↥R ⧸ C.subgroupOf R)).symm
    have hcomap := IsPGroup.comap_of_ker_isPGroup (p := 2) htop f hker
    have heq : (⊤ : Subgroup (↥R ⧸ C.subgroupOf R)).comap f = ⊤ :=
      Subgroup.comap_top f
    rw [heq] at hcomap
    exact hcomap.of_equiv (Subgroup.topEquiv (G := ↥(K ⊓ R)))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (TwelveFifteen.le_normalizer_inf Subgroup.le_normalizer (hKM.trans hMR)) hDom

theorem seventeen_fiftyfive_min_o2Trivial_autI {K V' : Subgroup G} (hV' : IsElemAbelian 2 V')
    (hKVN : K ≤ Subgroup.normalizer (V' : Set G))
    (hCK : K ⊓ Subgroup.centralizer (V' : Set G) = pCoreOf 2 K) :
    O2Trivial (autI hV' K) := by
  intro P hPB hPN hP2
  let f : ↥K →* MulAut (IntMod V' hV') := convHom hV' K hKVN
  have hrange : f.range = autI hV' K := range_convHom hV' K hKVN
  have hPle : P ≤ f.range := by rw [hrange]; exact hPB
  have hkereq : f.ker = (pCoreOf 2 K).subgroupOf K := by
    rw [ker_convHom hV' K hKVN, hCK]
  have hcomap : IsPGroup 2 ↥(P.comap f) := by
    refine IsPGroup.comap_of_ker_isPGroup hP2 f ?_
    rw [hkereq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 K)).symm
  have hnormal : (P.comap f).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn k
    rw [Subgroup.mem_comap] at hn ⊢
    have hfnA : f n ∈ autI hV' K := by
      rw [← hrange]
      exact ⟨n, rfl⟩
    have hfkA : f k ∈ autI hV' K := by
      rw [← hrange]
      exact ⟨k, rfl⟩
    have hconj := hPN.conj_mem ⟨f n, hfnA⟩ hn ⟨f k, hfkA⟩
    simpa [map_mul, map_inv] using (Subgroup.mem_subgroupOf.mp hconj)
  have hN : (⊤ : Subgroup ↥K) ≤
      Subgroup.normalizer ((P.comap f : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hnormal]
  have hHK : P.comap f ≤ pCoreOf 2 (⊤ : Subgroup ↥K) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hN hcomap
  refine le_bot_iff.1 ?_
  intro p hp
  obtain ⟨k, rfl⟩ := hPle hp
  have hkcore : k ∈ CFSG.pCore 2 ↥K := by
    have h := hHK hp
    rwa [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq ↥K] at h
  have hkO : ((k : ↥K) : G) ∈ pCoreOf 2 K := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.mem_map_of_mem _ hkcore
  have hkker : k ∈ f.ker := by
    rw [hkereq]
    exact Subgroup.mem_subgroupOf.mpr hkO
  simpa using MonoidHom.mem_ker.mp hkker

theorem seventeen_fiftyfive_min_twoReduced {D : Data G} {K V' : Subgroup G}
    (hV' : IsElemAbelian 2 V') (hKM : K ≤ D.M) (hKN : D.M ≤ Subgroup.normalizer (K : Set G))
    (hMV : D.M ≤ Subgroup.normalizer (V' : Set G))
    (hV'U : V' ≤ D.U) (hKV' : ⁅K, V'⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ Subgroup.normalizer (W : Set G) → W ≤ V' →
      ⁅K, W⁆ ≠ ⊥ → W = V')
    (hOV : pCoreOf 2 K ≤ Subgroup.centralizer (V' : Set G))
    (hCK : K ⊓ Subgroup.centralizer (V' : Set G) = pCoreOf 2 K) :
    TwoReduced D.M V' := by
  intro R hRM hMR hCR hIdx
  set C : Subgroup G := Subgroup.centralizer (V' : Set G)
  have hKR2 : K ⊓ R ≤ pCoreOf 2 K :=
    seventeen_fiftyfive_min_inf_le_pCore (M := D.M) hKM hRM hMV hMR hCR hCK hIdx
  have hcommKR : ⁅K, R⁆ ≤ K ⊓ R := by
    refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hRM.trans hKN)
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hKM.trans hMR)
  have hcomm : ⁅K, R⁆ ≤ C := hcommKR.trans (hKR2.trans hOV)
  have hRleN : R ≤ Subgroup.normalizer (V' : Set G) := hRM.trans hMV
  have hKleN : K ≤ Subgroup.normalizer (V' : Set G) := hKM.trans hMV
  obtain ⟨k, hkK, hkC⟩ : ∃ k ∈ K, k ∉ C := by
    by_contra h
    push Not at h
    exact hKV' (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  by_contra hRle
  set Vfix : Subgroup G := V' ⊓ Subgroup.centralizer (R : Set G)
  have hVfixU : Vfix ≤ D.U := inf_le_left.trans hV'U
  have hVfixM : D.M ≤ Subgroup.normalizer (Vfix : Set G) := fun m hm =>
    CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMR hm) (hMV hm)
  have hVfix_le : Vfix ≤ V' := inf_le_left
  have hVfix_ne : Vfix ≠ V' := by
    intro h
    apply hRle
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvfix : v ∈ Vfix := by rw [h]; exact hv
    exact ((Subgroup.mem_inf.1 hvfix).2 r hr).symm
  have hKVfix : ⁅K, Vfix⁆ = ⊥ := by
    by_contra hne
    exact hVfix_ne (hmin Vfix hVfixU hVfixM hVfix_le hne)
  have hKFix : K ≤ Subgroup.centralizer (Vfix : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKVfix
  have hB : O2Trivial (autI hV' K) :=
    seventeen_fiftyfive_min_o2Trivial_autI hV' hKleN hCK
  have hAB : ∀ a ∈ autI hV' R, ∀ b ∈ autI hV' K, a * b = b * a :=
    CFSG.Quasithin.H13.autOn_commute (by rwa [Subgroup.commutator_comm] at hcomm)
  have hW2 : IsPGroup 2 (IntMod V' hV') :=
    CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV'
  have hA2 : IsPGroup 2 (autI hV' R) := by
    obtain ⟨n, hn⟩ := hIdx
    apply IsPGroup.of_card (n := n)
    rw [card_autI_eq hV' hRleN]
    have hsub : (R ⊓ C).subgroupOf R = C.subgroupOf R := by
      ext x
      simp [Subgroup.mem_subgroupOf, and_comm]
    rw [show (R ⊓ C).relIndex R = ((R ⊓ C).subgroupOf R).index from rfl, hsub, hn]
  have hkN : (k : G) ∈ Subgroup.normalizer (V' : Set G) := hKleN hkK
  let kN : Subgroup.normalizer (V' : Set G) := ⟨k, hkN⟩
  have hb : convI hV' kN ∈ autI hV' K := convI_mem_autI hV' hkK hkN
  have hfix : ∀ w : IntMod V' hV', (∀ a ∈ autI hV' R, a w = w) → convI hV' kN w = w := by
    intro w hw
    have hwCR : w.val ∈ Subgroup.centralizer (R : Set G) :=
      (mem_fixV_autI hV' hRleN w).1 hw
    have hwVfix : w.val ∈ Vfix := ⟨w.val_mem, hwCR⟩
    refine IntMod.val_injective ?_
    rw [convI_apply_val]
    have hcent := Subgroup.mem_centralizer_iff.1 (hKFix hkK) w.val hwVfix
    rw [← hcent]
    change w.val * k * k⁻¹ = w.val
    group
  have h1 : convI hV' kN = 1 :=
    CFSG.GroupTheory.eq_one_of_forall_fixed_of_commute (p := 2) hW2 hA2 hAB hB hb hfix
  exact hkC ((convI_eq_one_iff hV' kN).1 h1)

theorem seventeen_fiftyfive_min_isIndivisible {D : Data G} {K V' : Subgroup G}
    (hV' : IsElemAbelian 2 V') (hMV : D.M ≤ Subgroup.normalizer (V' : Set G))
    (hV'U : V' ≤ D.U) (hKV' : ⁅K, V'⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ Subgroup.normalizer (W : Set G) → W ≤ V' →
      ⁅K, W⁆ ≠ ⊥ → W = V') :
    IsIndivisible (Mbar D.M (⊥ : Subgroup G) V' hV') := by
  intro U₁ U₂ hU₁ hU₂ hsup
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V' :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have htop : ∀ U : Subgroup (Vtil (⊥ : Subgroup G) V' hV'),
      preTil (⊥ : Subgroup G) V' hV' U = V' → U = ⊤ := by
    intro U hUV
    rw [← imgTil_preTil (⊥ : Subgroup G) V' hV' U, hUV,
      s15_Infra_imgTil_top]
  by_cases h₁ : preTil (⊥ : Subgroup G) V' hV' U₁ = V'
  · exact Or.inl (htop U₁ h₁)
  by_cases h₂ : preTil (⊥ : Subgroup G) V' hV' U₂ = V'
  · exact Or.inr (htop U₂ h₂)
  exfalso
  have hA₁U : preTil (⊥ : Subgroup G) V' hV' U₁ ≤ D.U :=
    (preTil_le (⊥ : Subgroup G) V' hV' U₁).trans hV'U
  have hA₂U : preTil (⊥ : Subgroup G) V' hV' U₂ ≤ D.U :=
    (preTil_le (⊥ : Subgroup G) V' hV' U₂).trans hV'U
  have hA₁M : D.M ≤ Subgroup.normalizer (preTil (⊥ : Subgroup G) V' hV' U₁ : Set G) :=
    TwelveSeventeen.le_normalizer_preTil hV' hMs hU₁
  have hA₂M : D.M ≤ Subgroup.normalizer (preTil (⊥ : Subgroup G) V' hV' U₂ : Set G) :=
    TwelveSeventeen.le_normalizer_preTil hV' hMs hU₂
  have hA₁fix : ⁅K, preTil (⊥ : Subgroup G) V' hV' U₁⁆ = ⊥ := by
    by_contra hne
    exact h₁ (hmin _ hA₁U hA₁M (preTil_le (⊥ : Subgroup G) V' hV' U₁) hne)
  have hA₂fix : ⁅K, preTil (⊥ : Subgroup G) V' hV' U₂⁆ = ⊥ := by
    by_contra hne
    exact h₂ (hmin _ hA₂U hA₂M (preTil_le (⊥ : Subgroup G) V' hV' U₂) hne)
  have hKV1 : K ≤ Subgroup.centralizer (preTil (⊥ : Subgroup G) V' hV' U₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hA₁fix
  have hKV2 : K ≤ Subgroup.centralizer (preTil (⊥ : Subgroup G) V' hV' U₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hA₂fix
  have hsupPre : preTil (⊥ : Subgroup G) V' hV' U₁ ⊔
      preTil (⊥ : Subgroup G) V' hV' U₂ = V' := by
    rw [← TwelveSeventeen.preTil_sup, hsup, preTil_top]
  have hKfix : K ≤ Subgroup.centralizer (V' : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hsupV : (preTil (⊥ : Subgroup G) V' hV' U₁).subgroupOf V' ⊔
        (preTil (⊥ : Subgroup G) V' hV' U₂).subgroupOf V' = ⊤ := by
      apply Subgroup.map_injective V'.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le
          (preTil_le (⊥ : Subgroup G) V' hV' U₁), Subgroup.map_subgroupOf_eq_of_le
          (preTil_le (⊥ : Subgroup G) V' hV' U₂), hsupPre, Subgroup.map_top,
        Subgroup.range_subtype]
    letI : CommGroup ↥V' := CommGroup.mk (fun a b => hV'.1.is_comm.comm a b)
    have hvsup' : (⟨v, hv⟩ : ↥V') ∈ (preTil (⊥ : Subgroup G) V' hV' U₁).subgroupOf V' ⊔
        (preTil (⊥ : Subgroup G) V' hV' U₂).subgroupOf V' := by
      rw [hsupV]
      exact Subgroup.mem_top _
    obtain ⟨a, b, hab⟩ := (Subgroup.mem_sup'
      (s := (preTil (⊥ : Subgroup G) V' hV' U₁).subgroupOf V')
      (t := (preTil (⊥ : Subgroup G) V' hV' U₂).subgroupOf V')).1 hvsup'
    have ha : ((a : ↥V') : G) ∈ preTil (⊥ : Subgroup G) V' hV' U₁ := a.2
    have hb : ((b : ↥V') : G) ∈ preTil (⊥ : Subgroup G) V' hV' U₂ := b.2
    have habG : ((a : ↥V') : G) * ((b : ↥V') : G) = v := by
      have := congrArg Subtype.val hab
      simpa using this
    have hka : ((a : ↥V') : G) * k = k * ((a : ↥V') : G) :=
      Subgroup.mem_centralizer_iff.1 (hKV1 hk) _ ha
    have hkb : ((b : ↥V') : G) * k = k * ((b : ↥V') : G) :=
      Subgroup.mem_centralizer_iff.1 (hKV2 hk) _ hb
    rw [← habG]
    calc ((a : ↥V') : G) * ((b : ↥V') : G) * k
        = ((a : ↥V') : G) * (((b : ↥V') : G) * k) := by group
      _ = ((a : ↥V') : G) * (k * ((b : ↥V') : G)) := by rw [hkb]
      _ = (((a : ↥V') : G) * k) * ((b : ↥V') : G) := by group
      _ = (k * ((a : ↥V') : G)) * ((b : ↥V') : G) := by rw [hka]
      _ = k * (((a : ↥V') : G) * ((b : ↥V') : G)) := by group
  exact hKV' (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKfix)

theorem seventeen_fiftyfive_min_eq_top_of_faithful {D : Data G} {K V' : Subgroup G}
    (hV' : IsElemAbelian 2 V') (hKM : K ≤ D.M)
    (hMV : D.M ≤ Subgroup.normalizer (V' : Set G))
    (hV'U : V' ≤ D.U) (hKV' : ⁅K, V'⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ Subgroup.normalizer (W : Set G) → W ≤ V' →
      ⁅K, W⁆ ≠ ⊥ → W = V')
    {U : Subgroup (Vtil (⊥ : Subgroup G) V' hV')}
    (hU : StableUnder (Mbar D.M (⊥ : Subgroup G) V' hV') U)
    (hf : ∀ y ∈ Mbar D.M (⊥ : Subgroup G) V' hV', (∀ u ∈ U, y u = u) → y = 1) :
    U = ⊤ := by
  by_contra hUtop
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V' :=
    le_stabTil hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  set A : Subgroup G := preTil (⊥ : Subgroup G) V' hV' U with hAdef
  have hA_le : A ≤ V' := preTil_le (⊥ : Subgroup G) V' hV' U
  have hAU : A ≤ D.U := hA_le.trans hV'U
  have hAM : D.M ≤ Subgroup.normalizer (A : Set G) :=
    TwelveSeventeen.le_normalizer_preTil hV' hMs hU
  have hAne : A ≠ V' := by
    intro h
    apply hUtop
    have hpre : preTil (⊥ : Subgroup G) V' hV' U = V' := by
      rw [← hAdef]
      exact h
    rw [← imgTil_preTil (⊥ : Subgroup G) V' hV' U, hpre, s15_Infra_imgTil_top]
  have hAfix : ⁅K, A⁆ = ⊥ := by
    by_contra hne
    exact hAne (hmin A hAU hAM hA_le hne)
  have hKA : K ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAfix
  obtain ⟨k, hkK, hkC⟩ : ∃ k ∈ K, k ∉ Subgroup.centralizer (V' : Set G) := by
    by_contra h
    push Not at h
    exact hKV' (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  let y : MulAut (Vtil (⊥ : Subgroup G) V' hV') := actTil (⊥ : Subgroup G) V' hV' ⟨k, hMs (hKM hkK)⟩
  have hy : y ∈ Mbar D.M (⊥ : Subgroup G) V' hV' :=
    barSub_mono (⊥ : Subgroup G) V' hV' hKM
      (actTil_mem_barSub (⊥ : Subgroup G) V' hV' hkK (hMs (hKM hkK)))
  have hyfix : ∀ u ∈ U, y u = u := by
    intro u hu
    rw [← imgTil_preTil (⊥ : Subgroup G) V' hV' U] at hu
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) V' hV' A u).1 hu
    change actTil (⊥ : Subgroup G) V' hV' ⟨k, hMs (hKM hkK)⟩ (mkTil (⊥ : Subgroup G) V' hV' x) =
      mkTil (⊥ : Subgroup G) V' hV' x
    rw [actTil_mk]
    apply congrArg (mkTil (⊥ : Subgroup G) V' hV')
    apply IntMod.val_injective
    rw [actStab_apply_val]
    have hcent := Subgroup.mem_centralizer_iff.1 (hKA hkK) x.val hx
    rw [← hcent]
    change x.val * k * k⁻¹ = x.val
    group
  have hy1 : y = 1 := hf y hy hyfix
  apply hkC
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h := (actTil_eq_one_iff (⊥ : Subgroup G) V' hV' ⟨k, hMs (hKM hkK)⟩).1
    (by simpa [y] using hy1) v hv
  rw [Subgroup.mem_bot] at h
  have h1 : k * v * k⁻¹ = v := mul_inv_eq_one.mp h
  have h2 : k * v = v * k := by
    calc k * v = (k * v * k⁻¹) * k := by group
      _ = v * k := by rw [h1]
  exact h2.symm

theorem seventeen_fiftyfive_min_isBasicModule {D : Data G} {K V' : Subgroup G}
    (hV' : IsElemAbelian 2 V') (hKM : K ≤ D.M)
    (hMV : D.M ≤ Subgroup.normalizer (V' : Set G))
    (hV'U : V' ≤ D.U) (hKV' : ⁅K, V'⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ Subgroup.normalizer (W : Set G) → W ≤ V' →
      ⁅K, W⁆ ≠ ⊥ → W = V') :
    IsBasicModule (Mbar D.M (⊥ : Subgroup G) V' hV') :=
  ⟨seventeen_fiftyfive_min_isIndivisible hV' hMV hV'U hKV' hmin,
    fun _ hU hf => seventeen_fiftyfive_min_eq_top_of_faithful hV' hKM hMV hV'U hKV' hmin hU hf⟩

theorem exists_inCalW_min_commutator {D : Data G} (h127 : R127 D)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKN : D.M ≤ Subgroup.normalizer (K : Set G))
    (hsimple : IsSimpleGroup (Bar2 K)) (hUT : UniqueMax D.M (K ⊔ D.T))
    (hKZ : ⁅K, D.Z⁆ ≠ ⊥) :
    ∃ V' : Subgroup G, V' ≤ D.U ∧ V' ≠ ⊥ ∧ InCalW D.M D.T V' ∧
      ¬ CFSG.CGT.Timmesfeld75.IsTI V' ∧ ⁅K, V'⁆ = V' ∧
      pCoreOf 2 K ≤ Subgroup.centralizer (V' : Set G) ∧
      ∃ hV' : IsElemAbelian 2 V',
        IsBasicModule (Mbar D.M (⊥ : Subgroup G) V' hV') ∧
          O2Trivial (Mbar D.M (⊥ : Subgroup G) V' hV') := by
  obtain ⟨V', hV'U, hMV, hKV', hmin⟩ := seventeen_fiftyfive_min_base hKZ
  have hKM : K ≤ D.M := hK.1.le
  have hV'M : V' ≤ D.M := hV'U.trans (uc22p22e_uCore_le D.sylowM.le)
  have hV'el : IsElemAbelian 2 V' :=
    uc22p22n_isElemAbelian_of_le hV'U (uc22p22e_inCalV_U D).2.2.2
  have hV'ne : V' ≠ ⊥ := by
    intro h
    exact hKV' (by rw [h, Subgroup.commutator_bot_right])
  have h8 : 8 ≤ Nat.card V' := by
    by_contra hlt
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV'el)
    have h4 : Nat.card V' ≤ 4 := by
      rw [hn] at hlt ⊢
      have h2 : n ≤ 2 := by
        by_contra h
        have h3 : 3 ≤ n := by omega
        have h4 := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
        omega
      exact Nat.pow_le_pow_right (by norm_num) h2
    have hcent := CFSG.SeitzReduction.LinearPilot.le_centralizer_of_perfect_of_card_le_four
      hK.2.1 (hKM.trans hMV) h4
    exact hKV' (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent)
  have hV'inCalV : InCalV D.M V' := ⟨hV'ne, hV'M, hMV, hV'el⟩
  have hV'inCalV1 : InCalV1 D.M D.T V' :=
    inCalV1_of_commutator_ne_bot hV'inCalV hK hKN hUT hKV'
  have hOV : pCoreOf 2 K ≤ Subgroup.centralizer (V' : Set G) :=
    seventeen_fiftyfive_min_pCore_le_centralizer hK hV'U
  have hCK : K ⊓ Subgroup.centralizer (V' : Set G) = pCoreOf 2 K :=
    seventeen_fiftyfive_min_centralizer_inf_eq_pCore hsimple (hKM.trans hMV) hKV' hOV
  have hKVeq : ⁅K, V'⁆ = V' :=
    seventeen_fiftyfive_min_commutator_eq hK hV'U hKN hMV hKV' hmin
  have hTwo : TwoReduced D.M V' :=
    seventeen_fiftyfive_min_twoReduced hV'el hKM hKN hMV hV'U hKV' hmin hOV hCK
  have hW : InCalW D.M D.T V' := ⟨hV'inCalV1, h8, hTwo⟩
  have hnotTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V' := by
    intro hTI
    exact (h127 h124 V' hV'inCalV hTI h8).1 hV'inCalV1
  have hBasic : IsBasicModule (Mbar D.M (⊥ : Subgroup G) V' hV'el) :=
    seventeen_fiftyfive_min_isBasicModule hV'el hKM hMV hV'U hKV' hmin
  have hO2 : O2Trivial (Mbar D.M (⊥ : Subgroup G) V' hV'el) :=
    o2Trivial_mbar_of_twoReduced hV'el hMV hTwo
  exact ⟨V', hV'U, hV'ne, hW, hnotTI, hKVeq, hOV, hV'el, hBasic, hO2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
