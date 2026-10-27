module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1PtL3
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T134
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TKX
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofNoSz
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TLeN
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem res1L3Q_of_card_nine {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Res1L3Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have hD := hR.toSec13Data
  have hq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_lA.1
  refine ⟨hL3, Sec16.Steps166.isSimpleGroup_of_isLThreePi hq hL3, ?_⟩
  let π : ↥L →* (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)
  let S : Subgroup ↥L := (A ⊓ L).subgroupOf L
  refine ⟨S.map π, ?_, ?_⟩
  · have hAe : CFSG.Open.IsElemAbelian 3 (A ⊓ L) := hD.isElemAbelian.mono inf_le_left
    exact (hAe.subgroupOf L).map π
  · have hP3 : IsPGroup 3 S := (hD.isElemAbelian.mono inf_le_left).isPGroup.comap_subtype
    have hinj : Set.InjOn π (S : Set ↥L) :=
      CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hP3
    rw [CFSG.RankThreeEvenClassification.Helpers.card_map_eq_of_injOn π S hinj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans h9

private theorem item1511_l3_at_K {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (h1511 : Item1511R) {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hL4 : L ∈ scriptY4 A (lB A)) (hK0 : K ∈ scriptY0 A (lB A)) (hLX : L ≤ X) :
    Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      K = (L ⊓ K) ⊔ CFSG.Open.pCoreOf 2 K := by
  obtain ⟨p, e, hp, he, hiso⟩ := hL3
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hK0.1.1.2
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hR.toSec13Data.A_le_normalizer_zpowers
  obtain ⟨P, hAP, hP⟩ := Proof1513Steps.exists_sylow_normalizer_inf
    (Proof1513Steps.isPGroup_of_sec13Data hR.toSec13Data) hAc hAK
  have hmeet : MeetsY4 A (lB A) L K :=
    ⟨L, hL4, le_inf le_rfl (hLX.trans hC.le_k)⟩
  obtain ⟨hprod, -, hcover, -, -⟩ :=
    h1511 G A c L hR p e he hiso K hK0 hmeet P hAP hP
  exact ⟨hprod, hcover⟩

theorem step155HostE0WRes1TypeFBarLe_l3_of_zExcl
    (h135 : Item135) (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14)
    (h142 : Concl142S14) (hL3g : Step142LowerGenL3) (h1511 : Item1511R)
    (hΩ : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (scriptY0 A (lB A)).Nonempty → omegaA A = {Subgroup.zpowers c})
    (hL34 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → (scriptY0 A (lB A)).Nonempty →
      ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    {P : ∀ (Y : Type) [Group Y], Prop} (hz : Sylow155R1.Res1ZExclLeN Res1L3Q P) :
    Step155HostE0WRes1TypeFBarLe (fun X _ => IsLThreePi X) P := by
  intro G _ _ A c L hR hL3 hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX
  by_contra hE0N
  have hY0 : (scriptY0 A (lB A)).Nonempty :=
    ⟨K, scriptY0Star_subset A (lB A) hC.mem_k⟩
  have h34 : ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := hL34 G A c L hR hY0
  have hLΔ : L ≤ delta A (lB A) L :=
    Sylow155R1.le_delta_of_lThreePi hL3g hR (h142 G A c L hS) hL3 h34
  have hL4 : L ∈ scriptY4 A (lB A) :=
    Sylow155R1.mem_scriptY4_of_le_delta h135 hR hLΔ
  have hK0 : K ∈ scriptY0 A (lB A) := scriptY0Star_subset A (lB A) hC.mem_k
  obtain ⟨hprod, hcover⟩ := item1511_l3_at_K hR hL3 h1511 hC hL4 hK0 hLX
  have hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K :=
    le_antisymm (hcover.le.trans (sup_le_sup_right (inf_le_left.trans hLX) _))
      (sup_le hC.le_k (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    Sec13.card_inf_eq_nine hR.toSec13Data (Sec13.isPerfect_lBar hR.toSec13Data) hprod.some
  have hcL : c ∉ L := hR.hypS.2.2 c hR.zpowers_mem_omegaA L hR.mem_lA
  have hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) := fun hPGL =>
    Proof1511.false_of_card_nine_of_isZ3PGLThreePi hR.toSec13Data hcL h9 hPGL
  have hΩ' : omegaA A = {Subgroup.zpowers c} := hΩ G A c L hR hL3 hnPGL hN hY0
  have hQ3 : Res1L3Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    res1L3Q_of_card_nine hR hL3 h9
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    center_eq_bot_of_types hR.toSec13Data.mem_lA.1
      (hR.chosen136.2 c hR.zpowers_mem_omegaA L hR.mem_lA).1
  have hE9 : ∃ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
      (∀ e ∈ E, e ^ 3 = 1) ∧ Nat.card E = 9 := by
    obtain ⟨E, hEe, hEcard⟩ := hQ3.2.2
    exact ⟨E, hEe.2, hEcard⟩
  obtain ⟨hMX, hMO⟩ :=
    Sylow155R1.eq_normalizer_x_of_le_of_center hS (h149 G A c L hS) hC hE hIX hLX hZ hE9
  obtain ⟨z, hz2, hzV, hzC, hzR, hAz, hKz, hCN, hJ⟩ :=
    Sylow155R1.exists_involution_of_not_le hR hbot (h1444 G A c L hS) h146
      (h149 G A c L hS) (h153 G A c L hR hL3) hC hmax habove hE hRP hIX hEA hKX hE0N
  exact hz G A c L hR hQ3 hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX hLΔ hKX hΩ' hMX hMO hE0N z hz2 hzV hzC hzR hAz hKz hCN hJ

theorem step155HostE0WRes1TypeFPt_l3_of_zExcl_of_in
    (h135 : Item135) (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14)
    (h142 : Concl142S14) (hL3g : Step142LowerGenL3) (h1511 : Item1511R)
    (hΩ : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (scriptY0 A (lB A)).Nonempty → omegaA A = {Subgroup.zpowers c})
    (hL34 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → (scriptY0 A (lB A)).Nonempty →
      ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    {P : ∀ (Y : Type) [Group Y], Prop} (hz : Sylow155R1.Res1ZExclLeN Res1L3Q P)
    (hin : Sylow155R1.Res1L112InPt Res1L3Pt P) :
    Step155HostE0WRes1TypeFPt Res1L3Pt P :=
  Sylow155R1.step155HostE0WRes1TypeFPt_of_le_of_in h149 (fun _ _ _ _ _ _ hPt => hPt.1)
    (step155HostE0WRes1TypeFBarLe_l3_of_zExcl h135 hbot h1444 h149 h142 hL3g h1511 hΩ hL34 h153
      hz) hin

end CFSG.RankThree.PartTwo.Sec15.GagenL3
