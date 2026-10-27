module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TLeN
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1L112
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T134
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step155HostE0WRes1TypeFBarLe_of_zExclPt (hbot : Item145BotS14)
    (h1444 : Item1444S14) (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hΩc : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      omegaA A = {Subgroup.zpowers c} ∧
        ∀ Y ∈ scriptY4 A (lB A), Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y)
    (hΔ : Res1DeltaQ Q) (hz : Res1ZExclLe Q P) :
    Step155HostE0WRes1TypeFBarLe Q P := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX
  by_contra hE0N
  have hLΔ := hΔ G A c L hR hq hN
  obtain ⟨hΩ, hcov⟩ := hΩc G A c L hR hq hN
  have hK4 : K ∈ scriptY4 A (lB A) := (scriptY0Star_subset A (lB A) hC.mem_k).1
  have hKc := hcov K hK4
  have hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K :=
    le_antisymm (hKc.le.trans (sup_le_sup_right (inf_le_left.trans hLX) _))
      (sup_le hC.le_k (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  obtain ⟨z, hz2, hzV, hzC, hzR, hAz, hKz, hCN, hJ⟩ :=
    exists_involution_of_not_le hR hbot (h1444 G A c L hS) h146 (h149 G A c L hS)
      (h153 G A c L hR hq) hC hmax habove hE hRP hIX hEA hKX hE0N
  exact hz G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX hLΔ hKX hΩ hE0N z hz2 hzV hzC hzR hAz hKz hCN hJ


theorem res1OmegaCover_a7 (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      omegaA A = {Subgroup.zpowers c} ∧
        ∀ Y ∈ scriptY4 A (lB A), Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := by
  intro G _ _ A c L hR h7 hN
  have hΩ := omegaA_eq_singleton_of_a7_m22 h131 h133 hset hR (Or.inr h7) hN
  exact ⟨hΩ, fun _ hY =>
    eq_inf_sup_pCoreOf_two_of_mem_scriptY4_of_a7 h148 hbot h142 h131 hR h7 hΩ hY⟩

theorem res1OmegaCover_m22 (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      omegaA A = {Subgroup.zpowers c} ∧
        ∀ Y ∈ scriptY4 A (lB A), Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := by
  intro G _ _ A c L hR h22 hN
  have hΩ := omegaA_eq_singleton_of_a7_m22 h131 h133 hset hR (Or.inl h22) hN
  exact ⟨hΩ, fun _ hY =>
    eq_inf_sup_pCoreOf_two_of_mem_scriptY4_of_m22 h148 hbot h142 hR h22 hΩ hY⟩

theorem step155HostE0WRes1TypeFBarLe_a7_of_zExclNPt (h131 : Item131) (h133 : Item133)
    (hset : Item13SetupAt) (h148 : Item148R) (hbot : Item145BotS14) (h142R : Item142R)
    (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (h142 : Concl142S14)
    {P : ∀ (Y : Type) [Group Y], Prop}
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      Item153Main A (lB A))
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P) :
    Step155HostE0WRes1TypeFBarLe (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P :=
  step155HostE0WRes1TypeFBarLe_of_zExclPt hbot h1444 h149 h153
    (res1OmegaCover_a7 h131 h133 hset h148 hbot h142R) (res1DeltaQ_a7 h142)
    (res1ZExclLe_a7_of_N h149 hz)

theorem step155HostE0WRes1TypeFBarLe_m22_of_zExclNPt
    (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt) (h148 : Item148R)
    (hbot : Item145BotS14) (h142R : Item142R) (h1444 : Item1444S14) (h149 : Sec16.Item149S14)
    (h142 : Concl142S14) (h22 : Step142LowerGenM22) {P : ∀ (Y : Type) [Group Y], Prop}
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
      Item153Main A (lB A))
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P) :
    Step155HostE0WRes1TypeFBarLe (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      P :=
  step155HostE0WRes1TypeFBarLe_of_zExclPt hbot h1444 h149 h153
    (res1OmegaCover_m22 h131 h133 hset h148 hbot h142R) (res1DeltaQ_m22 h22 h142)
    (res1ZExclLe_m22_of_N h149 hz)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
