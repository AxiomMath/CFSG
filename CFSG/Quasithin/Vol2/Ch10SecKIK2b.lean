module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2a
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.EmptyFaithful.SBc3List
public import CFSG.Quasithin.EmptyFaithful.T1515dA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Offender

variable {S L Y W : Subgroup G} [IsMulCommutative ↥W]

theorem exists_offender_of_thompsonJ (hWe : IsElemAbelian 2 W) (hred : IsTwoReducedIn Y W)
    (hSY : IsSylowTwoOf S Y) (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (h2 : ∀ y ∈ Y, ∃ e : ℕ, y ^ 2 ^ e ∈ L) (hq : CFSG.IsQuasisimple ↥(autOn L W))
    (hJS : ¬ thompsonJ S ≤ Subgroup.centralizer (W : Set G)) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W := by
  have hTN : S ≤ Subgroup.normalizer (L : Set G) := hSY.1.trans hYL
  have hTW : S ≤ Subgroup.normalizer (W : Set G) := hSY.1.trans hred.2.1
  have hnorm : ∀ A : Subgroup G, A ≤ S →
      autOn A W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := by
    intro A hAT x hx
    have hc := InternalSec.autOn_normal_of (U := W) (hAT.trans hTN)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A W).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ⁅autOn L W, autOn A W⁆ = autOn L W
  · obtain ⟨A, hA, hLA⟩ := hex
    have hAC : ¬ A ≤ Subgroup.centralizer (W : Set G) := by
      intro hAC
      have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, Subgroup.commutator_bot_right] at hLA
      refine not_commute_of_isQuasisimple1527d hq fun a ha b hb => ?_
      rw [← hLA, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hSY hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe hred.1 hred.2.1 ⟨A, hoff, rfl⟩, hLA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian S A →
        autOn A W ≤ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) := by
      intro A hA
      rcases commutator_eq_or_eq_bot1527d hq (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (Subgroup.mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S' : Subgroup G :=
      ((Subgroup.centralizer (autOn L W : Set (MulAut ↥W))).comap (conjAct W)).map
        (Subgroup.normalizer (W : Set G)).subtype with hS'
    have hJS' : thompsonJ S ≤ S' := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ Subgroup.normalizer (W : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    have hJSS : thompsonJ S ≤ S := iSup₂_le fun _ hA => hA.1
    apply hJS
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hJS' hx
    have hgS : (g : G) ∈ S := hJSS hx
    obtain ⟨k, hk⟩ := hSY.2.1 ⟨g, hgS⟩
    have hk' : (g : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact (convI_eq_one_iff hWe g).1
      (convI_eq_one_of_two_pow hWe hred hYL h2 (hSY.1 hgS) hk' hg)

end Offender

theorem b56List_autI (h56 : AsB56) {H R J V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hSQH : SQTKGroup ↥H) (hRsyl : IsSylowTwoOf R H) (hred : IsTwoReducedIn H V) (hJH : J ≤ H)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J)
    (hJq : CFSG.IsQuasisimple ↥(autI hV J))
    (hJR : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)) :
    B56QuasisimpleList ↥(autI hV J) := by
  have : IsMulCommutative ↥V := hV.1
  obtain ⟨A, -, hA, hLA⟩ := exists_offender_of_thompsonJ hV hred hRsyl hHJ h2 hJq hJR
  have hW2 : ∀ w ∈ V, w ^ 2 = 1 := fun w hw => by simpa [pow_two] using hV.2 w hw
  have hO2 : pCoreOf 2 (autOn H V) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  obtain ⟨hKJ, hn, -, -, hcases⟩ :=
    InternalSec.b56Cases_ffJ_autOn h56 hW2 hred.2.1 hJH hHJ hSQH hO2 hA hLA
  have hsn : IsSubnormal (autOn J V) (ffJ (autOn H V)) :=
    A3.subnormal_of_normal hKJ
      ((Subgroup.normal_subgroupOf_iff hKJ).2 fun k j hk hj => hn j hj k hk)
  exact SBc3.b56QL_of_subnormal hKJ hsn hJq hcases

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
