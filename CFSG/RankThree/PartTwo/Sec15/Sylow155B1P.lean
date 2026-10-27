module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155B1
import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Sylow
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Frattini

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155B1

theorem delta_host_facts {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) {X K Y M T P H : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hHinv : H ∈ invariantPiSubgroups ⊤ A (piCompl 3)) (hHU : H ≤ u155 A M X)
    (hPH : P ≤ Subgroup.normalizer (H : Set G)) (hRH : CFSG.Open.pCoreOf 2 Y ≤ H) :
    delta A (lB A) H ∈ scriptQ A (lB A) ∧
      CFSG.Open.pCoreOf 2 Y ≤ delta A (lB A) H ∧
      P ≤ Subgroup.normalizer (delta A (lB A) H : Set G) ∧
      CFSG.Open.fusionIsSylowIn 2 (CFSG.Open.pCoreOf 2 Y) (delta A (lB A) H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDH : delta A (lB A) H ∈ scriptQ A (lB A) := delta_mem_scriptQ h.isE27 h146 hHinv
  have hP𝓠 : P ∈ scriptQ A (lB A) := hE.mem_p.prop.1.1
  have hPDH : P ≤ Subgroup.normalizer (delta A (lB A) H : Set G) :=
    (le_delta hP𝓠 le_rfl).trans (delta_le_normalizer_delta
      (fun _ hZ => delta_mem_scriptQ h.isE27 h146 hZ) hHinv hPH)
  have hR𝓠 : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hP𝓠 hRP (le_normalizer_r hC)
  have hRDH : CFSG.Open.pCoreOf 2 Y ≤ delta A (lB A) H := le_delta hR𝓠 hRH
  obtain ⟨-, -, hPsyl⟩ :=
    Sylow155F.sylow_sup h h146 hE hDH ((delta_le _).trans (hHU.trans u155_le)) hPDH
  have hsyl := CFSG.LocalAnalysis.EvenBN.Tits.N.P6.fusionIsSylowIn_inf_of_normal hPsyl
    (le_sup_right : delta A (lB A) H ≤ P ⊔ delta A (lB A) H)
    (sup_le hPDH Subgroup.le_normalizer)
  have hinf : P ⊓ delta A (lB A) H = CFSG.Open.pCoreOf 2 Y := by
    refine le_antisymm ?_ (le_inf hRP hRDH)
    rw [← Sylow155F.inf_u155_eq hE hRP]
    exact inf_le_inf_left P ((delta_le _).trans hHU)
  rw [hinf] at hsyl
  exact ⟨hDH, hRDH, hPDH, hsyl⟩

theorem p_le_normalizer_of_host {A X K Y M T P H : Subgroup G} (hE : End155N A X K Y M T P)
    (hHN : Subgroup.normalizer (u155 A M X : Set G) ≤ Subgroup.normalizer (H : Set G)) :
    P ≤ Subgroup.normalizer (H : Set G) := by
  have hP𝓠 : P ∈ scriptQ A (lB A) := hE.mem_p.prop.1.1
  have hPM : P ≤ M ⊓ Subgroup.normalizer (X : Set G) := hE.mem_p.prop.1.2
  have hPI : P ≤ delta A (lB A) M := le_delta hP𝓠 (hPM.trans inf_le_left)
  exact (le_normalizer_u155 (hPI.trans Subgroup.le_normalizer) (hPM.trans inf_le_right)).trans hHN

theorem le_n155_of_le_normalizer_host {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) {X K Y M T P H : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hHinv : H ∈ invariantPiSubgroups ⊤ A (piCompl 3)) (hHU : H ≤ u155 A M X)
    (hPH : P ≤ Subgroup.normalizer (H : Set G)) (hRH : CFSG.Open.pCoreOf 2 Y ≤ H)
    (hH : delta A (lB A) H ≤ n155 A K) {V : Subgroup G} (hV : V ∈ scriptQ A (lB A))
    (hVH : V ≤ Subgroup.normalizer (H : Set G)) : V ≤ n155 A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDH, -, -, hsyl⟩ := delta_host_facts h h146 hC hE hRP hHinv hHU hPH hRH
  have hVDH : V ≤ Subgroup.normalizer (delta A (lB A) H : Set G) :=
    (le_delta hV le_rfl).trans (delta_le_normalizer_delta
      (fun _ hZ => delta_mem_scriptQ h.isE27 h146 hZ) hHinv hVH)
  have hH𝓠 : V ⊔ delta A (lB A) H ∈ scriptQ A (lB A) :=
    sup_mem_scriptQ_of_item146 h.isE27 h146 hV hDH hVDH
  have hfr := Sylow155F.le_sup_inf_normalizer hsyl
    (le_sup_right : delta A (lB A) H ≤ V ⊔ delta A (lB A) H)
    (sup_le hVDH Subgroup.le_normalizer)
  have hN𝓠 : (V ⊔ delta A (lB A) H) ⊓
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hH𝓠 inf_le_left
      (Late.le_normalizer_inf hH𝓠.1.2.2 ((le_normalizer_r hC).trans Subgroup.le_normalizer))
  have hNn := Sylow155F.le_n155_of_le_normalizer hC hE hN𝓠 inf_le_right
  exact le_sup_left.trans (hfr.trans (sup_le hH hNn))

theorem delta_le_n155_of_delta_host_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) {X K Y M T P H : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hHinv : H ∈ invariantPiSubgroups ⊤ A (piCompl 3)) (hHU : H ≤ u155 A M X)
    (hHN : Subgroup.normalizer (u155 A M X : Set G) ≤ Subgroup.normalizer (H : Set G))
    (hRH : CFSG.Open.pCoreOf 2 Y ≤ H)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hH : delta A (lB A) H ≤ n155 A K) : delta A (lB A) M ≤ n155 A K := by
  refine sSup_le fun V hV => ?_
  have hVI : V ≤ delta A (lB A) M := le_delta hV.1 hV.2
  have hVH : V ≤ Subgroup.normalizer (H : Set G) :=
    (le_normalizer_u155 (hVI.trans Subgroup.le_normalizer) (hVI.trans hIX)).trans hHN
  exact le_n155_of_le_normalizer_host h h146 hC hE hRP hHinv hHU (p_le_normalizer_of_host hE hHN)
    hRH hH hV.1 hVH

theorem pPrimeCoreOf_u155_mem_invariant {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    pPrimeCoreOf 3 (u155 A M X) ∈ invariantPiSubgroups ⊤ A (piCompl 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)),
    (le_normalizer_u155 (le_normalizer_delta M) (le_normalizer_x hC)).trans
      (normalizer_le_normalizer_pPrimeCoreOf 3 _)⟩

end Sylow155B1

end CFSG.RankThree.PartTwo.Sec15
