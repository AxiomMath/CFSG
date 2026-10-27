module

import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofSubn

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155B1

theorem le_normalizer_x {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    A ≤ Subgroup.normalizer (X : Set G) :=
  hC.res ▸ Sec14.le_normalizer_oPrimeResidualOf hC.isY.1.1.1.2

theorem le_normalizer_r {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
  hC.isY.1.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)

theorem x_le_delta {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    X ≤ delta A (lB A) M := by
  have hXY : X ≤ Y := hC.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hYM : Y ≤ M := fun y hy => hC.mem_m.2 (Subgroup.mem_sup_right hy)
  rw [hC.isY.1.2] at hXY
  exact hXY.trans (delta_mono hYM)

theorem le_normalizer_u155 {A M X H : Subgroup G}
    (hHI : H ≤ Subgroup.normalizer (delta A (lB A) M : Set G))
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer (u155 A M X : Set G) :=
  Late.le_normalizer_inf hHI (Proof155w2.le_normalizer_centralizerSection hHX
    (hHX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)))

theorem u155_le {A M X : Subgroup G} :
    u155 A M X ≤ M ⊓ Subgroup.normalizer (X : Set G) :=
  le_inf (inf_le_left.trans (delta_le M)) (inf_le_right.trans fun _ hc => hc.1)

theorem le_r_of_normalized {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) {X K Y M T P V : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hV : V ∈ scriptQ A (lB A)) (hVM : V ≤ M) (hV2 : IsPGroup 2 V)
    (hIV : delta A (lB A) M ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP𝓠 : P ∈ scriptQ A (lB A) := hE.mem_p.prop.1.1
  have hPM : P ≤ M ⊓ Subgroup.normalizer (X : Set G) := hE.mem_p.prop.1.2
  have hPI : P ≤ delta A (lB A) M := le_delta hP𝓠 (hPM.trans inf_le_left)
  have hVI : V ≤ delta A (lB A) M := le_delta hV hVM
  have hVpi : V ∈ scriptQPi A (lB A) (M ⊓ Subgroup.normalizer (X : Set G)) (piOf 2) :=
    ⟨⟨hV, le_inf hVM (hVI.trans hIX)⟩, (isPiSubgroup_piOf_iff Nat.prime_two V).mpr hV2⟩
  have hPV := sup_mem_scriptQPi_of_item146 h.isE27 h146 hE.mem_p.prop hVpi (hPI.trans hIV)
  have hVP : V ≤ P := le_sup_right.trans (hE.mem_p.eq_of_le hPV le_sup_left).symm.le
  rw [hE.eq_rq]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) (hVP.trans le_sup_left)
    (sup_le (hPI.trans hIV) ((x_le_delta hC).trans hIV)) hV2

theorem pCore_mem_invariant {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    CFSG.Open.pCoreOf 2 M ∈ invariantPiSubgroups ⊤ A (piCompl 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  refine ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr fun h3 => ?_,
    hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  rw [hn] at h3
  have h32 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h32

theorem delta_pCore_facts {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    delta A (lB A) (CFSG.Open.pCoreOf 2 M) ∈ scriptQ A (lB A) ∧
      delta A (lB A) M ≤
        Subgroup.normalizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) :=
  ⟨delta_mem_scriptQ h.isE27 h146 (pCore_mem_invariant hC),
    delta_le_normalizer_delta (fun _ hZ => delta_mem_scriptQ h.isE27 h146 hZ)
      (pCore_mem_invariant hC) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)⟩

theorem delta_pCore_le_r {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) :
    delta A (lB A) (CFSG.Open.pCoreOf 2 M) ≤ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, hIZ⟩ := delta_pCore_facts h h146 hC
  exact le_r_of_normalized h h146 hC hE hIX hZ
    ((delta_le _).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (delta_le _)) hIZ

end Sylow155B1

end CFSG.RankThree.PartTwo.Sec15
