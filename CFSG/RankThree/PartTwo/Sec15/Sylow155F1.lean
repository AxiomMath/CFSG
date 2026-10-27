module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155StepDefs
import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Z
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofON
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step155F1ZeroW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
      ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
        g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
          Odd (orderOf g) → g = 1

namespace Sylow155F1

theorem eq_one_of_mem_centralizer_pCoreOf {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) {g : G}
    (hgM : g ∈ M) (hgV : g ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G))
    (hg : Odd (orderOf g)) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hC.mem_m.1, fun z hz => hC.mem_m.2 (by rwa [sup_comm] at hz)⟩
  obtain ⟨-, -, -, hF⟩ := facts_of_mem_maximalTwoLocalsContaining h hMY
  have hMchar : M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤
      CFSG.Open.pCoreOf 2 M :=
    CFSG.RankThree.GF2n.Tim78.inf_centralizer_le_of_generalizedFitting_eq hF
  have hV2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  obtain ⟨k, hk⟩ := hV2 ⟨g, hMchar ⟨hgM, hgV⟩⟩
  have hgk : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hgk)
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · rw [hj] at hg
    exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩) (Nat.not_even_iff_odd.mpr hg)

theorem isCharacteristicP_of_f1Zero {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h1444 : Item1444 A (lB A))
    {X K Y M T H : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hF : ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
      g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
        Odd (orderOf g) → g = 1)
    (hH : H ∈ scriptQ A (lB A)) (hHI : H ≤ delta A (lB A) M)
    (hZH : delta A (lB A) (CFSG.Open.pCoreOf 2 M) ≤ H) : IsCharacteristicP 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  have hAV : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hHM : H ≤ M := hHI.trans (delta_le M)
  have hHV : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨h.toSec13Data.isElemAbelian, fun B hB hAB => (h.toSec13Data.eq_of_le hB hAB).le⟩
  have hH3 : ¬ 3 ∣ Nat.card H := (isPiSubgroup_piCompl_iff Nat.prime_three H).mp hH.1.2.1
  have hP := isPGroup_inf_centralizer_delta h.isE27 h1444 hV2 hAV hH hHV
    (fun g hg hgV hodd => eq_one_of_mem_centralizer_pCoreOf h hC (hHM hg) hgV hodd)
    fun g hg hgA hgZ hodd => hF g ⟨inf_centralizer_le_xA hAmax hH3 ⟨hg, hgA⟩, hHM hg⟩ hgZ hodd
  have hIZ := (Sylow155B1.delta_pCore_facts h h146 hC).2
  refine Proof153Twin3.isCharacteristicP_of_le_normalizer' hZH (hV2.to_le (delta_le _))
    (hHI.trans hIZ) fun g hg hgc => ?_
  obtain ⟨k, hk⟩ := hP ⟨g, hg, hgc⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem isCharacteristicP_delta_sup_of_f1Zero {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h1444 : Item1444 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hF : ∀ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
      g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) →
        Odd (orderOf g) → g = 1) :
    IsCharacteristicP 2
      ↥(delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) := by
  have hH := delta_mem_scriptQ h.isE27 h146 (Sylow155S.sup_mem_invariant hC hE hRP)
  have hHI : delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤
      delta A (lB A) M :=
    delta_mono ((Sylow155S.sup_le_u155 hE hRP).trans (Sylow155B1.u155_le.trans inf_le_left))
  have hZH : delta A (lB A) (CFSG.Open.pCoreOf 2 M) ≤
      delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) :=
    le_delta (Sylow155B1.delta_pCore_facts h h146 hC).1
      ((Sylow155B1.delta_pCore_le_r h h146 hC hE hIX).trans le_sup_left)
  exact isCharacteristicP_of_f1Zero h h146 h1444 hC hF hH hHI hZH

end Sylow155F1

theorem step155HostCharSupW_of_f1Zero {A : Subgroup G} {c : G} {L : Subgroup G}
    (h1444 : Item1444 A (lB A)) (hF : Step155F1ZeroW A c L) : Step155HostCharSupW A c L :=
  fun h X K Y M T P hC hmax hab hE h146 hRP hIX =>
    Sylow155F1.isCharacteristicP_delta_sup_of_f1Zero h h146 h1444 hC hE hRP hIX
      (hF h X K Y M T P hC hmax hab hE h146 hRP hIX)

end CFSG.RankThree.PartTwo.Sec15
