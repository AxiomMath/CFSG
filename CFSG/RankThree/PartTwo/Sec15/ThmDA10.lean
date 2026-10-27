module

public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Lemmas
public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Core
public import CFSG.RankThree.PartTwo.Sec15.ThmDLemma10

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem step153D3_of_inputs (hK7 : A7CentralizerThreeCycle) (h142 : Concl142S14) :
    Step153D3 := by
  intro G _ _ A c L hR Y hY hV hfaith hiso hK P hPY hP2 hAP
  obtain ⟨e⟩ := hiso
  have hS := hR.toSec14Std
  have hA : IsE27 A := hS.isE27
  have hAleY : A ≤ Y := a_le_of_faithful_a10 hR hY hfaith ⟨e⟩
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun x hx y hy =>
    congrArg Subtype.val (hR.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  refine mem_scriptQ_of_hyperplanes hA (h142 G A c L hS) hV hP3 hAP ?_
  intro B hB hBΩ p hp
  have hpP : p ∈ P := hp.1
  have hpB : p ∈ Subgroup.centralizer (B : Set G) := hp.2
  have hpY : p ∈ Y := hPY hpP
  obtain ⟨c', hc'A, hc'Y, hc'Ω, hc3⟩ := exists_threeCycle_point hK7 hA3 hAleY e hK
  have hcard : Nat.card (A.subgroupOf Y) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleY).toEquiv).trans hA.2
  have hBle : B ≤ A := hB.1
  have hB9 : Nat.card (B.subgroupOf Y) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBle.trans hAleY)).toEquiv]
    have := hB.2
    rw [hA.2] at this
    omega
  have hker := a10_fusion_core (psiOf Y e) (A.subgroupOf Y) hcard
    (fun a ha b hb => Subtype.ext (hAab a ha b hb))
    (fun a ha h => psiOf_eq_one_of_mem hA3 hAleY e ha h)
    {F' | ∃ F ∈ omegaA A, F' = F.subgroupOf Y}
    (fun n hn => exists_lift_psiOf hA3 hAab hAleY e hn)
    (fun m hm F' hF' => by
      obtain ⟨F, hF, rfl⟩ := hF'
      obtain ⟨F₂, hF₂, heq⟩ := exists_omega_conj_subgroupOf hAleY hF hm
      exact ⟨F₂, hF₂, heq⟩)
    ⟨c', hc'Y⟩ hc'A ⟨Subgroup.zpowers c', hc'Ω, zpowers_subgroupOf hc'Y⟩ hc3
    (B.subgroupOf Y) (fun x hx => hBle hx) hB9
    (by
      rintro F' ⟨F, hF, rfl⟩ hle
      refine hBΩ F hF fun x hx => ?_
      have hxY : x ∈ Y := hAleY (hF.1 hx)
      exact hle (show (⟨x, hxY⟩ : ↥Y) ∈ F.subgroupOf Y from hx))
    ⟨p, hpY⟩
    (fun b hb => Subtype.ext ((Subgroup.mem_centralizer_iff.mp hpB b hb).symm))
    (by
      obtain ⟨k, hk⟩ := hP2 ⟨p, hpP⟩
      refine isPGroup_zpowers_of_pow_eq_one (k := k) ?_
      rw [← map_pow]
      have : (⟨p, hpY⟩ : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one])
  have hmemO : p ∈ pPrimeCoreOf 3 Y :=
    Subgroup.mem_map.mpr ⟨⟨p, hpY⟩, (psiOf_eq_one_iff Y e _).mp hker, rfl⟩
  obtain ⟨k, hk⟩ := hP2 ⟨p, hpP⟩
  exact mem_pCoreOf_of_mem_pPrimeCoreOf hY hpY hmemO ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.RankThree.PartTwo.Sec15.ThmD
