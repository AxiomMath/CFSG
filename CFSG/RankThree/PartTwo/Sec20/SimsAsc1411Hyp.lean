module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private abbrev sylowMap (P : Sylow 2 ↥(CFSG.pPrimeCore 3 X)) : Subgroup X :=
  (P : Subgroup ↥(CFSG.pPrimeCore 3 X)).map (CFSG.pPrimeCore 3 X).subtype

private lemma pCore_two_le_pPrimeCore_three : CFSG.pCore 2 X ≤ CFSG.pPrimeCore 3 X := by
  refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := X))
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

private lemma pCore_le_sylowMap (P : Sylow 2 ↥(CFSG.pPrimeCore 3 X)) :
    CFSG.pCore 2 X ≤ sylowMap P := by
  intro q hq
  have hp : IsPGroup 2 ((CFSG.pCore 2 X).subgroupOf (CFSG.pPrimeCore 3 X)) :=
    CFSG.pCore_isPGroup.comap_subtype
  exact ⟨⟨q, pCore_two_le_pPrimeCore_three hq⟩, hp.le_sylow_of_normal P hq, rfl⟩

private lemma sylowMap_le_pCore (h : Hyp1411 X L S) (P : Sylow 2 ↥(CFSG.pPrimeCore 3 X)) :
    sylowMap P ≤ CFSG.pCore 2 X := by
  obtain ⟨-, -, -, -, -, -, -, hmin⟩ := h
  have hnorm : normalizer (sylowMap P : Set X) = ⊤ :=
    hmin _ ((pCore_le_sylowMap P).trans le_normalizer) (Sylow.normalizer_sup_eq_top P)
  exact le_sSup ⟨normalizer_eq_top_iff.1 hnorm, P.isPGroup'.map _⟩

theorem mem_pCore_of_mem_pPrimeCore_of_hyp1411 (h : Hyp1411 X L S) {s : X} (hs : s ∈ S)
    (hsK : s ∈ CFSG.pPrimeCore 3 X) : s ∈ CFSG.pCore 2 X := by
  have hz : IsPGroup 2 (zpowers s) := h.2.2.2.2.1.to_le (zpowers_le.2 hs)
  obtain ⟨P, hP⟩ := (hz.comap_subtype (K := CFSG.pPrimeCore 3 X)).exists_le_sylow
  exact sylowMap_le_pCore h P ⟨⟨s, hsK⟩, hP (mem_subgroupOf.2 (mem_zpowers s)), rfl⟩

theorem relIndex_pCore_le_card_map_of_hyp1411 (h : Hyp1411 X L S) {A : Subgroup X}
    (hAS : A ≤ S) :
    (CFSG.pCore 2 X).relIndex A ≤ Nat.card (S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
  have hAK : A ⊓ CFSG.pPrimeCore 3 X ≤ CFSG.pCore 2 X := fun x hx =>
    mem_pCore_of_mem_pPrimeCore_of_hyp1411 h (hAS hx.1) hx.2
  have hinf : A ⊓ CFSG.pCore 2 X = A ⊓ CFSG.pPrimeCore 3 X :=
    le_antisymm (inf_le_inf_left _ pCore_two_le_pPrimeCore_three) (le_inf inf_le_left hAK)
  have h1 : (CFSG.pCore 2 X).relIndex A = (CFSG.pPrimeCore 3 X).relIndex A := by
    rw [← inf_relIndex_left A (CFSG.pCore 2 X), hinf, inf_relIndex_left]
  have h2 : (CFSG.pPrimeCore 3 X).relIndex A =
      Nat.card (A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
  rw [h1, h2]
  exact Subgroup.card_le_of_le (map_mono hAS)

private lemma le_of_perfect_of_sup_eq_top {C : Subgroup X} [C.Normal] (hS : IsPGroup 2 S)
    (hCS : C ⊔ S = ⊤) (hL : ⁅L, L⁆ = L) : L ≤ C := by
  have hSmap : S.map (QuotientGroup.mk' C) = ⊤ := by
    have h1 : (C ⊔ S).map (QuotientGroup.mk' C) = ⊤ := by
      rw [hCS]
      exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
  have hpg : IsPGroup 2 ↥(L.map (QuotientGroup.mk' C)) :=
    (hS.map (QuotientGroup.mk' C)).to_le (hSmap ▸ le_top)
  have hperf : Group.IsPerfect ↥(L.map (QuotientGroup.mk' C)) := by
    rw [Subgroup.isPerfect_iff, ← map_commutator, hL]
  have : Group.IsNilpotent ↥(L.map (QuotientGroup.mk' C)) := hpg.isNilpotent
  have hbot : L.map (QuotientGroup.mk' C) = ⊥ := by
    by_contra hne
    have := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent ↥(L.map (QuotientGroup.mk' C)) inferInstance
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

private lemma map_inf_eq_bot_of_hyp1411 (h : Hyp1411 X L S)
    (hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    {C : Subgroup X} [C.Normal] (hLC : ¬ L ≤ C) :
    C.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥ := by
  obtain ⟨-, -, hLperf, -, hS2, hQS, hSL, hmin⟩ := h
  set K := CFSG.pPrimeCore 3 X
  have hCn : (C.map (QuotientGroup.mk' K)).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)
  have := hCn.subgroupOf (L.map (QuotientGroup.mk' K))
  rcases hsimp.eq_bot_or_eq_top_of_normal
    ((C.map (QuotientGroup.mk' K)).subgroupOf (L.map (QuotientGroup.mk' K))) with hbot | htop
  · exact disjoint_iff.1 (subgroupOf_eq_bot.1 hbot)
  · refine (hLC (le_of_perfect_of_sup_eq_top hS2 ?_ hLperf)).elim
    have hLK : L ≤ C ⊔ K := fun l hl => by
      have hl' : l ∈ (C.map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) :=
        subgroupOf_eq_top.1 htop (mem_map_of_mem (QuotientGroup.mk' K) hl)
      rwa [comap_map_eq, QuotientGroup.ker_mk'] at hl'
    refine hmin _ (hQS.trans le_sup_right) (top_unique ?_)
    rw [← hSL]
    exact sup_le (le_sup_right.trans le_sup_left) (hLK.trans (sup_le_sup_right le_sup_left _))

theorem map_centralizer_inf_eq_bot_of_hyp1411 (h : Hyp1411 X L S)
    (hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    {I : Subgroup X} (hI : I.Normal) (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) :
    (centralizer (I : Set X)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥ := by
  have := hI
  refine map_inf_eq_bot_of_hyp1411 h hsimp fun hLC => ?_
  obtain ⟨l, hl, i, hi, hne⟩ := hLI
  exact hne (by rw [← mem_centralizer_iff.1 (hLC hl) i hi, mul_inv_cancel_right])

theorem exists_not_commute_of_hyp1411 (h : Hyp1411 X L S)
    (hZ : center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥)
    {t : X} (htS : t ∈ S) (htQ : t ∉ CFSG.pCore 2 X) :
    ∃ l ∈ L, QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 X) l ≠
      QuotientGroup.mk' (CFSG.pPrimeCore 3 X) l *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t := by
  set K := CFSG.pPrimeCore 3 X
  by_contra hcon
  push Not at hcon
  have hF : CFSG.generalizedFitting (X ⧸ K) = L.map (QuotientGroup.mk' K) := h.2.2.2.1
  have hmem : QuotientGroup.mk' K t ∈ L.map (QuotientGroup.mk' K) := by
    rw [← hF]
    refine CFSG.centralizer_generalizedFitting_le _ ?_
    rw [hF, mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    exact (hcon l hl).symm
  have hzc : (⟨QuotientGroup.mk' K t, hmem⟩ : ↥(L.map (QuotientGroup.mk' K))) ∈
      center ↥(L.map (QuotientGroup.mk' K)) := by
    rw [mem_center_iff]
    rintro ⟨_, l, hl, rfl⟩
    exact Subtype.ext (hcon l hl).symm
  rw [hZ, mem_bot] at hzc
  have h1 : QuotientGroup.mk' K t = 1 := congrArg Subtype.val hzc
  exact htQ (mem_pCore_of_mem_pPrimeCore_of_hyp1411 h htS ((QuotientGroup.eq_one_iff t).1 h1))

end CFSG.RankThree.PartTwo.Sec20
