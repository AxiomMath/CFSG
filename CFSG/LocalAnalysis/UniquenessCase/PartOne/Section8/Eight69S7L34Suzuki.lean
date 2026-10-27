module

import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularStab
import CFSG.RankThree.PartOne.KS.Basic
import CFSG.Adapters.GeneralizedFitting
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.GroupTheory.ConjNormalFaithful
import CFSG.GroupTheory.NormalLeCentralizerOfInfBot
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (IsAutSz)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_normal)

section Inner

variable {G S : Type} [Group G] [Group S]

private theorem nonempty_mulEquiv_comap_inner (hZ : Subgroup.center S = ⊥) (e : G ≃* MulAut S) :
    Nonempty (S ≃* ↥((inner S).comap e.toMonoidHom)) := by
  have hmap : Subgroup.map e.toMonoidHom ((inner S).comap e.toMonoidHom) = inner S :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective (inner S)
  refine ⟨(MonoidHom.ofInjective
    (CFSG.mulAutConj_injective_of_center_eq_bot hZ)).trans ?_⟩
  exact ((Subgroup.equivMapOfInjective ((inner S).comap e.toMonoidHom) e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr hmap)).symm

private theorem centralizer_comap_inner_eq_bot (hZ : Subgroup.center S = ⊥) (e : G ≃* MulAut S) :
    Subgroup.centralizer (((inner S).comap e.toMonoidHom : Subgroup G) : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hy' : e y ∈ Subgroup.centralizer ((inner S : Subgroup (MulAut S)) : Set (MulAut S)) := by
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    obtain ⟨s, rfl⟩ := hx
    have hmem : e.symm (MulAut.conj s) ∈ (inner S).comap e.toMonoidHom := by
      change e (e.symm (MulAut.conj s)) ∈ inner S
      rw [MulEquiv.apply_symm_apply]
      exact ⟨s, rfl⟩
    have h1 := congrArg e (hy (e.symm (MulAut.conj s)) hmem)
    simpa only [MulEquiv.apply_symm_apply, map_mul] using h1
  rw [CFSG.QuasithinUnique.Id2519.centralizer_inner_eq_bot_of_center_bot hZ] at hy'
  have hα : e y = 1 := Subgroup.mem_bot.mp hy'
  exact e.injective (by rw [hα, map_one])

private theorem index_comap_inner (e : G ≃* MulAut S) :
    ((inner S).comap e.toMonoidHom).index = Nat.card (Outer S) := by
  rw [Subgroup.index_comap_of_surjective (inner S) e.surjective, Subgroup.index_eq_card]

private theorem not_seven_dvd_card_mulAut
    (hS : LieModel S .twistedB2 0 2 5) (hZ : Subgroup.center S = ⊥) :
    ¬ 7 ∣ Nat.card (MulAut S) := by
  have : Finite S := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hS
  have hCardAut : Nat.card (MulAut S) = Nat.card S * Nat.card (Outer S) :=
    CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hZ
  have h7S : ¬ 7 ∣ Nat.card S := by
    rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 hS]
    norm_num
  have h75 : ¬ 7 ∣ 5 := by norm_num
  rw [hCardAut]
  intro h7
  rcases Nat.prime_seven.dvd_mul.mp h7 with h1 | h1
  · exact h7S h1
  · exact h75 (h1.trans
      (CFSG.SeitzReduction.RankOne.card_outer_dvd_of_lieModel_twistedB2 hS))

end Inner

section Normal

variable {G : Type} [Group G]

private theorem le_of_isSimpleGroup_of_centralizer_eq_bot {A B : Subgroup G} (hA : A.Normal)
    (hB : B.Normal) (hAs : IsSimpleGroup A) (hC : Subgroup.centralizer (A : Set G) = ⊥)
    (hB1 : B ≠ ⊥) : A ≤ B := by
  by_contra hle
  have hK : ((A ⊓ B).subgroupOf A).Normal := by
    refine Subgroup.Normal.mk fun n hn a => ?_
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hA.conj_mem n hn.1 a, hB.conj_mem n hn.2 a⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A ⊓ B).subgroupOf A) with h0 | h0
  · have hinf : A ⊓ B = ⊥ := by
      have hbot : (A ⊓ B) ⊓ A = ⊥ :=
        disjoint_iff.mp ((Subgroup.subgroupOf_eq_bot).mp h0)
      have hEq : (A ⊓ B) ⊓ A = A ⊓ B := inf_eq_left.mpr (inf_le_left : A ⊓ B ≤ A)
      simpa [hEq] using hbot
    have hBA : B ≤ Subgroup.centralizer (A : Set G) :=
      CFSG.normal_le_centralizer_of_inf_eq_bot hB hA (by rw [inf_comm]; exact hinf)
    rw [hC] at hBA
    exact hB1 (le_bot_iff.mp hBA)
  · rw [Subgroup.subgroupOf_eq_top] at h0
    exact hle (h0.trans inf_le_right)

private theorem eq_commutator_of_index_dvd_prime {A B : Subgroup G} (hA : A.Normal) (hAB : A ≤ B)
    {p : ℕ} (hp : p.Prime) (hi : A.index ∣ p) (hperf : ⁅A, A⁆ = A) : A = ⁅B, B⁆ := by
  have hprod : A.relIndex B * B.index ∣ p := by
    rw [Subgroup.relIndex_mul_index hAB]
    exact hi
  have hrelDvd : A.relIndex B ∣ p := (Subgroup.relIndex_dvd_index_of_le hAB).trans hi
  have hBdvd : B.index ∣ p := (Subgroup.index_dvd_of_le hAB).trans hi
  rcases (Nat.dvd_prime hp).mp hrelDvd with hrel1 | hrelp
  · have hEq : A = B := le_antisymm hAB ((Subgroup.relIndex_eq_one).mp hrel1)
    rw [hEq] at hperf ⊢
    exact hperf.symm
  · by_cases hB1 : B.index = 1
    · have hTop : B = ⊤ := (Subgroup.index_eq_one).mp hB1
      rw [hTop]
      have hcard : Nat.card (G ⧸ A) ∣ p := by
        rw [← Subgroup.index_eq_card]
        exact hi
      have : Fact p.Prime := ⟨hp⟩
      have : IsCyclic (G ⧸ A) := isCyclic_of_card_dvd_prime hcard
      have hComm : IsMulCommutative (G ⧸ A) := IsCyclic.isMulCommutative
      have hle : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ A :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hComm
      refine le_antisymm ?_ hle
      rw [← hperf]
      exact Subgroup.commutator_mono le_top le_top
    · have hBp : B.index = p := (Nat.dvd_prime hp).mp hBdvd |>.resolve_left hB1
      exfalso
      rw [hrelp, hBp] at hprod
      have hle : p * p ≤ p := Nat.le_of_dvd hp.pos hprod
      have : p ≤ 1 :=
        Nat.le_of_mul_le_mul_left (a := p) (b := 1) (c := p) (by simpa using hle) hp.pos
      have hp2 : 2 ≤ p := hp.two_le
      omega

end Normal

section FStar

variable {Q : Type} [Group Q] [Finite Q]

private theorem genFittingFStar_ne_bot [Nontrivial Q] : genFittingFStar Q ≠ ⊥ := by
  intro h0
  have hB := CFSG.Adapters.generalized_fitting_self_centralizing Q
  rw [h0] at hB
  have htop : (⊤ : Subgroup Q) ≤ ⊥ := by
    have h_eq : Subgroup.centralizer (↑(⊥ : Subgroup Q) : Set Q) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
    rw [← h_eq]
    exact hB
  exact not_subsingleton Q ⟨fun x y => by
    rw [Subgroup.mem_bot.mp (htop (Subgroup.mem_top x)),
      Subgroup.mem_bot.mp (htop (Subgroup.mem_top y))]⟩

private theorem centralizer_map_subtype_eq_bot {Y : Subgroup Q} (hY : genFittingFStar Q ≤ Y)
    {A : Subgroup ↥Y} (hA : (A.map Y.subtype).Normal)
    (hC : Subgroup.centralizer (A : Set ↥Y) = ⊥) :
    Subgroup.centralizer ((A.map Y.subtype : Subgroup Q) : Set Q) = ⊥ := by
  have hCn : (Subgroup.centralizer ((A.map Y.subtype : Subgroup Q) : Set Q)).Normal :=
    Subgroup.normal_centralizer
  have hNn : (genFittingFStar Q).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hCinf : Subgroup.centralizer ((A.map Y.subtype : Subgroup Q) : Set Q) ⊓
      genFittingFStar Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxY : x ∈ Y := hY hx.2
    have hxC : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.centralizer (A : Set ↥Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hmem : (s : Q) ∈ A.map Y.subtype := ⟨s, hs, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp hx.1 (s : Q) hmem
      exact Subtype.ext hcomm
    rw [hC] at hxC
    rw [Subgroup.mem_bot] at hxC
    exact Subtype.ext_iff.mp hxC
  have hCN : Subgroup.centralizer ((A.map Y.subtype : Subgroup Q) : Set Q) ≤
      genFittingFStar Q :=
    (CFSG.normal_le_centralizer_of_inf_eq_bot hCn hNn hCinf).trans
      (CFSG.Adapters.generalized_fitting_self_centralizing Q)
  refine le_bot_iff.mp ?_
  calc Subgroup.centralizer ((A.map Y.subtype : Subgroup Q) : Set Q) ≤
        Subgroup.centralizer ((A.map Y.subtype : Subgroup Q) : Set Q) ⊓ genFittingFStar Q :=
      le_inf le_rfl hCN
    _ = ⊥ := hCinf

end FStar

theorem not_seven_dvd_card_of_isAutSz {Q : Type} [Group Q]
    [Finite Q] {Y : Subgroup Q} (hY : genFittingFStar Q ≤ Y) (h : IsAutSz ↥Y 5) :
    ¬ 7 ∣ Nat.card Q := by
  obtain ⟨S, _, hS, ⟨e⟩⟩ := h
  have hS' : LieModel S .twistedB2 0 2 5 := hS
  have := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS'
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hS'
  have hnc : ¬ IsMulCommutative S := fun hc => hab (hc.is_comm.comm a b)
  have hZ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  obtain ⟨eS⟩ := nonempty_mulEquiv_comap_inner hZ e
  have hAN : ((inner S).comap e.toMonoidHom).Normal := (inner_normal S).comap e.toMonoidHom
  have hAC := centralizer_comap_inner_eq_bot hZ e
  have hAi : ((inner S).comap e.toMonoidHom).index ∣ 5 := by
    rw [index_comap_inner]
    exact CFSG.SeitzReduction.RankOne.card_outer_dvd_of_lieModel_twistedB2 hS'
  generalize (inner S).comap e.toMonoidHom = A at eS hAN hAC hAi
  have hAs : IsSimpleGroup A := MulEquiv.isSimpleGroup eS.symm
  have hAnc : ¬ IsMulCommutative A := fun hc =>
    hab (eS.injective (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _))
  have : Group.IsPerfect A := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hAnc
  have hNn : (genFittingFStar Q).Normal := CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have : Nontrivial Q := (Y.subtype_injective.comp A.subtype_injective).nontrivial
  have hN1 : (genFittingFStar Q).subgroupOf Y ≠ ⊥ := fun h0 =>
    genFittingFStar_ne_bot ((Subgroup.subgroupOf_eq_bot.mp h0).eq_bot_of_le hY)
  have hAeq := eq_commutator_of_index_dvd_prime hAN
    (le_of_isSimpleGroup_of_centralizer_eq_bot hAN (hNn.subgroupOf Y) hAs hAC hN1)
    Nat.prime_five hAi Subgroup.commutator_eq_self
  have hmap : A.map Y.subtype = ⁅genFittingFStar Q, genFittingFStar Q⁆ := by
    rw [hAeq, Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hY]
  have hAQ : (A.map Y.subtype).Normal := by
    rw [hmap]
    infer_instance
  have hinj := @Subgroup.conjNormal_injective_of_centralizer_eq_bot Q _ _ hAQ
    (centralizer_map_subtype_eq_bot hY hAQ hAC)
  have e' : ↥(A.map Y.subtype) ≃* S :=
    (Subgroup.equivMapOfInjective A Y.subtype Y.subtype_injective).symm.trans eS.symm
  have hdvd : Nat.card Q ∣ Nat.card (MulAut S) := by
    rw [← Nat.card_congr (MulAut.congr e').toEquiv]
    exact Subgroup.card_dvd_of_injective _ hinj
  exact fun h7 => not_seven_dvd_card_mulAut hS' hZ (h7.trans hdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
