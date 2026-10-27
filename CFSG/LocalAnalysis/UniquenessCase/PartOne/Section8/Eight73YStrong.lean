module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.StrongQuotient
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.FrattiniSylow
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G] [Finite G]

theorem stronglyPEmbedded_quotient_of_maximal_of_prime {G : Type} [Group G] [Finite G]
    {M H Y : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hYH : Y ≤ H) (hYnorm : (Y.subgroupOf H).Normal) (hYM : Y ≤ M)
    (hYp : IsPGroup p Y)
    (hmax : ∀ Z : Subgroup G, Y < Z → Z ≤ M → IsPGroup p Z →
      Subgroup.normalizer (Z : Set G) ≤ M)
    (hne : ((M ⊓ H).subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H)) ≠ ⊤)
    (hpE : ∃ E : Subgroup G, E ≤ M ⊓ H ∧ IsPGroup p E ∧ ¬ E ≤ Y) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p
      (((M ⊓ H).subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let YH : Subgroup ↥H := Y.subgroupOf H
  haveI hYHnorm : YH.Normal := hYnorm
  let π : ↥H →* (↥H ⧸ YH) := QuotientGroup.mk' YH
  let MH : Subgroup ↥H := (M ⊓ H).subgroupOf H
  let Mq : Subgroup (↥H ⧸ YH) := MH.map π
  have hπ_surj : Function.Surjective π := QuotientGroup.mk'_surjective YH
  have hYH_MH : YH ≤ MH := by
    intro x hx
    exact ⟨hYM (Subgroup.mem_subgroupOf.mp hx), x.2⟩
  have hker : π.ker = YH := QuotientGroup.ker_mk' YH
  have hker_le_MH : π.ker ≤ MH := by rw [hker]; exact hYH_MH
  have hYHp : IsPGroup p YH := by
    change IsPGroup p (Y.comap H.subtype)
    exact hYp.comap_subtype (K := H)
  have hkerp : IsPGroup p π.ker := by rw [hker]; exact hYHp
  have hpdvd : p ∣ Nat.card Mq := by
    obtain ⟨E, hEMH, hEp, hEnotY⟩ := hpE
    let EH : Subgroup ↥H := E.subgroupOf H
    have hEHp : IsPGroup p EH := by
      change IsPGroup p (E.comap H.subtype)
      exact hEp.comap_subtype (K := H)
    let E' : Subgroup (↥H ⧸ YH) := EH.map π
    have hE'p : IsPGroup p E' := hEHp.map π
    have hEH_MH : EH ≤ MH := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hEMH (Subgroup.mem_subgroupOf.mp hx))
    have hE'_le : E' ≤ Mq := Subgroup.map_mono hEH_MH
    have hE'ne : E' ≠ ⊥ := by
      intro hbot
      have hEH_le_YH : EH ≤ YH := by
        have h := (Subgroup.map_eq_bot_iff (f := π) (H := EH)).mp hbot
        rwa [hker] at h
      have hE_le_Y : E ≤ Y := by
        intro e he
        have hxH : e ∈ H := (hEMH he).2
        have hxEH : (⟨e, hxH⟩ : ↥H) ∈ EH := he
        exact Subgroup.mem_subgroupOf.mp (hEH_le_YH hxEH)
      exact hEnotY hE_le_Y
    have hpE' : p ∣ Nat.card E' := by
      rcases hE'p.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hE'ne
      · exact h1
    exact hpE'.trans (Subgroup.card_dvd_of_le hE'_le)
  have hnorm : ∀ X : Subgroup (↥H ⧸ YH), X ≤ Mq → IsPGroup p X → X ≠ ⊥ →
      Subgroup.normalizer (X : Set (↥H ⧸ YH)) ≤ Mq := by
    intro X hXMq hXp hXne
    let E : Subgroup ↥H := X.comap π
    have hEp : IsPGroup p E := hXp.comap_of_ker_isPGroup π hkerp
    have hE_MH : E ≤ MH := by
      have h1 : E ≤ (MH.map π).comap π := Subgroup.comap_mono hXMq
      rwa [Subgroup.comap_map_eq_self hker_le_MH] at h1
    have hEne : E ≠ YH := by
      intro hEq
      apply hXne
      calc X = E.map π := (Subgroup.map_comap_eq_self_of_surjective hπ_surj X).symm
        _ = YH.map π := by rw [hEq]
        _ = ⊥ := by rw [Subgroup.map_eq_bot_iff, hker]
    have hYH_le_E : YH ≤ E := by
      have h := Subgroup.ker_le_comap π X
      rwa [hker] at h
    have hYH_lt_E : YH < E := lt_of_le_of_ne hYH_le_E (Ne.symm hEne)
    let Z : Subgroup G := E.map H.subtype
    have hZ_M : Z ≤ M := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact (Subgroup.mem_subgroupOf.mp (hE_MH hx)).1
    have hZp : IsPGroup p Z := hEp.map H.subtype
    have hYltZ : Y < Z := by
      have h := (Subgroup.map_lt_map_iff_of_injective
        (f := H.subtype) H.subtype_injective).mpr hYH_lt_E
      rw [Subgroup.map_subgroupOf_eq_of_le hYH] at h
      simpa [Z] using h
    have hNZ : Subgroup.normalizer (Z : Set G) ≤ M := hmax Z hYltZ hZ_M hZp
    have hN_E_map : (Subgroup.normalizer (E : Set ↥H)).map H.subtype ≤ M ⊓ H := by
      intro g hg
      obtain ⟨x, hx, rfl⟩ := hg
      have hxmap : (x : G) ∈
          (Subgroup.normalizer (E : Set ↥H)).map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype hx
      have hxZ : (x : G) ∈ Subgroup.normalizer (Z : Set G) :=
        Subgroup.le_normalizer_map (H := E) (f := H.subtype) hxmap
      exact ⟨hNZ hxZ, x.2⟩
    have hN_E : Subgroup.normalizer (E : Set ↥H) ≤ MH := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hN_E_map ⟨x, hx, rfl⟩)
    have hN_X : Subgroup.normalizer (X : Set (↥H ⧸ YH)) ≤ Mq := by
      have h1 : (Subgroup.normalizer (E : Set ↥H)).map π ≤ MH.map π :=
        Subgroup.map_mono hN_E
      have h2 : Subgroup.normalizer (E : Set ↥H) =
          (Subgroup.normalizer (X : Set (↥H ⧸ YH))).comap π :=
        (Subgroup.comap_normalizer_eq_of_surjective X hπ_surj).symm
      rw [h2, Subgroup.map_comap_eq_self_of_surjective hπ_surj] at h1
      simpa [Mq] using h1
    exact hN_X
  have hMq_ne : Mq ≠ ⊤ := by simpa only [Mq, MH, π, YH] using hne
  have hglb : CFSG.Open.GLBStronglyEmbedded p Mq :=
    CFSG.RankThree.PartTwo.Sec21.glbStronglyEmbedded_of_normalizer_le hMq_ne hpdvd hnorm
  exact CFSG.RankThree.PartOne.isStronglyPEmbedded_of_glbStronglyEmbedded hglb

theorem not_centralizer_le_of_maximal {G : Type} [Group G] [Finite G] {M Y E : Subgroup G}
    {p : ℕ}
    (hp : p.Prime) (hYM : Y ≤ M) (hYp : IsPGroup p Y)
    (hYab : Y ≤ Subgroup.centralizer (Y : Set G))
    (hYN : ¬ Subgroup.normalizer (Y : Set G) ≤ M)
    (hmax : ∀ Z : Subgroup G, Y < Z → Z ≤ M → IsPGroup p Z →
      Subgroup.normalizer (Z : Set G) ≤ M)
    (hEC : E ≤ Subgroup.centralizer (Y : Set G)) (hEp : IsPGroup p E) (hEY : ¬ E ≤ Y) :
    ¬ Subgroup.centralizer (Y : Set G) ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hCM
  let Cz : Subgroup G := Subgroup.centralizer (Y : Set G)
  let Nz : Subgroup G := Subgroup.normalizer (Y : Set G)
  have hsupC : E ⊔ Y ≤ Cz := sup_le hEC hYab
  have hsup : IsPGroup p (E ⊔ Y : Subgroup G) :=
    hEp.to_sup_of_normal_right' hYp
      (hEC.trans (Subgroup.centralizer_le_normalizer (Y : Set G)))
  have hsub : IsPGroup p ((E ⊔ Y).subgroupOf Cz) := by
    change IsPGroup p ((E ⊔ Y).comap Cz.subtype)
    exact hsup.comap_subtype (K := Cz)
  obtain ⟨S, hS⟩ := hsub.exists_le_sylow
  let SG : Subgroup G := (S : Subgroup ↥Cz).map Cz.subtype
  have hSGC : SG ≤ Cz := by
    show (S : Subgroup ↥Cz).map Cz.subtype ≤ Cz
    exact Subgroup.map_subtype_le _
  have hsupSG : E ⊔ Y ≤ SG := by
    show E ⊔ Y ≤ (S : Subgroup ↥Cz).map Cz.subtype
    have h1 : ((E ⊔ Y).subgroupOf Cz).map Cz.subtype ≤
        (S : Subgroup ↥Cz).map Cz.subtype := Subgroup.map_mono hS
    rwa [Subgroup.map_subgroupOf_eq_of_le hsupC] at h1
  have hYSG : Y ≤ SG := le_sup_right.trans hsupSG
  have hESG : E ≤ SG := le_sup_left.trans hsupSG
  have hYltSG : Y < SG :=
    lt_of_le_not_ge hYSG fun hSGY => hEY (hESG.trans hSGY)
  have hSGp : IsPGroup p SG := by
    show IsPGroup p ((S : Subgroup ↥Cz).map Cz.subtype)
    exact S.isPGroup'.map Cz.subtype
  have hNSG : Subgroup.normalizer (SG : Set G) ≤ M :=
    hmax SG hYltSG (hSGC.trans hCM) hSGp
  have hKC : Cz ≤ Nz := Subgroup.centralizer_le_normalizer (Y : Set G)
  have hKnorm : (Cz.subgroupOf Nz).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (Y : Set G)
  have hfr := eq_sup_normalizer_of_sylow (p := p) hKC hKnorm S
  have hNle : Nz ≤ M := by
    rw [hfr]
    refine sup_le hCM ?_
    exact inf_le_left.trans hNSG
  exact hYN hNle

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
