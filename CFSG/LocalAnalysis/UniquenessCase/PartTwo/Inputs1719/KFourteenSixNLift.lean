module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp146N (N T A : Subgroup G) (r : ℕ) : Prop where
  kGroup : CFSG.Open.IsKGroup ↥N
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T N
  prime : r.Prime
  three_lt : 3 < r
  two_pow : ∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1
  le : A ≤ N
  card : Nat.card A = r
  permutes : UC22.Permutes A T
  rank_three : CFSG.Open.pRank 3 N ≤ 1
  rank_r : CFSG.Open.pRank r N ≤ 1
  rank_two : ∀ s : ℕ, s.Prime → 3 < s → CFSG.Open.pRank s N ≤ 2

@[expose] noncomputable def barIn (H Y : Subgroup G) : Subgroup (UC22.BarInf H) :=
  (Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.solvableRadical ↥H))

@[expose] noncomputable def liftIn (H : Subgroup G) (L : Subgroup (UC22.BarInf H)) :
    Subgroup G :=
  (L.comap (QuotientGroup.mk' (CFSG.solvableRadical ↥H))).map H.subtype

variable {N T A : Subgroup G} {r : ℕ}

omit [Finite G] in
theorem map_subtype_map_conj {H : Subgroup G} (S : Subgroup ↥H) (y : ↥H) :
    (S.map (MulAut.conj y).toMonoidHom).map H.subtype =
      (S.map H.subtype).map (MulAut.conj (y : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem Hyp146N.conjClosure_le (h : Hyp146N N T A r) : UC22.conjClosure N A ≤ N :=
  UC22.uc22p22v_conjClosure_le Subgroup.le_normalizer h.le

theorem Hyp146N.exists_conj_eq (h : Hyp146N N T A r) {g : G} (hg : g ∈ N) :
    ∃ x ∈ UC22.conjClosure N A,
      A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj x).toMonoidHom := by
  have : Fact r.Prime := ⟨h.prime⟩
  have hAH : A ≤ UC22.conjClosure N A := UC22.uc22p22v_le_conjClosure N A
  have hBH : A.map (MulAut.conj g).toMonoidHom ≤ UC22.conjClosure N A := by
    have hgn : (UC22.conjClosure N A).map (MulAut.conj g).toMonoidHom =
        UC22.conjClosure N A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (UC22.uc22p22v_le_normalizer_conjClosure N A hg)
    calc A.map (MulAut.conj g).toMonoidHom
        ≤ (UC22.conjClosure N A).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hAH
      _ = UC22.conjClosure N A := hgn
  have hrankTop :
      CFSG.Open.pRank r (⊤ : Subgroup ↥(UC22.conjClosure N A)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (UC22.conjClosure N A)]
    exact (CFSG.SectionRank.pRank_mono h.prime.one_lt h.conjClosure_le).trans h.rank_r
  have hAcard : Nat.card (A.subgroupOf (UC22.conjClosure N A)) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, h.card]
  have hBcard : Nat.card
      ((A.map (MulAut.conj g).toMonoidHom).subgroupOf (UC22.conjClosure N A)) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card]
  obtain ⟨x, -, hxeq⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime
      (p := r) hrankTop le_top le_top hAcard hBcard
  refine ⟨x, x.2, ?_⟩
  have hL : ((A.subgroupOf (UC22.conjClosure N A)).map
      (MulAut.conj x).toMonoidHom).map (UC22.conjClosure N A).subtype =
      A.map (MulAut.conj (x : G)).toMonoidHom := by
    rw [map_subtype_map_conj, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
  have hR : ((A.map (MulAut.conj g).toMonoidHom).subgroupOf
      (UC22.conjClosure N A)).map (UC22.conjClosure N A).subtype =
      A.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBH]
  have hkey := congrArg (fun S : Subgroup ↥(UC22.conjClosure N A) =>
    S.map (UC22.conjClosure N A).subtype) hxeq
  rw [hL, hR] at hkey
  exact hkey.symm

theorem Hyp146N.not_dvd_card_OInf (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) :
    ¬ r ∣ Nat.card (UC22.OInf (UC22.conjClosure N A)) := by
  intro hdvd
  have : Fact r.Prime := ⟨h.prime⟩
  have hchar : (CFSG.solvableRadical ↥(UC22.conjClosure N A)).Characteristic :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_characteristic
  have hnorm : N ≤ Subgroup.normalizer (UC22.OInf (UC22.conjClosure N A) : Set G) :=
    (UC22.uc22p22v_le_normalizer_conjClosure N A).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.solvableRadical ↥(UC22.conjClosure N A)))
  have hdvd' : r ∣ Nat.card (CFSG.solvableRadical ↥(UC22.conjClosure N A)) := by
    have hmap : UC22.OInf (UC22.conjClosure N A) =
        (CFSG.solvableRadical ↥(UC22.conjClosure N A)).map
          (UC22.conjClosure N A).subtype := rfl
    rw [hmap, Subgroup.card_map_of_injective
      (UC22.conjClosure N A).subtype_injective] at hdvd
    exact hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hdvd'
  let B : Subgroup ↥(UC22.conjClosure N A) := Subgroup.zpowers z
  have hBcard : Nat.card B = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have hBR : B ≤ CFSG.solvableRadical ↥(UC22.conjClosure N A) :=
    Subgroup.zpowers_le.mpr z.2
  have hAH : A ≤ UC22.conjClosure N A := UC22.uc22p22v_le_conjClosure N A
  have hAcard : Nat.card (A.subgroupOf (UC22.conjClosure N A)) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, h.card]
  have hrankTop : CFSG.Open.pRank r (⊤ : Subgroup ↥(UC22.conjClosure N A)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (UC22.conjClosure N A)]
    exact (CFSG.SectionRank.pRank_mono h.prime.one_lt h.conjClosure_le).trans h.rank_r
  obtain ⟨x, -, hx⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime
      (p := r) hrankTop le_top (hBR.trans le_top) hAcard hBcard
  have hAR : A ≤ UC22.OInf (UC22.conjClosure N A) := by
    have hAR' : A.subgroupOf (UC22.conjClosure N A) ≤
        CFSG.solvableRadical ↥(UC22.conjClosure N A) := by
      intro a ha
      have hxa : x * a * x⁻¹ ∈ B := by
        have h1 : x * a * x⁻¹ ∈
            (A.subgroupOf (UC22.conjClosure N A)).map (MulAut.conj x).toMonoidHom :=
          ⟨a, ha, rfl⟩
        rwa [hx] at h1
      have h2 : x⁻¹ * (x * a * x⁻¹) * x ∈
          CFSG.solvableRadical ↥(UC22.conjClosure N A) :=
        (inferInstance : (CFSG.solvableRadical ↥(UC22.conjClosure N A)).Normal).conj_mem'
          _ (hBR hxa) x
      simpa [mul_assoc] using h2
    calc A = (A.subgroupOf (UC22.conjClosure N A)).map (UC22.conjClosure N A).subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
      _ ≤ (CFSG.solvableRadical ↥(UC22.conjClosure N A)).map
            (UC22.conjClosure N A).subtype := Subgroup.map_mono hAR'
      _ = UC22.OInf (UC22.conjClosure N A) := rfl
  have hHle : UC22.conjClosure N A ≤ UC22.OInf (UC22.conjClosure N A) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨y, hy, rfl⟩ := hK
    have hyN : y ∈ Subgroup.normalizer (UC22.OInf (UC22.conjClosure N A) : Set G) := hnorm hy
    have hyN' : (UC22.OInf (UC22.conjClosure N A)).map (MulAut.conj y).toMonoidHom =
        UC22.OInf (UC22.conjClosure N A) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
    calc A.map (MulAut.conj y).toMonoidHom
        ≤ (UC22.OInf (UC22.conjClosure N A)).map (MulAut.conj y).toMonoidHom :=
          Subgroup.map_mono hAR
      _ = UC22.OInf (UC22.conjClosure N A) := hyN'
  have htop : CFSG.solvableRadical ↥(UC22.conjClosure N A) = ⊤ := by
    refine le_antisymm le_top ?_
    intro a _
    have ha : (a : G) ∈ UC22.OInf (UC22.conjClosure N A) := hHle a.2
    obtain ⟨b, hb, hbe⟩ := ha
    have hba : b = a := Subtype.ext hbe
    rwa [hba] at hb
  have hsolR : Group.IsSolvable (CFSG.solvableRadical ↥(UC22.conjClosure N A)) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hsurj : Function.Surjective (CFSG.solvableRadical ↥(UC22.conjClosure N A)).subtype := by
    rw [← MonoidHom.range_eq_top, Subgroup.range_subtype]
    exact htop
  exact hns (Group.isSolvable_of_surjective (f :=
    (CFSG.solvableRadical ↥(UC22.conjClosure N A)).subtype) hsurj)

theorem Hyp146N.card_barIn (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) :
    Nat.card (barIn (UC22.conjClosure N A) A) = r := by
  have : Fact r.Prime := ⟨h.prime⟩
  have hAH : A ≤ UC22.conjClosure N A := UC22.uc22p22v_le_conjClosure N A
  have hOInf_card : Nat.card (UC22.OInf (UC22.conjClosure N A)) =
      Nat.card (CFSG.solvableRadical ↥(UC22.conjClosure N A)) :=
    Subgroup.card_map_of_injective (UC22.conjClosure N A).subtype_injective
  have hnotdvd : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥(UC22.conjClosure N A)) := by
    rw [← hOInf_card]
    exact h.not_dvd_card_OInf hns
  have hdisj : A ⊓ UC22.OInf (UC22.conjClosure N A) = ⊥ := by
    have hdvd1 : Nat.card ↥(A ⊓ UC22.OInf (UC22.conjClosure N A)) ∣ Nat.card ↥A :=
      Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥(A ⊓ UC22.OInf (UC22.conjClosure N A)) ∣
        Nat.card ↥(CFSG.solvableRadical ↥(UC22.conjClosure N A)) := by
      rw [← hOInf_card]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime h.prime).mp (h.card ▸ hdvd1) with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (h1 ▸ hdvd2) hnotdvd
  have hdisj' : (A.subgroupOf (UC22.conjClosure N A)) ⊓
      (QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A))).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', eq_bot_iff]
    intro a ha
    have hxA : (a : G) ∈ A := ha.1
    have hxO : (a : G) ∈ UC22.OInf (UC22.conjClosure N A) :=
      Subgroup.mem_map_of_mem _ ha.2
    have hmem : (a : G) ∈ A ⊓ UC22.OInf (UC22.conjClosure N A) := ⟨hxA, hxO⟩
    rw [hdisj] at hmem
    exact Subtype.ext hmem
  rw [barIn, CFSG.card_map_eq_card_of_inf_ker_eq_bot _ hdisj',
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, h.card]

theorem Hyp146N.isSylowOf_barIn (h : Hyp146N N T A r) :
    CFSG.ABGLocalTools.IsSylowOf 2 (barIn (UC22.conjClosure N A) T) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2
      (T ⊓ UC22.conjClosure N A) (UC22.conjClosure N A) :=
    h.sylow.inf_of_le_normalizer h.conjClosure_le
      (UC22.uc22p22v_le_normalizer_conjClosure N A)
  have hTH' : CFSG.ABGLocalTools.IsSylowOf 2
      (T.subgroupOf (UC22.conjClosure N A)) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2)
      (K := UC22.conjClosure N A)
      (A := T.subgroupOf (UC22.conjClosure N A)) (B := ⊤)).mp ?_
    simpa [Subgroup.map_top] using hTH
  unfold barIn
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, hTH'.isPGroup.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hd
  refine (CFSG.ABGLocalTools.isSylowOf_iff.mp hTH').2.2 ?_
  have hdvd : 2 ∣ (T.subgroupOf (UC22.conjClosure N A)).index :=
    hd.trans (Subgroup.index_map_dvd (H := T.subgroupOf (UC22.conjClosure N A))
      (f := QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A)))
      (QuotientGroup.mk'_surjective _))
  rwa [← Subgroup.relIndex_top_right] at hdvd

theorem Hyp146N.permutes_barIn (h : Hyp146N N T A r) :
    UC22.Permutes (barIn (UC22.conjClosure N A) A) (barIn (UC22.conjClosure N A) T) := by
  have hAH : A ≤ UC22.conjClosure N A := UC22.uc22p22v_le_conjClosure N A
  have hsub : ((A.subgroupOf (UC22.conjClosure N A) :
        Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) *
      ((T.subgroupOf (UC22.conjClosure N A) :
        Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) =
      ((T.subgroupOf (UC22.conjClosure N A) :
        Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) *
      ((A.subgroupOf (UC22.conjClosure N A) :
        Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_mul] at hx ⊢
      obtain ⟨a, haA, t, htT, rfl⟩ := hx
      have hxH : ((a : ↥(UC22.conjClosure N A)) : G) * (t : G) ∈
          UC22.conjClosure N A :=
        (UC22.conjClosure N A).mul_mem a.2 t.2
      have hmem : ((a : ↥(UC22.conjClosure N A)) : G) * (t : G) ∈
          (A : Set G) * (T : Set G) := ⟨(a : G), haA, (t : G), htT, rfl⟩
      rw [h.permutes] at hmem
      obtain ⟨t', ht'T, a', ha'A, he⟩ := hmem
      have ht'H : t' ∈ UC22.conjClosure N A := by
        have hEq : t' = ((a : ↥(UC22.conjClosure N A)) : G) * (t : G) * a'⁻¹ := by
          rw [← he]; group
        rw [hEq]
        exact (UC22.conjClosure N A).mul_mem hxH
          ((UC22.conjClosure N A).inv_mem (hAH ha'A))
      exact ⟨⟨t', ht'H⟩, ht'T, ⟨a', hAH ha'A⟩, ha'A, Subtype.ext he⟩
    · intro hx
      rw [Set.mem_mul] at hx ⊢
      obtain ⟨t, htT, a, haA, rfl⟩ := hx
      have hxH : ((t : ↥(UC22.conjClosure N A)) : G) * (a : G) ∈
          UC22.conjClosure N A :=
        (UC22.conjClosure N A).mul_mem t.2 a.2
      have hmem : ((t : ↥(UC22.conjClosure N A)) : G) * (a : G) ∈
          (T : Set G) * (A : Set G) := ⟨(t : G), htT, (a : G), haA, rfl⟩
      rw [← h.permutes] at hmem
      obtain ⟨a', ha'A, t', ht'T, he⟩ := hmem
      have ht'H : t' ∈ UC22.conjClosure N A := by
        have hEq : t' = a'⁻¹ * (((t : ↥(UC22.conjClosure N A)) : G) * (a : G)) := by
          rw [← he]; group
        rw [hEq]
        exact (UC22.conjClosure N A).mul_mem
          ((UC22.conjClosure N A).inv_mem (hAH ha'A)) hxH
      exact ⟨⟨a', hAH ha'A⟩, ha'A, ⟨t', ht'H⟩, ht'T, Subtype.ext he⟩
  have hbarA : ((barIn (UC22.conjClosure N A) A :
      Subgroup (UC22.BarInf (UC22.conjClosure N A))) :
      Set (UC22.BarInf (UC22.conjClosure N A))) =
      QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A)) ''
        ((A.subgroupOf (UC22.conjClosure N A) :
          Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) := by
    rw [barIn, Subgroup.coe_map]
  have hbarT : ((barIn (UC22.conjClosure N A) T :
      Subgroup (UC22.BarInf (UC22.conjClosure N A))) :
      Set (UC22.BarInf (UC22.conjClosure N A))) =
      QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A)) ''
        ((T.subgroupOf (UC22.conjClosure N A) :
          Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) := by
    rw [barIn, Subgroup.coe_map]
  rw [UC22.Permutes, hbarA, hbarT]
  conv_lhs => rw [← Set.image_mul
    (QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A)))]
  conv_rhs => rw [← Set.image_mul
    (QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A)))]
  rw [hsub]

theorem Hyp146N.normalClosure_barIn (h : Hyp146N N T A r) :
    normalClosure (barIn (UC22.conjClosure N A) A : Set (UC22.BarInf (UC22.conjClosure N A))) =
      ⊤ := by
  have hAH : A ≤ UC22.conjClosure N A := UC22.uc22p22v_le_conjClosure N A
  have hsurj : Function.Surjective
      (QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A))) :=
    QuotientGroup.mk'_surjective _
  have hCtop : Subgroup.normalClosure
      ((A.subgroupOf (UC22.conjClosure N A) :
        Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) = ⊤ := by
    set C : Subgroup ↥(UC22.conjClosure N A) := Subgroup.normalClosure
      ((A.subgroupOf (UC22.conjClosure N A) :
        Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) with hC
    have hAC : (A.subgroupOf (UC22.conjClosure N A) :
        Subgroup ↥(UC22.conjClosure N A)) ≤ C := by
      rw [hC]
      exact Subgroup.le_normalClosure
    have hle : UC22.conjClosure N A ≤ C.map (UC22.conjClosure N A).subtype := by
      conv_lhs => rw [show UC22.conjClosure N A = ⨆ K ∈ UC22.conjSetOf N A, K from rfl]
      refine iSup₂_le fun K hK => ?_
      obtain ⟨g, hg, rfl⟩ := hK
      obtain ⟨x, hxH, hxeq⟩ := h.exists_conj_eq hg
      rw [hxeq]
      rintro y ⟨a, ha, rfl⟩
      have haH : a ∈ UC22.conjClosure N A := hAH ha
      have hmem : (⟨a, haH⟩ : ↥(UC22.conjClosure N A)) ∈ C :=
        hAC (Subgroup.mem_subgroupOf.mpr ha)
      have hCn : C.Normal := Subgroup.normalClosure_normal
      have hconj : (⟨x, hxH⟩ : ↥(UC22.conjClosure N A)) * ⟨a, haH⟩ *
          (⟨x, hxH⟩ : ↥(UC22.conjClosure N A))⁻¹ ∈ C :=
        hCn.conj_mem ⟨a, haH⟩ hmem ⟨x, hxH⟩
      refine ⟨(⟨x, hxH⟩ : ↥(UC22.conjClosure N A)) * ⟨a, haH⟩ *
        (⟨x, hxH⟩ : ↥(UC22.conjClosure N A))⁻¹, hconj, ?_⟩
      show (x * a * x⁻¹ : G) = (MulAut.conj x) a
      rw [MulAut.conj_apply]
    have hmap : C.map (UC22.conjClosure N A).subtype = UC22.conjClosure N A :=
      le_antisymm (Subgroup.map_subtype_le _) hle
    have htop : (⊤ : Subgroup ↥(UC22.conjClosure N A)).map
        (UC22.conjClosure N A).subtype = UC22.conjClosure N A := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective (UC22.conjClosure N A).subtype_injective
      (hmap.trans htop.symm)
  have hcoe : ((barIn (UC22.conjClosure N A) A :
      Subgroup (UC22.BarInf (UC22.conjClosure N A))) :
      Set (UC22.BarInf (UC22.conjClosure N A))) =
      QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A)) ''
        ((A.subgroupOf (UC22.conjClosure N A) :
          Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A)) := by
    rw [barIn, Subgroup.coe_map]
  rw [hcoe, ← Subgroup.map_normalClosure
    ((A.subgroupOf (UC22.conjClosure N A) :
      Subgroup ↥(UC22.conjClosure N A)) : Set ↥(UC22.conjClosure N A))
    (QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A))) hsurj, hCtop,
    Subgroup.map_top_of_surjective _ hsurj]

theorem Hyp146N.pRank_barInf_le_one (h : Hyp146N N T A r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpN : CFSG.Open.pRank p N ≤ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (UC22.BarInf (UC22.conjClosure N A))) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p ↥(UC22.conjClosure N A) := Sylow.nonempty.some
  have hPle : (P : Subgroup ↥(UC22.conjClosure N A)).map
      (UC22.conjClosure N A).subtype ≤ N :=
    (Subgroup.map_subtype_le _).trans h.conjClosure_le
  have hPmap : IsPGroup p ((P : Subgroup ↥(UC22.conjClosure N A)).map
      (UC22.conjClosure N A).subtype) := P.isPGroup'.map _
  have hPrank : CFSG.Open.pRank p ((P : Subgroup ↥(UC22.conjClosure N A)).map
      (UC22.conjClosure N A).subtype) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hPle).trans hpN
  have hPcyc : IsCyclic ↥((P : Subgroup ↥(UC22.conjClosure N A)).map
      (UC22.conjClosure N A).subtype) := by
    by_contra hnc
    have h2 := CFSG.LocalAnalysis.UniquenessCase.UC6.two_le_pRank_of_not_isCyclic
      hp hp2 hPmap hnc
    omega
  have hPcyc' : IsCyclic ↥(P : Subgroup ↥(UC22.conjClosure N A)) :=
    (Subgroup.equivMapOfInjective (P : Subgroup ↥(UC22.conjClosure N A))
      (UC22.conjClosure N A).subtype (UC22.conjClosure N A).subtype_injective).isCyclic.mpr hPcyc
  let S : Sylow p (UC22.BarInf (UC22.conjClosure N A)) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥(UC22.conjClosure N A)))
  have hScyc : IsCyclic ↥(S : Subgroup (UC22.BarInf (UC22.conjClosure N A))) := by
    have : IsCyclic ↥(P : Subgroup ↥(UC22.conjClosure N A)) := hPcyc'
    rw [show (S : Subgroup (UC22.BarInf (UC22.conjClosure N A))) =
      (P : Subgroup ↥(UC22.conjClosure N A)).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A))) from
      Sylow.coe_mapSurjective _ _]
    exact isCyclic_of_surjective
      ((QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A))).subgroupMap
        (P : Subgroup ↥(UC22.conjClosure N A)))
      ((QuotientGroup.mk' (CFSG.solvableRadical ↥(UC22.conjClosure N A))).subgroupMap_surjective _)
  calc CFSG.Open.pRank p (⊤ : Subgroup (UC22.BarInf (UC22.conjClosure N A)))
      = CFSG.Open.pRank p (S : Subgroup (UC22.BarInf (UC22.conjClosure N A))) :=
        (CFSG.SectionRank.pRank_sylow S).1.symm
    _ ≤ 1 := CFSG.SectionRank.pRank_le_one_of_isCyclic hp hScyc

theorem Hyp146N.isKGroup_barInf (h : Hyp146N N T A r) :
    CFSG.Open.IsKGroup (UC22.BarInf (UC22.conjClosure N A)) := by
  have hchar : (CFSG.solvableRadical ↥(UC22.conjClosure N A)).Characteristic :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_characteristic
  have hHN : UC22.conjClosure N A ≤ N := h.conjClosure_le
  have hsub : CFSG.Open.IsKGroup ↥((UC22.conjClosure N A).subgroupOf N) :=
    h.kGroup.subgroup ((UC22.conjClosure N A).subgroupOf N)
  have hH : CFSG.Open.IsKGroup ↥(UC22.conjClosure N A) :=
    CFSG.Open.IsKGroup.of_injective hsub
      (Subgroup.subgroupOfEquivOfLe hHN).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHN).symm.injective
  exact CFSG.Open.IsKGroup.quotient hH (CFSG.solvableRadical ↥(UC22.conjClosure N A))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN
