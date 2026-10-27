module

public import CFSG.RankThree.Co2.Census
public import CFSG.RankThree.Co2.JUnique
public import CFSG.RankThree.Co2.CrMatConj
public import CFSG.RankThree.Co2.JClassesCert
public import Certificates.Certificate8102
public import Certificates.Certificate8104
public import Certificates.Certificate8106
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate16022
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem jWords_lt42 : ∀ k < jWords.size, ∀ l ∈ jWords[k]!, l < 42 := by
  decide +kernel

theorem mem_J_iff_crMat {y : Cr} : y ∈ subW jWords ↔ crMat y ∈ matGrp jWords :=
  mem_subW_iff_crMat jWords_lt42

theorem card_J_crConj {c : ℕ} (hc : c < 10) :
    Nat.card {j : subW jWords // IsConj (rep c) (j : Cr)} = nJ c := by
  have e := Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun j : subW jWords => IsConj (rep c) (j : Cr))
    (q := fun j : subW jWords => CrConj (repMat c) (crMat (j : Cr)))
    fun j => isConj_iff_crConj hc)
  exact e.trans (card_subW_crMat jWords_lt42 (CrConj (repMat c)))

theorem card_J_class_seven : Nat.card {j : subW jWords // IsConj (rep 7) (j : Cr)} = 16 := by
  rw [card_J_crConj (by norm_num), jClassFacts_cert.seven]

theorem crMat_rCr : crMat rCr = repMat 0 := by
  rw [← rep_zero, crMat_rep (by norm_num)]

theorem rCr_mem_J : rCr ∈ subW jWords := by
  rw [mem_J_iff_crMat, crMat_rCr]
  exact jClassFacts_cert.r_mem

@[expose] def omegaSeven : Set Cr := {y | y ∈ subW jWords ∧ (y = rCr ∨ IsConj (rep 7) y)}

theorem crMat_image_omegaSeven :
    crMat '' omegaSeven =
      {x | x ∈ matGrp jWords ∧ (CrConj (repMat 0) x ∨ CrConj (repMat 7) x)} := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, h⟩, rfl⟩
    refine ⟨mem_J_iff_crMat.1 hy, ?_⟩
    rw [← isConj_iff_crConj (by norm_num), ← isConj_iff_crConj (by norm_num),
      isConj_rep_zero_iff]
    exact h
  · rintro ⟨hx, h⟩
    rw [← map_subW_eq jWords_lt42] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← isConj_iff_crConj (by norm_num), ← isConj_iff_crConj (by norm_num),
      isConj_rep_zero_iff] at h
    exact ⟨y, ⟨hy, h⟩, rfl⟩

theorem card_V : Nat.card (Subgroup.closure omegaSeven) = 64 := by
  have e : Nat.card (Subgroup.closure omegaSeven).toSubmonoid =
      Nat.card ((Subgroup.closure omegaSeven).toSubmonoid.map crMat) :=
    Nat.card_congr (Submonoid.equivMapOfInjective _ crMat crMat_injective).toEquiv
  change Nat.card (Subgroup.closure omegaSeven).toSubmonoid = 64
  rw [e, closure_toSubmonoid_eq, MonoidHom.map_mclosure, crMat_image_omegaSeven]
  exact jClassFacts_cert.span

theorem card_J_r_or_crConj {c : ℕ} (hc : c < 10) (h1 : classSizes[c]! ≠ 1) :
    Nat.card {j : subW jWords // (j : Cr) = rCr ∨ IsConj (rep c) (j : Cr)} = nJ c + 1 := by
  have hd : Disjoint {j : subW jWords | IsConj (rep c) (j : Cr)} {j | (j : Cr) = rCr} := by
    rw [Set.disjoint_left]
    rintro j hj (e : (j : Cr) = rCr)
    rw [Set.mem_setOf_eq, e] at hj
    exact not_isConj_rep_rCr hc h1 hj
  have hr : {j : subW jWords | (j : Cr) = rCr} = {⟨rCr, rCr_mem_J⟩} := by
    ext j
    rw [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun e => Subtype.ext e, fun e => by rw [e]⟩
  have e : Nat.card {j : subW jWords // (j : Cr) = rCr ∨ IsConj (rep c) (j : Cr)} =
      Nat.card ↥({j : subW jWords | IsConj (rep c) (j : Cr)} ∪ {j | (j : Cr) = rCr}) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun j => by
      rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, or_comm])
  rw [e, Nat.card_coe_set_eq, Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _), hr,
    Set.ncard_singleton, ← Nat.card_coe_set_eq]
  exact congrArg (· + 1) (card_J_crConj hc)

theorem card_J_r_two :
    Nat.card {j : subW jWords // (j : Cr) = rCr ∨ IsConj (rep 2) (j : Cr)} = 61 := by
  rw [card_J_r_or_crConj (by norm_num) (by decide), jClassFacts_cert.two]

theorem card_J_r_seven :
    Nat.card {j : subW jWords // (j : Cr) = rCr ∨ IsConj (rep 7) (j : Cr)} = 17 := by
  rw [card_J_r_or_crConj (by norm_num) (by decide), jClassFacts_cert.seven]

theorem not_isConj_rep_nine_of_mem_J {y : Cr} (hy : y ∈ subW jWords) : ¬ IsConj (rep 9) y := by
  rw [isConj_iff_crConj (by norm_num)]
  exact jClassFacts_cert.not_nine _ (mem_J_iff_crMat.1 hy)

end CFSG.RankThree.Co2
