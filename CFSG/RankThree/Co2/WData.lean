module

public import CFSG.RankThree.Co2.WCert
public import CFSG.RankThree.Co2.CrBridge
public import CFSG.RankThree.Co2.JClasses
public import CFSG.RankThree.Co2.XSylow
public import CFSG.RankThree.Co2.X9FuseCert
public import Certificates.Certificate8102
public import Certificates.Certificate8110
public import Certificates.Certificate8113
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

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem card_subW_eq_matGrp {ws : Array (List ℕ)} (hws : ∀ k < ws.size, ∀ l ∈ ws[k]!, l < 42) :
    Nat.card (subW ws) = Nat.card (matGrp ws) := by
  rw [← card_map_subW, le_antisymm (map_subW_le hws) (matGrp_le_map hws)]

theorem wWords_size : wWords.size = 5 := rfl

theorem wWords_letters : ∀ k < wWords.size, ∀ l ∈ wWords[k]!, l < 42 := by
  decide +kernel

theorem pWords1_letters : ∀ k < pWords1.size, ∀ l ∈ pWords1[k]!, l < 42 := by
  decide +kernel

theorem mem_W_iff_crMat {y : Cr} :
    y ∈ subW wWords ↔ crMat y ∈ matGrp wGenWords :=
  mem_subW_iff_crMat wWords_letters

theorem exists_of_mem_matW {x : M22} (hx : x ∈ matGrp wGenWords) :
    ∃ y ∈ subW wWords, crMat y = x :=
  matGrp_le_map wWords_letters hx

theorem elemTwo_W : ElemTwo (subW wWords) := by
  refine ⟨fun x hx => crMat_injective ?_, fun x hx y hy => crMat_injective ?_⟩
  · rw [map_mul, map_one]
    exact wFacts_cert.sq _ (mem_W_iff_crMat.1 hx)
  · rw [map_mul, map_mul]
    exact wFacts_cert.comm _ (mem_W_iff_crMat.1 hx) _ (mem_W_iff_crMat.1 hy)

theorem gensW_W_zero : gensW wWords 0 = rep 1 := by
  rw [gensW, rep]
  rfl

theorem gensW_W_one : gensW wWords 1 = rCr := by
  rw [← rep_zero, gensW, rep]
  rfl

theorem rep_one_mem_W : rep 1 ∈ subW wWords := by
  rw [← gensW_W_zero]
  exact Subgroup.subset_closure ⟨0, by rw [Set.mem_setOf_eq, wWords_size]; norm_num, rfl⟩

theorem rCr_mem_W : rCr ∈ subW wWords := by
  rw [← gensW_W_one]
  exact Subgroup.subset_closure ⟨1, by rw [Set.mem_setOf_eq, wWords_size]; norm_num, rfl⟩

theorem W_le_C1 : subW wWords ≤ Subgroup.centralizer ({rep 1} : Set Cr) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact elemTwo_W.2 _ hy _ rep_one_mem_W

theorem rep_two_mul_rCr : rep 2 * rCr = rep 3 := by
  rw [← rep_zero, rep, rep, rep, ← wordCr_append]
  rfl

theorem rep_five_mul_rCr : rep 5 * rCr = rep 6 := by
  rw [← rep_zero, rep, rep, rep, ← wordCr_append]
  rfl

@[expose] def TypeAB (y : Cr) : Prop :=
  ∃ c < 10, ∃ c' < 10, inA c = true ∧ inB c' = true ∧ IsConj (rep c) y ∧ IsConj (rep c') (y * rep 1)

@[expose] def TypeBA (y : Cr) : Prop :=
  ∃ c < 10, ∃ c' < 10, inB c = true ∧ inA c' = true ∧ IsConj (rep c) y ∧ IsConj (rep c') (y * rep 1)

theorem isConj_of_InA {y : Cr} (h : InA (crMat y)) :
    ∃ c < 10, inA c = true ∧ IsConj (rep c) y := by
  obtain ⟨c, hc, hcy⟩ := h
  have hc' : c < 10 ∧ inA c = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ⟨by norm_num, rfl⟩
  exact ⟨c, hc'.1, hc'.2, (isConj_iff_crConj hc'.1).2 hcy⟩

theorem isConj_of_InB {y : Cr} (h : InB (crMat y)) :
    ∃ c < 10, inB c = true ∧ IsConj (rep c) y := by
  obtain ⟨c, hc, hcy⟩ := h
  have hc' : c < 10 ∧ inB c = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ⟨by norm_num, rfl⟩
  exact ⟨c, hc'.1, hc'.2, (isConj_iff_crConj hc'.1).2 hcy⟩

theorem InA_of_isConj {y : Cr} {c : ℕ} (hc : c < 10) (hA : inA c = true)
    (h : IsConj (rep c) y) : InA (crMat y) := by
  refine ⟨c, ?_, (isConj_iff_crConj hc).1 h⟩
  simp only [inA, Bool.or_eq_true, beq_iff_eq] at hA
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem InB_of_isConj {y : Cr} {c : ℕ} (hc : c < 10) (hB : inB c = true)
    (h : IsConj (rep c) y) : InB (crMat y) := by
  refine ⟨c, ?_, (isConj_iff_crConj hc).1 h⟩
  simp only [inB, Bool.or_eq_true, beq_iff_eq] at hB
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem typeAB_iff {y : Cr} :
    TypeAB y ↔ InA (crMat y) ∧ InB (crMat y * repMat 1) := by
  rw [← crMat_rep (by norm_num : 1 < 10), ← map_mul]
  constructor
  · rintro ⟨c, hc, c', hc', hA, hB, h, h'⟩
    exact ⟨InA_of_isConj hc hA h, InB_of_isConj hc' hB h'⟩
  · rintro ⟨hA, hB⟩
    obtain ⟨c, hc, hA', h⟩ := isConj_of_InA hA
    obtain ⟨c', hc', hB', h'⟩ := isConj_of_InB hB
    exact ⟨c, hc, c', hc', hA', hB', h, h'⟩

theorem typeBA_iff {y : Cr} :
    TypeBA y ↔ InB (crMat y) ∧ InA (crMat y * repMat 1) := by
  rw [← crMat_rep (by norm_num : 1 < 10), ← map_mul]
  constructor
  · rintro ⟨c, hc, c', hc', hB, hA, h, h'⟩
    exact ⟨InB_of_isConj hc hB h, InA_of_isConj hc' hA h'⟩
  · rintro ⟨hB, hA⟩
    obtain ⟨c, hc, hB', h⟩ := isConj_of_InB hB
    obtain ⟨c', hc', hA', h'⟩ := isConj_of_InA hA
    exact ⟨c, hc, c', hc', hB', hA', h, h'⟩

theorem mem_W_cases {y : Cr} (hy : y ∈ subW wWords) :
    y = 1 ∨ y = rep 1 ∨ TypeAB y ∨ TypeBA y := by
  rcases wFacts_cert.cases _ (mem_W_iff_crMat.1 hy) with h | h | h | h
  · exact Or.inl (crMat_injective (by rw [h, map_one]))
  · exact Or.inr (Or.inl (crMat_injective (by rw [h, crMat_rep (by norm_num)])))
  · exact Or.inr (Or.inr (Or.inl (typeAB_iff.2 h)))
  · exact Or.inr (Or.inr (Or.inr (typeBA_iff.2 h)))

theorem mem_W_of_type {y : Cr} (hya : y * rep 1 = rep 1 * y) (ht : TypeAB y ∨ TypeBA y) :
    y ∈ subW wWords := by
  refine mem_W_iff_crMat.2 (wFacts_cert.closed _ (crMat_mem_Cm y) ?_ ?_)
  · rw [← crMat_rep (by norm_num : 1 < 10), ← map_mul, ← map_mul, hya]
  · rcases ht with h | h
    · exact Or.inl (typeAB_iff.1 h)
    · exact Or.inr (typeBA_iff.1 h)

theorem card_typeAB_W : Nat.card {y : subW wWords // TypeAB (y : Cr)} = 15 := by
  rw [← wFacts_cert.card_typeAB]
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => ⟨crMat y.1, mem_W_iff_crMat.1 y.1.2, typeAB_iff.1 y.2⟩) ⟨?_, ?_⟩)
  · intro y z e
    exact Subtype.ext (Subtype.ext (crMat_injective (congrArg Subtype.val e)))
  · rintro ⟨x, hx, hA, hB⟩
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_matW hx
    exact ⟨⟨⟨y, hy⟩, typeAB_iff.2 ⟨hA, hB⟩⟩, rfl⟩

theorem card_P1 : Nat.card (subW pWords1) = 131072 :=
  sylCard1.trans (by norm_num)

theorem P1_le_C1 : subW pWords1 ≤ Subgroup.centralizer ({rep 1} : Set Cr) :=
  sylLe1

theorem W_le_P1 : subW wWords ≤ subW pWords1 := by
  intro y hy
  exact (mem_subW_iff_crMat pWords1_letters).2 (wFacts_cert.le (mem_W_iff_crMat.1 hy))

theorem mem_P1_iff_crMat {y : Cr} :
    y ∈ subW pWords1 ↔ crMat y ∈ matGrp pWords1 :=
  mem_subW_iff_crMat pWords1_letters

theorem card_matP1_le :
    Nat.card (matGrp pWords1) ≤ 2 ^ 17 :=
  (card_matGrp_le pWords1_letters).trans (le_of_eq (by rw [card_P1]; norm_num))

theorem mem_center_P1 {y : Cr} (hy : y ∈ subW pWords1)
    (hc : ∀ s ∈ subW pWords1, y * s = s * y) : y = 1 ∨ y = rep 1 ∨ y = rCr ∨ y = rCr * rep 1 := by
  have hz : ∀ z ∈ matGrp pWords1, crMat y * z = z * crMat y := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := matGrp_le_map pWords1_letters hz
    rw [← map_mul, ← map_mul, hc x hx]
  have h1 : crMat (rep 1) = repMat 1 := crMat_rep (by norm_num)
  have h0 : crMat rCr = repMat 0 := by rw [← rep_zero, crMat_rep (by norm_num)]
  rcases wFacts_cert.center card_matP1_le _ (mem_P1_iff_crMat.1 hy) hz with h | h | h | h
  · exact Or.inl (crMat_injective (by rw [h, map_one]))
  · exact Or.inr (Or.inl (crMat_injective (by rw [h, h1])))
  · exact Or.inr (Or.inr (Or.inl (crMat_injective (by rw [h, h0]))))
  · exact Or.inr (Or.inr (Or.inr (crMat_injective (by rw [h, map_mul, h0, h1]))))

end CFSG.RankThree.Co2
