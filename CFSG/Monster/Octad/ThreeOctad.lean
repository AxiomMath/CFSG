module

public import CFSG.Monster.Octad.EvenSubset
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import CFSG.Monster.Code.Bits
import Mathlib.FieldTheory.Finite.GaloisField

public noncomputable section

namespace CFSG.Monster.Octad

open Module

variable {I : Type*} [DecidableEq I]

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem zmod2_eq_add_of_add_add : ∀ a b c : ZMod 2, a + b + c = 0 → c = a + b := by
  decide

private theorem zmod2_add_eq_zero : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a + b = 0 := by decide

private theorem zmod2_two_cover : ∀ a b : ZMod 2, (a ≠ 0 ∨ b ≠ 0 ∨ a + b ≠ 0) →
    (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) + (if a + b ≠ 0 then 1 else 0) = 2 := by
  decide

private theorem zmod2_eq_of_add_eq_zero' : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

private theorem zmod2_iso4 : ∀ a b a' b' : ZMod 2,
    ((a = 0 ∧ a' = 0) ∨ (b = 0 ∧ b' = 0) ∨ (a + b = 0 ∧ a' + b' = 0)) →
      a * a' + (b * b' + (a + b) * (a' + b')) = 0 := by
  decide

private theorem zmod2_iso (a b c a' b' c' : ZMod 2) (h1 : a + b + c = 0) (h2 : a' + b' + c' = 0)
    (h3 : (a = 0 ∧ a' = 0) ∨ (b = 0 ∧ b' = 0) ∨ (c = 0 ∧ c' = 0)) :
    a * a' + (b * b' + c * c') = 0 := by
  rw [zmod2_eq_add_of_add_add a b c h1, zmod2_eq_add_of_add_add a' b' c' h2] at h3 ⊢
  exact zmod2_iso4 a b a' b' h3

private theorem zmod2_mul_aux : ∀ a b c : ZMod 2, a + b + c = 0 → c = 0 → a * b = b := by decide

private theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem ind_filter_eq {S : Finset I} {x : I → ZMod 2} (hx : ∀ i, i ∉ S → x i = 0) :
    ind (S.filter fun i => x i ≠ 0) = x := by
  funext i
  by_cases hi : i ∈ S
  · rcases zmod2_cases (x i) with h | h <;> simp [ind, hi, h]
  · simp [ind, hi, hx i hi]

omit [DecidableEq I] in
theorem evenSubsets_mono {S T : Finset I} (hST : S ⊆ T) {x : I → ZMod 2}
    (hx : x ∈ evenSubsets S) : x ∈ evenSubsets T := by
  refine ⟨fun i hi => hx.1 i fun h => hi (hST h), ?_⟩
  rw [← Finset.sum_subset hST fun i _ hi => hx.1 i hi]
  exact hx.2

theorem filter_mem_evenPowerset {S : Finset I} {x : I → ZMod 2} (hx : x ∈ evenSubsets S) :
    (S.filter fun i => x i ≠ 0) ∈ S.powerset.filter fun δ => Even δ.card := by
  have hsub : (S.filter fun i => x i ≠ 0) ⊆ S := Finset.filter_subset _ _
  refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even, ← sum_ind hsub, ind_filter_eq hx.1]
  exact hx.2

theorem filter_ind_ne_zero {S δ : Finset I} (h : δ ⊆ S) :
    (S.filter fun i => ind δ i ≠ 0) = δ := by
  ext i
  by_cases hi : i ∈ δ
  · simp [ind, hi, h hi]
  · simp [ind, hi]

def evenSubsetsEquiv (S : Finset I) :
    evenSubsets S ≃ (S.powerset.filter fun δ => Even δ.card) where
  toFun x := ⟨S.filter fun i => (x : I → ZMod 2) i ≠ 0, filter_mem_evenPowerset x.2⟩
  invFun δ := ⟨ind δ, ind_mem_evenSubsets (Finset.mem_powerset.1 (Finset.mem_filter.1 δ.2).1)
    (Finset.mem_filter.1 δ.2).2⟩
  left_inv x := Subtype.ext (ind_filter_eq x.2.1)
  right_inv δ :=
    Subtype.ext (filter_ind_ne_zero (Finset.mem_powerset.1 (Finset.mem_filter.1 δ.2).1))

theorem natCard_evenSubsets (S : Finset I) :
    Nat.card (evenSubsets S) = (S.powerset.filter fun δ => Even δ.card).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (evenSubsetsEquiv S)

omit [DecidableEq I] in
theorem card_even_powerset (S : Finset I) :
    (S.powerset.filter fun δ => Even δ.card).card =
      ∑ m ∈ Finset.range (S.card + 1), S.card.choose m • (if Even m then 1 else 0) := by
  rw [Finset.card_filter]
  exact Finset.sum_powerset_apply_card (fun n => if Even n then 1 else 0)

theorem finrank_evenSubsets_of_card_eq_twelve {S : Finset I} (hS : S.card = 12) :
    finrank (ZMod 2) (evenSubsets S) = 11 := by
  have h := FiniteField.pow_finrank_eq_natCard 2 (evenSubsets S)
  rw [natCard_evenSubsets, card_even_powerset, hS] at h
  have h2 : (∑ m ∈ Finset.range 13, (12 : ℕ).choose m • (if Even m then 1 else 0)) = 2 ^ 11 := by
    decide
  rw [h2] at h
  exact Nat.pow_right_injective le_rfl h

variable [Fintype I]

@[expose] def wordSupport (x : I → ZMod 2) : Finset I := Finset.univ.filter fun i => x i ≠ 0

omit [DecidableEq I] in
theorem mem_wordSupport {x : I → ZMod 2} {i : I} : i ∈ wordSupport x ↔ x i ≠ 0 := by
  simp [wordSupport]

omit [DecidableEq I] in
theorem card_wordSupport (x : I → ZMod 2) : (wordSupport x).card = hammingNorm x := rfl

theorem ind_wordSupport (x : I → ZMod 2) : ind (wordSupport x) = x :=
  ind_filter_eq fun i hi => absurd (Finset.mem_univ i) hi

theorem wordSupport_mul (x y : I → ZMod 2) :
    wordSupport (x * y) = wordSupport x ∩ wordSupport y := by
  ext i
  simp [wordSupport]

theorem hammingNorm_add_add (x y : I → ZMod 2) :
    hammingNorm (x + y) + 2 * (wordSupport x ∩ wordSupport y).card =
      hammingNorm x + hammingNorm y := by
  have h := wt_add Finset.univ x y
  rw [← wordSupport_mul, card_wordSupport, Code.hammingNorm_eq_sum_val (x * y),
    Code.hammingNorm_eq_sum_val x, Code.hammingNorm_eq_sum_val y,
    Code.hammingNorm_eq_sum_val (x + y)]
  exact h

omit [DecidableEq I] in
theorem wt_eq_hammingNorm {S : Finset I} {x : I → ZMod 2} (hx : ∀ i, i ∉ S → x i = 0) :
    wt S x = hammingNorm x := by
  rw [Code.hammingNorm_eq_sum_val, wt]
  exact Finset.sum_subset (Finset.subset_univ S) fun i _ hi => by rw [hx i hi]; rfl

omit [DecidableEq I] in
theorem sum_mul_eq_sum_univ {S : Finset I} {x y : I → ZMod 2} (hx : ∀ i, i ∉ S → x i = 0) :
    ∑ i ∈ S, x i * y i = ∑ i, x i * y i :=
  Finset.sum_subset (Finset.subset_univ S) fun i _ hi => by rw [hx i hi, zero_mul]

structure OctadTriple (C : Submodule (ZMod 2) (I → ZMod 2)) (d e f : I → ZMod 2) : Prop where
  dvd_four : ∀ c ∈ C, 4 ∣ hammingNorm c
  eight_le : ∀ c ∈ C, c ≠ 0 → 8 ≤ hammingNorm c
  d_mem : d ∈ C
  e_mem : e ∈ C
  f_mem : f ∈ C
  d_wt : hammingNorm d = 8
  e_wt : hammingNorm e = 8
  f_wt : hammingNorm f = 8
  sum_eq : d + e + f = 0

namespace OctadTriple

variable {C : Submodule (ZMod 2) (I → ZMod 2)} {d e f : I → ZMod 2}

omit [DecidableEq I] in
theorem rotate (h : OctadTriple C d e f) : OctadTriple C e f d :=
  ⟨h.dvd_four, h.eight_le, h.e_mem, h.f_mem, h.d_mem, h.e_wt, h.f_wt, h.d_wt, by
    rw [← h.sum_eq]; abel⟩

omit [DecidableEq I] in
theorem swap (h : OctadTriple C d e f) : OctadTriple C e d f :=
  ⟨h.dvd_four, h.eight_le, h.e_mem, h.d_mem, h.f_mem, h.e_wt, h.d_wt, h.f_wt, by
    rw [← h.sum_eq]; abel⟩

omit [DecidableEq I] in
theorem apply_eq (h : OctadTriple C d e f) (i : I) : f i = d i + e i :=
  zmod2_eq_add_of_add_add _ _ _ (by simpa using congrFun h.sum_eq i)

omit [DecidableEq I] in
theorem f_eq (h : OctadTriple C d e f) : f = d + e := funext h.apply_eq

theorem card_inter (h : OctadTriple C d e f) : (wordSupport d ∩ wordSupport e).card = 4 := by
  have := hammingNorm_add_add d e
  rw [← h.f_eq, h.f_wt, h.d_wt, h.e_wt] at this
  omega

omit [DecidableEq I] in
theorem not_mem_three (h : OctadTriple C d e f) {i : I} (hd : i ∈ wordSupport d)
    (he : i ∈ wordSupport e) : i ∉ wordSupport f := by
  rw [mem_wordSupport] at hd he ⊢
  rw [h.apply_eq, not_not]
  exact zmod2_add_eq_zero _ _ hd he

theorem wordSupport_f_subset (h : OctadTriple C d e f) :
    wordSupport f ⊆ wordSupport d ∪ wordSupport e := by
  intro i hi
  rw [mem_wordSupport, h.apply_eq] at hi
  rw [Finset.mem_union, mem_wordSupport, mem_wordSupport]
  by_contra hc
  push Not at hc
  rw [hc.1, hc.2, add_zero] at hi
  exact hi rfl

theorem card_union (h : OctadTriple C d e f) :
    (wordSupport d ∪ wordSupport e ∪ wordSupport f).card = 12 := by
  rw [Finset.union_eq_left.2 h.wordSupport_f_subset]
  have := Finset.card_union_add_card_inter (wordSupport d) (wordSupport e)
  rw [h.card_inter, card_wordSupport, card_wordSupport, h.d_wt, h.e_wt] at this
  omega

theorem two_cover (h : OctadTriple C d e f) {i : I}
    (hi : i ∈ wordSupport d ∪ wordSupport e ∪ wordSupport f) :
    (if i ∈ wordSupport d then 1 else 0) + (if i ∈ wordSupport e then 1 else 0) +
      (if i ∈ wordSupport f then 1 else 0) = 2 := by
  simp only [Finset.mem_union, mem_wordSupport, h.apply_eq] at hi ⊢
  exact zmod2_two_cover _ _ (by tauto)

theorem sum_card_inter (h : OctadTriple C d e f) {s : Finset I}
    (hs : s ⊆ wordSupport d ∪ wordSupport e ∪ wordSupport f) :
    (s ∩ wordSupport d).card + (s ∩ wordSupport e).card + (s ∩ wordSupport f).card =
      2 * s.card := by
  simp only [← Finset.filter_mem_eq_inter, Finset.card_filter, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun i hi => h.two_cover (hs hi), Finset.sum_const, smul_eq_mul,
    mul_comm]

theorem eq_of_wordSupport_subset (h : OctadTriple C d e f) {c : I → ZMod 2} (hc : c ∈ C)
    (hU : wordSupport c ⊆ wordSupport d ∪ wordSupport e ∪ wordSupport f) :
    c = 0 ∨ c = d ∨ c = e ∨ c = f := by
  have hw : hammingNorm c ≤ 12 := by
    rw [← card_wordSupport, ← h.card_union]
    exact Finset.card_le_card hU
  by_cases h0 : c = 0
  · exact Or.inl h0
  have h8 := h.eight_le c hc h0
  obtain ⟨k, hk⟩ := h.dvd_four c hc
  have hcases : hammingNorm c = 8 ∨ hammingNorm c = 12 := by omega
  rcases hcases with hc8 | hc12
  ·
    by_contra hne
    simp only [not_or] at hne
    have bound : ∀ x ∈ C, hammingNorm x = 8 → c ≠ x →
        (wordSupport c ∩ wordSupport x).card ≤ 4 := by
      intro x hx hx8 hcx
      have hne' : c + x ≠ 0 := fun h' => hcx (funext fun i =>
        zmod2_eq_of_add_eq_zero' _ _ (by simpa using congrFun h' i))
      have h1 := h.eight_le (c + x) (C.add_mem hc hx) hne'
      have h2 := hammingNorm_add_add c x
      omega
    have h1 := bound d h.d_mem h.d_wt hne.2.1
    have h2 := bound e h.e_mem h.e_wt hne.2.2.1
    have h3 := bound f h.f_mem h.f_wt hne.2.2.2
    have h4 := h.sum_card_inter hU
    rw [card_wordSupport, hc8] at h4
    omega
  ·
    exfalso
    have hSc : wordSupport c = wordSupport d ∪ wordSupport e ∪ wordSupport f :=
      Finset.eq_of_subset_of_card_le hU (by rw [h.card_union, card_wordSupport, hc12])
    have hinter : wordSupport c ∩ wordSupport d = wordSupport d := by
      rw [hSc]
      exact Finset.inter_eq_right.2 (Finset.subset_union_left.trans Finset.subset_union_left)
    have h1 := hammingNorm_add_add c d
    rw [hinter, card_wordSupport, h.d_wt, hc12] at h1
    have hne : c + d ≠ 0 := fun h' => by rw [h', hammingNorm_zero] at h1; omega
    have h2 := h.eight_le (c + d) (C.add_mem hc h.d_mem) hne
    omega

end OctadTriple

section Cocode

variable (C : Submodule (ZMod 2) (I → ZMod 2))

def cocodeMapOf (S : Finset I) (h : ind S ∈ C) : EvenQuot S →ₗ[ZMod 2] (I → ZMod 2) ⧸ C :=
  (complSpan S).liftQ (C.mkQ ∘ₗ (evenSubsets S).subtype) fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rcases (mem_complSpan_iff x).1 hx with h0 | h1
    · rw [Submodule.subtype_apply, h0]; exact C.zero_mem
    · rw [Submodule.subtype_apply, h1]; exact h

open Classical in
def cocodeMap (S : Finset I) : EvenQuot S →ₗ[ZMod 2] (I → ZMod 2) ⧸ C :=
  if h : ind S ∈ C then cocodeMapOf C S h else 0

variable {C}

omit [Fintype I] in
theorem cocodeMap_mk {S : Finset I} (h : ind S ∈ C) (x : evenSubsets S) :
    cocodeMap C S (mk S x) = Submodule.Quotient.mk (x : I → ZMod 2) := by
  rw [cocodeMap, dite_eq_left h]
  rfl

omit [Fintype I] in
theorem cocodeMap_cls {S δ : Finset I} (h : ind S ∈ C) (hδ : δ ⊆ S) (he : Even δ.card) :
    cocodeMap C S (cls S δ) = Submodule.Quotient.mk (ind δ) := by
  rw [cls_eq hδ he, cocodeMap_mk h]

end Cocode

abbrev TripleSpace (d e f : I → ZMod 2) : Type _ :=
  EvenQuot (wordSupport d) × EvenQuot (wordSupport e) × EvenQuot (wordSupport f)

def tripleQuad (d e f : I → ZMod 2) : QuadraticForm (ZMod 2) (TripleSpace d e f) :=
  (quadForm (wordSupport d)).prod ((quadForm (wordSupport e)).prod (quadForm (wordSupport f)))

def tripleCocode (C : Submodule (ZMod 2) (I → ZMod 2)) (d e f : I → ZMod 2) :
    TripleSpace d e f →ₗ[ZMod 2] (I → ZMod 2) ⧸ C :=
  (cocodeMap C (wordSupport d)).coprod
    ((cocodeMap C (wordSupport e)).coprod (cocodeMap C (wordSupport f)))

section Triple

variable {C : Submodule (ZMod 2) (I → ZMod 2)} {d e f : I → ZMod 2}

theorem tripleQuad_apply (u : EvenQuot (wordSupport d)) (v : EvenQuot (wordSupport e))
    (w : EvenQuot (wordSupport f)) :
    tripleQuad d e f (u, v, w) =
      quadForm (wordSupport d) u + quadForm (wordSupport e) v + quadForm (wordSupport f) w := by
  simp [tripleQuad, add_assoc]

theorem polarBilin_tripleQuad (x y : TripleSpace d e f) :
    QuadraticMap.polarBilin (tripleQuad d e f) x y =
      QuadraticMap.polarBilin (quadForm (wordSupport d)) x.1 y.1 +
        (QuadraticMap.polarBilin (quadForm (wordSupport e)) x.2.1 y.2.1 +
          QuadraticMap.polarBilin (quadForm (wordSupport f)) x.2.2 y.2.2) := by
  simp only [tripleQuad, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_prod]

theorem tripleCocode_apply (x : TripleSpace d e f) :
    tripleCocode C d e f x = cocodeMap C (wordSupport d) x.1 +
      (cocodeMap C (wordSupport e) x.2.1 + cocodeMap C (wordSupport f) x.2.2) := by
  simp [tripleCocode, LinearMap.coprod_apply]

end Triple

namespace OctadTriple

variable {C : Submodule (ZMod 2) (I → ZMod 2)} {d e f : I → ZMod 2}

theorem ind_d_mem (h : OctadTriple C d e f) : ind (wordSupport d) ∈ C := by
  rw [ind_wordSupport]; exact h.d_mem

theorem ind_e_mem (h : OctadTriple C d e f) : ind (wordSupport e) ∈ C := by
  rw [ind_wordSupport]; exact h.e_mem

theorem ind_f_mem (h : OctadTriple C d e f) : ind (wordSupport f) ∈ C := by
  rw [ind_wordSupport]; exact h.f_mem

omit [DecidableEq I] in
theorem card_d (h : OctadTriple C d e f) : (wordSupport d).card = 8 := by
  rw [card_wordSupport, h.d_wt]

omit [DecidableEq I] in
theorem card_e (h : OctadTriple C d e f) : (wordSupport e).card = 8 := by
  rw [card_wordSupport, h.e_wt]

omit [DecidableEq I] in
theorem card_f (h : OctadTriple C d e f) : (wordSupport f).card = 8 := by
  rw [card_wordSupport, h.f_wt]

theorem tripleCocode_mk (h : OctadTriple C d e f) (x : evenSubsets (wordSupport d))
    (y : evenSubsets (wordSupport e)) (z : evenSubsets (wordSupport f)) :
    tripleCocode C d e f (Octad.mk _ x, Octad.mk _ y, Octad.mk _ z) =
      Submodule.Quotient.mk ((x : I → ZMod 2) + y + z) := by
  rw [tripleCocode_apply, cocodeMap_mk h.ind_d_mem, cocodeMap_mk h.ind_e_mem,
    cocodeMap_mk h.ind_f_mem, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, add_assoc]

omit [Fintype I] in
theorem mk_ind_self (S : Finset I) (hS : Even S.card) :
    Octad.mk S ⟨ind S, ind_mem_evenSubsets subset_rfl hS⟩ = 0 :=
  (mk_eq_zero_iff _).2 ((mem_complSpan_iff _).2 (Or.inr rfl))

theorem exists_normal_rep (h : OctadTriple C d e f) {k : TripleSpace d e f}
    (hk : k ∈ LinearMap.ker (tripleCocode C d e f)) :
    ∃ x : evenSubsets (wordSupport d), ∃ y : evenSubsets (wordSupport e),
      ∃ z : evenSubsets (wordSupport f),
        k = (Octad.mk _ x, Octad.mk _ y, Octad.mk _ z) ∧ (x : I → ZMod 2) + y + z = 0 := by
  obtain ⟨k₁, k₂, k₃⟩ := k
  obtain ⟨x, rfl⟩ := mk_surjective _ k₁
  obtain ⟨y, rfl⟩ := mk_surjective _ k₂
  obtain ⟨z, rfl⟩ := mk_surjective _ k₃
  rw [LinearMap.mem_ker, h.tripleCocode_mk, Submodule.Quotient.mk_eq_zero] at hk
  have hU : wordSupport ((x : I → ZMod 2) + (y : I → ZMod 2) + (z : I → ZMod 2)) ⊆
      wordSupport d ∪ wordSupport e ∪ wordSupport f := by
    intro i hi
    rw [mem_wordSupport] at hi
    by_contra hiU
    simp only [Finset.mem_union, not_or] at hiU
    apply hi
    rw [Pi.add_apply, Pi.add_apply, x.2.1 i hiU.1.1, y.2.1 i hiU.1.2, z.2.1 i hiU.2, add_zero,
      add_zero]
  have hd8 : Even (wordSupport d).card := by rw [h.card_d]; decide
  have he8 : Even (wordSupport e).card := by rw [h.card_e]; decide
  have hself : ∀ v : I → ZMod 2, v + v = 0 := fun v => funext fun i => zmod2_add_self (v i)
  set dv : evenSubsets (wordSupport d) := ⟨ind (wordSupport d), ind_mem_evenSubsets subset_rfl hd8⟩
  set ev : evenSubsets (wordSupport e) := ⟨ind (wordSupport e), ind_mem_evenSubsets subset_rfl he8⟩
  have hdv : (dv : I → ZMod 2) = d := ind_wordSupport d
  have hev : (ev : I → ZMod 2) = e := ind_wordSupport e
  rcases h.eq_of_wordSupport_subset hk hU with h0 | hd | he | hf
  · exact ⟨x, y, z, rfl, h0⟩
  · refine ⟨x + dv, y, z, ?_, ?_⟩
    · rw [map_add, mk_ind_self _ hd8, add_zero]
    · rw [Submodule.coe_add, hdv,
        show (x : I → ZMod 2) + d + (y : I → ZMod 2) + (z : I → ZMod 2) =
          ((x : I → ZMod 2) + (y : I → ZMod 2) + (z : I → ZMod 2)) + d by abel, hd, hself]
  · refine ⟨x, y + ev, z, ?_, ?_⟩
    · rw [map_add (Octad.mk _), mk_ind_self _ he8, add_zero]
    · rw [Submodule.coe_add, hev,
        show (x : I → ZMod 2) + ((y : I → ZMod 2) + e) + (z : I → ZMod 2) =
          ((x : I → ZMod 2) + (y : I → ZMod 2) + (z : I → ZMod 2)) + e by abel, he, hself]
  · refine ⟨x + dv, y + ev, z, ?_, ?_⟩
    · rw [map_add, map_add (Octad.mk _), mk_ind_self _ hd8, mk_ind_self _ he8, add_zero, add_zero]
    · rw [Submodule.coe_add, Submodule.coe_add, hdv, hev,
        show (x : I → ZMod 2) + d + ((y : I → ZMod 2) + e) + (z : I → ZMod 2) =
          ((x : I → ZMod 2) + (y : I → ZMod 2) + (z : I → ZMod 2)) + (d + e) by abel, hf,
        ← h.f_eq, hself]

theorem polarBilin_mk_eq_zero (h : OctadTriple C d e f) (x x' : evenSubsets (wordSupport d))
    (y y' : evenSubsets (wordSupport e)) (z z' : evenSubsets (wordSupport f))
    (hs : (x : I → ZMod 2) + y + z = 0) (hs' : (x' : I → ZMod 2) + y' + z' = 0) :
    QuadraticMap.polarBilin (tripleQuad d e f) (Octad.mk _ x, Octad.mk _ y, Octad.mk _ z)
      (Octad.mk _ x', Octad.mk _ y', Octad.mk _ z') = 0 := by
  have h4d : 4 ∣ (wordSupport d).card := by rw [h.card_d]; norm_num
  have h4e : 4 ∣ (wordSupport e).card := by rw [h.card_e]; norm_num
  have h4f : 4 ∣ (wordSupport f).card := by rw [h.card_f]; norm_num
  simp only [polarBilin_tripleQuad]
  rw [polarBilin_quadForm_mk h4d, polarBilin_quadForm_mk h4e, polarBilin_quadForm_mk h4f,
    dotForm_apply, dotForm_apply, dotForm_apply, sum_mul_eq_sum_univ x.2.1,
    sum_mul_eq_sum_univ y.2.1, sum_mul_eq_sum_univ z.2.1, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => zmod2_iso _ _ _ _ _ _ (by simpa using congrFun hs i)
    (by simpa using congrFun hs' i) ?_
  by_cases hdi : i ∈ wordSupport d
  · by_cases hei : i ∈ wordSupport e
    · exact Or.inr (Or.inr ⟨z.2.1 i (h.not_mem_three hdi hei), z'.2.1 i (h.not_mem_three hdi hei)⟩)
    · exact Or.inr (Or.inl ⟨y.2.1 i hei, y'.2.1 i hei⟩)
  · exact Or.inl ⟨x.2.1 i hdi, x'.2.1 i hdi⟩

theorem tripleQuad_mk_eq (h : OctadTriple C d e f) (x : evenSubsets (wordSupport d))
    (y : evenSubsets (wordSupport e)) (z : evenSubsets (wordSupport f))
    (hs : (x : I → ZMod 2) + y + z = 0) :
    tripleQuad d e f (Octad.mk _ x, Octad.mk _ y, Octad.mk _ z) =
      QuadraticMap.polarBilin (tripleQuad d e f)
        (0, cls (wordSupport e) (wordSupport d ∩ wordSupport e), 0)
        (Octad.mk _ x, Octad.mk _ y, Octad.mk _ z) := by
  have h4d : 4 ∣ (wordSupport d).card := by rw [h.card_d]; norm_num
  have h4e : 4 ∣ (wordSupport e).card := by rw [h.card_e]; norm_num
  have h4f : 4 ∣ (wordSupport f).card := by rw [h.card_f]; norm_num
  have hω : wordSupport d ∩ wordSupport e ⊆ wordSupport e := Finset.inter_subset_right
  have hωe : Even (wordSupport d ∩ wordSupport e).card := by rw [h.card_inter]; decide
  rw [tripleQuad_apply, quadForm_mk h4d, quadForm_mk h4e, quadForm_mk h4f, evenQuad_apply,
    evenQuad_apply, evenQuad_apply]
  simp only [polarBilin_tripleQuad, map_zero, LinearMap.zero_apply, zero_add, add_zero]
  rw [cls_eq hω hωe, polarBilin_quadForm_mk h4e, dotForm_apply,
    wt_eq_hammingNorm x.2.1, wt_eq_hammingNorm y.2.1, wt_eq_hammingNorm z.2.1]
  have hz : (z : I → ZMod 2) = (x : I → ZMod 2) + (y : I → ZMod 2) :=
    funext fun i => zmod2_eq_add_of_add_add _ _ _ (by simpa using congrFun hs i)
  have hx2 : Even (hammingNorm (x : I → ZMod 2)) := wt_eq_hammingNorm x.2.1 ▸ even_wt x.2
  have hy2 : Even (hammingNorm (y : I → ZMod 2)) := wt_eq_hammingNorm y.2.1 ▸ even_wt y.2
  have hN : ((wordSupport (x : I → ZMod 2) ∩ wordSupport (y : I → ZMod 2)).card : ZMod 2) =
      ∑ i ∈ wordSupport e, ind (wordSupport d ∩ wordSupport e) i * (y : I → ZMod 2) i := by
    rw [← wordSupport_mul, card_wordSupport, ← Code.sum_eq_hammingNorm,
      sum_mul_eq_sum_univ (x := ind (wordSupport d ∩ wordSupport e)) fun i hi => by
        rw [ind_apply, ite_eq_right fun h' => hi (hω h')]]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, ind_apply]
    by_cases hi : i ∈ wordSupport d ∩ wordSupport e
    · rw [ite_eq_left hi, one_mul]
      obtain ⟨hdi, hei⟩ := Finset.mem_inter.1 hi
      exact zmod2_mul_aux _ _ _ (by simpa using congrFun hs i)
        (z.2.1 i (h.not_mem_three hdi hei))
    · rw [ite_eq_right hi, zero_mul]
      rw [Finset.mem_inter, not_and_or] at hi
      rcases hi with hdi | hei
      · rw [x.2.1 i hdi, zero_mul]
      · rw [y.2.1 i hei, mul_zero]
  rw [hz, ← hN]
  have hadd := hammingNorm_add_add (x : I → ZMod 2) (y : I → ZMod 2)
  obtain ⟨a, ha⟩ := hx2
  obtain ⟨b, hb⟩ := hy2
  have key : hammingNorm ((x : I → ZMod 2) + (y : I → ZMod 2)) / 2 +
      (wordSupport (x : I → ZMod 2) ∩ wordSupport (y : I → ZMod 2)).card =
      hammingNorm (x : I → ZMod 2) / 2 + hammingNorm (y : I → ZMod 2) / 2 := by
    omega
  have key' := congrArg (Nat.cast : ℕ → ZMod 2) key
  push_cast at key'
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (-1 : ZMod 2) * key' +
    ((hammingNorm ((x : I → ZMod 2) + (y : I → ZMod 2)) / 2 : ℕ) : ZMod 2) * h2

theorem tripleQuad_add_eq_zero (h : OctadTriple C d e f) {k : TripleSpace d e f}
    (hk : k ∈ LinearMap.ker (tripleCocode C d e f)) :
    tripleQuad d e f ((0, cls (wordSupport e) (wordSupport d ∩ wordSupport e), 0) + k) = 0 := by
  have h4e : 4 ∣ (wordSupport e).card := by rw [h.card_e]; norm_num
  have hω : wordSupport d ∩ wordSupport e ⊆ wordSupport e := Finset.inter_subset_right
  have hωe : Even (wordSupport d ∩ wordSupport e).card := by rw [h.card_inter]; decide
  obtain ⟨x, y, z, rfl, hs⟩ := h.exists_normal_rep hk
  rw [quad_add, h.tripleQuad_mk_eq x y z hs, tripleQuad_apply, map_zero, map_zero, zero_add,
    add_zero, quadForm_cls h4e hω hωe, h.card_inter, add_assoc, zmod2_add_self, add_zero]
  decide

theorem finrank_tripleSpace (h : OctadTriple C d e f) :
    finrank (ZMod 2) (TripleSpace d e f) = 18 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_evenQuot h.card_d,
    finrank_evenQuot h.card_e, finrank_evenQuot h.card_f]

theorem range_tripleCocode_le (h : OctadTriple C d e f) :
    LinearMap.range (tripleCocode C d e f) ≤
      (evenSubsets (wordSupport d ∪ wordSupport e ∪ wordSupport f)).map C.mkQ := by
  rintro _ ⟨⟨k₁, k₂, k₃⟩, rfl⟩
  obtain ⟨x, rfl⟩ := mk_surjective _ k₁
  obtain ⟨y, rfl⟩ := mk_surjective _ k₂
  obtain ⟨z, rfl⟩ := mk_surjective _ k₃
  rw [h.tripleCocode_mk]
  refine Submodule.mem_map.2 ⟨_, add_mem (add_mem ?_ ?_) ?_, rfl⟩
  · exact evenSubsets_mono (Finset.subset_union_left.trans Finset.subset_union_left) x.2
  · exact evenSubsets_mono (Finset.subset_union_right.trans Finset.subset_union_left) y.2
  · exact evenSubsets_mono Finset.subset_union_right z.2

theorem finrank_map_mkQ_le (h : OctadTriple C d e f) :
    finrank (ZMod 2)
      ((evenSubsets (wordSupport d ∪ wordSupport e ∪ wordSupport f)).map C.mkQ) ≤ 9 := by
  set W := evenSubsets (wordSupport d ∪ wordSupport e ∪ wordSupport f) with hW
  have hW11 : finrank (ZMod 2) W = 11 := finrank_evenSubsets_of_card_eq_twelve h.card_union
  have hrn := LinearMap.finrank_range_add_finrank_ker (C.mkQ.domRestrict W)
  rw [LinearMap.range_domRestrict, hW11] at hrn
  have hdW : d ∈ W := by
    rw [← ind_wordSupport d]
    exact evenSubsets_mono (Finset.subset_union_left.trans Finset.subset_union_left)
      (ind_mem_evenSubsets subset_rfl (by rw [h.card_d]; decide))
  have heW : e ∈ W := by
    rw [← ind_wordSupport e]
    exact evenSubsets_mono (Finset.subset_union_right.trans Finset.subset_union_left)
      (ind_mem_evenSubsets subset_rfl (by rw [h.card_e]; decide))
  have hmem : ∀ v (hv : v ∈ W), v ∈ C →
      (⟨v, hv⟩ : W) ∈ LinearMap.ker (C.mkQ.domRestrict W) := by
    intro v hv hvC
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hvC
  have hamb : LinearIndependent (ZMod 2) ![d, e] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    rcases zmod2_cases s with rfl | rfl <;> rcases zmod2_cases t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp only [zero_smul, one_smul, zero_add] at hst
      have := h.e_wt
      rw [hst, hammingNorm_zero] at this
      omega
    · exfalso
      simp only [zero_smul, one_smul, add_zero] at hst
      have := h.d_wt
      rw [hst, hammingNorm_zero] at this
      omega
    · exfalso
      simp only [one_smul] at hst
      have := h.f_wt
      rw [h.f_eq, hst, hammingNorm_zero] at this
      omega
  let v : Fin 2 → LinearMap.ker (C.mkQ.domRestrict W) :=
    ![⟨⟨d, hdW⟩, hmem d hdW h.d_mem⟩, ⟨⟨e, heW⟩, hmem e heW h.e_mem⟩]
  have hcomp : (W.subtype ∘ₗ (LinearMap.ker (C.mkQ.domRestrict W)).subtype) ∘ v = ![d, e] := by
    funext i
    fin_cases i <;> rfl
  have hli : LinearIndependent (ZMod 2) v :=
    LinearIndependent.of_comp (W.subtype ∘ₗ (LinearMap.ker (C.mkQ.domRestrict W)).subtype)
      (by rw [hcomp]; exact hamb)
  have h2 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h2
  omega

theorem nine_le_finrank_ker (h : OctadTriple C d e f) :
    9 ≤ finrank (ZMod 2) (LinearMap.ker (tripleCocode C d e f)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (tripleCocode C d e f)
  rw [h.finrank_tripleSpace] at hrn
  have := (Submodule.finrank_mono h.range_tripleCocode_le).trans h.finrank_map_mkQ_le
  omega

theorem ker_le_orthogonal (h : OctadTriple C d e f) :
    LinearMap.ker (tripleCocode C d e f) ≤
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (tripleQuad d e f))
        (LinearMap.ker (tripleCocode C d e f)) := by
  intro m hm
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨x, y, z, rfl, hs⟩ := h.exists_normal_rep hn
  obtain ⟨x', y', z', rfl, hs'⟩ := h.exists_normal_rep hm
  exact h.polarBilin_mk_eq_zero x x' y y' z z' hs hs'

theorem polarBilin_tripleQuad_nondegenerate (h : OctadTriple C d e f) :
    (QuadraticMap.polarBilin (tripleQuad d e f)).Nondegenerate := by
  have h4 : ∀ x : I → ZMod 2, hammingNorm x = 8 →
      4 ∣ (wordSupport x).card ∧ (wordSupport x).Nonempty := fun x hx =>
    ⟨by rw [card_wordSupport, hx]; norm_num,
      Finset.card_pos.1 (by rw [card_wordSupport, hx]; norm_num)⟩
  have hd := polarBilin_quadForm_separatingLeft (h4 d h.d_wt).1 (h4 d h.d_wt).2
  have he := polarBilin_quadForm_separatingLeft (h4 e h.e_wt).1 (h4 e h.e_wt).2
  have hf := polarBilin_quadForm_separatingLeft (h4 f h.f_wt).1 (h4 f h.f_wt).2
  have hl : (QuadraticMap.polarBilin (tripleQuad d e f)).SeparatingLeft := by
    rintro ⟨x₁, x₂, x₃⟩ hx
    have h1 : x₁ = 0 := hd x₁ fun y => by
      have := hx (y, 0, 0)
      rw [polarBilin_tripleQuad] at this
      simpa using this
    have h2 : x₂ = 0 := he x₂ fun y => by
      have := hx (0, y, 0)
      rw [polarBilin_tripleQuad] at this
      simpa using this
    have h3 : x₃ = 0 := hf x₃ fun y => by
      have := hx (0, 0, y)
      rw [polarBilin_tripleQuad] at this
      simpa using this
    rw [h1, h2, h3]
    rfl
  exact ⟨hl, fun y hy => hl y fun x => by rw [polarBilin_symm]; exact hy x⟩

end OctadTriple

theorem three_octad_lagrangian_correspondence (C : Submodule (ZMod 2) (I → ZMod 2))
    (hC4 : ∀ c ∈ C, 4 ∣ hammingNorm c) (hC8 : ∀ c ∈ C, c ≠ 0 → 8 ≤ hammingNorm c)
    {d e f : I → ZMod 2} (hd : d ∈ C) (he : e ∈ C) (hf : f ∈ C)
    (hd8 : hammingNorm d = 8) (he8 : hammingNorm e = 8) (hf8 : hammingNorm f = 8)
    (hdef : d + e + f = 0) :
    let q := tripleQuad d e f
    let b := QuadraticMap.polarBilin q
    let j := tripleCocode C d e f
    let K := LinearMap.ker j
    let ω := wordSupport d ∩ wordSupport e
    let a₀ : TripleSpace d e f := (0, cls (wordSupport e) ω, 0)
    let U := wordSupport d ∪ wordSupport e ∪ wordSupport f
    (∀ u v w, q (u, v, w) =
      quadForm (wordSupport d) u + quadForm (wordSupport e) v + quadForm (wordSupport f) w) ∧
    (∀ δ ε φ, δ ⊆ wordSupport d → Even δ.card → ε ⊆ wordSupport e → Even ε.card →
      φ ⊆ wordSupport f → Even φ.card →
      j (cls _ δ, cls _ ε, cls _ φ) = Submodule.Quotient.mk (ind δ + ind ε + ind φ)) ∧
    finrank (ZMod 2) (TripleSpace d e f) = 18 ∧
    finrank (ZMod 2) K = 9 ∧
    LinearMap.BilinForm.orthogonal b K = K ∧
    j a₀ = Submodule.Quotient.mk (ind ω) ∧
    (∀ k ∈ K, q (a₀ + k) = 0) ∧
    (∀ δ ε φ, δ ⊆ wordSupport d → Even δ.card → ε ⊆ wordSupport e → Even ε.card →
      φ ⊆ wordSupport f → Even φ.card →
      b a₀ (cls _ δ, cls _ ε, cls _ φ) = ((wordSupport d ∩ ε).card : ZMod 2)) ∧
    U.card = 12 ∧
    ∀ c ∈ C, (wordSupport c ⊆ U ↔ c = 0 ∨ c = d ∨ c = e ∨ c = f) := by
  dsimp only
  have h : OctadTriple C d e f := ⟨hC4, hC8, hd, he, hf, hd8, he8, hf8, hdef⟩
  have h4e : 4 ∣ (wordSupport e).card := by rw [h.card_e]; norm_num
  have hω : wordSupport d ∩ wordSupport e ⊆ wordSupport e := Finset.inter_subset_right
  have hωe : Even (wordSupport d ∩ wordSupport e).card := by rw [h.card_inter]; decide
  have hiso := h.ker_le_orthogonal
  have hperp := LinearMap.BilinForm.finrank_orthogonal h.polarBilin_tripleQuad_nondegenerate
    (LinearMap.ker (tripleCocode C d e f))
  rw [h.finrank_tripleSpace] at hperp
  have h9 := h.nine_le_finrank_ker
  have hle := Submodule.finrank_mono hiso
  have hK : finrank (ZMod 2) (LinearMap.ker (tripleCocode C d e f)) = 9 := by omega
  refine ⟨fun u v w => tripleQuad_apply u v w, fun δ ε φ hδ hδe hε hεe hφ hφe => ?_,
    h.finrank_tripleSpace, hK, ?_, ?_, fun k hk => h.tripleQuad_add_eq_zero hk,
    fun δ ε φ hδ hδe hε hεe hφ hφe => ?_, h.card_union, fun c hc => ⟨?_, ?_⟩⟩
  · rw [tripleCocode_apply]
    dsimp only
    rw [cocodeMap_cls h.ind_d_mem hδ hδe, cocodeMap_cls h.ind_e_mem hε hεe,
      cocodeMap_cls h.ind_f_mem hφ hφe, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add,
      add_assoc]
  · exact (Submodule.eq_of_le_of_finrank_le hiso (by omega)).symm
  · rw [tripleCocode_apply]
    dsimp only
    rw [map_zero, map_zero, zero_add, add_zero]
    exact cocodeMap_cls h.ind_e_mem hω hωe
  · rw [polarBilin_tripleQuad]
    dsimp only
    rw [map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply, zero_add, add_zero,
      polarBilin_quadForm_cls h4e hω hωe hε hεe, Finset.inter_assoc, Finset.inter_eq_right.2 hε]
  · exact h.eq_of_wordSupport_subset hc
  · rintro (rfl | rfl | rfl | rfl)
    · intro i hi
      simp [wordSupport] at hi
    · exact Finset.subset_union_left.trans Finset.subset_union_left
    · exact Finset.subset_union_right.trans Finset.subset_union_left
    · exact Finset.subset_union_right

end CFSG.Monster.Octad
