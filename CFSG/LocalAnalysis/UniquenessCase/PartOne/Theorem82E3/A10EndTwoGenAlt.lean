module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath

import CFSG.GF2Type.Smith1979W3.CaseD.Jordan
import CFSG.RankThree.PartTwo.Sec13.Item131bProofF
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.SpRankThree
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen

open Equiv Equiv.Perm Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase
open scoped Pointwise

namespace Star

open Equiv Equiv.Perm Subgroup MulAction
open scoped Pointwise

variable {n : ℕ} [NeZero n]

private def x (k : Fin n) : Perm (Fin n) := swap 0 k * swap 0 1

private def starSet (n : ℕ) [NeZero n] : Set (Perm (Fin n)) :=
  {σ | ∃ k : Fin n, k ≠ 0 ∧ k ≠ 1 ∧ σ = x k}

private theorem two_ne_zero (hn : 3 ≤ n) : (2 : Fin n) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  change 2 % n = 0 at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

private theorem two_ne_one (hn : 3 ≤ n) : (2 : Fin n) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  change 2 % n = 1 % n at this
  rw [Nat.mod_eq_of_lt (by omega : 2 < n), Nat.mod_eq_of_lt (by omega : 1 < n)] at this
  omega

private theorem zero_ne_one (hn : 3 ≤ n) : (0 : Fin n) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  change 0 = 1 % n at this
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at this
  omega

private theorem x_isThreeCycle (hn : 3 ≤ n) {k : Fin n} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (x k).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (Ne.symm hk0) (zero_ne_one hn) hk1

private theorem x_mem_alt (hn : 3 ≤ n) {k : Fin n} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    x k ∈ alternatingGroup (Fin n) :=
  (x_isThreeCycle hn hk0 hk1).mem_alternatingGroup

private theorem x_zero (hn : 3 ≤ n) {k : Fin n} (hk1 : k ≠ 1) : x k (0 : Fin n) = 1 := by
  rw [x, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (zero_ne_one hn)) (Ne.symm hk1)]

private theorem x_self (hn : 3 ≤ n) {k : Fin n} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    x k k = 0 := by
  rw [x, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hk0 hk1,
    Equiv.swap_apply_right]

private theorem x_one (hn : 3 ≤ n) {k : Fin n} (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    x k (1 : Fin n) = k := by
  rw [x, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]

private theorem point_map (hn : 3 ≤ n) (a : Fin n) :
    ∃ h : Subgroup.closure (starSet n), h • (1 : Fin n) = a := by
  classical
  have h2 : x (2 : Fin n) ∈ Subgroup.closure (starSet n) :=
    Subgroup.subset_closure ⟨2, two_ne_zero hn, two_ne_one hn, rfl⟩
  by_cases ha0 : a = 0
  · refine ⟨⟨(x (2 : Fin n)) ^ 2, Subgroup.pow_mem _ h2 2⟩, ?_⟩
    subst a
    show ((x (2 : Fin n)) ^ 2) (1 : Fin n) = 0
    rw [pow_two, Equiv.Perm.mul_apply, x_one hn (two_ne_zero hn) (two_ne_one hn),
      x_self hn (two_ne_zero hn) (two_ne_one hn)]
  by_cases ha1 : a = 1
  · refine ⟨1, ?_⟩
    simp [ha1]
  · refine ⟨⟨x a, Subgroup.subset_closure ⟨a, ha0, ha1, rfl⟩⟩, ?_⟩
    show x a (1 : Fin n) = a
    exact x_one hn ha0 ha1

private theorem star_transitive (hn : 3 ≤ n) :
    IsPretransitive (Subgroup.closure (starSet n)) (Fin n) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨ha, hha⟩ := point_map (n := n) hn a
  obtain ⟨hb, hhb⟩ := point_map (n := n) hn b
  refine ⟨hb * ha⁻¹, ?_⟩
  calc (hb * ha⁻¹) • a = hb • (ha⁻¹ • a) := by rw [mul_smul]
    _ = hb • (1 : Fin n) := by
      have : ha⁻¹ • a = 1 := by
        rw [← hha, ← mul_smul, inv_mul_cancel, one_smul]
      rw [this]
    _ = b := hhb

private theorem block_eq_univ_of_one (hn : 3 ≤ n) {B : Set (Fin n)}
    (hB : IsBlock (Subgroup.closure (starSet n)) B) (h0 : (0 : Fin n) ∈ B)
    (h1 : (1 : Fin n) ∈ B) : B = Set.univ := by
  have hall : ∀ k : Fin n, k ∈ B := by
    intro k
    by_cases hk0 : k = 0
    · rw [hk0]; exact h0
    by_cases hk1 : k = 1
    · rw [hk1]; exact h1
    · have hmem : x k ∈ Subgroup.closure (starSet n) :=
        Subgroup.subset_closure ⟨k, hk0, hk1, rfl⟩
      have hx0 : x k • (0 : Fin n) = 1 := x_zero hn hk1
      have hx1 : x k • (1 : Fin n) = k := x_one hn hk0 hk1
      let hxH : ↥(Subgroup.closure (starSet n)) := ⟨x k, hmem⟩
      have h1mem : (1 : Fin n) ∈ x k • B := by
        rw [← hx0]
        exact Set.smul_mem_smul_set h0
      have hinter : ((x k • B) ∩ B).Nonempty := ⟨1, h1mem, h1⟩
      have heq : x k • B = B := hB.smul_eq_of_nonempty (g := hxH) hinter
      have : x k • (1 : Fin n) ∈ x k • B := Set.smul_mem_smul_set h1
      rw [hx1, heq] at this
      exact this
  exact Set.eq_univ_of_forall hall

private theorem block_eq_univ_of_zero (hn : 3 ≤ n) {B : Set (Fin n)}
    (hB : IsBlock (Subgroup.closure (starSet n)) B) (h0 : (0 : Fin n) ∈ B)
    (hnt : ∃ b ∈ B, b ≠ 0) : B = Set.univ := by
  obtain ⟨b, hb, hb0⟩ := hnt
  by_cases hb1 : b = 1
  · exact block_eq_univ_of_one hn hB h0 (by rwa [hb1] at hb)
  · have hmem : x b ∈ Subgroup.closure (starSet n) :=
      Subgroup.subset_closure ⟨b, hb0, hb1, rfl⟩
    have hx0 : x b • (0 : Fin n) = 1 := x_zero hn hb1
    have hxb : x b • b = 0 := x_self hn hb0 hb1
    let hxH : ↥(Subgroup.closure (starSet n)) := ⟨x b, hmem⟩
    have h0mem : (0 : Fin n) ∈ x b • B := by
      rw [← hxb]
      exact Set.smul_mem_smul_set hb
    have hinter : ((x b • B) ∩ B).Nonempty := ⟨0, h0mem, h0⟩
    have heq : x b • B = B := hB.smul_eq_of_nonempty (g := hxH) hinter
    have : x b • (0 : Fin n) ∈ x b • B := Set.smul_mem_smul_set h0
    rw [hx0, heq] at this
    exact block_eq_univ_of_one hn hB h0 this

private theorem star_closure_isPreprimitive (hn : 3 ≤ n) :
    IsPreprimitive (Subgroup.closure (starSet n)) (Fin n) := by
  classical
  have htr := star_transitive hn
  refine { toIsPretransitive := htr, isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  by_cases hBsub : B.Subsingleton
  · exact Or.inl hBsub
  · right
    rw [Set.not_subsingleton_iff] at hBsub
    obtain ⟨b0, hb0, b1, hb1, hb01⟩ := hBsub
    obtain ⟨g, hg0⟩ := htr.exists_smul_eq b0 0
    set B' := g • B with hB'def
    have hB' : IsBlock (Subgroup.closure (starSet n)) B' := hB.translate g
    have h0B' : (0 : Fin n) ∈ B' := ⟨b0, hb0, hg0⟩
    have hnt : ∃ b ∈ B', b ≠ 0 := by
      refine ⟨g • b1, Set.smul_mem_smul_set hb1, ?_⟩
      intro h
      apply hb01
      exact (g : Perm (Fin n)).injective (h.trans hg0.symm).symm
    have hB'univ : B' = Set.univ := block_eq_univ_of_zero hn hB' h0B' hnt
    have hB_eq : B = g⁻¹ • B' := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, hB'def, inv_inv, Set.smul_mem_smul_set_iff]
    rw [hB_eq, hB'univ, Set.smul_set_univ]

private theorem star_closure_eq_alternating (hn : 3 ≤ n) :
    Subgroup.closure (starSet n) = alternatingGroup (Fin n) := by
  classical
  set H := Subgroup.closure (starSet n) with hH
  have hH_le : H ≤ alternatingGroup (Fin n) := by
    rw [hH, Subgroup.closure_le]
    rintro σ ⟨k, hk0, hk1, rfl⟩
    exact x_mem_alt hn hk0 hk1
  have hx2 : x (2 : Fin n) ∈ H :=
    Subgroup.subset_closure ⟨2, two_ne_zero hn, two_ne_one hn, rfl⟩
  have hAlt_le : alternatingGroup (Fin n) ≤ H :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
      (star_closure_isPreprimitive hn)
      (x_isThreeCycle hn (two_ne_zero hn) (two_ne_one hn)) hx2
  exact le_antisymm hH_le hAlt_le

end Star

private lemma support_closure_subset {n : ℕ} [NeZero n] {S : Finset (Fin n)}
    {a b : Perm (Fin n)} (ha : a.support ⊆ S) (hb : b.support ⊆ S) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set (Perm (Fin n))), x.support ⊆ S := by
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x.support ⊆ S) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  · simp
  · intro y z hy hz hyS hzS
    exact (Equiv.Perm.support_mul_le y z).trans (Finset.union_subset hyS hzS)
  · intro y hy hyS
    rwa [Equiv.Perm.support_inv]

private lemma map_closure_pair {n : ℕ} [NeZero n] {a b : alternatingGroup (Fin n)}
    {pa pb : Perm (Fin n)} (ha : (a : Perm (Fin n)) = pa) (hb : (b : Perm (Fin n)) = pb) :
    (Subgroup.closure ({a, b} : Set (alternatingGroup (Fin n)))).map
      (alternatingGroup (Fin n)).subtype =
      Subgroup.closure ({pa, pb} : Set (Perm (Fin n))) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl <;> simp [ha, hb]
  · rintro (rfl | rfl)
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨b, Or.inr rfl, hb⟩

private lemma closure_three_eq_sup {X : Type*} [Group X] (a b c : X) :
    Subgroup.closure ({a, b, c} : Set X) = zpowers a ⊔ zpowers b ⊔ zpowers c := by
  rw [show ({a, b, c} : Set X) = ({a, b} : Set _) ∪ {c} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;> tauto]
  rw [Subgroup.closure_union]
  rw [show ({a, b} : Set X) = ({a} : Set _) ∪ {b} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;> tauto]
  rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure]

private lemma mem_centGenI_of_centralizer {X : Type*} [Group X] {A0 F : Subgroup X} {x : X}
    (hFA : F ≤ A0) (hA0card : Nat.card A0 = 27) (hFcard : Nat.card F = 9)
    (hx : x ∈ Subgroup.centralizer (F : Set X)) :
    x ∈ GL83.CompFam.centGenI 3 A0 ⊤ := by
  have hcard : Nat.card A0 ≤ 3 * Nat.card F := by norm_num [hA0card, hFcard]
  have hmem : x ∈ (⊤ : Subgroup X) ⊓ Subgroup.centralizer (F : Set X) := ⟨trivial, hx⟩
  exact GL83.CompFam.le_centGenI (L := ⊤) hFA hcard hmem

private lemma map_closure_triple {n : ℕ} [NeZero n] {a b c : alternatingGroup (Fin n)}
    {pa pb pc : Perm (Fin n)} (ha : (a : Perm (Fin n)) = pa) (hb : (b : Perm (Fin n)) = pb)
    (hc : (c : Perm (Fin n)) = pc) :
    (Subgroup.closure ({a, b, c} : Set (alternatingGroup (Fin n)))).map
      (alternatingGroup (Fin n)).subtype =
      Subgroup.closure ({pa, pb, pc} : Set (Perm (Fin n))) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl | rfl), rfl⟩ <;> simp [ha, hb, hc]
  · rintro (rfl | rfl | rfl)
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨b, Or.inr (Or.inl rfl), hb⟩
    · exact ⟨c, Or.inr (Or.inr rfl), hc⟩

namespace Core

private lemma val_ofNat_lt (n : ℕ) [NeZero n] (m : ℕ) (hm : m < n) :
    (Fin.ofNat n m).val = m := by
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt hm]

private lemma ofNat_ne (n : ℕ) [NeZero n] (a b : ℕ) (ha : a < n) (hb : b < n)
    (hab : a ≠ b) : Fin.ofNat n a ≠ Fin.ofNat n b := by
  intro h
  have := congrArg Fin.val h
  rw [val_ofNat_lt n a ha, val_ofNat_lt n b hb] at this
  exact hab this

section
variable {n : ℕ} [NeZero n]

private lemma disjoint_triples {a b c d e f : Fin n}
    (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) :
    Disjoint ({a, b, c} : Finset (Fin n)) ({d, e, f} : Finset (Fin n)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals tauto

private lemma support_cyc3_subset {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) :
    (swap a b * swap a c).support ⊆ ({a, b, c} : Finset (Fin n)) := by
  refine (Equiv.Perm.support_mul_le _ _).trans ?_
  rw [Equiv.Perm.support_swap hab, Equiv.Perm.support_swap hac]
  intro x hx
  rw [Finset.sup_eq_union] at hx
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

private lemma cyc3_mem_support_left {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : a ∈ (swap a b * swap a c).support := by
  rw [Equiv.Perm.mem_support, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
  exact Ne.symm hac

private lemma not_mem_triple {a b c x : Fin n} (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    x ∉ ({a, b, c} : Finset (Fin n)) := by
  intro h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  tauto

private def p1 : Perm (Fin n) := swap 0 1 * swap 0 2
private def p2 : Perm (Fin n) := swap 3 4 * swap 3 5
private def p3 : Perm (Fin n) := swap 6 7 * swap 6 8

private lemma p1_three (hn : 10 ≤ n) : (p1 : Perm (Fin n)).IsThreeCycle := by
  rw [p1]
  exact isThreeCycle_swap_mul_swap_same
    (ofNat_ne n 0 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 2 (by omega) (by omega) (by norm_num))

private lemma p2_three (hn : 10 ≤ n) : (p2 : Perm (Fin n)).IsThreeCycle := by
  rw [p2]
  exact isThreeCycle_swap_mul_swap_same
    (ofNat_ne n 3 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 5 (by omega) (by omega) (by norm_num))

private lemma p3_three (hn : 10 ≤ n) : (p3 : Perm (Fin n)).IsThreeCycle := by
  rw [p3]
  exact isThreeCycle_swap_mul_swap_same
    (ofNat_ne n 6 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 8 (by omega) (by omega) (by norm_num))

private lemma p1_support (hn : 10 ≤ n) :
    (p1 : Perm (Fin n)).support ⊆ ({0, 1, 2} : Finset (Fin n)) := by
  rw [p1]
  exact support_cyc3_subset
    (ofNat_ne n 0 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 2 (by omega) (by omega) (by norm_num))

private lemma p2_support (hn : 10 ≤ n) :
    (p2 : Perm (Fin n)).support ⊆ ({3, 4, 5} : Finset (Fin n)) := by
  rw [p2]
  exact support_cyc3_subset
    (ofNat_ne n 3 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 5 (by omega) (by omega) (by norm_num))

private lemma p3_support (hn : 10 ≤ n) :
    (p3 : Perm (Fin n)).support ⊆ ({6, 7, 8} : Finset (Fin n)) := by
  rw [p3]
  exact support_cyc3_subset
    (ofNat_ne n 6 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 8 (by omega) (by omega) (by norm_num))

private lemma p12_disj (hn : 10 ≤ n) : (p1 : Perm (Fin n)).Disjoint (p2 : Perm (Fin n)) :=
  Equiv.Perm.disjoint_iff_disjoint_support.mpr
    (Disjoint.mono (p1_support hn) (p2_support hn)
      (disjoint_triples (n := n)
      (ofNat_ne n 0 3 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 0 4 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 0 5 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 1 3 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 1 4 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 1 5 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 2 3 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 2 4 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 2 5 (by omega) (by omega) (by norm_num))))

private lemma p13_disj (hn : 10 ≤ n) : (p1 : Perm (Fin n)).Disjoint (p3 : Perm (Fin n)) :=
  Equiv.Perm.disjoint_iff_disjoint_support.mpr
    (Disjoint.mono (p1_support hn) (p3_support hn)
      (disjoint_triples (n := n)
      (ofNat_ne n 0 6 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 0 7 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 0 8 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 1 6 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 1 7 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 1 8 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 2 6 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 2 7 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 2 8 (by omega) (by omega) (by norm_num))))

private lemma p23_disj (hn : 10 ≤ n) : (p2 : Perm (Fin n)).Disjoint (p3 : Perm (Fin n)) :=
  Equiv.Perm.disjoint_iff_disjoint_support.mpr
    (Disjoint.mono (p2_support hn) (p3_support hn)
      (disjoint_triples (n := n)
      (ofNat_ne n 3 6 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 3 7 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 3 8 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 4 6 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 4 7 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 4 8 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 5 6 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 5 7 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 5 8 (by omega) (by omega) (by norm_num))))

private def P0 : Subgroup (Perm (Fin n)) := closure {(p1 : Perm (Fin n)), p2, p3}
private def PF1 : Subgroup (Perm (Fin n)) := closure {(p2 : Perm (Fin n)), p3}
private def PF2 : Subgroup (Perm (Fin n)) := closure {(p1 : Perm (Fin n)), p3}
private def PF3 : Subgroup (Perm (Fin n)) := closure {(p1 : Perm (Fin n)), p2}

private lemma P0_eq_sup :
    P0 = zpowers (p1 : Perm (Fin n)) ⊔ zpowers (p2 : Perm (Fin n)) ⊔
      zpowers (p3 : Perm (Fin n)) :=
  closure_three_eq_sup (p1 : Perm (Fin n)) p2 p3

private lemma p2_not_mem_zpowers_p1 (hn : 10 ≤ n) :
    (p2 : Perm (Fin n)) ∉ zpowers (p1 : Perm (Fin n)) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have h3p2 : (3 : Fin n) ∈ (p2 : Perm (Fin n)).support := by
    rw [p2]
    exact cyc3_mem_support_left
      (ofNat_ne n 3 4 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 3 5 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 4 5 (by omega) (by omega) (by norm_num))
  have h3p1 : (3 : Fin n) ∉ (p1 : Perm (Fin n)).support :=
    fun hmem => not_mem_triple
      (ofNat_ne n 3 0 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 3 1 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 3 2 (by omega) (by omega) (by norm_num))
      (p1_support hn hmem)
  have hsub : (p2 : Perm (Fin n)).support ⊆ (p1 : Perm (Fin n)).support := by
    rw [← hk]
    exact Equiv.Perm.support_zpow_le _ _
  exact h3p1 (hsub h3p2)

private lemma six_not_mem (hn : 10 ≤ n) :
    (6 : Fin n) ∉ ({0, 1, 2, 3, 4, 5} : Finset (Fin n)) := by
  intro h6
  rw [show ({0, 1, 2, 3, 4, 5} : Finset (Fin n)) =
      ({0, 1, 2} : Finset (Fin n)) ∪ ({3, 4, 5} : Finset (Fin n)) by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] <;> tauto]
    at h6
  rcases Finset.mem_union.mp h6 with h6 | h6
  · exact not_mem_triple
      (ofNat_ne n 6 0 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 6 1 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 6 2 (by omega) (by omega) (by norm_num)) h6
  · exact not_mem_triple
      (ofNat_ne n 6 3 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 6 4 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 6 5 (by omega) (by omega) (by norm_num)) h6

private lemma p3_not_mem_sup (hn : 10 ≤ n) :
    (p3 : Perm (Fin n)) ∉ zpowers (p1 : Perm (Fin n)) ⊔ zpowers (p2 : Perm (Fin n)) := by
  intro h
  have h6p3 : (6 : Fin n) ∈ (p3 : Perm (Fin n)).support := by
    rw [p3]
    exact cyc3_mem_support_left
      (ofNat_ne n 6 7 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 6 8 (by omega) (by omega) (by norm_num))
      (ofNat_ne n 7 8 (by omega) (by omega) (by norm_num))
  have hle : (zpowers (p1 : Perm (Fin n)) ⊔ zpowers (p2 : Perm (Fin n))) =
      Subgroup.closure ({(p1 : Perm (Fin n)), p2} : Set (Perm (Fin n))) := by
    rw [show ({(p1 : Perm (Fin n)), p2} : Set (Perm (Fin n))) =
        ({(p1 : Perm (Fin n))} : Set _) ∪ {p2} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;> tauto]
    rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  have hsupp : ∀ x ∈ (zpowers (p1 : Perm (Fin n)) ⊔ zpowers (p2 : Perm (Fin n))),
      x.support ⊆ ({0, 1, 2, 3, 4, 5} : Finset (Fin n)) := by
    rw [hle]
    exact support_closure_subset
      ((p1_support hn).trans (by intro x hx; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hx ⊢; tauto))
      ((p2_support hn).trans (by intro x hx; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hx ⊢; tauto))
  exact six_not_mem hn (hsupp p3 h h6p3)

private lemma p1_cube (hn : 10 ≤ n) : (p1 : Perm (Fin n)) ^ 3 = 1 := by
  rw [← (p1_three hn).orderOf]
  exact pow_orderOf_eq_one _

private lemma p2_cube (hn : 10 ≤ n) : (p2 : Perm (Fin n)) ^ 3 = 1 := by
  rw [← (p2_three hn).orderOf]
  exact pow_orderOf_eq_one _

private lemma p3_cube (hn : 10 ≤ n) : (p3 : Perm (Fin n)) ^ 3 = 1 := by
  rw [← (p3_three hn).orderOf]
  exact pow_orderOf_eq_one _

private lemma P0_card (hn : 10 ≤ n) : Nat.card (P0 : Subgroup (Perm (Fin n))) = 27 := by
  have h := CFSG.RankThree.PartTwo.Sec13.Item131bProof.card_sup_sup_eq_27
    (x := (p1 : Perm (Fin n))) (y := p2) (w := p3)
    (p1_three hn).orderOf (p2_three hn).orderOf (p3_three hn).orderOf
    (p12_disj hn).commute.eq (p13_disj hn).commute.eq (p23_disj hn).commute.eq
    (p2_not_mem_zpowers_p1 hn) (p3_not_mem_sup hn)
  rw [P0_eq_sup]
  exact h.1

private lemma PF1_card (hn : 10 ≤ n) : Nat.card (PF1 : Subgroup (Perm (Fin n))) = 9 :=
  CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles
    (p2_three hn) (p3_three hn) (p23_disj hn)

private lemma PF2_card (hn : 10 ≤ n) : Nat.card (PF2 : Subgroup (Perm (Fin n))) = 9 :=
  CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles
    (p1_three hn) (p3_three hn) (p13_disj hn)

private lemma PF3_card (hn : 10 ≤ n) : Nat.card (PF3 : Subgroup (Perm (Fin n))) = 9 :=
  CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles
    (p1_three hn) (p2_three hn) (p12_disj hn)

private def c1 (hn : 10 ≤ n) : alternatingGroup (Fin n) :=
  ⟨(p1 : Perm (Fin n)), (p1_three hn).mem_alternatingGroup⟩
private def c2 (hn : 10 ≤ n) : alternatingGroup (Fin n) :=
  ⟨(p2 : Perm (Fin n)), (p2_three hn).mem_alternatingGroup⟩
private def c3 (hn : 10 ≤ n) : alternatingGroup (Fin n) :=
  ⟨(p3 : Perm (Fin n)), (p3_three hn).mem_alternatingGroup⟩

private def A0 (hn : 10 ≤ n) : Subgroup (alternatingGroup (Fin n)) :=
  closure {c1 hn, c2 hn, c3 hn}
private def F1 (hn : 10 ≤ n) : Subgroup (alternatingGroup (Fin n)) := closure {c2 hn, c3 hn}
private def F2 (hn : 10 ≤ n) : Subgroup (alternatingGroup (Fin n)) := closure {c1 hn, c3 hn}
private def F3 (hn : 10 ≤ n) : Subgroup (alternatingGroup (Fin n)) := closure {c1 hn, c2 hn}

private lemma c1_cube (hn : 10 ≤ n) : (c1 hn) ^ 3 = 1 := by
  apply Subtype.ext
  simpa [c1] using p1_cube hn

private lemma c2_cube (hn : 10 ≤ n) : (c2 hn) ^ 3 = 1 := by
  apply Subtype.ext
  simpa [c2] using p2_cube hn

private lemma c3_cube (hn : 10 ≤ n) : (c3 hn) ^ 3 = 1 := by
  apply Subtype.ext
  simpa [c3] using p3_cube hn

private lemma c1_comm_c2 (hn : 10 ≤ n) : Commute (c1 hn) (c2 hn) := by
  show c1 hn * c2 hn = c2 hn * c1 hn
  exact Subtype.ext (by simpa [c1, c2] using (p12_disj hn).commute.eq)

private lemma c1_comm_c3 (hn : 10 ≤ n) : Commute (c1 hn) (c3 hn) := by
  show c1 hn * c3 hn = c3 hn * c1 hn
  exact Subtype.ext (by simpa [c1, c3] using (p13_disj hn).commute.eq)

private lemma c2_comm_c3 (hn : 10 ≤ n) : Commute (c2 hn) (c3 hn) := by
  show c2 hn * c3 hn = c3 hn * c2 hn
  exact Subtype.ext (by simpa [c2, c3] using (p23_disj hn).commute.eq)

private lemma A0_isElemAbelian (hn : 10 ≤ n) : IsElemAbelian 3 (A0 hn) :=
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.isElemAbelian_closure_three
    (c1_comm_c2 hn) (c1_comm_c3 hn) (c2_comm_c3 hn)
    (c1_cube hn) (c2_cube hn) (c3_cube hn)

private lemma A0_eq_map (hn : 10 ≤ n) :
    (A0 hn).map (alternatingGroup (Fin n)).subtype = P0 := by
  rw [A0, P0]
  exact map_closure_triple rfl rfl rfl

private lemma F1_eq_map (hn : 10 ≤ n) :
    (F1 hn).map (alternatingGroup (Fin n)).subtype = PF1 := by
  rw [F1, PF1]
  exact map_closure_pair rfl rfl

private lemma F2_eq_map (hn : 10 ≤ n) :
    (F2 hn).map (alternatingGroup (Fin n)).subtype = PF2 := by
  rw [F2, PF2]
  exact map_closure_pair rfl rfl

private lemma F3_eq_map (hn : 10 ≤ n) :
    (F3 hn).map (alternatingGroup (Fin n)).subtype = PF3 := by
  rw [F3, PF3]
  exact map_closure_pair rfl rfl

private lemma A0_card (hn : 10 ≤ n) : Nat.card (A0 hn) = 27 := by
  rw [← Subgroup.card_map_of_injective (f := (alternatingGroup (Fin n)).subtype)
    (K := A0 hn) (alternatingGroup (Fin n)).subtype_injective, A0_eq_map hn, P0_card hn]

private lemma F1_card (hn : 10 ≤ n) : Nat.card (F1 hn) = 9 := by
  rw [← Subgroup.card_map_of_injective (f := (alternatingGroup (Fin n)).subtype)
    (K := F1 hn) (alternatingGroup (Fin n)).subtype_injective, F1_eq_map hn, PF1_card hn]

private lemma F2_card (hn : 10 ≤ n) : Nat.card (F2 hn) = 9 := by
  rw [← Subgroup.card_map_of_injective (f := (alternatingGroup (Fin n)).subtype)
    (K := F2 hn) (alternatingGroup (Fin n)).subtype_injective, F2_eq_map hn, PF2_card hn]

private lemma F3_card (hn : 10 ≤ n) : Nat.card (F3 hn) = 9 := by
  rw [← Subgroup.card_map_of_injective (f := (alternatingGroup (Fin n)).subtype)
    (K := F3 hn) (alternatingGroup (Fin n)).subtype_injective, F3_eq_map hn, PF3_card hn]

private def xk (hn : 10 ≤ n) (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    alternatingGroup (Fin n) :=
  ⟨swap 0 k * swap 0 1,
    (isThreeCycle_swap_mul_swap_same (Ne.symm hk0)
      (ofNat_ne n 0 1 (by omega) (by omega) (by norm_num)) hk1).mem_alternatingGroup⟩

private def x9 (hn : 10 ≤ n) : alternatingGroup (Fin n) :=
  xk hn 9 (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num))

private def g3 (hn : 10 ≤ n) (k l : Fin n) (hk9 : k ≠ 9) (hkl : k ≠ l) (hl9 : l ≠ 9) :
    alternatingGroup (Fin n) :=
  ⟨swap k 9 * swap k l,
    (isThreeCycle_swap_mul_swap_same hk9 hkl (Ne.symm hl9)).mem_alternatingGroup⟩

private lemma xk_support (hn : 10 ≤ n) (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    (xk hn k hk0 hk1 : Perm (Fin n)).support ⊆ ({0, k, 1} : Finset (Fin n)) := by
  rw [xk]
  exact support_cyc3_subset (Ne.symm hk0)
    (ofNat_ne n 0 1 (by omega) (by omega) (by norm_num))

private lemma g3_support (hn : 10 ≤ n) (k l : Fin n) (hk9 : k ≠ 9) (hkl : k ≠ l)
    (hl9 : l ≠ 9) :
    (g3 hn k l hk9 hkl hl9 : Perm (Fin n)).support ⊆ ({k, 9, l} : Finset (Fin n)) := by
  rw [g3]
  exact support_cyc3_subset hk9 hkl

private lemma g3_apply_zero (hn : 10 ≤ n) {k l : Fin n} (h0k : k ≠ 0) (h0l : l ≠ 0)
    (hk9 : k ≠ 9) (hkl : k ≠ l) (hl9 : l ≠ 9) :
    (g3 hn k l hk9 hkl hl9 : Perm (Fin n)) 0 = 0 := by
  rw [g3, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm h0k) (Ne.symm h0l)]
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h0k)
    (ofNat_ne n 0 9 (by omega) (by omega) (by norm_num))

private lemma g3_apply_one (hn : 10 ≤ n) {k l : Fin n} (h1k : k ≠ 1) (h1l : l ≠ 1)
    (hk9 : k ≠ 9) (hkl : k ≠ l) (hl9 : l ≠ 9) :
    (g3 hn k l hk9 hkl hl9 : Perm (Fin n)) 1 = 1 := by
  rw [g3, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm h1k) (Ne.symm h1l)]
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1k)
    (ofNat_ne n 1 9 (by omega) (by omega) (by norm_num))

private lemma g3_apply_nine (hn : 10 ≤ n) {k l : Fin n} (hk9 : k ≠ 9) (hkl : k ≠ l)
    (hl9 : l ≠ 9) : (g3 hn k l hk9 hkl hl9 : Perm (Fin n)) 9 = k := by
  rw [g3, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hk9) (Ne.symm hl9)]
  exact Equiv.swap_apply_right _ _

private lemma g3_conj_x9 (hn : 10 ≤ n) {k l : Fin n}
    (h0k : k ≠ 0) (h1k : k ≠ 1) (hk9 : k ≠ 9)
    (h0l : l ≠ 0) (h1l : l ≠ 1) (hl9 : l ≠ 9) (hkl : k ≠ l) :
    g3 hn k l hk9 hkl hl9 * x9 hn * (g3 hn k l hk9 hkl hl9)⁻¹ =
      xk hn k h0k h1k := by
  apply Subtype.ext
  change (swap k 9 * swap k l) * (swap 0 9 * swap 0 1) * (swap k 9 * swap k l)⁻¹ =
    swap 0 k * swap 0 1
  have hg0 : (swap k 9 * swap k l) (0 : Fin n) = 0 := by
    change (g3 hn k l hk9 hkl hl9 : Perm (Fin n)) 0 = 0
    exact g3_apply_zero hn h0k h0l hk9 hkl hl9
  have hg1 : (swap k 9 * swap k l) (1 : Fin n) = 1 := by
    change (g3 hn k l hk9 hkl hl9 : Perm (Fin n)) 1 = 1
    exact g3_apply_one hn h1k h1l hk9 hkl hl9
  have hg9 : (swap k 9 * swap k l) (9 : Fin n) = k := by
    change (g3 hn k l hk9 hkl hl9 : Perm (Fin n)) 9 = k
    exact g3_apply_nine hn hk9 hkl hl9
  have hA : (swap k 9 * swap k l) * swap 0 9 * (swap k 9 * swap k l)⁻¹ = swap 0 k := by
    have h := Equiv.swap_apply_apply (swap k 9 * swap k l) (0 : Fin n) 9
    rw [hg0, hg9] at h
    exact h.symm
  have hB : (swap k 9 * swap k l) * swap 0 1 * (swap k 9 * swap k l)⁻¹ = swap 0 1 := by
    have h := Equiv.swap_apply_apply (swap k 9 * swap k l) (0 : Fin n) 1
    rw [hg0, hg1] at h
    exact h.symm
  calc
    (swap k 9 * swap k l) * (swap 0 9 * swap 0 1) * (swap k 9 * swap k l)⁻¹
        = ((swap k 9 * swap k l) * swap 0 9 * (swap k 9 * swap k l)⁻¹) *
          ((swap k 9 * swap k l) * swap 0 1 * (swap k 9 * swap k l)⁻¹) := by group
    _ = swap 0 k * swap 0 1 := by rw [hA, hB]

private lemma mem_centGenI_of_support (hn : 10 ≤ n)
    {x : alternatingGroup (Fin n)} {F : Subgroup (alternatingGroup (Fin n))}
    (hFA : F ≤ A0 hn) (hcard : Nat.card F = 9) {a b : alternatingGroup (Fin n)}
    (hF : F = closure {a, b})
    (hxa : (x : Perm (Fin n)).Disjoint (a : Perm (Fin n)))
    (hxb : (x : Perm (Fin n)).Disjoint (b : Perm (Fin n))) :
    x ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  have hx : x ∈ Subgroup.centralizer (F : Set (alternatingGroup (Fin n))) := by
    rw [hF, Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rcases hy with rfl | rfl
    · exact Subtype.ext hxa.commute.eq.symm
    · exact Subtype.ext hxb.commute.eq.symm
  exact mem_centGenI_of_centralizer hFA (A0_card hn) hcard hx

private lemma F1_le_A0 (hn : 10 ≤ n) : F1 hn ≤ A0 hn := by
  rw [F1, A0]
  exact Subgroup.closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at hy ⊢; tauto)

private lemma F2_le_A0 (hn : 10 ≤ n) : F2 hn ≤ A0 hn := by
  rw [F2, A0]
  exact Subgroup.closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at hy ⊢; tauto)

private lemma F3_le_A0 (hn : 10 ≤ n) : F3 hn ≤ A0 hn := by
  rw [F3, A0]
  exact Subgroup.closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff] at hy ⊢; tauto)

private lemma disjoint_019_345 (hn : 10 ≤ n) :
    Disjoint ({0, 9, 1} : Finset (Fin n)) ({3, 4, 5} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 0 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 5 (by omega) (by omega) (by norm_num))

private lemma disjoint_019_678 (hn : 10 ≤ n) :
    Disjoint ({0, 9, 1} : Finset (Fin n)) ({6, 7, 8} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 0 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 8 (by omega) (by omega) (by norm_num))

private lemma x9_mem_centGenI (hn : 10 ≤ n) :
    x9 hn ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F1 hn) (F1_le_A0 hn) (F1_card hn) (a := c2 hn)
    (b := c3 hn) (by rw [F1]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (xk_support hn 9
        (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
        (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num)))
        (p2_support hn) (disjoint_019_345 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (xk_support hn 9
        (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
        (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num)))
        (p3_support hn) (disjoint_019_678 hn))

private lemma d394_012 (hn : 10 ≤ n) :
    Disjoint ({3, 9, 4} : Finset (Fin n)) ({0, 1, 2} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 3 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 2 (by omega) (by omega) (by norm_num))

private lemma d394_678 (hn : 10 ≤ n) :
    Disjoint ({3, 9, 4} : Finset (Fin n)) ({6, 7, 8} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 3 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 8 (by omega) (by omega) (by norm_num))

private lemma d495_012 (hn : 10 ≤ n) :
    Disjoint ({4, 9, 5} : Finset (Fin n)) ({0, 1, 2} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 4 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 2 (by omega) (by omega) (by norm_num))

private lemma d495_678 (hn : 10 ≤ n) :
    Disjoint ({4, 9, 5} : Finset (Fin n)) ({6, 7, 8} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 4 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 4 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 8 (by omega) (by omega) (by norm_num))

private lemma d593_012 (hn : 10 ≤ n) :
    Disjoint ({5, 9, 3} : Finset (Fin n)) ({0, 1, 2} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 5 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 2 (by omega) (by omega) (by norm_num))

private lemma d593_678 (hn : 10 ≤ n) :
    Disjoint ({5, 9, 3} : Finset (Fin n)) ({6, 7, 8} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 5 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 5 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 3 8 (by omega) (by omega) (by norm_num))

private lemma d697_012 (hn : 10 ≤ n) :
    Disjoint ({6, 9, 7} : Finset (Fin n)) ({0, 1, 2} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 6 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 2 (by omega) (by omega) (by norm_num))

private lemma d697_345 (hn : 10 ≤ n) :
    Disjoint ({6, 9, 7} : Finset (Fin n)) ({3, 4, 5} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 6 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 5 (by omega) (by omega) (by norm_num))

private lemma d798_012 (hn : 10 ≤ n) :
    Disjoint ({7, 9, 8} : Finset (Fin n)) ({0, 1, 2} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 7 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 2 (by omega) (by omega) (by norm_num))

private lemma d798_345 (hn : 10 ≤ n) :
    Disjoint ({7, 9, 8} : Finset (Fin n)) ({3, 4, 5} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 7 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 7 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 5 (by omega) (by omega) (by norm_num))

private lemma d896_012 (hn : 10 ≤ n) :
    Disjoint ({8, 9, 6} : Finset (Fin n)) ({0, 1, 2} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 8 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 2 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 0 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 1 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 2 (by omega) (by omega) (by norm_num))

private lemma d896_345 (hn : 10 ≤ n) :
    Disjoint ({8, 9, 6} : Finset (Fin n)) ({3, 4, 5} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 8 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 8 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 9 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 6 5 (by omega) (by omega) (by norm_num))

private lemma d021_345 (hn : 10 ≤ n) :
    Disjoint ({0, 2, 1} : Finset (Fin n)) ({3, 4, 5} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 0 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 2 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 2 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 2 5 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 3 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 4 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 5 (by omega) (by omega) (by norm_num))

private lemma d021_678 (hn : 10 ≤ n) :
    Disjoint ({0, 2, 1} : Finset (Fin n)) ({6, 7, 8} : Finset (Fin n)) :=
  disjoint_triples (n := n)
    (ofNat_ne n 0 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 0 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 2 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 2 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 2 8 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 6 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 7 (by omega) (by omega) (by norm_num))
    (ofNat_ne n 1 8 (by omega) (by omega) (by norm_num))

private lemma x2_mem (hn : 10 ≤ n) (h20 : (2 : Fin n) ≠ 0) (h21 : (2 : Fin n) ≠ 1) :
    xk hn 2 h20 h21 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F1 hn) (F1_le_A0 hn) (F1_card hn) (a := c2 hn)
    (b := c3 hn) (by rw [F1]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (xk_support hn 2 h20 h21) (p2_support hn) (d021_345 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (xk_support hn 2 h20 h21) (p3_support hn) (d021_678 hn))

private lemma g_mem_3_4 (hn : 10 ≤ n) (hk9 : (3 : Fin n) ≠ 9)
    (hkl : (3 : Fin n) ≠ (4 : Fin n)) (hl9 : (4 : Fin n) ≠ 9) :
    g3 hn 3 4 hk9 hkl hl9 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F2 hn) (F2_le_A0 hn) (F2_card hn)
    (a := c1 hn) (b := c3 hn) (by rw [F2]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 3 4 hk9 hkl hl9) (p1_support hn) (d394_012 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 3 4 hk9 hkl hl9) (p3_support hn) (d394_678 hn))

private lemma g_mem_4_5 (hn : 10 ≤ n) (hk9 : (4 : Fin n) ≠ 9)
    (hkl : (4 : Fin n) ≠ (5 : Fin n)) (hl9 : (5 : Fin n) ≠ 9) :
    g3 hn 4 5 hk9 hkl hl9 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F2 hn) (F2_le_A0 hn) (F2_card hn)
    (a := c1 hn) (b := c3 hn) (by rw [F2]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 4 5 hk9 hkl hl9) (p1_support hn) (d495_012 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 4 5 hk9 hkl hl9) (p3_support hn) (d495_678 hn))

private lemma g_mem_5_3 (hn : 10 ≤ n) (hk9 : (5 : Fin n) ≠ 9)
    (hkl : (5 : Fin n) ≠ (3 : Fin n)) (hl9 : (3 : Fin n) ≠ 9) :
    g3 hn 5 3 hk9 hkl hl9 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F2 hn) (F2_le_A0 hn) (F2_card hn)
    (a := c1 hn) (b := c3 hn) (by rw [F2]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 5 3 hk9 hkl hl9) (p1_support hn) (d593_012 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 5 3 hk9 hkl hl9) (p3_support hn) (d593_678 hn))

private lemma g_mem_6_7 (hn : 10 ≤ n) (hk9 : (6 : Fin n) ≠ 9)
    (hkl : (6 : Fin n) ≠ (7 : Fin n)) (hl9 : (7 : Fin n) ≠ 9) :
    g3 hn 6 7 hk9 hkl hl9 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F3 hn) (F3_le_A0 hn) (F3_card hn)
    (a := c1 hn) (b := c2 hn) (by rw [F3]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 6 7 hk9 hkl hl9) (p1_support hn) (d697_012 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 6 7 hk9 hkl hl9) (p2_support hn) (d697_345 hn))

private lemma g_mem_7_8 (hn : 10 ≤ n) (hk9 : (7 : Fin n) ≠ 9)
    (hkl : (7 : Fin n) ≠ (8 : Fin n)) (hl9 : (8 : Fin n) ≠ 9) :
    g3 hn 7 8 hk9 hkl hl9 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F3 hn) (F3_le_A0 hn) (F3_card hn)
    (a := c1 hn) (b := c2 hn) (by rw [F3]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 7 8 hk9 hkl hl9) (p1_support hn) (d798_012 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 7 8 hk9 hkl hl9) (p2_support hn) (d798_345 hn))

private lemma g_mem_8_6 (hn : 10 ≤ n) (hk9 : (8 : Fin n) ≠ 9)
    (hkl : (8 : Fin n) ≠ (6 : Fin n)) (hl9 : (6 : Fin n) ≠ 9) :
    g3 hn 8 6 hk9 hkl hl9 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F3 hn) (F3_le_A0 hn) (F3_card hn)
    (a := c1 hn) (b := c2 hn) (by rw [F3]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 8 6 hk9 hkl hl9) (p1_support hn) (d896_012 hn))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (g3_support hn 8 6 hk9 hkl hl9) (p2_support hn) (d896_345 hn))

private lemma xk3_mem (hn : 10 ≤ n) (hk0 : (3 : Fin n) ≠ 0)
    (hk1 : (3 : Fin n) ≠ 1) :
    xk hn 3 hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  let hk9 := ofNat_ne n 3 9 (by omega) (by omega) (by norm_num)
  let hkl := ofNat_ne n 3 4 (by omega) (by omega) (by norm_num)
  let hl9 := ofNat_ne n 4 9 (by omega) (by omega) (by norm_num)
  let h0l := ofNat_ne n 4 0 (by omega) (by omega) (by norm_num)
  let h1l := ofNat_ne n 4 1 (by omega) (by omega) (by norm_num)
  have hx : xk hn 3 hk0 hk1 =
      g3 hn 3 4 hk9 hkl hl9 * x9 hn * (g3 hn 3 4 hk9 hkl hl9)⁻¹ :=
    (g3_conj_x9 hn hk0 hk1 hk9 h0l h1l hl9 hkl).symm
  rw [hx]
  have hg := g_mem_3_4 hn hk9 hkl hl9
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (x9_mem_centGenI hn))
    (Subgroup.inv_mem _ hg)

private lemma xk4_mem (hn : 10 ≤ n) (hk0 : (4 : Fin n) ≠ 0)
    (hk1 : (4 : Fin n) ≠ 1) :
    xk hn 4 hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  let hk9 := ofNat_ne n 4 9 (by omega) (by omega) (by norm_num)
  let hkl := ofNat_ne n 4 5 (by omega) (by omega) (by norm_num)
  let hl9 := ofNat_ne n 5 9 (by omega) (by omega) (by norm_num)
  let h0l := ofNat_ne n 5 0 (by omega) (by omega) (by norm_num)
  let h1l := ofNat_ne n 5 1 (by omega) (by omega) (by norm_num)
  have hx : xk hn 4 hk0 hk1 =
      g3 hn 4 5 hk9 hkl hl9 * x9 hn * (g3 hn 4 5 hk9 hkl hl9)⁻¹ :=
    (g3_conj_x9 hn hk0 hk1 hk9 h0l h1l hl9 hkl).symm
  rw [hx]
  have hg := g_mem_4_5 hn hk9 hkl hl9
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (x9_mem_centGenI hn))
    (Subgroup.inv_mem _ hg)

private lemma xk5_mem (hn : 10 ≤ n) (hk0 : (5 : Fin n) ≠ 0)
    (hk1 : (5 : Fin n) ≠ 1) :
    xk hn 5 hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  let hk9 := ofNat_ne n 5 9 (by omega) (by omega) (by norm_num)
  let hkl := ofNat_ne n 5 3 (by omega) (by omega) (by norm_num)
  let hl9 := ofNat_ne n 3 9 (by omega) (by omega) (by norm_num)
  let h0l := ofNat_ne n 3 0 (by omega) (by omega) (by norm_num)
  let h1l := ofNat_ne n 3 1 (by omega) (by omega) (by norm_num)
  have hx : xk hn 5 hk0 hk1 =
      g3 hn 5 3 hk9 hkl hl9 * x9 hn * (g3 hn 5 3 hk9 hkl hl9)⁻¹ :=
    (g3_conj_x9 hn hk0 hk1 hk9 h0l h1l hl9 hkl).symm
  rw [hx]
  have hg := g_mem_5_3 hn hk9 hkl hl9
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (x9_mem_centGenI hn))
    (Subgroup.inv_mem _ hg)

private lemma xk6_mem (hn : 10 ≤ n) (hk0 : (6 : Fin n) ≠ 0)
    (hk1 : (6 : Fin n) ≠ 1) :
    xk hn 6 hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  let hk9 := ofNat_ne n 6 9 (by omega) (by omega) (by norm_num)
  let hkl := ofNat_ne n 6 7 (by omega) (by omega) (by norm_num)
  let hl9 := ofNat_ne n 7 9 (by omega) (by omega) (by norm_num)
  let h0l := ofNat_ne n 7 0 (by omega) (by omega) (by norm_num)
  let h1l := ofNat_ne n 7 1 (by omega) (by omega) (by norm_num)
  have hx : xk hn 6 hk0 hk1 =
      g3 hn 6 7 hk9 hkl hl9 * x9 hn * (g3 hn 6 7 hk9 hkl hl9)⁻¹ :=
    (g3_conj_x9 hn hk0 hk1 hk9 h0l h1l hl9 hkl).symm
  rw [hx]
  have hg := g_mem_6_7 hn hk9 hkl hl9
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (x9_mem_centGenI hn))
    (Subgroup.inv_mem _ hg)

private lemma xk7_mem (hn : 10 ≤ n) (hk0 : (7 : Fin n) ≠ 0)
    (hk1 : (7 : Fin n) ≠ 1) :
    xk hn 7 hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  let hk9 := ofNat_ne n 7 9 (by omega) (by omega) (by norm_num)
  let hkl := ofNat_ne n 7 8 (by omega) (by omega) (by norm_num)
  let hl9 := ofNat_ne n 8 9 (by omega) (by omega) (by norm_num)
  let h0l := ofNat_ne n 8 0 (by omega) (by omega) (by norm_num)
  let h1l := ofNat_ne n 8 1 (by omega) (by omega) (by norm_num)
  have hx : xk hn 7 hk0 hk1 =
      g3 hn 7 8 hk9 hkl hl9 * x9 hn * (g3 hn 7 8 hk9 hkl hl9)⁻¹ :=
    (g3_conj_x9 hn hk0 hk1 hk9 h0l h1l hl9 hkl).symm
  rw [hx]
  have hg := g_mem_7_8 hn hk9 hkl hl9
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (x9_mem_centGenI hn))
    (Subgroup.inv_mem _ hg)

private lemma xk8_mem (hn : 10 ≤ n) (hk0 : (8 : Fin n) ≠ 0)
    (hk1 : (8 : Fin n) ≠ 1) :
    xk hn 8 hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  let hk9 := ofNat_ne n 8 9 (by omega) (by omega) (by norm_num)
  let hkl := ofNat_ne n 8 6 (by omega) (by omega) (by norm_num)
  let hl9 := ofNat_ne n 6 9 (by omega) (by omega) (by norm_num)
  let h0l := ofNat_ne n 6 0 (by omega) (by omega) (by norm_num)
  let h1l := ofNat_ne n 6 1 (by omega) (by omega) (by norm_num)
  have hx : xk hn 8 hk0 hk1 =
      g3 hn 8 6 hk9 hkl hl9 * x9 hn * (g3 hn 8 6 hk9 hkl hl9)⁻¹ :=
    (g3_conj_x9 hn hk0 hk1 hk9 h0l h1l hl9 hkl).symm
  rw [hx]
  have hg := g_mem_8_6 hn hk9 hkl hl9
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (x9_mem_centGenI hn))
    (Subgroup.inv_mem _ hg)

private lemma d01k_345 (hn : 10 ≤ n) {k : Fin n} (hge : 9 ≤ k.val) :
    Disjoint ({0, k, 1} : Finset (Fin n)) ({3, 4, 5} : Finset (Fin n)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  all_goals
    first
    | exact ofNat_ne n 0 3 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 0 3 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 0 4 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 0 4 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 0 5 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 0 5 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 1 3 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 1 3 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 1 4 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 1 4 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 1 5 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 1 5 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | (have hv := congrArg Fin.val (hx.symm.trans hy)
       have hv' : (3 : Fin n).val = 3 := by
         change 3 % n = 3; exact Nat.mod_eq_of_lt (by omega)
       rw [hv'] at hv; omega)
    | (have hv := congrArg Fin.val (hx.symm.trans hy)
       have hv' : (4 : Fin n).val = 4 := by
         change 4 % n = 4; exact Nat.mod_eq_of_lt (by omega)
       rw [hv'] at hv; omega)
    | (have hv := congrArg Fin.val (hx.symm.trans hy)
       have hv' : (5 : Fin n).val = 5 := by
         change 5 % n = 5; exact Nat.mod_eq_of_lt (by omega)
       rw [hv'] at hv; omega)

private lemma d01k_678 (hn : 10 ≤ n) {k : Fin n} (hge : 9 ≤ k.val) :
    Disjoint ({0, k, 1} : Finset (Fin n)) ({6, 7, 8} : Finset (Fin n)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  all_goals
    first
    | exact ofNat_ne n 0 6 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 0 6 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 0 7 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 0 7 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 0 8 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 0 8 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 1 6 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 1 6 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 1 7 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 1 7 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | exact ofNat_ne n 1 8 (by omega) (by omega) (by norm_num) (hx.symm.trans hy)
    | exact (ofNat_ne n 1 8 (by omega) (by omega) (by norm_num)).symm (hx.symm.trans hy)
    | (have hv := congrArg Fin.val (hx.symm.trans hy)
       have hv' : (6 : Fin n).val = 6 := by
         change 6 % n = 6; exact Nat.mod_eq_of_lt (by omega)
       rw [hv'] at hv; omega)
    | (have hv := congrArg Fin.val (hx.symm.trans hy)
       have hv' : (7 : Fin n).val = 7 := by
         change 7 % n = 7; exact Nat.mod_eq_of_lt (by omega)
       rw [hv'] at hv; omega)
    | (have hv := congrArg Fin.val (hx.symm.trans hy)
       have hv' : (8 : Fin n).val = 8 := by
         change 8 % n = 8; exact Nat.mod_eq_of_lt (by omega)
       rw [hv'] at hv; omega)

private lemma xk_ge9_mem (hn : 10 ≤ n) (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hge : 9 ≤ k.val) :
    xk hn k hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  refine mem_centGenI_of_support hn (F := F1 hn) (F1_le_A0 hn) (F1_card hn) (a := c2 hn)
    (b := c3 hn) (by rw [F1]) ?_ ?_
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (xk_support hn k hk0 hk1) (p2_support hn) (d01k_345 hn hge))
  · exact Equiv.Perm.disjoint_iff_disjoint_support.mpr
      (Disjoint.mono (xk_support hn k hk0 hk1) (p3_support hn) (d01k_678 hn hge))

private lemma star_mem_centGenI (hn : 10 ≤ n) (k : Fin n) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    xk hn k hk0 hk1 ∈ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  by_cases hlt : k.val < 9
  · interval_cases h : k.val
    · have hk : k = (0 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 0 (by omega)).symm)
      exact (hk0 hk).elim
    · have hk : k = (1 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 1 (by omega)).symm)
      exact (hk1 hk).elim
    · have hk : k = (2 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 2 (by omega)).symm)
      subst hk
      exact x2_mem hn hk0 hk1
    · have hk : k = (3 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 3 (by omega)).symm)
      subst hk
      exact xk3_mem hn hk0 hk1
    · have hk : k = (4 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 4 (by omega)).symm)
      subst hk
      exact xk4_mem hn hk0 hk1
    · have hk : k = (5 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 5 (by omega)).symm)
      subst hk
      exact xk5_mem hn hk0 hk1
    · have hk : k = (6 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 6 (by omega)).symm)
      subst hk
      exact xk6_mem hn hk0 hk1
    · have hk : k = (7 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 7 (by omega)).symm)
      subst hk
      exact xk7_mem hn hk0 hk1
    · have hk : k = (8 : Fin n) := Fin.ext (by
        rw [h]; exact (val_ofNat_lt n 8 (by omega)).symm)
      subst hk
      exact xk8_mem hn hk0 hk1
  · exact xk_ge9_mem hn k hk0 hk1 (Nat.le_of_not_lt hlt)

private def S : Set (alternatingGroup (Fin n)) :=
  {σ | (σ : Perm (Fin n)) ∈ Star.starSet n}

private lemma S_image_eq (hn : 10 ≤ n) :
    (alternatingGroup (Fin n)).subtype '' (S : Set (alternatingGroup (Fin n))) =
      Star.starSet n := by
  ext p
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact hσ
  · intro hp
    rw [Star.starSet] at hp
    obtain ⟨k, hk0, hk1, rfl⟩ := hp
    exact ⟨⟨Star.x k, Star.x_mem_alt (by omega) hk0 hk1⟩, ⟨k, hk0, hk1, rfl⟩, rfl⟩

private lemma closure_S_eq_top (hn : 10 ≤ n) :
    Subgroup.closure (S : Set (alternatingGroup (Fin n))) = ⊤ := by
  apply Subgroup.map_injective (Subgroup.subtype_injective (alternatingGroup (Fin n)))
  rw [MonoidHom.map_closure, S_image_eq hn,
    Star.star_closure_eq_alternating (by omega), Subgroup.map_top, Subgroup.range_subtype]

private lemma S_subset_centGenI (hn : 10 ≤ n) :
    (S : Set (alternatingGroup (Fin n))) ⊆ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  intro σ hσ
  rw [S] at hσ
  rw [Star.starSet] at hσ
  obtain ⟨k, hk0, hk1, hk⟩ := hσ
  have hσk : σ = xk hn k hk0 hk1 := Subtype.ext hk
  rw [hσk]
  exact star_mem_centGenI hn k hk0 hk1

private lemma top_le_centGenI (hn : 10 ≤ n) :
    (⊤ : Subgroup (alternatingGroup (Fin n))) ≤ GL83.CompFam.centGenI 3 (A0 hn) ⊤ := by
  conv_lhs => rw [← closure_S_eq_top hn]
  exact (Subgroup.closure_le (K := GL83.CompFam.centGenI 3 (A0 hn) ⊤)).mpr
    (S_subset_centGenI hn)

private lemma glbCore_A0_eq_top (hn : 10 ≤ n) :
    CFSG.Open.GLBCore 3 2 (A0 hn) = ⊤ := by
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.le_glbCore_of_centGenI
    (Y := alternatingGroup (Fin n)) Nat.prime_three (B := A0 hn) (E := A0 hn) (K := ⊤)
    le_rfl (A0_isElemAbelian hn) (by rw [A0_card hn]; norm_num) (top_le_centGenI hn)
  exact top_le_iff.mp h

section
variable {n : ℕ} [NeZero n]

private lemma exists_conj_A0_le (hn : 10 ≤ n) {L : Type} [Group L] [Finite L]
    (e : L ≃* alternatingGroup (Fin n)) {P : Subgroup L}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) :
    ∃ k : alternatingGroup (Fin n),
      (A0 hn).map (MulAut.conj k).toMonoidHom ≤ P.map e.toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPEsylow : CFSG.ABGLocalTools.IsSylowOf 3 (P.map e.toMonoidHom) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hP.isPGroup.map e.toMonoidHom, ?_⟩
    rw [Subgroup.relIndex_top_right]
    change ¬ 3 ∣ (Subgroup.map (e : L →* alternatingGroup (Fin n)) P).index
    rw [Subgroup.index_map_equiv]
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP
    simpa [Subgroup.relIndex_top_right] using hP.2.2
  have hA0pg : IsPGroup 3 (A0 hn) :=
    IsPGroup.of_card (n := 3) (by rw [A0_card hn]; norm_num)
  obtain ⟨Q, hA0Q⟩ := hA0pg.exists_le_sylow
  have hQIs : CFSG.ABGLocalTools.IsSylowOf 3
      (Q : Subgroup (alternatingGroup (Fin n))) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  obtain ⟨k, -, hconj⟩ := hQIs.exists_mem_conj hPEsylow
  refine ⟨k, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  refine (hconj (k * a * k⁻¹)).mpr ?_
  have hxa : k⁻¹ * (k * a * k⁻¹) * k = a := by group
  rw [hxa]
  exact hA0Q ha

private lemma eq_of_e27_le {PE : Subgroup (alternatingGroup (Fin n))}
    (hPEZ : Nonempty (↥PE ≃* UC22.InS3.UC326.ZWr 1))
    {E F : Subgroup (alternatingGroup (Fin n))} (hE : E ≤ PE) (hF : F ≤ PE)
    (hEel : CFSG.Open.IsElemAbelian 3 E) (hFel : CFSG.Open.IsElemAbelian 3 F)
    (hEcard : Nat.card E = 27) (hFcard : Nat.card F = 27) : E = F := by
  obtain ⟨ePE⟩ := hPEZ
  obtain ⟨B, -, hBel, hBcard, huniq, -⟩ :=
    UC22.InS3.UC326.zwr_unique_E27 (n := 1) (by norm_num) ePE
  have hBmap : ∀ E : Subgroup (alternatingGroup (Fin n)), E ≤ PE →
      CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 → E = B.map PE.subtype := by
    intro E hE hEel hEcard
    have hE' : CFSG.Open.IsElemAbelian 3 (E.subgroupOf PE) := hEel.subgroupOf PE
    have hcard' : Nat.card (E.subgroupOf PE) = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv, hEcard]
    have heq := huniq (E.subgroupOf PE) hE' hcard'
    have hmap := congrArg (Subgroup.map PE.subtype) heq
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE] at hmap
    exact hmap
  exact (hBmap E hE hEel hEcard).trans (hBmap F hF hFel hFcard).symm

private theorem transport (hn : 10 ≤ n) {L : Type} [Group L] [Finite L]
    (he : UC22.IsAlt L n) {P A : Subgroup L}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hAP : A ≤ P)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := he
  let PE : Subgroup (alternatingGroup (Fin n)) := P.map e.toMonoidHom
  have hPEZ : Nonempty (↥PE ≃* UC22.InS3.UC326.ZWr 1) := by
    obtain ⟨φ⟩ := hPZ
    exact ⟨(e.subgroupMap P).symm.trans φ⟩
  obtain ⟨k, hA0conj⟩ := exists_conj_A0_le hn e hP hPZ
  have hAe_eq : A.map e.toMonoidHom = (A0 hn).map (MulAut.conj k).toMonoidHom :=
    eq_of_e27_le hPEZ (Subgroup.map_mono hAP) hA0conj
      (hA.map e.toMonoidHom) (A0_isElemAbelian hn |>.map _)
      (by rw [Subgroup.card_map_of_injective e.injective, hcard])
      (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, A0_card hn])
  have hcore_conj :
      CFSG.Open.GLBCore 3 2 ((A0 hn).map (MulAut.conj k).toMonoidHom) = ⊤ := by
    rw [CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_conj,
      glbCore_A0_eq_top hn, Subgroup.map_top_of_surjective _ (MulAut.conj k).surjective]
  have hcoreAe : CFSG.Open.GLBCore 3 2 (A.map e.toMonoidHom) = ⊤ := by
    rw [hAe_eq, hcore_conj]
  have hmap := CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_equiv
    (p := 3) (k := 2) e A
  have hright : (CFSG.Open.GLBCore 3 2 A).map e.toMonoidHom = ⊤ :=
    hmap.symm.trans hcoreAe
  have hEq : Subgroup.map e.toMonoidHom (CFSG.Open.GLBCore 3 2 A) =
      Subgroup.map e.toMonoidHom ⊤ := by
    rw [hright, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  exact Subgroup.map_injective e.injective hEq

end

end
end Core

theorem glbCore_eq_top_of_isAlt {L : Type} [Group L] [Finite L] {n : ℕ} (hn : n = 10 ∨ n = 11)
    (he : UC22.IsAlt L n) {P A : Subgroup L} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hAP : A ≤ P)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  have hn10 : 10 ≤ n := by omega
  haveI : NeZero n := by rcases hn with rfl | rfl <;> infer_instance
  exact Core.transport (n := n) hn10 he hP hPZ hAP hA hcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10TwoGen
