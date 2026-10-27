module

public import CFSG.LocalAnalysis.StandardType.SpEightFrameConjugacy
public import CFSG.LocalAnalysis.StandardType.SpEightExceptionalFrame
public import CFSG.LocalAnalysis.StandardType.SpEightCentralizers

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.StandardType.ElementaryAbelianNine

theorem exists_conj_E2 {E : Subgroup ↥(StatedSp 4 (ZMod 2))}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 9)
    (hne : Subgroup.closure {g : ↥(StatedSp 4 (ZMod 2)) | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} ≠ ⊤) :
    ∃ A : ↥(StatedSp 4 (ZMod 2)), ∀ x : ↥(StatedSp 4 (ZMod 2)),
      x ∈ E ↔ (((A⁻¹ * x * A : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2)) ∈ E2) := by
  have hcommE : ∀ x y : ↥E, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
  have hexpE : ∀ x : ↥E, x ^ 3 = 1 := fun x => Subtype.ext (hexp x x.2)
  obtain ⟨a, b, ha1, hb, hgen⟩ := exists_generators hcommE hexpE hcard
  obtain ⟨hcard3, hinj, -⟩ := line_facts hcommE hexpE hcard ha1 hb hgen
  have hV : ∀ k, spLineSpace (line a b k) ≠ ⊥ := fun k =>
    spLineSpace_ne_bot_of_closure_ne_top hcomm hexp hcard hne (hcard3 k)
  obtain ⟨bas, hgram, ha, hb'⟩ := exists_frame hcomm hexp hcard ha1 hb hcard3 hinj hV
  obtain ⟨A, hASp, hAa, hAb⟩ := exists_conj_aStd_bStd_of_frame
    (a' := (((a : ↥E) : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2)))
    (b' := (((b : ↥E) : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2))) bas hgram ha hb'
  let φ : MulAut (GL Idx (ZMod 2)) := MulAut.conj (hGL * A⁻¹)
  have hφa : φ (((a : ↥E) : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2)) = a2 := by
    simp only [φ, MulAut.conj_apply, a2, _root_.mul_inv_rev, inv_inv]
    rw [← hAa]
    simp only [mul_assoc]
  have hφb : φ (((b : ↥E) : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2)) = b2 := by
    simp only [φ, MulAut.conj_apply, b2, _root_.mul_inv_rev, inv_inv]
    rw [← hAb]
    simp only [mul_assoc]
  have hSp : A * hGL⁻¹ ∈ StatedSp 4 (ZMod 2) :=
    (StatedSp 4 (ZMod 2)).mul_mem hASp ((StatedSp 4 (ZMod 2)).inv_mem hGL_mem)
  refine ⟨⟨A * hGL⁻¹, hSp⟩, fun x => ?_⟩
  have hconj : (((⟨A * hGL⁻¹, hSp⟩ : ↥(StatedSp 4 (ZMod 2)))⁻¹ * x *
      ⟨A * hGL⁻¹, hSp⟩ : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2)) =
      φ (x : GL Idx (ZMod 2)) := by
    simp only [φ, MulAut.conj_apply, _root_.mul_inv_rev, inv_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, mul_assoc]
  rw [hconj]
  have hpow : ∀ i j : ℕ, φ ((((a ^ i * b ^ j : ↥E) : ↥(StatedSp 4 (ZMod 2))) :
      GL Idx (ZMod 2))) = a2 ^ i * b2 ^ j := by
    intro i j
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow, hφa, hφb]
  constructor
  · intro hx
    obtain ⟨i, j, hij⟩ := hgen ⟨x, hx⟩
    have hx' : (x : GL Idx (ZMod 2)) =
        (((a ^ i * b ^ j : ↥E) : ↥(StatedSp 4 (ZMod 2))) : GL Idx (ZMod 2)) := by
      rw [← hij]
    rw [hx', hpow]
    exact E2.mul_mem (E2.pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (E2.pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) _)
  · intro hx
    obtain ⟨i, j, hij⟩ := (mem_E2_iff _).1 hx
    have hxe : x = (((a ^ (i : ℕ) * b ^ (j : ℕ) : ↥E)) : ↥(StatedSp 4 (ZMod 2))) := by
      apply Subtype.ext
      apply φ.injective
      rw [hpow, ← hij]
    rw [hxe]
    exact (a ^ (i : ℕ) * b ^ (j : ℕ) : ↥E).2

end CFSG.StandardType.SpEight
