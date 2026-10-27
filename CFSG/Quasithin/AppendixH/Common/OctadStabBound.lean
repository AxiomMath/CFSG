module

public import CFSG.Quasithin.AppendixH.Common.OctadBasic

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

private theorem zmod2_eq_of_ne_zero_iff {a b : ZMod 2} (h : (a ≠ 0) ↔ (b ≠ 0)) : a = b := by
  revert a b
  decide

theorem card_octStab_octadB0_le : Nat.card (octStab octadB0) ≤ 322560 := by
  classical
  have hs : ∀ p : octStab octadB0, ∀ i, B 0 ((p : S24) i) = B 0 i := by
    intro p i
    have hp : (p : S24) • octadB0 = octadB0 := MulAction.mem_stabilizer_iff.1 p.2.2
    have hmem : (p : S24) i ∈ octadB0 ↔ i ∈ octadB0 := by
      have h : (p : S24) i ∈ (p : S24) • octadB0 ↔ i ∈ octadB0 := by
        rw [smul_finset_eq_map, Finset.mem_map_equiv]
        simp
      rwa [hp] at h
    have hne : (B 0 ((p : S24) i) ≠ 0) ↔ (B 0 i ≠ 0) := by
      simpa only [octadB0, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    exact zmod2_eq_of_ne_zero_iff hne
  have hex : ∀ p : octStab octadB0,
      ∃ Ab : GL (Fin 4) (ZMod 2) × (Fin 4 → ZMod 2), ∀ i : {i // B 0 i = 0},
        frameLabel ⟨(p : S24) i, (hs p i).trans i.2⟩ =
          (Ab.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (frameLabel i) + Ab.2 := by
    intro p
    obtain ⟨A, b, h⟩ := exists_affine p.2.1 (hs p)
    exact ⟨(A, b), h⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro p q hpq
    have hpt : ∀ i, B 0 i = 0 → (p : S24) i = (q : S24) i := by
      intro i hi
      have h1 := hf p ⟨i, hi⟩
      rw [hpq, ← hf q ⟨i, hi⟩] at h1
      exact congrArg Subtype.val (frame_affine.1.1 h1)
    have hr : (q : S24)⁻¹ * (p : S24) ∈ AutPerm :=
      AutPerm.mul_mem (AutPerm.inv_mem q.2.1) p.2.1
    have h1 := eq_one_of_fix_compl hr fun i hi => by
      rw [Equiv.Perm.mul_apply, hpt i hi]
      simp
    have h2 : (p : S24) = (q : S24) := by
      rw [← mul_one (q : S24), ← h1, mul_inv_cancel_left]
    exact Subtype.ext h2
  have hcard := Nat.card_le_card_of_injective f hinj
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have hGL : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field, ZMod.card]
    simp [Fin.prod_univ_four]
  rw [Nat.card_prod, hGL, h16] at hcard
  exact hcard

end CFSG.ASVolI.AppH
