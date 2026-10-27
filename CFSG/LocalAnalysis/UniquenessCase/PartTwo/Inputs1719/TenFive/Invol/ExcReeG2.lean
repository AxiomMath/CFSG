module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwist
public import CFSG.LieType.Ree.SmallReeRootParameters

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag smallReeX smallReeSigma smallReeRoot)
open scoped commutatorElement


private noncomputable def smallReeR (L : Type) [Field L] (i : Fin 6) (c : L) :
    adjointGroup ReeTag.G2.tag L :=
  ⟨smallReeX L i c, pinnedX_mem_adjointGroup _ c⟩

private theorem smallReeR_add {L : Type} [Field L] (i : Fin 6) (s t : L) :
    smallReeR L i (s + t) = smallReeR L i s * smallReeR L i t :=
  Subtype.ext (pinnedX_add Tag.G2 L (smallReeRoot i) s t)

private theorem smallReeR_neg {L : Type} [Field L] (i : Fin 6) (c : L) :
    smallReeR L i (-c) = (smallReeR L i c)⁻¹ := by
  apply Subtype.ext
  show smallReeX L i (-c) = (smallReeX L i c)⁻¹
  exact (pinnedX_neg Tag.G2 L (smallReeRoot i) c).symm

private theorem smallReeR_injective {L : Type} [Field L] (i : Fin 6) :
    Function.Injective (smallReeR L i) := by
  intro c d h
  exact pinnedX_injective Tag.G2 L (smallReeRoot i) (Subtype.ext_iff.mp h)

private theorem smallReeR_comm {L : Type} [Field L] [CharP L 3] {i j : Fin 6} (hij : i < j)
    (h1 : (i, j) ≠ (0, 1)) (h2 : (i, j) ≠ (0, 2)) (h3 : (i, j) ≠ (1, 4)) (s t : L) :
    Commute (smallReeR L j t) (smallReeR L i s) := by
  show smallReeR L j t * smallReeR L i s = smallReeR L i s * smallReeR L j t
  exact Subtype.ext
    ((CFSG.LieType.Ree.small_Ree_positive_root_collection_identities L s t).2.2.2 i j hij h1 h2 h3)

private theorem smallReeR_comm15 {L : Type} [Field L] [CharP L 3] (s t : L) :
    Commute (smallReeR L 5 s) (smallReeR L 1 t) :=
  smallReeR_comm (i := 1) (j := 5) (by decide) (by decide) (by decide) (by decide) t s

private theorem smallReeR_comm45 {L : Type} [Field L] [CharP L 3] (s t : L) :
    Commute (smallReeR L 5 s) (smallReeR L 4 t) :=
  smallReeR_comm (i := 4) (j := 5) (by decide) (by decide) (by decide) (by decide) t s

private theorem smallReeR_comm12 {L : Type} [Field L] [CharP L 3] (s t : L) :
    Commute (smallReeR L 2 s) (smallReeR L 1 t) :=
  smallReeR_comm (i := 1) (j := 2) (by decide) (by decide) (by decide) (by decide) t s

private theorem smallReeR_comm24 {L : Type} [Field L] [CharP L 3] (s t : L) :
    Commute (smallReeR L 2 s) (smallReeR L 4 t) :=
  (smallReeR_comm (i := 2) (j := 4) (by decide) (by decide) (by decide) (by decide) s t).symm

private theorem smallReeR_commutator {L : Type} [Field L] [CharP L 3] (s t : L) :
    ⁅smallReeR L 1 s, smallReeR L 4 t⁆ = smallReeR L 5 (s * t) := by
  have hcol := (CFSG.LieType.Ree.small_Ree_positive_root_collection_identities L (-s) t).2.2.1
  have harg : -((-s) * t) = s * t := by ring
  rw [harg] at hcol
  have hcolg : smallReeR L 4 t * smallReeR L 1 (-s) =
      smallReeR L 1 (-s) * smallReeR L 4 t * smallReeR L 5 (s * t) :=
    Subtype.ext hcol
  rw [smallReeR_neg 1 s] at hcolg
  have hswap : smallReeR L 1 s * smallReeR L 4 t =
      smallReeR L 4 t * smallReeR L 5 (s * t) * smallReeR L 1 s := by
    calc smallReeR L 1 s * smallReeR L 4 t
        = smallReeR L 1 s * (smallReeR L 4 t * (smallReeR L 1 s)⁻¹) * smallReeR L 1 s := by
            group
      _ = smallReeR L 1 s * ((smallReeR L 1 s)⁻¹ * smallReeR L 4 t * smallReeR L 5 (s * t)) *
            smallReeR L 1 s := by rw [hcolg]
      _ = smallReeR L 4 t * smallReeR L 5 (s * t) * smallReeR L 1 s := by group
  have hzb : Commute (smallReeR L 5 (s * t)) (smallReeR L 4 t) :=
    smallReeR_comm (i := 4) (j := 5) (by decide) (by decide) (by decide) (by decide) t (s * t)
  rw [commutatorElement_def, hswap]
  rw [← hzb.eq]
  group

private theorem smallReeR_finiteReeAut {L : Type} [Field L] [Finite L]
    [CharP L ReeTag.G2.prime] (a : ℕ) :
    ReeTag.G2.finiteReeAut L a (smallReeR L 4 1 * smallReeR L 2 (-1)) =
      smallReeR L 2 1 * smallReeR L 4 (-1) := by
  have hodd : Odd (3 * 3 ^ a) := by
    rw [mul_comm, ← pow_succ]
    exact Odd.pow (by decide : Odd 3)
  have hF1 : ReeTag.G2.finiteReeAut L a (smallReeR L 4 1) = smallReeR L 2 1 := by
    have h := (ReeTag.small_Ree_positive_root_F_parameters L a 1).2.2.2.1
    simpa [smallReeR, one_pow] using h
  have hF2 : ReeTag.G2.finiteReeAut L a (smallReeR L 2 (-1)) = smallReeR L 4 (-1) := by
    have h := (ReeTag.small_Ree_positive_root_F_parameters L a (-1)).2.2.1
    have hsig : smallReeSigma (K := L) a (-1) = -1 := by
      show (-1 : L) ^ (3 * 3 ^ a) = -1
      exact hodd.neg_one_pow
    simpa [smallReeR, hsig] using h
  rw [map_mul, hF1, hF2]

private theorem smallReeR_inv {L : Type} [Field L] :
    (smallReeR L 4 1 * smallReeR L 2 (-1))⁻¹ = smallReeR L 2 1 * smallReeR L 4 (-1) := by
  have h2 : (smallReeR L 2 (-1))⁻¹ = smallReeR L 2 1 := by
    simpa using (smallReeR_neg (L := L) 2 (-1)).symm
  have h4 : (smallReeR L 4 1)⁻¹ = smallReeR L 4 (-1) := (smallReeR_neg (L := L) 4 1).symm
  rw [mul_inv_rev, h2, h4]

private theorem smallReeR_order_good {L : Type} [Field L] [Finite L] [CharP L 3] (a : ℕ)
    (ha : 1 ≤ a) (hL : Nat.card L = 3 ^ (2 * a + 1)) :
    orderOf (smallReeR L 4 1 * smallReeR L 2 (-1)) = 3 ∧
      IsSpecialGood 3 (smallReeR L 4 1 * smallReeR L 2 (-1)) := by
  classical
  have h3 : 3 < 3 ^ (2 * a + 1) := by
    calc 3 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hza : ∀ s t : L, Commute (smallReeR L 5 s) (smallReeR L 1 t) := smallReeR_comm15
  have hzb : ∀ s t : L, Commute (smallReeR L 5 s) (smallReeR L 4 t) := smallReeR_comm45
  have hwa : ∀ s t : L, Commute (smallReeR L 2 s) (smallReeR L 1 t) := smallReeR_comm12
  have hwb : ∀ s t : L, Commute (smallReeR L 2 s) (smallReeR L 4 t) := smallReeR_comm24
  exact isSpecialGood_mul_of_comm (K := L)
    (S := adjointGroup ReeTag.G2.tag L) (p := 3) (e := 2 * a + 1)
    (xa := smallReeR L 1) (xb := smallReeR L 4) (z := smallReeR L 5) (w := smallReeR L 2)
    Nat.prime_three (by norm_num) hL h3 (smallReeR_add 1) (smallReeR_add 4)
    (smallReeR_add 5) (smallReeR_injective 5) smallReeR_commutator hza hzb
    (smallReeR_add 2) hwa hwb (-AddMonoidHom.id L) one_ne_zero

theorem exists_ree_inv_good (a : ℕ) (L : Type) [Field L] [Finite L] [CharP L ReeTag.G2.prime]
    (ha : 1 ≤ a) (hL : Nat.card L = 3 ^ (2 * a + 1)) :
    ∃ x : adjointGroup ReeTag.G2.tag L, orderOf x = 3 ∧
      ReeTag.G2.finiteReeAut L a x = x⁻¹ ∧ IsSpecialGood 3 x := by
  obtain ⟨hord, hgood⟩ := smallReeR_order_good a ha hL
  refine ⟨smallReeR L 4 1 * smallReeR L 2 (-1), hord, ?_, hgood⟩
  rw [smallReeR_finiteReeAut, smallReeR_inv]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
