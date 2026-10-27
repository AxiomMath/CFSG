module
public import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter
open scoped Pointwise
universe u

public theorem isComplement_map_conj
    {H : Type u} [Group H] [Finite H]
    (A B : Subgroup H) (g : H) (h : A.IsComplement' B) :
    (A.map (MulAut.conj g).toMonoidHom).IsComplement'
      (B.map (MulAut.conj g).toMonoidHom) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_mul]
  · rw [disjoint_iff]
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨hzA, hzB⟩
      rcases Subgroup.mem_map.mp hzA with ⟨a, ha, hfa⟩
      rcases Subgroup.mem_map.mp hzB with ⟨b, hb, hfb⟩
      have habf : (MulAut.conj g) a = (MulAut.conj g) b := by
        exact hfa.trans hfb.symm
      have hab : a = b := (MulAut.conj g).injective habf
      have hab' : a ∈ A ⊓ B := ⟨ha, hab ▸ hb⟩
      have haone : a = 1 := Subgroup.mem_bot.mp (h.disjoint.le_bot hab')
      have hzone : z = 1 := by
        rw [← hfa, haone]
        simp
      exact Subgroup.mem_bot.mpr hzone
    · exact bot_le

public theorem normalComplement_conj
    {H : Type u} [Group H] [Finite H]
    (P Q : Subgroup H) (g : H)
    (hQnormal : Q.Normal)
    (hcomp : Q.IsComplement' (Subgroup.normalizer (P : Set H))) :
    (Q.map (MulAut.conj g).toMonoidHom).Normal ∧
      (Q.map (MulAut.conj g).toMonoidHom).IsComplement'
        (Subgroup.normalizer
          ((P.map (MulAut.conj g).toMonoidHom) : Set H)) := by
  have hmap := isComplement_map_conj Q
    (Subgroup.normalizer (P : Set H)) g hcomp
  constructor
  · exact hQnormal.map (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective
  · rw [← Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)]
    exact hmap

end CFSG.GorensteinWalter
