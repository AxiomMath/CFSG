module

public import CFSG.RankThree.PartOne.Q1327T.Defs
public import CFSG.RankThree.PartOne.Q1327S.Weyl

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T

variable {p g : ℕ} {Q : Type} [Group Q] {Ē : Subgroup Q}

theorem mem_of_pow_eq_one (h : Row8Conf p g Q Ē) (hZ : Subgroup.center Q = ⊥) {y : Q}
    (hy : y ∈ Subgroup.centralizer (Ē : Set Q)) (hyp : y ^ p = 1) : y ∈ Ē := by
  have := h.elem
  have hz : IsElementaryAbelian p (Subgroup.zpowers y) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hyp
  have hzc : Subgroup.zpowers y ≤ Subgroup.centralizer (Ē : Set Q) :=
    Subgroup.zpowers_le.2 hy
  have hF : IsElementaryAbelian p ↥(Ē ⊔ Subgroup.zpowers y : Subgroup Q) :=
    IsElementaryAbelian.sup_of_le_centralizer hzc
  have hEc : Ē ≤ Subgroup.centralizer (Ē : Set Q) := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun f hf =>
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := Ē)).comm ⟨f, hf⟩ ⟨e, he⟩)
  have := h.max (Ē ⊔ Subgroup.zpowers y) hF (sup_le hEc hzc) le_sup_left
  rw [hZ, sup_bot_eq] at this
  exact this (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))

theorem p_sq_dvd_card [Finite Q] (h : Row8Conf p g Q Ē) : p ^ 2 ∣ Nat.card Q := by
  have := Subgroup.card_subgroup_dvd_card Ē
  rwa [h.card] at this

theorem le_centralizer_of_perm3 [Finite Q] (h : Row8Conf p g Q Ē)
    (hZ : Subgroup.center Q = ⊥) (hW : Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)))
    {P : Subgroup Q} (hP : IsPGroup p P) (hEP : Ē ≤ P) :
    P ≤ Subgroup.centralizer (Ē : Set Q) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.elem
  obtain ⟨φ⟩ := hW
  exact le_centralizer_of_weyl_coprime (fun y hy hyp => mem_of_pow_eq_one h hZ hy hyp)
    (not_dvd_card_of_perm3 φ h.prime h.five_le) hP hEP

end CFSG.RankThree.PartOne.Q1327S
