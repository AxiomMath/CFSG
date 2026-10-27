module

public import CFSG.RankThree.Co2.CrMat
public import CFSG.RankThree.Co2.CmWords

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Co2Inv


theorem crMat_mem_Cm (x : Cr) : crMat x ∈ Cm := by
  let S : Subgroup Cr :=
    { Submonoid.comap crMat Cm with
      inv_mem' := fun {a} ha => by
        have hn : orderOf a ≠ 0 := (orderOf_pos a).ne'
        have e : a ^ (orderOf a - 1) = a⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hn, pow_orderOf_eq_one])
        change crMat a⁻¹ ∈ Cm
        rw [← e, map_pow]
        exact Submonoid.pow_mem Cm ha _ }
  have hle : Subgroup.closure (gC '' {j | j < 21}) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    change crMat (gC j) ∈ Cm
    have hj' : j < 21 := hj
    have e : letterCr j = gC j := by
      unfold letterCr
      rw [if_pos hj']
    rw [← e, crMat_eq_of_hasRows (hasRows_letterCr (by omega))]
    exact letterMat_mem_Cm (by omega)
  exact hle (closure_gC ▸ Subgroup.mem_top x)

theorem isConj_iff_crConj {c : ℕ} (hc : c < 10) {y : Cr} :
    IsConj (rep c) y ↔ CrConj (repMat c) (crMat y) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    refine ⟨crMat g, crMat_mem_Cm g, ?_⟩
    rw [← crMat_rep hc, ← map_mul, ← map_mul, ← hg, inv_mul_cancel_right]
  · rintro ⟨g, hg, e⟩
    obtain ⟨g', rfl⟩ := MonoidHom.mem_mrange.1 (Cm_le_mrange hg)
    have e' : g' * rep c = y * g' := by
      apply crMat_injective
      rw [map_mul, map_mul, crMat_rep hc]
      exact e
    exact isConj_iff.2 ⟨g', by rw [e', mul_inv_cancel_right]⟩

end CFSG.RankThree.Co2

end
