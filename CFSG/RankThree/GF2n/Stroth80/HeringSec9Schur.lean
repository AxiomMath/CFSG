module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {Q Z M : Subgroup G} {K : Type} [Field K] {γ : G → K}

section Uline

variable {B : Subgroup G}

theorem Uline_conj_mem (hc : Ctx M Q Z B) {Y : Subgroup G} (hYM : Y ≤ M) {y : G} (hy : y ∈ Y)
    {x : G} (hx : x ∈ Uline Z B Y) : y * x * y⁻¹ ∈ Uline Z B Y := by
  have hle : Uline Z B Y ≤ (Uline Z B Y).comap (MulAut.conj y).toMonoidHom := by
    refine sup_le ?_ (iSup₂_le fun y' hy' => ?_)
    · intro z hz
      have : y * z * y⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hYM hy)) z).mp hz
      exact Subgroup.mem_sup_left this
    · intro x hx
      rw [Subgroup.mem_comap]
      have h1 : y * x * y⁻¹ ∈ conjSubgroup (y * y') B := by
        rw [mem_conjSubgroup]
        rw [mem_conjSubgroup] at hx
        have e : (y * y')⁻¹ * (y * x * y⁻¹) * (y * y') = y'⁻¹ * x * y' := by group
        rw [e]
        exact hx
      exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (y * y')
        (Subgroup.mem_iSup_of_mem (Y.mul_mem hy hy') h1))
  have := hle hx
  simpa [MulAut.conj_apply] using this

theorem conj_Uline (hc : Ctx M Q Z B) {Y : Subgroup G} (hYM : Y ≤ M) {y : G} (hy : y ∈ Y) :
    conjSubgroup y (Uline Z B Y) = Uline Z B Y := by
  ext x
  rw [mem_conjSubgroup]
  constructor
  · intro h
    have := Uline_conj_mem hc hYM hy h
    simpa [mul_assoc] using this
  · intro h
    have := Uline_conj_mem hc hYM (Y.inv_mem hy) h
    simpa using this

theorem Z_le_Uline (Z B Y : Subgroup G) : Z ≤ Uline Z B Y := le_sup_left

theorem B_le_Uline (Z B Y : Subgroup G) : B ≤ Uline Z B Y := by
  intro b hb
  refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
    (Subgroup.mem_iSup_of_mem Y.one_mem ?_))
  rw [mem_conjSubgroup]
  simpa using hb

theorem Uline_le_Q (hc : Ctx M Q Z B) {Y : Subgroup G} (hYM : Y ≤ M) : Uline Z B Y ≤ Q := by
  refine sup_le hc.hyp.Z_normal.1 (iSup₂_le fun y hy => ?_)
  intro x hx
  rw [mem_conjSubgroup] at hx
  have hb : y⁻¹ * x * y ∈ Q := hc.le hx
  have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hYM hy)) _).mp hb
  simpa [mul_assoc] using this

end Uline

end HS9

end CFSG.RankThree.GF2n.Stroth80
