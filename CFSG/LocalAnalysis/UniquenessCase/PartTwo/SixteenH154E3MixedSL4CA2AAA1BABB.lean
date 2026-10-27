module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA1BABA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl4_fpf_conj {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hrow : s16h_H5RowSL2 L U Z 2) (f : MulAut W) {b : MulAut W}
    (hb : b ∈ L.map (MulAut.conj f).toMonoidHom) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    ∀ u ∈ U.map f.toMonoidHom,
      b u * u⁻¹ ∈ Z.map f.toMonoidHom → u ∈ Z.map f.toMonoidHom := by
  obtain ⟨a, haL, haeq⟩ := Subgroup.mem_map.mp hb
  have ha : a = MulAut.conj f⁻¹ b := by
    rw [← haeq]
    ext v
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow, hb3, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hb1
    rw [← haeq, h, map_one]
  intro u hu huZ
  obtain ⟨v, hvU, hv⟩ := Subgroup.mem_map.mp hu
  have hbu : b u = f (a v) := by
    rw [← haeq, ← hv]
    simp [MulAut.conj_apply, MulAut.mul_apply]
  have hkey : b u * u⁻¹ = f (a v * v⁻¹) := by
    have hiv : ((MulEquiv.toMonoidHom f) v)⁻¹ = f (v⁻¹) := by
      rw [← map_inv]
      rfl
    rw [hbu, ← hv, hiv, ← map_mul]
  have hZ : a v * v⁻¹ ∈ Z := by
    rw [hkey] at huZ
    exact (Subgroup.mem_map_iff_mem (f := f.toMonoidHom) f.injective).mp huZ
  have hvZ : v ∈ Z := s16h_sl4_fpf_of_row hrow haL ha3 ha1 v hvU hZ
  exact hv ▸ Subgroup.mem_map_of_mem f.toMonoidHom hvZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
