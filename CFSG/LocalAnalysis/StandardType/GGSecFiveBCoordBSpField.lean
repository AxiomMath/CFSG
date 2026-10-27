module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSpDefs
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppSp
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem GGSecFiveBCoordBLabel.dvd_two_pow_sub_one_of_tag {n p : ℕ} {lab : LargeEvenLabel}
    (h : GGSecFiveBCoordBLabel n p lab) (ht : lab.tag = .B ∨ lab.tag = .C) (hm : 2 ≤ lab.n) :
    p ∣ 2 ^ lab.n - 1 := by
  rcases h with ⟨-, -, h | ⟨h, -⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · omega
  all_goals rcases ht with ht | ht <;> rw [ht] at h <;> exact absurd h (by decide)

theorem GGInnerDiagOnLabel.bCoordB_dvd_two_pow_sub_one {G : Type} [Group G] {p n f : ℕ}
    {Bs L : Subgroup G}
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L)
    (hRig : GGLabelRigidInput) (hn : 3 ≤ n) (hf : 2 ≤ f)
    (eL : ↥L ≃* StatedSp (n - 1) (GaloisField 2 f)) : p ∣ 2 ^ f - 1 := by
  obtain ⟨lab, hlab, has, -, -, -, -, -, hS, -⟩ := largeEvenMarking_exists_hasLabel hL
  have hC : GGHasLabel ⟨.C, n - 1, f⟩ (↥L ⧸ Subgroup.center ↥L) :=
    ggHasLabel_C_of_mulEquiv_statedSp (by omega) hf eL
  have hΛ : LargeEvenInLambda2 ⟨.C, n - 1, f⟩ :=
    ⟨show 1 ≤ f by omega, show 2 ≤ n - 1 by omega, fun _ => hf⟩
  have key : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = f := by
    rcases hRig lab _ _ hlab hΛ has hC with rfl | ⟨ht, -, -, hfn⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ |
      ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact ⟨Or.inr rfl, rfl⟩
    · exact ⟨ht, hfn⟩
    all_goals simp at h
  obtain ⟨ht, hfn⟩ := key
  rw [← hfn]
  exact GGSecFiveBCoordBLabel.dvd_two_pow_sub_one_of_tag hS ht (by omega)

theorem GGSecFiveBCoordBSpCell.dvd_two_pow_sub_one {G : Type} [Group G] {p n f : ℕ}
    {Bs L K : Subgroup G} {𝒦 : Finset (Subgroup G)} {i0 : Fin n}
    (hcell : GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L)
    (hRig : GGLabelRigidInput) (hn : 3 ≤ n) : p ∣ 2 ^ f - 1 := by
  obtain ⟨hf, -, -, ⟨eL⟩, -⟩ := hcell
  exact hL.bCoordB_dvd_two_pow_sub_one hRig hn hf eL

theorem GGSecFiveBCoordBSpSpCell.dvd_two_pow_sub_one {G : Type} [Group G] {p n f : ℕ}
    {Bs L K : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hcell : GGSecFiveBCoordBSpSpCell p Bs L 𝒦 n eta f K i0)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L)
    (hRig : GGLabelRigidInput) : p ∣ 2 ^ f - 1 := by
  obtain ⟨hf, hn, -, ⟨eL⟩, -⟩ := hcell
  exact hL.bCoordB_dvd_two_pow_sub_one hRig (by omega) hf eL

end CFSG.StandardType

end
