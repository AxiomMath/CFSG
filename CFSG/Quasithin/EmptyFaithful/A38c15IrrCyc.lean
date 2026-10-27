module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.Quasithin.A38c15

open Matrix CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists

theorem cyc_commutant_mul_comm {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) {A B : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hA : A ∈ commutant H) (hB : B ∈ commutant H) : A * B = B * A := by
  let := commutantField (isIrreducibleOn_iff.mpr hirr)
  exact congrArg Subtype.val (mul_comm (⟨A, hA⟩ : commutant H) ⟨B, hB⟩)

theorem cyc_mulAut_comm {N : Type*} [Group N] [IsCyclic N] (a b : MulAut N) : a * b = b * a :=
  (IsCyclic.mulAutMulEquiv N).injective (by rw [map_mul, map_mul, mul_comm])

theorem cyc_normal_subgroupOf {p : ℕ} [Fact p.Prime] {G H : Subgroup (GL (Fin 3) (ZMod p))}
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) : (H.subgroupOf G).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩

theorem isSolvable_of_cyclic_normal {p : ℕ} [Fact p.Prime]
    {G H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : CFSG.RepresentationTheory.IsIrreducibleMatrixRep H.subtype)
    (hcyc : IsCyclic ↥H) : Group.IsSolvable ↥G := by
  have : (H.subgroupOf G).Normal := cyc_normal_subgroupOf hnorm
  have : IsCyclic ↥(H.subgroupOf G) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hHG).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHG).symm.surjective
  let ρ : ↥G →* MulAut ↥(H.subgroupOf G) := MulAut.conjNormal
  have hker : ∀ a : ↥ρ.ker, ((a : ↥G) : GL (Fin 3) (ZMod p)).1 ∈ commutant H := by
    intro a
    rw [mem_commutant]
    intro x hx
    have h1 : ρ a = 1 := a.2
    have h2 := congrArg (fun f : MulAut ↥(H.subgroupOf G) => ((f ⟨⟨x, hHG hx⟩, by
      simpa [Subgroup.mem_subgroupOf] using hx⟩ : ↥(H.subgroupOf G)) : ↥G)) h1
    simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    have h3 := congrArg (fun y : ↥G => (y : GL (Fin 3) (ZMod p))) h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_iff_eq_mul] at h3
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h3.symm
  have hcomm : ∀ a b : ↥ρ.ker, a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (Units.ext
      (cyc_commutant_mul_comm hirr (hker a) (hker b))))
  have : Group.IsSolvable ↥ρ.ker := Group.isSolvable_of_comm hcomm
  have : Group.IsSolvable (MulAut ↥(H.subgroupOf G)) := Group.isSolvable_of_comm cyc_mulAut_comm
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ (Subgroup.range_subtype _).ge

end CFSG.Quasithin.A38c15
