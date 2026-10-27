module

public import CFSG.RankThree.PartOne.SolD3.USpecial
public import CFSG.RankThree.PartOne.SolD3.Inputs3
public import CFSG.CGT.PushingUpLit.STT.SzU3

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76X
open scoped Matrix LinearAlgebra.Projectivization commutatorElement

noncomputable section

theorem sylowSpecial_Sz (a : ℕ) (ha : 1 ≤ a) : SylowSpecial (Sz a) := by
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  let e := (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a).symm).trans
    (MulEquiv.subgroupCongr hmodel)
  have : Finite (Sz a) := Finite.of_surjective e e.surjective
  exact (sylowSpecial_suzukiMatrixGroup a (by omega)).map_mulEquiv e

theorem sylowSpecial_PSU3 (f : ℕ) (hf : 2 ≤ f) : SylowSpecial (PSU3 2 f) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_injective
    (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hB := sylowSpecial_projectiveSpecialUnitary J f hf hKcard hfixed hJ
  let e := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e' := e.trans (MulEquiv.subgroupCongr hmodel)
  have : Finite (PSU3 2 f) := Finite.of_surjective e' e'.surjective
  exact hB.map_mulEquiv e'

theorem sylowSpecial_of_isSzOrU3 {L : Type} [Group L] [Finite L] (h : IsSzOrU3 L) :
    SylowSpecial L := by
  rcases h with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  · have : Finite (Sz a) := Finite.of_equiv L e.toEquiv
    exact (sylowSpecial_Sz a ha).map_mulEquiv e.symm
  · have : Finite (PSU3 2 f) := Finite.of_equiv L e.toEquiv
    exact (sylowSpecial_PSU3 f hf).map_mulEquiv e.symm

theorem szU3SylowIndecomposable : SzU3SylowIndecomposable := by
  intro G _ _ hSz Q W R hW hWQ hRQ hcent hWR hdec
  have hsp := sylowSpecial_of_isSzOrU3 (CFSG.CGT.PushingUpLit.STT.isSzOrU3_of_stated hSz) Q
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
  have hwc : (⟨w, hWQ hwW⟩ : ↥(Q : Subgroup G)) ∈ Subgroup.center ↥(Q : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent w hwW g g.2).symm
  have hcomm := hsp hwc
  have hle : commutator ↥(Q : Subgroup G) ≤ R.subgroupOf (Q : Subgroup G) := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨w₁, hw₁, r₁, hr₁, hx⟩ := hdec x x.2
    obtain ⟨w₂, hw₂, r₂, hr₂, hy⟩ := hdec y y.2
    have hconj : ∀ u ∈ W, ∀ g ∈ (Q : Subgroup G), u * g * u⁻¹ = g := by
      intro u hu g hg
      have := hcent u hu g hg
      rw [this]
      group
    rw [Subgroup.mem_subgroupOf, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx, hy]
    have h1 : w₁ * r₁ * (w₂ * r₂) * (w₁ * r₁)⁻¹ * (w₂ * r₂)⁻¹ =
        w₂ * (w₁ * (r₁ * r₂ * r₁⁻¹) * w₁⁻¹) * r₂⁻¹ * w₂⁻¹ := by
      have e1 : w₁ * r₁ * w₂ = w₂ * (w₁ * r₁) := by
        have := hconj w₂ hw₂ (w₁ * r₁) (Q.mul_mem (hWQ hw₁) (hRQ hr₁))
        calc w₁ * r₁ * w₂ = (w₂ * (w₁ * r₁) * w₂⁻¹) * w₂ := by rw [this]
          _ = w₂ * (w₁ * r₁) := by group
      calc w₁ * r₁ * (w₂ * r₂) * (w₁ * r₁)⁻¹ * (w₂ * r₂)⁻¹
          = (w₁ * r₁ * w₂) * r₂ * (w₁ * r₁)⁻¹ * (w₂ * r₂)⁻¹ := by group
        _ = (w₂ * (w₁ * r₁)) * r₂ * (w₁ * r₁)⁻¹ * (w₂ * r₂)⁻¹ := by rw [e1]
        _ = w₂ * (w₁ * (r₁ * r₂ * r₁⁻¹) * w₁⁻¹) * r₂⁻¹ * w₂⁻¹ := by group
    have h2 : w₁ * (r₁ * r₂ * r₁⁻¹) * w₁⁻¹ = r₁ * r₂ * r₁⁻¹ := by
      refine hconj w₁ hw₁ _ ?_
      exact Q.mul_mem (Q.mul_mem (hRQ hr₁) (hRQ hr₂)) (Q.inv_mem (hRQ hr₁))
    have h3 : w₂ * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * w₂⁻¹ = r₁ * r₂ * r₁⁻¹ * r₂⁻¹ := by
      refine hconj w₂ hw₂ _ ?_
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem (hRQ hr₁) (hRQ hr₂)) (Q.inv_mem (hRQ hr₁)))
        (Q.inv_mem (hRQ hr₂))
    rw [h1, h2]
    have h4 : w₂ * (r₁ * r₂ * r₁⁻¹) * r₂⁻¹ * w₂⁻¹ = w₂ * (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) * w₂⁻¹ := by
      group
    rw [h4, h3]
    exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)
  have hwR : (⟨w, hWQ hwW⟩ : ↥(Q : Subgroup G)) ∈ R.subgroupOf (Q : Subgroup G) := hle hcomm
  have hwR' : w ∈ R := hwR
  have : w ∈ W ⊓ R := Subgroup.mem_inf.2 ⟨hwW, hwR'⟩
  rw [hWR, Subgroup.mem_bot] at this
  exact hw1 (Subtype.ext this)

end

end CFSG.RankThree.PartOne.SolD3
