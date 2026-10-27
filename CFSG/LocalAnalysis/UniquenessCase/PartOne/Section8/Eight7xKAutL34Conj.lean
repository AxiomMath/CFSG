module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts.L34

theorem exists_conj_of_orderOf_three_psl_three_four {L : Type} [Group L]
    (hL : CFSG.Blueprint.LieModel L .PSL 3 2 2) {x y : L} (hx : orderOf x = 3)
    (hy : orderOf y = 3) : ∃ g : L, g⁻¹ * x * g = y := by
  classical
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : Finite (projectiveSL 3 K) :=
    Nat.finite_of_card_ne_zero (by rw [card_projectiveSL hK4]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx' : orderOf (φ x) = 3 :=
    (orderOf_injective φ.toMonoidHom φ.injective x).trans hx
  have hy' : orderOf (φ y) = 3 :=
    (orderOf_injective φ.toMonoidHom φ.injective y).trans hy
  have hx'1 : φ x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx'; omega
  have hy'1 : φ y ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy'; omega
  have hxP : IsPGroup 3 (Subgroup.zpowers (φ x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx']; norm_num)
  have hyP : IsPGroup 3 (Subgroup.zpowers (φ y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy']; norm_num)
  obtain ⟨Sx, hxSx⟩ := hxP.exists_le_sylow
  obtain ⟨Sy, hySy⟩ := hyP.exists_le_sylow
  have hxSxm : φ x ∈ (Sx : Subgroup (projectiveSL 3 K)) := hxSx (Subgroup.mem_zpowers _)
  have hySym : φ y ∈ (Sy : Subgroup (projectiveSL 3 K)) := hySy (Subgroup.mem_zpowers _)
  have hSxcard : Nat.card (Sx : Subgroup (projectiveSL 3 K)) = 9 := by
    rw [Sylow.card_eq_multiplicity Sx, factorization_card hK4]; norm_num
  have hSycard : Nat.card (Sy : Subgroup (projectiveSL 3 K)) = 9 := by
    rw [Sylow.card_eq_multiplicity Sy, factorization_card hK4]; norm_num
  obtain ⟨a, ha⟩ := exists_eq_map_conj_eZero hK4 hSxcard
  obtain ⟨b, hb⟩ := exists_eq_map_conj_eZero hK4 hSycard
  set c : projectiveSL 3 K := b * a⁻¹ with hc
  have hhom : (MulAut.conj c).toMonoidHom.comp (MulAut.conj a).toMonoidHom
      = (MulAut.conj b).toMonoidHom := by
    rw [hc]
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hconj : Sy = Sx.map (MulAut.conj c).toMonoidHom := by
    rw [ha, hb, Subgroup.map_map, hhom]
  have hmem : c * φ x * c⁻¹ ∈ (Sy : Subgroup (projectiveSL 3 K)) := by
    rw [hconj]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hxSxm
  have hmem1 : c * φ x * c⁻¹ ≠ 1 := by
    intro h
    apply hx'1
    calc φ x = c⁻¹ * (c * φ x * c⁻¹) * c := by group
      _ = c⁻¹ * 1 * c := by rw [h]
      _ = 1 := by group
  obtain ⟨n, _, hnconj⟩ :=
    exists_mem_normalizer_conj_eq_of_card_eq_nine hK4 (E := (Sy : Subgroup (projectiveSL 3 K)))
      hSycard hmem hmem1 hySym hy'1
  have hz : (n * c) * φ x * (n * c)⁻¹ = φ y := by
    rw [← hnconj]; group
  refine ⟨φ.symm (n * c)⁻¹, ?_⟩
  apply φ.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
  exact hz

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
