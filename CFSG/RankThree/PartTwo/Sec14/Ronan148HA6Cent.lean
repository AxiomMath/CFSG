module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HOneLine

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Cent

set_option linter.unusedSectionVars false


open CFSG.RankThree.Native.ONTriple in
theorem part_two_M_center {A : Subgroup GM} (hA : Late.IsE27 A) {a : GM} (ha : a ∈ A)
    (haz : a ∉ Subgroup.zpowers zG) :
    ∃ K : Subgroup GM, IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
      Subgroup.centralizer {a} = Subgroup.zpowers a ⊔ K ∧ Subgroup.zpowers a ⊓ K = ⊥ ∧
      zG ∈ K := by
  obtain ⟨P, hAP⟩ := (isPGroup_of_E27 hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hP : (MulAut.conj g).toMonoidHom a ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.mem_map_of_mem _ (hAP ha)
  have hz : (MulAut.conj g).toMonoidHom a ∉ Subgroup.zpowers zG := by
    intro h
    apply haz
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_zpowers zG ▸ Subgroup.mem_map_of_mem
      (MulAut.conj g⁻¹).toMonoidHom h
    have e1 : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom a) = a := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e1, conj_zG] at h'
    exact h'
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 hP hz
  set n := g⁻¹ * wordN w
  have han : a = n * (xG 0 ^ 1 * zG ^ c) * n⁻¹ := by
    rw [pow_one, ← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  obtain ⟨h1, h2⟩ := centralizer_conj n (α := 1) (by norm_num) c
  rw [← han] at h1 h2
  exact ⟨_, map_conj_K0 n, h1, h2, ⟨zG, zG_mem_K0, conj_zG n⟩⟩

variable {X : Type} [Group X] [Finite X]

open CFSG.RankThree.Native.ONTriple in
theorem exists_centralizer_eq (hperf : Group.IsPerfect X)
    (hT : IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) {q : X} (hqP : q ∈ P) (hqZ : q ∉ Subgroup.center X) :
    ∃ K : Subgroup X, IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
      Subgroup.centralizer {q} = Subgroup.zpowers q ⊔ K ∧ Subgroup.zpowers q ⊓ K = ⊥ ∧
      Subgroup.center X ≤ K := by
  obtain ⟨φ, j, -, hPφ, hc⟩ := exists_model_AG hperf hT hP
  have hA : Late.IsE27 (AG j) := hPφ ▸ Sec13.ON134.isE27_map hP φ.toMonoidHom φ.injective
  have ha : φ q ∈ AG j := hPφ ▸ ⟨q, hqP, rfl⟩
  have haz : φ q ∉ Subgroup.zpowers zG := fun h => hqZ ((hc q).mpr h)
  obtain ⟨K, hK, hC, hI, hz⟩ := part_two_M_center hA ha haz
  have hcomap : ∀ H : Subgroup GM, H.comap φ.toMonoidHom = H.map φ.symm.toMonoidHom := fun H =>
    (Subgroup.map_equiv_eq_comap_symm φ.symm H).symm
  have hzq : (Subgroup.zpowers (φ q)).comap φ.toMonoidHom = Subgroup.zpowers q := by
    rw [hcomap, MonoidHom.map_zpowers]
    simp
  have hCq : (Subgroup.centralizer {φ q}).comap φ.toMonoidHom = Subgroup.centralizer {q} := by
    ext x
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact φ.injective (by rw [map_mul, map_mul, h])
    · intro h
      rw [← map_mul, ← map_mul, h]
  refine ⟨K.comap φ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · refine Sec4.Sporadic.J2.isExtOf_of_mulEquiv ?_ hK
    exact (φ.subgroupMap (K.comap φ.toMonoidHom)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective φ.surjective K))
  · rw [← hCq, hC, ← hzq, hcomap, hcomap, hcomap, Subgroup.map_sup]
  · rw [← hzq, ← Subgroup.comap_inf, hI, MonoidHom.comap_bot,
      (MonoidHom.ker_eq_bot_iff _).mpr φ.injective]
  · intro x hx
    exact (Subgroup.zpowers_le.mpr hz) ((hc x).mp hx)

end Cent

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
