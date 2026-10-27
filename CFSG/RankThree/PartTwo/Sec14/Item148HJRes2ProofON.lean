module

public import CFSG.RankThree.PartTwo.Sec14.ONCoverProofModel
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof

public section

namespace CFSG.RankThree.PartTwo.Sec14.HJRes2

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree.Native.ONTriple CFSG.RankThree.PartTwo Subgroup

theorem not_mem_of_isPerfect_model
    {g : GM} (hg3 : g ^ 3 = 1)
    (hgz : g ∉ zpowers zG) {X : Subgroup GM} (hXp : Group.IsPerfect X)
    (hXg : X ≤ centralizer {g}) : g ∉ X := by
  intro hgX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg1 : g ≠ 1 := fun h => hgz (h ▸ one_mem _)
  have hp : IsPGroup 3 (zpowers g) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hg3 hg1)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hgP : (MulAut.conj a).toMonoidHom g ∈ P0G := by
    rw [← P0Syl_coe, ← ha, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP (mem_zpowers g))
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 hgP (conj_not_mem_zpowers hgz a)
  set n := a⁻¹ * wordN w with hn
  have hgn : n⁻¹ * g * n = xG 0 * zG ^ c := by
    rw [← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  set φ := (MulAut.conj n⁻¹).toMonoidHom with hφ
  have hφg : φ g = xG 0 * zG ^ c := by
    rw [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgn]
  have hX'C : X.map φ ≤ centralizer {xG 0} := by
    have h1 : (centralizer {g}).map φ = centralizer {xG 0} := by
      rw [hφ, map_conj_centralizer, inv_inv, hgn, centralizer_mul_zpow]
    rw [← h1]
    exact map_mono hXg
  have hX'p : Group.IsPerfect (X.map φ) := by
    have := hXp
    exact Group.IsPerfect.map φ
  have hX'K : X.map φ ≤ K0G := by
    have := hX'p
    exact Sec15.ONCoverCent.le_K0_of_isPerfect hX'C
  have hmem : xG 0 ^ 1 * zG ^ c ∈ zpowers (xG 0 ^ 1 * zG ^ c) ⊓ K0G := by
    refine ⟨mem_zpowers _, ?_⟩
    rw [pow_one, ← hφg]
    exact hX'K (mem_map_of_mem φ hgX)
  rw [(centralizer_base (α := 1) (by norm_num) c).2, mem_bot, pow_one, ← hφg] at hmem
  exact hg1 ((map_eq_one_iff φ (MulAut.conj n⁻¹).injective).mp hmem)

theorem not_mem_of_isPerfect_of_isTripleCover
    {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (hT : Sec4.IsTripleCover X Blueprint.NativeSporadic.ON) {g : X}
    (hg3 : g ^ 3 = 1) (hgz : g ∉ center X) {K : Subgroup X} (hKp : Group.IsPerfect K)
    (hKg : K ≤ centralizer {g}) : g ∉ K := by
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hT
  intro hgK
  have hKp' : Group.IsPerfect (K.map ψ.toMonoidHom) := by
    have := hKp
    exact Group.IsPerfect.map ψ.toMonoidHom
  refine not_mem_of_isPerfect_model (g := ψ g) (by rw [← map_pow, hg3, map_one])
    (fun h => hgz ((Sec13.ON134.mem_center_iff_model ψ).2 h)) hKp' ?_
    (mem_map_of_mem ψ.toMonoidHom hgK)
  rintro _ ⟨k, hk, rfl⟩
  have hk' := mem_centralizer_singleton_iff.mp (hKg hk)
  rw [mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, hk']

end CFSG.RankThree.PartTwo.Sec14.HJRes2
