module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLDiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem centralizes_center_PSL
    {d : ℕ} {K : Type} [Field K] [Finite K]
    {M : Type} [Group M] {L' E : Subgroup M}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ') (hker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    (hdiag : ∀ e : E, ∃ t : Fin d → K,
      TypeANbrDvd.ActsDiag φ' (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t)
    (z : M) (hz : z ∈ L' ⊓ Subgroup.centralizer (L' : Set M)) :
    z ∈ Subgroup.centralizer (E : Set M) := by
  let zL : L' := ⟨z, hz.1⟩
  have hzLcenter : zL ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    show (l : M) * (zL : M) = (zL : M) * (l : M)
    exact Subgroup.mem_centralizer_iff.mp hz.2 l l.2
  obtain ⟨g, hg⟩ := hφs zL
  have hconj : ∀ y : SpecialLinearGroup (Fin d) K, φ' (g * y * g⁻¹) = φ' y := by
    intro y
    have hzy : φ' y * zL = zL * φ' y := Subgroup.mem_center_iff.mp hzLcenter (φ' y)
    rw [map_mul, map_mul, map_inv, hg, ← hzy]
    group
  obtain ⟨c, hc⟩ := TypeANbrDvd.exists_scalar_of_map_conj_eq hker hconj
  have hgdiag : (g : Matrix (Fin d) (Fin d) K).IsDiag := by
    rw [hc]
    intro i j hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨t, hact⟩ := hdiag ⟨e, he⟩
  have hfix : L'.normalizerMonoidHom ⟨e, hE he⟩ (φ' g) = φ' g :=
    hact.apply_of_isDiag hgdiag
  have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE he⟩ (φ' g)
  have hzg : ((φ' g : L') : M) = z := by rw [hg]
  have h1 : e * z * e⁻¹ = z := by
    rw [← hzg]
    rw [← hcoe, hfix]
  calc e * z = (e * z * e⁻¹) * e := by group
    _ = z * e := by rw [h1]

theorem mem_diagImage_of_commute_pTorsion_SL_all
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ') (hker : ∀ g, φ' g = 1 → g ∈ scalars d K) (c : L')
    (hc : ∀ s : SpecialLinearGroup (Fin d) K,
      (∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v) → s ^ p = 1 →
        c * φ' s = φ' s * c) :
    ∃ s : SpecialLinearGroup (Fin d) K,
      (∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v) ∧ φ' s = c := by
  classical
  obtain ⟨s, hs⟩ := hφs c
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := K) hp hpK
  have hp2 : p ≠ 2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one (K := K) hpK
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hsd : (s : Matrix (Fin d) (Fin d) K).IsDiag := by
    refine TypeANbrDvd.isDiag_of_conj_comm hker hd hζinv (fun k l _ D hD => ?_)
    have hDp : D ^ p = 1 :=
      TypeANbrDvd.pow_eq_one_of_diagonal hD (TypeA.pow_ggPairVec hζp)
    have hcD : c * φ' D = φ' D * c := hc D ⟨TypeA.ggPairVec k l ζ, hD⟩ hDp
    have hφsD : φ' s * φ' D = φ' D * φ' s := by rw [hs]; exact hcD
    calc MulAut.conj (φ' s) * MulAut.conj (φ' D)
        = MulAut.conj (φ' s * φ' D) := by rw [map_mul]
      _ = MulAut.conj (φ' D * φ' s) := by rw [hφsD]
      _ = MulAut.conj (φ' D) * MulAut.conj (φ' s) := by rw [map_mul]
  refine ⟨s, ⟨fun i => (s : Matrix (Fin d) (Fin d) K) i i, ?_⟩, hs⟩
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact hsd hij

end CFSG.StandardType
