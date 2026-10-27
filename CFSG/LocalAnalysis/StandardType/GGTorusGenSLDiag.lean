module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdCent
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeANormal
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLinePSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem map_diag_pTorsion_mem_E_SL
    {d p : ℕ} {K : Type} [Field K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE)
    {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hdiag : ∀ e : E, ∃ t : Fin d → K,
      TypeANbrDvd.ActsDiag φ' (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t)
    (s : SpecialLinearGroup (Fin d) K)
    (hs : ∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v) (hsp : s ^ p = 1) :
    ((φ' s : L') : M) ∈ E := by
  obtain ⟨v, hv⟩ := hs
  have hmem : ((φ' s : L') : M) ∈ E ⊔ L' := Subgroup.mem_sup_right (φ' s).2
  have hcent : ((φ' s : L') : M) ∈ Subgroup.centralizer (E : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨t, hact⟩ := hdiag ⟨e, he⟩
    have hfix : L'.normalizerMonoidHom ⟨e, hE he⟩ (φ' s) = φ' s :=
      hact.apply_of_isDiag (by rw [hv]; exact isDiag_diagonal v)
    have hcoe := Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE he⟩ (φ' s)
    have h1 : e * ((φ' s : L') : M) * e⁻¹ = ((φ' s : L') : M) := by
      rw [← hcoe, hfix]
    calc e * ((φ' s : L') : M) = (e * ((φ' s : L') : M) * e⁻¹) * e := by group
      _ = ((φ' s : L') : M) * e := by rw [h1]
  have hpow : ((φ' s : L') : M) ^ p = 1 := by
    have hpowL : (φ' s) ^ p = 1 := by rw [← map_pow, hsp, map_one]
    calc ((φ' s : L') : M) ^ p = (((φ' s) ^ p : L') : M) :=
          (map_pow L'.subtype (φ' s) p).symm
      _ = ((1 : L') : M) := by rw [hpowL]
      _ = 1 := map_one L'.subtype
  exact hpos.2.2.2.2.2.1 _ hmem hcent hpow

theorem eq_one_of_mem_center_of_pow_eq_one_PSL
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime) (hd : 4 ≤ d)
    (hpd : ¬ p ∣ d) {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ') (hker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    (z : L') (hz : z ∈ Subgroup.center L') (hzp : z ^ p = 1) : z = 1 := by
  obtain ⟨g, hg⟩ := hφs z
  have hconj : ∀ y, φ' (g * y * g⁻¹) = φ' y := by
    intro y
    have hzy : φ' y * z = z * φ' y := Subgroup.mem_center_iff.mp hz (φ' y)
    rw [map_mul, map_mul, map_inv, hg, ← hzy]
    group
  obtain ⟨c, hc⟩ := TypeANbrDvd.exists_scalar_of_map_conj_eq hker hconj
  have hd0 : 0 < d := by omega
  have hcd : c ^ d = 1 := (TypeA.mem_scalars_of_coe_eq_scalar hd0 hc).1
  have hgd : g ^ d = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hc, ← map_pow,
      hcd, map_one]
  have hzd : z ^ d = 1 := by
    calc z ^ d = (φ' g) ^ d := by rw [hg]
      _ = φ' (g ^ d) := (map_pow φ' g d).symm
      _ = 1 := by rw [hgd, map_one]
  have hgcdn : Nat.gcd p d = 1 := hp.coprime_iff_not_dvd.mpr hpd
  have h1 : z ^ Nat.gcd p d = 1 := (pow_gcd_eq_one).mpr ⟨hzp, hzd⟩
  rwa [hgcdn, pow_one] at h1

theorem mem_diagImage_of_commute_pTorsion_SL
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) (hpd : ¬ p ∣ d)
    {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφs : Function.Surjective φ') (hker : ∀ g, φ' g = 1 → g ∈ scalars d K) (c : L')
    (hc : ∀ s : SpecialLinearGroup (Fin d) K,
      (∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v) → s ^ p = 1 →
        c * φ' s = φ' s * c) :
    ∃ s : SpecialLinearGroup (Fin d) K,
      (∃ v : Fin d → K, (s : Matrix (Fin d) (Fin d) K) = diagonal v) ∧ φ' s = c := by
  classical
  obtain ⟨g, hg⟩ := hφs c
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := K) hp hpK
  have hp2 : p ≠ 2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one (K := K) hpK
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζne1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hd3 : 3 ≤ d := by omega
  have hkey : ∀ k i : Fin d, k ≠ i → (g : Matrix (Fin d) (Fin d) K) k i = 0 := by
    intro k i hki
    obtain ⟨j, hji, -⟩ := TypeANbrDvd.exists_ne_of_two hd3 i i
    have hij : i ≠ j := Ne.symm hji
    let D : SpecialLinearGroup (Fin d) K :=
      ⟨diagonal (TypeA.ggPairVec i j ζ), by
        rw [det_diagonal, TypeA.prod_ggPairVec ζ hζ0]⟩
    have hDm : (D : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec i j ζ) := rfl
    have hDp : D ^ p = 1 :=
      TypeANbrDvd.pow_eq_one_of_diagonal hDm (TypeA.pow_ggPairVec hζp)
    have hcommD : c * φ' D = φ' D * c := hc D ⟨TypeA.ggPairVec i j ζ, hDm⟩ hDp
    let S : SpecialLinearGroup (Fin d) K := g * D * g⁻¹ * D⁻¹
    have hSdef : S = g * D * g⁻¹ * D⁻¹ := rfl
    have hSker : φ' S = 1 := by
      rw [hSdef, map_mul, map_mul, map_mul, map_inv, map_inv, hg, hcommD]
      group
    have hSscal : S ∈ scalars d K := hker S hSker
    obtain ⟨c₀, hc₀d, hc₀m⟩ := mem_scalars.mp hSscal
    have hScenter : S ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) :=
      scalars_le_center d K hSscal
    have hcommSD : S * D = D * S := (Subgroup.mem_center_iff.mp hScenter D).symm
    have hSD : S * D = g * D * g⁻¹ := by
      rw [hSdef]; group
    have hpow : (S * D) ^ p = 1 := by
      rw [hSD]
      change ((MulAut.conj g) D) ^ p = 1
      rw [← map_pow, hDp, map_one]
    have hSp : S ^ p = 1 := by
      have h1 := Commute.mul_pow hcommSD p
      rw [h1, hDp, mul_one] at hpow
      exact hpow
    have hc₀p : (c₀ : K) ^ p = 1 := by
      have hmat : ((S : Matrix (Fin d) (Fin d) K)) ^ p = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_pow, hSp, Matrix.SpecialLinearGroup.coe_one]
      rw [hc₀m, ← map_pow] at hmat
      have := congrFun (congrFun hmat ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa [Matrix.scalar_apply] using this
    have hc₀p_units : c₀ ^ p = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hc₀p, Units.val_one]
    have hc₀ : c₀ = 1 := by
      have h1 : c₀ ^ Nat.gcd p d = 1 := (pow_gcd_eq_one).mpr ⟨hc₀p_units, hc₀d⟩
      rw [hp.coprime_iff_not_dvd.mpr hpd, pow_one] at h1
      exact h1
    have hc₀K : (c₀ : K) = 1 := by rw [hc₀, Units.val_one]
    have hS1 : S = 1 := by
      apply Subtype.ext
      rw [hc₀m, hc₀K, map_one, Matrix.SpecialLinearGroup.coe_one]
    have hgD : g * D = D * g := by
      have h1 : g * D * g⁻¹ = D := by
        rw [← hSD, hS1, one_mul]
      calc g * D = (g * D * g⁻¹) * g := by group
        _ = D * g := by rw [h1]
    have hmat : (g : Matrix (Fin d) (Fin d) K) * (D : Matrix (Fin d) (Fin d) K) =
        (D : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) := by
      have := congrArg (fun x : SpecialLinearGroup (Fin d) K =>
        (x : Matrix (Fin d) (Fin d) K)) hgD
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
    have h1 := congrFun (congrFun hmat k) i
    rw [hDm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have hvi : TypeA.ggPairVec i j ζ i = ζ := by
      rw [TypeA.ggPairVec_apply, ite_eq_left rfl, ite_eq_right hij, mul_one]
    rw [hvi] at h1
    have hvk : TypeA.ggPairVec i j ζ k ≠ ζ := by
      by_cases hkj : k = j
      · subst hkj
        rw [TypeA.ggPairVec_apply, ite_eq_right (Ne.symm hij), ite_eq_left rfl, one_mul]
        exact fun h => hζinv h.symm
      · rw [TypeA.ggPairVec_apply, ite_eq_right hki, ite_eq_right hkj, mul_one]
        exact fun h => hζne1 h.symm
    have h2 : (g : Matrix (Fin d) (Fin d) K) k i * (ζ - TypeA.ggPairVec i j ζ k) = 0 := by
      rw [mul_sub, h1]
      ring
    exact (mul_eq_zero.mp h2).resolve_right (fun h => hvk (sub_eq_zero.mp h).symm)
  have hgdiag : (g : Matrix (Fin d) (Fin d) K) =
      diagonal (fun i => (g : Matrix (Fin d) (Fin d) K) i i) := by
    ext k i
    by_cases hki : k = i
    · subst hki; simp
    · rw [Matrix.diagonal_apply_ne _ hki]
      exact hkey k i hki
  exact ⟨g, ⟨fun i => (g : Matrix (Fin d) (Fin d) K) i i, hgdiag⟩, hg⟩

end CFSG.StandardType
