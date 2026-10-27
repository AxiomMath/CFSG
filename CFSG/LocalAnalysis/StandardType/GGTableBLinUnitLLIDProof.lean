module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLIDPSL

public section

namespace CFSG.StandardType.LinUnitL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggBstarTwoLocalSCr_PSL (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) {r : ℕ}
    (hrd : d - 2 ≤ r) :
    GGBstarTwoLocalSCr p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf AB As hle hA hAI hAs hr h3 hmax
  have := Fact.mk hp
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_card_sub_one hpK
  have hAB : IsElemAbelian p AB := TableB.isElemAbelian_mono hA hle
  obtain ⟨A₀, φ', hφ's, hψφ', hdiag⟩ := exists_model' hp hpK hd hψ hker hperf hAB hAI
    ((Nat.pow_le_pow_right hp.pos hrd).trans hr) h3
  have hφker : ∀ g, φ' g = 1 → g ∈ scalars d K := by
    intro g hg
    have h1 : proj d K (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ g) = 1 := by
      rw [← hψφ', hg, map_one]
    exact mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp h1)
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  set U₀ := (SpecialLinearGroup.transvectionHom h01 : Multiplicative K →* _).range with hU₀
  set U' : Subgroup L' := U₀.map φ' with hU'
  have hU'ne : U' ≠ ⊥ := by
    intro hbot
    have hmem : φ' (SpecialLinearGroup.transvection h01 1) ∈ U' :=
      ⟨_, ⟨Multiplicative.ofAdd 1, by
        rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (hφker _ hmem)
    have h4 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M ⟨0, by omega⟩ ⟨1, by omega⟩) hc
    simp [CFSG.LinearGroups.coe_transvection] at h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU'2 : IsPGroup 2 U' := by
    refine IsPGroup.map (fun x => ⟨1, ?_⟩) φ'
    obtain ⟨y, c, hc⟩ := x
    have h2 : y ^ 2 = 1 := by
      rw [← hc, SpecialLinearGroup.transvectionHom_apply,
        CFSG.RankThree.CALinearPlane.transvection_pow, Nat.cast_ofNat, CharTwo.two_eq_zero,
        zero_mul]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero h01
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact h2
  have hU₀diag : ∀ (E : GL (Fin d) K) (t : Fin d → K),
      (E : Matrix (Fin d) (Fin d) K) = diagonal t → ∀ s ∈ U₀,
        φ' (CatalogueBHigherLinearAction.slConjugation d K E s) ∈ U' := by
    rintro E t hE _ ⟨c, rfl⟩
    refine ⟨_, ⟨Multiplicative.ofAdd (t ⟨0, by omega⟩ * Multiplicative.toAdd c *
      (t ⟨1, by omega⟩)⁻¹), rfl⟩, ?_⟩
    simp only [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]
    rw [slConjugation_transvection_of_diagonal hE h01]
  have hU'A : ∀ a ∈ AB, ∀ u ∈ U', a u ∈ U' := by
    rintro a ha _ ⟨s, hs, rfl⟩
    obtain ⟨t, E, hE, haE⟩ := hdiag a ha
    rw [haE]
    exact hU₀diag E t hE s hs
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hheart : ∀ (i j : Fin d) (hij : i ≠ j),
      MulAut.conj (φ' (diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij))) ∈ AB := by
    intro i j hij
    set D := diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij) with hD
    refine hmax (φ' D) ?_ (fun a ha => ?_) U' hU'ne hU'2 hU'A (fun u hu => ?_)
    · rw [← map_pow, pow_eq_one_of_diagonal (coe_diagSLOf _ _) (rootT_pow hζ.pow_eq_one i j),
        map_one]
    · obtain ⟨t, hat⟩ := hdiag a ha
      exact hat.apply_of_isDiag (by rw [coe_diagSLOf]; exact isDiag_diagonal _)
    · obtain ⟨s, hs, rfl⟩ := hu
      have e : φ' D * φ' s * (φ' D)⁻¹ = φ' (CatalogueBHigherLinearAction.slConjugation d K
          (SpecialLinearGroup.toGL D) s) := by
        rw [slConjugation_toGL_eq, map_mul, map_mul, map_inv]
      rw [e]
      exact hU₀diag (SpecialLinearGroup.toGL D) (rootT ζ i j)
        (by rw [SpecialLinearGroup.coe_GL_coe_matrix, hD, coe_diagSLOf]) s hs
  obtain ⟨hUne, hU2⟩ := unitriangular_conj_two (K := K) (by omega) A₀
  refine ⟨_, hUne, hU2, fun a ha φ hφa => ?_⟩
  have hap : a ^ p = 1 := hA.2 a ha
  have hφp : φ ^ p = 1 := by
    refine induced_unique ψ hψ (a := 1) (fun l => ?_) (fun l => rfl)
    rw [induced_pow ψ hφa p l, hap]
  have hodd : Odd (orderOf φ) := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hφp) with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  refine mapsTo_unitriangular_conj_of_comm hp hp2 hd hζ A₀ hodd (fun i j hij => ?_)
  set D := diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij) with hD
  have he := hheart i j hij
  have hcomm : a * MulAut.conj (φ' D) = MulAut.conj (φ' D) * a :=
    TableB.IsElemAbelian.comm hA ha (hle he)
  have hind : ∀ l, conjAut d K (A₀⁻¹ * rootGL hζ0 hij * A₀) (ψ l) =
      ψ (MulAut.conj (φ' D) l) := by
    intro l
    have e1 : A₀⁻¹ * rootGL hζ0 hij * A₀ = SpecialLinearGroup.toGL
        (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ D) := by
      rw [toGL_slConjugation, inv_inv]
      rfl
    rw [e1, ← conj_proj_eq_conjAut, ← hψφ', MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv]
  ext r
  obtain ⟨l, rfl⟩ := hψ r
  rw [MulAut.mul_apply, MulAut.mul_apply, hind, hφa, hφa, hind, ← MulAut.mul_apply,
    ← MulAut.mul_apply, hcomm]

end CFSG.StandardType.LinUnitL

end
