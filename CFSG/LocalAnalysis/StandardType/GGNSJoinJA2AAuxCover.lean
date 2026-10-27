module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBlock
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}

@[expose] noncomputable def nsJA2Cover (hK : Nat.card K = (2 ^ f) ^ 2) (ψ : Su K 2 f n →* G) :
    ↥(unitarySU 2 f K n) →* G :=
  ψ.comp (suEquivUnitarySU K 2 f hK n).symm.toMonoidHom

theorem nsJA2Cover_range (hK : Nat.card K = (2 ^ f) ^ 2) (ψ : Su K 2 f n →* G) :
    (nsJA2Cover hK ψ).range = ψ.range := by
  rw [nsJA2Cover, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (suEquivUnitarySU K 2 f hK n).symm.surjective,
    Subgroup.map_top]

theorem nsJA2Cover_ker_le (hK : Nat.card K = (2 ^ f) ^ 2) {ψ : Su K 2 f n →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) :
    (nsJA2Cover hK ψ).ker ≤ Subgroup.center ↥(unitarySU 2 f K n) := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  have h1 : (suEquivUnitarySU K 2 f hK n).symm u ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simpa only [nsJA2Cover, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hu
  have h2 : (suEquivUnitarySU K 2 f hK n).symm u ∈ Subgroup.center (Su K 2 f n) := hker h1
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro v
  apply (suEquivUnitarySU K 2 f hK n).symm.injective
  rw [map_mul, map_mul]
  exact h2 _

theorem nsJA2Cover_mem_suPairs (hK : Nat.card K = (2 ^ f) ^ 2) {ψ : Su K 2 f n →* G} {e : G}
    {g : GL (Fin n) K} (hg : ggIsDiagMat g) (he : GGInducesUnitary (p := 2) (f := f) ψ e g) :
    ∃ δ : Fin n → Kˣ, (e, diagHom n δ) ∈ SUTorus.suPairs (nsJA2Cover hK ψ) := by
  obtain ⟨d, hd⟩ := hg
  have hdet : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    refine Matrix.det_ne_zero_of_right_inverse
      (B := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hd, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let δ : Fin n → Kˣ := fun i => Units.mk0 (d i) (hd0 i)
  have hδg : diagHom n δ = g := Units.ext (by
    rw [CFSG.SectionRank.OddCover.coe_diagHom, hd]
    rfl)
  have hnorm : g ∈ Subgroup.normalizer ((unitarySU 2 f K n : Set (GL (Fin n) K))) := by
    refine Subgroup.mem_normalizer_fintype (fun h hh => ?_)
    obtain ⟨y, hy, -⟩ := he.2 ((suEquivUnitarySU K 2 f hK n).symm ⟨h, hh⟩)
    rw [coe_suEquivUnitarySU_symm] at hy
    rw [← hy, ← coe_suEquivUnitarySU (p := 2) (f := f) hK y]
    exact (suEquivUnitarySU K 2 f hK n y).2
  have hcompat : ∀ u v : ↥(unitarySU 2 f K n), (v : GL (Fin n) K) = g * u * g⁻¹ →
      e * nsJA2Cover hK ψ u * e⁻¹ = nsJA2Cover hK ψ v := by
    intro u v hv
    obtain ⟨y, hy, hconj⟩ := he.2 ((suEquivUnitarySU K 2 f hK n).symm u)
    rw [coe_suEquivUnitarySU_symm] at hy
    have hyv : y = (suEquivUnitarySU K 2 f hK n).symm v := by
      apply Subtype.ext
      rw [hy, coe_suEquivUnitarySU_symm]
      exact hv.symm
    rw [hyv] at hconj
    simpa only [nsJA2Cover, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hconj
  refine ⟨δ, ?_⟩
  rw [hδg]
  exact SUTorus.mem_suPairs.mpr ⟨hnorm, hcompat⟩

theorem nsJA2Cover_map_pairBlock_le (hK : Nat.card K = (2 ^ f) ^ 2) (ψ : Su K 2 f n →* G)
    {a b : Fin n} {S : Finset (Fin n)} (ha : a ∈ S) (hb : b ∈ S) :
    (ggSuPairBlock K 2 f n a b).map ψ ≤
      (TableBUE.blockSU (K := K) (n := f) S).map (nsJA2Cover hK ψ) := by
  rintro _ ⟨A, hA, rfl⟩
  refine ⟨(suEquivUnitarySU K 2 f hK n) A, ?_, ?_⟩
  · change (suEquivUnitarySU K 2 f hK n) A ∈ TableBUE.blockSU S
    rw [TableBUE.mem_blockSU]
    intro i j hij
    rw [coe_suEquivUnitarySU]
    rcases hij with hiS | hjS
    · exact hA i j (Or.inl ⟨by rintro rfl; exact hiS ha, by rintro rfl; exact hiS hb⟩)
    · exact hA i j (Or.inr ⟨by rintro rfl; exact hjS ha, by rintro rfl; exact hjS hb⟩)
  · simp only [nsJA2Cover, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]

theorem nsJA2Cover_map_blockSU_le_pairBlock (hK : Nat.card K = (2 ^ f) ^ 2) (ψ : Su K 2 f n →* G)
    {a b : Fin n} {S : Finset (Fin n)} (hS : S ⊆ {a, b}) :
    (TableBUE.blockSU (K := K) (n := f) S).map (nsJA2Cover hK ψ) ≤
      (ggSuPairBlock K 2 f n a b).map ψ := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨(suEquivUnitarySU K 2 f hK n).symm u, ?_, ?_⟩
  · intro i j hij
    rw [coe_suEquivUnitarySU_symm]
    have hu' : u ∈ TableBUE.blockSU S := hu
    refine (TableBUE.mem_blockSU.mp hu') i j ?_
    rcases hij with ⟨hia, hib⟩ | ⟨hja, hjb⟩
    · exact Or.inl (by
        rintro hiS
        have hmem : i ∈ ({a, b} : Finset (Fin n)) := hS hiS
        simp [hia, hib] at hmem)
    · exact Or.inr (by
        rintro hjS
        have hmem : j ∈ ({a, b} : Finset (Fin n)) := hS hjS
        simp [hja, hjb] at hmem)
  · rfl

end CFSG.StandardType

end
