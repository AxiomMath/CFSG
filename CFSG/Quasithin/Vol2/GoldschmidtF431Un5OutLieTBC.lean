module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTBB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieTC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique

variable {K : Type} [Field K] {f : ℕ} (hK : UnitaryFieldData 2 f K)

abbrev un5tb_gm (g : hypSU hK 2 1) : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
  ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K)

theorem un5tb_gram_of_fixed (g : hypSU hK 2 1)
    (hf : ∀ a b, hK.bar (un5tb_gm hK g a b) = un5tb_gm hK g a b) :
    (un5tb_gm hK g)ᵀ * hypGram 2 1 K * un5tb_gm hK g = hypGram 2 1 K := by
  have h1 := (mem_gramSU.mp g.2).1
  have h2 : (un5tb_gm hK g).map hK.bar = un5tb_gm hK g := Matrix.ext hf
  rwa [h2] at h1

theorem un5tb_ext_F {A B : Matrix (Fin 4) (Fin 4) hK.fixedField}
    (e : A.map hK.fixedField.subtype = B.map hK.fixedField.subtype) : A = B :=
  Matrix.map_injective hK.fixedField.subtype_injective e

@[expose] def un5tb_phiFun (H : Subgroup (hypSU hK 2 1))
    (hfix : ∀ g ∈ H, ∀ a b, hK.bar (un5tb_gm hK g a b) = un5tb_gm hK g a b) (g : H) :
    Matrix (Fin 4) (Fin 4) hK.fixedField :=
  Matrix.of fun i j =>
    ⟨un5tb_gm hK g.1 (un5tb_emb i) (un5tb_emb j), hK.mem_fixedField.mpr (hfix g.1 g.2 _ _)⟩

theorem un5tb_phiFun_map (H : Subgroup (hypSU hK 2 1))
    (hfix : ∀ g ∈ H, ∀ a b, hK.bar (un5tb_gm hK g a b) = un5tb_gm hK g a b) (g : H) :
    (un5tb_phiFun hK H hfix g).map hK.fixedField.subtype = un5tb_blk (un5tb_gm hK g.1) :=
  rfl

variable {H : Subgroup (hypSU hK 2 1)}
  (hfix : ∀ g ∈ H, ∀ a b, hK.bar (un5tb_gm hK g a b) = un5tb_gm hK g a b)

theorem un5tb_phiFun_mul (g g' : H) :
    un5tb_phiFun hK H hfix (g * g') = un5tb_phiFun hK H hfix g * un5tb_phiFun hK H hfix g' := by
  have := hK.charP
  refine un5tb_ext_F hK ?_
  rw [Matrix.map_mul, un5tb_phiFun_map, un5tb_phiFun_map, un5tb_phiFun_map]
  have hJ := un5tb_gram_of_fixed hK g.1 (hfix g g.2)
  have hc : ∀ i, un5tb_gm hK g.1 (un5tb_emb i) un5tb_z = 0 := fun i => by
    rw [un5tb_col_z hJ, ite_eq_right (un5tb_emb_ne_z i)]
  exact un5tb_blk_mul hc

theorem un5tb_phiFun_one : un5tb_phiFun hK H hfix 1 = 1 := by
  refine un5tb_ext_F hK ?_
  rw [un5tb_phiFun_map, Matrix.map_one _ (map_zero _) (map_one _)]
  ext i j
  simp [un5tb_blk, un5tb_gm, Matrix.one_apply, un5tb_emb_injective.eq_iff]

@[expose] def un5tb_phi : H →* Matrix (Fin 4) (Fin 4) hK.fixedField where
  toFun := un5tb_phiFun hK H hfix
  map_one' := un5tb_phiFun_one hK hfix
  map_mul' := un5tb_phiFun_mul hK hfix

@[expose] def un5tb_psi : H →* GL (Fin 4) hK.fixedField := (un5tb_phi hK hfix).toHomUnits

theorem un5tb_psi_coe (g : H) :
    ((un5tb_psi hK hfix g : GL (Fin 4) hK.fixedField) : Matrix (Fin 4) (Fin 4) hK.fixedField) =
      un5tb_phiFun hK H hfix g :=
  rfl

theorem un5tb_psi_injective : Function.Injective (un5tb_psi hK hfix) := by
  have := hK.charP
  intro g g' e
  have e1 : un5tb_phiFun hK H hfix g = un5tb_phiFun hK H hfix g' := by
    rw [← un5tb_psi_coe, ← un5tb_psi_coe, e]
  have e2 : ∀ i j, un5tb_gm hK g.1 (un5tb_emb i) (un5tb_emb j) =
      un5tb_gm hK g'.1 (un5tb_emb i) (un5tb_emb j) := fun i j =>
    congrArg Subtype.val (congrFun (congrFun e1 i) j)
  have hJ := un5tb_gram_of_fixed hK g.1 (hfix g g.2)
  have hJ' := un5tb_gram_of_fixed hK g'.1 (hfix g' g'.2)
  refine Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun a b => ?_)))
  rcases un5tb_cases a with rfl | ⟨i, rfl⟩
  · exact (un5tb_row_z hJ b).trans (un5tb_row_z hJ' b).symm
  rcases un5tb_cases b with rfl | ⟨j, rfl⟩
  · exact (un5tb_col_z hJ _).trans (un5tb_col_z hJ' _).symm
  · exact e2 i j

theorem un5tb_psi_mem (g : H) : un5tb_psi hK hfix g ∈ miyamotoSp4 hK := by
  have := hK.charP
  change ((un5tb_psi hK hfix g : GL (Fin 4) hK.fixedField) :
      Matrix (Fin 4) (Fin 4) hK.fixedField)ᵀ * miyamotoJ4 hK.fixedField *
    (un5tb_psi hK hfix g : GL (Fin 4) hK.fixedField) = miyamotoJ4 hK.fixedField
  refine un5tb_ext_F hK ?_
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, miyamotoJ4_map_subtype hK,
    un5tb_psi_coe, un5tb_phiFun_map]
  exact un5tb_blk_gram (un5tb_gram_of_fixed hK g.1 (hfix g g.2))

include hK in
theorem un5tb_twoPart_Sp4 : twoPart (miyamotoSp4 hK) = (2 ^ f) ^ 4 := by
  have := hK.charP
  have hf := hK.one_le
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hodd := OL.tfc_not_dvd_mul (Dvd.dvd.pow h2 (by norm_num : 2 ≠ 0))
    (Dvd.dvd.pow h2 (by norm_num : 4 ≠ 0)) (by positivity) (by positivity)
  have e : Nat.card (miyamotoSp4 hK) =
      2 ^ (f * 4) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
    rw [OL.tfc_card_Sp4, pow_mul]
  rw [OL.tfc_twoPart_eq_of_card hodd e, pow_mul]

end CFSG.Quasithin.H13.F431.Un.OL5
