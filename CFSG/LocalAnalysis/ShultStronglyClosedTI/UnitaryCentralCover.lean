module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverMixedInvariance
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.StronglyEmbedded.BenderUnitaryCenter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.Open
open scoped Matrix

universe u v

theorem unitaryCover_hyperbolic_kernel_eq_bot
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {E : Type v} [Group E] [Finite E] [Group.IsPerfect E]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (η : E →* ProjectiveSpecialUnitaryMatrixGroup J) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective Subtype.val Subtype.coe_injective
  let Q : Sylow 2 G := unitaryCoverSylow J f hf hcard hfixed hJ
  let : IsElementaryAbelian 2 (commutator (Q : Subgroup G)) :=
    (unitaryCoverRoot_layers_elementary J (2 ^ f) hcard hfixed hJ).1
  let : IsElementaryAbelian 2 (Abelianization (Q : Subgroup G)) :=
    (unitaryCoverRoot_layers_elementary J (2 ^ f) hcard hfixed hJ).2
  have hclass : commutator (Q : Subgroup G) ≤ Subgroup.center (Q : Subgroup G) := by
    change commutator (unitaryCoverRoot J hJ) ≤ Subgroup.center (unitaryCoverRoot J hJ)
    exact (unitaryCoverRoot_nativeStructure J (2 ^ f) hcard hfixed hJ).2.1.le
  exact central_two_cover_bilinear_Sylow_obstruction η hsurj hcentral hp Q hclass
    (unitaryCoverTorus J hJ) (unitaryCoverTorus_le_normalizer J hJ)
    (unitaryCoverTorus_card_odd J f hf hcard hfixed hJ)
    (unitaryCoverMixedInvariant_eq_zero J f hf hcard hfixed hJ)
    (unitaryCoverAbelianInvariant_eq_zero J f hf hcard hfixed hJ)

@[expose] def unitaryCoverCanonicalEquiv (f : ℕ) (hf : 2 ≤ f) :
    ProjectiveSpecialUnitaryMatrixGroup (binaryQuadraticHermitian f (by omega)) ≃* PSU3 2 f := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  let e := (projectiveSpecialUnitary_equiv_PSU3Model J f hf rfl hcard hfixed).some
  exact e.trans (MulEquiv.subgroupCongr (show PSU3Model f = PSU3 2 f by rfl))

theorem unitaryCover_native_kernel_eq_bot
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (f : ℕ) (hf : 2 ≤ f) (η : E →* PSU3 2 f) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  let e := unitaryCoverCanonicalEquiv f hf
  let φ := e.symm.toMonoidHom.comp η
  have hker : φ.ker = η.ker :=
    MonoidHom.ker_comp_of_injective η e.symm.toMonoidHom e.symm.injective
  have hbot := unitaryCover_hyperbolic_kernel_eq_bot J f hf hcard hfixed rfl φ
    (e.symm.surjective.comp hsurj) (hker.symm ▸ hcentral) (hker.symm ▸ hp)
  exact hker.symm.trans hbot

theorem even_unitary_three_perfect_central_two_cover_trivial
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ (2 * f))
    (η : E →* GLAProj (GLASUGroup (Fin 3) K (2 ^ f))) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) :
    η.ker = ⊥ ∧ ∃ e : E ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ f)),
      ∀ x : E, e x = η x := by
  let eJ := glaSU3EquivNative f hf hcard
  let φ := eJ.toMonoidHom.comp η
  have hker : φ.ker = η.ker :=
    MonoidHom.ker_comp_of_injective η eJ.toMonoidHom eJ.injective
  have hbot : η.ker = ⊥ := by
    have h := unitaryCover_native_kernel_eq_bot f hf φ (eJ.surjective.comp hsurj)
      (hker.symm ▸ hcentral) (hker.symm ▸ hp)
    exact hker.symm.trans h
  exact ⟨hbot, MulEquiv.ofBijective η ⟨η.ker_eq_bot_iff.mp hbot, hsurj⟩, fun _ => rfl⟩

theorem unitaryCover_native_simple (f : ℕ) (hf : 2 ≤ f) : IsSimpleGroup (PSU3 2 f) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hq : 2 < 2 ^ f := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hf
    norm_num at h ⊢
    omega
  exact (unitaryCoverCanonicalEquiv f hf).isSimpleGroup_congr.mp
    (huppert_II_10_13 J (2 ^ f) hq hcard hfixed)

theorem unitaryCover_exact_simple {K : Type} [Field K] [Finite K]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ (2 * f)) :
    IsSimpleGroup (GLAProj (GLASUGroup (Fin 3) K (2 ^ f))) :=
  (glaSU3EquivNative f hf hcard).isSimpleGroup_congr.mpr (unitaryCover_native_simple f hf)

theorem unitaryCover_psu_admissible (f : ℕ) (hf : 2 ≤ f) :
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 2 f :=
  CFSG.RankTwoShapes.statedLieAdmissible_PSU_three_two f hf

theorem unitaryCover_equiv_lieModel {K L : Type} [Field K] [Finite K] [Group L]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ (2 * f))
    (e : L ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ f))) :
    CFSG.Blueprint.LieModel L .PSU 3 2 f := by
  let eC : GLAProj (GLASUGroup (Fin 3) K (2 ^ f)) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K) :=
    MulEquiv.refl _
  have hc : Nat.card K = (2 ^ f) ^ 2 := by
    simpa only [← pow_mul, Nat.mul_comm] using hcard
  have hclass : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSU 3 2 f :=
    ⟨unitaryCover_psu_admissible f hf, K, inferInstance, inferInstance, hc, ⟨e.trans eC⟩⟩
  exact Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hclass⟩

theorem unitaryCover_native_center_quotient_full
    {L : Type u} [Group L] [Finite L] [Group.IsPerfect L]
    (f : ℕ) (hf : 2 ≤ f) (hp : IsPGroup 2 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* PSU3 2 f) :
    Subgroup.center L = ⊥ ∧ IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      Nonempty (L ≃* PSU3 2 f) ∧ fusionIsBenderGroup L := by
  let η := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hsurj : Function.Surjective η :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hbot := unitaryCover_native_kernel_eq_bot f hf η hsurj
    (hker.symm ▸ le_refl (Subgroup.center L)) (hker.symm ▸ hp)
  let eL : L ≃* PSU3 2 f := MulEquiv.ofBijective η ⟨η.ker_eq_bot_iff.mp hbot, hsurj⟩
  have hsimple : IsSimpleGroup L :=
    eL.isSimpleGroup_congr.mpr (unitaryCover_native_simple f hf)
  let : IsSimpleGroup L := hsimple
  exact ⟨hker.symm.trans hbot, hsimple, Group.IsPerfect.not_isMulCommutative L,
    ⟨eL⟩, Or.inr (Or.inl ⟨f, hf, ⟨eL⟩⟩)⟩

theorem even_unitary_three_perfect_center_quotient_full
    {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Group L] [Finite L] [Group.IsPerfect L]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ (2 * f))
    (hp : IsPGroup 2 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ f))) :
    Subgroup.center L = ⊥ ∧ IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      Nonempty (L ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ f))) ∧
      CFSG.Blueprint.LieModel L .PSU 3 2 f ∧ ExplicitUnitaryModel L ∧
      ExplicitRankOneModel L ∧ fusionIsBenderGroup L := by
  let η := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hsurj : Function.Surjective η :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  obtain ⟨hbot, eL, _heL⟩ := even_unitary_three_perfect_central_two_cover_trivial
    f hf hcard η hsurj (hker.symm ▸ le_refl (Subgroup.center L)) (hker.symm ▸ hp)
  have hsimple : IsSimpleGroup L :=
    eL.isSimpleGroup_congr.mpr (unitaryCover_exact_simple f hf hcard)
  let : IsSimpleGroup L := hsimple
  have hunitary : ExplicitUnitaryModel L :=
    ⟨f, hf, K, inferInstance, inferInstance, hcard, ⟨eL⟩⟩
  have hrank : ExplicitRankOneModel L := Or.inr (Or.inl hunitary)
  exact ⟨hker.symm.trans hbot, hsimple, Group.IsPerfect.not_isMulCommutative L,
    ⟨eL⟩, unitaryCover_equiv_lieModel f hf hcard eL, hunitary, hrank,
      (explicitRankOneModel_iff_fusionIsBenderGroup L).mp hrank⟩

end CFSG.ShultStronglyClosedTI
