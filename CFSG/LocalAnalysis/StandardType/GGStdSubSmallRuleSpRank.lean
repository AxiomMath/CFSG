module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRule
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TwoThree CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped Matrix

namespace SmallRule

section Form

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def spBilin (K : Type) [Field K] (m : ℕ) :
    LinearMap.BilinForm K (Fin m ⊕ Fin m → K) :=
  Matrix.toBilin' (gram K m)

theorem spBilin_apply (u v : Fin m ⊕ Fin m → K) : spBilin K m u v = form u v :=
  Matrix.toBilin'_apply' _ _ _

theorem spBilin_nondegenerate : (spBilin K m).Nondegenerate := by
  have hleft : ∀ x : Fin m ⊕ Fin m → K, (∀ y, spBilin K m x y = 0) → x = 0 := by
    intro x hx
    funext a
    have h1 := hx (Pi.single (par a) 1)
    rw [spBilin_apply, form_single_right, par_par] at h1
    exact (mul_eq_zero.mp h1).resolve_right (sgn_ne_zero _)
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  have h1 := hy x
  rw [spBilin_apply] at h1 ⊢
  rw [form_antisymm, h1, neg_zero]

theorem spBilin_isRefl : (spBilin K m).IsRefl := by
  intro x y h
  rw [spBilin_apply] at h ⊢
  rw [form_antisymm, h, neg_zero]

end Form

section Rep

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} [NeZero m]

@[expose] noncomputable def spRep :
    LargeEvenProj (LargeEvenSpGroup K m) →* (Module.End K (Fin m ⊕ Fin m → K))ˣ :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin m ⊕ Fin m) K ≃* _).toMonoidHom).comp
    ((LargeEvenSpGroup K m).subtype.comp (TableBSymp.spProjEquivSp (K := K) (m := m)).toMonoidHom)

theorem spRep_apply (r : LargeEvenProj (LargeEvenSpGroup K m)) (v : Fin m ⊕ Fin m → K) :
    (spRep r : Module.End K (Fin m ⊕ Fin m → K)) v =
      mat m K (TableBSymp.spProjEquivSp r) *ᵥ v := by
  simp [spRep, Matrix.GeneralLinearGroup.toLin_apply, mat]

theorem spRep_injective : Function.Injective (spRep (K := K) (m := m)) := by
  intro r s h
  have h1 : (LargeEvenSpGroup K m).subtype (TableBSymp.spProjEquivSp r) =
      (LargeEvenSpGroup K m).subtype (TableBSymp.spProjEquivSp s) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin m ⊕ Fin m) K ≃* _).injective h
  exact (TableBSymp.spProjEquivSp (K := K) (m := m)).injective
    (Subtype.ext h1)

theorem spRep_isometry (r : LargeEvenProj (LargeEvenSpGroup K m)) (v w : Fin m ⊕ Fin m → K) :
    spBilin K m ((spRep r : Module.End K (Fin m ⊕ Fin m → K)) v)
      ((spRep r : Module.End K (Fin m ⊕ Fin m → K)) w) = spBilin K m v w := by
  rw [spBilin_apply, spBilin_apply, spRep_apply, spRep_apply]
  exact form_mulVec _ _ _

theorem card_sq_le_sp_normalizes_two (hK : Nat.card K = 2)
    {A U : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian 3 A)
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    Nat.card A ^ 2 ≤ 3 ^ (2 * m - 1) := by
  have h := card_sq_le_of_normalizes_two hK spRep spRep_injective (spBilin K m)
    spBilin_nondegenerate spBilin_isRefl spRep_isometry hA hU1 hU2 hAU
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, ← two_mul] at h

theorem card_le_sp_normalizes_two (hK : Nat.card K = 2)
    {A U : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian 3 A)
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U) :
    Nat.card A ≤ 3 ^ (m - 1) := by
  have h := card_le_pow_half hA (card_sq_le_sp_normalizes_two hK hA hU1 hU2 hAU)
  have hm := Nat.pos_of_neZero m
  have e : (2 * m - 1) / 2 = m - 1 := by omega
  rwa [e] at h

theorem exists_isotropic_sp_finrank_le_two (hK : Nat.card K = 2)
    {A U : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian 3 A)
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    (hcard : 3 ^ (m - 1) ≤ Nat.card A) :
    ∃ T : Submodule K (Fin m ⊕ Fin m → K), T ≠ ⊥ ∧ Module.finrank K T ≤ 2 ∧
      (∀ u ∈ T, ∀ v ∈ T, form u v = 0) ∧
      ∀ a ∈ A, ∀ t ∈ T, (spRep a : Module.End K (Fin m ⊕ Fin m → K)) t ∈ T := by
  obtain ⟨T, hT0, hTiso, hTA, h⟩ := exists_isotropic_card_sq_le hK spRep spRep_injective
    (spBilin K m) spBilin_nondegenerate spBilin_isRefl spRep_isometry hA hU1 hU2 hAU
  refine ⟨T, hT0, ?_, fun u hu v hv => by rw [← spBilin_apply]; exact hTiso u hu v hv, hTA⟩
  have hdim : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, ← two_mul]
  rw [hdim] at h
  have hTle : Module.finrank K T ≤ 2 * m := hdim ▸ Submodule.finrank_le T
  have h2 : (3 ^ (m - 1)) ^ 2 ≤ Nat.card A ^ 2 := Nat.pow_le_pow_left hcard 2
  rw [← pow_mul] at h2
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (h2.trans h)
  have hm := Nat.pos_of_neZero m
  omega

end Rep

end SmallRule

section Three

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggStdSubTwoTorusNormSmallR_spTwo_three (hK : Nat.card K = 2) :
    GGStdSubTwoTorusNormSmallR 3 (3 - 1) (LargeEvenProj (LargeEvenSpGroup K 3))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 3)) (LargeEvenGSpSet K 3)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 hα _ _ _ _ _ _
  exfalso
  have hZ := TableBSymp.center_spProj_eq_bot (K := K) (m := 3)
  have hinj := mulAut_conj_injective hZ
  obtain ⟨U₀, hU₀1, hU₀2, hU₀A⟩ := hα
  set X := TypeA.inducedSub ψ A with hX
  have hXe : IsElemAbelian 3 X := TypeA.isElemAbelian_inducedSub hψ hA
  have hXc : Nat.card X = Nat.card A := TypeA.card_inducedSub hψ hker hperf (fun a ha => by
    obtain ⟨φ, -, h⟩ := hAI a ha
    exact ⟨φ, h⟩)
  have hXI : ∀ φ ∈ X, φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →* _) :=
    fun φ _ => mem_range_conj_sp hK (le_refl 3) φ
  set Ã : Subgroup (LargeEvenProj (LargeEvenSpGroup K 3)) :=
    X.comap (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →* _) with hÃ
  have hÃe : IsElemAbelian 3 Ã := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact IsElemAbelian.comm hXe a.2 b.2
    · rw [map_pow, map_one]
      exact hXe.2 _ hx
  have hÃc : Nat.card Ã = Nat.card A := by
    have hmap : Ã.map (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →* _) = X := by
      rw [hÃ, Subgroup.map_comap_eq, inf_eq_right.mpr]
      intro φ hφ
      exact hXI φ hφ
    rw [← hXc, Nat.card_congr (Ã.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hÃU : ∀ x ∈ Ã, ∀ u ∈ U₀, x * u * x⁻¹ ∈ U₀ := by
    intro x hx u hu
    obtain ⟨a', ha', hxa⟩ := hx
    obtain ⟨l, rfl⟩ := hψ u
    have h1 := hxa l
    rw [MulAut.conj_apply] at h1
    rw [h1]
    exact hU₀A a' ha' l hu
  have h := SmallRule.card_sq_le_sp_normalizes_two hK hÃe hU₀1 hU₀2 hÃU
  rw [hÃc] at h
  have h27 := Nat.pow_le_pow_left h3 2
  norm_num at h h27
  omega

end Three

end CFSG.StandardType
