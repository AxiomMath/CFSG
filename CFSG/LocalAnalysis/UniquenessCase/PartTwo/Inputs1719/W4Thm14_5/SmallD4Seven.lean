module

public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2Rep
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Rel
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

abbrev wLongA2 : WeylGroup TwistTag.D4.tag :=
  simple TwistTag.D4.tag 1 * simple TwistTag.D4.tag 3 * simple TwistTag.D4.tag 2 *
    simple TwistTag.D4.tag 3 * simple TwistTag.D4.tag 1

theorem wLongA2_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    wLongA2 • v = reflect TwistTag.D4.tag 1 (reflect TwistTag.D4.tag 3
      (reflect TwistTag.D4.tag 2 (reflect TwistTag.D4.tag 3 (reflect TwistTag.D4.tag 1 v)))) := by
  simp only [wLongA2, mul_smul, simple_smul]

theorem wLongA2_e0 : wLongA2 • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4P := by
  rw [wLongA2_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wLongA2_e2 : wLongA2 • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4C := by
  rw [wLongA2_smul]
  exact List.ofFn_injective (by decide +kernel)

@[expose] def sevenMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 0, 1; 1, 1, 1]

theorem sevenMat_eq : (1 + single 0 1 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (1 + single 1 2 1) *
    (1 + single 2 1 1) * (1 + single 1 0 1) = sevenMat := by
  decide

theorem sevenMat_pow_seven : sevenMat ^ 7 = 1 := by
  decide

section Field

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem map_one_add_single (φ : ZMod 2 →+* K) (p q : Fin 3) :
    φ.mapMatrix (1 + single p q 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + single p q 1 := by
  rw [map_add, map_one]
  congr 1
  ext a b
  simp [Matrix.single_apply]

theorem orderOf_sevenMat {g : SpecialLinearGroup (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = (ZMod.castHom (dvd_refl 2) K).mapMatrix sevenMat) :
    orderOf g = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hg' : g.1 = (ZMod.castHom (dvd_refl 2) K).mapMatrix sevenMat := hg
  refine orderOf_eq_prime (Subtype.ext ?_) fun h => ?_
  · change g.1 ^ 7 = 1
    rw [hg', ← map_pow, sevenMat_pow_seven, map_one]
  · have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K) 1 1) h
    simp only [hg, RingHom.mapMatrix_apply, Matrix.map_apply] at h'
    simp [sevenMat] at h'

end Field

section Seven

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem seven_dvd_orderOf_longA2 :
    7 ∣ orderOf (Xr d4P 1 * Xr d4C 1 * Xr (-d4C) 1 * Xr (-d4P) 1) := by
  have hx₀ : xUnit Tag.D4 K 0 1 ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
    Subgroup.subset_closure ⟨0, zero_mem_d4SuppA2, 1, Or.inl rfl⟩
  have hy₀ : yUnit Tag.D4 K 0 1 ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
    Subgroup.subset_closure ⟨0, zero_mem_d4SuppA2, 1, Or.inr rfl⟩
  have hx₂ : xUnit Tag.D4 K 2 1 ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
    Subgroup.subset_closure ⟨2, two_mem_d4SuppA2, 1, Or.inl rfl⟩
  have hy₂ : yUnit Tag.D4 K 2 1 ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
    Subgroup.subset_closure ⟨2, two_mem_d4SuppA2, 1, Or.inr rfl⟩
  have hmem : xUnit Tag.D4 K 0 1 * xUnit Tag.D4 K 2 1 * yUnit Tag.D4 K 2 1 * yUnit Tag.D4 K 0 1 ∈
      subsystemGroup Tag.D4 K d4SuppA2 :=
    mul_mem (mul_mem (mul_mem hx₀ hx₂) hy₂) hy₀
  have hmat : ((d4A2Rep K ⟨_, hmem⟩ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (ZMod.castHom (dvd_refl 2) K).mapMatrix sevenMat := by
    rw [coe_d4A2Rep]
    change d4A2Mat (xUnit Tag.D4 K 0 1 * xUnit Tag.D4 K 2 1 * yUnit Tag.D4 K 2 1 *
      yUnit Tag.D4 K 0 1) = _
    rw [d4A2Mat_mul hy₀, d4A2Mat_mul hy₂, d4A2Mat_mul hx₂, d4A2Mat_x0, d4A2Mat_x2, d4A2Mat_y2,
      d4A2Mat_y0, ← sevenMat_eq, map_mul, map_mul, map_mul, map_one_add_single,
      map_one_add_single, map_one_add_single, map_one_add_single]
  have h7 := orderOf_map_dvd (d4A2Rep K) ⟨_, hmem⟩
  rw [orderOf_sevenMat hmat, Subgroup.orderOf_mk] at h7
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K wLongA2 with hn
  have hconj : ∀ (α : Fin TwistTag.D4.tag.rank → ℤ), IsRoot TwistTag.D4.tag α →
      n * Xr α 1 * n⁻¹ = Xr (wLongA2 • α) 1 := fun α hα =>
    canonicalRep_conj_charTwo' wLongA2 hα 1
  have h0 : n * xUnit TwistTag.D4.tag K 0 1 * n⁻¹ = Xr d4P 1 := by
    have h := hconj _ (isRoot_single TwistTag.D4.tag 0)
    rwa [wLongA2_e0, pinnedX_single] at h
  have h2 : n * xUnit TwistTag.D4.tag K 2 1 * n⁻¹ = Xr d4C 1 := by
    have h := hconj _ (isRoot_single TwistTag.D4.tag 2)
    rwa [wLongA2_e2, pinnedX_single] at h
  have h2' : n * yUnit TwistTag.D4.tag K 2 1 * n⁻¹ = Xr (-d4C) 1 := by
    have h := hconj _ (isRoot_neg_single TwistTag.D4.tag 2)
    rwa [smul_neg, wLongA2_e2, pinnedX_neg_single] at h
  have h0' : n * yUnit TwistTag.D4.tag K 0 1 * n⁻¹ = Xr (-d4P) 1 := by
    have h := hconj _ (isRoot_neg_single TwistTag.D4.tag 0)
    rwa [smul_neg, wLongA2_e0, pinnedX_neg_single] at h
  have e : Xr d4P 1 * Xr d4C 1 * Xr (-d4C) 1 * Xr (-d4P) 1 =
      n * (xUnit TwistTag.D4.tag K 0 1 * xUnit TwistTag.D4.tag K 2 1 *
        yUnit TwistTag.D4.tag K 2 1 * yUnit TwistTag.D4.tag K 0 1) * n⁻¹ := by
    rw [← h0, ← h2, ← h2', ← h0']
    group
  rw [e, ← SemiconjBy.orderOf_eq n (SemiconjBy.conj_mk n _)]
  exact h7

end Seven

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
