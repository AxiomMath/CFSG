module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddSz
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeSeven
import CFSG.LinearAlgebra.TwoGroupNormalizerGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup

theorem commute_of_normalizes_two_of_finrank_le_four {F W : Type} [Field F] [Finite F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (hF : ringChar F ≠ 2)
    (hW : Module.finrank F W ≤ 4) {R : Subgroup (Module.End F W)ˣ} (hR : IsPGroup 2 R)
    {y : (Module.End F W)ˣ} {r : ℕ} (hr : r.Prime) (hr7 : r = 7 ∨ 17 ≤ r) (hy : y ^ r = 1)
    (hyR : y ∈ normalizer (R : Set (Module.End F W)ˣ)) : ∀ x ∈ R, y * x = x * y := by
  rcases hr7 with h7 | h17
  · subst h7
    exact CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree.commute_of_seven_normalizes_two
      hF hW hR ⟨1, by simpa using hy⟩ hyR
  · by_cases hd : 2 ≤ Module.finrank F W
    · intro x hx
      let e : (Module.End F W)ˣ ≃* GL (Fin (Module.finrank F W)) F :=
        Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis F W)).toMulEquiv
      have hP2 : IsPGroup 2 (R.map e.toMonoidHom) := hR.map e.toMonoidHom
      have hy2 : e y ^ r = 1 := by rw [← map_pow, hy, map_one]
      have hyP : e y ∈ normalizer
          (R.map e.toMonoidHom : Set (GL (Fin (Module.finrank F W)) F)) := by
        rw [Subgroup.mem_normalizer_iff']
        intro w
        rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
        simp only [map_mul, MulEquiv.symm_apply_apply]
        exact Subgroup.mem_normalizer_iff'.mp hyR (e.symm w)
      have hdr : Module.finrank F W * Module.finrank F W < r := by nlinarith
      have hcomm := CFSG.LinearAlgebra.TwoGroupNormalizerGL.commute_of_mem_normalizer_GL_of_sq_lt
        (Ring.two_ne_zero hF) hd hr hdr hP2 hyP (k := 1) (by simpa using hy2)
      have hx' : e x ∈ R.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      exact e.injective (by simpa using hcomm (e x) hx')
    · have hd1 : Module.finrank F W ≤ 1 := by omega
      have hsingle : ∀ i j : Fin (Module.finrank F W), i = j :=
        fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
      have hdiag : ∀ A : Matrix (Fin (Module.finrank F W)) (Fin (Module.finrank F W)) F,
          A = Matrix.diagonal (fun i => A i i) := by
        intro A
        ext i j
        have hij : i = j := hsingle i j
        subst hij
        rw [Matrix.diagonal_apply, if_pos rfl]
      have hmat : ∀ A B : Matrix (Fin (Module.finrank F W)) (Fin (Module.finrank F W)) F,
          A * B = B * A := by
        intro A B
        rw [hdiag A, hdiag B, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        congr 1
        ext i
        exact mul_comm _ _
      have hend : ∀ a b : Module.End F W, a * b = b * a := by
        intro a b
        let e := LinearMap.toMatrixAlgEquiv (Module.finBasis F W)
        refine e.injective ?_
        rw [map_mul, map_mul]
        exact hmat (e a) (e b)
      intro x hx
      exact Units.ext (hend y x)


theorem noSzOverTwo_of_finrank_le_four {X : Type} {F W : Type}
    [Group X] [Field F] [Finite F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (hF : ringChar F ≠ 2) (hW : Module.finrank F W ≤ 4) (ρ : X →* (Module.End F W)ˣ)
    (hρ : Function.Injective ρ) : NoSzOverTwo X := by
  refine noSzOverTwo_of_injective ρ hρ ?_
  intro H N hNnormal hN p f hSz
  obtain ⟨P, y, hP2, hPnab, hPnorm, hyprime, hy7, x, hxP, hxy⟩ :=
    exists_twoSubgroup_of_suzukiModel_quotient N hN hSz
  have hR2 : IsPGroup 2 (P.map H.subtype) := hP2.map H.subtype
  have hy_norm : H.subtype y ∈ normalizer (P.map H.subtype : Set (Module.End F W)ˣ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hw
      have hq' : y * q * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hPnorm q).mp hq
      refine Subgroup.mem_map.mpr ⟨y * q * y⁻¹, hq', ?_⟩
      simp
    · intro hw
      obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hw
      have hmem : y⁻¹ * q * y ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hPnorm) q).mp hq
      refine Subgroup.mem_map.mpr ⟨y⁻¹ * q * y, hmem, ?_⟩
      have hw' : w = (H.subtype y)⁻¹ * H.subtype q * (H.subtype y) := by
        rw [hqeq]
        group
      rw [hw']
      simp
  have hcomm := commute_of_normalizes_two_of_finrank_le_four hF hW hR2 hyprime hy7
    (by rw [← map_pow, pow_orderOf_eq_one, map_one]) hy_norm
  have hxmap : H.subtype x ∈ P.map H.subtype := Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  exact hxy (H.subtype_injective (by simpa using hcomm (H.subtype x) hxmap))


theorem noSzOverTwo_statedProj_statedSp {F : Type} [Field F]
    [Finite F] (hF : ringChar F ≠ 2) :
    NoSzOverTwo (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 F)) := by
  have hSp : NoSzOverTwo ↥(CFSG.Open.StatedSp 2 F) := by
    let ρ : ↥(CFSG.Open.StatedSp 2 F) →* (Module.End F (Fin 2 ⊕ Fin 2 → F))ˣ :=
      (Matrix.GeneralLinearGroup.toLin (n := Fin 2 ⊕ Fin 2) (R := F)).toMonoidHom.comp
        (CFSG.Open.StatedSp 2 F).subtype
    refine noSzOverTwo_of_finrank_le_four (W := Fin 2 ⊕ Fin 2 → F) hF ?_ ρ ?_
    · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
      norm_num
    · intro a b hab
      exact Subtype.ext
        ((Matrix.GeneralLinearGroup.toLin (n := Fin 2 ⊕ Fin 2) (R := F)).injective hab)
  have hK2 : IsPGroup 2 ((CFSG.Open.StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf
      (CFSG.Open.StatedSp 2 F)) := by
    have hexp : ∀ x : ↥((CFSG.Open.StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf
        (CFSG.Open.StatedSp 2 F)), x ^ 2 = 1 := by
      intro x
      obtain ⟨c, hc⟩ : ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c =
          (x.1.1 : GL (Fin 2 ⊕ Fin 2) F) := by
        simpa only [CFSG.Open.StatedScalars, MonoidHom.mem_range] using
          Subgroup.mem_subgroupOf.mp x.2
      have hcH : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈
          CFSG.Open.StatedSp 2 F := by
        rw [hc]
        exact x.1.2
      have hc2 : c ^ 2 = 1 :=
        (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 2) (by norm_num) c).mp hcH
      apply Subtype.ext
      apply Subtype.ext
      show ((x.1.1 : GL (Fin 2 ⊕ Fin 2) F)) ^ 2 = 1
      rw [← hc, ← map_pow, hc2, map_one]
    intro g
    exact ⟨1, by simpa using hexp g⟩
  exact noSzOverTwo_of_surjective
    (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf
      (CFSG.Open.StatedSp 2 F)))
    (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk']) hSp


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
