module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFaithful
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section WeylDiag

open TableBExc.E6Three

variable {K : Type} [Field K]

theorem hatAut_rootDiagUnit_eq_rootDiagAutHom_e6 {a : Fin Tag.E6.rank → Kˣ} :
    hatAut .E6 K ⟨rootDiagUnit .E6 a, rootDiagUnit_mem_hatGroup a⟩ =
      rootDiagAutHom .E6 K a := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [coe_hatAut_apply]
  exact (coe_rootDiagAut a g).symm

theorem rootDiagAutHom_zetaVec_eq_diag3 {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) :
    rootDiagAutHom .E6 K (zetaVec ζ hζ x) = diag3 ζ hζ (Multiplicative.ofAdd x) :=
  rfl

theorem exists_weyl_conj_diag3 {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {W : Set (Fin Tag.E6.rank → ZMod 3)} {h : MulAut (adjointGroup .E6 K)}
    (hh : h ∈ (hatAut .E6 K).range)
    (hW : ∀ x ∈ W, ∃ y ∈ W, h * diag3 ζ hζ (Multiplicative.ofAdd x) * h⁻¹ =
      diag3 ζ hζ (Multiplicative.ofAdd y)) :
    ∃ w : WeylGroup .E6, ∀ x ∈ W, h * diag3 ζ hζ (Multiplicative.ofAdd x) * h⁻¹ =
      diag3 ζ hζ (Multiplicative.ofAdd (adAct .E6 3 w x)) := by
  obtain ⟨ĝ, hĝ⟩ := hh
  obtain ⟨c, hc, a, hca⟩ := ĝ.2
  have hcH : c ∈ hatGroup .E6 K := adjointGroup_le_hatGroup hc
  have hmem : ∀ b : Fin Tag.E6.rank → Kˣ,
      c * rootDiagUnit .E6 b * c⁻¹ ∈ hatGroup .E6 K := by
    intro b
    exact mul_mem (mul_mem hcH (rootDiagUnit_mem_hatGroup b)) (inv_mem hcH)
  have hconj : ∀ b : Fin Tag.E6.rank → Kˣ,
      (↑(ĝ * (⟨rootDiagUnit .E6 b, rootDiagUnit_mem_hatGroup b⟩ : hatGroup .E6 K) * ĝ⁻¹) :
        ModGL .E6 K) = c * rootDiagUnit .E6 b * c⁻¹ := by
    intro b
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hca, mul_inv_rev]
    have hcomm : rootDiagUnit .E6 a * rootDiagUnit .E6 b =
        rootDiagUnit .E6 b * rootDiagUnit .E6 a := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hc1 : rootDiagUnit .E6 a * rootDiagUnit .E6 b * (rootDiagUnit .E6 a)⁻¹ =
        rootDiagUnit .E6 b := by
      rw [hcomm]; group
    rw [show (c * rootDiagUnit .E6 a) * rootDiagUnit .E6 b * ((rootDiagUnit .E6 a)⁻¹ * c⁻¹)
        = c * (rootDiagUnit .E6 a * rootDiagUnit .E6 b * (rootDiagUnit .E6 a)⁻¹) * c⁻¹
        from by group, hc1]
  let V : Set (ModGL .E6 K) := {d | ∃ x ∈ W, d = rootDiagUnit .E6 (zetaVec ζ hζ x)}
  have hVD : ∀ x ∈ V, ∃ b : Fin Tag.E6.rank → Kˣ, x = rootDiagUnit .E6 b := by
    rintro d ⟨x, -, rfl⟩
    exact ⟨zetaVec ζ hζ x, rfl⟩
  have hgV : ∀ x ∈ V, c * x * c⁻¹ ∈ V := by
    rintro d ⟨y, hyW, rfl⟩
    obtain ⟨z, hzW, hz⟩ := hW y hyW
    refine ⟨z, hzW, ?_⟩
    have heq :
        (⟨c * rootDiagUnit .E6 (zetaVec ζ hζ y) * c⁻¹,
            hmem (zetaVec ζ hζ y)⟩ : hatGroup .E6 K) =
          ⟨rootDiagUnit .E6 (zetaVec ζ hζ z), rootDiagUnit_mem_hatGroup _⟩ := by
      apply hatAut_injective
      have hL : hatAut .E6 K
            (⟨c * rootDiagUnit .E6 (zetaVec ζ hζ y) * c⁻¹,
              hmem (zetaVec ζ hζ y)⟩ : hatGroup .E6 K) =
          hatAut .E6 K (ĝ * (⟨rootDiagUnit .E6 (zetaVec ζ hζ y),
              rootDiagUnit_mem_hatGroup _⟩ : hatGroup .E6 K) * ĝ⁻¹) := by
        congr 1
        apply Subtype.ext
        exact (hconj (zetaVec ζ hζ y)).symm
      rw [hL, map_mul, map_mul, map_inv, hĝ,
        hatAut_rootDiagUnit_eq_rootDiagAutHom_e6 (a := zetaVec ζ hζ y),
        rootDiagAutHom_zetaVec_eq_diag3 (ζ := ζ) (hζ := hζ) y, hz,
        ← rootDiagAutHom_zetaVec_eq_diag3 (ζ := ζ) (hζ := hζ) z,
        ← hatAut_rootDiagUnit_eq_rootDiagAutHom_e6 (a := zetaVec ζ hζ z)]
    exact Subtype.ext_iff.mp heq
  obtain ⟨w, hw⟩ := exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag (τ := .E6) (k := K)
    hVD hc hgV
  refine ⟨w, ?_⟩
  intro x hx
  have hmemV : rootDiagUnit .E6 (zetaVec ζ hζ x) ∈ V := ⟨x, hx, rfl⟩
  have hcxd : c * rootDiagUnit .E6 (zetaVec ζ hζ x) * c⁻¹ =
      rootDiagUnit .E6 (zetaVec ζ hζ (adAct .E6 3 w x)) := by
    rw [hw _ hmemV, ← weylTuple_zetaVec (ζ := ζ) (hζ := hζ) (w := w) (x := x)]
    exact canonicalRep_conj_rootDiagUnit (K := K) w (zetaVec ζ hζ x)
  calc
    h * diag3 ζ hζ (Multiplicative.ofAdd x) * h⁻¹
        = hatAut .E6 K ĝ *
            hatAut .E6 K (⟨rootDiagUnit .E6 (zetaVec ζ hζ x),
              rootDiagUnit_mem_hatGroup _⟩ : hatGroup .E6 K) * (hatAut .E6 K ĝ)⁻¹ := by
            rw [← hĝ, ← rootDiagAutHom_zetaVec_eq_diag3 (ζ := ζ) (hζ := hζ) x,
              ← hatAut_rootDiagUnit_eq_rootDiagAutHom_e6 (a := zetaVec ζ hζ x)]
    _ = hatAut .E6 K (ĝ * (⟨rootDiagUnit .E6 (zetaVec ζ hζ x),
            rootDiagUnit_mem_hatGroup _⟩ : hatGroup .E6 K) * ĝ⁻¹) := by
            rw [map_mul, map_mul, map_inv]
    _ = hatAut .E6 K (⟨rootDiagUnit .E6 (zetaVec ζ hζ (adAct .E6 3 w x)),
            rootDiagUnit_mem_hatGroup _⟩ : hatGroup .E6 K) := by
            congr 1
            apply Subtype.ext
            rw [hconj, hcxd]
    _ = diag3 ζ hζ (Multiplicative.ofAdd (adAct .E6 3 w x)) := by
            rw [hatAut_rootDiagUnit_eq_rootDiagAutHom_e6,
              rootDiagAutHom_zetaVec_eq_diag3 (ζ := ζ) (hζ := hζ) (adAct .E6 3 w x)]

end WeylDiag

end NoOffE6Three

end CFSG.StandardType
