module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Open.StatedDefs
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal CFSG.Open QuadraticMap

section PairInvariance

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_perp_polar_ne_zero_of_pair {e f : V} (hQe : Q e = 0) (hQf : Q f = 0)
    (hef : polar Q e f = 1) (hQ : (polarBilin Q).Nondegenerate) {a : V} (ha0 : a ≠ 0)
    (hae : polar Q e a = 0) (haf : polar Q f a = 0) :
    ∃ w : V, polar Q e w = 0 ∧ polar Q f w = 0 ∧ polar Q a w ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ ha0
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  have hea : polar Q a e = 0 := by rw [polar_comm]; exact hae
  have hfa : polar Q a f = 0 := by rw [polar_comm]; exact haf
  refine ⟨y - polar Q y f • e - polar Q y e • f, ?_, ?_, ?_⟩
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_eq_zero hQe, hef, polar_comm Q e y]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hfe,
      polar_self_eq_zero hQf, polar_comm Q f y]
    ring
  · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hea, hfa]
    simpa using hy

theorem mem_left_of_polar_ne_zero {e f : V} (hQe : Q e = 0) (hQf : Q f = 0)
    (hef : polar Q e f = 1) (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V}
    (hW : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W) {a : V} (ha0 : a ≠ 0)
    (hae : polar Q e a = 0) (haf : polar Q f a = 0) {x : V} (hx : x ∈ W)
    (hxe : polar Q x e ≠ 0) : e ∈ W := by
  obtain ⟨w, hwe, -, haw⟩ := exists_perp_polar_ne_zero_of_pair hQe hQf hef hQ ha0 hae haf
  have hg : ∀ w' : V, polar Q e w' = 0 →
      polar Q x e • w' - (polar Q x w' + Q w' * polar Q x e) • e ∈ W := by
    intro w' hw'
    have h1 : eichler Q e w' x - x ∈ W := W.sub_mem (hW e w' x hx) hx
    have h2 : eichler Q e w' x - x =
        polar Q x e • w' - (polar Q x w' + Q w' * polar Q x e) • e := by
      rw [eichler_apply hQe hw']
      abel
    rw [← h2]
    exact h1
  have hkey : (polar Q a w * polar Q x e) • e =
      (polar Q x e • a - (polar Q x a + Q a * polar Q x e) • e) +
        (polar Q x e • w - (polar Q x w + Q w * polar Q x e) • e) -
        (polar Q x e • (a + w) - (polar Q x (a + w) + Q (a + w) * polar Q x e) • e) := by
    rw [polar_add_right, QuadraticMap.map_add Q a w]
    module
  have hmem : (polar Q a w * polar Q x e) • e ∈ W := by
    rw [hkey]
    refine W.sub_mem (W.add_mem (hg a hae) (hg w hwe)) (hg (a + w) ?_)
    rw [polar_add_right, hae, hwe, add_zero]
  have h3 := W.smul_mem (polar Q a w * polar Q x e)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero haw hxe), one_smul] at h3

theorem mem_or_mem_of_mem_ne_zero {e f : V} (hQe : Q e = 0) (hQf : Q f = 0)
    (hef : polar Q e f = 1) (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V}
    (hW : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W) {a : V} (ha0 : a ≠ 0)
    (hae : polar Q e a = 0) (haf : polar Q f a = 0) {x : V} (hx : x ∈ W) (hx0 : x ≠ 0) :
    e ∈ W ∨ f ∈ W := by
  by_cases hxe : polar Q x e = 0
  · by_cases hxf : polar Q x f = 0
    · have hxe' : polar Q e x = 0 := by rw [polar_comm]; exact hxe
      have hxf' : polar Q f x = 0 := by rw [polar_comm]; exact hxf
      obtain ⟨w, hwe, -, hxw⟩ := exists_perp_polar_ne_zero_of_pair hQe hQf hef hQ hx0 hxe' hxf'
      have h1 : eichler Q e w x - x ∈ W := W.sub_mem (hW e w x hx) hx
      have h2 : eichler Q e w x - x = (-polar Q x w) • e := by
        rw [eichler_apply hQe hwe, hxe]
        module
      rw [h2] at h1
      have h3 := W.smul_mem (-polar Q x w)⁻¹ h1
      rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hxw), one_smul] at h3
      exact Or.inl h3
    · exact Or.inr (mem_left_of_polar_ne_zero hQf hQe (by rw [polar_comm]; exact hef) hQ hW
        ha0 haf hae hx hxf)
  · exact Or.inl (mem_left_of_polar_ne_zero hQe hQf hef hQ hW ha0 hae haf hx hxe)

theorem mem_perp_of_mem_left {e f : V} (hQe : Q e = 0) (hQf : Q f = 0)
    (hef : polar Q e f = 1) {W : Submodule K V}
    (hW : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W) {w1 w2 : V}
    (h1e : polar Q e w1 = 0) (h1f : polar Q f w1 = 0) (h2e : polar Q e w2 = 0)
    (h2f : polar Q f w2 = 0) (h12 : polar Q w1 w2 ≠ 0) (he : e ∈ W) :
    f ∈ W ∧ ∀ w : V, polar Q e w = 0 → polar Q f w = 0 → w ∈ W := by
  have hz : ∀ w : V, polar Q e w = 0 → polar Q f w = 0 → w - Q w • f ∈ W := by
    intro w hwe hwf
    have h1 : eichler Q f w e - e ∈ W := W.sub_mem (hW f w e he) he
    have h2 : eichler Q f w e - e = w - Q w • f := by
      rw [eichler_apply hQf hwf, hef, hwe]
      module
    rw [← h2]
    exact h1
  have hsc : polar Q w1 w2 • f ∈ W := by
    have e1 := hz w1 h1e h1f
    have e2 := hz w2 h2e h2f
    have e12 := hz (w1 + w2) (by rw [polar_add_right, h1e, h2e, add_zero])
      (by rw [polar_add_right, h1f, h2f, add_zero])
    have h4 : polar Q w1 w2 • f =
        (w1 - Q w1 • f) + (w2 - Q w2 • f) - (w1 + w2 - Q (w1 + w2) • f) := by
      rw [QuadraticMap.map_add Q w1 w2]
      module
    rw [h4]
    exact W.sub_mem (W.add_mem e1 e2) e12
  have hf : f ∈ W := by
    have h3 := W.smul_mem (polar Q w1 w2)⁻¹ hsc
    rwa [smul_smul, inv_mul_cancel₀ h12, one_smul] at h3
  refine ⟨hf, fun w hwe hwf => ?_⟩
  have h5 := W.add_mem (hz w hwe hwf) (W.smul_mem (Q w) hf)
  rwa [sub_add_cancel] at h5

theorem eq_top_of_mem_pair {e f : V} (hQe : Q e = 0) (hQf : Q f = 0) (hef : polar Q e f = 1)
    {W : Submodule K V} (he : e ∈ W) (hf : f ∈ W)
    (hperp : ∀ w : V, polar Q e w = 0 → polar Q f w = 0 → w ∈ W) : W = ⊤ := by
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  rw [eq_top_iff]
  intro v _
  have hp : v - polar Q v f • e - polar Q v e • f ∈ W := by
    refine hperp _ ?_ ?_
    · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_self_eq_zero hQe, hef, polar_comm Q e v]
      ring
    · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hfe,
        polar_self_eq_zero hQf, polar_comm Q f v]
      ring
  have h6 := W.add_mem (W.add_mem (W.smul_mem (polar Q v f) he)
    (W.smul_mem (polar Q v e) hf)) hp
  have h7 : polar Q v f • e + polar Q v e • f + (v - polar Q v f • e - polar Q v e • f) = v := by
    abel
  rwa [h7] at h6

theorem submodule_eq_bot_or_top_of_eichler_invariant {e f : V} (hQe : Q e = 0) (hQf : Q f = 0)
    (hef : polar Q e f = 1) (hQ : (polarBilin Q).Nondegenerate) {a : V} (ha0 : a ≠ 0)
    (hae : polar Q e a = 0) (haf : polar Q f a = 0) {W : Submodule K V}
    (hW : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨w, hwe, hwf, haw⟩ := exists_perp_polar_ne_zero_of_pair hQe hQf hef hQ ha0 hae haf
  rcases mem_or_mem_of_mem_ne_zero hQe hQf hef hQ hW ha0 hae haf hx hx0 with he | hf
  · obtain ⟨hf, hperp⟩ := mem_perp_of_mem_left hQe hQf hef hW hae haf hwe hwf haw he
    exact eq_top_of_mem_pair hQe hQf hef he hf hperp
  · obtain ⟨he, hperp⟩ := mem_perp_of_mem_left hQf hQe
      (by rw [polar_comm]; exact hef) hW haf hae hwf hwe haw hf
    exact eq_top_of_mem_pair hQe hQf hef he hf (fun w' h1 h2 => hperp w' h2 h1)

end PairInvariance

theorem natIrred_statedOmegaMinus_two {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    NatIrred (StatedOmega (StatedQuadMinus 2 K b c)) := by
  intro S hS
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  let i0 : Fin (2 - 1) := ⟨0, by norm_num⟩
  let a : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1
  have ha0 : a ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inr (Sum.inr 0))
    simp [a] at h1
  have hae : polar (CFSG.LieType.Universal.Spin.quadMinus 2 K b c)
      (minusPair K b c i0).e a = 0 := by
    rw [minusPair_e, polar_single_inl_quadMinus]
    simp [a, Pi.single_apply]
  have haf : polar (CFSG.LieType.Universal.Spin.quadMinus 2 K b c)
      (minusPair K b c i0).f a = 0 := by
    rw [minusPair_f, polar_single_inr_quadMinus]
    simp [a, Pi.single_apply]
  have hW : ∀ u w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, ∀ x ∈ S,
      eichler (CFSG.LieType.Universal.Spin.quadMinus 2 K b c) u w x ∈ S := by
    intro u w x hx
    let g : Gom (CFSG.LieType.Universal.Spin.quadMinus 2 K b c) :=
      ⟨eichler (CFSG.LieType.Universal.Spin.quadMinus 2 K b c) u w,
        eichler_mem_elementaryGroup (CFSG.LieType.Universal.Spin.quadMinus 2 K b c) u w⟩
    let E := ElemMatrixIso.minus (K := K) (m := 2) (b := b) (c := c) le_rfl hirr
    have hA := hS (E.equiv.symm g).1 (E.equiv.symm g).2 x hx
    have happ := E.app (E.equiv.symm g) x
    rw [MulEquiv.apply_symm_apply] at happ
    rw [← happ] at hA
    exact hA
  exact submodule_eq_bot_or_top_of_eichler_invariant (minusPair K b c i0).Q_e
    (minusPair K b c i0).Q_f (minusPair K b c i0).polar_ef hQ ha0 hae haf hW

end CFSG.RankThree.GF2n.Stroth80
