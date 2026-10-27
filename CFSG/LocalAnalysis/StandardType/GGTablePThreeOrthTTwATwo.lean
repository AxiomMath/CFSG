module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLift
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTBlock
import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTFix
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
import CFSG.LocalAnalysis.StandardType.GGFusionExceptionFull
import CFSG.LocalAnalysis.StandardType.GGFusionShadowComponents
import CFSG.Assembly.GL83StatedBridge
import CFSG.CharacterTheory.Burnside
import CFSG.GH74.GLS.Stage4.Q9.Rigidity
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

private theorem orthTTwATwo_k {R : Type} [Group R] [IsSimpleGroup R]
    (hnab : ∃ a b : R, a * b ≠ b * a) {k : ℕ}
    (hlab : GGHasLabel ⟨.twA, 2, k⟩ R) : 2 ≤ k := by
  by_contra hk
  simp only [not_le] at hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  change LargeEvenRecipeUnitary 3 (2 ^ k) (fun R' _ _ _ => Nonempty (R ≃* R')) at hlab
  rcases hk01 with rfl | rfl
  · obtain ⟨K, hF, hFin, hcard, -⟩ := hlab
    haveI : Field K := hF
    haveI : Finite K := hFin
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcard] at h2
    norm_num at h2
  · obtain ⟨K, hF, hFin, hcard, ⟨e⟩⟩ := hlab
    have h4 : Nat.card K = 4 := by rw [hcard]; norm_num
    letI : Group.IsSolvable
        (@LargeEvenProj (Fin 3) (Fin.fintype 3) (instDecidableEqFin 3) K hF
          (@LargeEvenSUGroup (Fin 3) (Fin.fintype 3) (instDecidableEqFin 3) K hF 2)) :=
      @largeEvenProj_su_three_two_isSolvable K hF hFin h4
    have hsolv : Group.IsSolvable R :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact (CFSG.ComponentClassification.AS76b.not_isSolvable_of_isSimpleGroup
      (by
        intro h
        obtain ⟨a, b, hab⟩ := hnab
        exact hab (h a b))
      hsolv).elim

private theorem orthTTwATwo_iso {k : ℕ} {lab0 : LargeEvenLabel}
    (h : GGLabelIso ⟨.twA, 2, k⟩ lab0) : lab0 = ⟨.twA, 2, k⟩ := by
  rcases lab0 with ⟨t, r, n⟩
  cases t <;> simp [GGLabelIso] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

private theorem orthTTwATwo_lambda2_A {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (h : m = 2 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.A, m - 1, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_twA {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    (h : m = 3 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.twA, m - 1, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_A1 {n : ℕ} (hn : 2 ≤ n) :
    LargeEvenInLambda2 (⟨.A, 1, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_A1sq {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_A3 {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_twA3 {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_D {s n : ℕ} (hs : 4 ≤ s) (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.D, s, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_twD {s n : ℕ} (hs : 4 ≤ s) (hn : 1 ≤ n) :
    LargeEvenInLambda2 (⟨.twD, s, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

private theorem orthTTwATwo_lambda2_twA2 {k : ℕ} (hk : 2 ≤ k) :
    LargeEvenInLambda2 (⟨.twA, 2, k⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  omega

section OrthTTwATwoAux

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

private theorem orthTTwATwo_aux
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {r : ℕ} (hdim : Module.finrank K V = 2 * r) {k : ℕ}
    (hlab : GGHasLabel ⟨.twA, 2, k⟩ (J' ⧸ Subgroup.center J')) :
    Subgroup.center J' ≠ ⊥ ∧ r ≤ 4 := by
  classical
  have hlift := orthT_lift hQ hT hR hĀI
  obtain ⟨x, Â, hrest⟩ := hlift
  have hxodd := hrest.2.1
  have hxne1 := hrest.2.2.1
  have hfx := hrest.2.2.2.2.2.2.2.2.2.1
  have hcases := hrest.2.2.2.2.2.2.2.2.2.2
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
  have hq := hR.comp.2.2
  haveI : IsSimpleGroup (J' ⧸ Subgroup.center J') := hq.2
  haveI : Group.IsPerfect ↥J' := ⟨hq.1⟩
  haveI : Group.IsPerfect (J' ⧸ Subgroup.center J') := inferInstance
  have hnab : ∃ a b : J' ⧸ Subgroup.center J', a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative (J' ⧸ Subgroup.center J') := ⟨⟨h⟩⟩
    exact (Group.IsPerfect.not_isMulCommutative (J' ⧸ Subgroup.center J')) inferInstance
  have hk2 : 2 ≤ k := orthTTwATwo_k hnab hlab
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst hn0
    rw [hK] at hK2
    norm_num at hK2
  have hmain : ∃ h : K[X], h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧
      h = X ^ 2 + X + 1 ∧
      primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 ∧
      CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
      componentImage Q (x : V ≃ₗ[K] V) h = J' ∧
      ρ x ∈ J' ∧ n = k ∧ 3 ∣ Nat.card K + 1 := by
    have hrigid : ∀ {lab : LargeEvenLabel}, LargeEvenInLambda2 lab →
        GGHasLabel lab (J' ⧸ Subgroup.center J') → lab = ⟨.twA, 2, k⟩ := by
      intro lab hlam hlab0
      exact orthTTwATwo_iso (CFSG.StandardType.ggLabelRigidInput_holds ⟨.twA, 2, k⟩ lab
        (J' ⧸ Subgroup.center J') (orthTTwATwo_lambda2_twA2 hk2) hlam hlab hlab0)
    rcases hcases with ⟨h, hh, hne1, hqsp, hJ⟩ | ⟨F, hFq, hFle, hFn, hJ⟩
    · have hbl := orthT_blockLabel hK hxodd hh hne1 hqsp
          (L := componentImage Q (x : V ≃ₗ[K] V) h) rfl
      rcases hbl.2.2 with ⟨-, hdvd, hlabA⟩ | ⟨hphi, hdvdp, hcase⟩
      · have hn2 : 2 ≤ n := by
          by_contra h2
          have hn1' : n = 1 := by omega
          subst hn1'
          norm_num at hdvd
        rw [← hJ] at hlabA
        have hEq := hrigid (orthTTwATwo_lambda2_A hbl.1 hn1 (fun _ => hn2)) hlabA
        simp at hEq
      · rcases hcase with ⟨hm2, hn2, hlabA1⟩ | ⟨hm3, hexc, hlabTwA⟩
        · rw [← hJ] at hlabA1
          have hEq := hrigid (orthTTwATwo_lambda2_A1 hn2) hlabA1
          simp at hEq
        · have hn2 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 → 2 ≤ n := by
            intro hm
            by_contra h2
            exact hexc ⟨by omega, hm⟩
          rw [← hJ] at hlabTwA
          have hEq := hrigid (orthTTwATwo_lambda2_twA hm3 hn1 hn2) hlabTwA
          simp only [LargeEvenLabel.mk.injEq] at hEq
          obtain ⟨-, hm_eq, hnk⟩ := hEq
          have hm3' : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 3 := by omega
          refine ⟨h, hh, hphi, hm3', hqsp, hJ.symm, ?_, hnk, ?_⟩
          · have hdiv : 3 ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := by
              rw [hm3']
            have hmem := hbl.2.1 hdiv
            rw [← hJ] at hmem
            exact hmem
          · rw [hK]
            exact hdvdp
    · have hfl := orthT_fixedLabel hK hQ hxodd hFq hFle hFn
          (L := (F.subgroupOf (orthDerived Q)).map
            (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)))) rfl
      obtain ⟨s, -, hcasesL⟩ := hfl
      rcases hcasesL with ⟨hs4, -, hlabD⟩ | ⟨hs4, -, hlabTwD⟩ | ⟨hs3, -, hlabA3⟩ |
        ⟨hs3, -, hlabTwA3⟩ | ⟨hs2, -, hlabA1sq⟩ | ⟨hs2, -, hn2, hlabA1⟩
      · rw [← hJ] at hlabD
        have hEq := hrigid (orthTTwATwo_lambda2_D hs4 hn1) hlabD
        simp at hEq
      · rw [← hJ] at hlabTwD
        have hEq := hrigid (orthTTwATwo_lambda2_twD hs4 hn1) hlabTwD
        simp at hEq
      · rw [← hJ] at hlabA3
        have hEq := hrigid (orthTTwATwo_lambda2_A3 hn1) hlabA3
        simp at hEq
      · rw [← hJ] at hlabTwA3
        have hEq := hrigid (orthTTwATwo_lambda2_twA3 hn1) hlabTwA3
        simp at hEq
      · rw [← hJ] at hlabA1sq
        have hEq := hrigid (orthTTwATwo_lambda2_A1sq hn1) hlabA1sq
        simp at hEq
      · rw [← hJ] at hlabA1
        have hEq := hrigid (orthTTwATwo_lambda2_A1 hn2) hlabA1
        simp at hEq
  obtain ⟨h, hh, hphi, hm3, hqsp, hJcomp, hρxJ, hnk, hpqK⟩ := hmain
  have hρx_ne : ρ x ≠ 1 := by
    intro h1
    change QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)) x = 1 at h1
    have hxN : x ∈ (CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q) :=
      (QuotientGroup.eq_one_iff x).mp (by simpa only [QuotientGroup.mk'_apply] using h1)
    have hxscal : (x : V ≃ₗ[K] V) ∈ CFSG.ClassicalGroups.Orthogonal.scalars K V :=
      Subgroup.mem_subgroupOf.mp hxN
    haveI : Nontrivial V := by
      have hpos : 0 < Module.finrank K V := by
        obtain ⟨U, hU, -⟩ := hT
        have hle := Submodule.finrank_le U
        omega
      exact Module.nontrivial_of_finrank_pos (R := K) hpos
    exact hxne1 (Subtype.ext
      (CFSG.RankThree.PartOne.eq_one_of_mem_scalars_of_mem_orthDerived hQ x.2 hxscal))
  have hcomm : ∀ g ∈ J', ρ x * g = g * ρ x := by
    intro g hg
    have hg' : g ∈ ((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)).map ρ := by
      rw [← hJcomp] at hg
      simpa only [componentImage] using hg
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hg'
    have hf' : (f : V ≃ₗ[K] V) ∈ specialBlock Q (x : V ≃ₗ[K] V) h := hf
    have hfC : (f : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
      specialBlock_le_isometryCentralizer h hf'
    have hfx : (f : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) * (f : V ≃ₗ[K] V) := by
      ext v
      exact (mem_isometryCentralizer.mp hfC).2 v
    have hsub : f * x = x * f := Subtype.ext hfx
    rw [← map_mul, ← map_mul]
    exact congrArg ρ hsub.symm
  have hz : (⟨ρ x, hρxJ⟩ : ↥J') ∈ Subgroup.center ↥J' := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm (g : ProjOrthDerived Q) g.2).symm
  have hz_ne : (⟨ρ x, hρxJ⟩ : ↥J') ≠ 1 := by
    intro h1
    exact hρx_ne (congrArg Subtype.val h1)
  have hcenter : Subgroup.center J' ≠ ⊥ := by
    intro hbot
    have hmem : (⟨ρ x, hρxJ⟩ : ↥J') ∈ (⊥ : Subgroup ↥J') := hbot ▸ hz
    exact hz_ne (Subgroup.mem_bot.mp hmem)
  have hmem_phi : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_mem hxodd hpqK
      (fun h1 => hxne1 (Subtype.ext h1))
  have hdimW : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 2 * r - 6 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hxodd.fixed_others.1
    rw [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.othersSpace_eq hxodd hpqK hmem_phi,
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.finrank_phi hmem_phi] at hsum
    have hm_phi : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) = 3 := by
      rw [← hphi]
      exact hm3
    rw [hm_phi, hdim] at hsum
    omega
  have hrank : r ≤ 4 := by
    by_contra hr
    simp only [not_le] at hr
    have h4 : 4 ≤ Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) := by omega
    have hsmall : ¬ (Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
        n = 1) := by
      rintro ⟨-, -, hn1'⟩
      omega
    obtain ⟨F, hFq, hFle, hFn, -⟩ := orthT_fixedExists hK hQ hxodd h4 hsmall
    have hmap := hfx F hFq hFle hFn
    have hne1 : h ≠ X - 1 := by
      rw [hphi]
      exact CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_ne
    have hne := orthT_fixed_ne_block hQ hxodd hh hne1 hqsp hFq hFle
    exact hne (hmap.trans hJcomp.symm)
  exact ⟨hcenter, hrank⟩

end OrthTTwATwoAux

theorem orthT_twA2
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {Ā : Subgroup (MulAut (ProjOrthDerived Q))} {δ' : MulAut (ProjOrthDerived Q)}
    {J' : Subgroup (ProjOrthDerived Q)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenInnSet (ProjOrthDerived Q))
    {r : ℕ} (hdim : Module.finrank K V = 2 * r) {k : ℕ}
    (hlab : GGHasLabel ⟨.twA, 2, k⟩ (J' ⧸ Subgroup.center J')) :
    Subgroup.center J' ≠ ⊥ ∧ r ≤ 4 := by
  exact orthTTwATwo_aux hK hQ hT hR hĀI hdim hlab

end CFSG.StandardType.TablePThreeKG

end
