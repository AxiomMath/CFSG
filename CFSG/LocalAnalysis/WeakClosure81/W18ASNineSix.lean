module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthBridge
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthLow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open scoped commutatorElement

theorem noSocle185Factor_statedOmega_quadMinus_three_of_card_eq_three
    (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(StatedOmega (StatedQuadMinus 3 F b c)) := by
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hbc
  have hdim : Module.finrank F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hno : ¬ ∃ T : Submodule F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F),
      Module.finrank F T = 3 ∧ ∀ x ∈ T, quadMinus 3 F b c x = 0 := by
    rintro ⟨T, hT, hTQ⟩
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by norm_num) hbc
      ⟨T, by omega, hTQ⟩
  obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived hodd (quadMinus 3 F b c)
      hQ hdim hno
  have hM : CFSG.IsComponent
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c))) :=
    ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
  have hmodel :=
    (CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_nonsplit_six
      (p := 3) (e := 1) Nat.prime_three (by norm_num) le_rfl (by rw [hF]; norm_num)
      (quadMinus 3 F b c) hQ hdim hno hM).2
  have hcard : Nat.card (↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadMinus 3 F b c))) ⧸ Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadMinus 3 F b c)))) = 3265920 := by
    have h := CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1) (by norm_num)
      (by norm_num) hmodel
    rw [show CFSG.Open.ordTwistedA (4 - 1) (3 ^ 1) = 3265920 by decide] at h
    exact h
  let e := statedOmegaEquivCommutator (coe_quadMinus 3 F b c)
  haveI : Finite ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c))) :=
    Finite.of_equiv _ e.toEquiv
  haveI := hq.2.1
  refine NoSocle185Factor.of_mulEquiv e.symm (NoSocle185Factor.of_normal _
    (NoSocle185Factor.of_commute fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1))
    (NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun eT => ?_⟩))
  have hT3 : Nat.card T = 3265920 := by
    rw [← Nat.card_congr eT.toEquiv, hcard]
  exact (hT.card_facts hO).2.2.2.2 hT3

theorem noSocle185Factor_projOmegaMinus_two_of_card_eq_three
    (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(CFSG.PGLModel.projOmegaMinus 2 F b c) :=
  NoSocle185Factor.of_surjective
    ((Matrix.ProjGenLinGroup.mk : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F →* _).subgroupMap
      (StatedOmega (StatedQuadMinus 3 F b c)))
    (MonoidHom.subgroupMap_surjective _ _)
    (noSocle185Factor_statedOmega_quadMinus_three_of_card_eq_three hO hF hbc)

theorem noSocle185Factor_of_isOrth6MinusMod (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    (h : IsOrth6MinusMod Y) : NoSocle185Factor Y := by
  obtain ⟨F, _, _, hF3, b, c, hbc, N, hPN, hNO, ⟨e⟩⟩ := h
  refine NoSocle185Factor.of_mulEquiv e.symm ?_
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) := inferInstance
  have hkey : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ CFSG.PGLModel.projOmegaMinus 2 F b c := by
    intro x hx y hy
    obtain ⟨g, hg, rfl⟩ := hNO hx
    obtain ⟨h, hh, rfl⟩ := hNO hy
    rw [← map_commutatorElement Matrix.ProjGenLinGroup.mk]
    exact Subgroup.mem_map_of_mem _ (Subgroup.commutator_mem_commutator hg hh)
  haveI : ((CFSG.PGLModel.projOmegaMinus 2 F b c).subgroupOf N).Normal := by
    refine ⟨fun a ha n => ?_⟩
    have h1 : ⁅(n : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F),
        (a : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F)⁆ ∈
        CFSG.PGLModel.projOmegaMinus 2 F b c := hkey n n.2 a a.2
    have h2 : (a : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) ∈
        CFSG.PGLModel.projOmegaMinus 2 F b c := ha
    have h3 := mul_mem h1 h2
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def, mul_assoc] using h3
  refine NoSocle185Factor.of_normal ((CFSG.PGLModel.projOmegaMinus 2 F b c).subgroupOf N) ?_ ?_
  · exact NoSocle185Factor.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPN).symm
      (noSocle185Factor_projOmegaMinus_two_of_card_eq_three hO hF3 hbc)
  · refine NoSocle185Factor.of_commute fun a b => ?_
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hkey ((b⁻¹ : N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) (b⁻¹ : N).2
      ((a⁻¹ : N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) (a⁻¹ : N).2
    simpa [commutatorElement_def, mul_assoc] using this

end CFSG.LocalAnalysis.WeakClosure81

end
