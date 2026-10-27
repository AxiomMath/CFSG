module

public import CFSG.Quasithin.Background.Harris.KFact2d.Lin2
public import CFSG.Quasithin.Background.Harris.KFact2d.ModelU3
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Hyp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.SzOneV2d
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
  CFSG.Quasithin.A312U3 CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups Matrix

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]


variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem ker_rhoU_scalar (hF : Nat.card F = p ^ 2) {A : ↥(GU2Stated (p ^ 1) F)}
    (h : piU p F (Lemma41aU3.blkU (uniData hF) A) = 1) :
    ∃ l : F, l ^ 3 = 1 ∧ ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) l := by
  obtain ⟨c, hc3, hc⟩ := exists_scalar_of_mem_ker hF (MonoidHom.mem_ker.mpr h)
  rw [matU_blkU hF] at hc
  refine ⟨c, hc3, ?_⟩
  ext i j
  have := congrFun (congrFun hc (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [Lemma41aL3.blkMat, Matrix.scalar_apply] using this

theorem unitary_eq (hF : Nat.card F = p ^ 2) {M : GL (Fin 2) F} (hM : M ∈ GU2Stated (p ^ 1) F) :
    ((M : Matrix (Fin 2) (Fin 2) F).map (· ^ p))ᵀ * (M : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have := (Lemma41aU3.mem_GU2Stated_iff (uniData hF)).1 hM
  rwa [Lemma41aU3.bar_eq_pow (uniData hF), pow_one] at this

theorem f1At_special_u (hF : Nat.card F = p ^ 2) (hp4 : p % 4 = 1)
    {U : Subgroup (PSU3F p F)} (hU : SpecialSylowU hF U) : F1At (PSU3F p F) U := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_u hp2 hF
  obtain ⟨-, hUB, c, d, hQ, hc, hd⟩ := hU
  intro E hE hEU hUN t ht
  refine ⟨hEU ht, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  obtain ⟨_, ⟨A, rfl⟩, htA⟩ := hUB (hEU ht)
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hUB hu
  have htA' : t = piU p F (Lemma41aU3.blkU (uniData hF) A) := htA.symm
  subst htA'
  by_cases hs : ∃ a : F, ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a
  · obtain ⟨a, ha⟩ := hs
    have hAB : A * B = B * A := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [ha]
      exact scalar_mul_comm a _
    show piU p F (Lemma41aU3.blkU (uniData hF) B) * piU p F (Lemma41aU3.blkU (uniData hF) A) =
      piU p F (Lemma41aU3.blkU (uniData hF) A) * piU p F (Lemma41aU3.blkU (uniData hF) B)
    simp only [← map_mul]
    rw [hAB]
  · exfalso
    have hA : ∀ a : F, ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) a :=
      fun a h => hs ⟨a, h⟩
    have hsq : piU p F (Lemma41aU3.blkU (uniData hF) A) *
        piU p F (Lemma41aU3.blkU (uniData hF) A) = 1 := by
      have := hE.2 _ ht
      simpa [sq] using this
    obtain ⟨l, hl3, hAA'⟩ := ker_rhoU_scalar hF (A := A * A) (by rw [map_mul, map_mul]; exact hsq)
    have hAA : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (A : GL (Fin 2) F) =
        Matrix.scalar (Fin 2) l := by
      simpa [Units.val_mul] using hAA'
    have hl : l ≠ 0 := by
      rintro rfl
      simp at hl3
    have hconj : ∀ g : ↥(StatedSU 2 (p ^ 1) F), piU p F (ofSU2 hF g) ∈ U →
        (((g : GL (Fin 2) F) * (A : GL (Fin 2) F) * (g : GL (Fin 2) F)⁻¹ : GL (Fin 2) F)) *
          (A : GL (Fin 2) F) = (A : GL (Fin 2) F) *
          ((g : GL (Fin 2) F) * (A : GL (Fin 2) F) * (g : GL (Fin 2) F)⁻¹) := by
      intro g hg
      let Z : ↥(GU2Stated (p ^ 1) F) := Subgroup.inclusion su2_le_gu2 g
      have hg' : piU p F (Lemma41aU3.blkU (uniData hF) Z) ∈ U := hg
      have hn := (Subgroup.mem_normalizer_iff.mp (hUN hg') _).1 ht
      have hn' : piU p F (Lemma41aU3.blkU (uniData hF) (Z * A * Z⁻¹)) ∈ E := by
        simp only [map_mul, map_inv]
        exact hn
      have hcm := hE.1.is_comm.comm ⟨_, hn'⟩ ⟨_, ht⟩
      have hcm' := congrArg Subtype.val hcm
      have key := commute_of_piU_commute hF (A := Z * A * Z⁻¹) (B := A) (by simpa using hcm')
      have := congrArg (fun y : ↥(GU2Stated (p ^ 1) F) => (y : GL (Fin 2) F)) key
      exact this
    have hQ' := hQ.map (StatedSU 2 (p ^ 1) F).subtype (StatedSU 2 (p ^ 1) F).subtype_injective
    obtain ⟨hC, hD, hDC⟩ := quat_relations h2 (det_of_mem_su2 hF c) hQ'
    have hcG : ((c : ↥(StatedSU 2 (p ^ 1) F)) : GL (Fin 2) F) ∈ GU2Stated (p ^ 1) F :=
      su2_le_gu2 c.2
    have hdG : ((d : ↥(StatedSU 2 (p ^ 1) F)) : GL (Fin 2) F) ∈ GU2Stated (p ^ 1) F :=
      su2_le_gu2 d.2
    obtain ⟨x, hxG, hxx, hxA⟩ := exists_comm_sqm1 (GU2Stated (p ^ 1) F) hcG hdG hA hAA hl h2 hC hD hDC
      (hconj c hc) (hconj d hd)
    obtain ⟨m, hm⟩ : ∃ m, p + 1 = 2 * m := ⟨(p + 1) / 2, by omega⟩
    have hmo : Odd m := Nat.odd_iff.2 (by omega)
    exact false_of_sqm1_comm_unitary (p := p) hA hAA hl3 h2 hm hmo (unitary_eq hF A.2)
      (unitary_eq hF hxG) hxx hxA


theorem f1_psu {X : Type} [Group X] [Finite X] {K S : Subgroup X} (hp4 : p % 4 = 1)
    (hK : IsPSU 3 p 1 ↥K) (hS : IsSylowTwoOf S K) :
    ∀ E : Subgroup X, IsElemAbelian 2 E → E ≤ S → S ≤ Subgroup.normalizer (E : Set X) →
      E ≤ E2P.zOf S := by
  obtain ⟨F, _, _, hF, e, U₀, hU₀, hmap⟩ := exists_equiv_special_u (p := p) (by omega) hK hS
  have h := f1At_special_u hF hp4 hU₀
  rw [← hmap] at h
  exact f1_of_model hS.1 (F1At.of_map e _ h)

end CFSG.Quasithin.Background.Harris.KFact2d
