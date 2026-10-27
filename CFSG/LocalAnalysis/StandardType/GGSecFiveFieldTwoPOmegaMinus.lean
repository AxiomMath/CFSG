module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaMinusRoot
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEOmegaFourMinusPOmegaMinus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaMinus
import all CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinusFE

public section

namespace CFSG.StandardType

namespace FieldTwoPOmega

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.StandardType.ClassicalPosition
open scoped Matrix

section Cert


theorem omegaFourMinus_false_minus {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ n)
    (ψ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {L' : Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε⁆)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε < 2)
    (hm4 : ε.rank = 4 ∧ ∀ x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 f,
      Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 x = 0 →
      Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 y = 0 →
      QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y])
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hirr := minusCoeffs_irr 2 f
  have hprim := feomegm_isPrimIdemIn n hirr hn S hSU hS hodd hε hdeg
  have hdeg1 := feomegm_blockDegree_eq_one n hirr hn S hSU hS hodd hε hdeg hprim
  have htriv := feomegm_block_trivial n hirr hn S hSU hS hodd hε hdeg hprim hdeg1
  have hcomm := feomegm_blockGroup_commutator n hirr hn S hSU hS hodd hε htriv hm4.1 hm4.2
  have hJeq := feomegm_component_eq n hirr S hJe hcomm
  have hO : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsOmegaMinus
      (↥L' ⧸ Subgroup.center ↥L') 4 f :=
    feomegm_isOmegaMinus n hirr hn f hc S hJe hcomm hJeq
  have hL2 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2
      (↥L' ⧸ Subgroup.center ↥L') (2 * f) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isL2_of_isOmegaMinus_four hf hO
  obtain ⟨ξ⟩ := feomegm_quotientCenter ψ hψ hJe.2.2.1
  have h := fieldTwo_typeDet hl hn1 hne hM (t := .PSL) (m := 2) (f := 2 * f) (Or.inl rfl)
    (CFSG.Blueprint.LieModel.of_mulEquiv ξ
      (show CFSG.Blueprint.LieModel (↥L' ⧸ Subgroup.center ↥L') .PSL 2 2 (2 * f) from hL2))
  omega

theorem fieldExt_false_minus {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ n)
    (ψ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {L' : Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e))
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨t', m', f', hlt, ht', hmod⟩ :=
    RCKC1.rckIIp_component_model_PSL_or_PSU n (minusCoeffs_irr 2 f) hn f hc S hSU hS hodd hε hJe
      he heε hdeg
  exact false_of_fieldExt_model
    (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn (minusCoeffs_irr 2 f)) ψ hψ
    hl hn1 hne hM hlt hf ht' hmod

theorem dualPair_one_false_minus {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ n)
    (ψ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))
    (hsU : s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)).range)
    (hsodd : Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2)
    {L' : Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) {s}
        (e + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
            (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e),
        glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) {s}
        (e + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
            (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e)⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  have hSU : ∀ t ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      t ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)).range := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hsU
  have hS : ∀ t ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      ∀ t' ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
        Commute t t' := by
    intro t ht t' ht'
    rw [Set.mem_singleton_iff] at ht ht'
    rw [ht, ht']
  have hodd : ∀ t ∈ ({s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      Odd (orderOf t) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hsodd
  obtain ⟨r, ι, -, -, -, hcent, hrange, -⟩ :=
    exists_blockModel_dualPair_POmegaMinus_explicit n f hf {s} hSU hS hodd he hn hpair hdeg hJe
  exact false_of_dualPair_model hf
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) (minusCoeffs_irr 2 f))
    ψ hψ hl hn1 hne (FieldTwoPSp.not_isSolvable_of_isComponentOf hJe) hM ι hcent hrange s hsU he
    hpair hdeg

theorem selfDual_one_minus {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ n)
    (ψ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 f,
      Matrix.mulVec e x = x → Matrix.mulVec e y = y →
      Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 x = 0 →
      Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 y = 0 →
      QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    {L' : Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) :
    f = 1 ∧ SiegelBlock f
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) L' := by
  obtain ⟨t', m, ι, β₀, hcase, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩ :=
    exists_blockModel_selfDual_POmegaMinus_explicit n f hf S hSU hS hodd he hn hadj hdeg hnm hJe
  exact siegelBlock_of_selfDual_model hf ψ hψ hl hn1 hne
    (FieldTwoPSp.not_isSolvable_of_isComponentOf hJe) hM ι
    (hcase.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)) hlong hcent hrange hQ h₁ h₂ h₀ hX hX'

theorem selfDual_two_minus {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f) (hn : 4 ≤ n)
    (ψ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {L' : Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) :
    f = 1 ∧ SiegelBlock f
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) L' := by
  obtain ⟨r, ι, β₀, -, hlong, -, hrange, ⟨hinj, hr2, hnq⟩, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX,
    hX'⟩ := exists_blockModel_selfDualTwo_POmegaMinus_explicit_inj n f S hSU hS hodd he hn hadj
      hdeg₁ hdeg₂ hJe
  exact siegelBlock_of_SU_model hf ψ hψ hl hn1 hne hM ι hinj hr2 hnq hlong hrange hQ h₁ h₂ h₀ hX hX'

theorem finish_POmegaMinus {G : Type} [Group G] {n : ℕ} (hn : 4 ≤ n) {L : Subgroup G}
    (ψ : (ggU .POmegaMinus n 1).K →* G)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus n 1).K)
    {L' : Subgroup (ggU .POmegaMinus n 1).K} (hL'map : L'.map ψ = L)
    (hB : SiegelBlock 1
      (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) L') :
    ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
        ∃ (γ : Fin (ggU .POmegaMinus n 1).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .POmegaMinus n 1).D (GaloisField 2 1) γ)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
          ∃ u₀ : (ggU .POmegaMinus n 1).K,
            ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
              (ψ'.comp model'.phi).range := by
  obtain ⟨t', m, ι, β₀, hadm, hrank, hinj, hβ₀, hrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩ :=
    hB
  have hirr := minusCoeffs_irr 2 1
  let ψ₀ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1
    (minusCoeffs 2 1).2)) →* G := ψ
  have hinjA : Function.Injective (Spin.spinAction
      (Spin.quadMinus n (GaloisField 2 1) (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) := by
    have := Spin.isCentral_cliffordAlgebra_quadMinus n (minusCoeffs 2 1).1 (minusCoeffs 2 1).2 hirr
    exact (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero (GaloisField 2 1) 2))
  have hE := (Spin.range_spinAction_quadMinus (n := n) (K := GaloisField 2 1) hn hirr).ge
  obtain ⟨β, hβ, -, u, hu, -⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaMinus n hirr hn a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
  obtain ⟨model, model', hpt⟩ := exists_models_of_siegel (D := (ggU .POmegaMinus n 1).D)
    hinjA hE ι hinj hβ hβ₀ hQ h₁ h₂ h₀ hX hX' u hu
  refine ⟨t', m, ψ₀.comp ι, hadm, hrank, ?_, ?_, β, β₀, model, model', u, ?_⟩
  · intro y hy
    exact Subgroup.comap_center_le_center hinj (hψ hy)
  · rw [MonoidHom.range_comp, hrange]
    exact hL'map
  · congr 1
    ext A
    exact congrArg ψ₀ (hpt A)

theorem ggSecFiveQTwoFieldTwoSelectedAt_POmegaMinus :
    GGSecFiveQTwoFieldTwoSelectedAt .POmegaMinus := by
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  have hf : 1 ≤ f := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  let ψ₀ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
    (minusCoeffs 2 f).2)) →* G := ψ
  have hψ : ψ₀.ker ≤ Subgroup.center _ := hker
  have hsstar := hC.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hsstar.1.1.2 x hsstar.2.1
  have hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}) := by
    rw [hrange]
    exact hC.isComponentOf_ggG0_inf
  obtain ⟨s, -, hsodd, ε, hε, L', hL'comp, hL'map⟩ :=
    RCKRP.rckF1_POmegaMinus Nat.prime_three (by norm_num) hx3 (minusCoeffs_irr 2 f) hn ψ₀ rfl
      hψ hdiag hL
  obtain ⟨lab, hl, hn1, hne, -, hM⟩ := hC.exists_markedModel_of_qTwo hq
  rw [← hL'map] at hM
  let j := Spin.spinMatrix
    (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      ∀ b ∈ ({j s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
        Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))),
      Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hsodd
  obtain ⟨e, he, heε, hcase⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaMinus n f _ hSU hS hε
  rcases hcase with rfl | ⟨hne', hpair, hεeq⟩
  · have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val ''
        ({j s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))))) e < 2
    · by_cases hm4 : e.rank = 4 ∧ ∀ x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 f,
          Matrix.mulVec e x = x → Matrix.mulVec e y = y →
          Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 x = 0 →
          Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 y = 0 →
          QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 f) ![x, y]
      · exact (omegaFourMinus_false_minus hf hn ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp hdeg2
          hm4 hM).elim
      · obtain ⟨hf1, hB⟩ :=
          selfDual_one_minus hf hn ψ₀ hψ hl hn1 hne _ hSU hS hoddS he hadj hdeg2 hm4 hL'comp hM
        subst hf1
        exact finish_POmegaMinus hn ψ hker hL'map hB
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val ''
          ({j s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))))) e < 4
      · obtain ⟨hf1, hB⟩ := selfDual_two_minus hf hn ψ₀ hψ hl hn1 hne _ hSU hS hoddS he hadj
          (by omega) hdeg4 hL'comp hM
        subst hf1
        exact finish_POmegaMinus hn ψ hker hL'map hB
      · exact (fieldExt_false_minus hf hn ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp he heε
          (Or.inl ⟨rfl, by omega⟩) hM).elim
  · exfalso
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val ''
        ({j s} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f))))) e < 2
    · rw [hεeq] at hL'comp
      exact dualPair_one_false_minus hf hn ψ₀ hψ hl hn1 hne (j s) ⟨s, rfl⟩ hsodd he hpair hdeg2
        hL'comp hM
    · exact fieldExt_false_minus hf hn ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp he heε
        (Or.inr ⟨hne', by omega⟩) hM

theorem ggSecFiveQTwoFieldTwoSelectedInput_of_exc
    (hEx : ∀ t, GGExcFive t → GGSecFiveQTwoFieldTwoSelectedAt t) :
    GGSecFiveQTwoFieldTwoSelectedInput :=
  ggSecFiveQTwoFieldTwoSelectedInput_of_POmegaMinus_exc ggSecFiveQTwoFieldTwoSelectedAt_POmegaMinus
    hEx

theorem ggSecFiveQTwoFieldTwoSelectedInput_of_exc_tags
    (hF4 : GGSecFiveQTwoFieldTwoSelectedAt .F4) (hE6 : GGSecFiveQTwoFieldTwoSelectedAt .E6)
    (hE7 : GGSecFiveQTwoFieldTwoSelectedAt .E7) (hE8 : GGSecFiveQTwoFieldTwoSelectedAt .E8)
    (hTw : GGSecFiveQTwoFieldTwoSelectedAt .twistedE6) :
    GGSecFiveQTwoFieldTwoSelectedInput :=
  ggSecFiveQTwoFieldTwoSelectedInput_of_exc fun t ht => by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact hF4
    · exact hE6
    · exact hE7
    · exact hE8
    · exact hTw

end Cert

end FieldTwoPOmega

end CFSG.StandardType

end
