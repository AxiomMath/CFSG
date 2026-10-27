module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaMinus
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

theorem dualPair_star_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n F bq cq)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e) (hne : e ≠ ε) :
    formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) e ∈
        Algebra.adjoin F (Units.val '' S) ∧
      IsIdempotentElem (formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) e) ∧
      formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) e * e = 0 ∧
      e * formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) e = 0 ∧
      ε = e + formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) e := by
  obtain ⟨h1, h2, -, -, -, h6, h7, h8⟩ :=
    fepome_dualPair_star n hirr hn S hSU hS (J' := ⊥) hε he heε hne
  exact ⟨h1, h2, h6, h7, h8⟩

theorem exists_blockAction_dualPair_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n F bq cq)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra F K)
      (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)))
      (ρ : glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S ε →*
        (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e))),
      Module.finrank F K = blockDegree (Algebra.adjoin F (Units.val '' S)) e ∧
      Function.Bijective ρ ∧
      ∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S ε)
        (w : LinearMap.range (Matrix.mulVecLin e)),
        ((ρ u w : LinearMap.range (Matrix.mulVecLin e)) :
            Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) =
          ((Spin.spinMatrix (Spin.quadMinus n F bq cq)
              (u : ↥(spinGroup (Spin.quadMinus n F bq cq))) :
            Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
              F)).mulVec (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := by
  obtain ⟨K, hKfield, hKalg, hKfin, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) hS hodd he
  let := hKfield
  let := hKalg
  have := hKfin
  obtain ⟨W, rfl, hmod, htower, -, -, -, hK⟩ :=
    fepome_dualPair_blockModule n S hS he K π hπsurj hπker hπdeg
  let := hmod
  let := htower
  obtain ⟨ρ, hρ⟩ :=
    fepome_dualPair_blockActionHom n hirr hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg
      (LinearMap.range (Matrix.mulVecLin e)) rfl hK
  have hinj :=
    fepome_dualPair_blockAction_injective n hirr hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ
  have hsurj :=
    fepome_dualPair_blockAction_surjective n hirr hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ
  exact ⟨K, hKfield, hKfin, hKalg, hmod, htower, ρ, hπdeg, ⟨hinj, hsurj⟩, hρ⟩

end CFSG.StandardType.RCKRP
