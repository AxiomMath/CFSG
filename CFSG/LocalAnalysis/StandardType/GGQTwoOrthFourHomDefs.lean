module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorPerm
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.PhanDn
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

@[expose] def GGQTwoOrthFourHomInput : Prop :=
  GGResXDichotomyInput → GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow →
    GGForkA8NotReflInput → GGRawInnFieldInput → GGRawInndiagIsoInput →
    GGResNbrFixCentralizesInput → GGLBalanceInput →
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)}, GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 → B = Bs →
  ∀ (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))) (i0 : Fin 4),
    (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 3 →
    (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0 →
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L →
    (∀ (y : G) (M : Subgroup G), GGNbr 3 B x D J y M →
      ggAutomizer M Bs ≤ ggAutomizerJoin L Bs 𝒦) →
    ggG0 3 B x L D J = L ⊔ ⨆ M ∈ 𝒦, M →
  ∀ {w : G} (hw : w ∈ Subgroup.normalizer (Bs : Set G)) {j : Fin 4}, j ≠ i0 →
    MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap i0 j) →
    Subgroup.center L = ⊥ ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
        (_ : CharP K 2) (E : QuadExt F K (unitaryInvolution K 2 1)), Nat.card F = 2 ∧
        ∃ (π : Fin 4 ≃ Fin 4) (κ₁ κ₂ : normOmega E 3 →* G)
          (χ : Multiplicative (ZMod 3) →* Kˣ) (t : Equiv.Perm (Fin 4) →* G)
          (Ψ : normOmega E 4 →* G),
          π (Fin.last 3) = i0 ∧ π 0 = j ∧
          GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ ∧
          GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj w).toMonoidHom) eta
            ((finRotate 4).trans π) κ₂ χ ∧
          t.comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 3 ↪ Fin 4)) =
            κ₁.comp (normPerm E le_rfl) ∧
          t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) = κ₂.comp (normPerm E le_rfl) ∧
          (∀ y : normOmega E 2,
            κ₁ (normPerm E le_rfl (finRotate 3) * normOmegaCast E (by norm_num) y *
                (normPerm E le_rfl (finRotate 3))⁻¹) =
              κ₂ (normOmegaCast E (by norm_num) y)) ∧
          (∀ (σ : Equiv.Perm (Fin 3))
            (hσ : κ₁ (normPerm E le_rfl σ) ∈ Subgroup.normalizer (Bs : Set G)),
            MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
              ((Fin.castSuccEmb (n := 3)).trans π.toEmbedding) σ)) ∧
          (∀ (σ : Equiv.Perm (Fin 3))
            (hσ : κ₂ (normPerm E le_rfl σ) ∈ Subgroup.normalizer (Bs : Set G)),
            MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
              ((Fin.castSuccEmb (n := 3)).trans ((finRotate 4).trans π).toEmbedding) σ)) ∧
          Function.Injective Ψ ∧
          (∀ a, Ψ (normOmegaCast E (Nat.le_succ 3) a) = κ₁ a) ∧
          (∀ σ, Ψ (normPerm E (by norm_num : 3 ≤ 4) σ) = t σ) ∧ Ψ.range = L ⊔ t.range

end CFSG.StandardType

end
