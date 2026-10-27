module

public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Iso
public import CFSG.Quasithin.Background.SmithC27RCaseIIRad

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem three_of_residueTypeII_g2
    (hC132 : ASInputs.AS_C_1_32) (h : Hyp27 H R M K) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hV : IsElemAbelian 2 (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hKT : ∀ T : Subgroup (MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)),
      IsSylowTwoOf T (jPStar hV R K) → jPStar hV R K = autI hV K ⊔ T)
    (hG : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(quasithinG2 F) →* ↥(jPStar hV R K),
        (FFModel.zornQ (quasithinG2 F)).RealizesVia (jPStar hV R K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
        ∀ g : ↥(quasithinG2 F),
          ((π g : ↥(jPStar hV R K)) :
              MulAut (IntMod (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) hV)) ∈ autI hV K ↔
            (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  three_of_residueTypeII_g2_of_radical hC132 h h.starHyp hnS
    (pCore_autOn_inf_normalizer_R h.isTwoRadicalIn_sup h.starHyp) hV hKT hG

end CFSG.Quasithin.SmithC27
