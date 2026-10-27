module

public import CFSG.Quasithin.EmptyFaithful.S153D33

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input34Borel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp T Mc M V₁ V₂ Yp I t → Concl15333 T M V₁ Yp I L →
      (∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) →
        ∃ B : Subgroup G, B ≤ conjClosure L (Sgp153 T V₁) ∧
          IsBorelIn (conjClosure L (Sgp153 T V₁)) B ∧
          Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (B : Set G) ∧ CharTwo B ∧
          ∀ X : Subgroup G, X ≤ conjClosure L (Sgp153 T V₁) →
            Sgp153 T V₁ ≤ Subgroup.normalizer (X : Set G) → B ≤ X →
              X ≠ conjClosure L (Sgp153 T V₁) → X = B

@[expose] def Input34Centralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp T Mc M V₁ V₂ Yp I t → Concl15333 T M V₁ Yp I L →
      (∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) →
        ∀ B : Subgroup G, IsBorelIn (conjClosure L (Sgp153 T V₁)) B →
          Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (B : Set G) →
          B = M ⊓ conjClosure L (Sgp153 T V₁) →
            Yp ≤ Subgroup.centralizer (conjClosure L (Sgp153 T V₁) : Set G)

namespace S153H

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem conjClosure_le_I (hSI : Sgp153 T V₁ ≤ I) (hLI : L ≤ I) :
    conjClosure L (Sgp153 T V₁) ≤ I :=
  conjClosure_le fun _ hs _ hl => I.mul_mem (I.mul_mem (hSI hs) (hLI hl)) (I.inv_mem (hSI hs))

theorem le_M_of_Yp_le_centralizer (c : CtxComp T Mc M V₁ V₂ Yp I t) (hL : Concl15333 T M V₁ Yp I L)
    (hY : Yp ≤ Subgroup.centralizer (conjClosure L (Sgp153 T V₁) : Set G)) : L ≤ M := by
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hLI : L ≤ I := le_of_mem_cComp hL.mem
  have hL₀I := conjClosure_le_I (T := T) (V₁ := V₁) hSI hLI
  have hLL₀ : L ≤ conjClosure L (Sgp153 T V₁) := le_conjClosure _ _
  have hC : conjClosure L (Sgp153 T V₁) ≤ Subgroup.centralizer (Yp : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hY hy) x hx).symm
  have hN : conjClosure L (Sgp153 T V₁) ≤ I ⊓ Subgroup.normalizer (Yp : Set G) :=
    le_inf hL₀I (hC.trans (Subgroup.centralizer_le_normalizer _))
  rw [c.facts.norm_eq] at hN
  exact (hLL₀.trans hN).trans inf_le_left

end S153H

end CFSG.Quasithin
