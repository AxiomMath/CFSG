module

public import CFSG.LocalAnalysis.StandardType.GGSixE6A24Centre
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.Timmesfeld.LieEmbed.A5Roots

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

abbrev EC : Type := ↥(adjointGroup .E6 F2)

@[expose] def blk (k : Fin 3) (j : Fin 2) : Fin 6 := ⟨2 * k.val + j.val, by omega⟩

section Model

@[expose] noncomputable def xr (β : Fin Tag.E6.rank → ℤ) : EC :=
  ⟨pinnedX .E6 F2 β 1, pinnedX_mem_adjointGroup β 1⟩

@[expose] noncomputable def sTheta : Subgroup EC :=
  (EPilot.highRootSL2 .E6 F2).subgroupOf (adjointGroup .E6 F2)

@[expose] noncomputable def zE : EC := xr (highRoot .E6) * xr (-highRoot .E6)

@[expose] noncomputable def lE : Subgroup EC := E6Pilot.a5Levi F2

@[expose] noncomputable def rOne (k l : Fin 3) : EC :=
  xr (a5Root (blk k 0) (blk l 0)) * xr (a5Root (blk k 1) (blk l 1))

@[expose] noncomputable def rOmega (k l : Fin 3) : EC :=
  xr (a5Root (blk k 0) (blk l 1)) * xr (a5Root (blk k 1) (blk l 0)) *
    xr (a5Root (blk k 1) (blk l 1))

@[expose] noncomputable def jE : Subgroup EC :=
  Subgroup.closure {g | ∃ k l : Fin 3, k ≠ l ∧ (g = rOne k l ∨ g = rOmega k l)}

@[expose] def E6TwoCentT31 : Prop :=
  ∀ t ∈ lE, orderOf t = 31 →
    Subgroup.centralizer ({t} : Set EC) = Subgroup.zpowers t ⊔ sTheta ∧
      Disjoint (Subgroup.zpowers t) sTheta ∧
      Nat.card (Subgroup.centralizer ({t} : Set EC)) = 186

end Model

@[expose] def GGSixE6A24Concl {E : Type} [Group E] (x₀ : E) (J' : Subgroup E) : Prop :=
  ∃ R' J₀' : Subgroup E, R' ≤ J' ∧ R' ≠ ⊥ ∧ IsPGroup 2 R' ∧ J₀' ≤ J' ∧
    pCoreOf 2 (Subgroup.normalizer (R' : Set E)) ⊔ J₀' = ⊤ ∧
    (∀ Q' : Subgroup E, Q' = pCoreOf 2 (Subgroup.normalizer (R' : Set E)) →
      ∀ U : Subgroup E, (Subgroup.center ↥Q').map Q'.subtype ≤ U → U ≤ Q' →
        U ≠ (Subgroup.center ↥Q').map Q'.subtype → U ≠ Q' →
        Subgroup.normalizer (R' : Set E) ≤ Subgroup.normalizer (U : Set E) →
        J' ⊔ U = ⊤) ∧
    GGRootNormInner R' ∧
    ∀ g : E, g ^ 3 = 1 → g ≠ 1 → g ∈ Subgroup.centralizer {x₀} →
      g ∈ Subgroup.centralizer (J' : Set E) →
      ∀ K' : Subgroup E, J' ≤ K' →
        CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer {g}) →
        GGRootNormNoCentral (R'.subgroupOf K') ∧
          (GGRootNormInner (R'.subgroupOf K') ∨
            ∃ δ : ↥(Subgroup.normalizer (K' : Set E)),
              (δ : E) ∈ Subgroup.centralizer {g} ∧
                (δ : E) ∈ Subgroup.normalizer (R' : Set E) ∧
                GGRootNormInnerDiag (R'.subgroupOf K') (K'.normalizerMonoidHom δ))

section Statements

@[expose] def E6TwoModelRest : Prop := GGSixE6A24Concl (E := EC) zE jE

@[expose] def GGSixE6A24ModelKnown : Prop := E6TwoCentT31 ∧ E6TwoModelRest

@[expose] def E6TwoOrder3Conj : Prop :=
  ∀ x : EC, orderOf x = 3 → 31 ∣ Nat.card (Subgroup.centralizer ({x} : Set EC)) →
    ∃ g : EC, g * x * g⁻¹ = zE ∨ g * x * g⁻¹ = zE⁻¹

@[expose] def E6TwoJUnique : Prop :=
  ∀ J' : Subgroup EC, J' ≤ lE → CFSG.Assembly.IsQuasisimple ↥J' →
    LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL 3 2 2 →
      ∃ l ∈ lE, J'.map (MulAut.conj l).toMonoidHom = jE

end Statements

end CFSG.StandardType.GGSixE6Two
