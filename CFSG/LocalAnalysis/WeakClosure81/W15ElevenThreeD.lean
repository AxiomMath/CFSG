module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeA
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeB
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S4Branch15 (M V₀ V U S H : Subgroup G) : Prop :=
  Nonempty (↥(kHull15 V₀ H) ≃* Equiv.Perm (Fin 4)) ∧
    tSub15 M V₀ V U S ≤ kHull15 V₀ H ⊔ cSub15 M V₀ V U H S

@[expose] def W15Eleven3Dich (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M V₀ V U S H Q₀ : Subgroup G, ∀ p : ℕ, Cfg1511 M V₀ V U S H S Q₀ p →
    (∀ A ∈ elemFamilyIn 2 (tSub15 M V₀ V U S), A ≤ qSub15 M V₀ V U H S) ∨
      S4Branch15 M V₀ V U S H

@[expose] def W15Eleven3S4 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M V₀ V U S H Q₀ : Subgroup G, ∀ p : ℕ, Cfg1511 M V₀ V U S H S Q₀ p →
    S4Branch15 M V₀ V U S H →
    elemFamilyIn 2 (tSub15 M V₀ V U S) =
      {tSub15 M V₀ V U S ⊓ centralizer (V : Set G), iHull15 V₀ U H ⊔ cSub15 M V₀ V U H S}

namespace Cfg1511

variable {M V₀ V U S H Q₀ R X : Subgroup G} {p : ℕ} {v : G}

theorem R_le_normalizer_zOmega15
    (hD : W15Eleven3Dich G) (hS4 : W15Eleven3S4 G) (c : Cfg1511 M V₀ V U S H S Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) (hR : IsSylowIn 2 R (F11.CTilde M V₀ V))
    (hPR : S ⊓ F11.CTilde M V₀ V ≤ R) :
    R ≤ normalizer (zOmega15 (qSub15 M V₀ V U H S) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT : R ≤ normalizer (tSub15 M V₀ V U S : Set G) := c.R_le_normalizer_tSub15 hR hPR
  change R ≤ normalizer (elemCenterIn 2 (qSub15 M V₀ V U H S) : Set G)
  rcases hD M V₀ V U S H Q₀ p c with hA | hb
  · exact hRT.trans
      (normalizer_le_normalizer_elemCenterIn_of_forall_le 2 c.qSub15_le_tSub15 hA)
  · have hfam := hS4 M V₀ V U S H Q₀ p c hb
    have hRV : R ≤ normalizer (V : Set G) := by
      rw [c.cex.hyp.h6.normalizer_eq]
      exact hR.le.trans (cTilde_le_M M V₀ V)
    have hRD : R ≤ normalizer ((tSub15 M V₀ V U S ⊓ centralizer (V : Set G) : Subgroup G) :
        Set G) :=
      (le_inf hRT (le_normalizer_centralizer_of_le_normalizer hRV)).trans
        (Subgroup.inf_normalizer_le_normalizer_inf)
    have hfin := normalizer_inf_le_normalizer_elemCenterIn_of_family_eq 2 hfam
    rw [← c.qSub15_eq_sup hX] at hfin
    exact (le_inf hRT hRD).trans hfin

theorem three
    (hD : W15Eleven3Dich G) (hS4 : W15Eleven3S4 G) (c : Cfg1511 M V₀ V U S H S Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) (hR : IsSylowIn 2 R (F11.CTilde M V₀ V))
    (hPR : S ⊓ F11.CTilde M V₀ V ≤ R) :
    U ⊔ v1Sub15 V₀ U ≤ zOmega15 (qSub15 M V₀ V U H S) ∧
      R ≤ normalizer (zOmega15 (qSub15 M V₀ V U H S) : Set G) :=
  ⟨XData15.sup_le_zOmega15 c hX, c.R_le_normalizer_zOmega15 hD hS4 hX hR hPR⟩

theorem H_le_normalizer_zOmega15
    (hD : W15Eleven3Dich G) (hS4 : W15Eleven3S4 G) (c : Cfg1511 M V₀ V U S H S Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) :
    H ≤ normalizer (zOmega15 (qSub15 M V₀ V U H S) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hSR⟩ := exists_isSylowIn_ge 2 c.S_le_cTilde c.cex.sylow.isPGroup
  have hSR' : S ⊓ F11.CTilde M V₀ V ≤ R := inf_le_left.trans hSR
  have hRZ := c.R_le_normalizer_zOmega15 hD hS4 hX hR hSR'
  have hKQ : kHull15 V₀ H ≤ normalizer (qSub15 M V₀ V U H S : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
      (kHull15 V₀ H ⊔ tSub15 M V₀ V U S))
  have hKZ : kHull15 V₀ H ≤ normalizer (zOmega15 (qSub15 M V₀ V U H S) : Set G) :=
    hKQ.trans (normalizer_le_normalizer_elemCenterIn 2 (qSub15 M V₀ V U H S))
  have hHeq : kHull15 V₀ H ⊔ S = H := Hyp1510.eq_sup c.inputs c.std c.cex c.hyp
  exact hHeq.symm.le.trans (sup_le hKZ (hSR.trans hRZ))

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
