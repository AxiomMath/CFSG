module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourInputs
public import CFSG.ClassicalInvolution.WeakCT.F4Even
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Chain
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.RouteD.TypeF4Model

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD (IsTE6Chain exists_psi_of_chainTE6)

@[expose] def GGF4QGeFourSysF4Input :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGCentralImage .PSp 3 f L → GGCentralImage .PSp 3 f K →
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (U : Fin 4 → Subgroup G), Nat.card F = 2 ^ f ∧
          (∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
          (∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
            ∃ W, LinearBlockStandardPair F W (U i) (U j)) ∧
          (∃ W, SymplecticBlockStandardPair F W (U 1) (U 2)) ∧ ⨆ k, U k = ggG0 p B x L D J

@[expose] def GGF4QGeFourSysTwE6Input :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
    ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGSecFiveRouteCfg p B Bs x L D J {K} → GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∀ f, 2 ≤ f → p ∣ 2 ^ f - 1 → GGCentralImage .POmegaMinus 4 f L →
        (GGCentralImage .PSU 6 f K ∨ GGCentralImage .POmegaMinus 4 f K) →
          ∃ (hf : 1 ≤ f) (U : Fin 4 → Subgroup G),
            IsTE6Chain 2 f hf U ∧ ⨆ i, U i = ggG0 p B x L D J

theorem ggF4QGeFourF4Input_of_sys
    (h : GGF4QGeFourSysF4Input) : GGF4QGeFourF4Input := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK
  obtain ⟨F, _, _, U, hF, hcomm, hpair, hsp, hsup⟩ :=
    h G p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK
  have hadm : StatedLieAdmissible .F4 0 2 f := ⟨Nat.prime_two, by omega, rfl⟩
  have hq4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨Ψ, hker, hrange, -⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_f4_subgroup_even f hadm hF hq4 U hcomm hpair hsp
  exact ⟨Ψ, hadm, hker, hrange.trans hsup⟩

theorem ggF4QGeFourTwE6Input_of_sys
    (h : GGF4QGeFourSysTwE6Input) : GGF4QGeFourTwE6Input := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK
  obtain ⟨hf1, U, hU, hsup⟩ := h G p B Bs x L D J hR hW hq y K hNb hRC hWK f hf hp hL hK
  have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, hf1, rfl⟩
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨Ψ, hker, hrange, -⟩ := exists_psi_of_chainTE6 hadm hq4 hU
  exact ⟨Ψ, hadm, hker, hrange.trans hsup⟩

end CFSG.StandardType

end
