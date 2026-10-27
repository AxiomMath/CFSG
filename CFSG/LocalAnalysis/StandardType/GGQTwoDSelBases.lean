module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelUnit
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelOrth

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.ClassicalInvolution.Phan

section Bases


@[expose] def GGQTwoDUnitBaseInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        qtwoOrthL.compl G L 𝒦 →
          ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 2) (ψ : Su F0 2 1 m →* G)
            (ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)), QTwoUnitBase p B Bs x L ψ ε

@[expose] def GGQTwoDOrthBaseInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        qtwoOrthL G L 𝒦 →
          ∃ Φ : OrthTorus.OrthFrameCore p Bs L, Nat.card Φ.F = 2 ∧ Subgroup.center ↥L = ⊥

theorem ggQTwoLGenRankTwoInputOn_of_bases {R : ℕ → Prop} (hR : ∀ m, R m → 4 ≤ m)
    (hSM : GGQTwoDSelModuleInputOn R) (hU : GGQTwoDUnitBaseInputOn R)
    (hO : GGQTwoDOrthBaseInputOn R) : GGQTwoLGenRankTwoInputOn R := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM
  obtain ⟨β, hβ⟩ := hSM G p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM
  by_cases hc : qtwoOrthL G L 𝒦
  · obtain ⟨Φ, hF, hZ⟩ := hO G p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM hc
    have hrc := hcfg.1
    have : Fact p.Prime := ⟨(ggRouteCfg_prime hrc).1⟩
    obtain ⟨-, -, -, hpres, r, hr, hrC, h6⟩ := hcfg
    have hp : p = 3 := ggQTwo_p_eq_three hrc M e hpres hr hrC h6
    exact qtwoLGen_of_orthChart hp e' (hR m hRm) hM β hβ Φ hF hZ (ggRouteCfg_isElemAbelian hrc)
  · obtain ⟨F0, _, _, _, ψ, ε, hB⟩ := hU G p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM hc
    exact qtwoLGen_of_unitaryBase e' (hR m hRm) hM β hβ hB

end Bases

end CFSG.StandardType.QTwo

end
