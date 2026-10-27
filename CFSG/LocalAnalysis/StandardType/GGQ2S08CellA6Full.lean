module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA6FullE
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA6FullJ

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

@[expose] def GGQ2S08CellE (t : LargeEvenLieTag) (r : ℕ) (s : GGQ2ShapeTag) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → ¬ GGQTwoI1 Bs D J → 4 ∣ Nat.card ↥(ggAutomizer J Bs) →
    ∀ (M : GGQ2LDatum 3 Bs L x), M.HasShape s → ∀ {labL : LargeEvenLabel},
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
      labL.tag = t → labL.rank = r → GGLabQTwo 3 labL → GGQ2LabelWeyl labL M.coxeter →
      ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection 3 φ → GGQ2MovesX Bs x φ →
        GGQ2CentreNotIn Bs D φ → GGQ2EForm Bs J φ →
          g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G)

@[expose] def GGQ2S08CellK (t : LargeEvenLieTag) (r : ℕ) (s : GGQ2ShapeTag) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → ¬ GGQTwoI1 Bs D J → 4 ∣ Nat.card ↥(ggAutomizer J Bs) →
    ∀ (M : GGQ2LDatum 3 Bs L x), M.HasShape s → ∀ {labL : LargeEvenLabel},
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
      labL.tag = t → labL.rank = r → GGLabQTwo 3 labL → GGQ2LabelWeyl labL M.coxeter →
      ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection 3 φ → GGQ2MovesX Bs x φ →
        GGQ2CentreNotIn Bs D φ → ¬ GGQ2EForm Bs J φ → ∀ (y : G) (K : Subgroup G),
          GGNbr 3 B x D J y K → (∀ c : ↥Bs, (c : G) = y → φ c = c) →
          (¬ ∃ k ∈ K, GGQ2Ind Bs k φ) →
          (¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹) →
            g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G)

theorem GGQ2S08CellEK.of_halves {t : LargeEvenLieTag} {r : ℕ} {s : GGQ2ShapeTag}
    (hE : GGQ2S08CellE t r s) (hK : GGQ2S08CellK t r s) : GGQ2S08CellEK t r s := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hs labL hmark ht hr hq hW g φ hInd hR hM hCen
  exact ⟨hE hS hI1 hCav M hs hmark ht hr hq hW g φ hInd hR hM hCen,
    hK hS hI1 hCav M hs hmark ht hr hq hW g φ hInd hR hM hCen⟩

theorem a7fS_eq : a7fS = aFullS 7 := by
  funext k
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun (ZMod 3) (Fin 7)).ext fun j => ?_)
  rw [Pi.basisFun_apply]
  revert k j
  decide +kernel

theorem ggQ2s08_cellE_twA6
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hRig : GGLabelRigidInput) (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) :
    GGQ2S08CellE .twA 6 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl _ _
    hE
  have hW' : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 6).reindex e := by
    have key : ∀ m : ℕ, m = 6 → (∃ e : Fin m ≃ M.Λ, M.coxeter = (CoxeterMatrix.A m).reindex e) →
        ∃ e : Fin 6 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 6).reindex e := by
      rintro m rfl h
      exact h
    exact key _ hrank (by simpa only [GGQ2LabelWeyl, htag] using hWeyl)
  obtain ⟨e, he⟩ := hW'
  obtain ⟨κ, hκx, hκs⟩ := ggQ2_fullCoords_A7 M hShape.2.2.1 e (ggQ2_cartan_A e he M.isCartan)
  have hW := ggQ2Cell_map_automizer_L M κ e (aFullS 7) hκs
  rw [← a7fS_eq] at hW
  have hJ := ggQ2s08_a6f_jPos hRig hS M hMark ⟨htag, hrank, hq⟩ hWeyl κ hκx
    (hW ▸ closure_a7fS_le_permGroup)
  exact ggQ2s08_cellE_twA6_of_coords hLB hP hΓi hTBN hS hI1 hCav M κ hκx hW hJ g φ hInd hRefl hE

end CFSG.StandardType

end
