module

public import CFSG.Quasithin.EmptyFaithful.SBc7LDP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc7

section NotCentQ

variable {G : Type} [Group G]

theorem centralizes_of_hyperplane' {L I Yp : Subgroup G} (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L)
    (hLDP : ⁅L, I ⊓ Subgroup.centralizer (Yp : Set G)⁆ ≤ pCoreOf 2 L)
    (hQab : ∀ x : G, x ∈ ⁅pCoreOf 2 L, L⁆ → ∀ y : G, y ∈ ⁅pCoreOf 2 L, L⁆ → x * y = y * x)
    (hgen : ⁅pCoreOf 2 L, L⁆ ≤ ⨆ (W : Subgroup G) (_ : W ≤ ⁅pCoreOf 2 L, L⁆ ∧
      L ≤ Subgroup.normalizer (W : Set G) ∧ W ⊓ Yp ≠ ⊥ ∧ ∀ W' : Subgroup G, W' ≤ W →
        L ≤ Subgroup.normalizer (W' : Set G) → W' = ⊥ ∨ W' = W), W) :
    I ⊓ Subgroup.centralizer (Yp : Set G) ≤
      Subgroup.centralizer ((⁅pCoreOf 2 L, L⁆ : Subgroup G) : Set G) := by
  set Q : Subgroup G := ⁅pCoreOf 2 L, L⁆ with hQ
  set D : Subgroup G := I ⊓ Subgroup.centralizer (Yp : Set G) with hDdef
  have hLDQ : ⁅L, D⁆ ≤ Q := SBc4.commutator_le_Q hIL hperf inf_le_left hLDP
  intro d hd
  have hW : ∀ W : Subgroup G, (W ≤ Q ∧ L ≤ Subgroup.normalizer (W : Set G) ∧ W ⊓ Yp ≠ ⊥ ∧
      ∀ W' : Subgroup G, W' ≤ W → L ≤ Subgroup.normalizer (W' : Set G) → W' = ⊥ ∨ W' = W) →
      W ≤ Subgroup.centralizer ({d} : Set G) := by
    rintro W ⟨hWQ, hWn, hWY, hWirr⟩
    have hcl : conjClosure (W ⊓ Yp) L ≤ Subgroup.centralizer ({d} : Set G) := by
      refine conjClosure_le fun l hl y hy => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have hq : l * g * l⁻¹ * g⁻¹ ∈ Q :=
        hLDQ (Subgroup.commutator_mem_commutator hl hd)
      have hy' : l * y * l⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hWn hl) y).mp hy.1
      have hgy : y * g = g * y := Subgroup.mem_centralizer_iff.mp hd.2 y hy.2
      have hqy : (l * g * l⁻¹ * g⁻¹) * (l * y * l⁻¹) = (l * y * l⁻¹) * (l * g * l⁻¹ * g⁻¹) :=
        hQab _ hq _ (hWQ hy')
      have h1 : (l * g * l⁻¹) * (l * y * l⁻¹) = (l * y * l⁻¹) * (l * g * l⁻¹) := by
        calc (l * g * l⁻¹) * (l * y * l⁻¹) = l * (g * y) * l⁻¹ := by group
          _ = l * (y * g) * l⁻¹ := by rw [hgy]
          _ = (l * y * l⁻¹) * (l * g * l⁻¹) := by group
      set q : G := l * g * l⁻¹ * g⁻¹ with hqdef
      have hqd : l * g * l⁻¹ = q * g := by rw [hqdef]; group
      rw [hqd] at h1
      have h3 : q * (g * (l * y * l⁻¹)) = q * ((l * y * l⁻¹) * g) := by
        calc q * (g * (l * y * l⁻¹)) = (q * g) * (l * y * l⁻¹) := by group
          _ = (l * y * l⁻¹) * (q * g) := h1
          _ = ((l * y * l⁻¹) * q) * g := by group
          _ = (q * (l * y * l⁻¹)) * g := by rw [hqy]
          _ = q * ((l * y * l⁻¹) * g) := by group
      exact mul_left_cancel h3
    have hsub : conjClosure (W ⊓ Yp) L ≤ W := by
      refine conjClosure_le fun l hl y hy => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hWn hl) y).mp hy.1
    have hne : conjClosure (W ⊓ Yp) L ≠ ⊥ := fun h =>
      hWY (le_bot_iff.1 (h ▸ le_conjClosure (W ⊓ Yp) L))
    rcases hWirr _ hsub (le_normalizer_conjClosure (W ⊓ Yp) L) with h | h
    · exact absurd h hne
    · rw [← h]
      exact hcl
  have hQd : Q ≤ Subgroup.centralizer ({d} : Set G) := by
    refine hgen.trans (iSup₂_le fun W hWprop => hW W hWprop)
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact (Subgroup.mem_centralizer_iff.mp (hQd hq) d (Set.mem_singleton d)).symm

end NotCentQ

section Main

theorem input31NotCentQ_of_residue (hα : Input31QleYp) : Input31NotCentQ := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hout hnot
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hperf := SBc4.perfect_of_ctx c
  have hcases := hout.1
  have hcase12 : (IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L) → False := by
    intro h12
    have hD := commutator_centralizer_le_pCoreOf c hout h12
    have hgen := input31Hyperplane_holds G T Mc M V₁ V₂ Yp I L t c hout h12
    exact hnot (centralizes_of_hyperplane' hIL hperf hD (SBc4.blockU_comm_of_case12 c h12) hgen)
  rcases hcases with hA | hG | ⟨-, h1 | h2 | h3⟩
  · exact hnot (SBc4.centralizes_of_le_Yp (hα G T Mc M V₁ V₂ Yp I L t c hout (Or.inl hA)))
  · exact hnot (SBc4.centralizes_of_le_Yp
      (hα G T Mc M V₁ V₂ Yp I L t c hout (Or.inr (Or.inl hG))))
  · exact hcase12 (Or.inl h1)
  · exact hcase12 (Or.inr h2)
  · exact hnot (SBc4.centralizes_of_le_Yp
      (hα G T Mc M V₁ V₂ Yp I L t c hout (Or.inr (Or.inr h3))))

theorem input15331_of_residues (hMS : Input31MSOutcome) (hC : Input31Cover) (hα : Input31QleYp) :
    Input15331 :=
  S153H.input15331_of_named_inputs hMS (SBc4.input31CentQ_of_cover hC)
    (input31NotCentQ_of_residue hα)

end Main

end SBc7

end CFSG.Quasithin
