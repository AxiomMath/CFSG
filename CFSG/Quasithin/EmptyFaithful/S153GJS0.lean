module

public import CFSG.Quasithin.EmptyFaithful.S153GFinal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def CountS0Max : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → conjBy153 t' (S0153 T V₁ L) = S0153 T V₁ L →
        ∃ A : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) A ∧ A ≤ S0153 T V₁ L

section Tools

variable {G : Type} [Group G]

private theorem js0_mem_normalizer_commutator {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

private theorem js0_isMaxElemAbelian_of_le {S S₀ A' A₀ : Subgroup G} (hS₀ : S₀ ≤ S)
    (hA' : IsMaxElemAbelian S A') (hA'S₀ : A' ≤ S₀) (hA₀ : IsMaxElemAbelian S₀ A₀) :
    IsMaxElemAbelian S A₀ :=
  ⟨hA₀.1.trans hS₀, hA₀.2.1, fun B hB hBel =>
    (hA'.2.2 B hB hBel).trans (hA₀.2.2 A' hA'S₀ hA'.2.1)⟩

end Tools

section Offenders

variable {G : Type} [Group G] [Finite G]

theorem js0_exists_offender {T V₁ U A₀ : Subgroup G}
    (hA₀ : IsMaxElemAbelian (Sgp153 T V₁) A₀) (hnc : ¬ A₀ ≤ Subgroup.centralizer (U : Set G)) :
    ∃ B : Subgroup G, IsOffenderB T V₁ U B ∧ autOn B U ≤ autOn A₀ U := by
  have : Finite (MulAut ↥U) :=
    Finite.of_injective (fun f : MulAut ↥U => (f : ↥U → ↥U)) DFunLike.coe_injective
  suffices h : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card ↥(autOn A U) = n →
      IsMaxElemAbelian (Sgp153 T V₁) A → ¬ A ≤ Subgroup.centralizer (U : Set G) →
        ∃ B : Subgroup G, IsOffenderB T V₁ U B ∧ autOn B U ≤ autOn A U from h _ A₀ rfl hA₀ hnc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn hA hnA
    by_cases hoff : IsOffenderB T V₁ U A
    · exact ⟨A, hoff, le_rfl⟩
    · have hex : ∃ B' : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) B' ∧
          ¬ B' ≤ Subgroup.centralizer (U : Set G) ∧ autOn B' U ≤ autOn A U ∧
            autOn B' U ≠ autOn A U := by
        by_contra hcon
        refine hoff ⟨hA, hnA, fun B hB hBn hle => ?_⟩
        by_contra hne
        exact hcon ⟨B, hB, hBn, hle, hne⟩
      obtain ⟨B', hB', hB'n, hle, hne⟩ := hex
      have hlt : Nat.card ↥(autOn B' U) < n := by
        by_contra hge
        exact hne (Subgroup.eq_of_le_of_card_ge hle (hn ▸ not_lt.mp hge))
      obtain ⟨B, hBoff, hBle⟩ := ih _ hlt B' rfl hB' hB'n
      exact ⟨B, hBoff, hBle.trans hle⟩

end Offenders

theorem countJS0_of_narrow (hC : CountCentralizer) (hM : CountS0Max) : CountJS0 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hS0 hB
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 (Sgp153 T V₁) := hsyl.2.1
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIUI : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hIU : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := fun g hg =>
    js0_mem_normalizer_commutator (hIUI hg) (hIL hg)
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hOS : pCoreOf 2 I ≤ Sgp153 T V₁ := S153D.pCoreOf_le_Sgp153' hF
  have hOL : pCoreOf 2 I ≤ L ⊔ pCoreOf 2 (L ⊔ Sgp153 T V₁) := by
    rw [hIeq]
    exact le_sup_right
  have hOS₀ : pCoreOf 2 I ≤ S0153 T V₁ L := le_inf hOS hOL
  have hKS : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ Sgp153 T V₁ :=
    hC G T Mc M V₁ V₂ Yp I L t c cc
  have hIK : I ≤ Subgroup.normalizer
      ((I ⊓ Subgroup.centralizer (UL153 T I L : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B2F.le_normalizer_centralizer hIU hg⟩
  have hK2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (UL153 T I L : Set G)) := hS2.to_le hKS
  have hKO : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hIK hK2
  have hKS₀ : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ S0153 T V₁ L := hKO.trans hOS₀
  have hS₀S : S0153 T V₁ L ≤ Sgp153 T V₁ := inf_le_left
  obtain ⟨A', hA', hA'S₀⟩ := hM G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hS0
  unfold thompsonJ
  refine iSup₂_le fun A₀ hA₀ => ?_
  by_contra hnc
  obtain ⟨B, hBoff, hBle⟩ := js0_exists_offender (js0_isMaxElemAbelian_of_le hS₀S hA' hA'S₀ hA₀) hnc
  exact hB B hBoff (S153D.le_of_autOn_le hIU (hBoff.1.1.trans hSI) (hS₀S.trans hSI) hKS₀
    (hBle.trans (A4.autOn_mono hA₀.1)))

end CFSG.Quasithin
