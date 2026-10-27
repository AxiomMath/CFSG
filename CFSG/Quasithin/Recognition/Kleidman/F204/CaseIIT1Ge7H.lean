module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7G
public import CFSG.Quasithin.Recognition.Kleidman.F204.EqZ

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
private theorem card_conjSub_eq' (g : G) (V : Subgroup G) : Nat.card (conjSub g V) = Nat.card V := by
  unfold conjSub
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem false_of_five_centralizes (F : Frame L1 L2 S D X) {α β : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hαβ : β ∈ nbrs α) (hβ : vtype β = false) (hb5 : 5 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
    (hsec : ∀ c ∈ stab β, c ^ 5 = 1 → ∀ u ∈ Vball 3 β, c * u * c⁻¹ * u⁻¹ ∈ Vn β) : False := by
  have hA := Amal.of_frame F
  obtain ⟨c, hc, hcQ, hc5⟩ := exists_five_stab F hβ
  have hc5' : c ^ 5 ∈ Qv β := by rw [hc5]; exact one_mem _
  have hnorm : ∀ l ∈ nbrs β, c ∈ Subgroup.normalizer (Vball 2 l : Set G) := by
    intro l hl
    have hβl : β ∈ nbrs l := mem_nbrs_symm hl
    have hVl : Vn β ≤ Vball 2 l := Vn_le_Vball_two_of_mem_nbrs hl
    have hle : conjSub c (Vball 2 l) ≤ Vball 2 l := by
      intro x hx
      rw [mem_conjSub] at hx
      set v := c⁻¹ * x * c with hv
      have hvU : v ∈ Vball 3 β := Vball_le_Vball_of_mem_nbrs hl hx
      have h1 := hVl (hsec c hc hc5 v hvU)
      have e : x = (c * v * c⁻¹ * v⁻¹) * v := by rw [hv]; group
      rw [e]
      exact (Vball 2 l).mul_mem h1 hx
    have heq : conjSub c (Vball 2 l) = Vball 2 l :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub_eq'])
    exact mem_normalizer_of_conjSub_eq heq
  have hβα : α ∈ nbrs β := mem_nbrs_symm hαβ
  have hall : ∀ l ∈ nbrs β, Vball 2 l = Vball 2 α := by
    intro l hl
    obtain ⟨g, hg, hgl⟩ := exists_zpow_smul_nbr F hβ hc hcQ hc5' hβα hl
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgn : (g : G) ∈ Subgroup.normalizer (Vball 2 α : Set G) := by
      rw [← hi]; exact Subgroup.zpow_mem _ (hnorm α hβα) i
    rw [← hgl, Vball_smul]
    exact F7.conjSub_eq_of_mem_normalizer hgn
  have hnβ : stab β ≤ Subgroup.normalizer (Vball 2 α : Set G) := by
    intro g hg
    obtain ⟨hG0, hfix⟩ := mem_stab.mp hg
    have hgα : (⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • α ∈ nbrs β := by
      have := (smul_adj (⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S))).mpr
        (show (graph _ _ _).Adj β α from hβα)
      rwa [hfix] at this
    have e := Vball_smul (⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) 2 α
    rw [hall _ hgα] at e
    exact mem_normalizer_of_conjSub_eq e.symm
  have hQα : Vball 2 α ≤ Qv α := hA.Vball_le_Qv (by rw [CosetGeom.dist_self]; omega)
  have hU : Vball 2 α ≤ stab α ⊓ stab β :=
    le_inf (hQα.trans (pCoreOf_le 2 _)) (hQα.trans (hA.Qv_le_stab_of_mem_nbrs hαβ))
  have hbot := hA.eq_bot_of_normalizes_both (show (graph _ _ _).Adj α β from hαβ) hU
    (stab_le_normalizer_Vball 2 α) hnβ
  apply hA.Zv_ne_bot α
  rw [eq_bot_iff, ← hbot]
  exact Zv_le_Vball (by rw [CosetGeom.dist_self]; omega)

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
  (hb7 : 7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
  (hF1 : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → ∀ d ∈ nbrs x, ∀ d' ∈ nbrs x,
    d ≠ d' → Zv d ⊓ Zv d' = ⊥)
include F hT1 hc hII hb7 hF1

theorem caseII_T1_false_ge7_of {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : μ ∈ nbrs α')
    (hμβ : ¬ Zv μ ≤ Qv β)
    (hsec : ∀ t ∈ stab β, t ∉ Qv β → t ^ 2 = 1 → ∀ Y : Subgroup G, Y ≤ Vball 3 β →
      Y.relIndex (Vball 3 β) ≤ 2 → (∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ Vn β) →
      ∀ c ∈ stab β, c ^ 5 = 1 → ∀ u ∈ Vball 3 β, c * u * c⁻¹ * u⁻¹ ∈ Vn β) : False := by
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨t, htβ, htQ, ht2, Y, hYU, hYidx, hYt⟩ := exists_small_comm F hT1 hc hII hb7 hF1 hμ hμβ
  exact false_of_five_centralizes F (show β ∈ nbrs α from hc.adj) hβ (by omega)
    (hsec t htβ htQ ht2 Y hYU hYidx hYt)

end CaseII

end CFSG.Quasithin.Kleidman.F204
