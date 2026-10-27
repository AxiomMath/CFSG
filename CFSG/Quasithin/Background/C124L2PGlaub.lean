module

public import CFSG.Quasithin.Background.C124L2PBasic
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.C124L2PMP
public import CFSG.Quasithin.Background.C1GNA7Base

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.L2P

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5 E2
open CFSG.Quasithin.C124.L2 (R₂ card_sl2_four)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable {X R Y V : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setup X R Y V hV)

include s

theorem twoResidual_P₁ : twoResidual (Y ⊔ R₂ X R Y) = Y := by
  have hn : Y ⊔ R₂ X R Y ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer s.R₂_le_normalizer
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left hn
    (isTwoQuotient_of_sup_eq s.R₂_pGroup hn (sup_comm _ _))) ?_
  have := twoResidual_mono (le_sup_left : Y ≤ Y ⊔ R₂ X R Y)
  rwa [s.Y_res] at this

theorem not_Y_le_normalizer_R₂ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ¬ Y ≤ Subgroup.normalizer (R₂ X R Y : Set G) := by
  intro h
  apply hYS
  intro y hy
  have := normalizer_le_normalizer_baum (R₂ X R Y) (h hy)
  rwa [s.baum_R₂] at this

theorem minParabolic_P₁ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ∃ M : Subgroup G, MinParabolic (Y ⊔ R₂ X R Y) (R₂ X R Y) M := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := s.sl2
  exact minParabolic_of_sl2_perf hV s.hYN s.hR₂N s.R₂_pGroup s.R₂_le_normalizer
    (by rw [s.R₂_inf_Y]; exact s.RY_syl) s.Y_perf s.Y_inf_C_le_R₂ hF e
    (s.not_Y_le_normalizer_R₂ hYS)

theorem sylow_S (hE23 : E2.E23Statement) (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    IsSylowTwoOf (baum R) (Y ⊔ baum R) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := s.sl2
  obtain ⟨M, hM⟩ := s.minParabolic_P₁ hYS
  have hJ' : ¬ thompsonJ (R₂ X R Y) ≤ Subgroup.centralizer (V : Set G) := by
    rw [s.thompsonJ_R₂]
    exact s.hJ
  have hc := hE23 G (Y ⊔ R₂ X R Y) (R₂ X R Y) M V hV hM
    (C1GN.isSQTKTC_iff_sqtkGroup.1 s.sqtk_P₁) s.charTwo_P₁ (s.red_P₁ F hF e) hJ'
  obtain ⟨-, I, -, hJeq, -, -, -, htype, -, -, h2, -⟩ := hc
  have hnat : ∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual (Y ⊔ R₂ X R Y)))) n := by
    intro L hL
    rcases htype L hL with h | h
    · exact h
    · exfalso
      obtain ⟨θ, -⟩ := h
      have hLle : L ≤ autI hV Y := by
        have h1 : L ≤ ⨆ L' ∈ I, L' := le_iSup₂_of_le L hL le_rfl
        rw [← hJeq] at h1
        exact h1.trans (s.autI_P₁ ▸ autI_mono hV (B6.thompsonJ_le _))
      have hc120 : Nat.card L = 120 := by
        rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
        rfl
      have h60 : Nat.card ↥(autI hV Y) = 60 := by
        rw [Nat.card_congr e.toEquiv, card_sl2_four hF]
      have := Subgroup.card_le_of_le hLle
      omega
  obtain ⟨-, -, hsyl, -⟩ := h2 hnat
  rwa [s.baum_R₂, s.twoResidual_P₁] at hsyl

theorem sylow_S_inf_Y (hE23 : E2.E23Statement) (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    IsSylowTwoOf (baum R ⊓ Y) Y :=
  B6.isSylowTwoOf_inf_normal (s.sylow_S hE23 hYS) le_sup_left
    (sup_le Subgroup.le_normalizer s.S_norm)

theorem Y_inf_C_le_S (hE23 : E2.E23Statement) (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ⁅Y ⊓ Subgroup.centralizer (V : Set G), Y⁆ ≤ baum R := by
  have hn1 : Y ≤ Subgroup.normalizer
      ((Y ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer s.hYN hy⟩
  have hn : Y ≤ Subgroup.normalizer
      ((⁅Y ⊓ Subgroup.centralizer (V : Set G), Y⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator' hn1 Subgroup.le_normalizer
  have hle : ⁅Y ⊓ Subgroup.centralizer (V : Set G), Y⁆ ≤ Y :=
    Subgroup.commutator_le.2 fun a ha b hb =>
      Y.mul_mem (Y.mul_mem (Y.mul_mem ha.1 hb) (Y.inv_mem ha.1)) (Y.inv_mem hb)
  have h1 := le_pCoreOf_of_le_normalizer 2 hle hn ((pCoreOf_isPGroup 2 X).to_le s.Y_C)
  exact fun x hx => (B6.pCoreOf_two_le_of_isSylowTwoOf (s.sylow_S_inf_Y hE23 hYS) (h1 hx)).1

theorem minParabolic_P₃ (hE23 : E2.E23Statement)
    (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ∃ M : Subgroup G, MinParabolic (Y ⊔ baum R) (baum R) M := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := s.sl2
  exact minParabolic_of_sl2_perf hV s.hYN (s.S_le_X.trans s.hVN) (s.R_pGroup.to_le s.S_le_R)
    s.S_norm (s.sylow_S_inf_Y hE23 hYS) s.Y_perf (s.Y_inf_C_le_S hE23 hYS) hF e hYS

end Setup

end CFSG.Quasithin.C124.L2P
