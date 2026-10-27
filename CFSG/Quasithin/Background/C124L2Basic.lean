module

public import CFSG.Quasithin.Background.C124L2MP
public import CFSG.Quasithin.Background.C124B2102
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.C1GNBlockLemmas

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.L2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def R₂ (X R Y : Subgroup G) : Subgroup G := pCoreOf 2 X ⊔ baum R ⊔ (R ⊓ Y)

structure Setup (X R Y V : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  charTwo : CharTwo X
  sqtk : IsSQTKTC X
  red : IsTwoReducedIn X V
  R_le : R ≤ X
  R_pGroup : IsPGroup 2 R
  Q_le : pCoreOf 2 X ≤ R
  hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)
  Y_le : Y ≤ X
  Y_res : twoResidual Y = Y
  Q_norm : pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set G)
  S_norm : baum R ≤ Subgroup.normalizer (Y : Set G)
  Y_C : Y ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 X
  RY_syl : IsSylowTwoOf (R ⊓ Y) Y
  S_star : autI hV (baum R) ≤ autI hV Y
  Y_not_C : ¬ Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter (baum R) : Set G)
  sl2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥(autI hV Y) ≃* SL(2, F))

namespace Setup

variable {X R Y V : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setup X R Y V hV)

include s

theorem S_le_R : baum R ≤ R := inf_le_left

theorem Q_le_X : pCoreOf 2 X ≤ X := CFSG.openPCoreOf_le 2 X

theorem S_le_X : baum R ≤ X := s.S_le_R.trans s.R_le

theorem RY_le_X : R ⊓ Y ≤ X := inf_le_left.trans s.R_le

theorem R₂_le_R : R₂ X R Y ≤ R := sup_le (sup_le s.Q_le s.S_le_R) inf_le_left

theorem R₂_pGroup : IsPGroup 2 (R₂ X R Y) := s.R_pGroup.to_le s.R₂_le_R

theorem Q_le_R₂ : pCoreOf 2 X ≤ R₂ X R Y := le_sup_left.trans le_sup_left

theorem S_le_R₂ : baum R ≤ R₂ X R Y := le_sup_right.trans le_sup_left

theorem RY_le_R₂ : R ⊓ Y ≤ R₂ X R Y := le_sup_right

theorem R₂_le_X : R₂ X R Y ≤ X := s.R₂_le_R.trans s.R_le

theorem R₂_le_normalizer : R₂ X R Y ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le (sup_le s.Q_norm s.S_norm) (inf_le_right.trans Subgroup.le_normalizer)

theorem P₁_le : Y ⊔ R₂ X R Y ≤ X := sup_le s.Y_le s.R₂_le_X

theorem hVN : X ≤ Subgroup.normalizer (V : Set G) := s.red.2.1

theorem hYN : Y ≤ Subgroup.normalizer (V : Set G) := s.Y_le.trans s.hVN

theorem hR₂N : R₂ X R Y ≤ Subgroup.normalizer (V : Set G) := s.R₂_le_X.trans s.hVN

theorem thompsonJ_R₂ : thompsonJ (R₂ X R Y) = thompsonJ R :=
  B6.thompsonJ_eq_of_le ((B6.thompsonJ_le_baum R).trans s.S_le_R₂) s.R₂_le_R

theorem baum_R₂ : baum (R₂ X R Y) = baum R := by
  ext x
  unfold baum
  rw [s.thompsonJ_R₂]
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨s.R₂_le_R h.1, h.2⟩, fun h => ⟨s.S_le_R₂ (by
    simpa [baum] using h), h.2⟩⟩

theorem R₂_inf_Y : R₂ X R Y ⊓ Y = R ⊓ Y :=
  le_antisymm (inf_le_inf_right Y s.R₂_le_R) (le_inf s.RY_le_R₂ inf_le_right)

theorem sylow_R₂ : IsSylowTwoOf (R₂ X R Y) (Y ⊔ R₂ X R Y) := by
  refine isSylowTwoOf_sup_of_normalizing s.R₂_le_normalizer s.R₂_pGroup ?_
  rw [s.R₂_inf_Y]
  exact s.RY_syl

theorem Y_inf_C_le_R₂ : Y ⊓ Subgroup.centralizer (V : Set G) ≤ R₂ X R Y :=
  s.Y_C.trans s.Q_le_R₂

theorem autI_Q : autI hV (pCoreOf 2 X) = ⊥ :=
  autI_eq_bot_of_le_centralizer hV (pCoreOf_le_centralizer s.red)

theorem autI_R₂_le : autI hV (R₂ X R Y) ≤ autI hV Y := by
  have hQ := s.Q_le_X.trans s.hVN
  have hS := s.S_le_X.trans s.hVN
  have hRY := s.RY_le_X.trans s.hVN
  unfold R₂
  rw [autI_sup hV (sup_le hQ hS) hRY, autI_sup hV hQ hS, s.autI_Q, bot_sup_eq]
  exact sup_le s.S_star (autI_mono hV inf_le_right)

theorem autI_P₁ : autI hV (Y ⊔ R₂ X R Y) = autI hV Y := by
  rw [autI_sup hV s.hYN s.hR₂N]
  exact sup_eq_left.2 s.autI_R₂_le

theorem charTwo_P₁ : CharTwo (Y ⊔ R₂ X R Y) :=
  charTwo_of_pCore_le s.charTwo (s.Q_le_R₂.trans le_sup_right) s.P₁_le

theorem sqtk_P₁ : IsSQTKTC (Y ⊔ R₂ X R Y) := C1GN.IsSQTKTC.mono s.P₁_le s.sqtk

theorem V_le_R₂ : V ≤ R₂ X R Y :=
  (le_pCoreOf_of_reduced s.red).trans s.Q_le_R₂

theorem red_P₁ (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : ↥(autI hV Y) ≃* SL(2, F)) : IsTwoReducedIn (Y ⊔ R₂ X R Y) V := by
  refine ⟨s.V_le_R₂.trans le_sup_right, sup_le s.hYN s.hR₂N, hV, ?_⟩
  intro D hDP hDn hD2
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hF4
  have hsimple : IsSimpleGroup SL(2, F) := C126.Nat.isSimpleGroup_sl2 (by omega)
  have hsY : IsSimpleGroup ↥(autI hV Y) := e.isSimpleGroup
  have hPN : Y ⊔ R₂ X R Y ≤ Subgroup.normalizer (V : Set G) := sup_le s.hYN s.hR₂N
  have hDY : autI hV D ≤ autI hV Y := s.autI_P₁ ▸ autI_mono hV hDP
  have hDN : autI hV Y ≤ Subgroup.normalizer (autI hV D : Set (MulAut (IntMod V hV))) :=
    s.autI_P₁ ▸ autI_le_normalizer_of_le_normalizer hV hDn
  have hNorm : ((autI hV D).subgroupOf (autI hV Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).2 hDN
  have hD2' : IsPGroup 2 (autI hV D) := by
    intro ⟨φ, hφ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨k, hk⟩ := hD2 g hg
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : convI hV (g ^ 2 ^ k) = 1 := (convI_eq_one_iff hV _).2 hk
    simpa [map_pow] using h1
  have h60 : Nat.card ↥(autI hV Y) = 60 := by
    rw [Nat.card_congr e.toEquiv, card_sl2_four hF]
  have hbot : (autI hV D).subgroupOf (autI hV Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((autI hV D).subgroupOf (autI hV Y)) with h | h
    · exact h
    · exfalso
      have hle : autI hV Y ≤ autI hV D := Subgroup.subgroupOf_eq_top.1 h
      have hp : IsPGroup 2 ↥(autI hV Y) := hD2'.to_le hle
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hp
      rw [h60] at ha
      have : (60 : ℕ) = 2 ^ a := ha
      have h3 : 3 ∣ 2 ^ a := this ▸ (by norm_num : 3 ∣ 60)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have : autI hV D = ⊥ := by
    refine eq_bot_iff.2 fun φ hφ => ?_
    have hφ' : (⟨φ, hDY hφ⟩ : ↥(autI hV Y)) ∈ (autI hV D).subgroupOf (autI hV Y) := hφ
    rw [hbot, Subgroup.mem_bot] at hφ'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hφ')
  exact (autI_eq_bot_iff hV (hDP.trans hPN)).1 this

end Setup

end CFSG.Quasithin.C124.L2
