module

public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.H13.NQS134EE

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace End134

variable (S : A6.Setting134 G T L V)
include S

theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have h1 := S.card_V
  rw [h, card_bot] at h1
  norm_num at h1

theorem isUniqueM_normalizer :
    IsUniqueM (normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G))
      (normalizer (L : Set G)) := by
  rw [U3.s134_cT S]
  have hLT : L ⊔ T ≤ normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← U3.s134_cT S]
    exact le_inf S.V_le_T (le_centralizer_self S)
  have hne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h => V_ne_bot S (le_bot_iff.mp (h ▸ hVO))
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 (L ⊔ T) : Set G)) :=
    ⟨pCoreOf 2 (L ⊔ T), hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T), rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := S.uniqueM.2 M' ⟨hM', hLT.trans hle⟩
  subst hM'eq
  exact ⟨⟨hM', hle⟩, fun M'' hM'' => S.uniqueM.2 M'' ⟨hM''.1, hLT.trans hM''.2⟩⟩

theorem hypE322 : HypE322 T V :=
  ⟨A5.isSylowTwoOf_of_le S.h13.sylow le_top, S.V_le_T, S.frame.T_le⟩

theorem rk_pos : 0 < rk ↥V := by
  unfold rk
  rw [S.card_V, show (32 : ℕ) = 2 ^ 5 by norm_num, padicValNat.prime_pow]
  norm_num

theorem mem_gammaSet_zero {X A : Subgroup G} (hA : A ∈ gammaSet V 0 X) :
    A ≤ X ∧ ∃ g : G, A = conjSub g V := by
  obtain ⟨hAX, g, hAg, h0⟩ := hA
  have hV2 : IsPGroup 2 V := isPGroup_of_isElemAbelian (U3.s134_elemAbelian_V S)
  have hAeq : A = conjSubgroup V g :=
    (mQuot_eq_zero_iff (isPGroup_conjSubgroup hV2 g) hAg).1 h0
  exact ⟨hAX, g⁻¹, hAeq⟩

theorem wClos_zero_le {X Y : Subgroup G} (h : ∀ g : G, conjSub g V ≤ X → conjSub g V ≤ Y) :
    wClos V 0 X ≤ Y := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAX, g, rfl⟩ := mem_gammaSet_zero S hA
  exact h g hAX

theorem exists_conj_not_le
    (hA : ∀ g : G, conjSub g V ≤ T → conjSub g V ≤ centralizer (V : Set G))
    {P Y : Subgroup G} (hTP : T ≤ P) (hPM : ¬ P ≤ normalizer (L : Set G)) (hYP : Y ≤ P)
    (hY2 : IsPGroup 2 Y) (hPY : P ≤ normalizer (Y : Set G)) :
    ∃ g : G, conjSub g V ≤ T ∧ ¬ conjSub g V ≤ Y := by
  by_contra h
  push Not at h
  have hW : wClos V 0 T ≤ Y := wClos_zero_le S h
  have hw : ((0 : ℕ) : ℕ∞) < wParam T V := by
    have h1 : ((1 : ℕ) : ℕ∞) ≤ wParam T V := le_wParam_of_wClos_le fun j hj => by
      obtain rfl : j = 0 := by omega
      exact wClos_zero_le S fun g hg => le_inf hg (hA g hg)
    exact lt_of_lt_of_le (by norm_num) h1
  have hN := (e3_34_two (U3.s134_elemAbelian_V S) (hypE322 S) (isUniqueM_normalizer S)
    (rk_pos S) hw).1
  have hS : IsSylowIn 2 T P := A5.isSylowTwoOf_of_le S.h13.sylow hTP
  have hNY := e3_15_normalizer hS hYP hY2 hW
  exact hPM (hPY.trans (hNY.trans hN))

end End134

end CFSG.Quasithin.H13.NQS134
