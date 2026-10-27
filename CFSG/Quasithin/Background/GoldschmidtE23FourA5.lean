module

public import CFSG.Quasithin.Background.GoldschmidtE23FourL2
public import CFSG.Quasithin.Background.GoldschmidtE23FourES
public import CFSG.Quasithin.Background.GoldschmidtE23FourBlk
public import CFSG.Quasithin.Background.GoldschmidtE23FourVZ
public import CFSG.Quasithin.Background.C126RadFree
public import CFSG.Quasithin.Background.C126A5Extract
public import CFSG.Quasithin.Background.C126A5Lift10

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {G : Type} [Group G] [Finite G]

theorem exists_chi0Block_of_oneBlock {H T : Subgroup G} (h : C126.OneBlock H T) :
    ∃ L : Subgroup G, IsChi0Block H L ∧ H = L ⊔ T ∧ (¬ IsAltType L 3 → L ∈ cComp H) := by
  obtain ⟨K, hK, -, hH⟩ := h
  have hKH : K ≤ H := hK.1.2.1
  have hTH : T ≤ H := by
    rw [hH]
    exact le_sup_left
  refine ⟨K, hK, le_antisymm ?_ (sup_le hKH hTH), fun h3 => ?_⟩
  · calc H = T ⊔ conjClosure K T := hH
      _ ≤ T ⊔ (K ⊔ T) := sup_le_sup_left (A3.conjClosure_le_sup K T) T
      _ = K ⊔ T := by rw [sup_comm K T, ← sup_assoc, sup_idem]
  · refine L238.mem_cComp_of_isChi0Block_nonsolvable hK.1 ?_
    rcases hK.2 with h | h | h
    · exact Or.inl h
    · exact absurd h h3
    · exact Or.inr h

theorem oneBlock_of_a5Case (h129 : ASC129Statement G) {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hmin : MinParabolic H T M) (hSQ : IsSQTKTC H) (hF : CharTwo H)
    (hred : IsTwoReducedIn H V) (hVZ : V = VZ T H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    (hA5 : C126.A5Case H T V hV)
    (hPU : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set G)) : C126.OneBlock H T := by
  obtain ⟨Y, s, ⟨d⟩⟩ := C126.A5.exists_setting_data hV hmin hSQ hF hred hVZ hJ hRad hA5
  obtain ⟨hY, hA3⟩ := isShort2_and_isAltType_three_Y h129 s hPU
  obtain ⟨x, hxY, hx3, hxL, hxth⟩ := C126.A5.Lift.exists_x (s := s) (d := d)
  exact C126.A5.Lift.XData.oneBlock (s := s) (d := d) ⟨hxY, hx3, hxL, hxth⟩ hY hA3 hRad

theorem e23FourA5Statement_of (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (he23 : E23Statement) (hRF : C126.RadFreeStmt) : E23FourA5Statement := by
  intro Γ _ _ H T M V hV hmin hsq hF hred hJ hA5 hPU
  have hJZ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set Γ) := fun h =>
    not_le_centralizer_VZ_of_a5Case hV hmin hred hJ hA5
      (le_centralizer_VZ_of_thompsonJ_le hmin hF hred hJ h)
  have hredZ : IsTwoReducedIn H (VZ T H) := C1GN.isTwoReducedIn_VZ hF hmin.isSylow
  have hVel : IsElemAbelian 2 (VZ T H) := hredZ.2.2.1
  have hc := he23 Γ H T M (VZ T H) hVel hmin hsq hF hredZ hJZ
  rcases sylow_baum_or_a5Case hVel hc with hSyl | hA5Z
  · exact exists_chi0Block_of_sylow_baum (h129 Γ) hmin hsq hF hPU hSyl
  · have hSQ : IsSQTKTC H := C1GN.isSQTKTC_iff_sqtkGroup.2 hsq
    have hRad := hRF Γ H T M (VZ T H) hVel hmin hSQ hF hredZ rfl hJZ (Or.inr hA5Z)
    exact exists_chi0Block_of_oneBlock
      (oneBlock_of_a5Case (h129 Γ) hVel hmin hSQ hF hredZ rfl hJZ hRad hA5Z hPU)

end E2

end CFSG.Quasithin
