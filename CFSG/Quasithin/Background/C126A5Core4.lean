module

public import CFSG.Quasithin.Background.C126A5Core3
public import CFSG.Quasithin.Background.C1PackC126Solv

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C1Pack

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setting H T M V Y hV)

include s

theorem S_le_normalizer : baum T ≤ Subgroup.normalizer (Y : Set G) := s.S_norm

theorem P₃_le : Y ⊔ baum T ≤ H := sup_le s.Y_le (s.S_le_T.trans s.hT.1)

theorem P₃_le_normalizer : Y ⊔ baum T ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer s.S_norm

theorem Y_inf_S : Y ⊓ baum T = Y ⊓ pCoreOf 2 H := by
  apply le_antisymm
  · exact le_inf inf_le_left ((inf_le_inf_left Y (s.S_le_T)).trans s.Y_inf_T)
  · have hn : Y ⊔ baum T ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · intro y hy
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 H (s.Y_le hy)⟩
      · intro x hx
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨s.S_norm hx, le_normalizer_pCoreOf 2 H (s.S_le_T.trans s.hT.1 hx)⟩
    have h1 := le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left) hn
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun x hx => ⟨hx.1, B6.pCoreOf_two_le_of_isSylowTwoOf s.sylow_S (h1 hx)⟩

theorem sandwich_P₃ {K : Subgroup G} (h1 : baum T ≤ K) (h2 : K ≤ Y ⊔ baum T) :
    K = baum T ∨ K = Y ⊔ baum T := by
  have hYK : Y ⊓ pCoreOf 2 H ≤ K ⊓ Y :=
    le_inf ((inf_le_inf_left Y le_rfl |>.trans (s.Y_inf_S.symm.le)).trans
      (inf_le_right.trans h1)) inf_le_left
  rcases s.sandwich_Y hYK inf_le_right with h | h
  · left
    refine le_antisymm (fun k hk => ?_) h1
    have hk' : k ∈ ((Y ⊔ baum T : Subgroup G) : Set G) := h2 hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y (baum T) s.S_norm] at hk'
    obtain ⟨y, hy, r, hr, rfl⟩ := hk'
    have hyK : y ∈ K ⊓ Y := ⟨by simpa using K.mul_mem hk (K.inv_mem (h1 hr)), hy⟩
    rw [h] at hyK
    refine (baum T).mul_mem ?_ hr
    rw [← s.Y_inf_S] at hyK
    exact hyK.2
  · right
    exact le_antisymm h2 (sup_le (inf_eq_right.1 h) h1)

theorem relIndex_S_P₃ : (baum T).relIndex (Y ⊔ baum T) = 3 := by
  have h1 := Subgroup.relIndex_mul_card (baum T) (Y ⊔ baum T)
  rw [inf_eq_left.2 le_sup_right] at h1
  have h2 := card_sup_mul_card_inf_of_le_normalizer s.S_norm
  have h3 := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 H) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 H ≤ Y), s.relIndex_Y] at h3
  rw [s.Y_inf_S] at h2
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 H) := Nat.card_pos
  have hposR : 0 < Nat.card (baum T) := Nat.card_pos
  have : (baum T).relIndex (Y ⊔ baum T) * (Nat.card (baum T) * Nat.card ↥(Y ⊓ pCoreOf 2 H)) =
      3 * (Nat.card (baum T) * Nat.card ↥(Y ⊓ pCoreOf 2 H)) := by
    calc _ = Nat.card ↥(Y ⊔ baum T) * Nat.card ↥(Y ⊓ pCoreOf 2 H) := by rw [← h1]; ring
      _ = Nat.card Y * Nat.card (baum T) := h2
      _ = _ := by rw [← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposR hpos) this

theorem S_lt_P₃ : baum T < Y ⊔ baum T := by
  refine lt_of_le_of_ne le_sup_right fun h => ?_
  have : (baum T).relIndex (Y ⊔ baum T) = 1 := by rw [← h]; exact Subgroup.relIndex_self _
  rw [s.relIndex_S_P₃] at this
  omega

theorem not_P₃_le_normalizer : ¬ Y ⊔ baum T ≤ Subgroup.normalizer (baum T : Set G) :=
  fun h => s.not_Y_le_normalizer_baum (le_sup_left.trans h)

theorem minParabolic_P₃ : MinParabolic (Y ⊔ baum T) (baum T) (baum T) where
  isSylow := s.sylow_S
  not_normal := s.not_P₃_le_normalizer
  uniqueMax := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨⟨s.S_lt_P₃, fun K hK hKP => ?_⟩, le_rfl⟩, ?_⟩
    · rcases s.sandwich_P₃ hK.le hKP with h | h
      · exact absurd h hK.ne'
      · exact h
    · rintro N ⟨⟨hlt, _⟩, hSN⟩
      rcases s.sandwich_P₃ hSN hlt.le with h | h
      · exact h
      · exact absurd h hlt.ne

theorem charTwo_P₃ : CharTwo (Y ⊔ baum T) := by
  have hY : CharTwo Y := A4.charTwo_of_normal s.Y_le_P₁
    (fun g hg => s.P₁_le_normalizer hg) s.charTwo_P₁
  exact A4.charTwo_sup hY s.S_norm (s.hT.2.1.to_le s.S_le_T)

theorem isSolvable_P₃ : Group.IsSolvable ↥(Y ⊔ baum T) := by
  have hle : Y ⊔ baum T ≤ Y ⊔ R₁ H T := sup_le_sup_left s.S_le_R Y
  have := s.isSolvable_P₁
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem sqtk_P₃ : IsSQTKTC (Y ⊔ baum T) := C1GN.IsSQTKTC.mono s.P₃_le s.sqtk

theorem P₃_sup_T : (Y ⊔ baum T) ⊔ T = H := by
  apply le_antisymm (sup_le s.P₃_le s.hT.1)
  rw [← s.gen]
  exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

theorem twoResidual_P₃ : twoResidual (Y ⊔ baum T) = Y := by
  have hn := s.P₃_le_normalizer
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left hn
    (isTwoQuotient_of_sup_eq (s.hT.2.1.to_le s.S_le_T) hn (sup_comm _ _))) ?_
  have := twoResidual_mono (le_sup_left : Y ≤ Y ⊔ baum T)
  rwa [s.Y_res] at this

theorem inClassG_P₃ : InClassG (Y ⊔ baum T) (baum T) := by
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) := by
    rw [← s.hVZ]; exact s.hJ
  have hJ' := not_thompsonJ_baum_le_centralizer s.min s.charTwo s.minParabolic_P₃ s.charTwo_P₃
    s.P₃_sup_T s.not_P₃_le_normalizer hJ
  exact inClassG_of_solvable_minParabolic s.minParabolic_P₃ s.charTwo_P₃ s.isSolvable_P₃
    (pRank_le_two_of_isSQTKTC s.sqtk_P₃) hJ' (C1GN.baum_baum T)

theorem dichotomy {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂) :
    C₁ T ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ T : Set G) ∨
      (IsBlock2 (Y ⊔ baum T) Y ∧ IsAltType Y 3) := by
  have hT := s.hT
  have hT0 : T ≠ ⊥ := minParabolic_ne_bot s.min
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair T hT.2.1 hT0
  rcases hC.dichotomy hT.2.1 hT0 s.inClassG_P₃ with h1 | h2 | h3
  · left
    intro c hc
    have hcT : c ∈ centerOf T := C1GN.omegaOneCenterOf_le_centerOf T (h1Z hc)
    have hHc : H ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [← s.gen]
      refine sup_le (fun y hy => ?_) (fun t ht => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_iff.1 (h1 hc).2 y (Subgroup.mem_sup_left hy)).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_iff.1 hcT.2 t ht).symm
    refine ⟨s.hT.1 hcT.1, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (hHc hg) c rfl).symm
  · right; left
    have hTN : T ≤ Subgroup.normalizer (C₂ T : Set G) :=
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)).trans
        (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
    rw [← s.gen]
    exact sup_le (le_sup_left.trans h2) hTN
  · right; right
    rw [s.twoResidual_P₃] at h3
    exact ⟨h3.1, isAltType_three_of_isBlock2_of_solvable h3.1 s.isSolvable_P₃⟩

end Setting

end CFSG.Quasithin.C126.A5
