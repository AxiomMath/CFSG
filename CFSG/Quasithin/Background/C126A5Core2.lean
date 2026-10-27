module

public import CFSG.Quasithin.Background.C126A5Core1
public import CFSG.Quasithin.Background.C1GNBlockLemmas

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_isPGroup_two {K : Subgroup G} (h : IsPGroup 2 K) :
    Group.IsSolvable ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.isNilpotent
  infer_instance

namespace Setting

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setting H T M V Y hV)

include s

theorem R_le_normalizer : R₁ H T ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le s.Q_norm s.S_norm

theorem P₁_le : Y ⊔ R₁ H T ≤ H := sup_le s.Y_le (s.R_le_T.trans s.hT.1)

theorem R_le_P₁ : R₁ H T ≤ Y ⊔ R₁ H T := le_sup_right

theorem Y_le_P₁ : Y ≤ Y ⊔ R₁ H T := le_sup_left

theorem P₁_le_normalizer : Y ⊔ R₁ H T ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer s.R_le_normalizer

theorem card_P₁ : Nat.card ↥(Y ⊔ R₁ H T) * Nat.card ↥(Y ⊓ R₁ H T) =
    Nat.card Y * Nat.card (R₁ H T) :=
  card_sup_mul_card_inf_of_le_normalizer s.R_le_normalizer

theorem relIndex_R_P₁ : (R₁ H T).relIndex (Y ⊔ R₁ H T) = 3 := by
  have h1 := Subgroup.relIndex_mul_card (R₁ H T) (Y ⊔ R₁ H T)
  rw [inf_eq_left.2 s.R_le_P₁] at h1
  have h2 := s.card_P₁
  have h3 := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 H) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 H ≤ Y), s.relIndex_Y] at h3
  rw [s.Y_inf_R] at h2
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 H) := Nat.card_pos
  have hposR : 0 < Nat.card (R₁ H T) := Nat.card_pos
  have : (R₁ H T).relIndex (Y ⊔ R₁ H T) * (Nat.card (R₁ H T) * Nat.card ↥(Y ⊓ pCoreOf 2 H)) =
      3 * (Nat.card (R₁ H T) * Nat.card ↥(Y ⊓ pCoreOf 2 H)) := by
    calc _ = Nat.card ↥(Y ⊔ R₁ H T) * Nat.card ↥(Y ⊓ pCoreOf 2 H) := by rw [← h1]; ring
      _ = Nat.card Y * Nat.card (R₁ H T) := h2
      _ = _ := by rw [← h3]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposR hpos) this

theorem sylow_P₁ : IsSylowTwoOf (R₁ H T) (Y ⊔ R₁ H T) := by
  refine ⟨s.R_le_P₁, s.R_pGroup, ?_⟩
  have : ((R₁ H T).subgroupOf (Y ⊔ R₁ H T)).index = 3 := s.relIndex_R_P₁
  rw [this]
  omega

theorem sandwich_P₁ {K : Subgroup G} (h1 : R₁ H T ≤ K) (h2 : K ≤ Y ⊔ R₁ H T) :
    K = R₁ H T ∨ K = Y ⊔ R₁ H T := by
  have hYK : Y ⊓ pCoreOf 2 H ≤ K ⊓ Y :=
    le_inf ((inf_le_right.trans s.Q_le_R).trans h1) inf_le_left
  rcases s.sandwich_Y hYK inf_le_right with h | h
  · left
    refine le_antisymm (fun k hk => ?_) h1
    have hk' : k ∈ ((Y ⊔ R₁ H T : Subgroup G) : Set G) := h2 hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y (R₁ H T) s.R_le_normalizer] at hk'
    obtain ⟨y, hy, r, hr, rfl⟩ := hk'
    have hyK : y ∈ K ⊓ Y := ⟨by simpa using K.mul_mem hk (K.inv_mem (h1 hr)), hy⟩
    rw [h] at hyK
    exact (R₁ H T).mul_mem (s.Q_le_R hyK.2) hr
  · right
    exact le_antisymm h2 (sup_le (inf_eq_right.1 h) h1)

theorem not_Y_le_normalizer_baum : ¬ Y ≤ Subgroup.normalizer (baum T : Set G) := by
  intro hY
  have hT : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hH : H ≤ Subgroup.normalizer (baum T : Set G) := s.gen ▸ sup_le hY hT
  have hS : baum T ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (s.S_le_T.trans s.hT.1) hH (s.hT.2.1.to_le s.S_le_T)
  exact s.hJ ((B6.thompsonJ_le_baum T).trans (hS.trans s.Q_le_C))

theorem not_P₁_le_normalizer : ¬ Y ⊔ R₁ H T ≤ Subgroup.normalizer (R₁ H T : Set G) := by
  intro h
  apply s.not_Y_le_normalizer_baum
  have h1 : Y ≤ Subgroup.normalizer (R₁ H T : Set G) := s.Y_le_P₁.trans h
  intro y hy
  have := normalizer_le_normalizer_baum (R₁ H T) (h1 hy)
  rwa [s.baum_R] at this

theorem R_lt_P₁ : R₁ H T < Y ⊔ R₁ H T := by
  refine lt_of_le_of_ne s.R_le_P₁ fun h => s.not_P₁_le_normalizer ?_
  rw [← h]
  exact Subgroup.le_normalizer

theorem minParabolic_P₁ : MinParabolic (Y ⊔ R₁ H T) (R₁ H T) (R₁ H T) where
  isSylow := s.sylow_P₁
  not_normal := s.not_P₁_le_normalizer
  uniqueMax := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨⟨s.R_lt_P₁, fun K hK hKP => ?_⟩, le_rfl⟩, ?_⟩
    · rcases s.sandwich_P₁ hK.le hKP with h | h
      · exact absurd h hK.ne'
      · exact h
    · rintro N ⟨⟨hlt, _⟩, hRN⟩
      rcases s.sandwich_P₁ hRN hlt.le with h | h
      · exact h
      · exact absurd h hlt.ne

theorem Y_not_mem_Q {x : G} (hx3 : orderOf x = 3) : x ∉ pCoreOf 2 H := by
  intro hx
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hx⟩
  have h1 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h1
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
  omega

theorem Y_eq_sup {x : G} (hx : x ∈ Y) (hx3 : orderOf x = 3) :
    Y = (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x := by
  have hle : (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x ≤ Y :=
    sup_le inf_le_left ((Subgroup.zpowers_le).2 hx)
  rcases s.sandwich_Y le_sup_left hle with h | h
  · exfalso
    apply s.Y_not_mem_Q hx3
    have : x ∈ (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [h] at this
    exact this.2
  · exact h.symm

theorem isSolvable_Y : Group.IsSolvable ↥Y := by
  obtain ⟨x, hxY, hx3⟩ := s.exists_order_three
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hxY, le_normalizer_pCoreOf 2 H (s.Y_le hxY)⟩
  have h2 : Group.IsSolvable ↥(Y ⊓ pCoreOf 2 H) :=
    isSolvable_of_isPGroup_two ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  have h3 : Group.IsSolvable ↥(Subgroup.zpowers x) := inferInstance
  rw [s.Y_eq_sup hxY hx3]
  exact A3.isSolvable_sup_of_le_normalizer hN

theorem isSolvable_P₁ : Group.IsSolvable ↥(Y ⊔ R₁ H T) := by
  have h1 := s.isSolvable_Y
  have h2 := isSolvable_of_isPGroup_two s.R_pGroup
  exact A3.isSolvable_sup_of_le_normalizer s.R_le_normalizer

theorem charTwo_P₁ : CharTwo (Y ⊔ R₁ H T) :=
  charTwo_of_pCore_le s.charTwo (s.Q_le_R.trans s.R_le_P₁) s.P₁_le

theorem sqtk_P₁ : IsSQTKTC (Y ⊔ R₁ H T) := C1GN.IsSQTKTC.mono s.P₁_le s.sqtk

theorem twoResidual_P₁ : twoResidual (Y ⊔ R₁ H T) = Y := by
  refine le_antisymm (twoResidual_le_of_isTwoQuotient s.Y_le_P₁ s.P₁_le_normalizer
    (isTwoQuotient_of_sup_eq s.R_pGroup s.P₁_le_normalizer (sup_comm _ _))) ?_
  have := twoResidual_mono s.Y_le_P₁
  rwa [s.Y_res] at this

end Setting

end CFSG.Quasithin.C126.A5
