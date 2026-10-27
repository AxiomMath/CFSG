module

public import CFSG.Quasithin.Background.C126A5Core1

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.Z3

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5

variable {G : Type} [Group G] [Finite G]

@[expose] def R₁ (X R : Subgroup G) : Subgroup G := pCoreOf 2 X ⊔ baum R

structure Setup (X R Y : Subgroup G) : Prop where
  charTwo : CharTwo X
  R_le : R ≤ X
  R_pGroup : IsPGroup 2 R
  Q_le : pCoreOf 2 X ≤ R
  Y_le : Y ≤ X
  Y_res : twoResidual Y = Y
  Y_index : (Y ⊓ pCoreOf 2 X).relIndex Y = 3
  Q_norm : pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set G)
  S_norm : baum R ≤ Subgroup.normalizer (Y : Set G)
  Y_not_C : ¬ Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter (R₁ X R) : Set G)

theorem eq_of_relIndex_three_of_isPGroup {N K Y : Subgroup G} (hNK : N ≤ K) (hKY : K ≤ Y)
    (h3 : N.relIndex Y = 3) (hK : IsPGroup 2 K) : K = N := by
  have h := Subgroup.relIndex_mul_relIndex N K Y hNK hKY
  rw [h3] at h
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hK N
  have hdvd : N.relIndex K ∣ 3 := Dvd.intro _ h
  rw [hn] at hdvd
  have hn0 : n = 0 := by
    by_contra hne
    have : 2 ∣ 3 := (dvd_pow_self 2 hne).trans hdvd
    omega
  rw [hn0, pow_zero] at hn
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hn) hNK

namespace Setup

variable {X R Y : Subgroup G} (s : Setup X R Y)

include s

theorem S_le_R : baum R ≤ R := inf_le_left

theorem R₁_le_R : R₁ X R ≤ R := sup_le s.Q_le s.S_le_R

theorem R₁_pGroup : IsPGroup 2 (R₁ X R) := s.R_pGroup.to_le s.R₁_le_R

theorem Q_le_R₁ : pCoreOf 2 X ≤ R₁ X R := le_sup_left

theorem S_le_R₁ : baum R ≤ R₁ X R := le_sup_right

theorem R₁_le_X : R₁ X R ≤ X := s.R₁_le_R.trans s.R_le

theorem R₁_le_normalizer : R₁ X R ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le s.Q_norm s.S_norm

theorem P₁_le : Y ⊔ R₁ X R ≤ X := sup_le s.Y_le s.R₁_le_X

theorem P₁_le_normalizer : Y ⊔ R₁ X R ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer s.R₁_le_normalizer

theorem thompsonJ_R₁ : thompsonJ (R₁ X R) = thompsonJ R :=
  B6.thompsonJ_eq_of_le ((B6.thompsonJ_le_baum R).trans s.S_le_R₁) s.R₁_le_R

theorem baum_R₁ : baum (R₁ X R) = baum R := by
  ext x
  unfold baum
  rw [s.thompsonJ_R₁]
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨s.R₁_le_R h.1, h.2⟩, fun h => ⟨s.S_le_R₁ (by
    simpa [baum] using h), h.2⟩⟩

theorem Y_inf_R₁ : Y ⊓ R₁ X R = Y ⊓ pCoreOf 2 X :=
  eq_of_relIndex_three_of_isPGroup (inf_le_inf_left Y s.Q_le_R₁) inf_le_left s.Y_index
    (s.R₁_pGroup.to_le inf_le_right)

theorem card_Y : Nat.card Y = 3 * Nat.card ↥(Y ⊓ pCoreOf 2 X) := by
  have h := Subgroup.relIndex_mul_card (Y ⊓ pCoreOf 2 X) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ pCoreOf 2 X ≤ Y), s.Y_index] at h
  exact h.symm

theorem sandwich_Y {K : Subgroup G} (h1 : Y ⊓ pCoreOf 2 X ≤ K) (h2 : K ≤ Y) :
    K = Y ⊓ pCoreOf 2 X ∨ K = Y := by
  have h := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [s.Y_index] at h
  have hdvd : (K.relIndex Y) ∣ 3 := Dvd.intro_left _ h
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1' | h3'
  · right
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.1 h1')
  · left
    rw [h3'] at h
    have : (Y ⊓ pCoreOf 2 X).relIndex K = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 this) h1

theorem relIndex_R₁_P₁ : (R₁ X R).relIndex (Y ⊔ R₁ X R) = 3 := by
  have h1 := Subgroup.relIndex_mul_card (R₁ X R) (Y ⊔ R₁ X R)
  rw [inf_eq_left.2 (le_sup_right : R₁ X R ≤ Y ⊔ R₁ X R)] at h1
  have h2 := card_sup_mul_card_inf_of_le_normalizer s.R₁_le_normalizer
  rw [s.Y_inf_R₁] at h2
  have h3 := s.card_Y
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 X) := Nat.card_pos
  have hposR : 0 < Nat.card (R₁ X R) := Nat.card_pos
  have : (R₁ X R).relIndex (Y ⊔ R₁ X R) *
      (Nat.card (R₁ X R) * Nat.card ↥(Y ⊓ pCoreOf 2 X)) =
      3 * (Nat.card (R₁ X R) * Nat.card ↥(Y ⊓ pCoreOf 2 X)) := by
    calc _ = Nat.card ↥(Y ⊔ R₁ X R) * Nat.card ↥(Y ⊓ pCoreOf 2 X) := by rw [← h1]; ring
      _ = Nat.card Y * Nat.card (R₁ X R) := h2
      _ = _ := by rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposR hpos) this

theorem sylow_P₁ : IsSylowTwoOf (R₁ X R) (Y ⊔ R₁ X R) := by
  refine ⟨le_sup_right, s.R₁_pGroup, ?_⟩
  have : ((R₁ X R).subgroupOf (Y ⊔ R₁ X R)).index = 3 := s.relIndex_R₁_P₁
  rw [this]
  omega

theorem sandwich_P₁ {K : Subgroup G} (h1 : R₁ X R ≤ K) (h2 : K ≤ Y ⊔ R₁ X R) :
    K = R₁ X R ∨ K = Y ⊔ R₁ X R := by
  have hYK : Y ⊓ pCoreOf 2 X ≤ K ⊓ Y :=
    le_inf ((inf_le_right.trans s.Q_le_R₁).trans h1) inf_le_left
  rcases s.sandwich_Y hYK inf_le_right with h | h
  · left
    refine le_antisymm (fun k hk => ?_) h1
    have hk' : k ∈ ((Y ⊔ R₁ X R : Subgroup G) : Set G) := h2 hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y (R₁ X R) s.R₁_le_normalizer] at hk'
    obtain ⟨y, hy, r, hr, rfl⟩ := hk'
    have hyK : y ∈ K ⊓ Y := ⟨by simpa using K.mul_mem hk (K.inv_mem (h1 hr)), hy⟩
    rw [h] at hyK
    exact (R₁ X R).mul_mem (s.Q_le_R₁ hyK.2) hr
  · right
    exact le_antisymm h2 (sup_le (inf_eq_right.1 h) h1)

end Setup

end CFSG.Quasithin.C124.Z3
