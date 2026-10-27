module

public import CFSG.Quasithin.Background.C124Z3Min
public import CFSG.Quasithin.Background.C1PackSubnormal
public import CFSG.Quasithin.Background.E2SolvTwo

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.Z3

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5 CFSG.Quasithin.C1Pack

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable {X R Y : Subgroup G} (s : Setup X R Y)

include s

theorem hJ_V₁ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ¬ thompsonJ (R₁ X R) ≤
      Subgroup.centralizer (VZ (R₁ X R) (Y ⊔ R₁ X R) : Set G) := by
  intro hJR
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo s.sylow_P₁ s.charTwo_P₁
    (Z := quasithinOmegaOneCenter (R₁ X R)) le_rfl
  by_cases hP : Y ⊔ R₁ X R ≤ Subgroup.centralizer (VZ (R₁ X R) (Y ⊔ R₁ X R) : Set G)
  · apply s.Y_not_C
    have hZV : quasithinOmegaOneCenter (R₁ X R) ≤ VZ (R₁ X R) (Y ⊔ R₁ X R) :=
      le_conjClosure _ _
    exact le_sup_left.trans (hP.trans (Subgroup.centralizer_le hZV))
  · have htfae := MinParabolic.tfae_thompsonJ (s.minParabolic_P₁ hYS) hred hP
    have h1 : ⁅VZ (R₁ X R) (Y ⊔ R₁ X R), thompsonJ (R₁ X R)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJR
    have h3 : baum (R₁ X R) = baum (pCoreOf 2 (Y ⊔ R₁ X R)) := (htfae.out 1 3).1 h1
    apply hYS
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (pCoreOf 2 (Y ⊔ R₁ X R) : Set G) :=
      le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hy)
    have := normalizer_le_normalizer_baum _ hyN
    rwa [← h3, s.baum_R₁] at this

theorem sylow_S (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    IsSylowTwoOf (baum R) (Y ⊔ baum R) := by
  obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo s.sylow_P₁ s.charTwo_P₁
    (Z := quasithinOmegaOneCenter (R₁ X R)) le_rfl
  obtain ⟨-, -, h3, -⟩ := E2_3_two_of_isSolvable hel (s.minParabolic_P₁ hYS) s.isSolvable_P₁
    s.pRank_le_two_P₁ hred (s.hJ_V₁ hYS)
  rwa [s.baum_R₁, s.twoResidual_P₁] at h3

theorem P₃_le_normalizer : Y ⊔ baum R ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer s.S_norm

theorem P₃_le_P₁ : Y ⊔ baum R ≤ Y ⊔ R₁ X R := sup_le_sup_left s.S_le_R₁ Y

theorem Y_inf_S (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    Y ⊓ baum R = Y ⊓ pCoreOf 2 X := by
  apply le_antisymm
  · rw [← s.Y_inf_R₁]
    exact inf_le_inf_left Y s.S_le_R₁
  · have hn : Y ⊔ baum R ≤
        Subgroup.normalizer ((Y ⊓ pCoreOf 2 X : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · intro y hy
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 X (s.Y_le hy)⟩
      · intro x hx
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨s.S_norm hx, le_normalizer_pCoreOf 2 X (s.R_le (s.S_le_R hx))⟩
    have h1 := le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left) hn
      ((pCoreOf_isPGroup 2 X).to_le inf_le_right)
    exact fun x hx => ⟨hx.1, B6.pCoreOf_two_le_of_isSylowTwoOf (s.sylow_S hYS) (h1 hx)⟩

theorem sandwich_P₃ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) {K : Subgroup G}
    (h1 : baum R ≤ K) (h2 : K ≤ Y ⊔ baum R) : K = baum R ∨ K = Y ⊔ baum R := by
  have hYK : Y ⊓ pCoreOf 2 X ≤ K ⊓ Y :=
    le_inf (((s.Y_inf_S hYS).symm.le).trans (inf_le_right.trans h1)) inf_le_left
  rcases s.sandwich_Y hYK inf_le_right with h | h
  · left
    refine le_antisymm (fun k hk => ?_) h1
    have hk' : k ∈ ((Y ⊔ baum R : Subgroup G) : Set G) := h2 hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Y (baum R) s.S_norm] at hk'
    obtain ⟨y, hy, r, hr, rfl⟩ := hk'
    have hyK : y ∈ K ⊓ Y := ⟨by simpa using K.mul_mem hk (K.inv_mem (h1 hr)), hy⟩
    rw [h] at hyK
    refine (baum R).mul_mem ?_ hr
    rw [← s.Y_inf_S hYS] at hyK
    exact hyK.2
  · right
    exact le_antisymm h2 (sup_le (inf_eq_right.1 h) h1)

theorem relIndex_S_P₃ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    (baum R).relIndex (Y ⊔ baum R) = 3 := by
  have h1 := Subgroup.relIndex_mul_card (baum R) (Y ⊔ baum R)
  rw [inf_eq_left.2 (le_sup_right : baum R ≤ Y ⊔ baum R)] at h1
  have h2 := card_sup_mul_card_inf_of_le_normalizer s.S_norm
  rw [s.Y_inf_S hYS] at h2
  have h3 := s.card_Y
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 X) := Nat.card_pos
  have hposR : 0 < Nat.card (baum R) := Nat.card_pos
  have : (baum R).relIndex (Y ⊔ baum R) *
      (Nat.card (baum R) * Nat.card ↥(Y ⊓ pCoreOf 2 X)) =
      3 * (Nat.card (baum R) * Nat.card ↥(Y ⊓ pCoreOf 2 X)) := by
    calc _ = Nat.card ↥(Y ⊔ baum R) * Nat.card ↥(Y ⊓ pCoreOf 2 X) := by rw [← h1]; ring
      _ = Nat.card Y * Nat.card (baum R) := h2
      _ = _ := by rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposR hpos) this

theorem S_lt_P₃ (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) : baum R < Y ⊔ baum R := by
  refine lt_of_le_of_ne le_sup_right fun h => ?_
  have : (baum R).relIndex (Y ⊔ baum R) = 1 := by rw [← h]; exact Subgroup.relIndex_self _
  rw [s.relIndex_S_P₃ hYS] at this
  omega

theorem not_P₃_le_normalizer (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ¬ Y ⊔ baum R ≤ Subgroup.normalizer (baum R : Set G) :=
  fun h => hYS (le_sup_left.trans h)

end Setup

end CFSG.Quasithin.C124.Z3
