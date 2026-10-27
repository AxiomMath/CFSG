module

public import CFSG.Quasithin.EmptyFaithful.S152He9U
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_right {D R : Subgroup G} (hR : R ≤ Subgroup.normalizer (D : Set G)) :
    R.relIndex (D ⊔ R) = (D ⊓ R).relIndex D := by
  set Q := D ⊔ R with hQ
  set I := D ⊓ R with hI
  have h1 : D.relIndex (R ⊔ D) = D.relIndex R := F1.relIndex_sup_eq_of_le_normalizer hR
  rw [sup_comm] at h1
  have h2 : I.relIndex R = D.relIndex R := Subgroup.inf_relIndex_right D R
  have hm1 := Subgroup.relIndex_mul_relIndex I R Q inf_le_right le_sup_right
  have hm2 := Subgroup.relIndex_mul_relIndex I D Q inf_le_left le_sup_left
  have hne : D.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h2, ← h1] at hm1
  have : D.relIndex Q * R.relIndex Q = D.relIndex Q * I.relIndex D := by
    rw [hm1, mul_comm (D.relIndex Q) (I.relIndex D)]
    exact hm2.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem exists_Lc (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥) (hS : IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁)) :
    ∃ Lc ∈ cComp (g0Of T Mc M K₁), K₁ ≤ Lc ∧ (Lc.subgroupOf (g0Of T Mc M K₁)).Normal := by
  have hK := c.hs.qtfe
  have hB : K₁ ∈ lFamily (sOf T K₁) :=
    cComp_mem_of_le c.wr.comp₁ le_sup_left (sup_le c.wr.le₁ (S_le_T.trans c.hT.1))
  obtain ⟨Lc, hLc, hKL⟩ := lemma_1_2_4_exists hK.qtke hK.simple hK.nonabelian h37 h39 hne hS
    K₁_le_G₀ hB
  exact ⟨Lc, hLc, hKL, lemma_1_2_4_normal hK.qtke hK.simple hK.nonabelian h37 h38 hne hS hB hKL hLc
    S_le_normalizer_K₁⟩

theorem S_le_M₁ : sOf T K₁ ≤ M ⊓ g0Of T Mc M K₁ := le_inf c.S_le_M S_le_G₀

theorem charTwo_M₁ : CharTwo (M ⊓ g0Of T Mc M K₁) := by
  have hM : CharTwo M := c.charTwo_M
  have hTM : IsSylowTwoOf T M := isSylowTwoOf_of_le151 c.hs.qtfe.sylow c.y.data.T_le
  refine charTwo_of_relIndex_le_two hM hTM inf_le_left ?_
  have h1 : (M ⊓ g0Of T Mc M K₁).relIndex T ∣ (sOf T K₁).relIndex T :=
    Subgroup.relIndex_dvd_of_le_left T c.S_le_M₁
  have h2 : (sOf T K₁).relIndex T = 2 := c.wr.relIndex_S c.hT
  rw [h2] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem g0_eq {Lc : Subgroup G} (hK : K₁ ≤ Lc) (hL : Lc ≤ g0Of T Mc M K₁) :
    g0Of T Mc M K₁ = Lc ⊔ (M ⊓ g0Of T Mc M K₁) := by
  apply le_antisymm
  · refine sup_le (sup_le (sup_le ?_ ?_) (hK.trans le_sup_left)) ?_
    · exact le_sup_of_le_right (le_inf c.y.hYM Y_le_G₀)
    · exact le_sup_of_le_right (le_inf c.y.hRM rc_le_G₀)
    · exact le_sup_of_le_right c.S_le_M₁
  · exact sup_le hL inf_le_right

theorem not_Lc_le_M {Lc : Subgroup G} (hK : K₁ ≤ Lc) : ¬ Lc ≤ M ⊓ g0Of T Mc M K₁ :=
  fun h => c.not_K₁_le_M (hK.trans (h.trans inf_le_left))

end Ctx15204

end CFSG.Quasithin.He9
