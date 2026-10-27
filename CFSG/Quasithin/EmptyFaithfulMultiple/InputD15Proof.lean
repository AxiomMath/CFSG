module

public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15
public import CFSG.Quasithin.Background.D15Four
public import CFSG.Quasithin.Background.D15Solv

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}

theorem d15ConclAS_of_d125' (h : D11Hyp G₁ G₂ T V M₂)
    (hD125 : IsElemAbelian 2 (conjClosure V G₂) → D15Proof.D125 G₂ T (conjClosure V G₂)) :
    D15ConclAS G₁ G₂ T V h.reduced.2.2.1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold D15ConclAS
  by_cases hVR₂ : V ≤ pCoreOf 2 G₂
  swap
  · exact Or.inl hVR₂
  by_cases hq1 : qInt G₁ V h.reduced.2.2.1 ≤ 1
  · exact Or.inr (Or.inl ⟨hq1, (isFFInt_iff_qInt_le_one _ _ _).mpr hq1⟩)
  have hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1 := fun hff =>
    hq1 ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  by_cases hdual : IsDualFFInt G₁ V h.reduced.2.2.1
  · exact Or.inr (Or.inr (Or.inl hdual))
  have hUe := D15Proof.isElemAbelian_conjClosure h hnff hVR₂
  have hUR₂ : conjClosure V G₂ ≤ pCoreOf 2 G₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hg) v).mp (hVR₂ hv)
  have hU2 : IsPGroup 2 (conjClosure V G₂) := (pCoreOf_isPGroup 2 G₂).to_le hUR₂
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom (H := G₂) (U := conjClosure V G₂)
    (conjClosure V G₂) ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V G₂ hg) x).mp hx⟩
  rcases (show c = 0 ∨ c = 1 ∨ 2 ≤ c by omega) with hc | hc | hc
  ·
    exact absurd (D14.commutator_eq_bot_of_zero hU2 hser hc) (D15Proof.commutator_ne_bot h)
  ·
    subst hc
    exact Or.inr (Or.inr (Or.inr (Or.inr (D15Proof.d15Concl5 h hnff hVR₂ hser hdual))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨D15Proof.qInt_le_two h hnff hVR₂ (hD125 hUe) hc hser,
        (B6.isElemAbelian_iff.mp hUe).1, c, hc, hser⟩)))

theorem inputD15Solvable_holds :
    ∀ (G : Type) [Group G] [Finite G] (G₁ G₂ T V M₂ : Subgroup G) (h : D11Hyp G₁ G₂ T V M₂),
      Group.IsSolvable G₂ → D15ConclAS G₁ G₂ T V h.reduced.2.2.1 := by
  intro G _ _ G₁ G₂ T V M₂ h hsolv
  have hVG₂ : V ≤ G₂ := h.V_le_T.trans h.sylow₂.1
  refine d15ConclAS_of_d125' h fun hUe =>
    D15Proof.d125_of_isSolvable hsolv h.sylow₂.1 ?_ hUe
  exact conjClosure_le fun g hg v hv => G₂.mul_mem (G₂.mul_mem hg (hVG₂ hv)) (G₂.inv_mem hg)

end CFSG.Quasithin.EmptyFaithfulMultiple
