module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem le_of_isMaxTwoLocal_le {M I : Subgroup G} (hM : quasithinIsMaxTwoLocal M) (hle : M ≤ I)
    (hI : pCoreOf 2 I ≠ ⊥) : I ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 I : Set G)) :=
    ⟨pCoreOf 2 I, hI, pCoreOf_isPGroup 2 I, rfl⟩
  have h := hM.2 _ hloc (hle.trans (le_normalizer_pCoreOf 2 I))
  exact (le_normalizer_pCoreOf 2 I).trans h.le

theorem commutator_eq_zSOf {T Mc M H : Subgroup G} (h13 : Lemma15213Concl T Mc M H)
    {B₀ : Subgroup (MulAut (V154 T Mc M))} (hB₀ : IsB0 T Mc M B₀) {B : Subgroup G}
    (hB : B ∈ sigmaPrime T H (V154 T Mc M)) : ⁅V154 T Mc M, B⁆ = zSOf T Mc M B₀ := by
  obtain ⟨B₀', -, huniq, hall⟩ := h13.exists_B0
  have := huniq B₀ hB₀
  subst this
  exact (hall B hB).2.2.1

theorem lemma_15_2_16 {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))}
    {I : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hB₀ : IsB0 T Mc M B₀)
    (hI : Hyp15215 T Mc M B₀ I) (h14 : Lemma15214Concl T Mc M B₀)
    (h13 : Lemma15213Concl T Mc M H)
    (h11 : ∀ B ∈ sigmaPrime T H (V154 T Mc M), Lemma15211Concl T Mc M H B)
    (hN : Notation15209Concl T Mc M H) : Lemma15216Concl T Mc M H B₀ I := by
  have hZS : quasithinOmegaOneCenter T ≤ zSOf T Mc M B₀ := h14.le_zS
  have hC : Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤ Mc :=
    (Subgroup.centralizer_le hZS).trans h14.mc_eq.ge
  have hcI : Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) ≤ Mc ⊓ I :=
    le_inf inf_le_left hI.inH.1
  refine ⟨le_antisymm (le_inf hC le_rfl) inf_le_right, hcI, ?_, ?_⟩
  ·
    obtain ⟨B, hB⟩ := hN.sigmaPrime_nonempty
    have hZ := commutator_eq_zSOf h13 hB₀ hB
    have hKc : oTwoUpper H ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
      have := (h11 B hB).centralizes
      rwa [hZ] at this
    have hSc : sOf152 T Mc M B₀ ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := inf_le_right
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact hcI ⟨hN.le_mc (oTwoUpper_le H hx), hKc hx⟩
    · exact hcI ⟨h.t_le_mc hx.1, hSc hx⟩
  · refine lt_of_le_of_ne hZS fun heq => hI.not_le ?_
    have hMc : Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
      rw [← heq]
      exact h14.mc_eq.le
    have hMcI : Mc ≤ I := (le_inf le_rfl hMc).trans hI.inH.1
    exact le_of_isMaxTwoLocal_le h.mc_max hMcI hI.inH.2

theorem lemma_15_2_17 {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))}
    {I : Subgroup G} (h14 : Lemma15214Concl T Mc M B₀) (h16 : Lemma15216Concl T Mc M H B₀ I) :
    (Nonempty (↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) ∨
        IsOmegaFourPlusOn M (V154 T Mc M)) ∧
      Nat.card (quasithinOmegaOneCenter T) = 2 ∧ (sOf152 T Mc M B₀).relIndex T = 2 := by
  rcases h14.cases with ⟨-, heq, -⟩ | hb
  · exact absurd heq h16.lt_zS.ne
  · exact hb

end CFSG.Quasithin
