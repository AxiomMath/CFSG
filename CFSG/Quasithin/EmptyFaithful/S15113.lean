module

public import CFSG.Quasithin.EmptyFaithful.S1519
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_13_one {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h1512 : ∀ H : Subgroup G, IsHStar T M H →
      ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥) :
    ¬ Subgroup.centralizer (omegaOneCenterOf (thompsonJi T 1) : Set G) ≤ M := by
  obtain ⟨H, hH⟩ := exists_isHStar h.inM_mc hM.1.1 (Ne.symm hM.2.1)
  intro hC
  have hTM : T ≤ M := hM.1.1.2
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le151 h.sylow hH.1.1
  have hle : oTwoUpper H ≤ M := (le_centralizer_of_commutator_eq_bot (h1512 H hH)).trans hC
  exact hH.2.1 ((eq_oTwoUpper_sup_of_isSylowTwoOf hsyl).le.trans (sup_le hle hTM))

theorem lemma_15_1_13_two {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h157 : Lemma1517Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (hone : ¬ Subgroup.centralizer (omegaOneCenterOf (thompsonJi T 1) : Set G) ≤ M) :
    ⁅V154 T Mc M, thompsonJi T 1⁆ ≠ ⊥ := by
  intro hcomm
  have hrank : 1 < CFSG.Open.pRank 2 T := one_lt_pRank_T h hM h157
  have hJ1T : thompsonJi T 1 ≤ T := iSup₂_le fun _ hA => hA.1
  have hJ1R : thompsonJi T 1 ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf hJ1T (le_centralizer_of_commutator_eq_bot hcomm)
  have heq := thompsonJi_eq_of_le (S := T)
    (R := T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) (i := 1) hrank hJ1R inf_le_left
  have hN : M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (omegaOneCenterOf (thompsonJi T 1) : Set G) := by
    intro x hx
    have h1 := normalizer_le_normalizer_thompsonJi151
      (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) 1 (Subgroup.mem_inf.mp hx).2
    rw [← heq] at h1
    exact normalizer_le_normalizer_omegaOneCenterOf _ h1
  have hE1p : IsPGroup 2 (omegaOneCenterOf (thompsonJi T 1)) :=
    h.sylow.1.to_le ((omegaOneCenterOf_le_self _).trans hJ1T)
  have hE1 : omegaOneCenterOf (thompsonJi T 1) ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot (h.sylow.1.to_le hJ1T)
      (thompsonJi_one_ne_bot hrank)
  obtain ⟨K, hK, hNK⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (omegaOneCenterOf (thompsonJi T 1) : Set G)) ⟨_, hE1, hE1p, rfl⟩
  have hKM : K = M := h159.five.2 K ⟨hK, hN.trans hNK⟩
  exact hone ((Subgroup.centralizer_le_normalizer _).trans (hNK.trans hKM.le))

theorem lemma_15_1_13 {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h157 : Lemma1517Concl T Mc M) (h159 : Lemma1519Concl T Mc M)
    (h1512 : ∀ H : Subgroup G, IsHStar T M H →
      ⁅omegaOneCenterOf (thompsonJi T 1), oTwoUpper H⁆ = ⊥)
    (h3 : Lemma15113Three T Mc M) (h4 : Lemma15113Four T Mc M) : Lemma15113Concl T Mc M :=
  ⟨lemma_15_1_13_one h hM h1512, lemma_15_1_13_two h hM h157 h159 (lemma_15_1_13_one h hM h1512),
    h3, h4⟩

theorem stageLemma15113_of (h157 : StageLemma1517) (h159 : StageLemma1519)
    (h1512 : StageLemma15112) (h3 : StageLemma15113Three) (h4 : StageLemma15113Four) :
    StageLemma15113 := by
  intro G _ _ T Mc M h hM hCE
  exact lemma_15_1_13 h hM (h157 G T Mc M h hM hCE) (h159 G T Mc M h hM hCE)
    (fun H hH => (h1512 G T Mc M h hM hCE H hH).2) (h3 G T Mc M h hM hCE) (h4 G T Mc M h hM hCE)

end CFSG.Quasithin
