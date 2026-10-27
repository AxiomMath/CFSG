module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L62b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L67
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem kDown_apply
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    kDown (θ a) A = ⊥ :=
  h.theorem_6_6_b (h.apply_mem_msig ha ha1) (thetaOf_le_apply ha ha1)

theorem sol_apply
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    sol (θ a) = ⊥ :=
  sol_eq_bot_of_kDown_eq_bot (kDown_apply h ha ha1)

theorem kDown_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    kDown (thetaOf θ B) A = ⊥ :=
  h.theorem_6_6_b (h.thetaOf_mem_msig hBA hB) (thetaOf_anti hBA)

theorem sol_thetaOf
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    sol (thetaOf θ B) = ⊥ :=
  sol_eq_bot_of_kDown_eq_bot (kDown_thetaOf h hBA hB)

theorem thetaOf_eq_inf_centralizer (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A)
    {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    thetaOf θ B = θ b ⊓ Subgroup.centralizer (B : Set G) := by
  have h1 := h.isFunctor.inf_centralizer_eq_thetaOf (hBA hb) hb1 hBA
  rw [sup_eq_right.mpr (Subgroup.zpowers_le.mpr hb)] at h1
  exact h1.symm

theorem lcal_thetaOf_eq
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    lcal (thetaOf θ A) = {Y | ∃ M ∈ lcal (θ a),
      Y = CFSG.inSubgroup CFSG.generalizedFitting (smear M A)} := by
  have h1 := (theorem_5_15_f (h.kSetting_apply ha ha1) (kDown_apply h ha ha1) (le_refl A)).2.1
  rwa [h.isFunctor.inf_centralizer_self ha ha1] at h1

theorem lcal_apply_nonempty
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    (lcal (θ a)).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hK := (isDirectProduct_lcal_kOf (sol_apply h ha ha1)).sSup_eq
  rw [hne, sSup_empty] at hK
  have hbot : θ a = ⊥ := (kOf_eq_bot_iff _).mp hK.symm
  apply h.not_isSolvable_apply ha ha1
  rw [hbot]
  infer_instance

theorem lcal_thetaOf_nonempty
    (h : Counterexample p A θ) : (lcal (thetaOf θ A)).Nonempty := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  obtain ⟨M, hM⟩ := lcal_apply_nonempty h ha ha1
  rw [lcal_thetaOf_eq h ha ha1]
  exact ⟨_, M, hM, rfl⟩

theorem thetaOf_le_normalizer
    (h : Counterexample p A θ) {J : Subgroup G}
    (hJ : J ∈ lcal (thetaOf θ A)) : thetaOf θ A ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  rw [lcal_thetaOf_eq h ha ha1] at hJ
  obtain ⟨M, hM, rfl⟩ := hJ
  intro d hd
  have hdθ : d ∈ θ a := thetaOf_le_apply ha ha1 hd
  rw [← h.lemma_6_7 ha ha1] at hdθ
  have hdM : d ∈ Subgroup.normalizer (M : Set G) :=
    ((T515e.mem_khat_iff_of_sol_eq_bot (sol_apply h ha ha1)).mp hdθ).2 M hM
  exact mem_normalizer_fitting_smear hdM (h.isFunctor.thetaOf_le_centralizer le_rfl hd)

theorem le_centralizer_of_le_thetaOf (h : Counterexample p A θ) {J : Subgroup G}
    (hJ : J ≤ thetaOf θ A) : A ≤ Subgroup.centralizer (J : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  exact (Subgroup.mem_centralizer_iff.mp (h.isFunctor.thetaOf_le_centralizer le_rfl (hJ hj)) a
    ha).symm

structure IsGreatestCentralizing (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (J W : Subgroup G) :
    Prop where
  mem : W ∈ Msig p A θ
  le_centralizer : W ≤ Subgroup.centralizer (J : Set G)
  le_of_le : ∀ X ∈ Msig p A θ, X ≤ Subgroup.centralizer (J : Set G) → X ≤ W
  apply_inf_le : ∀ a ∈ A, a ≠ 1 → θ a ⊓ Subgroup.centralizer (J : Set G) ≤ W

theorem exists_isGreatest (h : Counterexample p A θ) {J : Subgroup G}
    (hJ : J ∈ lcal (thetaOf θ A)) : ∃ W, IsGreatestCentralizing p A θ J W := by
  have hJD : J ≤ thetaOf θ A := lcal_le hJ
  have hAJ : A ≤ Subgroup.centralizer (J : Set G) := le_centralizer_of_le_thetaOf h hJD
  have hfun : IsFunctor p A (restrictFunctor (Subgroup.centralizer (J : Set G)) θ) :=
    h.isFunctor.restrictFunctor (hAJ.trans Subgroup.le_normalizer)
  have hC : ∀ a ∈ A, a ≠ 1 →
      signalizerMcBrideHypothesisB p (restrictFunctor (Subgroup.centralizer (J : Set G)) θ a) :=
    fun a ha ha1 => hypB_mono inf_le_left (h.hypC a ha ha1)
  have hlt : size A (restrictFunctor (Subgroup.centralizer (J : Set G)) θ) < size A θ := by
    obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
    refine size_restrictFunctor_lt ⟨a, ha, ha1, fun hle => ?_⟩
    have hJC : J ≤ Subgroup.centralizer (J : Set G) :=
      hJD.trans ((thetaOf_le_apply ha ha1).trans hle)
    exact (mem_lcal_iff.mp hJ).2.2.2 (Subgroup.le_centralizer_iff_isMulCommutative.mp hJC)
  obtain ⟨W, hW, hWmax⟩ := h.complete_of_size_lt
    ⟨h.prime, h.odd, h.elemAbelian, h.card, hfun, hC⟩ hlt
  have hiff := fun {X : Subgroup G} =>
    mem_signalizers_restrictFunctor_iff (θ := θ) (P := signalizerMcBrideHypothesisB p) (X := X)
      (H := Subgroup.centralizer (J : Set G)) h.prime h.elemAbelian h.rank_two_le
  refine ⟨W, ((hiff).mp hW).1, ((hiff).mp hW).2, fun X hX hXC => hWmax X (hiff.mpr ⟨hX, hXC⟩),
    fun a ha ha1 => hWmax _ (hfun.apply_mem_signalizers ha ha1 (hC a ha ha1))⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68
