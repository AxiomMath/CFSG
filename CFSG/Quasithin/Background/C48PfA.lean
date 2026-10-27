module

public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin.C48Pf

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem center_eq_bot_of_isPSL_two_one {n : ℕ} {X : Type} [Group X] (h : IsPSL n 2 1 X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by simpa using hF
  let e' := e.trans (Setup.Family.statedProjSL_equiv_of_card_two n F hF2)
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have hz' : e' z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e'.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [Setup.Family.center_specialLinear_eq_bot_of_card_two n (ZMod 2) (by simp),
    Subgroup.mem_bot] at hz'
  exact e'.injective (hz'.trans (map_one e').symm)

omit [Finite G] in
theorem oTwoZIn_le_pCoreOf {K : Subgroup G}
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) : oTwoZIn K ≤ pCoreOf 2 K := by
  unfold oTwoZIn preimageModTwoCore pCoreOf
  rw [hZ, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem pCoreOf_le_pCoreOf_sup (hR : R ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_sup_left.trans' (CFSG.LieType.BorelTits.pCoreOf_le 2 K)) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) ?_
  exact hR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)

theorem le_normalizer_K (h : HypC28 H R M L V) (h41 : C41Conclusion H R M L V K) :
    R ≤ Subgroup.normalizer (K : Set G) := by
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    have := le_normalizer_conjClosure K H
    rwa [h41.2.2.1] at this
  exact h.le_M.trans (h.le_H.trans hHK)

theorem pCoreOf_sup_le (h22 : ASC22Three G) (h : HypC28 H R M L V) (hK : K ∈ cComp H)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 (K ⊔ R) ≤ R := by
  have hrad := (c2_9_two h).2
  have hRK' : R ⊓ Subgroup.normalizer (K : Set G) = R := inf_eq_left.mpr hRK
  obtain ⟨h1, -⟩ := h22 H R K h.sqtk hrad hK
  rw [hRK'] at h1
  exact Fin253.pCoreOf_le_of_radical le_sup_right h.pgroup h1.symm

theorem le_pCoreOf_conjClosure_sup (h : HypC28 H R M L V) :
    R ≤ pCoreOf 2 (conjClosure L M ⊔ R) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
    (sup_le (c2_9_two h).1 Subgroup.le_normalizer) h.pgroup

theorem le_centralizer_V (h : HypC28 H R M L V) : R ≤ Subgroup.centralizer (V : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvZ := h.V_center hv
  exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hvZ).2) r
    (le_pCoreOf_conjClosure_sup h hr)).symm

theorem le_omegaOneCenter (h22 : ASC22Three G) (h27 : ASC27Statement G)
    (h : HypC28 H R M L V) (hK : K ∈ cComp H) (hchar : CharTwo K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (h41 : C41Conclusion H R M L V K) (h4 : C41Case4 H R M L V K) :
    V ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) := by
  have hRK := le_normalizer_K h h41
  have hQR := pCoreOf_sup_le h22 h hK hRK
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases h4.1 with h4' | h5'
    · exact center_eq_bot_of_isPSL_two_one h4'
    · exact center_eq_bot_of_isPSL_two_one h5'
  set Q := pCoreOf 2 (K ⊔ R) with hQ
  set U := omegaOneCenterOf Q with hU
  obtain ⟨⟨-, hC, -⟩, -⟩ := h27 H R M K U (c2_10_four h) hK hq hchar hKM hRK rfl
  have hCQ : (K ⊔ R) ⊓ Subgroup.centralizer (U : Set G) ≤ Q :=
    hC.trans (sup_le le_rfl ((oTwoZIn_le_pCoreOf hZ).trans (pCoreOf_le_pCoreOf_sup hRK)))
  have hM0K : conjClosure L M ≤ K := h41.2.1.trans h41.2.2.1.le
  have hVK : V ≤ K ⊔ R := (h.V_le.trans hM0K).trans le_sup_left
  have hRV := le_centralizer_V h
  have hVQc : V ≤ Subgroup.centralizer (Q : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq'
    exact (Subgroup.mem_centralizer_iff.mp (hRV (hQR hq')) v hv).symm
  have hUQ : U ≤ Q := fun u hu => by
    have : omegaOneOf (centerOf Q) ≤ centerOf Q := by
      rw [omegaOneOf, Subgroup.closure_le]
      exact fun x hx => hx.1
    exact (this hu).1
  have hVU : V ≤ Subgroup.centralizer (U : Set G) := fun v hv =>
    Subgroup.centralizer_le hUQ (hVQc hv)
  have hVQ : V ≤ Q := fun v hv => hCQ ⟨hVK hv, hVU hv⟩
  intro v hv
  refine Subgroup.subset_closure ⟨⟨hVQ hv, hVQc hv⟩, ?_⟩
  exact h.V_elem.2 v hv

theorem le_commutator (h22 : ASC22Three G) (h27 : ASC27Statement G)
    (h : HypC28 H R M L V) (hK : K ∈ cComp H) (hchar : CharTwo K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (h41 : C41Conclusion H R M L V K) (h4 : C41Case4 H R M L V K) :
    V ≤ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆ ∧
      V ≤ Subgroup.centralizer (pCoreOf 2 (conjClosure L M) : Set G) := by
  have hVU := le_omegaOneCenter h22 h27 h hK hchar hq hKM h41 h4
  have hM0K : conjClosure L M ≤ K := h41.2.1.trans h41.2.2.1.le
  refine ⟨?_, ?_⟩
  · rw [← h.V_comm]
    exact Subgroup.commutator_mono hVU hM0K
  · have hOR : pCoreOf 2 (conjClosure L M) ≤ R := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hmax := (A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2
      have hM0M := C2Nine.conjClosure_le_M h
      have hPC := pCoreOf_le_centralizerSection hM0M
      have hRN : R ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure L M) : Set G) :=
        h.sylow.1.trans (centralizerSection_le_normalizer_right _ _ _)
      have hP : IsPGroup 2 ↥(pCoreOf 2 (conjClosure L M) ⊔ R) :=
        IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) h.pgroup hRN
      exact le_sup_left.trans (hmax _ (sup_le hPC h.sylow.1) hP le_sup_right)
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (le_centralizer_V h (hOR hx)) v hv).symm

end CFSG.Quasithin.C48Pf
