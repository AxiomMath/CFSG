module

public import CFSG.Quasithin.EmptyFaithful.T1515B
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem opResidual_two_oTwoUpper1516 (X : Subgroup G) : opResidual 2 (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (opResidual_le 2 _) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_opResidual_of_coprime (Subgroup.subset_closure hx) (Nat.coprime_two_right.mpr hx.2)

theorem Setting1516.V_le_g1 {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (h : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : V154 T Mc M ≤ g1_1516 Z₁ := by
  have hVab := h.V_isElemAbelian hq hM
  intro v hv
  rw [g1_1516, Subgroup.mem_centralizer_iff]
  intro z hz
  have := hVab.1
  have hcomm := mul_comm' (⟨z, h.z1_le_V hz⟩ : V154 T Mc M) ⟨v, hv⟩
  exact congrArg (fun a : V154 T Mc M => (a : G)) hcomm

theorem pRank_pCoreOf_le_two1516 {T Mc : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p H) ≤ 2 := fun p hp hp2 =>
  (CFSG.SectionRank.pRank_mono hp.one_lt (CFSG.LieType.BorelTits.pCoreOf_le p H)).trans
    (pRank_le_two_of_pCoreOf_ne_bot hq.qtke hH hp hp2)

theorem lemma_15_1_19_one {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂)
    (h18 : Lemma15118Concl T Mc M Z₁) : oddCoreIn (g1_1516 Z₁) = ⊥ := by
  have hVab := hS.V_isElemAbelian hq hM
  have hV2el : IsElemAbelian 2 V₂ := isElemAbelian_mono151 hS.v2_le hVab
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hS.pCore_g1_ne_bot hq hM
  have hX : oTwoUpper (M ⊓ g1_1516 Z₁) ≤ g1_1516 Z₁ := (oTwoUpper_le _).trans inf_le_right
  have hV2G : V₂ ≤ g1_1516 Z₁ := hS.v2_le.trans (hS.V_le_g1 hq hM)
  have hV2C : V₂ ≤ Subgroup.centralizer (fusionOddCoreOf (g1_1516 Z₁) : Set G) :=
    a126_one hX (opResidual_two_oTwoUpper1516 _) hV2G (isPGroup_of_isElemAbelian hV2el) hS.v2_comm
      (pRank_pCoreOf_le_two1516 hq hpc) (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hV2el)
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hq.omegaOneCenter_ne_bot
  have hzZ : (a : G) ∈ quasithinOmegaOneCenter T := a.2
  have hz1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hlez := hS.z_le hzZ
  have hH := h18.six (a : G) hzZ hz1
  have hprops := hH.oddCoreIn_properties
  refine eq_bot_iff.mpr fun y hy => ?_
  have hyG : y ∈ g1_1516 Z₁ := Subgroup.map_subtype_le _ hy
  have hcomm : ∀ w ∈ Z₁ ⊔ V₂, w * y = y * w := by
    have hle : Z₁ ⊔ V₂ ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact (Subgroup.mem_centralizer_iff.mp hyG w hw).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact Subgroup.mem_centralizer_iff.mp (hV2C hw) y hy
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) y (Set.mem_singleton y)).symm
  have hyz : y ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hcomm _ hlez
  have hmem : y ∈ oddCoreIn (g1_1516 Z₁) ⊓ Subgroup.centralizer ({(a : G)} : Set G) := ⟨hy, hyz⟩
  rw [hprops.2.1] at hmem
  exact hmem

theorem lemma_15_1_19_four {Mc Z₁ : Subgroup G}
    (h5 : mZ1516 Mc Z₁ = g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G)) :
    ∀ H : Subgroup G, mZ1516 Mc Z₁ ≤ H → H ≤ g1_1516 Z₁ → oTwoFstarIn H ≤ mZ1516 Mc Z₁ →
      H = mZ1516 Mc Z₁ := by
  intro H hMH hHG hF
  have hX : oTwoFstarIn H ≤ H ⊓ mZ1516 Mc Z₁ := le_inf (oTwoFstarIn_le H) hF
  have h441 := a4_4_1 (pCoreOf_le_oTwoFstarIn H) hX (a44Hyp_oTwoFstarIn H)
  rw [inf_eq_right.mpr hMH] at h441
  refine le_antisymm ?_ hMH
  rw [h5]
  refine le_inf hHG ?_
  have hN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  rw [← h441] at hN
  exact hN

structure Lemma15119Rest (T Mc M Z₁ V₂ : Subgroup G) : Prop where
  two : ∀ K : Subgroup G, K ≤ g1_1516 Z₁ → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
    mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ mZ1516 Mc Z₁
  three : oTwoFIn (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  five : solvRad (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  six : ∃ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) ∧
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ¬ L ≤ mZ1516 Mc Z₁
  seven : ∀ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → ¬ L ≤ mZ1516 Mc Z₁ →
      oTwoUpper (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ⊔ V₂ ≤ Subgroup.normalizer (L : Set G) ∧
        ⁅L, V₂⁆ ≠ ⊥

theorem lemma_15_1_19_of_rest {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂)
    (h18 : Lemma15118Concl T Mc M Z₁) (hR : Lemma15119Rest T Mc M Z₁ V₂) :
    Lemma15119Concl T Mc M Z₁ V₂ :=
  ⟨lemma_15_1_19_one hq hM hS h18, hR.two, hR.three, lemma_15_1_19_four h18.five.2.1, hR.five,
    hR.six, hR.seven⟩

end CFSG.Quasithin
