module

public import CFSG.Quasithin.Vol2.Ch3xThm316
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319
public import CFSG.Quasithin.EmptyFaithful.LRed13Ex

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Lemma319Shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False →
      oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
        Subgroup.centralizer (V : Set G) →
      ∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
        ChiefFactorShape H L N

section Prelim

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

omit [Finite G] in
theorem isMaxElemAbelian_of_le {T R A : Subgroup G} (hA : IsMaxElemAbelian T A) (hAR : A ≤ R)
    (hRT : R ≤ T) : IsMaxElemAbelian R A :=
  ⟨hAR, hA.2.1, fun B hBR hB => hA.2.2 B (hBR.trans hRT) hB⟩

omit [Finite G] in
theorem IsMinOffender.not_le {T H V A : Subgroup G} (hRT : pCoreOf 2 H ≤ T)
    (h : IsMinOffender T H V A) : ¬ A ≤ pCoreOf 2 H := fun hle =>
  h.2.1 (isMaxElemAbelian_of_le h.1 hle hRT)

end Prelim

section Counting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem count_one_of {A Q U : Subgroup G}
    (hu : (Subgroup.centralizer (A : Set G)).relIndex U = (Q.relIndex A) ^ 2) :
    Nat.card A ^ 2 * Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
      Nat.card (A ⊓ Q : Subgroup G) ^ 2 * Nat.card U := by
  have e1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) U
  have e2 := Subgroup.relIndex_mul_card Q A
  rw [inf_comm (Subgroup.centralizer (A : Set G)) U] at e1
  rw [inf_comm Q A] at e2
  rw [← e1, ← e2, hu]
  ring

omit [Finite G] in
theorem count_two_of {A Q U : Subgroup G}
    (hu : (Subgroup.centralizer (A : Set G)).relIndex U = (Q.relIndex A) ^ 2)
    (hb : (Subgroup.centralizer (U : Set G)).relIndex (Q ⊓ A) = Q.relIndex A) :
    Nat.card U * Nat.card (A ⊓ Q ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) ^ 2 =
      Nat.card (A ⊓ Q : Subgroup G) ^ 2 *
        Nat.card (U ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have e1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (A : Set G)) U
  have e3 := Subgroup.relIndex_mul_card (Subgroup.centralizer (U : Set G)) (Q ⊓ A)
  rw [inf_comm (Subgroup.centralizer (A : Set G)) U] at e1
  have hsub : A ⊓ Q ⊓ Subgroup.centralizer (U : Set G) =
      Subgroup.centralizer (U : Set G) ⊓ (Q ⊓ A) := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hsub2 : (A ⊓ Q : Subgroup G) = Q ⊓ A := inf_comm _ _
  rw [hsub, hsub2]
  rw [hb] at e3
  rw [← e1, hu]
  rw [← e3]
  ring

omit [Finite G] in
theorem count_three_of {B W : Subgroup G}
    (h : ((Subgroup.centralizer (W : Set G)).relIndex B) ^ 2 =
      (Subgroup.centralizer (B : Set G)).relIndex W) :
    Nat.card B ^ 2 * Nat.card (W ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) =
      Nat.card (B ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) ^ 2 * Nat.card W := by
  have e1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (W : Set G)) B
  have e2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (B : Set G)) W
  rw [inf_comm (Subgroup.centralizer (W : Set G)) B] at e1
  rw [inf_comm (Subgroup.centralizer (B : Set G)) W] at e2
  rw [← e1, ← e2, ← h]
  ring

theorem inf_eq_of_relIndex_eq {K₁ K₂ U : Subgroup G} (h : K₁ ≤ K₂)
    (hidx : K₁.relIndex U = K₂.relIndex U) : U ⊓ K₁ = U ⊓ K₂ := by
  have e1 := Subgroup.relIndex_mul_card K₁ U
  have e2 := Subgroup.relIndex_mul_card K₂ U
  have hpos : 0 < K₂.relIndex U := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card ↥(K₁ ⊓ U) = Nat.card ↥(K₂ ⊓ U) := by
    rw [hidx] at e1
    exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
  rw [inf_comm U K₁, inf_comm U K₂]
  exact Subgroup.eq_of_le_of_card_ge (inf_le_inf_right U h) hcard.ge

omit [Finite G] in
theorem cSecIn_eq_centralizerMod {A L N H U : Subgroup G} (hAH : A ≤ H) (hL : IsNormalIn H U L) :
    cSecIn A L N = centralizerMod L A N := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro f ⟨hfA, hf⟩
    exact ⟨hfA, D14.le_normalizer_of_isNormalIn hL (hAH hfA), hf⟩
  · intro x hx
    exact Subgroup.subset_closure ⟨hx.1, hx.2.2⟩

omit [Finite G] in
theorem fixSecIn_eq_centralizerMod {A L N H U : Subgroup G} (hNH : N ≤ H) (hL : IsNormalIn H U L) :
    fixSecIn A L N = centralizerMod L N A := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxN, hx⟩
    refine ⟨hxN, D14.le_normalizer_of_isNormalIn hL (hNH hxN), fun a ha => ?_⟩
    have h1 := L.inv_mem (hx a ha)
    rwa [show (a * x * a⁻¹ * x⁻¹)⁻¹ = x * a * x⁻¹ * a⁻¹ by group] at h1
  · intro x hx
    refine Subgroup.subset_closure ⟨hx.1, fun a ha => ?_⟩
    have h1 := L.inv_mem (hx.2.2 a ha)
    rwa [show (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ by group] at h1

omit [Finite G] in
theorem count_four_of {A Q N D : Subgroup G} (hDN : D ≤ N)
    (hu : D.relIndex N = Q.relIndex A) :
    Nat.card A * Nat.card D = Nat.card (A ⊓ Q : Subgroup G) * Nat.card N := by
  have e1 := Subgroup.relIndex_mul_card D N
  have e2 := Subgroup.relIndex_mul_card Q A
  rw [inf_eq_left.mpr hDN] at e1
  rw [inf_comm Q A] at e2
  rw [← e1, ← e2, hu]
  ring

end Counting

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem d125_of_input {M₀ H T V M₂ : Subgroup G} (hD125 : D125NonsolvableSQTK)
    (hD : D11Hyp M₀ H T V M₂) (hsq : IsSQTKSub H)
    (hq1 : ¬ qInt M₀ V hD.reduced.2.2.1 ≤ 1) (hVR₂ : V ≤ pCoreOf 2 H)
    (hUe : IsElemAbelian 2 (conjClosure V H)) : D15Proof.D125 H T (conjClosure V H) := by
  by_cases hsolv : Group.IsSolvable H
  · have hVH : V ≤ H := hD.V_le_T.trans hD.sylow₂.1
    refine D15Proof.d125_of_isSolvable hsolv hD.sylow₂.1 ?_ hUe
    exact conjClosure_le fun g hg v hv => H.mul_mem (H.mul_mem hg (hVH hv)) (H.inv_mem hg)
  · exact hD125 G M₀ H T V M₂ hD hsq hsolv hq1 hVR₂ hUe

variable {T M M₀ H V : Subgroup G}

theorem Hyp319.exists_c (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T) (hM : InM T M)
    (h : Hyp319 T M M₀ H V) :
    ∃ c : ℕ, 2 ≤ c ∧ IsChiefSeriesFrom H (conjClosure V H) (conjClosure V H) c := by
  have hD := h.d11Hyp hT
  have hsqH : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  rcases hD15 G M₀ H T V (H ⊓ M) hD hsqH with h1' | ⟨h2, -⟩ | h3 | ⟨-, -, c, hc2, hc⟩ |
      ⟨h5a, h5b, h5c, -, -, -⟩
  · exact absurd h.le_pCore h1'
  · exact absurd h2 h.not_qInt_le_one
  · exact absurd h3 h.not_dualFF
  · exact ⟨c, hc2, hc⟩
  · exfalso
    have hsyl : IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀) := by
      by_cases hsolv : Group.IsSolvable H
      · exact EmptyFaithfulMultiple.inputD14Solvable_holds G M₀ H T V (H ⊓ M) hD h.le_pCore h5c
          h.not_dualFF hsolv (charTwo_of_inH' hK hT h.inH_H)
      · exact hS316 G T M M₀ H V hs hnab hK hT hM ⟨h.toHyp315Base, Or.inr h.caseII⟩ h.V_ne_bot
          h.not_exists_normal h.not_qInt_le_one h.not_dualFF h.le_pCore h5a h5b hsolv
    exact h.not_exists_normal (h.toHyp315Base.exists_normal_of_sylow hC58 hs hnab hK hT hM hsyl)

theorem Hyp319.pCoreOf_le (hT : quasithinIsSylowTwo T) (h : Hyp319 T M M₀ H V) :
    pCoreOf 2 H ≤ T :=
  B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hT h.hStar.1.1)

end Reduction

section Main

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_le_T {G₁ G₂ T V M₂ : Subgroup G} (h : D11Hyp G₁ G₂ T V M₂)
    (hVR₂ : V ≤ pCoreOf 2 G₂) : conjClosure V G₂ ≤ T := by
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₂ : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 G₂
  have hUR₂ : conjClosure V G₂ ≤ pCoreOf 2 G₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  exact hUR₂.trans (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂)

theorem not_le_centralizer_conjClosure {G₁ G₂ T V M₂ : Subgroup G} (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) {A : Subgroup G} (hAT : A ≤ T)
    (hA : ¬ A ≤ pCoreOf 2 G₂) : ¬ A ≤ Subgroup.centralizer (conjClosure V G₂ : Set G) := by
  intro hle
  apply hA
  have hmp := h.minParabolic hnff
  exact (le_inf le_rfl hle).trans (D15Proof.inf_centralizer_le_pCoreOf hmp
    (le_normalizer_conjClosure V G₂) (D15Proof.commutator_ne_bot h) hAT)

variable {T M M₀ H V : Subgroup G}

theorem Hyp319.concl_core (hC58 : TheoremC58) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : InM T M) (h : Hyp319 T M M₀ H V) : Concl319 T M V H False := by
  obtain ⟨c, hc2, hser⟩ := Hyp319.exists_c hC58 hD15 hS316 hs hnab hK hT hM h
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hsq : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  have hUe := D15Proof.isElemAbelian_conjClosure hD hnff h.le_pCore
  have hD125' := d125_of_input hD125 hD hsq h.not_qInt_le_one h.le_pCore hUe
  have hq2 : (2 : WithTop ℚ) ≤ qInt M₀ V h.reduced.2.2.1 := h.q_eq.ge
  have hc : c = 2 := Ch3y.c_eq_two hD hnff h.le_pCore hD125' hq2 hc2 hser
  subst hc
  have hRT := h.pCoreOf_le hT
  have hUT := conjClosure_le_T hD h.le_pCore
  have hTH : T ≤ H := h.hStar.1.1
  have hchain : ∀ A : Subgroup G, IsMinOffender T H V A →
      (Subgroup.centralizer (conjClosure V H : Set G)).relIndex (pCoreOf 2 H ⊓ A) =
        (pCoreOf 2 H).relIndex A ∧
      (Subgroup.centralizer (A : Set G)).relIndex (conjClosure V H) =
        ((pCoreOf 2 H).relIndex A) ^ 2 ∧
      (Subgroup.centralizer ((pCoreOf 2 H ⊓ A : Subgroup G) : Set G)).relIndex (conjClosure V H) =
        ((pCoreOf 2 H).relIndex A) ^ 2 ∧
      (∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
        (centralizerMod L N A).relIndex N = (pCoreOf 2 H).relIndex A ∧
          centralizerMod L A N = pCoreOf 2 H ⊓ A) ∧
      (∀ k ∈ H, ¬ (pCoreOf 2 H ⊓ A) ≤ Subgroup.centralizer (cjSub k V : Set G) →
        ((Subgroup.centralizer (cjSub k V : Set G)).relIndex (pCoreOf 2 H ⊓ A)) ^ 2 =
          (Subgroup.centralizer ((pCoreOf 2 H ⊓ A : Subgroup G) : Set G)).relIndex (cjSub k V)) := by
    intro A hA
    obtain ⟨-, hb, hu, hv, hst, hcj⟩ := Ch3y.chain_two hD hnff h.le_pCore hD125' hq2 le_rfl hser
      hA.1.1 hA.1.2.1 hA.2.2.2 (not_le_centralizer_conjClosure hD hnff hA.1.1 (hA.not_le hRT))
      (card_le_relIndex_mul_card hUe hUT hA.1)
    exact ⟨hb, hu, hv, hst, hcj⟩
  refine
    { elemAbelian := hUe
      chief := hser
      exists_A := LRed13.exists_isMinOffender_quadratic hD hnff h.le_pCore hq2
      quadratic := fun A hA => hA.2.2.2
      count_one := fun A hA => count_one_of (hchain A hA).2.1
      count_two := fun A hA => ?_
      count_three := fun A hA k hk hne => ?_
      count_four := fun A hA L N hstep hnc => ?_
      fixed_eq := fun A hA => ?_
      shape := fun hf => hf.elim }
  · have hb := (hchain A hA).1
    have hu := (hchain A hA).2.1
    exact count_two_of hu hb
  · have hBW : ¬ (pCoreOf 2 H ⊓ A) ≤ Subgroup.centralizer (cjSub k⁻¹ V : Set G) := by
      rw [inf_comm]
      intro hle
      exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
    have heq := (hchain A hA).2.2.2.2 k⁻¹ (H.inv_mem hk) hBW
    rw [inf_comm (pCoreOf 2 H) A] at heq
    exact count_three_of (B := A ⊓ pCoreOf 2 H) (W := conjSubgroup V k) heq
  · obtain ⟨hu₀, hD'⟩ := (hchain A hA).2.2.2.1 L N hstep hnc
    have hL : IsNormalIn H (conjClosure V H) L := hstep.2.1
    have hNH : N ≤ H := hstep.1.1.trans (hUT.trans hTH)
    refine ⟨?_, ?_⟩
    · rw [cSecIn_eq_centralizerMod (U := conjClosure V H) (H := H) (hA.1.1.trans hTH) hL, hD',
        inf_comm]
    · rw [fixSecIn_eq_centralizerMod (U := conjClosure V H) hNH hL]
      exact count_four_of (centralizerMod_le_left L N A) hu₀
  · have hu := (hchain A hA).2.1
    have hv := (hchain A hA).2.2.1
    rw [inf_comm (pCoreOf 2 H) A] at hv
    exact inf_eq_of_relIndex_eq (Subgroup.centralizer_le fun x hx => (Subgroup.mem_inf.mp hx).1)
      (hu.trans hv.symm)

end Main

end CFSG.Quasithin
