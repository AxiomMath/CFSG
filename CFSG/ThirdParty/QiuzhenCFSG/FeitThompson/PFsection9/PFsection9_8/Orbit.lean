module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.Linear

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

@[expose] public def H0COrderedComponentCharacterFamilyData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 C : Subgroup G)
    (p q : ℕ) : Prop :=
  theorem_9_7_orderedCaseAComponentTransitionData_sec9 MF H0 U W1 C p q


@[expose] public def H0COrderedXmuCoordinateData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 C : Subgroup G)
    (q aρ : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
  (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i)) : Prop :=
  ∃ hW1normU : W1 ≤ Subgroup.normalizer (U : Set G),
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    ∃ w0 : W1,
      Subgroup.zpowers w0 = ⊤ ∧
        ∃ hqpos : 0 < q,
          (∀ i : Fin q,
            quotientSubgroupConjugateByElement MF H0
              (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) ∧
            ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →*
                Multiplicative (ZMod aρ),
              (∀ i, ∀ x y : U ⧸ C.subgroupOf U,
                χbar i x = χbar i y → ρ i x = ρ i y) ∧
                ∀ x : U,
                  ∀ i,
                    χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
                      χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
                        (QuotientGroup.mk' (C.subgroupOf U) x)

public theorem H0COrderedXmuCoordinateData_of_ordered_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U W1 H0 C : Subgroup G)
    (p q : ℕ) :
    H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q →
      ∃ aρ : ℕ,
        ∃ hnormalH0 : (H0.subgroupOf MF).Normal,
          letI : (H0.subgroupOf MF).Normal := hnormalH0
          ∃ hnormalC : (C.subgroupOf U).Normal,
            letI : (C.subgroupOf U).Normal := hnormalC
            ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
              ∃ _hHcard : ∀ i, Nat.card (H i) = p,
                (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                  iSupIndep H ∧
                  iSup H = ⊤ ∧
                  (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) aρ) ∧
                  (∃ hqpos : 0 < q,
                    ∀ i : Fin q,
                      ∃ w : W1,
                        quotientSubgroupConjugateByElement MF H0
                          (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                  ∃ ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i),
                    (∀ i, IsCyclic (ρ i).range) ∧
                      (∀ i, Nat.card (ρ i).range = aρ) ∧
                      (∀ i, ∀ x : U ⧸ C.subgroupOf U,
                        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
                          ∃ hconjMF : ∀ h : MF,
                            (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                            ∀ h : MF,
                            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                              (ρ i x
                                ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                                  MF ⧸ H0.subgroupOf MF) =
                                QuotientGroup.mk' (H0.subgroupOf MF)
                                  ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                    hconjMF h⟩) ∧
                      (∀ i, ∀ x : U ⧸ C.subgroupOf U,
                        ρ i x = 1 ↔
                          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
                            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G)) ∧
                      H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ := by
  classical
  intro hordered
  rcases hordered with
    ⟨aρ, hnormalH0, hW1normU, hnormalC, w0, hw0gen, H, hHcard, hHnorm,
      hHindep, hHsup, hfac, hqpos, hsucc, χbar, hχdata, hχtransition⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  choose ρ hρ using hχdata
  have hρcyc : ∀ i, IsCyclic (ρ i).range := fun i => (hρ i).1
  have hρcard : ∀ i, Nat.card (ρ i).range = aρ := fun i => (hρ i).2.1
  have hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ :=
    fun i => (hρ i).2.2.1
  have hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) :=
    fun i => (hρ i).2.2.2.1
  have hρsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y :=
    fun i => (hρ i).2.2.2.2
  have hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩)
            (H i) (w : G) :=
    ⟨hqpos,
      theorem_9_7_weak_orbit_of_successor_conjugates_sec9
        (MF := MF) (H0 := H0) (W1 := W1) hqpos H w0 hsucc⟩
  have horderedXmu :
      H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ :=
    ⟨hW1normU, w0, hw0gen, hqpos, hsucc, χbar, hρsep, hχtransition⟩
  exact
    ⟨aρ, hnormalH0, hnormalC, H, hHcard, hHnorm, hHindep, hHsup, hfac,
      hconj, ρ, hρcyc, hρcard, hρaction, hρker, horderedXmu⟩

public abbrev H0CLinearCandidateXthetaRawIndex_sec9 (p q : ℕ) : Type u :=
  ULift.{u, 0} (Fin q → Fin (p - 1))

public abbrev H0CLinearCandidateXmuRawIndex_sec9 (p : ℕ) : Type :=
  Fin (p - 1)


public theorem quotientSubgroupConjugateByElement_mulEquiv_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    ∃ e : Q ≃* R,
      ∃ hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF,
        ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
          (e ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨g⁻¹ * (h : G) * g, hconjMF h⟩ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  let e0 : Q ≃* Q.map action.toMonoidHom := action.subgroupMap Q
  let e : Q ≃* R := e0.trans (MulEquiv.subgroupCongr hR.symm)
  refine ⟨e, hconjMF, ?_⟩
  intro h hhQ
  change action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
    QuotientGroup.mk' (H0.subgroupOf MF) ⟨g⁻¹ * (h : G) * g, hconjMF h⟩
  exact haction h

public theorem conj_inv_mem_of_conj_mem_finite_sec9
    {G : Type u} [Group G] [Finite G]
    {MF : Subgroup G} {g : G}
    (hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF) :
    ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF := by
  classical
  letI : Fintype MF := Fintype.ofFinite MF
  let f : MF → MF := fun h => ⟨g⁻¹ * (h : G) * g, hconjMF h⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    dsimp [f] at hval
    calc
      (x : G) = g * (g⁻¹ * (x : G) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * (y : G) * g) * g⁻¹ := by rw [hval]
      _ = (y : G) := by group
  have hf_surj : Function.Surjective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, rfl⟩ |>.2
  intro h
  rcases hf_surj h with ⟨k, hk⟩
  have hkval := congrArg Subtype.val hk
  dsimp [f] at hkval
  have hk_eq : (k : G) = g * (h : G) * g⁻¹ := by
    calc
      (k : G) = g * (g⁻¹ * (k : G) * g) * g⁻¹ := by group
      _ = g * (h : G) * g⁻¹ := by rw [hkval]
  simpa [hk_eq] using k.property

public theorem quotientSubgroupConjugateByElement_action_symm_apply_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    ∃ hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF,
      ∃ action : MulAut (MF ⧸ H0.subgroupOf MF),
        (∀ h : MF,
          action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨g⁻¹ * (h : G) * g, hconjMF h⟩) ∧
          R = Q.map action.toMonoidHom ∧
          ∃ hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF,
            ∀ h : MF,
              action.symm (QuotientGroup.mk' (H0.subgroupOf MF) h) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  have hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF :=
    conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  refine ⟨hconjMF, action, haction, hR, hconjInvMF, ?_⟩
  intro h
  apply action.injective
  simp only [MulEquiv.apply_symm_apply]
  symm
  calc
    action (QuotientGroup.mk' (H0.subgroupOf MF)
        ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩) =
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨g⁻¹ * (g * (h : G) * g⁻¹) * g,
            hconjMF ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩⟩ := haction _
    _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        group

public theorem quotientSubgroupConjugateByElement_symm_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    quotientSubgroupConjugateByElement MF H0 R Q g⁻¹ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  have hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF :=
    conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  refine ⟨?_, action.symm, ?_, ?_⟩
  · intro h
    simpa only [inv_inv] using hconjInvMF h
  · intro h
    apply action.injective
    simp only [MulEquiv.apply_symm_apply]
    symm
    calc
      action (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(g⁻¹)⁻¹ * (h : G) * g⁻¹, by
            simpa only [inv_inv] using hconjInvMF h⟩) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * ((g⁻¹)⁻¹ * (h : G) * g⁻¹) * g,
              hconjMF ⟨(g⁻¹)⁻¹ * (h : G) * g⁻¹, by
                simpa only [inv_inv] using hconjInvMF h⟩⟩ :=
        haction _
      _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        group
  · ext x
    constructor
    · intro hxQ
      refine ⟨action x, ?_, by simp⟩
      rw [hR]
      exact ⟨x, hxQ, rfl⟩
    · rintro ⟨y, hyR, hyx⟩
      rw [hR] at hyR
      rcases hyR with ⟨z, hzQ, rfl⟩
      have hzx : z = x := by
        simpa using congrArg action hyx
      simpa [← hzx] using hzQ

public theorem quotientSubgroupConjugateByElement_one_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    quotientSubgroupConjugateByElement MF H0 Q Q (1 : G) := by
  refine ⟨?_, 1, ?_, ?_⟩
  · intro h
    simp
  · intro h
    simp
  · ext x
    simp [Subgroup.mem_map]

public theorem quotientSubgroupConjugateByElement_trans_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R S : Subgroup (MF ⧸ H0.subgroupOf MF)} {g h : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g)
    (hRS : quotientSubgroupConjugateByElement MF H0 R S h) :
    quotientSubgroupConjugateByElement MF H0 Q S (g * h) := by
  rcases hQR with ⟨hconjG, actionG, hactionG, hR⟩
  rcases hRS with ⟨hconjH, actionH, hactionH, hS⟩
  let hconjGH : ∀ k : MF, (g * h)⁻¹ * (k : G) * (g * h) ∈ MF := by
    intro k
    have hmem := hconjH ⟨g⁻¹ * (k : G) * g, hconjG k⟩
    simpa [mul_assoc] using hmem
  refine ⟨hconjGH, actionG.trans actionH, ?_, ?_⟩
  · intro k
    calc
      (actionG.trans actionH) (QuotientGroup.mk' (H0.subgroupOf MF) k) =
          actionH (actionG (QuotientGroup.mk' (H0.subgroupOf MF) k)) := rfl
      _ = actionH (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (k : G) * g, hconjG k⟩) := by
          rw [hactionG k]
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨h⁻¹ * (g⁻¹ * (k : G) * g) * h,
              hconjH ⟨g⁻¹ * (k : G) * g, hconjG k⟩⟩ := by
          exact hactionH ⟨g⁻¹ * (k : G) * g, hconjG k⟩
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(g * h)⁻¹ * (k : G) * (g * h), hconjGH k⟩ := by
          congr 1
          apply Subtype.ext
          group
  · calc
      S = R.map actionH.toMonoidHom := hS
      _ = (Q.map actionG.toMonoidHom).map actionH.toMonoidHom := by rw [hR]
      _ = Q.map (actionG.trans actionH).toMonoidHom := by
          rw [Subgroup.map_map]
          rfl

public theorem quotientSubgroupConjugateByElement_target_eq_of_same_element_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R S : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g)
    (hQS : quotientSubgroupConjugateByElement MF H0 Q S g) :
    R = S := by
  rcases hQR with ⟨hconjMF_R, actionR, hactionR, hR⟩
  rcases hQS with ⟨hconjMF_S, actionS, hactionS, hS⟩
  have haction : actionR = actionS := by
    ext x
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨m, rfl⟩
    calc
      actionR (QuotientGroup.mk' (H0.subgroupOf MF) m) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (m : G) * g, hconjMF_R m⟩ := hactionR m
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (m : G) * g, hconjMF_S m⟩ := by
            congr 1
      _ = actionS (QuotientGroup.mk' (H0.subgroupOf MF) m) := (hactionS m).symm
  calc
    R = Q.map actionR.toMonoidHom := hR
    _ = Q.map actionS.toMonoidHom := by rw [haction]
    _ = S := hS.symm

public theorem quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hw0Q : quotientSubgroupConjugateByElement MF H0 Q Q (w0 : G)) :
    quotientSubgroupNormalizedBy MF H0 W1 Q := by
  let N : Subgroup W1 :=
    { carrier := {w | quotientSubgroupConjugateByElement MF H0 Q Q (w : G)}
      one_mem' := by
        simpa using
          quotientSubgroupConjugateByElement_one_sec9
            (MF := MF) (H0 := H0) (Q := Q)
      mul_mem' := by
        intro a b ha hb
        simpa using
          quotientSubgroupConjugateByElement_trans_sec9 ha hb
      inv_mem' := by
        intro a ha
        simpa using
          quotientSubgroupConjugateByElement_symm_sec9 ha }
  intro w
  have hw0N : w0 ∈ N := by
    simpa [N] using hw0Q
  have hwmem : w ∈ Subgroup.zpowers w0 := by
    rw [hw0gen]
    exact Subgroup.mem_top w
  have hwN : w ∈ N :=
    (Subgroup.zpowers_le_of_mem hw0N) hwmem
  simpa [N] using hwN

public theorem subgroup_ne_bot_of_prime_card_sec9
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p)
    (Q : Subgroup G) (hQcard : Nat.card Q = p) :
    Q ≠ ⊥ := by
  intro hQbot
  have hcard : Nat.card Q = 1 := by
    rw [hQbot]
    exact Subgroup.card_bot
  exact hp.ne_one (hQcard.symm.trans hcard)

public theorem iSupIndep_subgroups_injective_of_prime_card_sec9
    {G : Type u} [Group G] [Finite G]
    {ι : Type v} [DecidableEq ι]
    {p : ℕ} (hp : Nat.Prime p)
    (H : ι → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H) :
    Function.Injective H := by
  intro i j hij
  by_contra hne
  have hji : j ≠ i := by
    intro hji
    exact hne hji.symm
  have hleRest : H j ≤ (⨆ k, ⨆ _ : k ≠ i, H k) := by
    exact le_iSup_of_le j (le_iSup_of_le hji le_rfl)
  have hmeet : H i ⊓ H j = ⊥ := by
    have hdisj := (iSupIndep_def.mp hHindep i)
    apply le_bot_iff.mp
    calc
      H i ⊓ H j ≤ H i ⊓ (⨆ k, ⨆ _ : k ≠ i, H k) :=
        inf_le_inf_left _ hleRest
      _ = ⊥ := disjoint_iff.mp hdisj
  have hHi_bot : H i = ⊥ := by
    calc
      H i = H i ⊓ H j := by rw [hij, inf_idem]
      _ = ⊥ := hmeet
  exact subgroup_ne_bot_of_prime_card_sec9 hp (H i) (hHcard i) hHi_bot

public theorem theorem_9_8_base_not_W1_normalized_of_case_a_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a) :
    ¬ quotientSubgroupNormalizedBy MF H0 W1 (H ⟨0, hqpos⟩) := by
  classical
  rcases hcase with
    ⟨h92, _hH0MF, _hC, hpprime, hqprime, hpDataFull, _hdecomp,
      hquotCard, _hadiv, _hbarU⟩
  rcases hpDataFull with ⟨hp, _hp_eq, hpData, h96⟩
  let Q : Subgroup (MF ⧸ H0.subgroupOf MF) := H ⟨0, hqpos⟩
  have hQnormU : quotientSubgroupNormalizedBy MF H0 U Q := by
    dsimp [Q]
    exact hHnorm ⟨0, hqpos⟩
  have hQneBot : Q ≠ ⊥ := by
    exact subgroup_ne_bot_of_prime_card_sec9 hpprime Q (by
      simpa [Q] using hHcard ⟨0, hqpos⟩)
  have hQneTop : Q ≠ ⊤ := by
    intro hQtop
    have hcardTop : Nat.card Q = Nat.card (MF ⧸ H0.subgroupOf MF) := by
      calc
        Nat.card Q = Nat.card (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) := by
          rw [hQtop]
        _ = Nat.card (MF ⧸ H0.subgroupOf MF) := Subgroup.card_top
    have hp_eq_pow : p = p ^ q := by
      rw [show Nat.card Q = p by simpa [Q] using hHcard ⟨0, hqpos⟩,
        hquotCard] at hcardTop
      exact hcardTop
    have hpow_gt : p < p ^ q := by
      simpa using Nat.pow_lt_pow_right hpprime.one_lt hqprime.one_lt
    exact (Nat.ne_of_lt hpow_gt) hp_eq_pow
  exact
    quotientSubgroup_not_W1_normalized_of_proper_U_normalized_quotientChiefFactorData_sec9
      M MF U W1 W2 H0 q hp
      h92 hpData h96 hnormalH0
      Q hQnormU hQneBot hQneTop

public theorem theorem_9_8_weak_orbit_nonidentity_moves_base_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a) :
    ∀ w : W1, w ≠ 1 →
      ∃ i : Fin q, i ≠ ⟨0, hqpos⟩ ∧
        quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
          (w : G) := by
  classical
  intro w hwne
  let base : Fin q := ⟨0, hqpos⟩
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hHinj : Function.Injective H :=
    iSupIndep_subgroups_injective_of_prime_card_sec9 hpprime H hHcard hHindep
  let v : Fin q → W1 := fun i => Classical.choose (hconjBase i)
  have hv : ∀ i : Fin q,
      quotientSubgroupConjugateByElement MF H0 (H base) (H i) (v i : G) := by
    intro i
    exact Classical.choose_spec (hconjBase i)
  have hvinj : Function.Injective v := by
    intro i j hij
    apply hHinj
    exact quotientSubgroupConjugateByElement_target_eq_of_same_element_sec9
      (hv i) (by simpa [v, hij] using hv j)
  letI : Fintype W1 := Fintype.ofFinite W1
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hcard_v : Fintype.card (Fin q) = Fintype.card W1 := by
    calc
      Fintype.card (Fin q) = q := Fintype.card_fin q
      _ = Nat.card W1 := h92.q_eq.symm
      _ = Fintype.card W1 := Nat.card_eq_fintype_card
  have hvsurj : Function.Surjective v := by
    letI : DecidableEq W1 := Classical.decEq W1
    by_contra hnot
    rw [Function.Surjective] at hnot
    push Not at hnot
    rcases hnot with ⟨w0, hw0⟩
    have hw0not : w0 ∉ (Finset.univ : Finset (Fin q)).image v := by
      intro hwmem
      rcases Finset.mem_image.mp hwmem with ⟨i, _hi, hiw⟩
      exact hw0 i hiw
    have hproper :
        (Finset.univ : Finset (Fin q)).image v ⊂ (Finset.univ : Finset W1) := by
      refine ⟨Finset.subset_univ _, ?_⟩
      intro hEq
      exact hw0not (hEq (Finset.mem_univ w0))
    have hlt :
        ((Finset.univ : Finset (Fin q)).image v).card <
          (Finset.univ : Finset W1).card :=
      Finset.card_lt_card hproper
    have himage :
        ((Finset.univ : Finset (Fin q)).image v).card = Fintype.card (Fin q) :=
      Finset.card_image_of_injective (Finset.univ : Finset (Fin q)) hvinj
    have huniv :
        (Finset.univ : Finset W1).card = Fintype.card W1 :=
      Finset.card_univ
    omega
  rcases hvsurj w with ⟨i, hiw⟩
  have hine : i ≠ base := by
    intro hibase
    have hself :
        quotientSubgroupConjugateByElement MF H0 (H base) (H base) (w : G) := by
      simpa [base, hibase, hiw.symm] using hv i
    have hW1prime : Nat.Prime (Nat.card W1) := by
      rw [h92.q_eq]
      exact case_9_7_a_q_prime_sec9 hcase
    have hwgen : Subgroup.zpowers w = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one hW1prime hwne
    exact
      theorem_9_8_base_not_W1_normalized_of_case_a_sec9
        H hqpos hHcard hHnorm hcase
        (quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
          w hwgen hself)
  exact ⟨i, by simpa [base] using hine, by simpa [hiw.symm, base] using hv i⟩

@[expose] public noncomputable def H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (base : Fin q)
    (E : ∀ j : Fin q, H base ≃* H j)
    (i : H0CLinearCandidateXmuRawIndex_sec9 p) :
    H0CLinearCandidateXthetaRawIndex_sec9.{u} p q :=
  ULift.up fun j =>
    (nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j)).symm
      ⟨((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).1.comp (E j).symm.toMonoidHom, by
        intro htriv
        exact ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).2 <| by
          ext x
          have hval := congrArg
            (fun χ : H j →* ℂˣ => χ ((E j) x)) htriv
          simpa [MonoidHom.comp_apply] using hval⟩

public theorem H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (base : Fin q)
    (E : ∀ j : Fin q, H base ≃* H j)
    (i : H0CLinearCandidateXmuRawIndex_sec9 p)
    (j : Fin q) :
    ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
        ((H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
          p q H hHcard base E i).down j)).1 =
      ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).1.comp (E j).symm.toMonoidHom := by
  simp [H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9]

public theorem H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_injective_sec9
    {G : Type u} [Group G] [Finite G] [IsMulCommutative G]
    (p q : ℕ)
    (H : Fin q → Subgroup G)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (base : Fin q)
    (E : ∀ j : Fin q, H base ≃* H j) :
    Function.Injective
      (H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
        p q H hHcard base E) := by
  intro i j hij
  let ebase := nonprincipalLinearCharacterEquivFin_sec9 (H base) p (hHcard base)
  have hcoord :
      (H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
        p q H hHcard base E i).down base =
      (H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
        p q H hHcard base E j).down base := by
    exact congrArg (fun f : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q =>
      f.down base) hij
  have hcomp :
      (ebase i).1.comp (E base).symm.toMonoidHom =
        (ebase j).1.comp (E base).symm.toMonoidHom := by
    have hcoordChar := congrArg
      (nonprincipalLinearCharacterEquivFin_sec9 (H base) p (hHcard base)) hcoord
    have hval := congrArg
      (fun χ : {χ : H base →* ℂˣ // χ ≠ 1} => χ.1) hcoordChar
    simpa [ebase,
      H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9]
      using hval
  have hbaseChar : ebase i = ebase j := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    have hval := congrArg (fun χ : H base →* ℂˣ => χ ((E base) x)) hcomp
    simpa [MonoidHom.comp_apply] using hval
  exact ebase.injective hbaseChar

public theorem H0CLinearCandidateXmuRawIndex_card_sec9 (p : ℕ) :
    Fintype.card (H0CLinearCandidateXmuRawIndex_sec9 p) = p - 1 := by
  simp [H0CLinearCandidateXmuRawIndex_sec9]


@[expose] public def H0CLinearCandidateXmuTransportedRawCoordinateOfConjData_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (p q : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) : Prop :=
  ∃ hqpos : 0 < q,
    let base : Fin q := ⟨0, hqpos⟩
    ∃ w : ∀ _j : Fin q, W,
      ∃ _hw : ∀ j : Fin q,
        quotientSubgroupConjugateByElement MF H0 (H base) (H j) (w j : G),
        ∃ E : ∀ j : Fin q, H base ≃* H j,
          (∀ j : Fin q,
            ∃ hconjMF : ∀ h : MF, (w j : G)⁻¹ * (h : G) * (w j : G) ∈ MF,
              ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H base,
                (E j ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                    MF ⧸ H0.subgroupOf MF) =
                  QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(w j : G)⁻¹ * (h : G) * (w j : G), hconjMF h⟩) ∧
            μraw =
              H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
                p q H hHcard base E


@[expose] public def H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (p q : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (w0 : W1)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) : Prop :=
  ∃ hqpos : 0 < q,
    let base : Fin q := ⟨0, hqpos⟩
    ∃ _hw : ∀ j : Fin q,
      quotientSubgroupConjugateByElement MF H0 (H base) (H j)
        ((w0 ^ j.1 : W1) : G),
      ∃ E : ∀ j : Fin q, H base ≃* H j,
        (∀ j : Fin q,
          ∃ hconjMF : ∀ h : MF,
            (((w0 ^ j.1 : W1) : G))⁻¹ * (h : G) *
                (((w0 ^ j.1 : W1) : G)) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H base,
              (E j ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(((w0 ^ j.1 : W1) : G))⁻¹ * (h : G) *
                      (((w0 ^ j.1 : W1) : G)), hconjMF h⟩) ∧
          μraw =
            H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
              p q H hHcard base E

public theorem
    H0CLinearCandidateXmuOrderedTransportedRawCoordinate_data_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (p q : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (w0 : W1)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    ∃ μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
        H0CLinearCandidateXthetaRawIndex_sec9.{u} p q,
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw ∧
        H0CLinearCandidateXmuTransportedRawCoordinateOfConjData_sec9
          (MF := MF) (H0 := H0) (W := W1) p q H hHcard μraw ∧
        Function.Injective μraw := by
  classical
  let base : Fin q := ⟨0, hqpos⟩
  have hw : ∀ j : Fin q,
      quotientSubgroupConjugateByElement MF H0 (H base) (H j)
        ((w0 ^ j.1 : W1) : G) := by
    intro j
    simpa [base] using
      theorem_9_7_successor_conjugates_pow_sec9 hqpos H w0 hsucc j.1 j.2
  choose E hE using fun j =>
    quotientSubgroupConjugateByElement_mulEquiv_sec9 (hw j)
  let μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q :=
    H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_sec9
      p q H hHcard base E
  refine ⟨μraw, ?_, ?_, ?_⟩
  · refine ⟨hqpos, hw, E, ?_, rfl⟩
    intro j
    simpa using hE j
  · let w : ∀ j : Fin q, W1 := fun j => w0 ^ j.1
    refine ⟨hqpos, w, ?_, E, ?_, rfl⟩
    · intro j
      exact hw j
    · intro j
      simpa [w] using hE j
  · exact
      H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_injective_sec9
        p q H hHcard base E

@[expose] public def H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
    {G : Type u} [Group G] [Finite G]
    {MF U W1 H0 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (p q aρ : ℕ)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) : Prop :=
  ∃ hW1normU : W1 ≤ Subgroup.normalizer (U : Set G),
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    ∃ w0 : W1,
      Subgroup.zpowers w0 = ⊤ ∧
        H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
          (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw ∧
        ∃ hqpos : 0 < q,
          (∀ i : Fin q,
            quotientSubgroupConjugateByElement MF H0
              (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) ∧
            ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →*
                Multiplicative (ZMod aρ),
              (∀ i, ∀ x y : U ⧸ C.subgroupOf U,
                χbar i x = χbar i y → ρ i x = ρ i y) ∧
                ∀ x : U,
                  ∀ i,
                    χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
                      χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
                        (QuotientGroup.mk' (C.subgroupOf U) x)


public theorem H0CLinearCandidateXmu_image_card_of_injective_withRaw_sec9
    (p : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι) :
    Function.Injective μorbit →
      (Finset.univ.image μorbit).card = p - 1 := by
  intro hinj
  rw [Finset.card_image_of_injective _ hinj]
  exact H0CLinearCandidateXmuRawIndex_card_sec9 p


@[expose] public def H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  Function.Injective μorbit ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inducedCF Dm (θ (μorbit i)) ∈
        reducibleCharacterFilter_sec9 M SH0C) ∧
    (∀ χ : Section1.ClassFunction M,
      χ ∈ reducibleCharacterFilter_sec9 M SH0C →
        ∃ i : H0CLinearCandidateXmuRawIndex_sec9 p,
          χ = Section1.inducedCF Dm (θ (μorbit i))) ∧
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ∀ j : ι, j ∉ Finset.univ.image μorbit →
        Section1.inducedCF Dm (θ (μorbit i)) ≠ Section1.inducedCF Dm (θ j)

@[expose] public def H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      μfinal i ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ∀ j : ι,
        μfinal i = Section1.inducedCF Dm (θ j) →
          j ∈ Finset.univ.image μorbit

@[expose] public def H0CLinearCandidateXmuSmuDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      μfinal i ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ∀ j : ι,
          μfinal i = Section1.inducedCF Dm (θ j) →
            j ∈ Finset.univ.image μorbit

@[expose] public def H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal

@[expose] public def H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) : Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  Function.Injective μfinal ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤) ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      μfinal i ∈ reducibleCharacterFilter_sec9 M SH0C) ∧
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ∀ j : ι,
        μfinal i = Section1.inducedCF Dm (θ j) →
          j ∈ Finset.univ.image μorbit

@[expose] public def H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  Function.Injective θ ∧
    (∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤) ∧
    ∀ i : ι,
      Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
        ¬ Section1.subgroupInKernel' (θ i)
          ((MF.subgroupOf M).subgroupOf Dm) ∧
        Section1.subgroupInKernel' (θ i)
          (((H0 ⊔ C).subgroupOf M).subgroupOf Dm)

@[expose] public def H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M _MF _H0 _C : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
    Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤

@[expose] public def H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M W1 : Subgroup G)
    (p : ℕ)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
    W1.subgroupOf M ≤ Section1.inertiaSubgroup Dm (θ (μorbit i))


public theorem inertiaSubgroup_eq_top_of_isComplement'_le_sec9
    {G : Type u} [Group G]
    (H W : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθ : Section1.IsClassFunction θ)
    (hcomp : H.IsComplement' W)
    (hW : W ≤ Section1.inertiaSubgroup H θ) :
    Section1.inertiaSubgroup H θ = ⊤ := by
  apply le_antisymm le_top
  intro g _hg
  rcases hcomp.2 g with ⟨⟨h, w⟩, hgw⟩
  have hHleI : H ≤ Section1.inertiaSubgroup H θ :=
    Section1.proposition_1_7_inertia_contains_H H θ hθ
  have hhI : (h : G) ∈ Section1.inertiaSubgroup H θ :=
    hHleI h.property
  have hwI : (w : G) ∈ Section1.inertiaSubgroup H θ :=
    hW w.property
  have hmulI : (h : G) * (w : G) ∈ Section1.inertiaSubgroup H θ :=
    (Section1.inertiaSubgroup H θ).mul_mem hhI hwI
  simpa [hgw] using hmulI

public theorem subgroupOf_le_inertiaSubgroup_of_zpowers_generator_mem_sec9
    {G : Type u} [Group G]
    {M W1 : Subgroup G}
    (H : Subgroup M) [H.Normal]
    (θ : Section1.ClassFunction H)
    (w0 : W1)
    (hW1M : W1 ≤ M)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hw0I : (⟨(w0 : G), hW1M w0.property⟩ : M) ∈
      Section1.inertiaSubgroup H θ) :
    W1.subgroupOf M ≤ Section1.inertiaSubgroup H θ := by
  let f : W1 →* M :=
    { toFun := fun w => ⟨(w : G), hW1M w.property⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro x y
        ext
        rfl }
  have hw0pre :
      w0 ∈ (Section1.inertiaSubgroup H θ).comap f := by
    simpa [f] using hw0I
  have htop_le : (⊤ : Subgroup W1) ≤
      (Section1.inertiaSubgroup H θ).comap f := by
    rw [← hw0gen]
    exact Subgroup.zpowers_le_of_mem hw0pre
  intro x hx
  let xW1 : W1 := ⟨(x : G), hx⟩
  have hxpre : xW1 ∈ (Section1.inertiaSubgroup H θ).comap f :=
    htop_le trivial
  have hfx : f xW1 = x := by
    ext
    rfl
  simpa [hfx] using hxpre


public theorem induced_eq_imp_conjugateOrbitConj_for_xmu_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {φ θ : Section1.ClassFunction H}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hInd : Section1.inducedCF H φ = Section1.inducedCF H θ) :
    ∃ i : Section1.conjugateOrbitIndex H θ,
      φ = Section1.conjugateOrbitConj H θ i := by
  classical
  rcases hφ with ⟨nφ, φRep, hφirr, hφeq⟩
  rcases hθ with ⟨nθ, θRep, hθirr, hθeq⟩
  subst φ
  subst θ
  exact Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
    H φRep θRep hφirr hθirr hInd

public theorem conjugateOrbitConj_eq_self_of_inertia_top_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H)
    (hI : Section1.inertiaSubgroup H θ = ⊤)
    (i : Section1.conjugateOrbitIndex H θ) :
    Section1.conjugateOrbitConj H θ i = θ := by
  refine Quotient.inductionOn i ?_
  intro g
  have hg : g ∈ Section1.inertiaSubgroup H θ := by
    rw [hI]
    trivial
  change Section1.conjugateOnNormal H θ g = θ
  simpa [Section1.inertiaSubgroup] using hg


public theorem H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (∀ i : ι, Section1.IsClassFunction (θ i)) →
        H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p
            ι μorbit θ →
          H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C
            p ι μorbit θ := by
  intro hcase hθclass hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  dsimp [H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9] at hdata
  have hcomp : Dm.IsComplement' (W1.subgroupOf M) := by
    dsimp [Dm]
    exact ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  intro i
  exact inertiaSubgroup_eq_top_of_isComplement'_le_sec9
    Dm (W1.subgroupOf M) (θ (μorbit i)) (hθclass (μorbit i)) hcomp
    (by simpa [Dm] using hdata i)

public theorem H0CLinearCandidateXmu_final_inertia_membership_withRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M))
    (hSH0C : kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C)
    (hθdata :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf
              ((ambientDerivedSubgroup M).subgroupOf M))) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      Section1.inducedCF Dm (θ (μorbit i)) ∈ SH0C := by
  intro Dm i
  rcases hSH0C with ⟨_hYle, _hMFle, hmem⟩
  rw [hmem]
  exact ⟨θ (μorbit i), (hθdata (μorbit i)).1,
    (hθdata (μorbit i)).2.1, (hθdata (μorbit i)).2.2, rfl⟩

public theorem H0CLinearCandidateXmu_final_inertia_not_irreducible_withRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι}
    {θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)}
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hθirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (θ i))
    (hfinalInertia :
      let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
      let hDnormal : Dm.Normal := by
        simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
      letI : Dm.Normal := hDnormal
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        Section1.inertiaSubgroup Dm (θ (μorbit i)) = ⊤) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF Dm (θ (μorbit i))) := by
  classical
  intro Dm i hIndIrr
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  rcases hθirr (μorbit i) with ⟨n, ρ, hρirr, hθeq⟩
  have hnormInd :
      Section1.scalarProduct M
          (Section1.inducedCF Dm (θ (μorbit i)))
          (Section1.inducedCF Dm (θ (μorbit i))) =
        (Subgroup.index Dm : ℕ) := by
    have hnormρ :
        Section1.scalarProduct M
            (Section1.inducedCF Dm ρ.character)
            (Section1.inducedCF Dm ρ.character) =
          Dm.relIndex (Section1.inertiaSubgroup Dm ρ.character) :=
      Section1.proposition_1_5_b_rep_orbit_relIndex_canonical Dm ρ hρirr
    have hIρ :
        Section1.inertiaSubgroup Dm ρ.character = ⊤ := by
      simpa [hθeq, Dm] using hfinalInertia i
    simpa [hθeq, hIρ, Subgroup.relIndex_top_right] using hnormρ
  have hnormIrr :
      Section1.scalarProduct M
          (Section1.inducedCF Dm (θ (μorbit i)))
          (Section1.inducedCF Dm (θ (μorbit i))) = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self hIndIrr
  have hindex_eq_one : Subgroup.index Dm = 1 := by
    exact_mod_cast hnormInd.symm.trans hnormIrr
  have hqeq : Subgroup.index Dm = q := by
    simpa [Dm] using
      ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  have hqone : q = 1 := hqeq.symm.trans hindex_eq_one
  exact (case_9_7_a_q_prime_sec9 hcase).ne_one hqone

public theorem H0CLinearCandidateXmuSmuCoreDataWithRaw_of_finalInertiaData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
        H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
            ι μorbit θ →
          H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p
              ι μorbit θ →
            H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p
              SH0C ι μorbit θ := by
  classical
  intro hcase hSH0C hdata hfinalInj
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9] at hdata
  dsimp [H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9] at hfinalInj
  rcases hdata with ⟨hθinj, hfinalInertia, hθdata⟩
  have hSHmem :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        Section1.inducedCF Dm (θ (μorbit i)) ∈ SH0C := by
    simpa [Dm] using
      H0CLinearCandidateXmu_final_inertia_membership_withRaw_sec9
        M MF H0 C p SH0C μorbit θ hSH0C hθdata
  have hnotIrr :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ¬ Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF Dm (θ (μorbit i))) := by
    simpa [Dm] using
      H0CLinearCandidateXmu_final_inertia_not_irreducible_withRaw_sec9
        M MF U W1 W2 H0 C p q a hcase (fun i => (hθdata i).1)
        (by simpa [Dm] using hfinalInertia)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [μfinal, Dm] using hfinalInj
  · intro i
    exact hfinalInertia i
  · intro i
    have hpair :
        Section1.inducedCF Dm (θ (μorbit i)) ∈ SH0C ∧
          ¬ Section1.IsIrreducibleCharacterOnGroup
            (Section1.inducedCF Dm (θ (μorbit i))) :=
      ⟨hSHmem i, hnotIrr i⟩
    simpa [μfinal, reducibleCharacterFilter_sec9, Dm] using hpair
  · intro i j hij
    have hInd :
        Section1.inducedCF Dm (θ j) =
          Section1.inducedCF Dm (θ (μorbit i)) := by
      simpa [μfinal, Dm] using hij.symm
    rcases induced_eq_imp_conjugateOrbitConj_for_xmu_sec9
        Dm (hθdata j).1 (hθdata (μorbit i)).1 hInd with
      ⟨o, ho⟩
    have hconjSelf :
        Section1.conjugateOrbitConj Dm (θ (μorbit i)) o = θ (μorbit i) :=
      conjugateOrbitConj_eq_self_of_inertia_top_sec9
        Dm (θ (μorbit i)) (hfinalInertia i) o
    have hθeq : θ j = θ (μorbit i) := ho.trans hconjSelf
    refine Finset.mem_image.mpr ⟨i, by simp, ?_⟩
    exact (hθinj hθeq).symm

public theorem H0CLinearCandidateXmuFinalInjectiveDataWithRaw_of_finalInertiaData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Function.Injective μorbit →
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
          ι μorbit θ →
        H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p
          ι μorbit θ := by
  classical
  intro hμinj hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9] at hdata
  dsimp [H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9]
  rcases hdata with ⟨hθinj, hfinalInertia, hθdata⟩
  intro i j hij
  have hInd :
      Section1.inducedCF Dm (θ (μorbit i)) =
        Section1.inducedCF Dm (θ (μorbit j)) := by
    simpa [μfinal, Dm] using hij
  rcases induced_eq_imp_conjugateOrbitConj_for_xmu_sec9
      Dm (hθdata (μorbit i)).1 (hθdata (μorbit j)).1 hInd with
    ⟨o, ho⟩
  have hconjSelf :
      Section1.conjugateOrbitConj Dm (θ (μorbit j)) o = θ (μorbit j) :=
    conjugateOrbitConj_eq_self_of_inertia_top_sec9
      Dm (θ (μorbit j)) (hfinalInertia j) o
  have hθeq : θ (μorbit i) = θ (μorbit j) := ho.trans hconjSelf
  exact hμinj (hθinj hθeq)

public theorem H0CLinearCandidateXmuSmuDataWithRaw_of_coreData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ →
      H0CLinearCandidateXmuSmuDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ := by
  classical
  intro hcore
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9] at hcore
  rcases hcore with ⟨hfinalInj, _hfinalInertia, hfinalRed, hfinalEqMem⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact hfinalInj (by simpa [μfinal, Dm] using hij)
  · intro i
    simpa [μfinal, Dm] using hfinalRed i
  · intro i j hij
    exact hfinalEqMem i j (by simpa [μfinal, Dm] using hij)

public theorem H0CLinearCandidateXmuFinalSeparationDataWithRaw_of_smuData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    H0CLinearCandidateXmuSmuDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ →
      H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ := by
  intro h
  simpa [H0CLinearCandidateXmuSmuDataWithRaw_sec9,
    H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9] using h

public theorem H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_of_final_separation_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 →
      H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9 M MF H0 C p
          SH0C ι μorbit θ →
        H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9 M MF H0 C p
          SH0C ι μorbit θ := by
  classical
  intro hredCard hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let μfinal : H0CLinearCandidateXmuRawIndex_sec9 p → Section1.ClassFunction M :=
    fun i => Section1.inducedCF Dm (θ (μorbit i))
  dsimp [H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9] at hdata
  rcases hdata with ⟨hfinalInj, hfinalRed, hfinalEqMem⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply hfinalInj
    simpa [μfinal, Dm] using
      congrArg (fun t : ι => Section1.inducedCF Dm (θ t)) hij
  · intro i
    simpa [μfinal, Dm] using hfinalRed i
  · intro χ hχred
    let Smu : Finset (Section1.ClassFunction M) := Finset.univ.image μfinal
    have hSmuSub : Smu ⊆ reducibleCharacterFilter_sec9 M SH0C := by
      intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
      simpa [μfinal, Dm] using hfinalRed i
    have hSmuCard : Smu.card = p - 1 := by
      rw [Finset.card_image_of_injective _ hfinalInj]
      exact H0CLinearCandidateXmuRawIndex_card_sec9 p
    have hSmuEq :
        Smu = reducibleCharacterFilter_sec9 M SH0C :=
      Finset.eq_of_subset_of_card_le hSmuSub (by rw [hredCard, hSmuCard])
    have hχSmu : χ ∈ Smu := by
      rw [hSmuEq]
      exact hχred
    rcases Finset.mem_image.mp hχSmu with ⟨i, _hi, hiχ⟩
    exact ⟨i, hiχ.symm⟩
  · intro i j hj hijeq
    exact hj (hfinalEqMem i j (by simpa [μfinal, Dm] using hijeq))

public theorem H0CLinearCandidateXmuFinalImageData_of_concrete_final_image_withRaw_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF H0 C : Subgroup G)
    (p : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ →
      H0CLinearCandidateXmuFinalImageData_sec9 M MF H0 C p SH0C ι θ := by
  classical
  intro hdata
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let Xmu : Finset ι := Finset.univ.image μorbit
  dsimp [H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9] at hdata
  rcases hdata with ⟨hinj, hred, hcover, hsep⟩
  refine ⟨Xmu, ?_, ?_, ?_, ?_⟩
  · simpa [Xmu] using
      H0CLinearCandidateXmu_image_card_of_injective_withRaw_sec9 p μorbit hinj
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, _hj, rfl⟩
    simpa [Dm] using hred j
  · intro χ hχ
    rcases hcover χ hχ with ⟨i, hχeq⟩
    refine ⟨μorbit i, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    · simpa [Dm] using hχeq
  · intro i hi j hj hijeq
    rcases Finset.mem_image.mp hi with ⟨k, _hk, rfl⟩
    exact hsep k j (by simpa [Xmu] using hj) (by
      simpa [Dm] using hijeq)


@[expose] public def H0CLinearCandidateXthetaThetaCoordinateActionData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U _H0 C : Subgroup G)
    (p q ubar : ℕ)
    (ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) : Prop :=
  let κ : Type u := ULift.{u, 0} (Fin q → Fin (p - 1))
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  ∃ hnormalC : (C.subgroupOf U).Normal,
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ instAction : MulAction (U ⧸ C.subgroupOf U) κ,
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      (∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥) ∧
        Nat.card (U ⧸ C.subgroupOf U) = ubar ∧
        ∀ hnormalHCD : HCD.Normal,
          letI : HCD.Normal := hnormalHCD
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
          (∀ k : κ,
            Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
              HCD) ∧
            ∀ k l : κ,
              θ k = θ l ↔
                MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l

@[expose] public def H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U _H0 C : Subgroup G)
    (p q : ℕ)
    (ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) : Prop :=
  let κ : Type u := ULift.{u, 0} (Fin q → Fin (p - 1))
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  ∃ hnormalC : (C.subgroupOf U).Normal,
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ instAction : MulAction (U ⧸ C.subgroupOf U) κ,
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      (∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥) ∧
        ∀ hnormalHCD : HCD.Normal,
          letI : HCD.Normal := hnormalHCD
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
          (∀ k : κ,
            Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
              HCD) ∧
            ∀ k l : κ,
              θ k = θ l ↔
                MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l

@[expose] public def H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U _H0 C : Subgroup G)
    (p q ubar : ℕ)
    (ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) : Prop :=
  let κ : Type u := ULift.{u, 0} (Fin q → Fin (p - 1))
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  ∃ hnormalC : (C.subgroupOf U).Normal,
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ instAction : MulAction (U ⧸ C.subgroupOf U) κ,
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      (∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥) ∧
        Nat.card (U ⧸ C.subgroupOf U) = ubar ∧
        ∀ hnormalHCD : HCD.Normal,
          letI : HCD.Normal := hnormalHCD
          let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
          let ψ : ι → Section1.ClassFunction HCm :=
            fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
          let θ : ι → Section1.ClassFunction Dm :=
            fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
          Function.Injective θ ∧
            ∀ i : ι,
              Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD


public theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_of_core_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C : Subgroup G)
    (p q ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    quotientBarUCardinality U C ubar →
      H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
        M MF U H0 C p q ψHC →
        H0CLinearCandidateXthetaThetaCoordinateActionData_sec9
          M MF U H0 C p q ubar ψHC := by
  intro hBarU hcore
  rcases hBarU with ⟨_hCU, hnormalBarC, hbarCard⟩
  rcases hcore with ⟨hnormalC, instAction, hstab, hcoord⟩
  refine ⟨hnormalC, instAction, hstab, ?_, hcoord⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  simpa using hbarCard

public theorem isIrreducible_subgroupOfClassFunction_sec9
    {G : Type u} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T)
    {θ : Section1.ClassFunction H}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.subgroupOfClassFunction (T := T) θ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let e : H.subgroupOf T ≃* H := Subgroup.subgroupOfEquivOfLe hHT
  let ρH : Representation ℂ (H.subgroupOf T) (Fin n → ℂ) :=
    ρ.comp e.toMonoidHom
  refine ⟨n, ρH, ?_, ?_⟩
  · exact (Section6.representation_isIrreducible_comp_surjective
      ρ e.toMonoidHom e.surjective hρirr)
  · ext h
    simp [ρH, e, Section1.subgroupOfClassFunction, hθeq,
      Representation.character, Subgroup.subgroupOfEquivOfLe]

public theorem subgroupInKernel'_subgroupOfClassFunction_sec9
    {G : Type u} [Group G] {H T A : Subgroup G}
    (_hAT : A ≤ T) (hAH : A ≤ H)
    {θ : Section1.ClassFunction H}
    (hθker : Section1.subgroupInKernel' θ (A.subgroupOf H)) :
    Section1.subgroupInKernel'
      (Section1.subgroupOfClassFunction (T := T) θ)
        ((A.subgroupOf T).subgroupOf (H.subgroupOf T)) := by
  intro a
  have haA : (((a : H.subgroupOf T) : T) : G) ∈ A := by
    have haAT : ((a : H.subgroupOf T) : T) ∈ A.subgroupOf T :=
      (a : (A.subgroupOf T).subgroupOf (H.subgroupOf T)).property
    simpa [Subgroup.mem_subgroupOf] using haAT
  let aH : A.subgroupOf H := ⟨⟨(((a : H.subgroupOf T) : T) : G), hAH haA⟩, by
    simpa [Subgroup.mem_subgroupOf] using haA⟩
  have ha := hθker aH
  simpa [Section1.subgroupOfClassFunction, aH,
    Section1.degree_subgroupOfClassFunction]
    using ha

public theorem subgroupInKernel'_of_subgroupOfClassFunction_sec9
    {G : Type u} [Group G] {H T A : Subgroup G}
    (hAT : A ≤ T) (_hAH : A ≤ H)
    {θ : Section1.ClassFunction H}
    (hθker : Section1.subgroupInKernel'
      (Section1.subgroupOfClassFunction (T := T) θ)
        ((A.subgroupOf T).subgroupOf (H.subgroupOf T))) :
    Section1.subgroupInKernel' θ (A.subgroupOf H) := by
  intro a
  have haA : ((a : H) : G) ∈ A := by
    exact (a : A.subgroupOf H).property
  let aT : H.subgroupOf T := ⟨⟨((a : H) : G), hAT haA⟩, by
    exact (a : H).property⟩
  have haT : (aT : T) ∈ A.subgroupOf T := by
    simpa [aT, Subgroup.mem_subgroupOf] using haA
  let aHT : (A.subgroupOf T).subgroupOf (H.subgroupOf T) := ⟨aT, haT⟩
  have ha := hθker aHT
  simpa [aT, aHT, Section1.subgroupOfClassFunction,
    Section1.degree_subgroupOfClassFunction] using ha

public theorem inducedCF_isIrreducible_of_inertia_eq_self_sec9
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    {X : Section1.ClassFunction K}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup X)
    (hIeq : Section1.inertiaSubgroup K X = K) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) := by
  rcases hXirr with ⟨n, ρ, hρirr, hXeq⟩
  have hIeqρ :
      Section1.inertiaSubgroup K ρ.character = K := by
    simpa [hXeq] using hIeq
  have hrel :
      K.relIndex (Section1.inertiaSubgroup K ρ.character) = 1 := by
    rw [hIeqρ]
    simp [Subgroup.relIndex]
  simpa [hXeq] using
    Section1.proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical
      K ρ hρirr hrel

public theorem inertiaSubgroup_eq_of_semidirect_no_nontrivial_complement_fixed_sec9
    {L : Type u} [Group L] [Finite L]
    (K W : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    {X : Section1.ClassFunction K}
    (hXclass : Section1.IsClassFunction X)
    (hnoFix :
      ∀ g : L, g ∈ W → g ≠ 1 →
        Section1.conjugateOnNormal K X g ≠ X) :
    Section1.inertiaSubgroup K X = K := by
  have hKleI : K ≤ Section1.inertiaSubgroup K X := by
    intro x hx
    change Section1.conjugateOnNormal K X x = X
    funext h
    unfold Section1.conjugateOnNormal
    change X ((⟨x, hx⟩ : K) * h * (⟨x, hx⟩ : K)⁻¹) = X h
    exact hXclass ⟨x, hx⟩ h
  apply le_antisymm
  · intro g hgI
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hkK, w, hwW, hkw⟩
    have hkI : k ∈ Section1.inertiaSubgroup K X := hKleI hkK
    have hwI : w ∈ Section1.inertiaSubgroup K X := by
      have :
          k⁻¹ * g ∈ Section1.inertiaSubgroup K X :=
        (Section1.inertiaSubgroup K X).mul_mem
          ((Section1.inertiaSubgroup K X).inv_mem hkI) hgI
      simpa [hkw, mul_assoc] using this
    have hw1 : w = 1 := by
      by_contra hwne
      have hfixw : Section1.conjugateOnNormal K X w = X := by
        simpa [Section1.inertiaSubgroup] using hwI
      exact hnoFix w hwW hwne hfixw
    have hgk : g = k := by
      calc
        g = k * w := hkw
        _ = k := by simp [hw1]
    simpa [hgk] using hkK
  · exact hKleI

public theorem inducedCF_isIrreducible_of_semidirect_no_nontrivial_complement_fixed_sec9
    {L : Type u} [Group L] [Finite L]
    (K W : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    {X : Section1.ClassFunction K}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup X)
    (hnoFix :
      ∀ g : L, g ∈ W → g ≠ 1 →
        Section1.conjugateOnNormal K X g ≠ X) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) := by
  rcases hXirr with ⟨n, ρ, hρirr, rfl⟩
  have hXclass : Section1.IsClassFunction ρ.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hIeq :
      Section1.inertiaSubgroup K ρ.character = K :=
    inertiaSubgroup_eq_of_semidirect_no_nontrivial_complement_fixed_sec9
      K W hsemi hXclass hnoFix
  exact inducedCF_isIrreducible_of_inertia_eq_self_sec9 K
    ⟨n, ρ, hρirr, rfl⟩ hIeq

public theorem subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {θ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (A.subgroupOf K)) :
    Section1.subgroupInKernel' (Section1.inducedCF K θ) A := by
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hρker : Section1.subgroupInKernel' ρ.character (A.subgroupOf K) := by
    simpa [hθeq] using hθker
  have hindKer : Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) A :=
    (Section1.proposition_1_6_a K A hAK ρ).mp hρker
  simpa [hθeq] using hindKer

public theorem subgroupInKernel'_of_inducedCF_sec9
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {θ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' (Section1.inducedCF K θ) A) :
    Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hindKer :
      Section1.subgroupInKernel' (Section1.inducedCF K ρ.character) A := by
    simpa [hθeq] using hθker
  have hρker : Section1.subgroupInKernel' ρ.character (A.subgroupOf K) :=
    (Section1.proposition_1_6_a K A hAK ρ).mpr hindKer
  simpa [hθeq] using hρker

public theorem subgroupInKernel'_sup_of_irreducible_sec9
    {L : Type u} [Group L] [Finite L]
    {θ : Section1.ClassFunction L} {A B : Subgroup L}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hA : Section1.subgroupInKernel' θ A)
    (hB : Section1.subgroupInKernel' θ B) :
    Section1.subgroupInKernel' θ (A ⊔ B) := by
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  subst θ
  have hAker : Section1.subgroupInRepresentationKernel ρ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ A).mp hA
  have hBker : Section1.subgroupInRepresentationKernel ρ B :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ B).mp hB
  let K : Subgroup L :=
    { carrier := {g | ρ g = 1}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change ρ (x * y) = 1
        rw [map_mul, hx, hy, one_mul]
      inv_mem' := by
        intro x hx
        change ρ x = 1 at hx
        change ρ (x⁻¹) = 1
        have hmul : ρ (x⁻¹) * ρ x = 1 := by
          rw [← map_mul]
          simp
        rw [hx] at hmul
        simpa using hmul }
  have hAK : A ≤ K := by
    intro x hx
    exact hAker ⟨x, hx⟩
  have hBK : B ≤ K := by
    intro x hx
    exact hBker ⟨x, hx⟩
  have hsupK : A ⊔ B ≤ K := sup_le hAK hBK
  apply (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
    ρ (A ⊔ B)).mpr
  intro x
  exact hsupK x.property



end CFSG.Section9
