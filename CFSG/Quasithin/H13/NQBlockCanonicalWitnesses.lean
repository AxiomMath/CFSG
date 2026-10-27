module

public import CFSG.Quasithin.H13.NQBlockCanonicalResidual
public import CFSG.Quasithin.SteinbergCCSylowCoreResidual

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement Pointwise

theorem critical_whole_shape {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] {r : ℕ}
    [hr : Fact r.Prime] (hr2 : r ≠ 2) (hodd : Odd (Nat.card (CFSG.fittingSubgroup L)))
    (hQL : ⁅CFSG.pCore r L, (⊤ : Subgroup L)⁆ = CFSG.pCore r L)
    (D : Subgroup (CFSG.pCore r L)) [D.Characteristic] (hD : IsCriticalData r (CFSG.pCore r L) D)
    (hker : (criticalAction D).ker = CFSG.fittingSubgroup L) :
    (¬ IsMulCommutative D → D = ⊤) ∧
      (IsElementaryAbelian r D → IsMulCommutative (CFSG.pCore r L) ∧
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (CFSG.pCore r L ≃*
          Multiplicative (ZMod (r ^ a)) × Multiplicative (ZMod (r ^ a)))) ∧
        D = CFSG.omega₁ (CFSG.pCore r L) (p := r)) := by
  have hQF : CFSG.pCore r L ≤ CFSG.fittingSubgroup L := CFSG.pCore_le_fitting L r
  have hQH := closure_conj_eq_top_of_commutator_eq hQL
  have hirr : ∀ U : Subgroup (D ⧸ frattini D), Nat.card U = r →
      ∃ h : L, ∃ u ∈ U, frattiniAction D (MulAut.conjNormal h) u ∉ U := by
    intro U hU
    obtain ⟨g, ⟨l, rfl⟩, u, hu, hgu⟩ := hD.irreducible U hU
    exact ⟨l, u, hu, hgu⟩
  have hQtriv : ∀ q : CFSG.pCore r L, frattiniAction D (MulAut.conj q) = 1 := by
    intro q
    rw [conj_eq_conjNormal]
    have h1 : (q : L) ∈ (criticalAction D).ker := by
      rw [hker]
      exact hQF q.2
    exact h1
  have ht : ∃ t : L, orderOf t = 2 ∧ ∀ w, frattiniAction D (MulAut.conjNormal t) w = w⁻¹ := by
    obtain ⟨g, hg, hg1, hginv⟩ := hD.inv_mem
    have hg2 : g * g = 1 := MulEquiv.ext fun w => by
      rw [MulAut.mul_apply, hginv, hginv, inv_inv, MulAut.one_apply]
    have hodd' : Odd (Nat.card (criticalAction D).ker) := by
      rw [hker]
      exact hodd
    obtain ⟨t, ht2, htg⟩ := exists_involution_preimage (criticalAction D) hodd' hg hg1 hg2
    refine ⟨t, ht2, fun w => ?_⟩
    have h1 : criticalAction D t = frattiniAction D (MulAut.conjNormal t) := rfl
    rw [← h1, htg, hginv]
  have hshapeD : (IsElementaryAbelian r D ∧ Nat.card D = r ^ 2) ∨
      (¬ IsMulCommutative D ∧ Nat.card D = r ^ 3 ∧ (∀ x ∈ D, x ^ r = 1) ∧
        frattini D = center D ∧ Nat.card (frattini D) = r) := by
    rcases hD.shape with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, hD.pow_eq_one, h3, h4⟩
  exact supercritical_whole_pgroup_shape hr2 CFSG.pCore_isPGroup MulAut.conjNormal D hQH
    hD.torsion hshapeD hirr hQtriv ht

theorem canonical_prime_data {M : Type*} [Group M] [Finite M]
    (hSQT : CFSG.IsStronglyQuasithin M) (hO2 : CFSG.pCore 2 M = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup M)) (hq : ¬ CFSG.IsQuasisimple M) {q : ℕ}
    [hqp : Fact q.Prime] (hqF : q ∈ (Nat.card (CFSG.fittingSubgroup M)).primeFactors)
    (D : Subgroup M) (hD : D = closure {a | a ∈ CFSG.pCore q M ∧ a ^ q = 1}) :
    5 ≤ q ∧ ∃ _ : D.Characteristic, IsPGroup q D ∧ (∀ d ∈ D, d ^ q = 1) ∧ D ≠ ⊥ ∧
      CFSG.pRank q D = 2 ∧ Nat.card (D ⧸ frattini D) = q ^ 2 ∧
      ((IsMulCommutative (CFSG.pCore q M) ∧ (∃ a : ℕ, 1 ≤ a ∧
          Nonempty (CFSG.pCore q M ≃* Multiplicative (ZMod (q ^ a)) ×
            Multiplicative (ZMod (q ^ a)))) ∧
          IsElementaryAbelian q D ∧ Nat.card D = q ^ 2) ∨
        (CFSG.pCore q M = D ∧ ¬ IsMulCommutative (CFSG.pCore q M) ∧
          Nat.card (CFSG.pCore q M) = q ^ 3 ∧ ∀ x ∈ CFSG.pCore q M, x ^ q = 1)) ∧
      (wholeFrattiniAction D).ker = CFSG.fittingSubgroup M ∧ wholeFrattiniAction D ≠ 1 ∧
      ∀ U : Subgroup (D ⧸ frattini D), Nat.card U = q →
        ∃ m : M, ∃ u ∈ U, wholeFrattiniAction D m u ∉ U := by
  classical
  obtain ⟨-, -, hodd, hCF, hcomm, hcores⟩ := odd_Fitting_cores_self hSQT hO2 hLC hq
  have hLperf : Group.IsPerfect M := Group.isPerfect_def.mpr (by
    rw [commutator_def]
    exact hLC.2.1)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hqF))
  obtain ⟨-, hcrit⟩ := all_prime_critical_actions_core hLC hCF hodd hcomm hcores
  set Q := CFSG.pCore q M with hQ
  obtain ⟨hQL, A, hAc, hA, hker⟩ := hcrit q hqF
  obtain ⟨hnab, hab⟩ := critical_whole_shape hq2 hodd hQL A hA hker
  have hQp : IsPGroup q Q := CFSG.pCore_isPGroup
  have hAD : A.map Q.subtype = D := by
    rw [hD]
    by_cases hAab : IsMulCommutative A
    · have hel : IsElementaryAbelian q A := by
        rcases hA.shape with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd hAab h
      obtain ⟨-, -, hAΩ⟩ := hab hel
      rw [hAΩ]
      simp only [CFSG.omega₁, CFSG.omega, pow_one]
      rw [MonoidHom.map_closure]
      congr 1
      ext a
      simp only [Set.mem_image, Set.mem_ofPred_eq, subtype_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, by rw [← SubgroupClass.coe_pow, hx, OneMemClass.coe_one]⟩
      · rintro ⟨haQ, hap⟩
        exact ⟨⟨a, haQ⟩, Subtype.ext hap, rfl⟩
    · have hAtop := hnab hAab
      apply le_antisymm
      · rintro _ ⟨x, -, rfl⟩
        refine subset_closure ⟨x.2, ?_⟩
        have h1 : x ∈ A := by
          rw [hAtop]
          exact mem_top x
        rw [subtype_apply, ← SubgroupClass.coe_pow, hA.pow_eq_one x h1, OneMemClass.coe_one]
      · rw [closure_le]
        rintro a ⟨haQ, -⟩
        exact ⟨⟨a, haQ⟩, by rw [hAtop]; exact mem_top _, rfl⟩
  subst hAD
  set eA : A ≃* A.map Q.subtype := A.equivMapOfInjective Q.subtype Q.subtype_injective with heA
  have hcardD : Nat.card (A.map Q.subtype) = Nat.card A := (Nat.card_congr eA.toEquiv).symm
  have hDp : IsPGroup q (A.map Q.subtype) := hQp.to_le (map_subtype_le A)
  have hDexp : ∀ d ∈ A.map Q.subtype, d ^ q = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA.pow_eq_one x hx, map_one]
  have hDne : A.map Q.subtype ≠ ⊥ := by
    rw [Ne, map_eq_bot_iff_of_injective _ Q.subtype_injective]
    exact hA.ne_bot
  have hrankA : CFSG.pRank q A = 2 := by
    apply le_antisymm
    · have h1 : CFSG.pRank q A ≤ CFSG.pRank q Q := by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
        exact CFSG.SectionRank.pRank_top_le_of_injective hqp.out.one_lt A.subtype
          A.subtype_injective
      exact h1.trans (hcores q hqF).2
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      rcases hA.shape with ⟨hel, hc⟩ | ⟨hnc, hc, -, -⟩
      · refine CFSG.SectionRank.le_pRank (E := ⊤) hqp.out.one_lt (le_refl (⊤ : Subgroup A)) ?_ ?_
        · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x _ => ?_⟩
          · exact hel.toIsMulCommutative.is_comm.comm (a : A) b
          · exact Subtype.ext (by
              rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
              exact hA.pow_eq_one _ x.2)
        · rw [card_top, hc]
      · obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime q (n := 2)
          (show q ^ 2 ∣ Nat.card A by rw [hc]; exact pow_dvd_pow q (by norm_num))
        have hnc' : ∃ a b : A, a * b ≠ b * a := by
          by_contra h
          push Not at h
          exact hnc ⟨⟨h⟩⟩
        obtain ⟨-, -, -, -, -, hTs, -⟩ := nonabelian_prime_cube_central_structure hc hnc'
        obtain ⟨-, -, hTc, -⟩ := hTs T hT
        refine CFSG.SectionRank.le_pRank (E := T) hqp.out.one_lt le_top
          ⟨⟨⟨fun a b => Subtype.ext (hTc a a.2 b b.2)⟩⟩, fun x _ => Subtype.ext (by
            rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
            exact hA.pow_eq_one _ x.2)⟩ hT
  have hrankD : CFSG.pRank q (A.map Q.subtype) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv
      hqp.out.one_lt eA, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrankA
  set θ : A ⧸ frattini A ≃* A.map Q.subtype ⧸ frattini (A.map Q.subtype) :=
    QuotientGroup.congr _ _ eA (map_frattini_mulEquiv eA) with hθ
  have hθeq : ∀ (m : M) (w : A ⧸ frattini A),
      θ (criticalAction A m w) = wholeFrattiniAction (A.map Q.subtype) m (θ w) := by
    intro m w
    induction w using QuotientGroup.induction_on with
    | H a =>
      rw [hθ, QuotientGroup.congr_mk]
      change θ (frattiniAction A (MulAut.conjNormal m) (a : A ⧸ frattini A)) = _
      rw [frattiniAction_mk, hθ, QuotientGroup.congr_mk]
      change ((eA ⟨_, _⟩ : A.map Q.subtype) : A.map Q.subtype ⧸ frattini (A.map Q.subtype)) =
        autQuotient (frattini (A.map Q.subtype)) (MulAut.conjNormal m)
          ((eA a : A.map Q.subtype) : A.map Q.subtype ⧸ frattini (A.map Q.subtype))
      rw [autQuotient_mk]
      rfl
  have hcardW : Nat.card (A.map Q.subtype ⧸ frattini (A.map Q.subtype)) = q ^ 2 := by
    rw [← Nat.card_congr θ.toEquiv, hA.card_quotient]
  have hshape : ((IsMulCommutative Q ∧ (∃ a : ℕ, 1 ≤ a ∧
        Nonempty (Q ≃* Multiplicative (ZMod (q ^ a)) × Multiplicative (ZMod (q ^ a)))) ∧
        IsElementaryAbelian q (A.map Q.subtype) ∧ Nat.card (A.map Q.subtype) = q ^ 2) ∨
      (Q = A.map Q.subtype ∧ ¬ IsMulCommutative Q ∧ Nat.card Q = q ^ 3 ∧
        ∀ x ∈ Q, x ^ q = 1)) := by
    rcases hA.shape with ⟨hel, hc⟩ | ⟨hnc, hc, -, -⟩
    · left
      obtain ⟨hQab, hhom, -⟩ := hab hel
      have := hel
      exact ⟨hQab, hhom, CFSG.QuasithinUnique.Setup.Layer.isElementaryAbelian_map Q.subtype A,
        hcardD.trans hc⟩
    · right
      have hAtop := hnab hnc
      have hQA : Q = A.map Q.subtype := by
        rw [hAtop, Subgroup.map_top, range_subtype]
      refine ⟨hQA, fun hQc => hnc ?_, ?_, fun x hx => ?_⟩
      · rw [hAtop]
        exact ⟨⟨fun a b => Subtype.ext (hQc.is_comm.comm (a : Q) b)⟩⟩
      · rw [hQA, hcardD, hc]
      · rw [hQA] at hx
        exact hDexp x hx
  refine ⟨hA.five_le, inferInstance, hDp, hDexp, hDne, hrankD, hcardW, hshape, ?_, ?_, ?_⟩
  ·
    ext m
    rw [← hker]
    constructor
    · intro hm
      rw [MonoidHom.mem_ker] at hm ⊢
      ext w
      apply θ.injective
      rw [hθeq, hm, MulAut.one_apply, MulAut.one_apply]
    · intro hm
      rw [MonoidHom.mem_ker] at hm ⊢
      ext w
      obtain ⟨w', rfl⟩ := θ.surjective w
      rw [← hθeq, hm, MulAut.one_apply, MulAut.one_apply]
  ·
    intro h1
    apply hA.range_ne_bot
    rw [eq_bot_iff]
    rintro _ ⟨m, rfl⟩
    rw [mem_bot]
    ext w
    apply θ.injective
    rw [hθeq, h1, MonoidHom.one_apply, MulAut.one_apply, MulAut.one_apply]
  ·
    intro U hU
    by_contra hcon
    push Not at hcon
    obtain ⟨g, ⟨m, rfl⟩, u, hu, hgu⟩ := hA.irreducible (U.map θ.symm.toMonoidHom)
      (by rw [card_map_of_injective (f := θ.symm.toMonoidHom) θ.symm.injective, hU])
    obtain ⟨v, hv, rfl⟩ := hu
    apply hgu
    refine ⟨wholeFrattiniAction (A.map Q.subtype) m v, hcon m v hv, ?_⟩
    apply θ.injective
    change θ (θ.symm _) = θ (criticalAction A m (θ.symm v))
    rw [MulEquiv.apply_symm_apply, hθeq, MulEquiv.apply_symm_apply]

theorem eq_bot_or_eq_top_of_no_invariant_line {G W : Type*} [Group G] [Group W] [Finite W]
    {p : ℕ} [hp : Fact p.Prime] (hW : Nat.card W = p ^ 2) (ρ : G →* MulAut W) (S : Set G)
    (hirr : ∀ U : Subgroup W, Nat.card U = p → ∃ g ∈ S, ∃ u ∈ U, ρ g u ∉ U)
    (U : Subgroup W) (hU : ∀ g ∈ S, ∀ u ∈ U, ρ g u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have hdvd : Nat.card U ∣ p ^ 2 := hW ▸ card_subgroup_dvd_card U
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  interval_cases j
  · left
    rw [pow_zero, card_eq_one] at hjc
    exact hjc
  · obtain ⟨g, hg, u, hu, hgu⟩ := hirr U (by rw [hjc, pow_one])
    exact absurd (hU g hg u hu) hgu
  · right
    exact eq_top_of_card_eq U (hjc.trans hW.symm)

theorem mem_of_characteristic {L : Type*} [Group L] (X : Subgroup L) [hX : X.Characteristic] :
    ∀ (α : MulAut L) (x : L), x ∈ X → α x ∈ X :=
  fun α x hx => (SetLike.ext_iff.mp (hX.fixed α) x).mpr hx

@[expose] noncomputable def ambientResidualAction {H : Type*} [Group H] (L : Subgroup H)
    [L.Normal] (X : Subgroup L) [X.Characteristic] :
    H →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  (autQuotient (frattini (X ⧸ CFSG.pCore 2 X))).comp
    ((autQuotient (CFSG.pCore 2 X)).comp
      ((autRestrict X (mem_of_characteristic X)).comp MulAut.conjNormal))

theorem ambientResidualAction_mk {H : Type*} [Group H] (L : Subgroup H) [L.Normal]
    (X : Subgroup L) [X.Characteristic] (h : H) (x : X) :
    ambientResidualAction L X h (((x : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸
      frattini (X ⧸ CFSG.pCore 2 X)) =
      ((((autRestrict X (mem_of_characteristic X) (MulAut.conjNormal h) x : X) :
        X ⧸ CFSG.pCore 2 X)) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  rfl

theorem ambientResidualAction_comp_subtype {H : Type*} [Group H] (L : Subgroup H) [L.Normal]
    (X : Subgroup L) [X.Characteristic] :
    (ambientResidualAction L X).comp L.subtype = residualAction X := by
  ext l w
  induction w using QuotientGroup.induction_on with
  | H w =>
    induction w using QuotientGroup.induction_on with
    | H x => rfl

theorem ambientResidualAction_coe {H : Type*} [Group H] (L : Subgroup H) [L.Normal]
    (X : Subgroup L) [X.Characteristic] (l : L) :
    ambientResidualAction L X (l : H) = residualAction X l :=
  DFunLike.congr_fun (ambientResidualAction_comp_subtype L X) l

theorem ambient_transport {H : Type*} [Group H] [Finite H] (L : Subgroup H) [L.Normal]
    (X : Subgroup L) [X.Characteristic] :
    ∃ (ι : X ≃* X.map L.subtype)
      (ιP : X ⧸ CFSG.pCore 2 X ≃* X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype))
      (ιW : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃*
        (X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype)) ⧸
          frattini (X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype))),
      (∀ x : X, (ι x : H) = x) ∧
      (∀ x : X, ιP (x : X ⧸ CFSG.pCore 2 X) = ((ι x : X.map L.subtype) :
        X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype))) ∧
      ∀ (h : H) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        ιW (ambientResidualAction L X h w) =
          CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) h (ιW w) := by
  classical
  set ι : X ≃* X.map L.subtype := X.equivMapOfInjective L.subtype L.subtype_injective with hι
  set ιP : X ⧸ CFSG.pCore 2 X ≃* X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype) :=
    QuotientGroup.congr _ _ ι (CFSG.pCore_map_iso 2 ι) with hιP
  set ιW := QuotientGroup.congr _ _ ιP (map_frattini_mulEquiv ιP) with hιW
  refine ⟨ι, ιP, ιW, fun _ => rfl, fun _ => rfl, fun h w => ?_⟩
  induction w using QuotientGroup.induction_on with
  | H w =>
    induction w using QuotientGroup.induction_on with
    | H x => rfl

theorem residual_equiv_of_map_eq {L : Type*} [Group L] [Finite L] (X : Subgroup L)
    [X.Characteristic] (D : Subgroup (L ⧸ CFSG.pCore 2 L))
    (hXD : X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) = D) :
    ∃ (_ : D.Normal) (φ : X ⧸ CFSG.pCore 2 X ≃* D)
      (θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃* D ⧸ frattini D),
      (∀ x : X, (φ (x : X ⧸ CFSG.pCore 2 X) : L ⧸ CFSG.pCore 2 L) =
        QuotientGroup.mk' (CFSG.pCore 2 L) (x : L)) ∧
      (∀ v : X ⧸ CFSG.pCore 2 X,
        θ (v : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =
          ((φ v : D) : D ⧸ frattini D)) ∧
      ∀ (l : L) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        θ (residualAction X l w) =
          wholeFrattiniAction D (QuotientGroup.mk' (CFSG.pCore 2 L) l) (θ w) := by
  classical
  subst hXD
  set π := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
  have hDn : (X.map π).Normal := (inferInstance : X.Normal).map π (QuotientGroup.mk'_surjective _)
  let ψ : X →* X.map π := (π.comp X.subtype).codRestrict (X.map π) fun x => ⟨x, x.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨d, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hψker : ψ.ker = CFSG.pCore 2 X :=
    (MonoidHom.ker_codRestrict _ _ _).trans (ker_mk_comp_subtype_eq_pCore X)
  set φ : X ⧸ CFSG.pCore 2 X ≃* X.map π :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) with hφ
  set θ := QuotientGroup.congr _ _ φ (map_frattini_mulEquiv φ) with hθ
  refine ⟨hDn, φ, θ, fun _ => rfl, fun _ => rfl, fun l w => ?_⟩
  induction w using QuotientGroup.induction_on with
  | H w =>
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [residualAction_mk, hθ, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      change ((φ ((MulAut.conjNormal l x : X) : X ⧸ CFSG.pCore 2 X) : X.map π) :
          X.map π ⧸ frattini (X.map π)) =
        autQuotient (frattini (X.map π)) (MulAut.conjNormal (π l))
          ((φ (x : X ⧸ CFSG.pCore 2 X) : X.map π) : X.map π ⧸ frattini (X.map π))
      rw [autQuotient_mk]
      congr 1

theorem ker_residualAction_eq {L : Type*} [Group L] (X : Subgroup L) [X.Characteristic]
    (D : Subgroup (L ⧸ CFSG.pCore 2 L)) [D.Normal]
    (θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃* D ⧸ frattini D)
    (hθ : ∀ (l : L) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      θ (residualAction X l w) =
        wholeFrattiniAction D (QuotientGroup.mk' (CFSG.pCore 2 L) l) (θ w)) :
    (residualAction X).ker =
      (wholeFrattiniAction D).ker.comap (QuotientGroup.mk' (CFSG.pCore 2 L)) := by
  ext l
  rw [mem_comap, MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    ext w
    obtain ⟨w', rfl⟩ := θ.surjective w
    rw [← hθ, h, MulAut.one_apply, MulAut.one_apply]
  · intro h
    ext w
    apply θ.injective
    rw [hθ, h, MulAut.one_apply, MulAut.one_apply]

theorem isOddResidualWitness_of {L : Type*} [Group L] [Finite L] {q : ℕ} [hq : Fact q.Prime]
    (hq2 : q ≠ 2) (D : Subgroup (L ⧸ CFSG.pCore 2 L)) [D.Characteristic] (hDp : IsPGroup q D)
    (hDexp : ∀ d ∈ D, d ^ q = 1) (hDne : D ≠ ⊥) (hDrank : CFSG.pRank q D = 2)
    (hDW : Nat.card (D ⧸ frattini D) = q ^ 2) (hDnt : wholeFrattiniAction D ≠ 1)
    (hDirr : ∀ U : Subgroup (D ⧸ frattini D), Nat.card U = q →
      ∃ m : L ⧸ CFSG.pCore 2 L, ∃ u ∈ U, wholeFrattiniAction D m u ∉ U)
    (E X : Subgroup L) (hE : E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)))
    (hX : X = closure {x | x ∈ E ∧ Odd (orderOf x)}) :
    E.Characteristic ∧ Group.IsSolvable E ∧ IsOddResidualWitness q X ∧
      X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) = D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 L with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hEmem : ∀ y : L, y ∈ E ↔ π y ∈ D := fun y => by rw [hE, mem_comap]
  have hEchar : E.Characteristic := by
    rw [characteristic_iff_le_comap]
    intro σ x hx
    rw [mem_comap, MulEquiv.coe_toMonoidHom, hEmem]
    have h1 := (characteristic_iff_le_comap.mp (inferInstance : D.Characteristic)
      (autQuotient N σ)) ((hEmem x).mp hx)
    exact h1
  have hNE : N ≤ E := fun n hn => by
    rw [hEmem, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hEsolv : Group.IsSolvable E := by
    have : Group.IsSolvable N := by
      have := (CFSG.pCore_isPGroup : IsPGroup 2 N).isNilpotent
      infer_instance
    have : Group.IsSolvable D := by
      have := hDp.isNilpotent
      infer_instance
    let g : E →* D := (π.comp E.subtype).codRestrict D fun x => (hEmem x).mp x.2
    refine Group.isSolvable_of_ker_le_range (inclusion hNE) g fun x hx => ?_
    have hx' : (x : L) ∈ N := by
      have h1 : g x = 1 := hx
      have h2 : π x = 1 := congrArg Subtype.val h1
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact ⟨⟨x, hx'⟩, rfl⟩
  obtain ⟨-, -, hRmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L
  have hERad : E ≤ CFSG.solvableRadical L := hRmax E inferInstance hEsolv
  have hXE : X ≤ E := by
    rw [hX, closure_le]
    exact fun x hx => hx.1
  have hXchar : X.Characteristic := by
    rw [characteristic_iff_le_comap]
    intro σ
    rw [hX, closure_le]
    rintro x ⟨hxE, hxo⟩
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom]
    refine subset_closure ⟨(characteristic_iff_le_comap.mp hEchar σ) hxE, ?_⟩
    have h1 : orderOf (σ x) = orderOf x := orderOf_injective σ.toMonoidHom σ.injective x
    rw [h1]
    exact hxo
  have hgenX : ∀ x : L, x ∈ E → Odd (orderOf x) → x ∈ X := fun x hxE hxo => by
    rw [hX]
    exact subset_closure ⟨hxE, hxo⟩
  have hnoq : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X := by
    intro K _ hK2
    have hgen : ∀ x : L, ∀ (hxE : x ∈ E) (hxo : Odd (orderOf x)),
        (⟨x, hgenX x hxE hxo⟩ : X) ∈ K := by
      intro x hxE hxo
      obtain ⟨k, hk⟩ := hK2 ((⟨x, hgenX x hxE hxo⟩ : X) : X ⧸ K)
      have h1 := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf ((⟨x, hgenX x hxE hxo⟩ : X) : X ⧸ K) ∣ orderOf x := by
        have := orderOf_map_dvd (QuotientGroup.mk' K) (⟨x, hgenX x hxE hxo⟩ : X)
        rwa [Subgroup.orderOf_mk] at this
      have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
        Nat.Coprime.pow_right k (Odd.coprime_two_right hxo)
      have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
      rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    rw [eq_top_iff]
    intro y _
    have hy : (y : L) ∈ K.map X.subtype := by
      have hle : X ≤ K.map X.subtype := by
        conv_lhs => rw [hX]
        rw [closure_le]
        rintro x ⟨hxE, hxo⟩
        exact ⟨⟨x, hgenX x hxE hxo⟩, hgen x hxE hxo, rfl⟩
      exact hle y.2
    obtain ⟨k, hk, hky⟩ := hy
    rwa [← Subtype.ext hky]
  have hπX : X.map π = D := by
    refine le_antisymm ((map_le_iff_le_comap).mpr (hE ▸ hXE)) fun d hd => ?_
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective N d
    have heE : e ∈ E := by
      rw [hE, mem_comap]
      exact hd
    have hodd' : Odd (orderOf (π e)) := by
      obtain ⟨k, hk⟩ := hDp ⟨π e, hd⟩
      have h1 : orderOf (π e) ∣ q ^ k := by
        rw [← Subgroup.orderOf_mk (π e) hd]
        exact orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq.out).mp h1
      rw [hj]
      exact (hq.out.odd_of_ne_two hq2).pow
    obtain ⟨k, hko, hkπ⟩ := exists_odd_pow_map_eq π e hodd'
    exact ⟨e ^ k, hgenX _ (pow_mem heE k) hko, hkπ⟩
  obtain ⟨hDn, φ, θ, -, -, hθeq⟩ := residual_equiv_of_map_eq X D hπX
  have : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hDne
  have : Nontrivial (X ⧸ CFSG.pCore 2 X) := φ.toEquiv.nontrivial
  have hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = q := by
    rw [Monoid.exponent_eq_prime_iff hq.out]
    intro g hg
    rw [← orderOf_injective φ.toMonoidHom φ.injective g]
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hDexp _ (φ g).2)
    · intro h1
      exact hg (φ.injective (h1.trans (map_one φ).symm))
  have hrank : CFSG.pRank q (X ⧸ CFSG.pCore 2 X) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_top_eq_of_mulEquiv
      hq.out.one_lt φ, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hDrank
  have hcardW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = q ^ 2 := by
    rw [Nat.card_congr θ.toEquiv, hDW]
  refine ⟨hEchar, hEsolv, ⟨hXchar, hXE.trans hERad, hnoq, hDp.of_equiv φ.symm, hexp, hrank,
    hcardW, ?_, ?_⟩, hπX⟩
  ·
    intro h1
    apply hDnt
    ext l w
    obtain ⟨w', rfl⟩ := θ.surjective w
    change wholeFrattiniAction D (π l) (θ w') = θ w'
    rw [← hθeq, h1, MonoidHom.one_apply, MulAut.one_apply]
  ·
    intro U hU
    by_contra hcon
    push Not at hcon
    obtain ⟨m, u', hu', hmu⟩ := hDirr (U.map θ.toMonoidHom)
      (by rw [card_map_of_injective (f := θ.toMonoidHom) θ.injective, hU])
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N m
    obtain ⟨u, hu, rfl⟩ := hu'
    apply hmu
    refine ⟨residualAction X l u, hcon l u hu, ?_⟩
    change θ (residualAction X l u) = wholeFrattiniAction D (π l) (θ u)
    exact hθeq l u

theorem witness_prime_data
    {L : Type*} [Group L] [Finite L] (hSQT : CFSG.IsStronglyQuasithin L)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {X : Subgroup L} [X.Characteristic]
    (hX : IsOddResidualWitness p X) :
    p ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors ∧
      (residualAction X).ker = (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 L)) ∧
      ∀ X' : Subgroup L, IsOddResidualWitness p X' → X' = X := by
  classical
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  have hcan := original_characteristic_radical_witness_is_canonical_prime_residual hSQT hLC hq hp5
    hX (CFSG.pCore p (L ⧸ CFSG.pCore 2 L))
    (closure {a | a ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧ a ^ p = 1})
    ((closure {a | a ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧ a ^ p = 1}).comap
      (QuotientGroup.mk' (CFSG.pCore 2 L))) rfl rfl rfl
  obtain ⟨hQne, -, -, -, -, -, -, ⟨hDnX, φX, θX, -, -, hθX⟩, huniq⟩ := hcan
  have hpF : p ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hp.out, ?_, Nat.card_pos.ne'⟩
    have h1 : Nat.card (CFSG.pCore p (L ⧸ CFSG.pCore 2 L)) ∣
        Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L)) :=
      card_dvd_of_le (CFSG.pCore_le_fitting _ p)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup :
      IsPGroup p (CFSG.pCore p (L ⧸ CFSG.pCore 2 L))).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hk
      exact hQne hk
    rw [hk] at h1
    exact (dvd_pow_self p hk0).trans h1
  have hcpd := canonical_prime_data (M := L ⧸ CFSG.pCore 2 L) hSQT' hO2' hLC' hq hpF
    (closure {a | a ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧ a ^ p = 1}) rfl
  obtain ⟨-, hDcX, -, -, -, -, -, -, hDkerX, -, -⟩ := hcpd
  refine ⟨hpF, ?_, huniq⟩
  rw [ker_residualAction_eq X _ θX hθX, hDkerX]

theorem canonical_prime_witness {L : Type*} [Group L] [Finite L]
    (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) {q : ℕ}
    (hqF : q ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors)
    (Q D : Subgroup (L ⧸ CFSG.pCore 2 L)) (E Xq : Subgroup L)
    (hQ : Q = CFSG.pCore q (L ⧸ CFSG.pCore 2 L)) (hD : D = closure {a | a ∈ Q ∧ a ^ q = 1})
    (hE : E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)))
    (hXq : Xq = closure {e | e ∈ E ∧ Odd (orderOf e)}) :
    5 ≤ q ∧ ∃ _ : Xq.Characteristic, IsOddResidualWitness q Xq ∧ Group.IsSolvable Xq ∧
      E = CFSG.pCore 2 L ⊔ Xq ∧ (CFSG.pCore 2 L).subgroupOf Xq = CFSG.pCore 2 Xq ∧
      (∃ (_ : D.Normal) (φ : Xq ⧸ CFSG.pCore 2 Xq ≃* D)
          (θ : (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq) ≃* D ⧸ frattini D),
        (∀ x : Xq, (φ (x : Xq ⧸ CFSG.pCore 2 Xq) : L ⧸ CFSG.pCore 2 L) =
          QuotientGroup.mk' (CFSG.pCore 2 L) (x : L)) ∧
        (∀ (l : L) (x y : Xq), (y : L) = l * x * l⁻¹ →
          (φ (y : Xq ⧸ CFSG.pCore 2 Xq) : L ⧸ CFSG.pCore 2 L) =
            QuotientGroup.mk' (CFSG.pCore 2 L) l *
              (φ (x : Xq ⧸ CFSG.pCore 2 Xq) : L ⧸ CFSG.pCore 2 L) *
              (QuotientGroup.mk' (CFSG.pCore 2 L) l)⁻¹) ∧
        (∀ v : Xq ⧸ CFSG.pCore 2 Xq,
          θ (v : (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)) =
            ((φ v : D) : D ⧸ frattini D)) ∧
        ∀ (l : L) (w : (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
          θ (residualAction Xq l w) =
            wholeFrattiniAction D (QuotientGroup.mk' (CFSG.pCore 2 L) l) (θ w)) ∧
      ((IsMulCommutative Q ∧ (∃ a : ℕ, 1 ≤ a ∧
          Nonempty (Q ≃* Multiplicative (ZMod (q ^ a)) × Multiplicative (ZMod (q ^ a)))) ∧
          IsElementaryAbelian q D ∧ Nat.card D = q ^ 2) ∨
        (Q = D ∧ ¬ IsMulCommutative Q ∧ Nat.card Q = q ^ 3 ∧ ∀ x ∈ Q, x ^ q = 1)) ∧
      (residualAction Xq).ker = (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 L)) := by
  classical
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqF
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  subst hQ
  have hcpd := canonical_prime_data (M := L ⧸ CFSG.pCore 2 L) hSQT' hO2' hLC' hq hqF D hD
  obtain ⟨hq5, hDc, hDp, hDexp, hDne, hDrank, hDW, hshape, hDker, hDnt, hDirr⟩ := hcpd
  have hq2 : q ≠ 2 := by omega
  have hiw := isOddResidualWitness_of hq2 D hDp hDexp hDne hDrank hDW hDnt hDirr E Xq hE hXq
  obtain ⟨-, -, hWq, hπXq⟩ := hiw
  have hXqc := hWq.characteristic
  have hcan := original_characteristic_radical_witness_is_canonical_prime_residual hSQT hLC hq
    hq5 hWq (CFSG.pCore q (L ⧸ CFSG.pCore 2 L)) D E rfl hD hE
  obtain ⟨-, -, hkerq, hENX, -, -, -, -, -⟩ := hcan
  have hre := residual_equiv_of_map_eq Xq D hπXq
  obtain ⟨hDn, φ, θ, hφ, hθφ, hθ⟩ := hre
  have hRads : Group.IsSolvable (CFSG.solvableRadical L) :=
    (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).2.1
  refine ⟨hq5, hXqc, hWq, Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hWq.le_rad), hENX, ?_, ⟨hDn, φ, θ, hφ, fun l x y hy => ?_, hθφ, hθ⟩,
    hshape, ?_⟩
  · rw [← hkerq]
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply, subtype_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · rw [hφ, hφ, hy, map_mul, map_mul, map_inv]
  · rw [ker_residualAction_eq Xq D θ hθ, hDker]

theorem witness_frattiniQuotConj {H : Type*} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    {p : ℕ} [hp : Fact p.Prime] {X : Subgroup L} [X.Characteristic]
    (hX : IsOddResidualWitness p X) :
    CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 (X.map L.subtype) ∧
      IsPGroup p (X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype)) ∧
      frattini (X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype)) ≠ ⊤ ∧
      (∀ U : Subgroup ((X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype)) ⧸
          frattini (X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype))),
        (∀ l ∈ L, ∀ u ∈ U,
          CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) l u ∈ U) →
          U = ⊥ ∨ U = ⊤) ∧
      (∃ l ∈ L, ∃ w, CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) l w ≠ w) ∧
      ∀ h h' : H, CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) h =
          CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) h' →
        ambientResidualAction L X h = ambientResidualAction L X h' := by
  classical
  obtain ⟨ι, ιP, ιW, -, -, hιW⟩ := ambient_transport L X
  refine ⟨CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective ι.toMonoidHom
    ι.surjective hX.noTwoQuotient, hX.isPGroup.of_equiv ιP, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := hX.card_W
    rw [Nat.card_congr ιW.toEquiv, h] at h1
    have h2 : Nat.card ((X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype)) ⧸
        (⊤ : Subgroup (X.map L.subtype ⧸ CFSG.pCore 2 (X.map L.subtype)))) = 1 :=
      Subgroup.index_top
    rw [h2] at h1
    have := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  · intro U hU
    have hsurj : Function.Surjective ιW.toMonoidHom := ιW.surjective
    have h1 := eq_bot_or_eq_top_of_no_invariant_line hX.card_W (residualAction X) Set.univ
      (fun U' hU' => by
        obtain ⟨l, u, hu, hlu⟩ := hX.irreducible U' hU'
        exact ⟨l, Set.mem_univ _, u, hu, hlu⟩)
      (U.comap ιW.toMonoidHom) (fun l _ u hu => by
        rw [mem_comap, MulEquiv.coe_toMonoidHom] at hu ⊢
        rw [← ambientResidualAction_coe L X l, hιW]
        exact hU l l.2 _ hu)
    rcases h1 with h1 | h1
    · left
      rw [← map_comap_eq_self_of_surjective hsurj U, h1, Subgroup.map_bot]
    · right
      rw [← map_comap_eq_self_of_surjective hsurj U, h1, map_top_of_surjective _ hsurj]
  · by_contra hcon
    push Not at hcon
    apply hX.nontrivial
    ext l w
    rw [MonoidHom.one_apply, MulAut.one_apply]
    apply ιW.injective
    rw [← ambientResidualAction_coe L X l, hιW]
    exact hcon l l.2 (ιW w)
  · intro h h' hh
    ext w
    apply ιW.injective
    rw [hιW, hιW, hh]

theorem original_witness_normalizer {H : Type*} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hLperf : Group.IsPerfect L) (T : Sylow 2 H) (hLT : L ⊔ (T : Subgroup H) = ⊤) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup L} [X.Characteristic]
    (hX : IsOddResidualWitness p X) :
    let R := (CFSG.pCore 2 (X.map L.subtype ⊔ (T : Subgroup H) : Subgroup H)).map
      (X.map L.subtype ⊔ (T : Subgroup H)).subtype
    let A := L ⊓ normalizer (R : Set H)
    let Y := (CFSG.perfectResidual A).map A.subtype
    (CFSG.pCore 2 L).map L.subtype ≤ R ∧ Group.IsPerfect Y ∧
      (T : Subgroup H) ≤ normalizer (Y : Set H) ∧ X.map L.subtype ≤ Y ∧ Y ≤ L ∧
      ∀ l ∈ L, ∃ y ∈ Y, ambientResidualAction L X y = ambientResidualAction L X l := by
  intro R A Y
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX2, hP, hW, hirrX, hntX, hdet⟩ := witness_frattiniQuotConj hX
  have hS :=
    CFSG.Quasithin.SteinbergCC.sylow_core_normalizer_perfect_residual_retains_original_prime_witness
      hLperf T hLT hp.out hp2 (map_subtype_le X) hX2 hP hW hirrX hntX
  obtain ⟨hCker, hRker, -, -, -, -, hYperf, -, -, -, -, hYLmap, -, hXY, hYA, hAL, hTY⟩ := hS
  have hYLmap' : Y.map (CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype)) =
      L.map (CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype)) := hYLmap
  have hNR : (CFSG.pCore 2 L).map L.subtype ≤ R := by
    have hN2 : IsPGroup 2 ((CFSG.pCore 2 L).map L.subtype) := CFSG.pCore_isPGroup.map L.subtype
    have hRker' : R = (T : Subgroup H) ⊓
        (CFSG.Quasithin.SteinbergCC.coreQuotConj (X.map L.subtype)).ker := hRker
    rw [hRker']
    intro n hn
    refine mem_inf.mpr ⟨hN2.le_sylow_of_normal T hn, ?_⟩
    have h1 : n ∈ ((CFSG.Quasithin.SteinbergCC.coreQuotConj (X.map L.subtype)).ker : Set H) := by
      rw [hCker, Set.mem_ofPred_eq]
      intro x hx
      have hxn1 : ⁅x, n⁆ ∈ X.map L.subtype := by
        have := mul_mem hx
          ((inferInstance : (X.map L.subtype).Normal).conj_mem _ (inv_mem hx) n)
        simpa [commutatorElement_def, mul_assoc] using this
      have hxn2 : ⁅x, n⁆ ∈ (CFSG.pCore 2 L).map L.subtype := by
        rw [commutatorElement_def]
        exact mul_mem ((inferInstance : ((CFSG.pCore 2 L).map L.subtype).Normal).conj_mem n hn x)
          (inv_mem hn)
      have hle : ((CFSG.pCore 2 L).map L.subtype).subgroupOf (X.map L.subtype) ≤
          CFSG.pCore 2 (X.map L.subtype) :=
        CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup inferInstance
          hN2.comap_subtype
      exact ⟨⟨⁅x, n⁆, hxn1⟩, hle (mem_subgroupOf.mpr hxn2), rfl⟩
    exact h1
  refine ⟨hNR, hYperf, hTY, hXY, hYA.trans hAL, fun l hl => ?_⟩
  have h1 : CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype) l ∈
      Y.map (CFSG.Quasithin.SteinbergCC.frattiniQuotConj (X.map L.subtype)) := by
    rw [hYLmap']
    exact ⟨l, hl, rfl⟩
  obtain ⟨y, hy, hyl⟩ := h1
  exact ⟨y, hy, hdet y l hyl⟩

theorem ambient_map_eq_of_ker_eq {H : Type*} [Group H] {L : Subgroup H} [L.Normal]
    {X X' : Subgroup L} [X.Characteristic] [X'.Characteristic] {Y : Subgroup H} (hYL : Y ≤ L)
    (hY : ∀ l ∈ L, ∃ y ∈ Y, ambientResidualAction L X y = ambientResidualAction L X l)
    (hker : (residualAction X).ker = (residualAction X').ker) :
    Y.map (ambientResidualAction L X') = L.map (ambientResidualAction L X') := by
  apply le_antisymm (map_mono hYL)
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨y, hy, hyl⟩ := hY l hl
  refine ⟨y, hy, ?_⟩
  have hyL : y ∈ L := hYL hy
  have h1 : (⟨y, hyL⟩⁻¹ * ⟨l, hl⟩ : L) ∈ (residualAction X).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← ambientResidualAction_coe L X,
      ← ambientResidualAction_coe L X]
    change (ambientResidualAction L X y)⁻¹ * ambientResidualAction L X l = 1
    rw [hyl, inv_mul_cancel]
  rw [hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
    ← ambientResidualAction_coe L X', ← ambientResidualAction_coe L X'] at h1
  exact h1

theorem witness_ambient_facts {H : Type*} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    {q : ℕ} [Fact q.Prime] {Xq : Subgroup L} [Xq.Characteristic]
    (hW : IsOddResidualWitness q Xq) {Y : Subgroup H}
    (hY : Y.map (ambientResidualAction L Xq) = L.map (ambientResidualAction L Xq)) :
    (∃ l ∈ L, ∃ w, ambientResidualAction L Xq l w ≠ w) ∧
      (∀ U : Subgroup ((Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
        (∀ l ∈ L, ∀ u ∈ U, ambientResidualAction L Xq l u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      (∃ y ∈ Y, ∃ w, ambientResidualAction L Xq y w ≠ w) ∧
      (∀ U : Subgroup ((Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
        (∀ y ∈ Y, ∀ u ∈ U, ambientResidualAction L Xq y u ∈ U) → U = ⊥ ∨ U = ⊤) := by
  have hmem : ∀ l ∈ L, ∃ y ∈ Y, ambientResidualAction L Xq y = ambientResidualAction L Xq l := by
    intro l hl
    have h1 : ambientResidualAction L Xq l ∈ Y.map (ambientResidualAction L Xq) := by
      rw [hY]
      exact ⟨l, hl, rfl⟩
    exact h1
  have hnt : ∃ l ∈ L, ∃ w, ambientResidualAction L Xq l w ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hW.nontrivial
    ext l w
    rw [MonoidHom.one_apply, MulAut.one_apply, ← ambientResidualAction_coe L Xq l]
    exact hcon l l.2 w
  have hirr : ∀ U : Subgroup ((Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
      (∀ l ∈ L, ∀ u ∈ U, ambientResidualAction L Xq l u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    exact eq_bot_or_eq_top_of_no_invariant_line hW.card_W (residualAction Xq) Set.univ
      (fun U' hU' => by
        obtain ⟨l, u, hu, hlu⟩ := hW.irreducible U' hU'
        exact ⟨l, Set.mem_univ _, u, hu, hlu⟩)
      U (fun l _ u hu => by
        rw [← ambientResidualAction_coe L Xq l]
        exact hU l l.2 u hu)
  refine ⟨hnt, hirr, ?_, fun U hU => hirr U fun l hl u hu => ?_⟩
  · obtain ⟨l, hl, w, hw⟩ := hnt
    obtain ⟨y, hy, hyl⟩ := hmem l hl
    exact ⟨y, hy, w, by rw [hyl]; exact hw⟩
  · obtain ⟨y, hy, hyl⟩ := hmem l hl
    rw [← hyl]
    exact hU y hy u hu

theorem witness_two_product {H : Type*} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {Xq : Subgroup L} [Xq.Characteristic]
    (hXqs : Group.IsSolvable Xq) (hPq : IsPGroup q (Xq ⧸ CFSG.pCore 2 Xq)) {R : Subgroup H}
    (hR2 : IsPGroup 2 R) (hO2R : ((CFSG.pCore 2 Xq).map Xq.subtype).map L.subtype ≤ R) :
    ((Xq.map L.subtype ⊔ R : Subgroup H) : Set H) = (Xq.map L.subtype : Set H) * (R : Set H) ∧
      Group.IsSolvable (Xq.map L.subtype ⊔ R : Subgroup H) ∧
      (∀ r : ℕ, r.Prime → r ∣ Nat.card (Xq.map L.subtype ⊔ R : Subgroup H) →
        r = 2 ∨ r = q) ∧
      Xq.map L.subtype ⊓ R = ((CFSG.pCore 2 Xq).map Xq.subtype).map L.subtype ∧
      CFSG.ABGLocalTools.IsSylowOf 2 R (Xq.map L.subtype ⊔ R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqp : q.Prime := Fact.out
  have hXR : Xq.map L.subtype ⊓ R = ((CFSG.pCore 2 Xq).map Xq.subtype).map L.subtype := by
    refine le_antisymm ?_ (le_inf (map_mono (map_subtype_le _)) hO2R)
    rintro z ⟨⟨x, hx, rfl⟩, hzR⟩
    obtain ⟨k, hk⟩ := hR2 ⟨_, hzR⟩
    have hxk : (x : H) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_pow] at this
    have hk' : ((⟨x, hx⟩ : Xq) : Xq ⧸ CFSG.pCore 2 Xq) ^ 2 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow]
      have h1 : (⟨x, hx⟩ : Xq) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hxk
      rw [h1, QuotientGroup.mk_one]
    obtain ⟨j, hj⟩ := hPq ((⟨x, hx⟩ : Xq) : Xq ⧸ CFSG.pCore 2 Xq)
    have hcop : Nat.Coprime (2 ^ k) (q ^ j) :=
      Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_two hqp).mpr (Ne.symm hq2))
    have h2 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk') hcop)
      (orderOf_dvd_of_pow_eq_one hj)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h2
    exact ⟨x, ⟨⟨x, hx⟩, h2, rfl⟩, rfl⟩
  obtain ⟨j, hj⟩ := hPq.exists_card_eq
  have hidx : R.relIndex (Xq.map L.subtype ⊔ R) = q ^ j := by
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (Xq.map L.subtype) R, ← hj]
    have h1 := Subgroup.relIndex_mul_card (H := R) (K := Xq.map L.subtype)
    rw [inf_comm, hXR, card_map_of_injective L.subtype_injective,
      card_map_of_injective L.subtype_injective, card_map_of_injective Xq.subtype_injective,
      card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 Xq)] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hndvd : ¬ 2 ∣ (R.subgroupOf (Xq.map L.subtype ⊔ R)).index := by
    change ¬ 2 ∣ R.relIndex (Xq.map L.subtype ⊔ R)
    rw [hidx]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 R (Xq.map L.subtype ⊔ R) := by
    have hR2V : IsPGroup 2 (R.subgroupOf (Xq.map L.subtype ⊔ R)) := by
      rw [← comap_subtype]
      exact hR2.comap_subtype
    refine ⟨hR2V.toSylow hndvd, ?_⟩
    rw [IsPGroup.toSylow_coe, subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right]
  have h2q : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Xq.map L.subtype ⊔ R : Subgroup H) →
      r = 2 ∨ r = q := by
    intro r hr hrd
    have h1 := Subgroup.relIndex_mul_card (H := R) (K := Xq.map L.subtype ⊔ R)
    rw [inf_eq_left.mpr le_sup_right, hidx] at h1
    obtain ⟨m, hm⟩ := hR2.exists_card_eq
    rw [← h1, hm] at hrd
    rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hqp).mp (hr.dvd_of_dvd_pow h))
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
  have hXqhs : Group.IsSolvable (Xq.map L.subtype) :=
    Group.isSolvable_of_surjective
      (f := (Xq.equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hVs : Group.IsSolvable (Xq.map L.subtype ⊔ R : Subgroup H) := by
    have hQ2 : IsPGroup 2 ((Xq.map L.subtype ⊔ R : Subgroup H) ⧸
        (Xq.map L.subtype).subgroupOf (Xq.map L.subtype ⊔ R)) := by
      intro v
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
      have hv : (v : H) ∈ (Xq.map L.subtype : Set H) * (R : Set H) := by
        rw [← normal_mul]
        exact v.2
      obtain ⟨x, hx, r, hr, hxr⟩ := hv
      obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, SubgroupClass.coe_pow]
      have hrk : r ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        rwa [SubgroupClass.coe_pow] at this
      have h1 : ((v : H) : H ⧸ Xq.map L.subtype) ^ 2 ^ k = 1 := by
        rw [← hxr, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).mpr hx, one_mul,
          ← QuotientGroup.mk_pow, hrk, QuotientGroup.mk_one]
      rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    have := hQ2.isNilpotent
    refine Group.isSolvable_of_ker_le_range
      (inclusion (le_sup_left : Xq.map L.subtype ≤ Xq.map L.subtype ⊔ R))
      (QuotientGroup.mk' ((Xq.map L.subtype).subgroupOf (Xq.map L.subtype ⊔ R))) fun g hg => ?_
    rw [QuotientGroup.ker_mk', mem_subgroupOf] at hg
    exact ⟨⟨g, hg⟩, rfl⟩
  exact ⟨normal_mul _ _, hVs, h2q, hXR, hSyl⟩

theorem all_canonical_prime_witnesses_retain_original_normalizer_derived_Frattini_actions
    {H : Type*} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hSQT : CFSG.IsStronglyQuasithin L) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (T : Sylow 2 H) (hLT : L ⊔ (T : Subgroup H) = ⊤)
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {X : Subgroup L} (hX : IsOddResidualWitness p X) :
    let R := (CFSG.pCore 2 (X.map L.subtype ⊔ (T : Subgroup H) : Subgroup H)).map
      (X.map L.subtype ⊔ (T : Subgroup H)).subtype
    let A := L ⊓ normalizer (R : Set H)
    let Y := (CFSG.perfectResidual A).map A.subtype
    (CFSG.pCore 2 L).map L.subtype ≤ R ∧ Group.IsPerfect Y ∧
      (T : Subgroup H) ≤ normalizer (Y : Set H) ∧ X.map L.subtype ≤ Y ∧
      p ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors ∧
      ∀ q ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors,
      ∀ (Q D : Subgroup (L ⧸ CFSG.pCore 2 L)) (E Xq : Subgroup L),
        Q = CFSG.pCore q (L ⧸ CFSG.pCore 2 L) → D = closure {a | a ∈ Q ∧ a ^ q = 1} →
        E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)) →
        Xq = closure {e | e ∈ E ∧ Odd (orderOf e)} →
        5 ≤ q ∧ ∃ _ : Xq.Characteristic, Group.IsSolvable Xq ∧
          Xq ≤ CFSG.solvableRadical L ∧ CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 Xq ∧
          E = CFSG.pCore 2 L ⊔ Xq ∧ (CFSG.pCore 2 L).subgroupOf Xq = CFSG.pCore 2 Xq ∧
          (∃ (_ : D.Normal) (φ : Xq ⧸ CFSG.pCore 2 Xq ≃* D)
              (θ : (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq) ≃*
                D ⧸ frattini D),
            (∀ x : Xq, (φ (x : Xq ⧸ CFSG.pCore 2 Xq) : L ⧸ CFSG.pCore 2 L) =
              QuotientGroup.mk' (CFSG.pCore 2 L) (x : L)) ∧
            (∀ (l : L) (x y : Xq), (y : L) = l * x * l⁻¹ →
              (φ (y : Xq ⧸ CFSG.pCore 2 Xq) : L ⧸ CFSG.pCore 2 L) =
                QuotientGroup.mk' (CFSG.pCore 2 L) l *
                  (φ (x : Xq ⧸ CFSG.pCore 2 Xq) : L ⧸ CFSG.pCore 2 L) *
                  (QuotientGroup.mk' (CFSG.pCore 2 L) l)⁻¹) ∧
            (∀ v : Xq ⧸ CFSG.pCore 2 Xq,
              θ (v : (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)) =
                ((φ v : D) : D ⧸ frattini D)) ∧
            ∀ (l : L) (w : (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
              θ (residualAction Xq l w) =
                wholeFrattiniAction D (QuotientGroup.mk' (CFSG.pCore 2 L) l) (θ w)) ∧
          ((IsMulCommutative Q ∧ (∃ a : ℕ, 1 ≤ a ∧
              Nonempty (Q ≃* Multiplicative (ZMod (q ^ a)) × Multiplicative (ZMod (q ^ a)))) ∧
              IsElementaryAbelian q D ∧ Nat.card D = q ^ 2) ∨
            (Q = D ∧ ¬ IsMulCommutative Q ∧ Nat.card Q = q ^ 3 ∧ ∀ x ∈ Q, x ^ q = 1)) ∧
          Monoid.exponent (Xq ⧸ CFSG.pCore 2 Xq) = q ∧
          CFSG.pRank q (Xq ⧸ CFSG.pCore 2 Xq) = 2 ∧
          Nat.card ((Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)) = q ^ 2 ∧
          ((ambientResidualAction L Xq).comp L.subtype).ker =
            (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L)).comap
              (QuotientGroup.mk' (CFSG.pCore 2 L)) ∧
          (∃ l ∈ L, ∃ w, ambientResidualAction L Xq l w ≠ w) ∧
          (∀ U : Subgroup ((Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
            (∀ l ∈ L, ∀ u ∈ U, ambientResidualAction L Xq l u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
          Y.map (ambientResidualAction L Xq) = L.map (ambientResidualAction L Xq) ∧
          (∃ y ∈ Y, ∃ w, ambientResidualAction L Xq y w ≠ w) ∧
          (∀ U : Subgroup ((Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)),
            (∀ y ∈ Y, ∀ u ∈ U, ambientResidualAction L Xq y u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
          (q = p → Xq = X) ∧
          ((Xq.map L.subtype ⊔ R : Subgroup H) : Set H) = (Xq.map L.subtype : Set H) * (R : Set H) ∧
          Group.IsSolvable (Xq.map L.subtype ⊔ R : Subgroup H) ∧
          (∀ r : ℕ, r.Prime → r ∣ Nat.card (Xq.map L.subtype ⊔ R : Subgroup H) →
            r = 2 ∨ r = q) ∧
          Xq.map L.subtype ⊓ R = ((CFSG.pCore 2 Xq).map Xq.subtype).map L.subtype ∧
          CFSG.ABGLocalTools.IsSylowOf 2 R (Xq.map L.subtype ⊔ R) := by
  intro R A Y
  have hp2 : p ≠ 2 := by omega
  have hXc := hX.characteristic
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr (by
    rw [_root_.commutator_def]
    exact hLC.2.1)
  have hpd := witness_prime_data hSQT hLC hq hp5 hX
  obtain ⟨hpF, hkerX, huniq⟩ := hpd
  have hnorm := original_witness_normalizer hLperf T hLT hp2 hX
  obtain ⟨hNR, hYperf, hTY, hXY, hYL, hYLp⟩ := hnorm
  refine ⟨hNR, hYperf, hTY, hXY, hpF, ?_⟩
  intro q hqF Q D E Xq hQ hD hE hXq
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF⟩
  have hcw := canonical_prime_witness hSQT hLC hq hqF Q D E Xq hQ hD hE hXq
  obtain ⟨hq5, hXqc, hWq, hXqs, hENX, hNsub, hiso, hshape, hkerq⟩ := hcw
  have hq2 : q ≠ 2 := by omega
  have hYmap := ambient_map_eq_of_ker_eq hYL hYLp (hkerX.trans hkerq.symm)
  have haf := witness_ambient_facts hWq hYmap
  obtain ⟨hntq, hirrq, hYnt, hYirr⟩ := haf
  have hO2R : ((CFSG.pCore 2 Xq).map Xq.subtype).map L.subtype ≤ R := by
    refine (map_mono ?_).trans hNR
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x ∈ (CFSG.pCore 2 L).subgroupOf Xq := by
      rw [hNsub]
      exact hx
    exact mem_subgroupOf.mp h1
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup.map _
  have htp := witness_two_product hq2 hXqs hWq.isPGroup hR2 hO2R
  obtain ⟨hVset, hVs, h2q, hXR, hSyl⟩ := htp
  refine ⟨hq5, hXqc, hXqs, hWq.le_rad, hWq.noTwoQuotient, hENX, hNsub, hiso, hshape,
    hWq.exponent, hWq.pRank, hWq.card_W, ?_, hntq, hirrq, hYmap, hYnt, hYirr, fun hqp => ?_,
    hVset, hVs, h2q, hXR, hSyl⟩
  · rw [ambientResidualAction_comp_subtype]
    exact hkerq
  · subst hqp
    exact huniq Xq hWq

end CFSG.Quasithin.H13.NQBlock
