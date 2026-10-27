module

public import CFSG.SignalizerFunctorTheorem.Solvable.ZJ.LargerNormalizer
public import CFSG.SignalizerFunctorTheorem.Solvable.ZJ.Refinement
public import CFSG.SignalizerFunctorTheorem.Solvable.ZJ.Transfer
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerNormalizerFactorizationComplete

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Solvable

variable {G : Type*} [Group G] [Finite G]

theorem zj_global_normalizer_control
    (prime rank q : ℕ) (prime_prime : prime.Prime) (q_prime : q.Prime) (hq : 5 ≤ q)
    (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (S : Subgroup G) (hS : S ≠ ⊥)
    (hScomp : solvableSignalizerCompatible prime rank actor values S) (hSq : IsPGroup q S)
    (hSmax : ∀ T : Subgroup G, solvableSignalizerCompatible prime rank actor values T →
      IsPGroup q T → S ≤ T → T = S) :
    solvableSignalizerCompatible prime rank actor values
        (signalizerNormalizerCompletion prime rank actor values (embeddedOrderThompsonCenter S)) ∧
      signalizerNormalizerFactorization prime rank q actor values
        (signalizerNormalizerCompletion prime rank actor values (embeddedOrderThompsonCenter S)) := by
  classical
  have large' : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  have rank_large : prime ^ rank ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans large'
  have actor_pgroup : IsPGroup prime actor := elementary_abelian_isPGroup prime actor elementary
  have : Fact q.Prime := ⟨q_prime⟩
  have distinct : prime ≠ q := by
    intro same
    have coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary rank_large
      values conditions.coprime S hScomp.1.1 hScomp.1.2
    rcases hSq.card_eq_or_dvd with cardinality | divides
    · exact hS ((Subgroup.eq_bot_iff_card S).mpr cardinality)
    · exact prime_prime.coprime_iff_not_dvd.mp coprime (same ▸ divides)
  have solvable_of_pgroup : ∀ T : Subgroup G, IsPGroup q T → Group.IsSolvable T := fun T hT => by
    have := hT.isNilpotent
    infer_instance
  have hSmaximal : Maximal (signalizerPrimeCompatible prime rank q actor values) S :=
    maximal_iff.mpr ⟨⟨hScomp.1, hSq⟩, fun T hT hST =>
      (hSmax T ⟨hT.1, solvable_of_pgroup T hT.2⟩ hT.2 hST).symm⟩
  obtain ⟨hZSne, -⟩ := embedded_order_thompson_center_pgroup q q_prime S hSq hS
  obtain ⟨hZSle, -, hZSnorm⟩ := embedded_order_thompson_center_properties S actor hScomp.1.1
  have hZScomp := solvable_signalizer_compatible_of_le prime rank actor values S _ hScomp hZSle
    hZSnorm
  have hMcomp : solvableSignalizerCompatible prime rank actor values
      (signalizerNormalizerCompletion prime rank actor values (embeddedOrderThompsonCenter S)) :=
    locally_complete.1 _ hZSne hZScomp
  refine ⟨hMcomp, ?_⟩
  set M := signalizerNormalizerCompletion prime rank actor values (embeddedOrderThompsonCenter S)
    with hM
  rw [signalizerNormalizerFactorization_iff_controlled]
  by_contra hfail
  push Not at hfail
  obtain ⟨W₀, hW₀ne, hW₀comp, hW₀q, hW₀fail⟩ := hfail
  let Bad : Subgroup G → Subgroup G → Prop := fun W T =>
    W ≠ ⊥ ∧ solvableSignalizerCompatible prime rank actor values W ∧ IsPGroup q W ∧
      ¬ NormalizerControlled prime rank q actor values M W ∧
      ∃ P : Sylow q (signalizerNormalizerCompletion prime rank actor values W),
        (P : Subgroup (signalizerNormalizerCompletion prime rank actor values W)).map
          (signalizerNormalizerCompletion prime rank actor values W).subtype = T ∧
        actor ≤ Subgroup.normalizer (T : Set G)
  have extremal : ∃ W T : Subgroup G, Bad W T ∧ ∀ W' T' : Subgroup G, Bad W' T' →
      Nat.card T' ≤ Nat.card T := by
    have hU₀comp := locally_complete.1 W₀ hW₀ne hW₀comp
    obtain ⟨P₀, hP₀⟩ := normalized_subgroup_invariant_sylow prime q prime_prime q_prime actor
      (signalizerNormalizerCompletion prime rank actor values W₀) actor_pgroup hU₀comp.1.1
      (signalizer_subgroup_coprime prime rank prime_prime actor elementary rank_large values
        conditions.coprime _ hU₀comp.1.1 hU₀comp.1.2)
    have : Nonempty {x : Subgroup G × Subgroup G // Bad x.1 x.2} :=
      ⟨⟨(W₀, (P₀ : Subgroup (signalizerNormalizerCompletion prime rank actor values W₀)).map
        (signalizerNormalizerCompletion prime rank actor values W₀).subtype),
        hW₀ne, hW₀comp, hW₀q, hW₀fail, P₀, rfl, hP₀⟩⟩
    obtain ⟨⟨⟨W, T⟩, hbad⟩, hmax⟩ := Finite.exists_max
      (fun x : {x : Subgroup G × Subgroup G // Bad x.1 x.2} => Nat.card x.1.2)
    exact ⟨W, T, hbad, fun W' T' h => hmax ⟨(W', T'), h⟩⟩
  obtain ⟨W, T, ⟨hW, hWcomp, hWq, hWfail, P, rfl, hPnorm⟩, hmax⟩ := extremal
  set T := (P : Subgroup (signalizerNormalizerCompletion prime rank actor values W)).map
    (signalizerNormalizerCompletion prime rank actor values W).subtype
  set Z := embeddedOrderThompsonCenter T
  set L := signalizerNormalizerCompletion prime rank actor values Z
  obtain ⟨hTne, hZne, hTcomp, hZcomp, hLcomp, hfactor, hWL⟩ := zj_normalizer_refinement prime rank q
    prime_prime q_prime hq actor elementary large' values conditions locally_complete W hW hWcomp
    hWq P hPnorm
  have hTq : IsPGroup q T := P.isPGroup'.map _
  obtain ⟨hZle, -, -⟩ := embedded_order_thompson_center_properties T actor hPnorm
  have hZq : IsPGroup q Z := hTq.to_le hZle
  obtain ⟨Sstar, hTle, hSstar⟩ := Finite.exists_le_maximal
    (p := signalizerPrimeCompatible prime rank q actor values) (a := T) ⟨hTcomp.1, hTq⟩
  by_cases heq : T = Sstar
  · have hTmax : Maximal (signalizerPrimeCompatible prime rank q actor values) T := heq ▸ hSstar
    obtain ⟨c, hc⟩ := signalizer_prime_transitivity prime rank q prime_prime q_prime distinct actor
      elementary large values conditions.coprime conditions.normalized conditions.balanced S T
      hSmaximal hTmax
    refine hWfail ⟨c, ?_⟩
    have hcL : conjugateSubgroup c.val M = L := by
      rw [hM, conjugate_zj_normalizer_completion prime rank actor values conditions.balanced S c, hc]
    rw [hcL]
    exact hfactor.symm
  · have hlt : T < Sstar := lt_of_le_of_ne hTle heq
    have hSstarcomp : solvableSignalizerCompatible prime rank actor values Sstar :=
      ⟨hSstar.prop.1, solvable_of_pgroup Sstar hSstar.prop.2⟩
    obtain ⟨R, hRcomp, hRq, hRL, hcard⟩ := zj_larger_normalizer prime rank q prime_prime q_prime
      actor elementary large' values conditions locally_complete T Sstar hTne hTcomp hSstarcomp
      hSstar.prop.2 hlt
    obtain ⟨P', hRP', hP'norm⟩ := normalized_pgroup_actor_sylow_containing prime q prime_prime
      q_prime actor L R actor_pgroup hLcomp.1.1
      (signalizer_subgroup_coprime prime rank prime_prime actor elementary rank_large values
        conditions.coprime L hLcomp.1.1 hLcomp.1.2) hRL hRq hRcomp.1.1
    have hZcontrolled : NormalizerControlled prime rank q actor values M Z := by
      by_contra hZfail
      have hle := hmax Z ((P' : Subgroup L).map L.subtype)
        ⟨hZne, hZcomp, hZq, hZfail, P', rfl, hP'norm⟩
      exact absurd (hcard.trans_le ((Subgroup.card_le_of_le hRP').trans hle)) (lt_irrefl _)
    exact hWfail (normalizer_controlled_transfer prime rank q prime_prime q_prime actor elementary
      large' values conditions locally_complete M Z W hMcomp hLcomp hW hWcomp hWq hWL hZcontrolled
      hfactor.symm)

theorem complete_of_locallyComplete_of_five_le
    (prime rank q : ℕ) (prime_prime : prime.Prime) (q_prime : q.Prime) (hq : 5 ≤ q)
    (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (q_member : q ∈ signalizerSpectrum prime rank actor values) :
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
  obtain ⟨_, selected, member, divides⟩ := q_member
  obtain ⟨sylow, normalized, nontrivial⟩ := normalized_subgroup_invariant_sylow_nontrivial
    prime q prime_prime q_prime actor (values selected)
    (elementary_abelian_isPGroup prime actor elementary) (conditions.normalized selected member)
    (conditions.coprime selected member) divides
  set W₀ := (sylow : Subgroup (values selected)).map (values selected).subtype with hW₀
  have hW₀q : IsPGroup q W₀ := sylow.isPGroup'.map _
  have hW₀comp : solvableSignalizerCompatible prime rank actor values W₀ :=
    solvable_signalizer_compatible_of_le prime rank actor values (values selected) W₀
      (solvable_signalizer_value_compatible prime rank actor values conditions selected member)
      (Subgroup.map_subtype_le _) normalized
  obtain ⟨S, hS⟩ := (Set.toFinite {T : Subgroup G |
      solvableSignalizerCompatible prime rank actor values T ∧ IsPGroup q T ∧ W₀ ≤ T}).exists_maximal
    ⟨W₀, hW₀comp, hW₀q, le_rfl⟩
  have hSmax : ∀ T : Subgroup G, solvableSignalizerCompatible prime rank actor values T →
      IsPGroup q T → S ≤ T → T = S := fun T hT hTq hST =>
    le_antisymm (hS.2 ⟨hT, hTq, hS.1.2.2.trans hST⟩ hST) hST
  have hSne : S ≠ ⊥ := fun h => nontrivial (le_bot_iff.mp (h ▸ hS.1.2.2))
  obtain ⟨hMcomp, hfact⟩ := zj_global_normalizer_control prime rank q prime_prime q_prime hq actor
    elementary large values conditions locally_complete S hSne hS.1.1 hS.1.2.1 hSmax
  exact signalizer_normalizer_factorization_complete prime rank q prime_prime q_prime actor _
    elementary large values conditions locally_complete ⟨q_prime, selected, member, divides⟩
    hMcomp hfact

end CFSG.SignalizerFunctorTheorem.Solvable
