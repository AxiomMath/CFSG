module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FLinearField
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ExcRank
import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankChev
import CFSG.Timmesfeld.RankTwo.LevisExtras
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldNF
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Chevalley
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)


theorem uc22s2114r4f_exceptional_root_pair (τ : Tag) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [CharP K 2] :
    ∃ ρ : (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) →*
        adjointGroup τ K,
      Function.Injective ρ ∧ ∀ (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 2) K ×
        SpecialLinearGroup (Fin 2) K), entrywiseAdjointAut τ σ (ρ A) =
          ρ (SpecialLinearGroup.map σ.toRingHom A.1, SpecialLinearGroup.map σ.toRingHom A.2) := by
  obtain ⟨α, hroot, horth⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_four_roots τ
      hτ
  have hroot' : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  let j : Fin 4 → SpecialLinearGroup (Fin 2) K →* adjointGroup τ K := fun i =>
    (rootSL2 τ K (α i)).codRestrict (adjointGroup τ K)
      (exceptional_Lang_root_rank_one_data τ K (α i)).2.2.2.2.1
  have hj : ∀ i, Function.Injective (j i) := fun i A B hAB =>
    (even_Chevalley_pinned_root_SL2_maps τ K (hroot' i)).1 (congrArg Subtype.val hAB)
  have hc : ∀ A B, Commute (j 0 A) (j 1 B) := by
    intro A B
    obtain ⟨h0, hp, hm⟩ := horth 0 1 (by decide)
    have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
      fun hv hr => by rw [← RootOps.isRootB_iff, hv] at hr; exact Bool.false_ne_true hr
    exact Subtype.ext (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
      (hroot' 0) (hroot' 1) h0 (hnot hp) (hnot hm) _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)
  let ρ := (j 0).noncommCoprod (j 1) hc
  have hfield : ∀ i (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 2) K),
      entrywiseAdjointAut τ σ (j i A) = j i (SpecialLinearGroup.map σ.toRingHom A) := by
    intro i σ A
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut]
    exact entrywise_rootSL2_of_field σ.toRingHom (α i) A
  refine ⟨ρ, CFSG.Timmesfeld.LevisExtras.injective_noncommCoprod (hj 0) (hj 1) hc, ?_⟩
  intro σ A
  change entrywiseAdjointAut τ σ (j 0 A.1 * j 1 A.2) =
    j 0 (SpecialLinearGroup.map σ.toRingHom A.1) * j 1 (SpecialLinearGroup.map σ.toRingHom A.2)
  rw [map_mul, hfield, hfield]

theorem uc22s2114r4f_higher_root_pair (τ : Tag) (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [CharP K 2] :
    ∃ ρ : (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) →*
        adjointGroup τ K,
      Function.Injective ρ ∧ ∀ (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 2) K ×
        SpecialLinearGroup (Fin 2) K), entrywiseAdjointAut τ σ (ρ A) =
          ρ (SpecialLinearGroup.map σ.toRingHom A.1, SpecialLinearGroup.map σ.toRingHom A.2)  :=
  uc22s2114r4f_exceptional_root_pair τ (hτ.elim Or.inl (fun h => Or.inr (Or.inr h)))

theorem uc22s2114r4f_ordinary_root_pair (τ : Tag) (hτ : τ = .F4 ∨ τ = .E8)
    {K : Type} [Field K] [CharP K 2] :
    ∃ ρ : (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) →*
        adjointGroup τ K,
      Function.Injective ρ ∧ ∀ (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 2) K ×
        SpecialLinearGroup (Fin 2) K), entrywiseAdjointAut τ σ (ρ A) =
          ρ (SpecialLinearGroup.map σ.toRingHom A.1, SpecialLinearGroup.map σ.toRingHom A.2)  :=
  uc22s2114r4f_higher_root_pair τ (hτ.elim Or.inl (fun h => Or.inr (Or.inr h)))

theorem uc22s2114r4f_f4_root_pair {K : Type} [Field K] [CharP K 2] :
    ∃ ρ : (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) →*
        adjointGroup .F4 K,
      Function.Injective ρ ∧ ∀ (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 2) K ×
        SpecialLinearGroup (Fin 2) K), entrywiseAdjointAut .F4 σ (ρ A) =
          ρ (SpecialLinearGroup.map σ.toRingHom A.1, SpecialLinearGroup.map σ.toRingHom A.2) :=
  uc22s2114r4f_ordinary_root_pair .F4 (Or.inl rfl)

theorem uc22s2114r4f_exists_fpf_f4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (σ : K ≃+* K) (hσ : orderOf σ = r) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* adjointGroup .F4 K, Function.Injective ι ∧
            ∀ a, entrywiseAdjointAut .F4 σ (ι a) = ι (κ a) := by
  obtain ⟨q, hq, hq7, hqr, -, -, Q, _, _, hQ, τ, hτ, j, hj, hσj⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_sl2 hf hK hr hr5 σ hσ
  obtain ⟨ρ, hρ, hρfield⟩ := uc22s2114r4f_f4_root_pair (K := K)
  let A := Q × Q
  let κ : A →* A := τ.prodMap τ
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 2) (by
    change Nat.card (Q × Q) = q ^ 2
    rw [Nat.card_prod, hQ]
    ring)
  have hAc : ¬ IsCyclic A := by
    intro hc
    have h := (Group.isCyclic_prod_iff.1 hc).2.2
    simp only [hQ] at h
    exact hq.ne_one (Nat.coprime_self q |>.1 h)
  have hκ : ∀ a : A, κ a = a → a = 1 := fun a ha =>
    Prod.ext (hτ a.1 (congrArg Prod.fst ha)) (hτ a.2 (congrArg Prod.snd ha))
  let ι : A →* adjointGroup .F4 K := ρ.comp (j.prodMap j)
  have hι : Function.Injective ι := hρ.comp (by
    intro a b hab
    exact Prod.ext (hj (congrArg Prod.fst hab)) (hj (congrArg Prod.snd hab)))
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change entrywiseAdjointAut .F4 σ (ρ (j a.1, j a.2)) = ρ (j (τ a.1), j (τ a.2))
  rw [hρfield, hσj, hσj]

theorem uc22s2114r4f_exists_fixed_three_f4 {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) :
    ∃ X : Subgroup (adjointGroup .F4 K), IsPGroup 3 X ∧ ¬ IsCyclic X ∧
      ∀ x ∈ X, entrywiseAdjointAut .F4 σ x = x := by
  obtain ⟨X, hfix, hX, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_fixed_rank_four .F4 (Or.inl rfl) σ
  exact ⟨X, hX.isPGroup, PartTwo.s16c7_not_isCyclic_of_elemAbelian Nat.prime_three
    hX (by rw [hcard]; norm_num), fun x hx => hfix hx⟩

theorem uc22s2114r4f_exists_fpf_e8 {K : Type} [Field K] [Finite K] [CharP K 2]
    {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (σ : K ≃+* K) (hσ : orderOf σ = r) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* adjointGroup .E8 K, Function.Injective ι ∧
            ∀ a, entrywiseAdjointAut .E8 σ (ι a) = ι (κ a) := by
  obtain ⟨q, hq, hq7, hqr, -, -, Q, _, _, hQ, τ, hτ, j, hj, hσj⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_sl2 hf hK hr hr5 σ hσ
  obtain ⟨ρ, hρ, hρfield⟩ := uc22s2114r4f_ordinary_root_pair .E8 (Or.inr rfl) (K := K)
  let A := Q × Q
  let κ : A →* A := τ.prodMap τ
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 2) (by
    change Nat.card (Q × Q) = q ^ 2
    rw [Nat.card_prod, hQ]
    ring)
  have hAc : ¬ IsCyclic A := by
    intro hc
    have h := (Group.isCyclic_prod_iff.1 hc).2.2
    simp only [hQ] at h
    exact hq.ne_one (Nat.coprime_self q |>.1 h)
  have hκ : ∀ a : A, κ a = a → a = 1 := fun a ha =>
    Prod.ext (hτ a.1 (congrArg Prod.fst ha)) (hτ a.2 (congrArg Prod.snd ha))
  let ι : A →* adjointGroup .E8 K := ρ.comp (j.prodMap j)
  have hι : Function.Injective ι := hρ.comp (by
    intro a b hab
    exact Prod.ext (hj (congrArg Prod.fst hab)) (hj (congrArg Prod.snd hab)))
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change entrywiseAdjointAut .E8 σ (ρ (j a.1, j a.2)) = ρ (j (τ a.1), j (τ a.2))
  rw [hρfield, hσj, hσj]

theorem uc22s2114r4f_exists_fixed_three_e8 {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) :
    ∃ X : Subgroup (adjointGroup .E8 K), IsPGroup 3 X ∧ ¬ IsCyclic X ∧
      ∀ x ∈ X, entrywiseAdjointAut .E8 σ x = x := by
  obtain ⟨X, hfix, hX, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_fixed_rank_four .E8
      (Or.inr (Or.inr (Or.inr rfl))) σ
  exact ⟨X, hX.isPGroup, PartTwo.s16c7_not_isCyclic_of_elemAbelian Nat.prime_three
    hX (by rw [hcard]; norm_num), fun x hx => hfix hx⟩

theorem uc22s2114r4f_exists_fpf_e7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (σ : K ≃+* K) (hσ : orderOf σ = r) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* adjointGroup .E7 K, Function.Injective ι ∧
            ∀ a, entrywiseAdjointAut .E7 σ (ι a) = ι (κ a) := by
  obtain ⟨q, hq, hq7, hqr, -, -, Q, _, _, hQ, τ, hτ, j, hj, hσj⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_sl2 hf hK hr hr5 σ hσ
  obtain ⟨ρ, hρ, hρfield⟩ := uc22s2114r4f_higher_root_pair .E7 (Or.inr (Or.inl rfl)) (K := K)
  let A := Q × Q
  let κ : A →* A := τ.prodMap τ
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 2) (by
    change Nat.card (Q × Q) = q ^ 2
    rw [Nat.card_prod, hQ]
    ring)
  have hAc : ¬ IsCyclic A := by
    intro hc
    have h := (Group.isCyclic_prod_iff.1 hc).2.2
    simp only [hQ] at h
    exact hq.ne_one (Nat.coprime_self q |>.1 h)
  have hκ : ∀ a : A, κ a = a → a = 1 := fun a ha =>
    Prod.ext (hτ a.1 (congrArg Prod.fst ha)) (hτ a.2 (congrArg Prod.snd ha))
  let ι : A →* adjointGroup .E7 K := ρ.comp (j.prodMap j)
  have hι : Function.Injective ι := hρ.comp (by
    intro a b hab
    exact Prod.ext (hj (congrArg Prod.fst hab)) (hj (congrArg Prod.snd hab)))
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change entrywiseAdjointAut .E7 σ (ρ (j a.1, j a.2)) = ρ (j (τ a.1), j (τ a.2))
  rw [hρfield, hσj, hσj]

theorem uc22s2114r4f_exists_fixed_three_e7 {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) :
    ∃ X : Subgroup (adjointGroup .E7 K), IsPGroup 3 X ∧ ¬ IsCyclic X ∧
      ∀ x ∈ X, entrywiseAdjointAut .E7 σ x = x := by
  obtain ⟨X, hfix, hX, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_fixed_rank_four .E7
      (Or.inr (Or.inr (Or.inl rfl))) σ
  exact ⟨X, hX.isPGroup, PartTwo.s16c7_not_isCyclic_of_elemAbelian Nat.prime_three
    hX (by rw [hcard]; norm_num), fun x hx => hfix hx⟩

theorem uc22s2114r4f_exists_fpf_e6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (σ : K ≃+* K) (hσ : orderOf σ = r) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* adjointGroup .E6 K, Function.Injective ι ∧
            ∀ a, entrywiseAdjointAut .E6 σ (ι a) = ι (κ a) := by
  obtain ⟨q, hq, hq7, hqr, -, -, Q, _, _, hQ, τ, hτ, j, hj, hσj⟩ :=
    uc22s2114r4f_exists_fpf_nonsplit_sl2 hf hK hr hr5 σ hσ
  obtain ⟨ρ, hρ, hρfield⟩ := uc22s2114r4f_exceptional_root_pair .E6 (Or.inr (Or.inl rfl)) (K := K)
  let A := Q × Q
  let κ : A →* A := τ.prodMap τ
  have hAp : IsPGroup q A := IsPGroup.of_card (n := 2) (by
    change Nat.card (Q × Q) = q ^ 2
    rw [Nat.card_prod, hQ]
    ring)
  have hAc : ¬ IsCyclic A := by
    intro hc
    have h := (Group.isCyclic_prod_iff.1 hc).2.2
    simp only [hQ] at h
    exact hq.ne_one (Nat.coprime_self q |>.1 h)
  have hκ : ∀ a : A, κ a = a → a = 1 := fun a ha =>
    Prod.ext (hτ a.1 (congrArg Prod.fst ha)) (hτ a.2 (congrArg Prod.snd ha))
  let ι : A →* adjointGroup .E6 K := ρ.comp (j.prodMap j)
  have hι : Function.Injective ι := hρ.comp (by
    intro a b hab
    exact Prod.ext (hj (congrArg Prod.fst hab)) (hj (congrArg Prod.snd hab)))
  refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, ?_⟩
  intro a
  change entrywiseAdjointAut .E6 σ (ρ (j a.1, j a.2)) = ρ (j (τ a.1), j (τ a.2))
  rw [hρfield, hσj, hσj]

theorem uc22s2114r4f_exists_fixed_three_e6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) :
    ∃ X : Subgroup (adjointGroup .E6 K), IsPGroup 3 X ∧ ¬ IsCyclic X ∧
      ∀ x ∈ X, entrywiseAdjointAut .E6 σ x = x := by
  obtain ⟨X, hfix, hX, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_fixed_rank_four .E6
      (Or.inr (Or.inl rfl)) σ
  exact ⟨X, hX.isPGroup, PartTwo.s16c7_not_isCyclic_of_elemAbelian Nat.prime_three
    hX (by rw [hcard]; norm_num), fun x hx => hfix hx⟩

section Field


theorem uc22s2114r4f_f4_field_descent {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .F4 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ ∃ σ : K ≃+* K, orderOf σ = r ∧
        ∃ ε : Y ≃* adjointGroup .F4 K, ∀ x, ε (θ x) = entrywiseAdjointAut .F4 σ (ε x) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hY.chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e : Y ≃* adjointGroup .F4 K := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field .F4 K)).trans QuotientGroup.quotientBot)
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hx]
  obtain ⟨σ, δ, hσ, hδ⟩ := CFSG.HardMathSupport.Lang.E6Descent.even_F4_odd_prime_field_descent
    hadm.2.1 K hK hr (by omega) (MulAut.congr e θ) hθ' hout'
  change MulAut (adjointGroup Tag.F4 K) at δ
  change δ * MulAut.congr e θ * δ⁻¹ = entrywiseAdjointAut Tag.F4 σ at hδ
  have hrf : r ∣ f := (CFSG.RankThree.PartOne.card_semilinearFixedSubfield
    Nat.prime_two hadm.2.1 hK hσ).1
  refine ⟨hrf, K, inferInstance, inferInstance, inferInstance, hK, σ, hσ, e.trans δ, ?_⟩
  intro x
  have hconj := congrArg (fun α : MulAut (adjointGroup .F4 K) => α (δ (e x))) hδ
  have hθe : (MulAut.congr e θ) (e x) = e (θ x) := by
    change e (θ (e.symm (e x))) = e (θ x)
    rw [MulEquiv.symm_apply_apply]
  change δ ((MulAut.congr e θ) (δ.symm (δ (e x)))) =
    entrywiseAdjointAut .F4 σ (δ (e x)) at hconj
  rw [MulEquiv.symm_apply_apply, hθe] at hconj
  exact hconj

theorem uc22s2114r4f_fieldSubgroups_of_f4 {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .F4 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hrf, K, _, _, _, hK, σ, hσ, e, he⟩ :=
    uc22s2114r4f_f4_field_descent hY hr hr5 θ hθ hout
  have hε : ∀ x, θ (e.symm x) = e.symm (entrywiseAdjointAut .F4 σ x) := by
    intro x
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he (e.symm x)
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_f4 σ
    let j : X →* Y := e.symm.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := e.symm.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg e.symm (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_f4 hY.admissible.2.1 hK hr hr5 σ hσ
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg e.symm (hσι a))

end Field

theorem uc22s2114r4f_e8_field_descent {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .E8 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ ∃ σ : K ≃+* K, orderOf σ = r ∧
        ∃ ε : Y ≃* adjointGroup .E8 K, ∀ x, ε (θ x) = entrywiseAdjointAut .E8 σ (ε x) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hY.chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e : Y ≃* adjointGroup .E8 K := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field .E8 K)).trans QuotientGroup.quotientBot)
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hx]
  have hθr : MulAut.congr e θ ^ r = 1 := hθ' ▸ pow_orderOf_eq_one (MulAut.congr e θ)
  obtain ⟨σ, δ, hσ, hδ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.exists_conj_entrywise_excE
      (Or.inr (Or.inr rfl)) hr (by omega) (by intro _; omega) hθr hout'
  have hrf : r ∣ f := (CFSG.RankThree.PartOne.card_semilinearFixedSubfield
    Nat.prime_two hadm.2.1 hK hσ).1
  refine ⟨hrf, K, inferInstance, inferInstance, inferInstance, hK, σ, hσ, e.trans δ, ?_⟩
  intro x
  have hconj := congrArg (fun α : MulAut (adjointGroup .E8 K) => α (δ (e x))) hδ
  have hθe : (MulAut.congr e θ) (e x) = e (θ x) := by
    change e (θ (e.symm (e x))) = e (θ x)
    rw [MulEquiv.symm_apply_apply]
  change δ ((MulAut.congr e θ) (δ.symm (δ (e x)))) =
    entrywiseAdjointAut .E8 σ (δ (e x)) at hconj
  rw [MulEquiv.symm_apply_apply, hθe] at hconj
  exact hconj

theorem uc22s2114r4f_fieldSubgroups_of_e8 {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .E8 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hrf, K, _, _, _, hK, σ, hσ, e, he⟩ :=
    uc22s2114r4f_e8_field_descent hY hr hr5 θ hθ hout
  have hε : ∀ x, θ (e.symm x) = e.symm (entrywiseAdjointAut .E8 σ x) := by
    intro x
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he (e.symm x)
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_e8 σ
    let j : X →* Y := e.symm.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := e.symm.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg e.symm (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_e8 hY.admissible.2.1 hK hr hr5 σ hσ
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg e.symm (hσι a))

theorem uc22s2114r4f_e7_field_descent {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .E7 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ ∃ σ : K ≃+* K, orderOf σ = r ∧
        ∃ ε : Y ≃* adjointGroup .E7 K, ∀ x, ε (θ x) = entrywiseAdjointAut .E7 σ (ε x) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hY.chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e : Y ≃* adjointGroup .E7 K := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field .E7 K)).trans QuotientGroup.quotientBot)
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hx]
  have hθr : MulAut.congr e θ ^ r = 1 := hθ' ▸ pow_orderOf_eq_one (MulAut.congr e θ)
  obtain ⟨σ, δ, hσ, hδ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.exists_conj_entrywise_excE
      (Or.inr (Or.inl rfl)) hr (by omega) (by intro _; omega) hθr hout'
  have hrf : r ∣ f := (CFSG.RankThree.PartOne.card_semilinearFixedSubfield
    Nat.prime_two hadm.2.1 hK hσ).1
  refine ⟨hrf, K, inferInstance, inferInstance, inferInstance, hK, σ, hσ, e.trans δ, ?_⟩
  intro x
  have hconj := congrArg (fun α : MulAut (adjointGroup .E7 K) => α (δ (e x))) hδ
  have hθe : (MulAut.congr e θ) (e x) = e (θ x) := by
    change e (θ (e.symm (e x))) = e (θ x)
    rw [MulEquiv.symm_apply_apply]
  change δ ((MulAut.congr e θ) (δ.symm (δ (e x)))) =
    entrywiseAdjointAut .E7 σ (δ (e x)) at hconj
  rw [MulEquiv.symm_apply_apply, hθe] at hconj
  exact hconj

theorem uc22s2114r4f_fieldSubgroups_of_e7 {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .E7 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hrf, K, _, _, _, hK, σ, hσ, e, he⟩ :=
    uc22s2114r4f_e7_field_descent hY hr hr5 θ hθ hout
  have hε : ∀ x, θ (e.symm x) = e.symm (entrywiseAdjointAut .E7 σ x) := by
    intro x
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he (e.symm x)
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_e7 σ
    let j : X →* Y := e.symm.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := e.symm.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg e.symm (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_e7 hY.admissible.2.1 hK hr hr5 σ hσ
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg e.symm (hσι a))

theorem uc22s2114r4f_four_le_pRank_three_e6 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ}
    (hX : LieModel (BarInf L) .E6 0 2 f) : 4 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hX.chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e := eb.symm.trans e0
  obtain ⟨E, hE, hcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank.centralCoverFour_adjointQuotient_of_charTwo
      (K := K) (Or.inr (Or.inl rfl)) (Bar2 L)
      (e.toMonoidHom.comp (QuotientGroup.mk' (center (Bar2 L))))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun y hy => by simpa using hy)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

theorem uc22s2114r4f_e6_field_descent {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .E6 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ f ∧ ∃ σ : K ≃+* K, orderOf σ = r ∧
        ∃ ε : Y ≃* adjointGroup .E6 K, ∀ x, ε (θ x) = entrywiseAdjointAut .E6 σ (ε x) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hY.chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e : Y ≃* adjointGroup .E6 K := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field .E6 K)).trans QuotientGroup.quotientBot)
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hx]
  have hθr : MulAut.congr e θ ^ r = 1 := hθ' ▸ pow_orderOf_eq_one (MulAut.congr e θ)
  obtain ⟨σ, δ, hσ, hδ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.exists_conj_entrywise_excE
      (Or.inl rfl) hr (by omega) (by intro _; omega) hθr hout'
  have hrf : r ∣ f := (CFSG.RankThree.PartOne.card_semilinearFixedSubfield
    Nat.prime_two hadm.2.1 hK hσ).1
  refine ⟨hrf, K, inferInstance, inferInstance, inferInstance, hK, σ, hσ, e.trans δ, ?_⟩
  intro x
  have hconj := congrArg (fun α : MulAut (adjointGroup .E6 K) => α (δ (e x))) hδ
  have hθe : (MulAut.congr e θ) (e x) = e (θ x) := by
    change e (θ (e.symm (e x))) = e (θ x)
    rw [MulEquiv.symm_apply_apply]
  change δ ((MulAut.congr e θ) (δ.symm (δ (e x)))) =
    entrywiseAdjointAut .E6 σ (δ (e x)) at hconj
  rw [MulEquiv.symm_apply_apply, hθe] at hconj
  exact hconj

theorem uc22s2114r4f_fieldSubgroups_of_e6 {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hY : LieModel Y .E6 0 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (θ : MulAut Y) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    r ∣ f ∧
    (∃ X : Subgroup Y, IsPGroup 3 X ∧ ¬ IsCyclic X ∧ ∀ x ∈ X, θ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ ∀ a, θ (ι a) = ι (κ a)) := by
  obtain ⟨hrf, K, _, _, _, hK, σ, hσ, e, he⟩ :=
    uc22s2114r4f_e6_field_descent hY hr hr5 θ hθ hout
  have hε : ∀ x, θ (e.symm x) = e.symm (entrywiseAdjointAut .E6 σ x) := by
    intro x
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he (e.symm x)
  refine ⟨hrf, ?_, ?_⟩
  · obtain ⟨X, hXp, hXc, hfix⟩ := uc22s2114r4f_exists_fixed_three_e6 σ
    let j : X →* Y := e.symm.toMonoidHom.comp X.subtype
    have hj : Function.Injective j := e.symm.injective.comp X.subtype_injective
    let η := MonoidHom.ofInjective hj
    refine ⟨j.range, hXp.of_equiv η, fun hc => hXc (η.isCyclic.2 hc), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (hε x).trans (congrArg e.symm (hfix x x.2))
  · obtain ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hσι⟩ :=
      uc22s2114r4f_exists_fpf_e6 hY.admissible.2.1 hK hr hr5 σ hσ
    refine ⟨q, hq, hq7, hqr, A, inferInstance, inferInstance, hAp, hAc, κ, hκ,
      e.symm.toMonoidHom.comp ι, e.symm.injective.comp hι, ?_⟩
    intro a
    exact (hε (ι a)).trans (congrArg e.symm (hσι a))

section Multiplier


theorem uc22s2114r4f_card_center_f4 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .F4 0 2 f) :
    Nat.card (center (Bar2 L)) = 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.chevalleyExceptionalModel (by decide)
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) hf)
  have hM := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_hopfMultiplier hK5).2
  have : Subsingleton (griessHopfMultiplier (BarInf L)) :=
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv.subsingleton
  have : Finite (griessHopfMultiplier (BarInf L)) := Finite.of_subsingleton
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  have hcard : Nat.card (griessHopfMultiplier (BarInf L)) = 1 := Nat.card_unique
  rw [hcard] at hd
  exact Nat.dvd_one.1 hd

theorem uc22s2114r4f_not_dvd_radical_f4 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .F4 0 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL, uc22s2114r4f_card_center_f4 hL hf hX, mul_one]
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
  rw [ha]
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem uc22s2114r4f_four_le_pRank_three_f4 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .F4 0 2 f) :
    4 ≤ CFSG.Open.pRank 3 L := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    rw [uc22s2114r4f_card_center_f4 hL hf hX]
    norm_num
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := (LieModel.of_mulEquiv eb hX).chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field .F4 K)).trans QuotientGroup.quotientBot)
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_fixed_rank_four .F4 (Or.inl rfl) (1 : K ≃+* K)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
    ← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three h3Z, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

theorem uc22s2114r4f_card_center_e8 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .E8 0 2 f) :
    Nat.card (center (Bar2 L)) = 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.chevalleyExceptionalModel (by decide)
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) hf)
  have hM := (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.e8_hopfMultiplier hK5).2
  have : Subsingleton (griessHopfMultiplier (BarInf L)) :=
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv.subsingleton
  have : Finite (griessHopfMultiplier (BarInf L)) := Finite.of_subsingleton
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  have hcard : Nat.card (griessHopfMultiplier (BarInf L)) = 1 := Nat.card_unique
  rw [hcard] at hd
  exact Nat.dvd_one.1 hd

theorem uc22s2114r4f_not_dvd_radical_e8 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .E8 0 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL, uc22s2114r4f_card_center_e8 hL hf hX, mul_one]
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
  rw [ha]
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem uc22s2114r4f_four_le_pRank_three_e8 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .E8 0 2 f) :
    4 ≤ CFSG.Open.pRank 3 L := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    rw [uc22s2114r4f_card_center_e8 hL hf hX]
    norm_num
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := (LieModel.of_mulEquiv eb hX).chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field .E8 K)).trans QuotientGroup.quotientBot)
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_fixed_rank_four .E8
      (Or.inr (Or.inr (Or.inr rfl))) (1 : K ≃+* K)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
    ← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three h3Z, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

section F4Body


theorem uc22s2114r4f_fieldDataBody_f4 {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {f : ℕ} (hX : LieModel (BarInf L) .F4 0 2 f) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p X ∧ ¬ IsCyclic X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨hrf, ⟨X, hXp, hXc, hXfix⟩, ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_f4 hX hr hr5 (inducedBarInfAutHom L ⟨b, hbL⟩)
      (orderOf_eq_prime hθr hθ1) hin
  have hf : 3 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_f4 hL hf hX hr (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_f4 hL hf hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_f4 hL hf hX hq (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

end F4Body

theorem uc22s2114r4f_fieldDataBody_e8 {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {f : ℕ} (hX : LieModel (BarInf L) .E8 0 2 f) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p X ∧ ¬ IsCyclic X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨hrf, ⟨X, hXp, hXc, hXfix⟩, ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_e8 hX hr hr5 (inducedBarInfAutHom L ⟨b, hbL⟩)
      (orderOf_eq_prime hθr hθ1) hin
  have hf : 3 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_e8 hL hf hX hr (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_e8 hL hf hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_e8 hL hf hX hq (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

section E7Multiplier


theorem uc22s2114r4f_card_center_e7 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .E7 0 2 f) :
    Nat.card (center (Bar2 L)) = 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.chevalleyExceptionalModel (by decide)
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨em⟩ := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e7_hopfMultiplier hK5).2
  have hgcd : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    rw [hK]
    exact Nat.coprime_two_left.2 (Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one)
  rw [hgcd] at em
  have : Subsingleton (griessHopfMultiplier (AdjointQuotient .E7 K)) :=
    em.injective.subsingleton
  have : Subsingleton (griessHopfMultiplier (BarInf L)) :=
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv.subsingleton
  have : Finite (griessHopfMultiplier (BarInf L)) := Finite.of_subsingleton
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  have hcard : Nat.card (griessHopfMultiplier (BarInf L)) = 1 := Nat.card_unique
  rw [hcard] at hd
  exact Nat.dvd_one.1 hd

theorem uc22s2114r4f_not_dvd_radical_e7 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .E7 0 2 f)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL, uc22s2114r4f_card_center_e7 hL hf hX, mul_one]
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
  rw [ha]
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem uc22s2114r4f_four_le_pRank_three_e7 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f) (hX : LieModel (BarInf L) .E7 0 2 f) :
    4 ≤ CFSG.Open.pRank 3 L := by
  have h3Z : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    rw [uc22s2114r4f_card_center_e7 hL hf hX]
    norm_num
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := (LieModel.of_mulEquiv eb hX).chevalleyExceptionalModel (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let e := e0.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot_field .E7 K)).trans QuotientGroup.quotientBot)
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc.exists_fixed_rank_four .E7
      (Or.inr (Or.inr (Or.inl rfl))) (1 : K ≃+* K)
  rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num),
    ← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three h3Z, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

theorem uc22s2114r4f_fieldDataBody_e7 {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {f : ℕ} (hX : LieModel (BarInf L) .E7 0 2 f) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p X ∧ ¬ IsCyclic X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨hrf, ⟨X, hXp, hXc, hXfix⟩, ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_e7 hX hr hr5 (inducedBarInfAutHom L ⟨b, hbL⟩)
      (orderOf_eq_prime hθr hθ1) hin
  have hf : 3 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_e7 hL hf hX hr (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_e7 hL hf hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_e7 hL hf hX hq (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

end E7Multiplier

end Multiplier

section E6Multiplier


theorem uc22s2114r4f_card_center_e6_dvd_three {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f)
    (hX : LieModel (BarInf L) .E6 0 2 f) : Nat.card (center (Bar2 L)) ∣ 3 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.chevalleyExceptionalModel (by decide)
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact (by norm_num : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨em⟩ := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier hK5).2
  have hcardM : Nat.card (griessHopfMultiplier (AdjointQuotient .E6 K)) =
      Nat.gcd 3 (Nat.card K - 1) := (Nat.card_congr em.toEquiv).trans (by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])
  have hcard : Nat.card (griessHopfMultiplier (BarInf L)) = Nat.gcd 3 (Nat.card K - 1) :=
    (Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv).trans hcardM
  have : Finite (griessHopfMultiplier (BarInf L)) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact Nat.gcd_ne_zero_left (by decide))
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  rw [hcard] at hd
  exact hd.trans (Nat.gcd_dvd_left _ _)

theorem uc22s2114r4f_not_dvd_radical_e6 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) {f : ℕ} (hf : 3 ≤ f)
    (hX : LieModel (BarInf L) .E6 0 2 f) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    ¬ q ∣ Nat.card (CFSG.solvableRadical L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [uc22s2114r3f_card_solvableRadical hL]
  intro h
  rcases hq.dvd_mul.1 h with h2 | h3
  · obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)).exists_card_eq
    rw [ha] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
  · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
      (h3.trans (uc22s2114r4f_card_center_e6_dvd_three hL hf hX)))

theorem uc22s2114r4f_fieldDataBody_e6 {G : Type} [Group G] [Finite G]
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {f : ℕ} (hX : LieModel (BarInf L) .E6 0 2 f) {b : G}
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hbr : orderOf b = r) (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    (¬ r ∣ Nat.card (CFSG.solvableRadical L)) ∧
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
      ∃ X : Subgroup (BarInf L), IsPGroup p X ∧ ¬ IsCyclic X ∧
        ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
    (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
      ¬ q ∣ Nat.card (CFSG.solvableRadical L) ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  have : Fact r.Prime := ⟨hr⟩
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : normalizer (L : Set G)) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  have hθ1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => hin ⟨1, by rw [map_one, h1]⟩
  obtain ⟨hrf, ⟨X, hXp, hXc, hXfix⟩, ⟨q, hq, hq7, hqr, A, _, _, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩ :=
    uc22s2114r4f_fieldSubgroups_of_e6 hX hr hr5 (inducedBarInfAutHom L ⟨b, hbL⟩)
      (orderOf_eq_prime hθr hθ1) hin
  have hf : 3 ≤ f := by
    have := Nat.le_of_dvd (by have := hX.admissible.2.1; omega : 0 < f) hrf
    omega
  exact ⟨uc22s2114r4f_not_dvd_radical_e6 hL hf hX hr (by omega) (by omega),
    ⟨3, Nat.prime_three, by norm_num, hSg.four_mem 3 Nat.prime_three (by norm_num)
      ((uc22s2114r4f_four_le_pRank_three_e6 hL hX).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) hL.1.le)), X, hXp, hXc, hXfix⟩,
    ⟨q, hq, hq7, hqr, uc22s2114r4f_not_dvd_radical_e6 hL hf hX hq (by omega) (by omega),
      A, inferInstance, inferInstance, hAp, hAc, κ, hκ, ι, hι, hθι⟩⟩

end E6Multiplier

end CFSG.LocalAnalysis.UniquenessCase.UC22
