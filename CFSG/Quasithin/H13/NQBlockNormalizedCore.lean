module

public import CFSG.Quasithin.H13.NQBlockCanonicalWitnesses

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement Pointwise

@[expose] noncomputable def normalizerResidualAction {K : Type*} [Group K] (X : Subgroup K) :
    normalizer (X : Set K) →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
  (autQuotient (frattini (X ⧸ CFSG.pCore 2 X))).comp
    ((autQuotient (CFSG.pCore 2 X)).comp X.normalizerMonoidHom)

theorem normalizerResidualAction_mk {K : Type*} [Group K] (X : Subgroup K)
    (g : normalizer (X : Set K)) (x : X) :
    normalizerResidualAction X g (((x : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸
      frattini (X ⧸ CFSG.pCore 2 X)) =
      ((((X.normalizerMonoidHom g x : X) : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸
        frattini (X ⧸ CFSG.pCore 2 X)) :=
  rfl

theorem normalizerResidualAction_eq {K : Type*} [Group K] (X : Subgroup K) [X.Characteristic]
    (g : normalizer (X : Set K)) : normalizerResidualAction X g = residualAction X g := by
  ext w
  induction w using QuotientGroup.induction_on with
  | H w =>
    induction w using QuotientGroup.induction_on with
    | H x => rfl

theorem isSolvable_of_isPGroup_quotient_pCore {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) : Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsSolvable (CFSG.pCore 2 X) := by
    have := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)).isNilpotent
    infer_instance
  have : Group.IsSolvable (X ⧸ CFSG.pCore 2 X) := by
    have := hP.isNilpotent
    infer_instance
  refine Group.isSolvable_of_ker_le_range (CFSG.pCore 2 X).subtype
    (QuotientGroup.mk' (CFSG.pCore 2 X)) fun x hx => ?_
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem le_fitting_of_perfect_normalizer
    {M : Type*} [Group M] [Finite M]
    (hSQT : CFSG.IsStronglyQuasithin M) (hO2 : CFSG.pCore 2 M = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup M)) (hq : ¬ CFSG.IsQuasisimple M)
    {V A : Subgroup M} (hV : Group.IsPerfect V) (hAV : A ≤ V)
    (hVA : V ≤ normalizer (A : Set M)) (hAs : Group.IsSolvable A)
    (hA2 : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 A) :
    A ≤ CFSG.fittingSubgroup M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hFne, hodd, -, -, hcores⟩ := odd_Fitting_cores_self hSQT hO2 hLC hq
  obtain ⟨-, hcrit⟩ := all_prime_critical_actions_self hSQT hO2 hLC hq
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr ((one_lt_card_iff_ne_bot _).mpr hFne)
  have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hr))
  obtain ⟨-, B, hBc, hB, hker⟩ := hcrit r hr
  set α : V →* MulAut (CFSG.pCore r M) := MulAut.conjNormal.comp V.subtype with hα
  have hχ : ∀ v : V, criticalAction B v = ((frattiniAction B).comp α) v := fun v => rfl
  suffices h : ∀ a ∈ A, criticalAction B a = 1 by
    intro a ha
    rw [← hker]
    exact h a ha
  by_cases hα1 : α = 1
  · intro a ha
    rw [hχ ⟨a, hAV ha⟩, MonoidHom.comp_apply, hα1, MonoidHom.one_apply, map_one]
  have hrank : CFSG.Open.pRank r (⊤ : Subgroup (CFSG.pCore r M)) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact (hcores r hr).2
  obtain ⟨-, -, -, -, -, hJq, hJcen, -, -⟩ := critical_rank_two_action_recognition hr2
    CFSG.pCore_isPGroup hrank B hB.pow_eq_one hB.ker_isPGroup α hα1 _ rfl
  have hJq' := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hJq
  set ρ := (frattiniAction B).comp α with hρ
  set ψ : A →* ρ.range := ρ.rangeRestrict.comp (inclusion hAV) with hψ
  have hψn : ψ.range.Normal := by
    refine ⟨fun z hz j => ?_⟩
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨v, rfl⟩ := ρ.rangeRestrict_surjective j
    have hva : (v : M) * a * (v : M)⁻¹ ∈ A := (mem_normalizer_iff.mp (hVA v.2) a).mp a.2
    refine ⟨⟨_, hva⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hψs : Group.IsSolvable ψ.range :=
    Group.isSolvable_of_surjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hcen := le_center_of_isSolvable_of_isQuasisimple hJq' ψ.range hψs
  have hsq : ∀ a : A, ψ a * ψ a = 1 := by
    intro a
    rcases (hJcen (ψ a)).mp (hcen ⟨a, rfl⟩) with h | h
    · have h' : ψ a = 1 := Subtype.ext h
      rw [h', one_mul]
    · apply Subtype.ext
      ext w
      rw [Subgroup.coe_mul, MulAut.mul_apply, h, h, inv_inv]
      rfl
  have hK2 : IsPGroup 2 (A ⧸ ψ.ker) := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow,
      pow_two, hsq]
  have htop := hA2 ψ.ker hK2
  intro a ha
  have h1 : ψ ⟨a, ha⟩ = 1 := by
    rw [← MonoidHom.mem_ker, htop]
    exact mem_top _
  have h2 := congrArg Subtype.val h1
  rw [hχ ⟨a, hAV ha⟩]
  exact h2

theorem two_core_subgroupOf_eq_of_le_fitting {K : Type*} [Group K] [Finite K] {X : Subgroup K}
    (hXF : X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
      CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K))
    (hodd : Odd (Nat.card (CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K)))) :
    (CFSG.pCore 2 K).subgroupOf X = CFSG.pCore 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup inferInstance
      (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).comap_subtype
  · intro x hx
    rw [mem_subgroupOf]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)) ⟨x, hx⟩
    have hxk : (x : K) ^ 2 ^ k = 1 := by
      have h1 := congrArg Subtype.val (congrArg Subtype.val hk)
      rwa [SubgroupClass.coe_pow, SubgroupClass.coe_pow] at h1
    have hxF : QuotientGroup.mk' (CFSG.pCore 2 K) (x : K) ∈
        CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K) := hXF ⟨x, x.2, rfl⟩
    set y : CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K) := ⟨_, hxF⟩ with hy
    have hyk : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      show (QuotientGroup.mk' (CFSG.pCore 2 K) (x : K)) ^ 2 ^ k = 1
      rw [← map_pow, hxk, map_one]
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K))) :=
      Nat.Coprime.pow_left k (Nat.coprime_comm.mp (Odd.coprime_two_right hodd))
    have h1 : orderOf y = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hyk) hcop) (orderOf_dvd_natCard y)
    rw [orderOf_eq_one_iff] at h1
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 K) (x : K) = 1 := congrArg Subtype.val h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2

theorem exists_two_core_quotient_equiv_map {K : Type*} [Group K] {X : Subgroup K}
    (hNX : (CFSG.pCore 2 K).subgroupOf X = CFSG.pCore 2 X) :
    ∃ φ : X ⧸ CFSG.pCore 2 X ≃* X.map (QuotientGroup.mk' (CFSG.pCore 2 K)),
      ∀ x : X, (φ (x : X ⧸ CFSG.pCore 2 X) : K ⧸ CFSG.pCore 2 K) =
        QuotientGroup.mk' (CFSG.pCore 2 K) (x : K) := by
  classical
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X →* X.map (QuotientGroup.mk' (CFSG.pCore 2 K)),
      ∀ x, (ψ x : K ⧸ CFSG.pCore 2 K) = QuotientGroup.mk' (CFSG.pCore 2 K) (x : K) :=
    ⟨((QuotientGroup.mk' (CFSG.pCore 2 K)).comp X.subtype).codRestrict _
      fun x => ⟨x, x.2, rfl⟩, fun _ => rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨d, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, Subtype.ext (hψ _)⟩
  have hψker : ψ.ker = CFSG.pCore 2 X := by
    rw [← hNX]
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hψ, OneMemClass.coe_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf]
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs), fun x => ?_⟩
  exact hψ x

theorem not_le_of_normal_line {K : Type*} [Group K] [Finite K] {Y X : Subgroup K}
    (hYX : Y ≤ normalizer (X : Set K)) {p : ℕ} [hp : Fact p.Prime]
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ y : Y, ∀ u ∈ U, normalizerResidualAction X (inclusion hYX y) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hNX : (CFSG.pCore 2 K).subgroupOf X = CFSG.pCore 2 X)
    (hcard : Nat.card (X.map (QuotientGroup.mk' (CFSG.pCore 2 K))) = p ^ 2)
    (hexp : ∀ d ∈ X.map (QuotientGroup.mk' (CFSG.pCore 2 K)), d ^ p = 1)
    {Z : Subgroup (K ⧸ CFSG.pCore 2 K)} [Z.Normal]
    (hZX : Z ≤ X.map (QuotientGroup.mk' (CFSG.pCore 2 K))) (hZ : Nat.card Z = p) : False := by
  classical
  set D₀ := X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) with hD₀
  obtain ⟨φ0, hφ0⟩ := exists_two_core_quotient_equiv_map hNX
  have hD0el : IsElementaryAbelian p D₀ :=
    { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by
          rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
          exact hexp _ x.2) }
  have : Fact (IsPGroup p D₀) := ⟨IsPGroup.of_card hcard⟩
  have hΦ : frattini D₀ = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (R := D₀) (p := p)
  have hinj : Function.Injective (QuotientGroup.mk' (frattini D₀)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hΦ]
  set ι : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃* D₀ ⧸ frattini D₀ :=
    QuotientGroup.congr _ _ φ0 (map_frattini_mulEquiv φ0) with hι
  set U0 : Subgroup (D₀ ⧸ frattini D₀) := (Z.subgroupOf D₀).map (QuotientGroup.mk' _) with hU0
  set U := U0.map ι.symm.toMonoidHom with hU
  have hmemU : ∀ x : X, (((x : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸
      frattini (X ⧸ CFSG.pCore 2 X)) ∈ U ↔ QuotientGroup.mk' (CFSG.pCore 2 K) (x : K) ∈ Z := by
    intro x
    rw [hU, mem_map_equiv, MulEquiv.symm_symm, hι, QuotientGroup.congr_mk, hU0]
    have e1 : φ0 (x : X ⧸ CFSG.pCore 2 X) =
        ⟨QuotientGroup.mk' (CFSG.pCore 2 K) (x : K), x, x.2, rfl⟩ := Subtype.ext (hφ0 x)
    rw [e1]
    change QuotientGroup.mk' (frattini D₀) _ ∈ _ ↔ _
    rw [mem_map_iff_mem hinj, mem_subgroupOf]
  have hUcard : Nat.card U = p := by
    rw [hU, card_map_of_injective (f := ι.symm.toMonoidHom) ι.symm.injective, hU0,
      card_map_of_injective hinj,
      Nat.card_congr (subgroupOfEquivOfLe hZX).toEquiv, hZ]
  have hinv : ∀ y : Y, ∀ u ∈ U, normalizerResidualAction X (inclusion hYX y) u ∈ U := by
    intro y u hu
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u'
    rw [normalizerResidualAction_mk, hmemU]
    rw [hmemU] at hu
    have h1 : ((X.normalizerMonoidHom (inclusion hYX y) x : X) : K) =
        (y : K) * x * (y : K)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact (inferInstance : Z.Normal).conj_mem _ hu _
  rcases hirr U hinv with h | h
  · rw [h, card_bot] at hUcard
    exact hp.out.one_lt.ne hUcard
  · rw [h, card_top, hW] at hUcard
    have h2 : p < p ^ 2 := by
      have := hp.out.one_lt
      nlinarith
    exact h2.ne' hUcard

theorem normalized_witness_map_eq {K : Type*} [Group K] [Finite K]
    (hSQT : CFSG.IsStronglyQuasithin K) (hLC : CFSG.IsCComponent (⊤ : Subgroup K))
    (hq : ¬ CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) {Y X : Subgroup K}
    (hYX : Y ≤ normalizer (X : Set K)) {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ y : Y, ∀ u ∈ U, normalizerResidualAction X (inclusion hYX y) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hNX : (CFSG.pCore 2 K).subgroupOf X = CFSG.pCore 2 X)
    (hXF : X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
      CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K)) :
    p ∈ (Nat.card (CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K))).primeFactors ∧
      CFSG.pCore p (K ⧸ CFSG.pCore 2 K) ≠ ⊥ ∧
      X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) =
        closure {a | a ∈ CFSG.pCore p (K ⧸ CFSG.pCore 2 K) ∧ a ^ p = 1} := by
  classical
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  obtain ⟨φ0, -⟩ := exists_two_core_quotient_equiv_map hNX
  set D₀ := X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) with hD₀
  set Q := CFSG.pCore p (K ⧸ CFSG.pCore 2 K) with hQ
  set D := closure {a | a ∈ Q ∧ a ^ p = 1} with hD
  have hD0p : IsPGroup p D₀ := hP.of_equiv φ0
  have hD0exp : ∀ d ∈ D₀, d ^ p = 1 := by
    intro d hd
    have h1 : ∀ y : X ⧸ CFSG.pCore 2 X, y ^ p = 1 := fun y => by
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one y
    have h2 := congrArg φ0 (h1 (φ0.symm ⟨d, hd⟩))
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
    exact congrArg Subtype.val h2
  have hD0card : p ^ 2 ≤ Nat.card D₀ := by
    have hrank' : CFSG.Open.pRank p (⊤ : Subgroup D₀) = 2 := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt φ0,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hrank
    obtain ⟨E0, -, -, hE0card⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (⊤ : Subgroup D₀)
    rw [hrank'] at hE0card
    rw [← hE0card]
    exact card_le_card_group E0
  have hD0ne : D₀ ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hD0card
    have := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  have hD0Q : D₀ ≤ Q := by
    obtain ⟨S, hS⟩ := (hD0p.of_equiv (subgroupOfEquivOfLe hXF).symm :
      IsPGroup p (D₀.subgroupOf (CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K)))).exists_le_sylow
    intro d hd
    rw [hQ, ← sylow_fitting_map_eq_pCore S]
    exact ⟨⟨d, hXF hd⟩, hS (mem_subgroupOf.mpr hd), rfl⟩
  have hQne : Q ≠ ⊥ := fun h => hD0ne (le_bot_iff.mp (h ▸ hD0Q))
  have hpF : p ∈ (Nat.card (CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K))).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hp.out, ?_, Nat.card_pos.ne'⟩
    have h1 : Nat.card Q ∣ Nat.card (CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K)) :=
      card_dvd_of_le (CFSG.pCore_le_fitting _ p)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup p Q).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hk
      exact hQne hk
    rw [hk] at h1
    exact (dvd_pow_self p hk0).trans h1
  have hD0D : D₀ ≤ D := fun d hd => subset_closure ⟨hD0Q hd, hD0exp d hd⟩
  refine ⟨hpF, hQne, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hshape⟩ := whole_Frattini_assembly_self hSQT' hO2' hLC' hq p hpF
  rcases hshape with ⟨hnc, hQ3, hQexp⟩ | ⟨hQab, a, ha, ⟨eQ⟩⟩
  ·
    have hDQ : D = Q := by
      apply le_antisymm
      · rw [hD, closure_le]
        exact fun a ha => ha.1
      · intro x hx
        refine subset_closure ⟨hx, ?_⟩
        have h1 := congrArg Subtype.val (hQexp ⟨x, hx⟩)
        simpa using h1
    rw [hDQ]
    by_contra hne'
    have hdvd : Nat.card D₀ ∣ p ^ 3 := hQ3 ▸ card_dvd_of_le hD0Q
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hj2 : j = 2 := by
      have h1 : p ^ 2 ≤ p ^ j := hjc ▸ hD0card
      have h2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp h1
      have h3 : j ≠ 3 := by
        rintro rfl
        exact hne' (eq_of_le_of_card_ge hD0Q (by rw [hQ3, hjc]))
      omega
    subst hj2
    have hnc' : ∃ a b : Q, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hnc ⟨⟨h⟩⟩
    obtain ⟨-, hZp, -, -, -, hT, -⟩ := nonabelian_prime_cube_central_structure hQ3 hnc'
    have hTcard : Nat.card (D₀.subgroupOf Q) = p ^ 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hD0Q).toEquiv, hjc]
    obtain ⟨hZT, -, -, -⟩ := hT _ hTcard
    have hZD0 : (center Q).map Q.subtype ≤ D₀ := by
      rintro _ ⟨z, hz, rfl⟩
      exact mem_subgroupOf.mp (hZT hz)
    have hZcard : Nat.card ((center Q).map Q.subtype) = p := by
      rw [card_map_of_injective Q.subtype_injective, hZp]
    exact not_le_of_normal_line hYX hW hirr hNX hjc hD0exp hZD0 hZcard
  ·
    let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hQab.is_comm.comm }
    have hker := homocyclic_card_ker_pow_le eQ p hp.out.pos
    have hDle : D ≤ ((powMonoidHom p : Q →* Q).ker).map Q.subtype := by
      rw [hD, closure_le]
      rintro x ⟨hxQ, hxp⟩
      refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply]
      exact Subtype.ext hxp
    have hDcard : Nat.card D ≤ p ^ 2 := by
      refine (card_le_of_le hDle).trans ?_
      rw [card_map_of_injective Q.subtype_injective]
      exact hker
    exact eq_of_le_of_card_ge hD0D (hDcard.trans hD0card)

theorem eq_closure_odd_of_normalized {K : Type*} [Group K] [Finite K] {X : Subgroup K}
    (hNX : CFSG.pCore 2 K ≤ normalizer (X : Set K))
    (hX2 : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X) {E : Subgroup K}
    (hE : E = CFSG.pCore 2 K ⊔ X) : X = closure {e | e ∈ E ∧ Odd (orderOf e)} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXE : X ≤ E := hE ▸ le_sup_right
  have hEX : E ≤ normalizer (X : Set K) := hE ▸ sup_le hNX le_normalizer
  have hXn : (X.subgroupOf E).Normal := (normal_subgroupOf_iff_le_normalizer hXE).mpr hEX
  have hodd : ∀ e ∈ E, Odd (orderOf e) → e ∈ X := by
    intro e he heo
    have he' : e ∈ ((CFSG.pCore 2 K ⊔ X : Subgroup K) : Set K) := by
      rw [← hE]
      exact he
    rw [normal_mul, Set.mem_mul] at he'
    obtain ⟨n, hn, x, hx, hnx⟩ := he'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨n, hn⟩
    have hk' : n ^ 2 ^ k = 1 := by
      have h1 := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_pow] at h1
    have hnE : n ∈ E := hE ▸ mem_sup_left hn
    have h1 : ((⟨e, he⟩ : E) : E ⧸ X.subgroupOf E) ^ 2 ^ k = 1 := by
      have e1 : (⟨e, he⟩ : E) = ⟨n, hnE⟩ * ⟨x, hXE hx⟩ := Subtype.ext hnx.symm
      rw [e1, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (⟨x, hXE hx⟩ : E)).mpr (mem_subgroupOf.mpr hx), mul_one,
        ← QuotientGroup.mk_pow]
      have e2 : (⟨n, hnE⟩ : E) ^ 2 ^ k = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hk')
      rw [e2, QuotientGroup.mk_one]
    have h2 : orderOf ((⟨e, he⟩ : E) : E ⧸ X.subgroupOf E) ∣ orderOf e := by
      have := orderOf_map_dvd (QuotientGroup.mk' (X.subgroupOf E)) (⟨e, he⟩ : E)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (orderOf e) (2 ^ k) :=
      Nat.Coprime.pow_right k (Odd.coprime_two_right heo)
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop)
      (orderOf_dvd_of_pow_eq_one h1)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, mem_subgroupOf] at h3
    exact h3
  set U := closure {e | e ∈ E ∧ Odd (orderOf e)} with hU
  have hUX : U ≤ X := by
    rw [hU, closure_le]
    exact fun e he => hodd e he.1 he.2
  apply le_antisymm _ hUX
  have hUconj : ∀ g ∈ E, ∀ z ∈ U, g * z * g⁻¹ ∈ U := by
    intro g hgE z hz
    induction hz using closure_induction with
    | mem z hz =>
      refine subset_closure ⟨?_, ?_⟩
      · exact mul_mem (mul_mem hgE hz.1) (inv_mem hgE)
      · have h1 : orderOf (MulAut.conj g z) = orderOf z :=
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
        rw [MulAut.conj_apply] at h1
        rw [h1]
        exact hz.2
    | one => simp
    | mul a b _ _ iha ihb =>
      have h1 := mul_mem iha ihb
      simpa [mul_assoc] using h1
    | inv a _ iha =>
      have h1 := inv_mem iha
      simpa [mul_assoc] using h1
  have hUn : (U.subgroupOf X).Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    exact hUconj g (hXE g.2) y hy
  have hK2 : IsPGroup 2 (X ⧸ U.subgroupOf X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨(orderOf (x : K)).factorization 2, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, SubgroupClass.coe_pow]
    exact subset_closure ⟨pow_mem (hXE x.2) _, odd_orderOf_pow_two_part (x : K)⟩
  have hK := hX2 (U.subgroupOf X) hK2
  intro x hx
  have h1 : (⟨x, hx⟩ : X) ∈ U.subgroupOf X := by
    rw [hK]
    exact mem_top _
  exact mem_subgroupOf.mp h1

theorem normalized_two_core_forces_original_witness_canonicity_in_nonquasisimple_overgroup
    {K : Type*} [Group K] [Finite K] (hSQT : CFSG.IsStronglyQuasithin K)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup K))
    (hq : ¬ CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) {Y : Subgroup K} (hY : Group.IsPerfect Y)
    {p : ℕ} [hp : Fact p.Prime] (_hp2 : p ≠ 2) {X : Subgroup K} (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set K))
    (hX2 : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (_hnt : ∃ y : Y, ∃ w, normalizerResidualAction X (inclusion hYX y) w ≠ w)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ y : Y, ∀ u ∈ U, normalizerResidualAction X (inclusion hYX y) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hNX : CFSG.pCore 2 K ≤ normalizer (X : Set K))
    (Q D : Subgroup (K ⧸ CFSG.pCore 2 K)) (E : Subgroup K)
    (hQ : Q = CFSG.pCore p (K ⧸ CFSG.pCore 2 K)) (hD : D = closure {a | a ∈ Q ∧ a ^ p = 1})
    (hE : E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 K))) :
    5 ≤ p ∧ X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
        CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K) ∧
      Q ≠ ⊥ ∧ (CFSG.pCore 2 K).subgroupOf X = CFSG.pCore 2 X ∧
      X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) = D ∧ E = CFSG.pCore 2 K ⊔ X ∧
      X = closure {e | e ∈ E ∧ Odd (orderOf e)} ∧ X.Characteristic ∧
      ((IsMulCommutative Q ∧ (∃ a : ℕ, 1 ≤ a ∧
          Nonempty (Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))) ∧
          IsElementaryAbelian p D ∧ Nat.card D = p ^ 2) ∨
        (Q = D ∧ ¬ IsMulCommutative Q ∧ Nat.card Q = p ^ 3 ∧ ∀ x ∈ Q, x ^ p = 1)) ∧
      ∃ (_ : D.Normal) (φ : X ⧸ CFSG.pCore 2 X ≃* D)
        (θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃* D ⧸ frattini D),
        (∀ x : X, (φ (x : X ⧸ CFSG.pCore 2 X) : K ⧸ CFSG.pCore 2 K) =
          QuotientGroup.mk' (CFSG.pCore 2 K) (x : K)) ∧
        (∀ y ∈ Y, ∀ x x' : X, (x' : K) = y * x * y⁻¹ →
          (φ (x' : X ⧸ CFSG.pCore 2 X) : K ⧸ CFSG.pCore 2 K) =
            QuotientGroup.mk' (CFSG.pCore 2 K) y *
              (φ (x : X ⧸ CFSG.pCore 2 X) : K ⧸ CFSG.pCore 2 K) *
              (QuotientGroup.mk' (CFSG.pCore 2 K) y)⁻¹) ∧
        (∀ v : X ⧸ CFSG.pCore 2 X,
          θ (v : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =
            ((φ v : D) : D ⧸ frattini D)) ∧
        ∀ (y : Y) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
          θ (normalizerResidualAction X (inclusion hYX y) w) =
            wholeFrattiniAction D (QuotientGroup.mk' (CFSG.pCore 2 K) y) (θ w) := by
  classical
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  obtain ⟨-, -, hodd, -, -, -⟩ := odd_Fitting_cores_self hSQT' hO2' hLC' hq
  have hXs : Group.IsSolvable X := isSolvable_of_isPGroup_quotient_pCore hP
  have hXF : X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
      CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K) := by
    refine le_fitting_of_perfect_normalizer hSQT' hO2' hLC' hq (V := Y.map (QuotientGroup.mk' _))
      (Group.IsPerfect.map (QuotientGroup.mk' (CFSG.pCore 2 K)) (H := Y)) (map_mono hXY) ?_
      (Group.isSolvable_of_surjective
        (f := (QuotientGroup.mk' (CFSG.pCore 2 K)).subgroupMap X)
        ((QuotientGroup.mk' (CFSG.pCore 2 K)).subgroupMap_surjective X))
      (CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective
        ((QuotientGroup.mk' (CFSG.pCore 2 K)).subgroupMap X)
        ((QuotientGroup.mk' (CFSG.pCore 2 K)).subgroupMap_surjective X) hX2)
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp (hYX hy) x).mp hx, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨x, hx, hxz⟩
      have h1 : y⁻¹ * x * y ∈ X := by
        have h2 := (mem_normalizer_iff.mp (hYX (inv_mem hy)) x).mp hx
        rwa [inv_inv] at h2
      refine ⟨y⁻¹ * x * y, h1, ?_⟩
      rw [map_mul, map_mul, map_inv, hxz]
      group
  have hNXX := two_core_subgroupOf_eq_of_le_fitting hXF hodd
  obtain ⟨hpF, hQne, hXD⟩ :=
    normalized_witness_map_eq hSQT hLC hq hYX hP hexp hrank hW hirr hNXX hXF
  subst hQ
  have hXD' : X.map (QuotientGroup.mk' (CFSG.pCore 2 K)) = D := hXD.trans hD.symm
  have hEX : E = CFSG.pCore 2 K ⊔ X := by
    rw [hE, ← hXD', comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  have hXcl := eq_closure_odd_of_normalized hNX hX2 hEX
  have hcw := canonical_prime_witness hSQT hLC hq hpF (CFSG.pCore p (K ⧸ CFSG.pCore 2 K)) D E X
    rfl hD hE hXcl
  obtain ⟨hp5, hXc, -, -, -, -, ⟨hDn, φ, θ, hφ, hφeq, hθφ, hθ⟩, hshape, -⟩ := hcw
  refine ⟨hp5, hXF, hQne, hNXX, hXD', hEX, hXcl, hXc, hshape, hDn, φ, θ, hφ,
    fun y _ x x' hx' => hφeq y x x' hx', hθφ, fun y w => ?_⟩
  rw [normalizerResidualAction_eq]
  exact hθ y w

end CFSG.Quasithin.H13.NQBlock
