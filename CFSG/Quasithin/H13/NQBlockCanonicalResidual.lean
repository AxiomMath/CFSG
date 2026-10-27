module

public import CFSG.Quasithin.H13.NQBlockOddResidual

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm

structure IsOddResidualWitness {L : Type*} [Group L] [Finite L] (p : ℕ) (X : Subgroup L) :
    Prop where
  characteristic : X.Characteristic
  le_rad : X ≤ CFSG.solvableRadical L
  noTwoQuotient : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X
  isPGroup : IsPGroup p (X ⧸ CFSG.pCore 2 X)
  exponent : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p
  pRank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2
  card_W : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2
  nontrivial : @residualAction L _ X characteristic ≠ 1
  irreducible : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
    Nat.card U = p → ∃ l : L, ∃ u ∈ U, @residualAction L _ X characteristic l u ∉ U


theorem witness_image {L : Type*} [Group L] [Finite L] {p : ℕ} [hp : Fact p.Prime]
    {X : Subgroup L} (hX : IsOddResidualWitness p X) :
    ∃ _ : (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal,
      (∀ d ∈ X.map (QuotientGroup.mk' (CFSG.pCore 2 L)), d ^ p = 1) ∧
      X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) ≠ ⊥ ∧
      p ^ 2 ≤ Nat.card (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))) ∧
      X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) ≤ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧
      ∀ U : Subgroup (X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) ⧸
          frattini (X.map (QuotientGroup.mk' (CFSG.pCore 2 L)))),
        Nat.card U = p → ∃ l : L, ∃ u ∈ U,
          wholeFrattiniAction (X.map (QuotientGroup.mk' (CFSG.pCore 2 L)))
            (QuotientGroup.mk' (CFSG.pCore 2 L) l) u ∉ U := by
  classical
  have := hX.characteristic
  obtain ⟨hn, φ, θ, hφmk, hθeq⟩ := residual_equiv X
  have hD0p : IsPGroup p (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))) := hX.isPGroup.of_equiv φ
  refine ⟨hn, ?_, ?_, ?_, le_sSup ⟨hn, hD0p⟩, ?_⟩
  · intro d hd
    have h1 : ∀ y : X ⧸ CFSG.pCore 2 X, y ^ p = 1 := fun y => by
      rw [← hX.exponent]
      exact Monoid.pow_exponent_eq_one y
    have h2 := congrArg φ (h1 (φ.symm ⟨d, hd⟩))
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
    exact congrArg Subtype.val h2
  · intro h
    have hW := hX.card_W
    rw [Nat.card_congr θ.toEquiv] at hW
    have h1 := Subgroup.card_quotient_dvd_card
      (frattini (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))))
    have h2 : Nat.card (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))) = 1 := by
      rw [h, card_bot]
    rw [hW, h2, Nat.dvd_one] at h1
    have := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  · have hrank :
        CFSG.Open.pRank p (⊤ : Subgroup (X.map (QuotientGroup.mk' (CFSG.pCore 2 L)))) = 2 := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt φ,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hX.pRank
    obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt
      (⊤ : Subgroup (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))))
    rw [hrank] at hEcard
    rw [← hEcard]
    exact card_le_card_group E
  · intro U hU
    by_contra hcon
    push Not at hcon
    obtain ⟨l, u, hu, hlu⟩ := hX.irreducible (U.map θ.symm.toMonoidHom)
      (by rw [card_map_of_injective (f := θ.symm.toMonoidHom) θ.symm.injective, hU])
    obtain ⟨v, hv, rfl⟩ := hu
    apply hlu
    refine ⟨wholeFrattiniAction (X.map (QuotientGroup.mk' (CFSG.pCore 2 L)))
      (QuotientGroup.mk' (CFSG.pCore 2 L) l) v, hcon l v hv, ?_⟩
    apply θ.injective
    change θ (θ.symm _) = θ (residualAction X l (θ.symm v))
    rw [MulEquiv.apply_symm_apply, hθeq, MulEquiv.apply_symm_apply]

theorem witness_map_eq
    {L : Type*} [Group L] [Finite L] (hSQT : CFSG.IsStronglyQuasithin L)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    {p : ℕ} [hp : Fact p.Prime] {X : Subgroup L} (hX : IsOddResidualWitness p X) :
    X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) =
      closure {a | a ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ∧ a ^ p = 1} := by
  classical
  obtain ⟨hn, hexp, hne, hcard, hle, hirr⟩ := witness_image hX
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  set M := L ⧸ CFSG.pCore 2 L with hM
  set Q := CFSG.pCore p M with hQ
  set D₀ := X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) with hD₀
  set D := closure {a | a ∈ Q ∧ a ^ p = 1} with hD
  have hQne : Q ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hle))
  have hpF : p ∈ (Nat.card (CFSG.fittingSubgroup M)).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hp.out, ?_, Nat.card_pos.ne'⟩
    have h1 : Nat.card Q ∣ Nat.card (CFSG.fittingSubgroup M) :=
      card_dvd_of_le (CFSG.pCore_le_fitting M p)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup p Q).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, card_eq_one] at hk
      exact hQne hk
    rw [hk] at h1
    exact (dvd_pow_self p hk0).trans h1
  have hD0D : D₀ ≤ D := fun d hd => subset_closure ⟨hle hd, hexp d hd⟩
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
    have hdvd : Nat.card D₀ ∣ p ^ 3 := hQ3 ▸ card_dvd_of_le hle
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hj2 : j = 2 := by
      have h1 : p ^ 2 ≤ p ^ j := hjc ▸ hcard
      have h2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp h1
      have h3 : j ≠ 3 := by
        rintro rfl
        exact hne' (eq_of_le_of_card_ge hle (by rw [hQ3, hjc]))
      omega
    subst hj2
    have hnc' : ∃ a b : Q, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact hnc ⟨⟨h⟩⟩
    obtain ⟨-, hZp, -, -, -, hT, -⟩ := nonabelian_prime_cube_central_structure hQ3 hnc'
    have hTcard : Nat.card (D₀.subgroupOf Q) = p ^ 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hjc]
    obtain ⟨hZT, -, -, -⟩ := hT _ hTcard
    set Z := (center Q).map Q.subtype with hZ
    have hZD0 : Z ≤ D₀ := by
      rintro _ ⟨z, hz, rfl⟩
      exact mem_subgroupOf.mp (hZT hz)
    have hZcard : Nat.card Z = p := by
      rw [hZ, card_map_of_injective Q.subtype_injective, hZp]
    have hZn : Z.Normal := inferInstance
    have hD0el : IsElementaryAbelian p D₀ :=
      { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hjc
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by
            rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
            exact hexp _ x.2) }
    have : Fact (IsPGroup p D₀) := ⟨IsPGroup.of_card hjc⟩
    have hΦ : frattini D₀ = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (R := D₀) (p := p)
    set U0 : Subgroup (D₀ ⧸ frattini D₀) :=
      (Z.subgroupOf D₀).map (QuotientGroup.mk' (frattini D₀)) with hU0def
    have hinj : Function.Injective (QuotientGroup.mk' (frattini D₀)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hΦ]
    have hU0 : Nat.card U0 = p := by
      rw [hU0def, card_map_of_injective hinj, Nat.card_congr (subgroupOfEquivOfLe hZD0).toEquiv,
        hZcard]
    obtain ⟨l, u, hu, hlu⟩ := hirr U0 hU0
    obtain ⟨v, hv, rfl⟩ := hu
    apply hlu
    refine ⟨MulAut.conjNormal (QuotientGroup.mk' (CFSG.pCore 2 L) l) v, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply]
    exact hZn.conj_mem _ (mem_subgroupOf.mp hv) _
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
    exact eq_of_le_of_card_ge hD0D (hDcard.trans hcard)

theorem odd_orderOf_pow_two_part {G : Type*} [Group G] [Finite G] (x : G) :
    Odd (orderOf (x ^ 2 ^ (orderOf x).factorization 2)) := by
  have hpos : 0 < orderOf x := orderOf_pos x
  have h1 : orderOf (x ^ 2 ^ (orderOf x).factorization 2) =
      orderOf x / 2 ^ (orderOf x).factorization 2 :=
    orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (Nat.ordProj_dvd _ _)
  rw [h1]
  have h3 := Nat.coprime_ordCompl Nat.prime_two hpos.ne'
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ((Nat.Prime.coprime_iff_not_dvd
    Nat.prime_two).mp h3))

theorem witness_eq_closure {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {X : Subgroup L} (hX : IsOddResidualWitness p X) :
    X = closure {e | e ∈ (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 L)) ∧ Odd (orderOf e)} := by
  classical
  have := hX.characteristic
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 L with hN
  set π := QuotientGroup.mk' N with hπ
  set E := (X.map π).comap π with hE
  have hEXN : E = X ⊔ N := by rw [hE, comap_map_eq, hπ, QuotientGroup.ker_mk']
  have hXE : X ≤ E := le_comap_map _ _
  set Y := closure {e | e ∈ E ∧ Odd (orderOf e)} with hY
  have hodd : ∀ e ∈ E, Odd (orderOf e) → e ∈ X := by
    intro e he heo
    have he' : e ∈ ((X ⊔ N : Subgroup L) : Set L) := by
      rw [← hEXN]
      exact he
    rw [mul_normal, Set.mem_mul] at he'
    obtain ⟨x, hx, n, hn, rfl⟩ := he'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 N) ⟨n, hn⟩
    have hk' : n ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : ((x * n : L) : L ⧸ X) ^ 2 ^ k = 1 := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).mpr hx, one_mul,
        ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    have h2 : orderOf ((x * n : L) : L ⧸ X) ∣ orderOf (x * n) :=
      orderOf_map_dvd (QuotientGroup.mk' X) _
    have hcop : Nat.Coprime (orderOf (x * n)) (2 ^ k) :=
      Nat.Coprime.pow_right k (Odd.coprime_two_right heo)
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop)
      (orderOf_dvd_of_pow_eq_one h1)
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  apply le_antisymm
  ·
    have hEn : E.Normal := by
      rw [hEXN]
      infer_instance
    have hYn : Y.Normal := by
      refine ⟨fun y hy g => ?_⟩
      induction hy using closure_induction with
      | mem x hx =>
        refine subset_closure ⟨hEn.conj_mem x hx.1 g, ?_⟩
        have h1 : orderOf (MulAut.conj g x) = orderOf x :=
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        rw [MulAut.conj_apply] at h1
        rw [h1]
        exact hx.2
      | one => simp
      | mul a b _ _ iha ihb =>
        have h1 := mul_mem iha ihb
        simpa [mul_assoc] using h1
      | inv a _ iha =>
        have h1 := inv_mem iha
        simpa [mul_assoc] using h1
    have hK2 : IsPGroup 2 (X ⧸ Y.subgroupOf X) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨(orderOf (x : L)).factorization 2, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, SubgroupClass.coe_pow]
      exact subset_closure ⟨pow_mem (hXE x.2) _, odd_orderOf_pow_two_part (x : L)⟩
    have hK := hX.noTwoQuotient (Y.subgroupOf X) hK2
    intro x hx
    have h1 : (⟨x, hx⟩ : X) ∈ Y.subgroupOf X := by
      rw [hK]
      exact mem_top _
    exact mem_subgroupOf.mp h1
  · rw [hY, closure_le]
    exact fun e he => hodd e he.1 he.2

theorem original_characteristic_radical_witness_is_canonical_prime_residual
    {L : Type*}
    [Group L] [Finite L] (hSQT : CFSG.IsStronglyQuasithin L)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hq : ¬ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) {p : ℕ} [Fact p.Prime] (_hp5 : 5 ≤ p)
    {X : Subgroup L} (hX : IsOddResidualWitness p X) (Q D : Subgroup (L ⧸ CFSG.pCore 2 L))
    (E : Subgroup L) (hQ : Q = CFSG.pCore p (L ⧸ CFSG.pCore 2 L))
    (hD : D = closure {a | a ∈ Q ∧ a ^ p = 1})
    (hE : E = D.comap (QuotientGroup.mk' (CFSG.pCore 2 L))) :
    Q ≠ ⊥ ∧ X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) = D ∧
      ((QuotientGroup.mk' (CFSG.pCore 2 L)).comp X.subtype).ker = CFSG.pCore 2 X ∧
      E = CFSG.pCore 2 L ⊔ X ∧ X = closure {e | e ∈ E ∧ Odd (orderOf e)} ∧
      (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Characteristic ∧
      ((IsMulCommutative Q ∧ (∃ a : ℕ, 1 ≤ a ∧
          Nonempty (Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))) ∧
          IsElementaryAbelian p D ∧ Nat.card D = p ^ 2) ∨
        (Q = D ∧ ¬ IsMulCommutative Q ∧ Nat.card Q = p ^ 3 ∧ ∀ x ∈ Q, x ^ p = 1)) ∧
      (∃ (_ : D.Normal) (φ : X ⧸ CFSG.pCore 2 X ≃* D)
          (θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃* D ⧸ frattini D),
        (∀ x : X, (φ (x : X ⧸ CFSG.pCore 2 X) : L ⧸ CFSG.pCore 2 L) =
          QuotientGroup.mk' (CFSG.pCore 2 L) (x : L)) ∧
        (∀ (l : L) (x y : X), (y : L) = l * x * l⁻¹ →
          (φ (y : X ⧸ CFSG.pCore 2 X) : L ⧸ CFSG.pCore 2 L) =
            QuotientGroup.mk' (CFSG.pCore 2 L) l *
              (φ (x : X ⧸ CFSG.pCore 2 X) : L ⧸ CFSG.pCore 2 L) *
              (QuotientGroup.mk' (CFSG.pCore 2 L) l)⁻¹) ∧
        ∀ (l : L) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
          θ (@residualAction L _ X hX.characteristic l w) =
            wholeFrattiniAction D (QuotientGroup.mk' (CFSG.pCore 2 L) l) (θ w)) ∧
      ∀ X' : Subgroup L, IsOddResidualWitness p X' → X' = X := by
  classical
  have := hX.characteristic
  have hmap := witness_map_eq hSQT hLC hq hX
  have hcl := witness_eq_closure hX
  obtain ⟨hSQT', hO2', hLC'⟩ := quotient_two_core_setup hSQT hLC
  obtain ⟨-, -, hne, -, hle, -⟩ := witness_image hX
  subst hQ
  have hXD : X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) = D := hmap.trans hD.symm
  subst hXD
  subst hE
  have hQne : CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hle))
  have hDchar : (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Characteristic := by
    rw [hmap, characteristic_iff_le_comap]
    intro σ
    rw [closure_le]
    rintro a ⟨haQ, hap⟩
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom]
    refine subset_closure ⟨(characteristic_iff_le_comap.mp inferInstance σ) haQ, ?_⟩
    rw [← map_pow, hap, map_one]
  have hpF : p ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Nat.card_pos.ne'⟩
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
  obtain ⟨-, -, -, -, -, -, -, hshape⟩ := whole_Frattini_assembly_self hSQT' hO2' hLC' hq p hpF
  have hshape' : (IsMulCommutative (CFSG.pCore p (L ⧸ CFSG.pCore 2 L)) ∧ (∃ a : ℕ, 1 ≤ a ∧
        Nonempty (CFSG.pCore p (L ⧸ CFSG.pCore 2 L) ≃*
          Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))) ∧
        IsElementaryAbelian p (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))) ∧
        Nat.card (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))) = p ^ 2) ∨
      (CFSG.pCore p (L ⧸ CFSG.pCore 2 L) = X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) ∧
        ¬ IsMulCommutative (CFSG.pCore p (L ⧸ CFSG.pCore 2 L)) ∧
        Nat.card (CFSG.pCore p (L ⧸ CFSG.pCore 2 L)) = p ^ 3 ∧
        ∀ x ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L), x ^ p = 1) := by
    obtain ⟨-, hexp, -, hcard, -, -⟩ := witness_image hX
    rcases hshape with ⟨hnc, hQ3, hQexp⟩ | ⟨hQab, a, ha, ⟨eQ⟩⟩
    · right
      have hQexp' : ∀ x ∈ CFSG.pCore p (L ⧸ CFSG.pCore 2 L), x ^ p = 1 := fun x hx => by
        have h1 := congrArg Subtype.val (hQexp ⟨x, hx⟩)
        simpa using h1
      refine ⟨le_antisymm ?_ hle, hnc, hQ3, hQexp'⟩
      intro x hx
      rw [hmap]
      exact subset_closure ⟨hx, hQexp' x hx⟩
    · left
      have hcomm : IsMulCommutative (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))) :=
        ⟨⟨fun x y => Subtype.ext (by
          have h := hQab.is_comm.comm (⟨x, hle x.2⟩ : CFSG.pCore p (L ⧸ CFSG.pCore 2 L))
            ⟨y, hle y.2⟩
          have h' := congrArg Subtype.val h
          exact h')⟩⟩
      have hel : IsElementaryAbelian p (X.map (QuotientGroup.mk' (CFSG.pCore 2 L))) :=
        { toIsMulCommutative := hcomm
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (by
              rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
              exact hexp _ x.2) }
      refine ⟨hQab, ⟨a, ha, ⟨eQ⟩⟩, hel, ?_⟩
      ·
        let _ : CommGroup (CFSG.pCore p (L ⧸ CFSG.pCore 2 L)) :=
          { (inferInstance : Group (CFSG.pCore p (L ⧸ CFSG.pCore 2 L))) with
            mul_comm := hQab.is_comm.comm }
        have hker := homocyclic_card_ker_pow_le eQ p (Fact.out : p.Prime).pos
        have hDle : X.map (QuotientGroup.mk' (CFSG.pCore 2 L)) ≤
            ((powMonoidHom p : CFSG.pCore p (L ⧸ CFSG.pCore 2 L) →*
              CFSG.pCore p (L ⧸ CFSG.pCore 2 L)).ker).map
                (CFSG.pCore p (L ⧸ CFSG.pCore 2 L)).subtype := by
          intro d hd
          refine ⟨⟨d, hle hd⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply]
          exact Subtype.ext (hexp d hd)
        refine le_antisymm ((card_le_of_le hDle).trans ?_) hcard
        rw [card_map_of_injective (Subgroup.subtype_injective _)]
        exact hker
  obtain ⟨hn, φ, θ, hφmk, hθeq⟩ := residual_equiv X
  refine ⟨hQne, rfl, ker_mk_comp_subtype_eq_pCore X, ?_, hcl, hDchar, hshape', ⟨hn, φ, θ, hφmk,
    fun l x => ?_, hθeq⟩, fun X' hX' => ?_⟩
  · rw [comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  · intro y hy
    rw [hφmk, hφmk, hy, map_mul, map_mul, map_inv]
  ·
    have h1 := witness_map_eq hSQT hLC hq hX'
    have h2 := witness_eq_closure hX'
    rw [h2, h1, ← hmap]
    exact hcl.symm

end CFSG.Quasithin.H13.NQBlock
