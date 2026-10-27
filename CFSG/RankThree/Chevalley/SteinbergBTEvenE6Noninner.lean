module

public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6CanonicalField
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem exists_conj_eq_entrywiseAdjointAut_of_ambient (τ : Tag) {ℓ f e p : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hp : 1 ≤ p) (hep : e * p = f) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (x : ModGL τ L) (hx : x ∈ adjointGroup τ L) (β : MulAut (adjointGroup τ K))
    (hβ : ∀ u : adjointGroup τ K, baseChangeGL (algebraMap K L) (β u : ModGL τ K) =
      x * baseChangeGL (algebraMap K L) (entrywiseAdjointAut τ T u : ModGL τ K) * x⁻¹)
    (hβp : β ^ p = 1) :
    ∃ ψ : MulAut (adjointGroup τ K), ψ * β * ψ⁻¹ = entrywiseAdjointAut τ T := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hTp : T ^ p = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_apply, RingAut.one_apply]
    have hit : ∀ n : ℕ, (⇑T)^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hT, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L e he).1 τ
  have hS1 : ∀ g, ((S.toMonoidHom g : adjointGroup τ L) : ModGL τ L) =
      Units.map (entrywiseHom (iterateFrobenius L ℓ e)) g := hS
  let ι : adjointGroup τ K →* adjointGroup τ L :=
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).codRestrict
      (adjointGroup τ L) fun u => baseChangeGL_mem_adjointGroup (algebraMap K L) u.2
  have hι : ∀ u, (ι u : ModGL τ L) = baseChangeGL (algebraMap K L) u := fun _ => rfl
  have hFrc : (iterateFrobenius L ℓ e).comp (algebraMap K L) =
      (algebraMap K L).comp T.toRingHom := by
    ext c
    simp [iterateFrobenius_def, hT, map_pow]
  have hFι : ∀ w : ModGL τ K, Units.map (entrywiseHom (iterateFrobenius L ℓ e))
      (baseChangeGL (algebraMap K L) w) =
        baseChangeGL (algebraMap K L) (Units.map (entrywiseHom T.toRingHom) w) := fun w => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hSι : ∀ u, S (ι u) = ι (entrywiseAdjointAut τ T u) := fun u => Subtype.ext (by
    rw [hS, hι, hι, coe_entrywiseAdjointAut, hFι])
  have hSpow : ∀ (n : ℕ) (u : adjointGroup τ K),
      (S ^ n) (ι u) = ι ((entrywiseAdjointAut τ T ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ih, hSι, pow_succ', MulAut.mul_apply]
  let x' : adjointGroup τ L := ⟨x, hx⟩
  have hx'v : (x' : ModGL τ L) = x := rfl
  have hext : ∀ u, (MulAut.conj x' * S) (ι u) = ι (β u) := fun u => Subtype.ext (by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hSι, hι, hι, hβ, hx'v])
  have hextpow : ∀ (n : ℕ) (u : adjointGroup τ K),
      ((MulAut.conj x' * S) ^ n) (ι u) = ι ((β ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ih, hext, pow_succ', MulAut.mul_apply]
  set N := ((List.range p).map fun i => (S ^ i) x').prod with hN
  have hNc : ∀ u, N * ι u * N⁻¹ = ι u := by
    intro u
    have h1 := hextpow p u
    rw [hβp, MulAut.one_apply, conj_mul_pow, MulAut.mul_apply, MulAut.conj_apply, hSpow,
      ← entrywiseAdjointAut_pow, hTp, entrywiseAdjointAut_one, MulAut.one_apply] at h1
    exact h1
  have hN1 : N = 1 := by
    obtain ⟨-, -, hfaith, -⟩ :=
      Chevalley_large_finite_root_centralizer_faithfulness_of_four_le τ K hK4 L (algebraMap K L)
    refine Subtype.ext (hfaith _ N.2 fun w hw => ?_)
    obtain ⟨u, hu, rfl⟩ := hw
    have h1 : (N : ModGL τ L) * baseChangeGL (algebraMap K L) u * (N : ModGL τ L)⁻¹ =
        baseChangeGL (algebraMap K L) u := congrArg Subtype.val (hNc ⟨u, hu⟩)
    calc (N : ModGL τ L) * baseChangeGL (algebraMap K L) u =
        (N : ModGL τ L) * baseChangeGL (algebraMap K L) u * (N : ModGL τ L)⁻¹ * N := by group
      _ = baseChangeGL (algebraMap K L) u * N := by rw [h1]
  have hiter : ∀ (i : ℕ) (y : adjointGroup τ L), (⇑S.toMonoidHom)^[i] y = (S ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
      rfl
  have hnorm : ((List.range p).map fun i => (⇑S.toMonoidHom)^[i] x').prod = 1 :=
    (congrArg List.prod (List.map_congr_left fun i _ => hiter i x')).trans hN1
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom hp hLang x' hnorm
  have hFrK : ∀ c : L, ((iterateFrobenius L ℓ e) ^ p) c = c ^ Nat.card K := by
    intro c
    rw [RingHom.coe_pow]
    have hit : ∀ n : ℕ, (⇑(iterateFrobenius L ℓ e))^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep, hK]
  have hiterS : ∀ (n : ℕ) (g : adjointGroup τ L), (((⇑S.toMonoidHom)^[n] g : adjointGroup τ L) :
      ModGL τ L) = Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ n)) g := by
    intro n
    induction n with
    | zero =>
      intro g
      refine Units.ext ?_
      rw [Function.iterate_zero, id_eq, Units.coe_map, pow_zero, RingHom.one_def]
      exact (entrywise_id (R := L) _).symm
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply', hS1, ih]
      refine Units.ext ?_
      rw [Units.coe_map, Units.coe_map, Units.coe_map, pow_succ', RingHom.mul_def]
      exact entrywise_entrywise (R := L) _ _ _
  have hhfix : (h : ModGL τ L) ∈ adjointGroup τ L ⊓
      (Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ p))).eqLocus (MonoidHom.id _) := by
    refine ⟨h.2, ?_⟩
    change Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ p)) (h : ModGL τ L) = h
    rw [← hiterS p h, mem_iterateFixedSubgroup.1 hR]
  obtain ⟨-, -, hnorml⟩ := Chevalley_Frobenius_fixed_ambient_normalizer τ K L _ hFrK
  have hmap : ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj (h : ModGL τ L)).toMonoidHom =
        (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
    map_conj_eq_of_mem_normalizer (hnorml hhfix)
  let eH : adjointGroup τ K ≃* (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
    Subgroup.equivMapOfInjective (adjointGroup τ K) (baseChangeGL (algebraMap K L))
      (baseChangeGL_injective _)
  have heH : ∀ u, ((eH u : (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) :
      ModGL τ L) = baseChangeGL (algebraMap K L) u := fun u =>
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  let δ : MulAut (adjointGroup τ K) :=
    eH.trans ((mulAutRestrict _ (MulAut.conj (h : ModGL τ L)) hmap).trans eH.symm)
  have hδ : ∀ u, baseChangeGL (algebraMap K L) (δ u : ModGL τ K) =
      (h : ModGL τ L) * baseChangeGL (algebraMap K L) u * (h : ModGL τ L)⁻¹ := by
    intro u
    rw [← heH, ← heH]
    change ((eH (eH.symm (mulAutRestrict _ (MulAut.conj (h : ModGL τ L)) hmap (eH u))) :
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) : ModGL τ L) = _
    rw [MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply]
  have hδinv : ∀ u, baseChangeGL (algebraMap K L) (δ⁻¹ u : ModGL τ K) =
      (h : ModGL τ L)⁻¹ * baseChangeGL (algebraMap K L) u * (h : ModGL τ L) := by
    intro u
    have h1 := hδ (δ⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  have hxv : x = (h : ModGL τ L)⁻¹ *
      Units.map (entrywiseHom (iterateFrobenius L ℓ e)) (h : ModGL τ L) := by
    rw [← hS h, ← hx'v]
    exact congrArg Subtype.val hxh
  refine ⟨δ, MulEquiv.ext fun u => Subtype.ext (baseChangeGL_injective (algebraMap K L) ?_)⟩
  change baseChangeGL (algebraMap K L) ((δ (β (δ⁻¹ u)) : adjointGroup τ K) : ModGL τ K) =
    baseChangeGL (algebraMap K L) ((entrywiseAdjointAut τ T u : adjointGroup τ K) : ModGL τ K)
  rw [hδ, hβ, coe_entrywiseAdjointAut, coe_entrywiseAdjointAut, ← hFι, ← hFι, hδinv, map_mul,
    map_mul, map_inv, hxv]
  group

theorem exists_conj_entrywise_of_not_innerDiag_of_quotient (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (Θ : MulAut (adjointGroup τ K) →* RingAut K × Multiplicative (ZMod (exactE τ)))
    (hΘ : ∀ (β : MulAut (adjointGroup τ K)) (g : adjointGroup τ K)
      (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE τ)),
      (∀ h : adjointGroup τ K, (β h : ModGL τ K) = (g : ModGL τ K) *
        rootDiagUnit τ a * exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom)
          (h : ModGL τ K) * (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ *
            (g : ModGL τ K)⁻¹) →
      Θ β = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE τ))))
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut τ K a) :
    ∃ (d : ℕ) (T : K ≃+* K) (r j : ℕ) (ψ : MulAut (adjointGroup τ K)), f = p * d ∧
      orderOf T = p ∧ Nat.card (fixSubfield T) = ℓ ^ d ∧ (∀ c, T c = c ^ ℓ ^ d) ∧
        orderOf (T ^ j) = p ∧ (α ^ r) ^ j = α ∧ ψ * α ^ r * ψ⁻¹ = entrywiseAdjointAut τ T ∧
        Θ α = (T ^ j, Multiplicative.ofAdd 0) ∧
        ψ * α * ψ⁻¹ = entrywiseAdjointAut τ (T ^ j) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL τ K) := finite_modGL
  have h2p : ¬2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form τ hτ K
  have hgraph : ∀ (β : MulAut (adjointGroup τ K)) (g : adjointGroup τ K)
      (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE τ)),
      (∀ h : adjointGroup τ K, (β h : ModGL τ K) = (g : ModGL τ K) *
        rootDiagUnit τ a * exactQ τ K ε * Units.map (entrywiseHom σ.toRingHom)
          (h : ModGL τ K) * (exactQ τ K ε)⁻¹ * (rootDiagUnit τ a)⁻¹ *
            (g : ModGL τ K)⁻¹) → β ^ p = 1 → (ε : ℕ) = 0 ∧ σ ^ p = 1 := by
    intro β g a σ ε hβ hβp
    have h1 : Θ β ^ p = 1 := by rw [← map_pow, hβp, map_one]
    rw [hΘ β g a σ ε hβ, Prod.pow_mk, Prod.mk_eq_one, ← ofAdd_nsmul, ofAdd_eq_one,
      nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h1
    refine ⟨?_, h1.1⟩
    have hE2 : exactE τ ∣ 2 := by
      rcases hτ with rfl | rfl | rfl <;> decide
    have h2 : exactE τ ∣ (ε : ℕ) := Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.coprime_dvd_left hE2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2p))
      h1.2
    exact Nat.eq_zero_of_dvd_of_lt h2 ε.isLt
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  obtain ⟨hε0, hσp1⟩ := hgraph α g a σ ε hga hαp
  have hΘα : Θ α = (σ, Multiplicative.ofAdd 0) := by
    rw [hΘ α g a σ ε hga, hε0, Nat.cast_zero]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    refine hnd g a (MulEquiv.ext fun h => Subtype.ext ?_)
    have h1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL τ K) = h := by
      have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
      rw [e1]
      exact Units.ext (entrywise_id (R := K) _)
    rw [hga h, hε0, exactQ_zero, hσ1, h1, MulAut.mul_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
    group
  have hαord : orderOf α = p := orderOf_eq_prime hαp fun h1 => hσ1 (by
    have h := hΘα
    rw [h1, map_one] at h
    exact (congrArg Prod.fst h).symm)
  have hσp : orderOf σ = p := orderOf_eq_prime hσp1 hσ1
  obtain ⟨hpf, -⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hpf
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hℓ hf hK
  have hfpos : 0 < f := hf
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hσmem : σ ∈ Subgroup.zpowers fr := by rw [hgen]; exact Subgroup.mem_top σ
  obtain ⟨k, hk, hkσ⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσmem)
  replace hkσ : fr ^ k = σ := hkσ
  rw [Finset.mem_range, hord] at hk
  have hdk : d ∣ k := by
    have h1 : f ∣ k * p := by
      rw [← hord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, hkσ, ← hσp, pow_orderOf_eq_one]
    rw [← hdp] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hp.pos h1
  obtain ⟨j, rfl⟩ := hdk
  have hjp : j < p := by
    by_contra hjp
    have : d * p ≤ d * j := Nat.mul_le_mul_left d (not_lt.1 hjp)
    omega
  have hj0 : 0 < j := by
    refine Nat.pos_of_ne_zero fun hj => ?_
    rw [hj, mul_zero, pow_zero] at hkσ
    exact hσ1 hkσ.symm
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ ℓ ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hTj : T ^ j = σ := by rw [hTdef, ← pow_mul, hkσ]
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow_of_dvd (by omega) (by rw [hord, ← hdp]; exact Dvd.intro p rfl), hord,
      ← hdp, Nat.mul_div_cancel_left p hd0]
  obtain ⟨r, hr⟩ := exists_mul_mod_eq_one hp hj0 hjp
  have hσr : σ ^ r = T := by
    rw [← hTj, ← pow_mul, pow_eq_self_of_mod_eq_one hTord (by rw [mul_comm]; exact hr)]
  have hαrp : (α ^ r) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hαp, one_pow]
  obtain ⟨g', a', σ', ε', hga'⟩ := hex (α ^ r)
  obtain ⟨hε'0, -⟩ := hgraph _ g' a' σ' ε' hga' hαrp
  have hσ'T : σ' = T := by
    have h1 := hΘ _ g' a' σ' ε' hga'
    rw [map_pow, hΘα, Prod.pow_mk] at h1
    have h2 : σ ^ r = σ' := congrArg Prod.fst h1
    rw [← h2, hσr]
  set L := AlgebraicClosure K with hL
  set x : ModGL τ L :=
    baseChangeGL (algebraMap K L) ((g' : ModGL τ K) * rootDiagUnit τ a') with hxdef
  have hx : x ∈ adjointGroup τ L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ g'.2)
      (exceptional_Lang_adjoint_diagonal_lift τ L _).1
  have hβ : ∀ u : adjointGroup τ K, baseChangeGL (algebraMap K L)
      (((α ^ r) u : adjointGroup τ K) : ModGL τ K) = x * baseChangeGL (algebraMap K L)
        ((entrywiseAdjointAut τ T u : adjointGroup τ K) : ModGL τ K) * x⁻¹ := by
    intro u
    rw [hga' u, hε'0, exactQ_zero, hσ'T, coe_entrywiseAdjointAut, hxdef]
    simp only [map_mul, map_inv, mul_one, inv_one]
    group
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    have hpf3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · exact (Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le (fun h2 => hp2 h2.symm)))
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by
        have : p ≤ f := by rw [← hdp]; exact Nat.le_mul_of_pos_left p hd0
        omega)
      _ ≤ ℓ ^ f := Nat.pow_le_pow_left hℓ.two_le f
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_of_ambient τ K hK hK4 hd0
    hp.one_lt.le hdp T hT L x hx (α ^ r) hβ hαrp
  have hcard := (card_fixSubfield hℓ hf hK T).2
  have hαβ : (α ^ r) ^ j = α := by rw [← pow_mul, pow_eq_self_of_mod_eq_one hαord hr]
  have hψα : ψ * α * ψ⁻¹ = entrywiseAdjointAut τ (T ^ j) := by
    conv_lhs => rw [← hαβ]
    rw [← conj_pow, hψ, ← entrywiseAdjointAut_pow]
  refine ⟨d, T, r, j, ψ, hd, hTord, ?_, hT, by rw [hTj]; exact hσp, hαβ, hψ, by rw [hTj]; exact hΘα, hψα⟩
  rw [hcard, hTord, hd, Nat.mul_div_cancel_left d hp.pos]

theorem even_E6_noninner_large_prime_field_descent_and_local_core_trivial {f p : ℕ}
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)))
    (hΘ : ∀ (β : MulAut (adjointGroup Tag.E6 K)) (g : adjointGroup Tag.E6 K)
      (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) (ε : Fin (exactE Tag.E6)),
      (∀ h : adjointGroup Tag.E6 K, (β h : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) *
        rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε * Units.map (entrywiseHom σ.toRingHom)
          (h : ModGL Tag.E6 K) * (exactQ Tag.E6 K ε)⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ *
            (g : ModGL Tag.E6 K)⁻¹) →
      Θ β = (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE Tag.E6))))
    (hp : p.Prime) (hp3 : 3 < p) (B : Subgroup (MulAut (adjointGroup Tag.E6 K)))
    (hB : (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ≤ B)
    (α : B) (hα : (α : MulAut (adjointGroup Tag.E6 K)) ∉
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range)
    (hαp : orderOf α = p) :
    (∃ σ : K ≃+* K, Θ α = (σ, Multiplicative.ofAdd 0) ∧ orderOf σ = p ∧
      ∃ ψ : MulAut (adjointGroup Tag.E6 K),
        ψ * (α : MulAut (adjointGroup Tag.E6 K)) * ψ⁻¹ = entrywiseAdjointAut Tag.E6 σ) ∧
      p ∣ f ∧ aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  set α' : MulAut (adjointGroup Tag.E6 K) := (α : MulAut (adjointGroup Tag.E6 K)) with hα'
  have hα'p : orderOf α' = p := by rw [hα', Subgroup.orderOf_coe, hαp]
  have hα'pow : α' ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one α'
  have hnd : ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      α' ≠ MulAut.conj g * rootDiagAut Tag.E6 K a := by
    intro g a hαdiag
    obtain ⟨Φ, -, hΦker, hΦcard⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
    have hmker : QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) α' ∈ Φ.ker := by
      rw [hΦker]
      refine ⟨a, ?_⟩
      have hc : QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) (MulAut.conj g) = 1 :=
        (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
      rw [hαdiag, map_mul, hc, one_mul]
      rfl
    have hm3 : orderOf (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) α') ∣ 3 := by
      have h1 := Subgroup.orderOf_dvd_natCard Φ.ker hmker
      rw [det_cartan_E6] at hΦcard
      exact h1.trans hΦcard
    have hmp : orderOf (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) α') ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα'pow, map_one])
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have hm1 : orderOf (QuotientGroup.mk' (inner (adjointGroup Tag.E6 K)) α') = 1 :=
      Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd hmp hm3)
    exact hα ((QuotientGroup.eq_one_iff (N := inner (adjointGroup Tag.E6 K)) α').1
      (orderOf_eq_one_iff.1 hm1))
  obtain ⟨d, T, r, j, ψ, hd, -, -, hT, hTjord, hαβ, hψ, hΘα, hψα⟩ :=
    exists_conj_entrywise_of_not_innerDiag_of_quotient Tag.E6 (Or.inl rfl) hf K hK hp
      (by omega) Θ hΘ α' hα'pow hnd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hαβB : (α ^ r) ^ j = α :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_pow]; exact hαβ)
  have hK' : Nat.card K = 2 ^ (d * p) := by rw [hK, hdp]
  obtain ⟨-, -, -, hJC, hsimple, hnc, ⟨ι, -⟩, hNδ, hnormal, hcent, -⟩ :=
    even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer hd0 hp.two_le K hK' T hT
  have hαr : orderOf (α ^ r) = p := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← pow_mul, mul_comm, pow_mul, ← hαp, pow_orderOf_eq_one, one_pow]
    · have h2 : α = 1 := by rw [← hαβB, h1, one_pow]
      rw [h2, orderOf_one] at hαp
      exact hp.one_lt.ne hαp
  have hcentr : (Subgroup.centralizer {α} : Subgroup B) = Subgroup.centralizer {α ^ r} := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ((Commute.pow_right h r).eq : _)
    · intro h
      have h1 := (Commute.pow_right (show Commute y (α ^ r) from h) j).eq
      rwa [hαβB] at h1
  have hψr : ψ * ((α ^ r : B) : MulAut (adjointGroup Tag.E6 K)) * ψ⁻¹ =
      entrywiseAdjointAut TwistTag.E6.tag T := by
    rw [Subgroup.coe_pow]
    exact hψ
  refine ⟨⟨T ^ j, hΘα, hTjord, ψ, hψα⟩, ⟨d, hd⟩, ?_⟩
  rw [hcentr]
  exact aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB (α ^ r) hαr ψ _ hψr
    hsimple hnc ι hNδ hnormal hcent

end CFSG.RankThree.Chevalley
