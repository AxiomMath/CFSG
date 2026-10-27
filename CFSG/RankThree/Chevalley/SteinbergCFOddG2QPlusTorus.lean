module

public import CFSG.RankThree.Chevalley.G2CyclotomicTori
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical

theorem card_rootsOfUnity_of_dvd_card_sub_one {F : Type*} [Field F] [Finite F] {n : ℕ}
    [NeZero n] (hn : n ∣ Nat.card F - 1) : Nat.card (rootsOfUnity n F) = n := by
  set N := Nat.card F - 1 with hN
  have hNu : Nat.card Fˣ = N := Nat.card_units F
  have : NeZero N := ⟨by
    have := Finite.one_lt_card (α := F)
    omega⟩
  have htop : rootsOfUnity N F = ⊤ := by
    ext x
    simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    rw [← hNu]
    exact pow_card_eq_one'
  have hcard : N ≤ Nat.card (rootsOfUnity N F) := by
    rw [htop, Subgroup.card_top, hNu]
  have : HasEnoughRootsOfUnity F N := HasEnoughRootsOfUnity.of_card_le hcard
  have : HasEnoughRootsOfUnity F n := HasEnoughRootsOfUnity.of_dvd F hn
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := F) (n := n)
  exact hζ.card_rootsOfUnity

theorem ringChar_ne_two_of_odd_natCard {F : Type*} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) : ringChar F ≠ 2 := fun h => by
  have : Fintype F := Fintype.ofFinite F
  have := FiniteField.even_card_iff_char_two.1 h
  rw [← Nat.card_eq_fintype_card] at this
  exact (Nat.not_even_iff_odd.2 hF) (Nat.even_iff.2 this)

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

omit [Finite K] in
theorem natCard_eq_sq_of_finrank_eq_two (hdeg : Module.finrank K K₂ = 2) :
    Nat.card K₂ = Nat.card K ^ 2 := by
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  rw [Module.natCard_eq_pow_finrank (K := K), hdeg]

theorem exists_frobenius_eq_neg (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    (∀ c, σ (σ c) = c) ∧ ∃ ω : K₂, ω ≠ 0 ∧ σ ω = -ω := by
  obtain ⟨-, hord, -⟩ := quadratic_frobenius hdeg σ hσ
  have hσ2 : σ ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hinv : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun f : K₂ ≃+* K₂ => f c) hσ2
    simp only [pow_two, RingAut.mul_apply, RingAut.one_apply] at h
    exact h
  have hne : σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra h
    push Not at h
    exact hne (RingEquiv.ext fun x => by rw [h x]; rfl)
  refine ⟨hinv, c - σ c, sub_ne_zero.2 (Ne.symm hc), ?_⟩
  rw [map_sub, hinv]
  ring

section Matrix

variable {L : Type} [Field L]

@[expose] def quadraticTorusP (ω : L) (hω : ω ≠ 0) (h2 : (2 : L) ≠ 0) : SL2 L :=
  ⟨!![1 / 2, -ω; 1 / (2 * ω), 1], by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

@[expose] def twoMulUnit (ω : L) (hω : ω ≠ 0) (h2 : (2 : L) ≠ 0) : Lˣ :=
  Units.mk0 (2 * ω) (mul_ne_zero h2 hω)

theorem quadraticTorusP_mul_nSL (σ : L ≃+* L) {ω : L} (hω : ω ≠ 0) (h2 : (2 : L) ≠ 0)
    (hσω : σ ω = -ω) :
    quadraticTorusP ω hω h2 * nSL (twoMulUnit ω hω h2) =
      Matrix.SpecialLinearGroup.map (σ : L →+* L) (quadraticTorusP ω hω h2) := by
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [quadraticTorusP, nSL, twoMulUnit, Matrix.mul_apply, Fin.sum_univ_two, hσω, hσ2]
  all_goals field_simp

end Matrix

theorem iform_g2a_g2v : iform g2a g2v = 0 := by decide

theorem not_isRoot_g2a_add_g2v : ¬ IsRoot .G2 (g2a + g2v) := fun h => by
  have := g2Pair_mem_of_isRoot h
  revert this
  decide

theorem not_isRoot_g2a_sub_g2v : ¬ IsRoot .G2 (g2a - g2v) := fun h => by
  have := g2Pair_mem_of_isRoot h
  revert this
  decide

theorem rootReflection_g2a_mul_g2v_smul (v : Fin Tag.G2.rank → ℤ) :
    (rootReflection g2a * rootReflection g2v) • v = -v := by
  have hinv : ∀ i : Fin Tag.G2.rank, (simple .G2 i)⁻¹ = simple .G2 i :=
    (coxeterSystem .G2).inv_simple
  have h1 : rootReflection g2a = simple .G2 g2ia := by
    rw [rootReflection_eq_conj (w := 1) (j := g2ia) (by rw [one_smul, g2a_eq_single]), one_mul,
      inv_one, mul_one]
  have h2 : rootReflection g2v = simple .G2 g2ir * simple .G2 g2ia * simple .G2 g2ir *
      (simple .G2 g2ir * simple .G2 g2ia)⁻¹ :=
    rootReflection_eq_conj (by
      rw [mul_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel))
  have ha : (rootReflection g2a * rootReflection g2v) • g2a = -g2a := by
    rw [h1, h2]
    simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have hr : (rootReflection g2a * rootReflection g2v) • g2r = -g2r := by
    rw [h1, h2]
    simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  conv_lhs => rw [g2_eq_smul_add v]
  conv_rhs => rw [g2_eq_smul_add v]
  rw [smul_add, smul_comm _ (v g2ia), smul_comm _ (v g2ir), ha, hr, neg_add, smul_neg, smul_neg]

section Lang

variable {L : Type} [Field L]

theorem rootSL2_g2v_mul_rootSL2_g2a (A B : SL2 L) :
    rootSL2 .G2 L g2v A * rootSL2 .G2 L g2a B = rootSL2 .G2 L g2a B * rootSL2 .G2 L g2v A :=
  (exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .G2 L isRoot_g2a isRoot_g2v
    iform_g2a_g2v not_isRoot_g2a_add_g2v not_isRoot_g2a_sub_g2v _ ⟨B, rfl⟩ _ ⟨A, rfl⟩).symm

theorem rootSL2_pair_mul_entrywise_inv_eq (σ : L →+* L) {A B : SL2 L}
    (hAB : A * B = Matrix.SpecialLinearGroup.map σ A) :
    rootSL2 .G2 L g2a A⁻¹ * rootSL2 .G2 L g2v A⁻¹ *
        (Units.map (entrywiseHom σ) (rootSL2 .G2 L g2a A⁻¹ * rootSL2 .G2 L g2v A⁻¹))⁻¹ =
      rootSL2 .G2 L g2a B * rootSL2 .G2 L g2v B := by
  have hB : B = A⁻¹ * Matrix.SpecialLinearGroup.map σ A := by rw [← hAB, inv_mul_cancel_left]
  have hc := rootSL2_g2v_mul_rootSL2_g2a (L := L) (A⁻¹ * Matrix.SpecialLinearGroup.map σ A)
    (Matrix.SpecialLinearGroup.map σ A)
  rw [map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field, map_inv, hB, map_mul,
    map_mul]
  rw [map_mul] at hc
  simp only [map_inv, mul_inv_rev, inv_inv] at hc ⊢
  rw [mul_assoc, ← mul_assoc _ (rootSL2 .G2 L g2v (Matrix.SpecialLinearGroup.map σ A)), hc,
    ← mul_assoc]

theorem rootWeylSL2_pair_mem_monomial (c : Lˣ) :
    ∃ hz : rootWeylSL2 .G2 L g2a c * rootWeylSL2 .G2 L g2v c ∈ monomialSubgroup .G2 L,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 L ⟨_, hz⟩ • v = -v := by
  obtain ⟨-, -, ha, -⟩ := exceptional_Lang_root_rank_one_torus_transport .G2 L isRoot_g2a
  obtain ⟨-, -, hv, -⟩ := exceptional_Lang_root_rank_one_torus_transport .G2 L isRoot_g2v
  obtain ⟨ha1, ha2⟩ := ha c
  obtain ⟨hv1, hv2⟩ := hv c
  refine ⟨mul_mem ha1 hv1, fun v => ?_⟩
  have e : (⟨_, mul_mem ha1 hv1⟩ : monomialSubgroup .G2 L) = ⟨_, ha1⟩ * ⟨_, hv1⟩ := rfl
  rw [e, map_mul, ha2, hv2]
  exact rootReflection_g2a_mul_g2v_smul v

end Lang

section Inversion

variable {L : Type} [Field L] {τ : Tag}

theorem rootChar_inv_tuple (b : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar b⁻¹ v = (rootChar b v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem conj_rootDiagUnit_of_smul_eq_neg {z : ModGL τ L} (hz : z ∈ monomialSubgroup τ L)
    (hw : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨z, hz⟩ • v = -v) (b : Fin τ.rank → Lˣ) :
    z * rootDiagUnit τ b * z⁻¹ = rootDiagUnit τ b⁻¹ := by
  obtain ⟨w, h, hh, rfl⟩ := monomialSubgroup_le_torusWeylCosets hz
  have hπ : weylQuotientHom τ L ⟨h * canonicalRep (coxeterSystem τ) L w, hz⟩ = w :=
    weylQuotientHom_eq (by
      simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w))
  have hw' : ∀ v : Fin τ.rank → ℤ, w • v = -v := fun v => by rw [← hπ]; exact hw v
  have hn : canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ b⁻¹ :=
    ((rootDiagUnit_eq_conj_canonicalRep_iff b⁻¹ b w).2 fun v => by
      rw [hw', rootChar_neg_eq_inv, rootChar_inv_tuple, inv_inv]).symm
  calc h * canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
        (h * canonicalRep (coxeterSystem τ) L w)⁻¹ =
      h * (canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) L w)⁻¹) * h⁻¹ := by group
    _ = rootDiagUnit τ b⁻¹ := by
        rw [hn, ← rootDiagUnit_mul_comm_of_mem_torusGroup _ hh, mul_inv_cancel_right]

theorem conj_pinnedX_of_smul_eq_neg {z : ModGL τ L} (hz : z ∈ monomialSubgroup τ L)
    (hw : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨z, hz⟩ • v = -v) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    ∃ μ : Lˣ, ∀ c : L, z * pinnedX τ L γ c * z⁻¹ = pinnedX τ L (-γ) (μ * c) := by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hz hγ
  exact ⟨μ, fun c => by rw [hμ, hw]⟩

end Inversion

section Twisted

variable {τ : Tag} {L : Type} [Field L]

@[expose] def twistedEntrywise (z : ModGL τ L) (σ : L →+* L) : ModGL τ L →* ModGL τ L :=
  (MulAut.conj z).toMonoidHom.comp (Units.map (entrywiseHom σ))

theorem twistedEntrywise_apply (z : ModGL τ L) (σ : L →+* L) (y : ModGL τ L) :
    twistedEntrywise z σ y = z * Units.map (entrywiseHom σ) y * z⁻¹ :=
  rfl

@[expose] def conjEntrywiseImage (k : Type) [Field k] [Algebra k L] (g : ModGL τ L) :
    Subgroup (ModGL τ L) :=
  (adjointGroup τ k).map ((MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap k L)))

theorem units_map_entrywiseHom_entrywiseHom {σ : L →+* L} (hσ : ∀ c, σ (σ c) = c)
    (y : ModGL τ L) : Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ) y) = y := by
  ext1
  simp only [Units.coe_map]
  change entrywise σ (entrywise σ _) = _
  rw [entrywise_entrywise, show σ.comp σ = RingHom.id L from RingHom.ext hσ, entrywise_id]

theorem twistedEntrywise_twistedEntrywise {σ : L →+* L} (hσ : ∀ c, σ (σ c) = c)
    {g z : ModGL τ L} (hz : z = g * (Units.map (entrywiseHom σ) g)⁻¹) (y : ModGL τ L) :
    twistedEntrywise z σ (twistedEntrywise z σ y) = y := by
  have hzz : z * Units.map (entrywiseHom σ) z = 1 := by
    rw [hz, map_mul, map_inv, units_map_entrywiseHom_entrywiseHom hσ]
    group
  rw [twistedEntrywise_apply, twistedEntrywise_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_entrywiseHom hσ]
  calc z * (Units.map (entrywiseHom σ) z * y * (Units.map (entrywiseHom σ) z)⁻¹) * z⁻¹ =
        (z * Units.map (entrywiseHom σ) z) * y * (z * Units.map (entrywiseHom σ) z)⁻¹ := by
        group
    _ = y := by rw [hzz, one_mul, inv_one, mul_one]

theorem twistedEntrywise_rootDiagUnit {z : ModGL τ L} (hz : z ∈ monomialSubgroup τ L)
    (hw : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨z, hz⟩ • v = -v) (σ : L →+* L) {q : ℕ}
    (hσ : ∀ c, σ c = c ^ q) (c : Fin τ.rank → Lˣ) :
    twistedEntrywise z σ (rootDiagUnit τ c) = rootDiagUnit τ (c ^ q)⁻¹ := by
  rw [twistedEntrywise_apply, entrywise_frob_rootDiagUnit σ hσ,
    conj_rootDiagUnit_of_smul_eq_neg hz hw]

end Twisted

theorem conjEntrywiseImage_eq_fixed [Finite K₂] (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂} (hg : g ∈ adjointGroup .G2 K₂)
    (hz : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹) :
    conjEntrywiseImage K g = adjointGroup .G2 K₂ ⊓
      (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) := by
  have hfix := frobenius_fixed_eq_map_of_bijective (k := K) (τ := .G2) (Or.inl rfl)
    (σ : K₂ →+* K₂) hσ (Finite.injective_iff_bijective.1 σ.injective)
  have hzg : z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g = g := by
    rw [hz, inv_mul_cancel_right]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxF : baseChangeGL (algebraMap K K₂) x ∈ adjointGroup .G2 K₂ ⊓
        (Units.map (entrywiseHom (σ : K₂ →+* K₂))).eqLocus (MonoidHom.id _) := by
      rw [hfix]
      exact ⟨x, hx, rfl⟩
    obtain ⟨hxC, hxσ⟩ := Subgroup.mem_inf.1 hxF
    have hxσ' : Units.map (entrywiseHom (σ : K₂ →+* K₂)) (baseChangeGL (algebraMap K K₂) x) =
        baseChangeGL (algebraMap K K₂) x := hxσ
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hg hxC) (inv_mem hg)
    · change twistedEntrywise z (σ : K₂ →+* K₂)
          (g * baseChangeGL (algebraMap K K₂) x * g⁻¹) =
        g * baseChangeGL (algebraMap K K₂) x * g⁻¹
      rw [twistedEntrywise_apply, map_mul, map_mul, map_inv, hxσ']
      calc z * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g * baseChangeGL (algebraMap K K₂) x *
            (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹) * z⁻¹ =
          (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g) * baseChangeGL (algebraMap K K₂) x *
            (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := by group
        _ = g * baseChangeGL (algebraMap K K₂) x * g⁻¹ := by rw [hzg]
  · intro hy
    obtain ⟨hyC, hyF⟩ := Subgroup.mem_inf.1 hy
    have hyF' : z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) y * z⁻¹ = y := hyF
    have hσy : Units.map (entrywiseHom (σ : K₂ →+* K₂)) y = z⁻¹ * y * z := by
      calc Units.map (entrywiseHom (σ : K₂ →+* K₂)) y =
            z⁻¹ * (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) y * z⁻¹) * z := by group
        _ = z⁻¹ * y * z := by rw [hyF']
    have hσg : Units.map (entrywiseHom (σ : K₂ →+* K₂)) g = z⁻¹ * g := by
      calc Units.map (entrywiseHom (σ : K₂ →+* K₂)) g =
            z⁻¹ * (z * Units.map (entrywiseHom (σ : K₂ →+* K₂)) g) := by group
        _ = z⁻¹ * g := by rw [hzg]
    have hu : g⁻¹ * y * g ∈ adjointGroup .G2 K₂ ⊓
        (Units.map (entrywiseHom (σ : K₂ →+* K₂))).eqLocus (MonoidHom.id _) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg) hyC) hg, ?_⟩
      change Units.map (entrywiseHom (σ : K₂ →+* K₂)) (g⁻¹ * y * g) = g⁻¹ * y * g
      rw [map_mul, map_mul, map_inv, hσy, hσg]
      group
    rw [hfix] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hxu]
    group

section Torus

variable {L : Type} [Field L]

@[expose] def g2PairTuple (M : Type*) [CommGroup M] : M × M →* (Fin Tag.G2.rank → M) where
  toFun st i := if i = g2ia then st.1 else st.2
  map_one' := by
    funext i
    by_cases hi : i = g2ia <;> simp [hi]
  map_mul' st st' := by
    funext i
    by_cases hi : i = g2ia <;> simp [hi]

theorem g2PairTuple_ia {M : Type*} [CommGroup M] (st : M × M) :
    g2PairTuple M st g2ia = st.1 := by
  simp [g2PairTuple]

theorem g2PairTuple_ir {M : Type*} [CommGroup M] (st : M × M) :
    g2PairTuple M st g2ir = st.2 := by
  simp [g2PairTuple, g2ia, g2ir]

theorem g2PairTuple_eq {M : Type*} [CommGroup M] (c : Fin Tag.G2.rank → M) :
    g2PairTuple M (c g2ia, c g2ir) = c := by
  funext j
  rcases fin_G2_cases j with rfl | rfl
  · exact g2PairTuple_ia _
  · exact g2PairTuple_ir _

theorem g2PairTuple_injective {M : Type*} [CommGroup M] : Function.Injective (g2PairTuple M) := by
  intro st st' h
  have h1 := congrFun h g2ia
  have h2 := congrFun h g2ir
  rw [g2PairTuple_ia, g2PairTuple_ia] at h1
  rw [g2PairTuple_ir, g2PairTuple_ir] at h2
  exact Prod.ext h1 h2

variable (L) in
@[expose] def torusTorsion (n : ℕ) : Subgroup (ModGL .G2 L) :=
  ((rootsOfUnity n L).prod (rootsOfUnity n L)).map
    ((rootDiagUnitHom .G2 L).comp (g2PairTuple Lˣ))

theorem rootDiagUnit_mem_torusTorsion_iff (n : ℕ) (c : Fin Tag.G2.rank → Lˣ) :
    rootDiagUnit .G2 c ∈ torusTorsion L n ↔ c ^ n = 1 := by
  constructor
  · rintro ⟨st, hst, h⟩
    have hc : g2PairTuple Lˣ st = c := rootDiagUnit_injective h
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hst
    have hst1 : st ^ n = 1 := Prod.ext (by simpa using (mem_rootsOfUnity _ _).1 h1)
      (by simpa using (mem_rootsOfUnity _ _).1 h2)
    rw [← hc, ← map_pow, hst1, map_one]
  · intro h
    refine ⟨(c g2ia, c g2ir), Subgroup.mem_prod.2 ⟨(mem_rootsOfUnity _ _).2 ?_,
      (mem_rootsOfUnity _ _).2 ?_⟩, ?_⟩
    · simpa using congrFun h g2ia
    · simpa using congrFun h g2ir
    · change rootDiagUnit .G2 (g2PairTuple Lˣ (c g2ia, c g2ir)) = rootDiagUnit .G2 c
      rw [g2PairTuple_eq]

theorem rootDiagUnit_mem_torusGroup_G2 (c : Fin Tag.G2.rank → Lˣ) :
    rootDiagUnit .G2 c ∈ torusGroup .G2 L := by
  obtain ⟨⟨B, hB, -⟩, hdiag⟩ := G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) L
  exact (hdiag B hB c).2.1

theorem torusTorsion_le_torusGroup (n : ℕ) : torusTorsion L n ≤ torusGroup .G2 L := by
  rintro _ ⟨st, -, rfl⟩
  exact rootDiagUnit_mem_torusGroup_G2 _

theorem torusTorsion_mono {m n : ℕ} (h : m ∣ n) : torusTorsion L m ≤ torusTorsion L n :=
  Subgroup.map_mono (Subgroup.prod_mono (rootsOfUnity_le_of_dvd h) (rootsOfUnity_le_of_dvd h))

theorem mem_torusTorsion_iff {n : ℕ} {h : ModGL .G2 L} :
    h ∈ torusTorsion L n ↔ h ∈ torusGroup .G2 L ∧ h ^ n = 1 := by
  constructor
  · intro hh
    refine ⟨torusTorsion_le_torusGroup n hh, ?_⟩
    obtain ⟨st, hst, rfl⟩ := hh
    have h1 := (rootDiagUnit_mem_torusTorsion_iff n (g2PairTuple Lˣ st)).1 ⟨st, hst, rfl⟩
    change rootDiagUnitHom .G2 L (g2PairTuple Lˣ st) ^ n = 1
    rw [← map_pow, h1, map_one]
  · rintro ⟨hH, hn⟩
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
    refine (rootDiagUnit_mem_torusTorsion_iff n c).2 (rootDiagUnit_injective ?_)
    change rootDiagUnitHom .G2 L (c ^ n) = rootDiagUnitHom .G2 L 1
    rw [map_pow, map_one]
    exact hn

variable (L) in
@[expose] def torusTorsionEquiv (n : ℕ) :
    (rootsOfUnity n L × rootsOfUnity n L) ≃* torusTorsion L n :=
  (Subgroup.prodEquiv _ _).symm.trans (Subgroup.equivMapOfInjective _ _
    (rootDiagUnit_injective.comp g2PairTuple_injective))

theorem natCard_torusTorsion [Finite L] {n : ℕ} [NeZero n] (hn : n ∣ Nat.card L - 1) :
    Nat.card (torusTorsion L n) = n ^ 2 := by
  rw [← Nat.card_congr (torusTorsionEquiv L n).toEquiv, Nat.card_prod,
    card_rootsOfUnity_of_dvd_card_sub_one hn, sq]

theorem nonempty_torusTorsion_mulEquiv [Finite L] {n : ℕ} [NeZero n] (hn : n ∣ Nat.card L - 1) :
    Nonempty (torusTorsion L n ≃* Multiplicative (ZMod n) × Multiplicative (ZMod n)) := by
  have e : rootsOfUnity n L ≃* Multiplicative (ZMod n) :=
    mulEquivOfCyclicCardEq (by rw [card_rootsOfUnity_of_dvd_card_sub_one hn]; simp)
  exact ⟨(torusTorsionEquiv L n).symm.trans (MulEquiv.prodCongr e e)⟩

theorem torusGroup_inf_eq_torusTorsion {z : ModGL .G2 L} (hz : z ∈ monomialSubgroup .G2 L)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 L ⟨z, hz⟩ • v = -v) (σ : L →+* L)
    {q : ℕ} (hσ : ∀ c, σ c = c ^ q) {Γ : Subgroup (ModGL .G2 L)}
    (hΓ : Γ = adjointGroup .G2 L ⊓ (twistedEntrywise z σ).eqLocus (MonoidHom.id _)) :
    torusGroup .G2 L ⊓ Γ = torusTorsion L (q + 1) := by
  have key : ∀ c : Fin Tag.G2.rank → Lˣ,
      twistedEntrywise z σ (rootDiagUnit .G2 c) = rootDiagUnit .G2 c ↔ c ^ (q + 1) = 1 := by
    intro c
    rw [twistedEntrywise_rootDiagUnit hz hw σ hσ]
    constructor
    · intro h
      rw [pow_succ]
      exact inv_eq_iff_mul_eq_one.1 (rootDiagUnit_injective h)
    · intro h
      rw [inv_eq_iff_mul_eq_one.2 (by rw [← pow_succ]; exact h)]
  ext x
  constructor
  · rintro ⟨hxH, hxΓ⟩
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
    rw [hΓ] at hxΓ
    exact (rootDiagUnit_mem_torusTorsion_iff _ c).2 ((key c).1 hxΓ.2)
  · intro hx
    obtain ⟨st, hst, rfl⟩ := hx
    have hc := (rootDiagUnit_mem_torusTorsion_iff (q + 1) (g2PairTuple Lˣ st)).1 ⟨st, hst, rfl⟩
    refine ⟨rootDiagUnit_mem_torusGroup_G2 _, ?_⟩
    rw [hΓ]
    exact ⟨torusGroup_le_adjointGroup_G2 (rootDiagUnit_mem_torusGroup_G2 _), (key _).2 hc⟩

end Torus

theorem not_dvd_of_sq_mul_eq_ordG2 {q I p : ℕ} (hq : 1 ≤ q) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ q + 1) (h : (q + 1) ^ 2 * I = CFSG.Open.ordG2 q) : ¬ p ∣ I := by
  have hZ : ((q : ℤ) + 1) ^ 2 * I = (q : ℤ) ^ 6 * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 2 - 1) := by
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    rw [CFSG.Open.ordG2] at h'
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at h'
    exact h'
  have hI : (I : ℤ) = (q : ℤ) ^ 6 * ((q : ℤ) - 1) ^ 2 * ((q : ℤ) ^ 2 + q + 1) *
      ((q : ℤ) ^ 2 - q + 1) := by
    have hne : ((q : ℤ) + 1) ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro hdvd
  have hI0 : (I : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff I p).2 hdvd
  have hqp : (q : ZMod p) = -1 := by
    have h1 := (ZMod.natCast_eq_zero_iff (q + 1) p).2 hpq
    push_cast at h1
    linear_combination h1
  have h12 : ((12 : ℕ) : ZMod p) = 0 := by
    have h' := congrArg (Int.cast : ℤ → ZMod p) hI
    push_cast at h'
    rw [hqp, hI0] at h'
    rw [h']
    norm_num
  have hp12 := (ZMod.natCast_eq_zero_iff 12 p).1 h12
  have := Nat.le_of_dvd (by norm_num) hp12
  interval_cases p <;> first | (norm_num at hp; done) | norm_num at hp12

theorem exists_sylow_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {T : Subgroup G} (hT : ¬ p ∣ T.index) :
    ∃ S : Sylow p G, (S : Subgroup G) ≤ T := by
  obtain ⟨S₀⟩ : Nonempty (Sylow p T) := inferInstance
  have hS : IsPGroup p ((S₀ : Subgroup T).map T.subtype) := S₀.isPGroup'.map T.subtype
  have hSi : ¬ p ∣ ((S₀ : Subgroup T).map T.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hT
  exact ⟨hS.toSylow hSi, by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.map_subtype_le _⟩

theorem natCard_conjEntrywiseImage {τ : Tag} {L : Type} [Field L] (k : Type) [Field k]
    [Algebra k L] (g : ModGL τ L) :
    Nat.card (conjEntrywiseImage k g) = Nat.card (adjointGroup τ k) :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom.comp
    (baseChangeGL (algebraMap k L))) ((MulAut.conj g).injective.comp
      (baseChangeGL_injective (τ := τ) (algebraMap k L)))

end CFSG.RankThree.Chevalley
