module

public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Arith

theorem not_dvd_d4_index_aux {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ha : p ∣ a) :
    ¬ p ∣ (a + 2) * ((a + 1) ^ 3 + 1) * ((a + 1) ^ 8 + (a + 1) ^ 4 + 1) := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  have h' : (((a + 2) * ((a + 1) ^ 3 + 1) * ((a + 1) ^ 8 + (a + 1) ^ 4 + 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  have ha' : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr ha
  push_cast at h'
  rw [ha'] at h'
  norm_num at h'
  have h12 : ((12 : ℕ) : ZMod p) = 0 := by
    exact_mod_cast (by linear_combination h' : (12 : ZMod p) = 0)
  have h12' : p ∣ 12 := (ZMod.natCast_eq_zero_iff _ _).mp h12
  have := Nat.le_of_dvd (by norm_num) h12'
  interval_cases p <;> first | omega | (exfalso; revert hp; decide)

theorem index_cancel_aux {I a A Q C1 C2 : ℕ} (ha : 0 < a) (hA : 0 < A) (hQ : 0 < Q)
    (h : I * (a * A * a * Q) = Q * (a * (a + 2)) * (C1 * (a * A)) * C2) :
    I = (a + 2) * C1 * C2 := by
  have hK : 0 < a * a * A * Q := by positivity
  apply Nat.eq_of_mul_eq_mul_right hK
  calc I * (a * a * A * Q) = I * (a * A * a * Q) := by ring
    _ = Q * (a * (a + 2)) * (C1 * (a * A)) * C2 := h
    _ = (a + 2) * C1 * C2 * (a * a * A * Q) := by ring

end Arith

section Split


theorem closure_centralizers_graphFixed_of_conj_borel (t : TwistTag) (k : Type) [Field k]
    [Finite k] (r p : ℕ) [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p)
    (σ : k ≃+* k) (hσ : σ ^ t.order = 1) [IsSimpleGroup (graphFixedRootGroup t k σ.toRingHom)]
    (A : Subgroup (ModGL t.tag k)) (hAC : A ≤ graphFixedRootGroup t k σ.toRingHom)
    [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A)
    (hUr : IsPGroup r (graphFixedPosUnipotent t k σ.toRingHom))
    (hU : graphFixedPosUnipotent t k σ.toRingHom ≠ ⊥)
    (hidx : ¬ p ∣ ((graphFixedRootBorel t k σ.toRingHom).subgroupOf
      (graphFixedRootGroup t k σ.toRingHom)).index) :
    (⨆ a ∈ A, ⨆ (_ : a ≠ 1), graphFixedRootGroup t k σ.toRingHom ⊓
        Subgroup.centralizer ({a} : Set (ModGL t.tag k))) =
      graphFixedRootGroup t k σ.toRingHom := by
  have := finite_modGL (τ := t.tag) (K := k)
  obtain ⟨y, hyC, hyA⟩ := exists_conj_le_of_not_dvd_index hAC
    (IsElementaryAbelian.isPGroup p A) hidx
  have hA'C : A.map (MulAut.conj y).toMonoidHom ≤ graphFixedRootGroup t k σ.toRingHom := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem hyC (hAC ha)) (inv_mem hyC)
  have : IsElementaryAbelian p (A.map (MulAut.conj y).toMonoidHom) := IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj y).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact hcard
  have hAR : A.map (MulAut.conj y).toMonoidHom ≤
      Subgroup.normalizer (graphFixedPosUnipotent t k σ.toRingHom : Set (ModGL t.tag k)) :=
    hyA.trans graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent
  have hmain := fixed_root_invariant_prime_subgroup_centralizer_generation t k r p hrp σ hσ
    (A.map (MulAut.conj y).toMonoidHom) hA'C hcard' (graphFixedPosUnipotent t k σ.toRingHom)
    (graphFixedPosUnipotent_le_graphFixedRootGroup t k σ.toRingHom) hUr hU hAR
  refine le_antisymm (iSup₂_le fun a _ => iSup_le fun _ => inf_le_left) ?_
  exact le_iSup_inf_centralizer_of_map_conj hyC hmain.ge

theorem not_dvd_index_borel_D4 (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (X : Type) [Field X]
    [Finite X] (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f - 1) :
    ¬ p ∣ ((graphFixedRootBorel TwistTag.D4 X σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 X σ.toRingHom)).index := by
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  obtain ⟨hC, hT, hU⟩ := triality_both_orientations_exact_finite_order ℓ f hℓ hf X hX 1
    (Or.inl rfl) σ.toRingHom (by simpa using hσ)
  have hB := CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootBorel (t := TwistTag.D4)
    (K := X) (σ := σ.toRingHom) σ.surjective
  have h1 := Subgroup.index_mul_card ((graphFixedRootBorel TwistTag.D4 X σ.toRingHom).subgroupOf
    (graphFixedRootGroup TwistTag.D4 X σ.toRingHom))
  rw [card_subgroupOf_of_le (graphFixedRootBorel_le TwistTag.D4 X σ.toRingHom), hB, hT, hU,
    hC] at h1
  obtain ⟨m, hm⟩ := hpq
  generalize ℓ ^ f = q at hq2 h1 hm
  have hq : q = p * m + 1 := by omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm; omega
    · exact h0
  subst hq
  have e1 : (p * m + 1 - 1) = p * m := Nat.add_sub_cancel (n := p * m) (m := 1)
  have e2 : (p * m + 1) ^ 2 - 1 = (p * m) * (p * m + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e3 : (p * m + 1) ^ 3 - 1 = (p * m) * ((p * m + 1) ^ 2 + (p * m + 1) + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e4 : (p * m + 1) ^ 6 - 1 = ((p * m + 1) ^ 3 + 1) * ((p * m + 1) ^ 3 - 1) := by
    have h := Nat.mul_self_sub_mul_self_eq ((p * m + 1) ^ 3) 1
    rw [← pow_two, ← pow_mul, mul_one] at h
    simpa using h
  rw [e4, e3, e2, e1] at h1
  intro hdiv
  have hind := index_cancel_aux (by positivity) (by positivity) (by positivity) h1
  rw [hind] at hdiv
  exact not_dvd_d4_index_aux hp hp5 (dvd_mul_right p m) hdiv

theorem closure_centralizers_graphFixed_D4_split (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (X : Type) [Field X] [Finite X] [CharP X ℓ] (hX : Nat.card X = (ℓ ^ f) ^ 3) (σ : X ≃+* X)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hσ3 : σ ^ TwistTag.D4.order = 1) (p : ℕ) [Fact p.Prime]
    (hrp : ℓ ≠ p) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f - 1)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.D4 X σ.toRingHom)]
    (E₁ : Subgroup (graphFixedRootGroup TwistTag.D4 X σ.toRingHom)) [IsElementaryAbelian p E₁]
    (hcard : Nat.card E₁ = p ^ 2) :
    Subgroup.closure {k' : graphFixedRootGroup TwistTag.D4 X σ.toRingHom |
      ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  let C : Subgroup (ModGL TwistTag.D4.tag X) := graphFixedRootGroup TwistTag.D4 X σ.toRingHom
  let A : Subgroup (ModGL TwistTag.D4.tag X) := E₁.map C.subtype
  have hAC : A ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have : IsElementaryAbelian p A := IsElementaryAbelian.map _
  have hcardA : p ^ 2 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hcard]
  obtain ⟨-, -, hU⟩ := triality_both_orientations_exact_finite_order ℓ f hℓ hf X hX 1
    (Or.inl rfl) σ.toRingHom (by simpa using hσ)
  have hUr : IsPGroup ℓ (graphFixedPosUnipotent TwistTag.D4 X σ.toRingHom) := by
    refine IsPGroup.of_card (n := f * 12) ?_
    rw [hU, pow_mul]
  have hU0 : graphFixedPosUnipotent TwistTag.D4 X σ.toRingHom ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU
    have : 1 < (ℓ ^ f) ^ 12 := Nat.one_lt_pow (by norm_num) hq2
    omega
  have hmain := closure_centralizers_graphFixed_of_conj_borel TwistTag.D4 X ℓ p hrp σ hσ3 A hAC
    hcardA hUr hU0 (not_dvd_index_borel_D4 ℓ f hℓ hf X hX σ hσ p Fact.out hp5 hpq)
  exact closure_centralizers_of_iSup_eq C E₁ hmain

end Split

section Models


theorem exists_trialityD4_model {q : TauCeti.PrimePower} (hq : q.p = 2) {K : Type} [Group K]
    (hiso : IsoLie K (.trialityD4 q)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (σ : X ≃+* X), Nat.card X = (2 ^ q.exponent) ^ 3 ∧
      (∀ c, σ c = c ^ (2 ^ q.exponent)) ∧ σ ^ TwistTag.D4.order = 1 ∧
      Nonempty (K ≃* graphFixedRootGroup TwistTag.D4 X σ.toRingHom) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hm' : TwistedChevalleyModel K .D4 (q.p ^ q.exponent) :=
    CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e0
  obtain ⟨X, _, _, hcardX, σ, hσ, ⟨e⟩⟩ := hm'
  have hf1 : 1 ≤ q.exponent := q.exponent_pos
  rw [hq] at hcardX hσ
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields .D4 Nat.prime_two hf1 X hcardX
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, ⟨E'⟩⟩ :=
    even_triality_exact_automorphism_normal_form hf1 X hcardX σ' hσ'
  exact ⟨X, inferInstance, inferInstance, σ', hcardX, hσ', by
    rw [← hord]; exact pow_orderOf_eq_one σ', ⟨e.trans E'⟩⟩

theorem extSeitzAtInnerFor_trialityD4_split {q : TauCeti.PrimePower} (hq : q.p = 2) :
    ExtSeitzAtInnerFor (.trialityD4 q) fun p => p ∣ q.card - 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hpq E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, σ, hX, hσ, hσ3, ⟨e⟩⟩ := exists_trialityD4_model hq hiso
  have : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 X σ.toRingHom) :=
    MulEquiv.isSimpleGroup e.symm
  have : CharP X 2 := finite_field_prime_power_characteristic Nat.prime_two
    (k := q.exponent * 3) (Nat.mul_pos q.exponent_pos (by norm_num)) (by rw [hX, ← pow_mul])
  have hpq' : p ∣ 2 ^ q.exponent - 1 := by simpa [PrimePower.card_def, hq] using hpq
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  exact closure_centralizers_graphFixed_D4_split 2 q.exponent Nat.prime_two q.exponent_pos X hX σ
    hσ hσ3 p (by omega) hp5 hpq' E₁ hcard₁

end Models

end CFSG.RankThree.PartOne.CTP
