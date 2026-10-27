module

public import CFSG.RankThree.PartOne.S11d.FixedFactsE6Tw

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

section


@[expose] def TwistedE6Canon (d m : ℕ) (K : Type) [Field K] [Finite K] (κ σ : K ≃+* K)
    (σ₀ : fixSubfield κ ≃+* fixSubfield κ) (ε : K ≃+* K) : Prop :=
  (∀ c : K, c ∈ fixSubfield κ ↔ c ^ 2 ^ (2 * d) = c) ∧
    Nat.card (fixSubfield κ) = 2 ^ (2 * d) ∧
    subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧
    orderOf (fieldActor (t := TwistTag.E6) σ ε) = m ∧
    ⁅MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))⁆ =
      (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∧
    IsSimpleGroup (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) ∧
    (¬∀ a b : subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀, a * b = b * a) ∧
    (∃ ι : ↥((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ≃*
        ↥(subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀),
      ∀ j, (ι j : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) =
        MulAut.conj (j : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ∧
    subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀ ≤
      Subgroup.centralizer {fieldActor σ ε} ∧
    ((subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀).subgroupOf
      (Subgroup.centralizer {fieldActor σ ε})).Normal ∧
    Subgroup.centralizer {fieldActor σ ε} ⊓
        Subgroup.centralizer (subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀ :
          Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) =
      Subgroup.zpowers (fieldActor σ ε) ∧
    Nat.card (Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε)) = m

theorem twistedE6_descent {T : Type} [Group T] [Finite T] {p f₀ : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) (hM : LieModel T .twistedE6 0 2 (p * f₀)) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ κ ε : K ≃+* K)
      (σ₀ : fixSubfield κ ≃+* fixSubfield κ) (φ : T ≃* twistedE6RootGroup K σ),
      Nat.card K = 2 ^ (2 * f₀ * p) ∧ (∀ c, σ c = c ^ 2 ^ (f₀ * p)) ∧
      (∀ c, κ c = c ^ 2 ^ (2 * f₀)) ∧ (∀ c, ε c = c ^ 2 ^ (f₀ * (p + 1))) ∧
      (∀ c : fixSubfield κ, (σ₀ c : K) = (c : K) ^ 2 ^ f₀) ∧
      (∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧
        MulAut.congr φ α = fieldActor (t := TwistTag.E6) σ ε ^ s) ∧
      fixSub (MulAut.congr φ α) = fixSub (fieldActor (t := TwistTag.E6) σ ε) ∧
      TwistedE6Canon f₀ p K κ σ σ₀ ε ∧
      (∀ q : ℕ, q.Prime → q ≠ 3 → ∀ x ∈ fixSub (fieldActor (t := TwistTag.E6) σ ε),
        (∃ k : ℕ, orderOf x = q ^ k) →
        (x : ModGL TwistTag.E6.tag K) ∈ subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) ∧
      Nonempty (↥(subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) ≃*
        twistedE6RootGroup (fixSubfield κ) σ₀) ∧
      LieModel (twistedE6RootGroup (fixSubfield κ) σ₀) .twistedE6 0 2 f₀ := by
  classical
  obtain ⟨-, hCEM⟩ := lieModel_twistedE6_iff.mp hM
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hCEM
  have hK2 : Nat.card K = 2 ^ (2 * (p * f₀)) := by rw [hKcard, ← pow_mul, mul_comm]
  have : Finite (twistedE6RootGroup K σ) := Finite.of_equiv T e.toEquiv
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (twistedE6RootGroup K σ) := MulAut.congr e α with hα'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hKcard σ hσ
  obtain ⟨hηord, hpf, ⟨ψ, hψ⟩, -⟩ :=
    twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK2 σ
      hσ Θ hΘ hp (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hf'f₀ : f' = f₀ := (Nat.eq_of_mul_eq_mul_left hp.pos hff').symm
  have hd : 1 ≤ f' := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ε, hε, hzp⟩ := exists_canonical_generator_odd hf hK2 hηord hp hp2 hff'
  have hK' : Nat.card K = 2 ^ (2 * f' * p) := by rw [hK2, hff']; ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
  obtain ⟨φ, hφ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * (p * f₀)) hK2
  obtain ⟨κ, hκdef⟩ : ∃ κ, φ ^ (2 * f') = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ 2 ^ (2 * f') := fun c => by
    rw [← hκdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  obtain ⟨T₁, hTdef⟩ : ∃ T₁, φ ^ f' = T₁ := ⟨_, rfl⟩
  have hT : ∀ c, T₁ c = c ^ 2 ^ f' := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  set σ₀ : fixSubfield κ ≃+* fixSubfield κ := fixSubfieldRestrict T₁ κ with hσ₀def
  have hσ₀ : ∀ c : fixSubfield κ, (σ₀ c : K) = (c : K) ^ 2 ^ f' := fun c => by
    rw [hσ₀def, coe_fixSubfieldRestrict, hT]
  have hcanon : TwistedE6Canon f' p K κ σ σ₀ ε :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_two hd
      (by omega : 3 ≤ p) (hp.odd_of_ne_two hp2) K hK' κ hκ σ hσ' σ₀ hσ₀ ε hε
  obtain ⟨-, hk, -, hεord, -⟩ := id hcanon
  have : Finite (fixSubfield κ) := Subtype.finite
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ with hJ
  set φ' : T ≃* twistedE6RootGroup K σ := e.trans ψ with hφ'
  have hφα : MulAut.congr φ' α = ψ * MulAut.congr e α * ψ⁻¹ := rfl
  have h1 : ψ * MulAut.congr e α * ψ⁻¹ = fieldActor σ (Θ α') := hψ
  obtain ⟨s, hs⟩ : ∃ s : ℤ, ε ^ s = Θ α' :=
    Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_zpowers _)
  have hcongr : MulAut.congr φ' α = fieldActor (t := TwistTag.E6) σ ε ^ s := by
    rw [hφα, h1, ← hs]
    exact map_zpow (fieldActorHom (t := TwistTag.E6) σ) ε s
  have hs' : ¬ (p : ℤ) ∣ s := by
    intro hdvd
    have h2 : fieldActor (t := TwistTag.E6) σ ε ^ s = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hεord]; exact hdvd)
    have h3 : α = 1 := (MulEquiv.map_eq_one_iff (MulAut.congr φ')).mp (hcongr.trans h2)
    exact hαinn (h3 ▸ (innerAut T).one_mem)
  have hfix_eq : fixSub (MulAut.congr φ' α) = fixSub (fieldActor (t := TwistTag.E6) σ ε) := by
    rw [hφα, h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (fieldActorHom (t := TwistTag.E6) σ)) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hψpow : ∀ c, (σ * ε) c = c ^ 2 ^ f' := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ (2 * f' * p) := by
      rw [← Nat.card_eq_fintype_card, hK']
    have h1 : c ^ (2 ^ (2 * f' * p)) = c := by
      have := FiniteField.pow_card c
      rwa [hcard] at this
    rw [RingAut.mul_apply, hε, hσ', ← pow_mul, show 2 ^ (f' * (p + 1)) * 2 ^ (f' * p) =
      2 ^ (2 * f' * p) * 2 ^ f' by rw [← pow_add, ← pow_add]; congr 1; ring, pow_mul, h1]
  have hK0 : Nat.card (fixSubfield κ) = (2 ^ f') ^ 2 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ 2 ^ f' := fun c => Subtype.ext (by
    rw [hσ₀, SubmonoidClass.coe_pow])
  have hPq : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ x ∈ fixSub (fieldActor (t := TwistTag.E6) σ ε),
      (∃ k : ℕ, orderOf x = q ^ k) → (x : ModGL TwistTag.E6.tag K) ∈ J := by
    intro q hq hq3 x hx ⟨j, hj⟩
    have hδx : Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x := by
      have h := congrArg Subtype.val (mem_fixSub.mp hx)
      rwa [coe_fieldActor] at h
    have hxψ : (x : ModGL TwistTag.E6.tag K) ∈
        twistedFixedGroup TwistTag.E6 K (σ * ε).toRingHom := by
      obtain ⟨hxA, hxσ⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
        (graphFixedRootGroup_le _ _ _ x.2)
      refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (σ * ε).toRingHom).2
        ⟨hxA, ?_⟩
      rw [twistHom_apply] at hxσ ⊢
      rw [show (σ * ε).toRingHom = σ.toRingHom.comp ε.toRingHom from RingHom.ext fun _ => rfl,
        ← units_map_entrywiseHom_comp, hδx]
      exact hxσ
    exact twistedE6_pElement_mem_subfield Nat.prime_two hd (fixSubfield κ) hK0 σ₀ hσ₀ (σ * ε)
      hψpow hq hq3 hxψ ⟨j, by rw [Subgroup.orderOf_coe, hj]⟩
  have hZk : Subgroup.center (twistedE6RootGroup (fixSubfield κ) σ₀) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 (fixSubfield κ) σ₀
  let eJ : ↥J ≃* twistedE6RootGroup (fixSubfield κ) σ₀ :=
    (Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom)
      (baseChangeGL (fixSubfield κ).subtype) (baseChangeGL_injective _)).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eDQ⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hd (fixSubfield κ)
      hK0 σ₀ hσ₀'
  have hXmodel : LieModel (twistedE6RootGroup (fixSubfield κ) σ₀) .twistedE6 0 2 f' :=
    lieModel_twistedE6_iff.mpr ⟨rfl, ⟨Nat.prime_two, hd, rfl⟩, fixSubfield κ, inferInstance,
      inferInstance, hK0, σ₀.toRingHom, hσ₀', ⟨eDQ.symm⟩⟩
  subst hf'f₀
  exact ⟨K, hKf, hKfin, σ, κ, ε, σ₀, φ', hK', hσ', hκ, hε, hσ₀, ⟨s, hs', hcongr⟩, hfix_eq,
    hcanon, hPq, ⟨eJ⟩, hXmodel⟩

end

end CFSG.RankThree.PartOne.FieldFix
