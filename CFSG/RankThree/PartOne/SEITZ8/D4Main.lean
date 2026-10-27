module

public import CFSG.RankThree.PartOne.SEITZ8.D4Fin
public import CFSG.RankThree.PartOne.SEITZ8.D4Field
import CFSG.RankThree.PartOne.SEITZ8.D4Order
public import CFSG.RankThree.PartOne.SEITZ2.D4Outer

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ2
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)


theorem closure_transport {G H : Type*} [Group G] [Group H] (e : G ≃* H) (A : Subgroup G)
    (B : Subgroup H) (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (g : G)
    (h : Subgroup.closure ((B : Set H) ∪ (B.map (MulAut.conj (e g)).toMonoidHom : Set H)) = ⊤) :
    Subgroup.closure ((A : Set G) ∪ (A.map (MulAut.conj g).toMonoidHom : Set G)) = ⊤ := by
  set T : Subgroup G := Subgroup.closure ((A : Set G) ∪ (A.map (MulAut.conj g).toMonoidHom : Set G))
    with hT
  have hle : Subgroup.closure ((B : Set H) ∪ (B.map (MulAut.conj (e g)).toMonoidHom : Set H)) ≤
      T.map e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y (hy | ⟨b, hb, rfl⟩)
    · refine ⟨e.symm y, Subgroup.subset_closure (Or.inl ?_), by simp⟩
      exact (hAB _).2 (by simpa using hy)
    · have hb' : e.symm b ∈ A := (hAB _).2 (by simpa using hb)
      refine ⟨g * e.symm b * g⁻¹, Subgroup.subset_closure (Or.inr ⟨e.symm b, hb', ?_⟩), ?_⟩
      · simp [MulAut.conj_apply]
      · simp [MulAut.conj_apply]
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ T.map e.toMonoidHom := hle (h ▸ Subgroup.mem_top _)
  obtain ⟨t, ht, hte⟩ := hx
  have : t = x := e.injective hte
  rw [← this]
  exact ht

section Bridge

variable {K : Type} [Field K]

noncomputable def eGamma {σ : K →+* K}
    (hC0 : graphFixedRootGroup TwistTag.D4 K σ = (twistedGroup σ).map (adjointGroup d4 K).subtype) :
    ↥(graphFixedRootGroup TwistTag.D4 K σ) ≃* twistedGroup σ :=
  (MulEquiv.subgroupCongr hC0).trans (Subgroup.equivMapOfInjective _ (adjointGroup d4 K).subtype
    (adjointGroup d4 K).subtype_injective).symm

theorem coe_eGamma {σ : K →+* K}
    (hC0 : graphFixedRootGroup TwistTag.D4 K σ = (twistedGroup σ).map (adjointGroup d4 K).subtype)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ)) :
    (((eGamma hC0 x : twistedGroup σ) : adjointGroup d4 K) : ModGL d4 K) = (x : ModGL d4 K) := by
  have h := (Subgroup.equivMapOfInjective _ (adjointGroup d4 K).subtype
    (adjointGroup d4 K).subtype_injective).apply_symm_apply (MulEquiv.subgroupCongr hC0 x)
  have h2 := congrArg (fun z : ↥((twistedGroup σ).map (adjointGroup d4 K).subtype) =>
    (z : ModGL d4 K)) h
  simp only [Subgroup.coe_equivMapOfInjective_apply] at h2
  exact h2

end Bridge

theorem map_conj_eq_of_mem {G : Type*} [Group G] {A : Subgroup G} {g : G} (hg : g ∈ A) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using A.mul_mem (A.mul_mem hg hx) (A.inv_mem hg)
  · intro hy
    refine ⟨g⁻¹ * y * g, A.mul_mem (A.mul_mem (A.inv_mem hg) hy) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

section Pair

variable {K : Type} [Field K]

theorem stab_of_bridge [Finite K] (σ δ : K ≃+* K)
    (hC0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype)
    (g : twistedGroup σ.toRingHom) :
    ∃ g' : twistedGroup σ.toRingHom, ((g' : adjointGroup d4 K) : ModGL d4 K) =
      Units.map (entrywiseHom δ.toRingHom) ((g : adjointGroup d4 K) : ModGL d4 K) := by
  refine ⟨eGamma hC0 (fieldActor (t := TwistTag.D4) σ δ ((eGamma hC0).symm g)), ?_⟩
  have hx : (((eGamma hC0).symm g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL d4 K) = ((g : adjointGroup d4 K) : ModGL d4 K) := by
    have := coe_eGamma hC0 ((eGamma hC0).symm g)
    rwa [MulEquiv.apply_symm_apply] at this
  rw [coe_eGamma, coe_fieldActor, hx]

theorem mem_fixedSubgroup_iff [Finite K] (σ δ : K ≃+* K)
    (hC0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    x ∈ fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) ↔
      eGamma hC0 x ∈ Rg σ.toRingHom δ.toRingHom := by
  rw [mem_fixedSubgroup, mem_Rg, coe_eGamma]
  constructor
  · intro h
    have := congrArg
      (fun z : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => (z : ModGL d4 K)) h
    exact (coe_fieldActor σ δ x).symm.trans this
  · intro h
    apply Subtype.ext
    rw [coe_fieldActor]
    exact h

variable [Finite K]

theorem pair_big {f0 p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf0 : 2 ≤ f0)
    (hK : Nat.card K = (2 ^ (f0 * p)) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ (f0 * p))
    {δ : K ≃+* K} (hδ : ∀ c, δ c = c ^ 2 ^ (3 * f0))
    (g : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hne : (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map
        (MulAut.conj g).toMonoidHom ≠ fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) :
    Subgroup.closure ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∪
      ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map (MulAut.conj g).toMonoidHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = ⊤ := by
  have hK' : Nat.card K = 2 ^ (3 * f0 * p) := by
    rw [hK, ← pow_mul]
    congr 1
    ring
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3 * f0 * p) (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega))
    hK'
  obtain ⟨k, F0, hfix, hrat, hF0, hcard, hfour, hspan⟩ := field_data hp hp5 hf0 hK' hσ hδ
  have hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ (f0 * p)) := hσ
  have hq2 : 2 ≤ 2 ^ (f0 * p) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (f0 * p) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hσ3 : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c := sigma_three_of_card hK hσq
  have hC0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =
      (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype :=
    (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two (f := f0 * p) (by nlinarith) K hK
      σ.toRingHom hσq).2.2.1.symm.trans
      (commutator_twistedFixedGroup_eq_map σ.toRingHom hq2 hK hσq)
  have S : D4Setup σ.toRingHom δ.toRingHom k F0 p (2 ^ (f0 * p)) :=
    { hσ3 := hσ3
      hcomm := fun c => by
        show δ (σ c) = σ (δ c)
        rw [hσ, hσ, map_pow]
      hfix := hfix
      rat := hrat
      hF0 := hF0
      prime := hp
      ne2 := by omega
      card := hcard
      four := hfour
      span := hspan
      q2 := hq2
      hKq := hK
      hσq := hσq
      stab := stab_of_bridge σ δ hC0 }
  have hg : eGamma hC0 g ∉ Rg σ.toRingHom δ.toRingHom := fun h =>
    hne (map_conj_eq_of_mem ((mem_fixedSubgroup_iff σ δ hC0 g).2 h))
  exact closure_transport (eGamma hC0) _ _ (mem_fixedSubgroup_iff σ δ hC0) g
    (closure_eq_top S (eGamma hC0 g) hg)

end Pair

section Wrapper

@[expose] def SubfieldPairD4Two : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → (p = 7 ∨ p = 13) → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (2 ^ p) ^ 3 → ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ 2 ^ p) →
      ∀ (δ : K ≃+* K), orderOf δ = p → ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map (MulAut.conj g).toMonoidHom ≠
          fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) →
        Subgroup.closure ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∪
          ((fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)).map (MulAut.conj g).toMonoidHom :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = ⊤


theorem subfieldPairD4_of_two (h2 : SubfieldPairD4Two) : SubfieldPairD4 := by
  intro f hf K _ _ hK σ hσ δ p hp hp5 hδ g hne
  classical
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hf3 : 1 ≤ 3 * f := by omega
  obtain ⟨φ, hφ, hφord, -, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf3 hK3
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpf3 : p ∣ 3 * f := by
    rw [← hδ, ← hcardAut]
    exact orderOf_dvd_natCard δ
  have hpf : p ∣ f := by
    rcases (Nat.Prime.dvd_mul hp).1 hpf3 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
      omega
    · exact h
  obtain ⟨f', hff'⟩ := hpf
  have hf'1 : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h] at hff'
      omega
    · exact h
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ 2 ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers δ = Subgroup.zpowers δc :=
    zpowers_ringEquiv_eq_of_orderOf Nat.prime_two hf3 hK3 hδ hδcord
  have hfix : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) =
      fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) :=
    fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.D4) σ) hzp
  by_cases hf'one : f' = 1
  · have hfp : f = p := by rw [hff', hf'one, mul_one]
    by_cases h713 : p = 7 ∨ p = 13
    · subst hfp
      exact Or.inl (h2 f hp hp5 h713 K hK σ hσ δ hδ g hne)
    · refine Or.inr fun hd => h713 ?_
      subst hf'one
      rw [hfix, card_fixedSubgroup_two hp hp5 (σ := σ) (δ := δc)
        (by rw [hK, hff', ← pow_mul]; congr 1; ring)
        (fun c => by rw [hσ, hff']; ring_nf) hδc] at hd
      exact prime_dvd_ordTrialityD4_two hp hp5 hd
  · have hf'2 : 2 ≤ f' := by omega
    left
    rw [hfix] at hne ⊢
    have hKe : Nat.card K = (2 ^ (f' * p)) ^ 3 := by rw [hK, hff', mul_comm]
    have hσe : ∀ c, σ c = c ^ 2 ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm]
    exact pair_big hp hp5 hf'2 hKe hσe hδc g hne

end Wrapper

end CFSG.RankThree.PartOne.SEITZ8
