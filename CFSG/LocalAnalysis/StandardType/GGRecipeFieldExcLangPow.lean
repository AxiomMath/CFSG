module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem four_le_card_of_ne_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {σ : K ≃+* K} (hσ : σ ≠ 1) : 4 ≤ Nat.card K := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : f = 1 := by omega
    rw [hf1] at hcard
    have : Subsingleton (K ≃+* K) := (Nat.card_eq_one_iff_unique.1 hcard).1
    exact hσ (Subsingleton.elim _ _)
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ.two_le 2
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf2

theorem exists_conj_eq_inndiagFieldAut {ℓ f p : ℕ} [Fact ℓ.Prime] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (x : inndiagGroup τ K) (hx : (MulAut.conj x * inndiagFieldAut τ K σ) ^ p = 1) :
    ∃ g : inndiagGroup τ K, MulAut.conj g * (MulAut.conj x * inndiagFieldAut τ K σ) *
      (MulAut.conj g)⁻¹ = inndiagFieldAut τ K σ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  have hK4 := four_le_card_of_ne_one hℓ hf hK hσ1
  have hpf : p ∣ f := by
    rw [← hσ, ← hcardAut]
    exact orderOf_dvd_natCard σ
  set e := f / p with he
  have hep : e * p = f := Nat.div_mul_cancel hpf
  have he1 : 1 ≤ e := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  set T := φ ^ e with hTdef
  have hT : ∀ c, T c = c ^ (ℓ ^ e) := by
    intro c
    rw [hTdef, ringEquiv_pow_apply]
    have hit : ∀ n : ℕ, (⇑φ)^[n] c = c ^ (ℓ ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, pow_succ, pow_mul]
    exact hit e
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow' φ (by omega), hφord, Nat.gcd_eq_right ⟨p, hep.symm⟩]
    rw [← hep, Nat.mul_div_cancel_left _ (by omega)]
  have hzz : Subgroup.zpowers T = Subgroup.zpowers σ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hTord, hσ])
  obtain ⟨r, hr⟩ : ∃ r : ℕ, σ ^ r = T := by
    have h : T ∈ Subgroup.zpowers σ := hzz ▸ Subgroup.mem_zpowers T
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, T ^ r' = σ := by
    have h : σ ∈ Subgroup.zpowers T := hzz ▸ Subgroup.mem_zpowers σ
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  set Φσ := inndiagFieldAut τ K σ with hΦσ
  set x' := ((List.range r).map fun i => (Φσ ^ i) x).prod with hx'
  have hβr : (MulAut.conj x * Φσ) ^ r = MulAut.conj x' * inndiagFieldAut τ K T := by
    rw [CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, hΦσ, ← map_pow, hr]
  have hβrp : (MulAut.conj x' * inndiagFieldAut τ K T) ^ p = 1 := by
    rw [← hβr, ← pow_mul, mul_comm, pow_mul, hx, one_pow]
  obtain ⟨g, hg⟩ := exists_conj_eq_inndiagFieldAut_frob hK hK4 he1 hp.one_lt.le hep T hT x' hβrp
  have hrr : (MulAut.conj x * Φσ) ^ (r * r') = MulAut.conj x * Φσ := by
    have hσrr : σ ^ (r * r') = σ ^ 1 := by rw [pow_mul, hr, hr', pow_one]
    rw [pow_eq_pow_iff_modEq, hσ] at hσrr
    have hdvd : orderOf (MulAut.conj x * Φσ) ∣ p := orderOf_dvd_of_pow_eq_one hx
    have h2 := Nat.ModEq.of_dvd hdvd hσrr
    rw [← pow_eq_pow_iff_modEq, pow_one] at h2
    exact h2
  refine ⟨g, ?_⟩
  rw [← hrr, pow_mul, hβr, ← conj_pow, hg, ← map_pow, hr']

theorem map_conj_adjointGroup_of_mem_inndiag {w : ModGL τ K} (hw : w ∈ inndiagGroup τ K) :
    (adjointGroup τ K).map (MulAut.conj w).toMonoidHom = adjointGroup τ K := by
  refine le_antisymm ?_ fun h hh => ?_
  · rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_adjointGroup_of_mem_inndiag hw hh
  · refine ⟨w⁻¹ * h * w, ?_, ?_⟩
    · have := conj_mem_adjointGroup_of_mem_inndiag (inv_mem hw) hh
      rwa [inv_inv] at this
    · change w * (w⁻¹ * h * w) * w⁻¹ = h
      group

variable (τ K) in
@[expose] noncomputable def inndiagConj : inndiagGroup τ K →* MulAut (adjointGroup τ K) where
  toFun w := mulAutRestrict (adjointGroup τ K) (MulAut.conj (w : ModGL τ K))
    (map_conj_adjointGroup_of_mem_inndiag w.2)
  map_one' := MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_mulAutRestrict, MulAut.one_apply]
    simp)
  map_mul' v w := MulEquiv.ext fun h => Subtype.ext (by
    rw [MulAut.mul_apply, coe_mulAutRestrict, coe_mulAutRestrict, coe_mulAutRestrict]
    simp [MulAut.conj_apply, mul_assoc])

theorem coe_inndiagConj (w : inndiagGroup τ K) (h : adjointGroup τ K) :
    ((inndiagConj τ K w h : adjointGroup τ K) : ModGL τ K) =
      (w : ModGL τ K) * h * (w : ModGL τ K)⁻¹ :=
  rfl

theorem exists_inndiag_conj_of_pow_fix {ℓ f p : ℕ} [Fact ℓ.Prime] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hinner : ∀ (ρ : K ≃+* K) (v : ModGL τ K), v ∈ inndiagGroup τ K →
      (∀ h ∈ adjointGroup τ K, Units.map (entrywiseHom ρ.toRingHom) h = v * h * v⁻¹) → ρ = 1)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (w : inndiagGroup τ K)
    (hX : ∀ (h : ModGL τ K) (hh : h ∈ adjointGroup τ K),
      ((((MulAut.conj w * inndiagFieldAut τ K σ) ^ p) ⟨h, adjointGroup_le_inndiagGroup hh⟩ :
        inndiagGroup τ K) : ModGL τ K) = h) :
    orderOf σ = p ∧ ∃ g : inndiagGroup τ K,
      MulAut.conj g * (MulAut.conj w * inndiagFieldAut τ K σ) * (MulAut.conj g)⁻¹ =
        inndiagFieldAut τ K σ := by
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have hK4 := four_le_card_of_ne_one hℓ hf hK hσ
  set N := ((List.range p).map fun i => (inndiagFieldAut τ K σ ^ i) w).prod with hN
  have hpow : (MulAut.conj w * inndiagFieldAut τ K σ) ^ p =
      MulAut.conj N * inndiagFieldAut τ K (σ ^ p) := by
    rw [CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, map_pow]
  have hval : ∀ (h : ModGL τ K) (hh : h ∈ adjointGroup τ K), (N : ModGL τ K) *
      ((inndiagFieldAut τ K (σ ^ p) ⟨h, adjointGroup_le_inndiagGroup hh⟩ :
        inndiagGroup τ K) : ModGL τ K) * (N : ModGL τ K)⁻¹ = h := by
    intro h hh
    have := hX h hh
    rwa [hpow, MulAut.mul_apply, MulAut.conj_apply] at this
  have hσp : σ ^ p = 1 := by
    refine hinner _ (N : ModGL τ K)⁻¹ (inv_mem N.2) fun h hh => ?_
    have e1 := hval h hh
    rw [coe_inndiagFieldAut] at e1
    rw [inv_inv]
    calc Units.map (entrywiseHom (σ ^ p).toRingHom) h = (N : ModGL τ K)⁻¹ * ((N : ModGL τ K) *
          Units.map (entrywiseHom (σ ^ p).toRingHom) h * (N : ModGL τ K)⁻¹) *
            (N : ModGL τ K) := by group
      _ = (N : ModGL τ K)⁻¹ * h * (N : ModGL τ K) := by rw [e1]
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ
  have hN1 : N = 1 := by
    refine Subtype.ext (eq_one_of_commute_adjointGroup hK4 N.2 fun h hh => ?_)
    have e1 := hval h hh
    rw [hσp, map_one, MulAut.one_apply] at e1
    calc (N : ModGL τ K) * h = ((N : ModGL τ K) * h * (N : ModGL τ K)⁻¹) * (N : ModGL τ K) := by
          group
      _ = h * (N : ModGL τ K) := by rw [e1]
  have hXp : (MulAut.conj w * inndiagFieldAut τ K σ) ^ p = 1 := by
    rw [hpow, hσp, hN1, map_one, map_one, mul_one]
  exact ⟨hord, exists_conj_eq_inndiagFieldAut hf hK hp σ hord w hXp⟩

end RecipeExcLang

end CFSG.StandardType
