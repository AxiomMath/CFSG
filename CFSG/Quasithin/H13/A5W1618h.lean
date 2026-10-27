module

public import CFSG.Quasithin.H13.A5S136oa
public import CFSG.Quasithin.H13.A5W1618a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

section Averaging

variable {Γ A : Type*} [Group Γ] [Finite Γ] [CommGroup A]

theorem exists_coboundary_mod_of_odd_index (hA : ∀ x : A, x ^ 2 = 1) (ρ : Γ →* MulAut A)
    (δ : Γ → A) (hδ : ∀ g h, δ (g * h) = ρ h⁻¹ (δ g) * δ h) (Z₀ : Subgroup A)
    (hZ₀ : ∀ g, ∀ z ∈ Z₀, ρ g z = z) (D : Subgroup Γ) (hD : ∀ d ∈ D, δ d ∈ Z₀)
    (hodd : ¬ 2 ∣ D.index) :
    ∃ m : A, ∀ g, (ρ g⁻¹ m * m⁻¹)⁻¹ * δ g ∈ Z₀ := by
  classical
  have : Fintype (Γ ⧸ D) := Fintype.ofFinite _
  set π : A →* A ⧸ Z₀ := QuotientGroup.mk' Z₀ with hπ
  set η : Γ → A := fun x => δ x⁻¹ with hη
  have hηmul : ∀ g x, η (g * x) = ρ g (η x) * δ g⁻¹ := by
    intro g x
    show δ (g * x)⁻¹ = ρ g (δ x⁻¹) * δ g⁻¹
    rw [mul_inv_rev, hδ, inv_inv]
  have hηD : ∀ x, ∀ d ∈ D, π (η (x * d)) = π (η x) := by
    intro x d hd
    show π (δ (x * d)⁻¹) = π (δ x⁻¹)
    have hd' : δ d⁻¹ ∈ Z₀ := hD _ (D.inv_mem hd)
    rw [mul_inv_rev, hδ, inv_inv, map_mul, hZ₀ x _ hd']
    have h1 : π (δ d⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hd'
    rw [h1, one_mul]
  set P : A := ∏ q : Γ ⧸ D, η q.out with hP
  have hcard : Fintype.card (Γ ⧸ D) = D.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hpow : ∀ x : A, x ^ D.index = x := by
    intro x
    obtain ⟨k, hk⟩ := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    rw [hk, pow_succ, pow_mul, hA, one_pow, one_mul]
  have key : ∀ g, π P = π (ρ g P) * π (δ g⁻¹) := by
    intro g
    have h1 : ∀ q : Γ ⧸ D, π (η (g • q).out) = π (ρ g (η q.out)) * π (δ g⁻¹) := by
      intro q
      have hq : ((g * q.out : Γ) : Γ ⧸ D) = (((g • q).out : Γ) : Γ ⧸ D) := by
        rw [QuotientGroup.out_eq']
        exact MulAction.Quotient.mk_smul_out D g q
      have hd := QuotientGroup.eq.mp hq
      have he : (g • q).out = (g * q.out) * ((g * q.out)⁻¹ * (g • q).out) := by
        rw [mul_inv_cancel_left]
      rw [he, hηD _ _ hd, hηmul, map_mul]
    have h2 : π P = ∏ q : Γ ⧸ D, π (η (g • q).out) := by
      rw [hP, map_prod]
      exact (Equiv.prod_comp (MulAction.toPerm g) (fun q : Γ ⧸ D => π (η q.out))).symm
    rw [h2, Finset.prod_congr rfl (fun q _ => h1 q), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, hcard, ← map_pow, hpow, ← map_prod, ← map_prod]
  refine ⟨P⁻¹, fun g => ?_⟩
  rw [← QuotientGroup.eq]
  have h := key g⁻¹
  rw [inv_inv] at h
  show π (ρ g⁻¹ P⁻¹ * P⁻¹⁻¹) = π (δ g)
  rw [map_inv, inv_inv, map_mul, map_inv, h]
  group

theorem exists_coboundary_of_odd_index (hA : ∀ x : A, x ^ 2 = 1) (ρ : Γ →* MulAut A)
    (δ : Γ → A) (hδ : ∀ g h, δ (g * h) = ρ h⁻¹ (δ g) * δ h) (Z₀ : Subgroup A)
    (hZ₀ : ∀ g, ∀ z ∈ Z₀, ρ g z = z) (D : Subgroup Γ) (hD : ∀ d ∈ D, δ d ∈ Z₀)
    (hodd : ¬ 2 ∣ D.index) (hperf : commutator Γ = ⊤) :
    ∃ m : A, ∀ g, δ g = ρ g⁻¹ m * m⁻¹ := by
  obtain ⟨m, hm⟩ := exists_coboundary_mod_of_odd_index hA ρ δ hδ Z₀ hZ₀ D hD hodd
  have hδ1 : δ 1 = 1 := by
    have h := hδ 1 1
    rw [mul_one, inv_one, map_one, MulAut.one_apply] at h
    exact mul_eq_left.mp h.symm
  let ε : Γ →* A :=
    { toFun := fun g => (ρ g⁻¹ m * m⁻¹)⁻¹ * δ g
      map_one' := by
        simp only [inv_one, map_one, MulAut.one_apply, mul_inv_cancel, inv_one, hδ1, mul_one]
      map_mul' := fun g h => by
        have hfix := hZ₀ h⁻¹ _ (hm g)
        conv_rhs => rw [← hfix]
        rw [hδ, show (g * h)⁻¹ = h⁻¹ * g⁻¹ from mul_inv_rev g h, map_mul ρ, MulAut.mul_apply]
        simp only [map_mul, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel }
  have hε : ∀ g, ε g = 1 := fun g =>
    (Abelianization.commutator_subset_ker ε) (hperf ▸ Subgroup.mem_top g)
  exact ⟨m, fun g => (inv_mul_eq_one.mp (hε g)).symm⟩

end Averaging

theorem card_filter_comm_alt_five_lt : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 →
    ((Finset.univ : Finset (Equiv.Perm (Fin 5))).filter
      (fun g => g ∈ alternatingGroup (Fin 5) ∧ σ * g = g * σ)).card < 12 := by
  decide +kernel

theorem eq_of_mulAut_alt_five_of_fix
    {ψ : ↥(alternatingGroup (Fin 5)) ≃* ↥(alternatingGroup (Fin 5))}
    {H : Subgroup ↥(alternatingGroup (Fin 5))} (h4 : 4 ∣ Nat.card H) (h3 : 3 ∣ Nat.card H)
    (hfix : ∀ x ∈ H, ψ x = x) (x : ↥(alternatingGroup (Fin 5))) : ψ x = x := by
  classical
  obtain ⟨σ, hσ⟩ := CFSG.QuasithinUnique.A5.Delta5.aut_inner ψ
  by_cases h1 : σ = 1
  · apply Subtype.ext
    rw [hσ, h1, one_mul, inv_one, mul_one]
  · exfalso
    have hc : ∀ h ∈ H, σ * ((h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        ((h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * σ := by
      intro h hh
      have e := hσ h
      rw [hfix h hh] at e
      calc σ * ((h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          = σ * ((h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * σ⁻¹ * σ := by group
        _ = ((h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * σ := by rw [← e]
    have hle : Nat.card H ≤ ((Finset.univ : Finset (Equiv.Perm (Fin 5))).filter
        (fun g => g ∈ alternatingGroup (Fin 5) ∧ σ * g = g * σ)).card := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      refine Finset.card_le_card_of_injOn
        (fun h : ↥H => ((h : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))) ?_ ?_
      · intro h _
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        exact ⟨(h : ↥(alternatingGroup (Fin 5))).2, hc h h.2⟩
      · intro a _ b _ hab
        exact Subtype.ext (Subtype.ext hab)
    have h12 : 12 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
    have hpos : 0 < Nat.card H := Nat.card_pos
    have h12' := Nat.le_of_dvd hpos h12
    have := card_filter_comm_alt_five_lt σ h1
    omega

theorem eq_zero_of_mulVec_eq_of_pow_three {F : Type} [Field F] [CharP F 2]
    {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1) (h3 : M ^ 3 = 1) (h1 : M ≠ 1)
    {x : Fin 2 → F} (hx : M.mulVec x = x) : x = 0 := by
  have ht := trace_eq_one_of_pow_three hdet h3 h1
  have hsq := mul_self_eq_of_det hdet
  rw [ht, one_smul] at hsq
  have h2 : (M * M).mulVec x = x := by rw [← Matrix.mulVec_mulVec, hx, hx]
  rw [hsq, Matrix.add_mulVec, Matrix.one_mulVec, hx] at h2
  have h0 : x + x = 0 := funext fun i => CharTwo.add_self_eq_zero (x i)
  rw [h0] at h2
  exact h2.symm

theorem pact_sq_Wa : ∀ σ : Equiv.Perm (Fin 5), pact σ E12 = E12 → pact (σ * σ) Wa = Wa := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem sq_conj_a {g : G} (hgN : g ∈ Subgroup.normalizer (V : Set G))
    (hgv : g ∈ Subgroup.centralizer ({S.v12} : Set G)) : g ^ 2 * S.a * (g ^ 2)⁻¹ = S.a := by
  have hfix : pact (S.frame.ρ ⟨g, hgN⟩) E12 = E12 := by
    have h1 : g * S.v12 * g⁻¹ = S.v12 := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hgv]
      group
    have h2 := (S.conj_eq_iff ⟨g, hgN⟩ ⟨S.v12, S.v12_mem_V⟩).1 h1
    rwa [S.psi_v12] at h2
  have h := (S.conj_eq_iff (⟨g, hgN⟩ ^ 2) ⟨S.a, S.a_mem_V⟩).2 (by
    rw [S.psi_a, map_pow, pow_two]
    exact pact_sq_Wa _ hfix)
  simpa using h

end Setting

end CFSG.Quasithin.H13.A5
