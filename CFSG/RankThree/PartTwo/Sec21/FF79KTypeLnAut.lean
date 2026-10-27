module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Matrix Hering214 CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem embedTwo_bijective {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {n : ℕ} (hn : n = 4 ∨ n = 5) : Function.Bijective (embedTwo K n) := by
  have hinj := embedTwo_injective hK (n := n) (by omega)
  have h1 : Nat.card (SpecialLinearGroup (Fin n) (ZMod 2)) = Nat.card (projectiveSL n K) := by
    rw [card_projectiveSL, scalars_eq_bot_of_natCard_eq_two hK (by omega), Subgroup.card_bot,
      Nat.div_one]
    rcases hn with rfl | rfl
    · rw [card_specialLinearGroup_four hK, card_specialLinearGroup_four (K := ZMod 2)
        (Nat.card_zmod 2)]
    · rw [card_specialLinearGroup_five hK, card_specialLinearGroup_five (K := ZMod 2)
        (Nat.card_zmod 2)]
  exact (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, h1⟩


section AutForm

variable {n : ℕ}

noncomputable def eTwo (hn : n = 4 ∨ n = 5) :
    SpecialLinearGroup (Fin n) (ZMod 2) ≃* projectiveSL n (ZMod 2) :=
  MulEquiv.ofBijective (embedTwo (ZMod 2) n) (embedTwo_bijective (Nat.card_zmod 2) hn)

theorem eTwo_apply (hn : n = 4 ∨ n = 5) (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    eTwo hn g = proj n (ZMod 2) g := by
  show proj n (ZMod 2) (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) (ZMod 2)) g) = _
  congr 1
  exact Matrix.SpecialLinearGroup.ext _ _ fun a b => by simp

noncomputable def deltaS (hn : n = 4 ∨ n = 5) : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) :=
  MulAut.congr (eTwo hn).symm (dualAut n (ZMod 2))

theorem deltaS_apply (hn : n = 4 ∨ n = 5) {x : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : ((x⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      ((x⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) :
    deltaS hn x = x⁻¹ := by
  have h1 : dualAut n (ZMod 2) (eTwo hn x) = eTwo hn x⁻¹ := by
    rw [eTwo_apply, eTwo_apply, dualAut_proj]
    congr 1
    exact Matrix.SpecialLinearGroup.ext _ _ fun a b => by
      have := congrFun (congrFun hx b) a
      simpa [Matrix.SpecialLinearGroup.coe_transpose] using this.symm
  show (eTwo hn).symm (dualAut n (ZMod 2) (eTwo hn x)) = x⁻¹
  rw [h1, MulEquiv.symm_apply_apply]

theorem deltaS_coe (hn : n = 4 ∨ n = 5) (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    ((deltaS hn g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
  have h1 : dualAut n (ZMod 2) (eTwo hn g) = eTwo hn (g⁻¹).transpose := by
    rw [eTwo_apply, eTwo_apply, dualAut_proj]
  have h2 : deltaS hn g = (g⁻¹).transpose := by
    show (eTwo hn).symm (dualAut n (ZMod 2) (eTwo hn g)) = _
    rw [h1, MulEquiv.symm_apply_apply]
  rw [h2, SpecialLinearGroup.coe_transpose]

theorem congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (y : G) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem autForm (hn : n = 4 ∨ n = 5) (α : MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) :
    ∃ s0 : SpecialLinearGroup (Fin n) (ZMod 2), ∃ ε : ℕ, ε ≤ 1 ∧
      α = MulAut.conj s0 * deltaS hn ^ ε := by
  have hn3 : 3 ≤ n := by omega
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨-, hgen⟩ := automorphism_generation (K := ZMod 2) hn3
  obtain ⟨A, σ, ε, hε, hβ⟩ := hgen (MulAut.congr (eTwo hn) α)
  have hσ1 : fieldAut n (ZMod 2) σ = 1 := by
    rw [ringEquiv_eq_one_of_natCard_eq_two hK σ, map_one]
  rw [hσ1, mul_one] at hβ
  obtain ⟨y, hy⟩ := conjAut_mem_range_conj_of_det_eq_pow (A := A) (μ := 1)
    (by rw [det_eq_one_of_natCard_eq_two hK A, one_pow])
  refine ⟨(eTwo hn).symm y, ε, hε, ?_⟩
  have hα : α = MulAut.congr (eTwo hn).symm (MulAut.congr (eTwo hn) α) := by
    ext x; simp [MulAut.congr_apply]
  rw [hα, hβ, ← hy, map_mul, map_pow, congr_conj, deltaS]

end AutForm


section Model

variable {S : Type} [Group S]

structure TModel (S : Type) [Group S] (R : Subgroup S) : Prop where
  cube : ∀ x ∈ R, x ^ 3 = 1
  comm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  card : Nat.card R = 9
  tau : ∃ τ ∈ Subgroup.normalizer (R : Set S), ∀ x ∈ R, τ * x * τ⁻¹ = x⁻¹
  count : {f : R → S | ∃ j ∈ Subgroup.normalizer (R : Set S),
    ∀ x : R, f x = j * x * j⁻¹}.ncard = 8
  noncomm : ∃ x ∈ R, ∃ j₁ ∈ Subgroup.normalizer (R : Set S),
    ∃ j₂ ∈ Subgroup.normalizer (R : Set S),
      j₁ * (j₂ * x * j₂⁻¹) * j₁⁻¹ ≠ j₂ * (j₁ * x * j₁⁻¹) * j₂⁻¹
  cent : ∀ s : S, (∀ x ∈ R, s * x = x * s) → s ∈ R
  aute : ∀ α : MulAut S, (∀ x ∈ R, α x ∈ R) →
    ∃ j ∈ Subgroup.normalizer (R : Set S), ∀ x ∈ R, α x = j * x * j⁻¹
  autf : ∃ γ : MulAut S, (∀ x ∈ R, γ x = x) ∧ ∀ α : MulAut S, (∀ x ∈ R, α x = x) →
    ∃ p ∈ R, α = MulAut.conj p ∨ α = MulAut.conj p * γ

theorem hconj_of_trace {a b : S} (D : E9Data a b) {T : Type} (tr : S → T)
    (hconj : ∀ s x, tr (s * x * s⁻¹) = tr x) (hba : tr b = tr a)
    (hcls : ∀ i j : Fin 3, tr (a ^ (i : ℕ) * b ^ (j : ℕ)) = tr a →
      ((i = 1 ∨ i = 2) ∧ j = 0) ∨ (i = 0 ∧ (j = 1 ∨ j = 2))) :
    ∀ s ∈ Subgroup.normalizer (R a b : Set S),
      InBlocks a b (MulAut.conj s a) ∧ InBlocks a b (MulAut.conj s b) := by
  have key : ∀ s ∈ Subgroup.normalizer (R a b : Set S), ∀ x, x ∈ R a b → tr x = tr a →
      InBlocks a b (MulAut.conj s x) := by
    intro s hs x hx htx
    have hmem : s * x * s⁻¹ ∈ R a b := (Subgroup.mem_normalizer_iff.mp hs x).mp hx
    obtain ⟨i, j, hij⟩ := D.mem_R_iff.mp hmem
    have htr : tr (a ^ (i : ℕ) * b ^ (j : ℕ)) = tr a := by
      rw [← hij, hconj, htx]
    show InBlocks a b (s * x * s⁻¹)
    rw [hij]
    unfold InBlocks
    rcases hcls i j htr with ⟨hi | hi, hj⟩ | ⟨hi, hj | hj⟩ <;> subst_vars <;> simp
  intro s hs
  exact ⟨key s hs a D.a_mem rfl, key s hs b D.b_mem hba⟩


theorem TModel.of_data [Finite S] {a b r₁ r₂ w : S} (D : NormData a b r₁ r₂ w)
    (hconj : ∀ s ∈ Subgroup.normalizer (R a b : Set S),
      InBlocks a b (MulAut.conj s a) ∧ InBlocks a b (MulAut.conj s b))
    (hcent : ∀ s : S, s * a = a * s → s * b = b * s → ∃ i j : Fin 3,
      s = a ^ (i : ℕ) * b ^ (j : ℕ))
    (δ : MulAut S) (hδ : ∀ x ∈ R a b, δ x = x⁻¹)
    (hform : ∀ α : MulAut S, ∃ s₀ : S, ∃ ε : ℕ, ε ≤ 1 ∧ α = MulAut.conj s₀ * δ ^ ε) :
    TModel S (R a b) := by
  have E := D.toE9Data
  have hinvmem : ∀ x ∈ R a b, x⁻¹ ∈ R a b := fun x hx => inv_mem hx
  have hcentR : ∀ s : S, (∀ x ∈ R a b, s * x = x * s) → s ∈ R a b := by
    intro s hs
    obtain ⟨i, j, rfl⟩ := hcent s (hs a E.a_mem) (hs b E.b_mem)
    exact E.mem_R_iff.mpr ⟨i, j, rfl⟩
  obtain ⟨τ, hτN, hτ⟩ : ∃ τ ∈ Subgroup.normalizer (R a b : Set S),
      ∀ x ∈ R a b, τ * x * τ⁻¹ = x⁻¹ := ⟨r₁ * r₂, D.tau_mem, fun x hx => D.tau_inv hx⟩
  have hτ' : ∀ x ∈ R a b, τ⁻¹ * x * τ = x⁻¹ := by
    intro x hx
    have := hτ x⁻¹ (hinvmem x hx)
    rw [inv_inv] at this
    calc τ⁻¹ * x * τ = τ⁻¹ * (τ * x⁻¹ * τ⁻¹) * τ := by rw [this]
      _ = x⁻¹ := by group
  refine ⟨fun x hx => E.cube_R hx, fun x hx y hy => E.comm_R hx hy, E.card_R, ⟨τ, hτN, hτ⟩,
    D.ncard_conj hconj, ?_, hcentR, ?_, ?_⟩
  · obtain ⟨x, hx, hne⟩ := D.noncomm
    exact ⟨x, hx, r₁, by simpa [jk] using D.jk_mem 1, w, by simpa [jk] using D.jk_mem 4, hne⟩
  · intro α hα
    obtain ⟨s₀, ε, hε, hαe⟩ := hform α
    have hmem : ∀ x ∈ R a b, α x ∈ R a b := hα
    interval_cases ε
    · have hαx : ∀ x, α x = s₀ * x * s₀⁻¹ := fun x => by
        rw [hαe]; simp [MulAut.conj_apply]
      refine ⟨s₀, mem_normalizer_of_forall_conj_mem fun x hx => ?_, fun x _ => hαx x⟩
      rw [← hαx]; exact hmem x hx
    · have hαx : ∀ x ∈ R a b, α x = s₀ * x⁻¹ * s₀⁻¹ := fun x hx => by
        rw [hαe]; simp [MulAut.conj_apply, hδ x hx]
      have hs₀ : s₀ ∈ Subgroup.normalizer (R a b : Set S) :=
        mem_normalizer_of_forall_conj_mem fun x hx => by
          have := hmem x⁻¹ (hinvmem x hx)
          rwa [hαx x⁻¹ (hinvmem x hx), inv_inv] at this
      refine ⟨s₀ * τ, mul_mem hs₀ hτN, fun x hx => ?_⟩
      rw [hαx x hx]
      calc s₀ * x⁻¹ * s₀⁻¹ = s₀ * (τ * x * τ⁻¹) * s₀⁻¹ := by rw [hτ x hx]
        _ = s₀ * τ * x * (s₀ * τ)⁻¹ := by group
  · refine ⟨MulAut.conj τ * δ, fun x hx => ?_, fun α hα => ?_⟩
    · simp only [MulAut.mul_apply, hδ x hx, MulAut.conj_apply]
      have := hτ x⁻¹ (hinvmem x hx)
      rw [inv_inv] at this
      exact this
    · obtain ⟨s₀, ε, hε, hαe⟩ := hform α
      interval_cases ε
      · have hαx : ∀ x, α x = s₀ * x * s₀⁻¹ := fun x => by
          rw [hαe]; simp [MulAut.conj_apply]
        refine ⟨s₀, hcentR s₀ fun x hx => ?_, Or.inl (by rw [hαe]; simp)⟩
        have := hα x hx
        rw [hαx] at this
        exact (mul_inv_eq_iff_eq_mul.mp this)
      · have hαx : ∀ x ∈ R a b, α x = s₀ * x⁻¹ * s₀⁻¹ := fun x hx => by
          rw [hαe]; simp [MulAut.conj_apply, hδ x hx]
        have hinv₀ : ∀ x ∈ R a b, s₀ * x * s₀⁻¹ = x⁻¹ := by
          intro x hx
          have := hα x⁻¹ (hinvmem x hx)
          rw [hαx x⁻¹ (hinvmem x hx), inv_inv] at this
          exact this
        have hp : s₀ * τ⁻¹ ∈ R a b := by
          refine hcentR _ fun x hx => ?_
          have h1 : s₀ * τ⁻¹ * x = (s₀ * τ⁻¹ * x * τ * s₀⁻¹) * (s₀ * τ⁻¹) := by group
          have h2 : s₀ * τ⁻¹ * x * τ * s₀⁻¹ = x := by
            calc s₀ * τ⁻¹ * x * τ * s₀⁻¹ = s₀ * (τ⁻¹ * x * τ) * s₀⁻¹ := by group
              _ = s₀ * x⁻¹ * s₀⁻¹ := by rw [hτ' x hx]
              _ = x := by rw [hinv₀ x⁻¹ (hinvmem x hx), inv_inv]
          rw [h1, h2]
        refine ⟨s₀ * τ⁻¹, hp, Or.inr ?_⟩
        rw [hαe]
        have : (MulAut.conj s₀ : MulAut S) = MulAut.conj (s₀ * τ⁻¹) * MulAut.conj τ := by
          rw [← map_mul]; congr 1; group
        rw [pow_one, this, mul_assoc]


theorem trace_conj_sl {n : ℕ} (s x : SpecialLinearGroup (Fin n) (ZMod 2)) :
    ((s * x * s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).trace =
      (x : Matrix (Fin n) (Fin n) (ZMod 2)).trace := by
  have h : ((s * x * s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) =
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) * (x : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    simp [Matrix.SpecialLinearGroup.coe_mul]
  have h2 : ((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  rw [h, Matrix.trace_mul_cycle, h2, one_mul]

theorem sym_R {n : ℕ} {a b : SpecialLinearGroup (Fin n) (ZMod 2)} (D : E9Data a b)
    (hsym : ∀ i j : Fin 3, ((a ^ (i : ℕ) * b ^ (j : ℕ) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      ((a ^ (i : ℕ) * b ^ (j : ℕ) : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))) {x : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : x ∈ R a b) :
    ((x : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = x := by
  obtain ⟨i, j, rfl⟩ := D.mem_R_iff.mp hx
  exact hsym i j

theorem tModel4 : TModel (SpecialLinearGroup (Fin 4) (ZMod 2)) (R sA4 sB4) :=
  TModel.of_data normData4
    (hconj_of_trace normData4.toE9Data (fun g => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).trace)
      trace_conj_sl trace4' trace4)
    cent4_sl (deltaS (Or.inl rfl))
    (fun x hx => deltaS_apply _ (sym_R normData4.toE9Data sym4 (inv_mem hx)))
    (autForm (Or.inl rfl))

theorem tModel5 : TModel (SpecialLinearGroup (Fin 5) (ZMod 2)) (R sA5 sB5) :=
  TModel.of_data normData5
    (hconj_of_trace normData5.toE9Data (fun g => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).trace)
      trace_conj_sl trace5' trace5)
    cent5_sl (deltaS (Or.inr rfl))
    (fun x hx => deltaS_apply _ (sym_R normData5.toE9Data sym5 (inv_mem hx)))
    (autForm (Or.inr rfl))

theorem card_R_sylow4 : Nat.card (R sA4 sB4) =
    3 ^ (Nat.card (SpecialLinearGroup (Fin 4) (ZMod 2))).factorization 3 := by
  rw [normData4.toE9Data.card_R, card_specialLinearGroup_four (Nat.card_zmod 2),
    Nat.factorization_def _ Nat.prime_three]
  have : padicValNat 3 20160 = 2 := by decide +kernel
  rw [this]
  norm_num

theorem card_R_sylow5 : Nat.card (R sA5 sB5) =
    3 ^ (Nat.card (SpecialLinearGroup (Fin 5) (ZMod 2))).factorization 3 := by
  rw [normData5.toE9Data.card_R, card_specialLinearGroup_five (Nat.card_zmod 2),
    Nat.factorization_def _ Nat.prime_three]
  have : padicValNat 3 9999360 = 2 := by decide +kernel
  rw [this]
  norm_num

end Model

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
