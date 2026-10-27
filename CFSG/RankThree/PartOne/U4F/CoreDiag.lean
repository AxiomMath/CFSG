module

public import CFSG.RankThree.PartOne.U4F.Config
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartOne.U4F

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K]

theorem card_SL_two_lt [Finite K] {F : Type} [Field F] [Finite F] (hF : 2 ≤ Nat.card F)
    (h : Nat.card F < Nat.card K) :
    Nat.card (SpecialLinearGroup (Fin 2) F) < Nat.card (SpecialLinearGroup (Fin 2) K) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have h1 : Nat.card F ^ 2 < Nat.card K ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
  have h2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
  exact Nat.mul_lt_mul'' h (by omega)

variable {σ : K ≃+* K}

theorem sup_eq_top_of_map_conj {A B : Subgroup ↥(SU σ 4)} (g : ↥(SU σ 4))
    (h : A.map (MulAut.conj g).toMonoidHom ⊔ B.map (MulAut.conj g).toMonoidHom = ⊤) :
    A ⊔ B = ⊤ := by
  rw [← Subgroup.map_sup] at h
  rw [eq_top_iff]
  intro x _
  have hx : g * x * g⁻¹ ∈ (A ⊔ B).map (MulAut.conj g).toMonoidHom := by rw [h]; trivial
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := by
    have h' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    simpa using h'
  rwa [this] at hy

theorem map_conj_eq_of_mem {A : Subgroup ↥(SU σ 4)} {g : ↥(SU σ 4)} (hg : g ∈ A) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact A.mul_mem (A.mul_mem hg hx) (A.inv_mem hg)
  · intro y hy
    refine ⟨g⁻¹ * y * g, A.mul_mem (A.mul_mem (A.inv_mem hg) hy) hg, ?_⟩
    show g * (g⁻¹ * y * g) * g⁻¹ = y
    group

theorem piU_conj_mem_torus5 [CharP K 2] {r : ℕ} {g : ↥(SU σ 4)} (hg : g ∈ torus5 σ r) :
    piU σ * g * (piU σ)⁻¹ ∈ torus5 σ r := by
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus5_iff.1 hg
  refine mem_torus5_iff.2 ⟨a, b⁻¹, ha, by rw [inv_pow, hb, inv_one], ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hab, Subgroup.coe_inv, piU_conj_diag]

theorem ne_one_params {γ : ↥(SU σ 4)} {a b : Kˣ} (hγ : (γ : GL (Fin 4) K) = diagU (dvec4 a b))
    (hγ1 : γ ≠ 1) : ¬ (a = 1 ∧ b = 1) := by
  rintro ⟨rfl, rfl⟩
  apply hγ1
  apply Subtype.ext
  rw [hγ]
  have : dvec4 (1 : Kˣ) 1 = 1 := by
    funext i
    fin_cases i <;> simp [dvec4]
  rw [this, diagU_one]
  rfl

theorem closure_pair_le_torus5 {r : ℕ} {ρ τ : ↥(SU σ 4)} (hρ : ρ ∈ torus5 σ r)
    (hτ : τ ∈ torus5 σ r) {γ : ↥(SU σ 4)} (hγ : γ ∈ Subgroup.closure {ρ, τ}) :
    γ ∈ torus5 σ r := by
  refine (Subgroup.closure_le _).2 ?_ hγ
  intro x hx
  rcases hx with rfl | rfl
  · exact hρ
  · exact hτ

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem card_range_suBlockB (hσσ : ∀ x, σ (σ x) = x) :
    Nat.card ↥(suBlockB σ hσσ).range = Nat.card (SpecialLinearGroup (Fin 2) K) :=
  Nat.card_congr (MonoidHom.ofInjective (suBlockB_injective σ hσσ)).toEquiv.symm

omit [Finite K] in
theorem card_range_suBlock :
    Nat.card ↥(suBlock σ).range = Nat.card (SpecialLinearGroup (Fin 2) (fixF σ)) :=
  Nat.card_congr (MonoidHom.ofInjective (suBlock_injective σ)).toEquiv.symm

theorem core_diag_I (hσσ : ∀ x, σ (σ x) = x) (hK4 : 4 ≤ Nat.card K)
    (hF4 : 4 ≤ Nat.card (fixF σ)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hfix : ∀ u : Kˣ, u ^ r = 1 → σ (u : K) = u) (hprim : ∃ ζ : Kˣ, IsPrimitiveRoot ζ r)
    (hgen : (suBlock σ).range ⊔ (suBlockB σ hσσ).range = ⊤)
    {A B : Subgroup ↥(SU σ 4)} {ρ τ : ↥(SU σ 4)} (c : Config σ r A B ρ τ)
    (hρ : ρ ∈ torus5 σ r) (hτ : τ ∈ torus5 σ r) (hA : A = (suBlockB σ hσσ).range) :
    A ⊔ B = ⊤ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨γ, hγ, hγ1, hγc⟩ := c.gamma₂
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus5_iff.1 (closure_pair_le_torus5 hρ hτ hγ)
  have hBn : B ≠ ⊥ := fun h => c.tau_ne (by
    have := c.tau_mem
    rw [h, Subgroup.mem_bot] at this
    exact this)
  rcases perfect_commute_diag σ hσσ hK4 hF4 hr hr2 hfix ha hb (ne_one_params hab hγ1) c.perfB
    hBn hab hγc with ⟨-, hB⟩ | ⟨-, hB⟩ | ⟨-, hB⟩ | ⟨-, hB⟩
  ·
    exfalso
    have hτC : τ ∈ torus5 σ r ⊓ (suBlockB σ hσσ).range := ⟨hτ, hB c.tau_mem⟩
    have hρC : ρ ∈ torus5 σ r ⊓ (suBlockB σ hσσ).range := ⟨hρ, hA ▸ c.rho_mem⟩
    have hcard := card_torus5_inf_rangeB hσσ hr.pos hfix hprim
    have hρ1 : (⟨ρ, hρC⟩ : ↥(torus5 σ r ⊓ (suBlockB σ hσσ).range)) ≠ 1 := fun h =>
      c.rho_ne (congrArg Subtype.val h)
    have hmem := mem_powers_of_prime_card hcard hρ1
      (g' := (⟨τ, hτC⟩ : ↥(torus5 σ r ⊓ (suBlockB σ hσσ).range)))
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 hmem
    have hρn : ρ ^ n = τ := by simpa using congrArg Subtype.val hn
    have h1 := c.inter n 1 (by rw [pow_one]; exact hρn)
    exact c.tau_ne (by rw [← hρn, h1])
  ·
    exfalso
    have hτ' : piU σ * τ * (piU σ)⁻¹ ∈ torus5 σ r ⊓ (suBlockB σ hσσ).range :=
      ⟨piU_conj_mem_torus5 hτ, hB ⟨τ, c.tau_mem, rfl⟩⟩
    rw [torus5_inf_rangeB_eq hσσ r hfix] at hτ'
    obtain ⟨e, he, hee⟩ := hτ'
    have he' : e ^ r = 1 := (mem_rootsOfUnity r _).1 he
    have hτe : τ = bB σ e (hfix e he') := by
      have h1 : piU σ * (piU σ * τ * (piU σ)⁻¹) * (piU σ)⁻¹ = τ := by
        calc piU σ * (piU σ * τ * (piU σ)⁻¹) * (piU σ)⁻¹
            = (piU σ * piU σ) * τ * ((piU σ)⁻¹ * (piU σ)⁻¹) := by group
          _ = τ := by rw [piU_mul_self, piU_inv, piU_mul_self]; group
      apply Subtype.ext
      rw [← h1, ← hee, Subgroup.coe_mul, Subgroup.coe_mul, coe_rhoB hσσ (hfix e he'),
        Subgroup.coe_inv, piU_conj_diag, inv_inv]
      rfl
    obtain ⟨a₀, ha₀, hne⟩ := c.std
    apply hne
    rw [hA] at ha₀
    obtain ⟨A₀, rfl⟩ := ha₀
    have := Subgroup.mem_centralizer_singleton_iff.1
      (suBlockB_mem_centralizer σ hσσ (hfix e he') A₀)
    rw [hτe]
    exact this.symm
  ·
    have hBeq : B = (suBlock σ).range := by
      refine Subgroup.eq_of_le_of_card_ge hB ?_
      rw [card_range_suBlock, c.cardB]
    rw [hA, hBeq, sup_comm, hgen]
  ·
    have hωA : omU σ ∈ A := hA ▸ omU_mem_range σ hσσ
    have hBeq : B.map (MulAut.conj (omU σ)).toMonoidHom = (suBlock σ).range := by
      refine Subgroup.eq_of_le_of_card_ge hB ?_
      rw [card_range_suBlock, Subgroup.card_map_of_injective (MulAut.conj (omU σ)).injective,
        c.cardB]
    apply sup_eq_top_of_map_conj (omU σ)
    rw [map_conj_eq_of_mem hωA, hBeq, sup_comm, hA]
    exact hgen

theorem core_diag (hσσ : ∀ x, σ (σ x) = x) (hK4 : 4 ≤ Nat.card K) (hF4 : 4 ≤ Nat.card (fixF σ))
    (hlt : Nat.card (fixF σ) < Nat.card K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hfix : ∀ u : Kˣ, u ^ r = 1 → σ (u : K) = u) (hprim : ∃ ζ : Kˣ, IsPrimitiveRoot ζ r)
    (hgen : (suBlock σ).range ⊔ (suBlockB σ hσσ).range = ⊤)
    {A B : Subgroup ↥(SU σ 4)} {ρ τ : ↥(SU σ 4)} (c : Config σ r A B ρ τ)
    (hρ : ρ ∈ torus5 σ r) (hτ : τ ∈ torus5 σ r) : A ⊔ B = ⊤ := by
  classical
  have hSL := card_SL_two_lt (K := K) (F := fixF σ) (by omega) hlt
  obtain ⟨γ, hγ, hγ1, hγc⟩ := c.gamma₁
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus5_iff.1 (closure_pair_le_torus5 hρ hτ hγ)
  have hAn : A ≠ ⊥ := fun h => c.rho_ne (by
    have := c.rho_mem
    rw [h, Subgroup.mem_bot] at this
    exact this)
  rcases perfect_commute_diag σ hσσ hK4 hF4 hr hr2 hfix ha hb (ne_one_params hab hγ1) c.perfA
    hAn hab hγc with ⟨-, hAr⟩ | ⟨-, hAr⟩ | ⟨-, hAr⟩ | ⟨-, hAr⟩
  · exact core_diag_I hσσ hK4 hF4 hr hr2 hfix hprim hgen c hρ hτ
      (Subgroup.eq_of_le_of_card_ge hAr (by rw [card_range_suBlockB, c.cardA]))
  · have hAeq : A.map (MulAut.conj (piU σ)).toMonoidHom = (suBlockB σ hσσ).range := by
      refine Subgroup.eq_of_le_of_card_ge hAr ?_
      rw [card_range_suBlockB, Subgroup.card_map_of_injective (MulAut.conj (piU σ)).injective,
        c.cardA]
    exact sup_eq_top_of_map_conj (piU σ) (core_diag_I hσσ hK4 hF4 hr hr2 hfix hprim hgen
      (c.conj (piU σ)) (piU_conj_mem_torus5 hρ) (piU_conj_mem_torus5 hτ) hAeq)
  · exfalso
    have := Subgroup.card_le_of_le hAr
    rw [c.cardA, card_range_suBlock] at this
    exact absurd this (not_le.2 hSL)
  · exfalso
    have h1 := Subgroup.card_le_of_le hAr
    rw [Subgroup.card_map_of_injective (MulAut.conj (omU σ)).injective, c.cardA,
      card_range_suBlock] at h1
    exact absurd h1 (not_le.2 hSL)

end CFSG.RankThree.PartOne.U4F
