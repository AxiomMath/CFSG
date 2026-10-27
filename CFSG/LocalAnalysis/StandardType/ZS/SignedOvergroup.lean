module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroupMonomial
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroupOrth

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

private theorem range_transvection_sub_id_of_apply_eq_one {R : Type*} [Ring R]
    {V : Type*} [AddCommGroup V] [Module R V] {f : Module.Dual R V} {v w : V}
    (hfv : f v = 0) (hfw : f w = 1) :
    LinearMap.range ((LinearEquiv.transvection hfv : V →ₗ[R] V) - LinearMap.id) =
      Submodule.span R {v} := by
  have happly : ∀ x, (LinearEquiv.transvection hfv : V →ₗ[R] V) x = x + f x • v :=
    fun x => LinearEquiv.transvection.apply hfv x
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, happly]
    rw [show y + f y • v - y = f y • v by abel]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro hx
    refine (Submodule.span_le.mpr ?_) hx
    rintro z rfl
    refine ⟨w, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, happly, hfw, one_smul]
    abel

private theorem exists_transvection_of_slpm {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (hn : 2 ≤ n) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g, g ∈ A ↔ LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1) :
    ∃ τ ∈ A,
      Module.finrank (ZMod p) (LinearMap.range ((τ : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 ∧
        ∀ v, τ (τ v - v) = τ v - v := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h10 : i1 ≠ i0 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  have hfv : (b.coord i1) (b i0) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne h10]
  have hfw : (b.coord i1) (b i1) = 1 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  let τ : U ≃ₗ[ZMod p] U := LinearEquiv.transvection hfv
  have hτ : ∀ x, τ x = x + (b.coord i1) x • b i0 := fun x =>
    LinearEquiv.transvection.apply hfv x
  have hτ0 : τ (b i0) = b i0 := by rw [hτ (b i0), hfv, zero_smul, add_zero]
  refine ⟨τ, (hA τ).mpr (Or.inl ?_), ?_, ?_⟩
  · simp [τ]
  · rw [range_transvection_sub_id_of_apply_eq_one hfv hfw]
    simpa using finrank_span_singleton (Module.Basis.ne_zero b i0)
  · intro v
    have hdiff : τ v - v = (b.coord i1) v • b i0 := by
      rw [hτ v]
      abel
    rw [hdiff, map_smul, hτ0]

private theorem false_of_slpm_of_signed_le {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (hn : 2 ≤ n) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ g, g ∈ A ↔ LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)
    (htv : ∀ τ ∈ A,
      Module.finrank (ZMod p) (LinearMap.range ((τ : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v) : False := by
  obtain ⟨τ, hτA, hrank, hfix⟩ := exists_transvection_of_slpm b hn hA
  obtain ⟨v, hv⟩ := htv τ hτA hrank
  exact hv (hfix v)

private theorem false_of_excRow_of_signed_le {n : ℕ} (hn : 5 ≤ n) {k : ExcRow}
    (hnk : n = k.deg) {N : ℕ} (hdvd : 2 ^ n * n.factorial ∣ N) (hcard : N = k.ord) : False := by
  cases k <;> simp only [ExcRow.deg] at hnk
  · omega
  · omega
  · rw [hnk] at hdvd
    rw [hcard] at hdvd
    norm_num [ExcRow.ord] at hdvd
  · rw [hnk] at hdvd
    rw [hcard] at hdvd
    norm_num [ExcRow.ord] at hdvd
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem eq_of_basis_fin {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (f : Module.Basis (Fin m) (ZMod p) U) : m = n := by
  simpa using (Module.finrank_eq_card_basis f).symm.trans (Module.finrank_eq_card_basis b)

theorem linWeyl_or_reflFix_or_twist_of_signed_le (hp : p ≠ 2) (hn : 5 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hfam : Family p A)
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (hdvd : 2 ^ n * n.factorial ∣ Nat.card A)
    (htv : ∀ τ ∈ A,
      Module.finrank (ZMod p) (LinearMap.range ((τ : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v)
    (i₀ : Fin n) :
    LinWeyl p A ∨
      (∃ r ∈ A, IsRefl p r ∧ r (b i₀) = b i₀ ∧ r (∑ i, b i) = ∑ i, b i ∧
        ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), ∀ i, r (b i) = c i • b (σ i)) ∨
      ((∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
          ∀ i, a (b i) = c i • b (σ i)) ∧
        ∀ a₁ a₂ : Fin n, a₁ ≠ a₂ → ∃ ζ : (ZMod p)ˣ, (ζ : ZMod p) ≠ 1 ∧ (ζ : ZMod p) ≠ -1 ∧
          diagMap p b (pairUnit p a₁ a₂ ζ) * permMap p b (Equiv.swap a₁ a₂) ∈ A) := by
  cases hfam with
  | weyl h => exact Or.inl h
  | slpm h => exact (false_of_slpm_of_signed_le b (by omega) h htv).elim
  | orth Q _ hA =>
      exact Or.inr (Or.inl
        (exists_isRefl_fix_not_monomial_of_orth hp hn b hperm hsgn Q hA i₀))
  | orthClass Q c hQ hc hA =>
      exact Or.inr (Or.inl
        (exists_isRefl_fix_not_monomial_of_orthClass hp hn b hperm hsgn Q hQ hc hA i₀))
  | gmmn f j₀ j₁ ζ _ hi _ _ hA =>
      obtain rfl := eq_of_basis_fin b f
      exact (false_of_gmmn_of_signed_le hp (by omega) b f hperm hsgn hi ζ hA).elim
  | g2mmn f j₀ j₁ ζ m hi hm hord hA =>
      obtain rfl := eq_of_basis_fin b f
      exact Or.inr (Or.inr
        (exists_twist_mem_of_g2mmn hp (by omega) b f hperm hsgn hi hm hord hA))
  | exc k _ hdim hcard _ _ _ _ =>
      exfalso
      have hb : Module.finrank (ZMod p) U = n := by simpa using Module.finrank_eq_card_basis b
      exact false_of_excRow_of_signed_le hn (by omega) hdvd hcard
  | h4 _ hdim _ _ _ _ =>
      exfalso
      have hb : Module.finrank (ZMod p) U = n := by simpa using Module.finrank_eq_card_basis b
      omega

omit [Fact p.Prime] in
private theorem n4_or_en4_of_excRow_of_signed_four {k : ExcRow} (hk : k.admissible p)
    (hdeg : k.deg = 4) {N : ℕ} (hdvd : 2 ^ 4 * Nat.factorial 4 ∣ N) (hcard : N = k.ord)
    (hcen : k.cen ∣ p - 1) : k = .N4 ∨ k = .EN4 := by
  cases k <;> simp only [ExcRow.deg] at hdeg
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso; omega
  · exfalso; omega
  · exfalso
    rw [hcard] at hdvd
    norm_num [ExcRow.ord, Nat.factorial] at hdvd
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso
    have hp3 : p = 3 := hk
    rw [hp3] at hcen
    norm_num [ExcRow.cen] at hcen

private theorem orth_cases_of_signed_four (hp : p ≠ 2) (b : Module.Basis (Fin 4) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hA : ∀ g, g ∈ A ↔ IsIsom p Q g) (i₀ : Fin 4) :
    (p ≠ 3 ∧ (∃ r ∈ A, IsRefl p r ∧ r (b i₀) = b i₀ ∧
        ¬ ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p), ∀ i, r (b i) = c i • b (σ i)) ∧
      ∃ r ∈ A, IsRefl p r ∧ r (∑ i, b i) = ∑ i, b i ∧
        ∀ (k : Fin 4) (c s : ZMod p), r (b 3) ≠ c • b k + s • ∑ i, b i) ∨
    (p = 3 ∧ ∃ Q' : QuadraticForm (ZMod p) U,
      (QuadraticMap.polarBilin Q').Nondegenerate ∧
      (∃ W : Submodule (ZMod p) U, Module.finrank (ZMod p) W = 2 ∧ ∀ w ∈ W, Q' w = 0) ∧
      ∀ g, g ∈ A ↔ IsIsom p Q' g) := by
  by_cases hp3 : p = 3
  · refine Or.inr ⟨hp3, Q, hQ, ?_, hA⟩
    exact exists_singular_plane_of_signed_three hp3 b (fun σ => (hA _).1 (hperm σ))
      (fun i => (hA _).1 (hsgn i))
  · exact Or.inl ⟨hp3, exists_isRefl_fix_not_monomial_of_orth_of_ne_three hp hp3 (by norm_num)
      b hperm hsgn Q hA i₀, exists_isRefl_fix_sum_of_orth_four hp hp3 b hperm hsgn Q hA⟩

private theorem exc_four_of_signed_four {A : Subgroup (U ≃ₗ[ZMod p] U)} (hirr : AbsIrred p A)
    (b : Module.Basis (Fin 4) (ZMod p) U)
    {k : ExcRow} (hk : k.admissible p)
    (hdim : Module.finrank (ZMod p) U = k.deg) (hcard : Nat.card A = k.ord)
    (hcen : Nat.card (Subgroup.center A) = k.cen) (hdmax : DMax p A k.dmax) (hone : OneClass p A)
    (hmodel : k.needsModel → ModelIso p k A) (hdvd : 2 ^ 4 * Nat.factorial 4 ∣ Nat.card A) :
    ∃ k : ExcRow, (k = .N4 ∨ k = .EN4) ∧ Nat.card A = k.ord ∧ DMax p A k.dmax ∧
      OneClass p A ∧ ModelIso p k A ∧ 4 ∣ p - 1 := by
  have hb : Module.finrank (ZMod p) U = 4 := by simpa using Module.finrank_eq_card_basis b
  have hdeg : k.deg = 4 := by rw [← hdim, hb]
  have hcen' : k.cen ∣ p - 1 := hcen ▸ card_center_dvd_sub_one hirr
  obtain hk' | hk' := n4_or_en4_of_excRow_of_signed_four hk hdeg hdvd hcard hcen'
  · subst hk'
    exact ⟨.N4, Or.inl rfl, hcard, hdmax, hone, hmodel trivial,
      by simpa [ExcRow.cen] using hcen'⟩
  · subst hk'
    exact ⟨.EN4, Or.inr rfl, hcard, hdmax, hone, hmodel trivial,
      by simpa [ExcRow.cen] using hcen'⟩

theorem linWeyl_or_cases_of_signed_four (hp : p ≠ 2) (b : Module.Basis (Fin 4) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hfam : Family p A) (hirr : AbsIrred p A)
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A)
    (hdvd : 2 ^ 4 * Nat.factorial 4 ∣ Nat.card A)
    (htv : ∀ τ ∈ A,
      Module.finrank (ZMod p) (LinearMap.range ((τ : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v)
    (i₀ : Fin 4) :
    LinWeyl p A ∨
      (p ≠ 3 ∧ (∃ r ∈ A, IsRefl p r ∧ r (b i₀) = b i₀ ∧
          ¬ ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p), ∀ i, r (b i) = c i • b (σ i)) ∧
        ∃ r ∈ A, IsRefl p r ∧ r (∑ i, b i) = ∑ i, b i ∧
          ∀ (k : Fin 4) (c s : ZMod p), r (b 3) ≠ c • b k + s • ∑ i, b i) ∨
      ((∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p), (∀ i, c i ≠ 0) ∧
          ∀ i, a (b i) = c i • b (σ i)) ∧
        ∀ a₁ a₂ : Fin 4, a₁ ≠ a₂ → ∃ ζ : (ZMod p)ˣ, (ζ : ZMod p) ≠ 1 ∧ (ζ : ZMod p) ≠ -1 ∧
          diagMap p b (pairUnit p a₁ a₂ ζ) * permMap p b (Equiv.swap a₁ a₂) ∈ A) ∨
      (p = 3 ∧ ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
        (∃ W : Submodule (ZMod p) U, Module.finrank (ZMod p) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
        ∀ g, g ∈ A ↔ IsIsom p Q g) ∨
      ∃ k : ExcRow, (k = .N4 ∨ k = .EN4) ∧ Nat.card A = k.ord ∧ DMax p A k.dmax ∧ OneClass p A ∧
        ModelIso p k A ∧ 4 ∣ p - 1 := by
  cases hfam with
  | weyl h => exact Or.inl h
  | slpm h => exact (false_of_slpm_of_signed_le b (by norm_num) h htv).elim
  | orth Q hQ hA =>
      obtain h2 | h4 := orth_cases_of_signed_four hp b hperm hsgn Q hQ hA i₀
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  | orthClass Q c hQ hc hA =>
      by_cases hp3 : p = 3
      · exact (false_of_orthClass_of_signed_three hp3 (by norm_num) b hperm hsgn Q hQ hc hA).elim
      · exact Or.inr (Or.inl ⟨hp3, exists_isRefl_fix_not_monomial_of_orthClass_of_ne_three hp hp3
          (by norm_num) b hperm hsgn Q hQ hc hA i₀,
          exists_isRefl_fix_sum_of_orthClass_four hp hp3 b hperm hsgn Q hQ hc hA⟩)
  | gmmn f j₀ j₁ ζ _ hi _ _ hA =>
      obtain rfl := eq_of_basis_fin b f
      exact (false_of_gmmn_of_signed_le hp (by norm_num) b f hperm hsgn hi ζ hA).elim
  | g2mmn f j₀ j₁ ζ _ hi hm hord hA =>
      obtain rfl := eq_of_basis_fin b f
      exact Or.inr (Or.inr (Or.inl
        (exists_twist_mem_of_g2mmn hp (by norm_num) b f hperm hsgn hi hm hord hA)))
  | exc k hk hdim hcard hcen hdmax hone hmodel =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (exc_four_of_signed_four hirr b hk hdim hcard hcen hdmax hone hmodel hdvd))))
  | h4 _ _ hcard _ _ _ =>
      rw [hcard] at hdvd
      exact absurd hdvd (by decide)

end CFSG.StandardType.ZS

end
