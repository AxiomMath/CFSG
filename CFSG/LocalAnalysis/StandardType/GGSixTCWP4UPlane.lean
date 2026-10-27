module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem exists_langSetup_of_tcPlane
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup ↥(adjointGroup τ K)) (hE : ∀ x ∈ E, x ^ p = 1)
    (htor : ∃ g ∈ adjointGroup τ (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∈
        torusGroup τ (AlgebraicClosure K)) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = 2 ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ S.D.q) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      (∃ w : WeylGroup τ, S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ∀ x ∈ E, ι x ∈ S.D.torus := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h <;> exact single_edge_perfect τ K (by simp [h])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_finite_field_card_two_pow hK
  have hf1 : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobenius_def 2 f c
  have hFrK : ∀ c : L, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 f c
  have hcardK : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L 2 f (baseChangeGL ι₁ y) = baseChangeGL ι₁ y := by
    intro y
    have hcomp : (iterateFrobenius L 2 f).comp ι₁ = ι₁ := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L 2 f) (ι₁ c) = ι₁ c
      rw [iterateFrobenius_def, ← map_pow, ← hcardK]
      congr 1
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hpq : Nat.Coprime p (2 ^ f) := by
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  set ι₀ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι₁).comp (adjointGroup τ K).subtype with hι₀
  have hι₀inj : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  obtain ⟨g, hg, hgE⟩ := htor
  obtain ⟨w, g0, hg0, hF, hmem⟩ := exists_lang_torus_of_conj_torus f hf1 hpq (ℓ := 2)
    (A := E.map ι₀)
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      change (baseChangeGL ι₁ (y : ModGL τ K)) ^ p = 1
      rw [← map_pow, ← Subgroup.coe_pow, hE y hy]
      simp)
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hFix y)
    hg (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hgE y hy)
  set D : LangDatum τ L :=
    LangDatum.ofFrobenius (iterateFrobenius L 2 f) (2 ^ f) hFr w hg0 hF with hD
  have hDq : D.q = 2 ^ f := rfl
  have hd : LangDescent D 7 ι₀ := by
    have hΦ : D.Φ = Units.map (entrywiseHom (iterateFrobenius L 2 f)) := rfl
    rcases hτ' with h' | h' | h' | h' | h'
    · exact langDescent_exact (Or.inl h') hFrK D hΦ hperf
    · exact langDescent_exact (Or.inr h') hFrK D hΦ hperf
    · exact langDescent_untw 3 (Or.inl ⟨h', rfl⟩) hFrK D hΦ Nat.prime_seven (by norm_num) hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h', rfl⟩)) hFrK D hΦ Nat.prime_seven
        (by norm_num) hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h', rfl⟩)) hFrK D hΦ Nat.prime_seven
        (by norm_num) hperf
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    rw [hDq]
    exact ⟨Nat.prime_two.isPrimePow.pow (by omega),
      (CharP.cast_eq_zero_iff L 2 _).2 (dvd_pow_self 2 (by omega))⟩
  have hpq5 : ¬ 5 ∣ D.q := by
    rw [hDq]
    intro h
    have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  have hq5 : 5 ≤ 5 ∨ 4 ≤ D.q := Or.inl le_rfl
  let ι : ↥(adjointGroup τ K) →* ModGL τ L := (MulAut.conj D.g0⁻¹).toMonoidHom.comp ι₀
  have hι : ∀ c, ι c = D.g0⁻¹ * ι₀ c * D.g0 := fun c => by
    change (MulAut.conj D.g0⁻¹) (ι₀ c) = _
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨D.toSetup 5 ρ hρ Nat.prime_five hq5 hqpow hpq5 hd.finite_model, ι, hDq,
    ⟨iterateFrobenius L 2 f, hFr, rfl⟩, ⟨w, rfl⟩,
    (MulAut.conj D.g0⁻¹).injective.comp hι₀inj, ?_, fun x hx => ?_⟩
  · show ι.range = D.Γ
    rw [hd.Γ_eq]
    exact MonoidHom.range_comp (MulAut.conj D.g0⁻¹).toMonoidHom ι₀
  · obtain ⟨y, hy, hyx⟩ := hmem (ι₀ x) ⟨x, hx, rfl⟩
    have hyeq : y = D.g0⁻¹ * ι₀ x * D.g0 := by
      have h : D.g0 * y * D.g0⁻¹ = ι₀ x := hyx
      rw [← h]
      group
    show ι x ∈ D.torus
    rw [hι x, ← hyeq]
    exact hy

end CFSG.StandardType.TableCRes

end
