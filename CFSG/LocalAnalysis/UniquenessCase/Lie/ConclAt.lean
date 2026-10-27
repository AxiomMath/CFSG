module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

@[expose] def uc22pwlie_ConclAt (Ep : ∀ (Y : Type) [Group Y], Subgroup Y → Prop) (X : Type) [Group X]
    [Finite X] (U : Subgroup X) (P : Type) [Group P] (ψ : P →* MulAut X) (n m' : ℕ) (E : Subgroup X) :
    Prop :=
  E ≤ normalizer (U : Set X) ∧ Ep X E ∧ piSet E = etaSet n ∧
    (∀ g : P, ∀ x ∈ E, ψ g x ∈ E ⊔ U) ∧
    (∀ g : P, ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ψ g x * x⁻¹ ∈ U) ∧
    ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧ normalizer (U : Set X) ⊔ zpowers w = ⊤

variable {X Y : Type} [Group X] [Group Y]

theorem uc22pwlie_ConclAt.of_mulEquiv {Ep : ∀ (Y : Type) [Group Y], Subgroup Y → Prop}
    (hEp : ∀ {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z) (E : Subgroup Y), Ep Y E →
      Ep Z (E.map e.toMonoidHom))
    [Finite X] [Finite Y] (e : X ≃* Y) {U : Subgroup X} {P : Type} [Group P] (ψ : P →* MulAut X)
    {n m' : ℕ} {E' : Subgroup Y}
    (h : uc22pwlie_ConclAt Ep Y (U.map e.toMonoidHom) P ((MulAut.congr e).toMonoidHom.comp ψ) n m' E') :
    uc22pwlie_ConclAt Ep X U P ψ n m' (E'.map e.symm.toMonoidHom) := by
  obtain ⟨hE'N, hE'p, hE'π, hE'inv, hE'α, w', hw'2, hw'inv, hw'gen⟩ := h
  have hmapN : (normalizer (U : Set X)).map e.toMonoidHom =
      normalizer ((U.map e.toMonoidHom : Subgroup Y) : Set Y) := Subgroup.map_equiv_normalizer_eq U e
  refine ⟨?_, hEp e.symm E' hE'p, ?_, ?_, ?_, e.symm w', ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ (normalizer (U : Set X)).map e.toMonoidHom := by
      rw [hmapN]
      exact hE'N hy
    obtain ⟨z, hz, hzy⟩ := hy'
    have : z = e.symm y := by rw [← hzy]; simp
    show e.symm y ∈ normalizer (U : Set X)
    rw [← this]
    exact hz
  · rw [uc22pwlie_piSet_map, hE'π]
  · rintro g _ ⟨y, hy, rfl⟩
    have h1 := hE'inv g y hy
    have h2 : e (ψ g (e.symm y)) ∈ E' ⊔ U.map e.toMonoidHom := by
      simpa [MulAut.congr_apply] using h1
    have h3 : ψ g (e.symm y) ∈ (E' ⊔ U.map e.toMonoidHom).map e.symm.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      simpa using h2
    rwa [Subgroup.map_sup, uc22pwlie_map_map_symm] at h3
  · rintro g x hx
    have hx' : e x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E' := uc22pwlie_oPi_le_comap e _ E' hx
    have h1 := hE'α g (e x) hx'
    have h2 : e (ψ g x * x⁻¹) ∈ U.map e.toMonoidHom := by
      simpa [MulAut.congr_apply] using h1
    rw [uc22pwlie_mem_map_iff] at h2
    simpa using h2
  · rw [← map_pow, hw'2, map_one]
  · rintro _ ⟨y, hy, rfl⟩
    have := hw'inv y hy
    show e.symm w' * e.symm y * (e.symm w')⁻¹ = (e.symm y)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, this, map_inv]
  · have hmap : (normalizer (U : Set X) ⊔ zpowers (e.symm w')).map e.toMonoidHom = ⊤ := by
      rw [Subgroup.map_sup, hmapN, MonoidHom.map_zpowers]
      simpa using hw'gen
    exact Subgroup.map_injective e.injective
      (hmap.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)

@[expose] def uc22pwlie_Gal (U E : Subgroup X) {P : Type} [Group P] (ψ : P →* MulAut X) : Prop :=
  ∀ g : P, ∃ i : ℕ, ∀ x ∈ E, ψ g x * (x ^ 2 ^ i)⁻¹ ∈ U

theorem uc22pwlie_Gal.of_mulEquiv (e : X ≃* Y) {U : Subgroup X} {P : Type} [Group P]
    (ψ : P →* MulAut X) {E' : Subgroup Y}
    (h : uc22pwlie_Gal (U.map e.toMonoidHom) E' ((MulAut.congr e).toMonoidHom.comp ψ)) :
    uc22pwlie_Gal U (E'.map e.symm.toMonoidHom) ψ := by
  intro g
  obtain ⟨i, hi⟩ := h g
  refine ⟨i, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 := hi y hy
  have h2 : e (ψ g (e.symm y) * ((e.symm y) ^ 2 ^ i)⁻¹) ∈ U.map e.toMonoidHom := by
    simpa [MulAut.congr_apply] using h1
  rw [uc22pwlie_mem_map_iff] at h2
  simpa using h2

@[expose] def uc22pwlie_RShape (U E : Subgroup X) {P : Type} [Group P] (ψ : P →* MulAut X) : Prop :=
  ∃ (H : Type) (_ : CommGroup H) (_ : Finite H) (ι : H →* X) (ρ : MulAut H),
    Function.Injective ι ∧ Odd (Nat.card H) ∧ ι.range ≤ normalizer (U : Set X) ∧ E ≤ ι.range ∧
      (∀ t : H, ρ (ρ t) = t ^ 2) ∧ ∀ g : P, ∃ m : ℕ, ∀ t : H, ψ g (ι t) * (ι ((ρ ^ m) t))⁻¹ ∈ U

theorem uc22pwlie_RShape.of_mulEquiv (e : X ≃* Y) {U : Subgroup X} {P : Type} [Group P]
    (ψ : P →* MulAut X) {E' : Subgroup Y}
    (h : uc22pwlie_RShape (U.map e.toMonoidHom) E' ((MulAut.congr e).toMonoidHom.comp ψ)) :
    uc22pwlie_RShape U (E'.map e.symm.toMonoidHom) ψ := by
  obtain ⟨H, _, _, ι, ρ, hι, hodd, hN, hE, hρ, hsh⟩ := h
  have hmapN : (normalizer (U : Set X)).map e.toMonoidHom =
      normalizer ((U.map e.toMonoidHom : Subgroup Y) : Set Y) := Subgroup.map_equiv_normalizer_eq U e
  refine ⟨H, inferInstance, inferInstance, e.symm.toMonoidHom.comp ι, ρ, e.symm.injective.comp hι,
    hodd, ?_, ?_, hρ, ?_⟩
  · rintro _ ⟨t, rfl⟩
    have hy' : ι t ∈ (normalizer (U : Set X)).map e.toMonoidHom := by
      rw [hmapN]
      exact hN ⟨t, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hy'
    have : z = e.symm (ι t) := by rw [← hzy]; simp
    show e.symm (ι t) ∈ normalizer (U : Set X)
    rw [← this]
    exact hz
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := hE hy
    exact ⟨t, rfl⟩
  · intro g
    obtain ⟨m, hm⟩ := hsh g
    refine ⟨m, fun t => ?_⟩
    have h1 := hm t
    have h2 : e (ψ g (e.symm (ι t)) * (e.symm (ι ((ρ ^ m) t)))⁻¹) ∈ U.map e.toMonoidHom := by
      simpa [MulAut.congr_apply] using h1
    rw [uc22pwlie_mem_map_iff] at h2
    simpa using h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
