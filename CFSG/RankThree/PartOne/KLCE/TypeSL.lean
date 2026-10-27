module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Push

theorem exists_hom_of_push {G G' D : Type} [Group G] [Group G'] [Group D] (ψ : G →* G')
    (hψ : Function.Injective ψ) (ρ : D →* G') (hρ : Function.Injective ρ)
    (hrange : ρ.range ≤ ψ.range) :
    ∃ φ : D →* G, Function.Injective φ ∧ (∀ d, ψ (φ d) = ρ d) ∧
      φ.range = (ρ.range).comap ψ := by
  classical
  have hex : ∀ d, ∃ g, ψ g = ρ d := fun d => hrange ⟨d, rfl⟩
  choose f hf using hex
  have hmul : ∀ a b, f (a * b) = f a * f b := fun a b => by
    apply hψ
    rw [map_mul, hf, hf, hf, map_mul]
  have hone : f 1 = 1 := by
    apply hψ
    rw [hf, map_one, map_one]
  refine ⟨⟨⟨f, hone⟩, hmul⟩, ?_, hf, ?_⟩
  · intro a b hab
    apply hρ
    rw [← hf a, ← hf b]
    exact congrArg ψ hab
  · ext g
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, (hf d).symm⟩
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      apply hψ
      exact (hf d).trans hd

end Push

section SL

variable {m : ℕ} {K' : Type} [Field K']

theorem map_transvection (σ' : K' →+* K') {i j : Fin (m + 2)} (h : i ≠ j) (a : K') :
    SpecialLinearGroup.map σ' (SpecialLinearGroup.transvection h a) =
      SpecialLinearGroup.transvection h (σ' a) := by
  ext k l
  simp [SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]

theorem transvection_noncomm :
    SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K') *
      SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K') ≠
    SpecialLinearGroup.transvection (show (1 : Fin (m + 2)) ≠ 0 by simp) (1 : K') *
      SpecialLinearGroup.transvection (show (0 : Fin (m + 2)) ≠ 1 by simp) (1 : K') := by
  intro h
  have h0 := congrArg (fun C : SpecialLinearGroup (Fin (m + 2)) K' =>
    C • (Pi.single 0 1 : Fin (m + 2) → K')) h
  simp only [mul_smul, SpecialLinearGroup.transvection_smul_single_fst,
    SpecialLinearGroup.transvection_smul_single_snd, one_smul, smul_add] at h0
  have := congrFun h0 0
  simp at this

theorem orderOf_transvection_one [CharP K' 2] {i j : Fin (m + 2)} (h : i ≠ j) :
    orderOf (SpecialLinearGroup.transvection h (1 : K')) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← SpecialLinearGroup.transvection_add]
    have h2 : (1 : K') + 1 = 0 := by
      have := CharP.cast_eq_zero K' 2
      simpa [one_add_one_eq_two] using this
    rw [h2, SpecialLinearGroup.transvection_coeff_zero]
  · intro h1
    have := (SpecialLinearGroup.transvection_mem_center_iff h (1 : K')).1
      (h1 ▸ Subgroup.one_mem _)
    exact one_ne_zero this

theorem sl_center_pow (z : SpecialLinearGroup (Fin (m + 2)) K')
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K')) : z ^ (m + 2) = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr
  have h1 : ((z ^ (m + 2) : SpecialLinearGroup (Fin (m + 2)) K') :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K') = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one]
  ext i j
  have := congrFun (congrFun h1 i) j
  simpa using this

theorem transvection_injective {i j : Fin (m + 2)} (h : i ≠ j) :
    Function.Injective (SpecialLinearGroup.transvection (F := K') h) := by
  intro a b hab
  have := congrFun (congrFun (congrArg (fun A : SpecialLinearGroup (Fin (m + 2)) K' =>
    (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K')) hab) i) j
  simpa [SpecialLinearGroup.transvection_coe, Matrix.single_apply, h] using this

theorem lieModel_psl_of_range {p f' m : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f') {K' : Type} [Field K']
    [Finite K'] (hK' : Nat.card K' = 2 ^ (p * f')) {G : Type} [Group G]
    (φ : SpecialLinearGroup (Fin (m + 2)) K' →* G) (hφ : Function.Injective φ) :
    LieModel (↥φ.range ⧸ Subgroup.center ↥φ.range) .PSL (m + 2) 2 (p * f') := by
  let e : SpecialLinearGroup (Fin (m + 2)) K' ≃* ↥φ.range := MonoidHom.ofInjective hφ
  let e' : ProjectiveSpecialLinearGroup (Fin (m + 2)) K' ≃* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hpf : 5 ≤ p * f' := by nlinarith
  have hbig : 8 ≤ 2 ^ (p * f') := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hadm : StatedLieAdmissible .PSL (m + 2) 2 (p * f') := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  refine Or.inl ⟨by decide, ?_⟩
  refine CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e' ?_
  exact ⟨hadm, K', inferInstance, inferInstance, hK',
    ⟨projectiveSpecialLinearGroupEquivStatedProj (m + 2) K'⟩⟩

theorem sl_type_claims {p f' m : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f') {K' : Type}
    [Field K'] [Finite K'] [CharP K' 2] (hK' : Nat.card K' = 2 ^ (p * f')) {σ' : K' ≃+* K'}
    (hσ' : σ' ≠ 1) {G : Type} [Group G] (α : MulAut G)
    (φ : SpecialLinearGroup (Fin (m + 2)) K' →* G) (hφ : Function.Injective φ)
    (hαφ : ∀ B, α (φ B) = φ (SpecialLinearGroup.map σ'.toRingHom B)) (Q : Subgroup G)
    (hQ : φ.range = Q) :
    (∀ g ∈ Q, α g ∈ Q) ∧ (∃ g ∈ Q, α g ≠ g) ∧
      (∀ z ∈ Subgroup.center ↥Q, z ^ (m + 2) = 1) ∧
      (∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
        LieModel (↥Q ⧸ Subgroup.center ↥Q) t' n' 2 (p * f'')) ∧
      ∃ t₁ ∈ Q, α t₁ = t₁ ∧ ∃ t₂ ∈ Q, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
        (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  subst hQ
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_, ⟨.PSL, m + 2, f', hf', lieModel_psl_of_range hp5 hf' hK' φ hφ⟩, ?_⟩
  · rintro _ ⟨B, rfl⟩
    exact ⟨_, (hαφ B).symm⟩
  · obtain ⟨a, ha⟩ : ∃ a, σ' a ≠ a := by
      by_contra h
      exact hσ' (RingEquiv.ext fun a => by_contra fun hne => h ⟨a, hne⟩)
    refine ⟨φ (SpecialLinearGroup.transvection h01 a), ⟨_, rfl⟩, ?_⟩
    rw [hαφ, map_transvection]
    intro h
    exact ha (transvection_injective h01 (hφ h))
  · intro z hz
    let e : SpecialLinearGroup (Fin (m + 2)) K' ≃* ↥φ.range := MonoidHom.ofInjective hφ
    have hz' : e.symm z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 2)) K') := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hz (e g)
    have := sl_center_pow _ hz'
    calc z ^ (m + 2) = e ((e.symm z) ^ (m + 2)) := by rw [map_pow, MulEquiv.apply_symm_apply]
      _ = 1 := by rw [this, map_one]
  · have hc : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hone : σ'.toRingHom (1 : K') = 1 := map_one _
    refine ⟨φ (SpecialLinearGroup.transvection h01 1), ⟨_, rfl⟩, ?_,
      φ (SpecialLinearGroup.transvection h10 1), ⟨_, rfl⟩, ?_, ⟨1, ?_⟩, ⟨1, ?_⟩, ?_⟩
    · rw [hαφ, map_transvection, hone]
    · rw [hαφ, map_transvection, hone]
    · rw [orderOf_injective φ hφ, orderOf_transvection_one h01, pow_one]
    · rw [orderOf_injective φ hφ, orderOf_transvection_one h10, pow_one]
    · intro h
      rw [← map_mul, ← map_mul] at h
      exact transvection_noncomm (hφ h)

end SL

end CFSG.RankThree.PartOne.KLCE
