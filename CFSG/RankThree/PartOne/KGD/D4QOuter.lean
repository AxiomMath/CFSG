module

public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

theorem d4Q_not_dvd_card_fixed {Q p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hQ : 2 ≤ Q)
    (hpq : p ∣ Q ^ 2 + 1) :
    ¬ p ∣ Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1) := by
  intro h
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hz : (p : ℤ) ∣ (Q : ℤ) ^ 12 * ((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1) *
      ((Q : ℤ) ^ 8 + (Q : ℤ) ^ 4 + 1) := by
    have := Int.natCast_dvd_natCast.2 h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at this
    exact this
  have hz2 : (p : ℤ) ∣ (Q : ℤ) ^ 2 + 1 := by exact_mod_cast hpq
  have h12 : (p : ℤ) ∣ 12 := by
    have e : (12 : ℤ) = (Q : ℤ) ^ 12 * ((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1) *
        ((Q : ℤ) ^ 8 + (Q : ℤ) ^ 4 + 1) - ((Q : ℤ) ^ 2 + 1) *
        ((Q : ℤ) ^ 26 - 2 * (Q : ℤ) ^ 24 + 3 * (Q : ℤ) ^ 22 - 5 * (Q : ℤ) ^ 20 +
          7 * (Q : ℤ) ^ 18 - 9 * (Q : ℤ) ^ 16 + 10 * (Q : ℤ) ^ 14 - 11 * (Q : ℤ) ^ 12 +
          12 * (Q : ℤ) ^ 10 - 12 * (Q : ℤ) ^ 8 + 12 * (Q : ℤ) ^ 6 - 12 * (Q : ℤ) ^ 4 +
          12 * (Q : ℤ) ^ 2 - 12) := by ring
    rw [e]
    exact dvd_sub hz (dvd_mul_of_dvd_left hz2 _)
  have h12' : p ∣ 12 := by exact_mod_cast h12
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) h12'
  interval_cases p <;> first | omega | norm_num at hp

theorem d4Q_involution_conj {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hη2 : η ^ 2 = 1)
    (hηo : η ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    ∃ e : ℕ, f = 2 * e ∧ ∃ δ : K ≃+* K, (∀ c, δ c = c ^ (ℓ ^ (3 * e))) ∧
      ∃ ψ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ψ * η * ψ⁻¹ = fieldActor σ δ := by
  classical
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  · obtain ⟨hev, δ, hδ, -, ψ, hψ, -⟩ :=
      even_triality_outer_involutions_canonical_field hf K hK σ hσ η hη2 hηo
    obtain ⟨e, he⟩ := hev
    refine ⟨e, by omega, δ, fun c => ?_, ψ, hψ⟩
    rw [hδ c]
    congr 2
    omega
  · obtain ⟨-, hNF, ⟨Θ, hΘ, -, hker, hinv⟩, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF η
    change η = MulAut.conj g * fieldActor σ δ at hgδ
    have hΘη : Θ η = δ := hΘ η g δ hgδ
    have hδ1 : Θ η ≠ 1 := fun h1 => hηo (by
      rw [← MonoidHom.mem_ker, hker] at h1
      exact h1)
    obtain ⟨hev, hδc⟩ := (hinv η hη2).resolve_left hδ1
    rw [hΘη] at hδc
    obtain ⟨e, he⟩ := hev
    have he1 : 1 ≤ e := by omega
    have hr : IsPrimePow (ℓ ^ e) := hℓ.isPrimePow.pow (by omega)
    have hro : Odd (ℓ ^ e) := (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
    have hK6 : Nat.card K = (ℓ ^ e) ^ 6 := by
      rw [hK, he, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hσ6 : ∀ c, σ c = c ^ ((ℓ ^ e) ^ 2) := fun c => by
      rw [hσ, he, ← pow_mul]
      congr 2
      omega
    have hδ3 : 3 * f / 2 = 3 * e := by omega
    have hδ6 : ∀ c, δ c = c ^ ((ℓ ^ e) ^ 3) := fun c => by
      rw [hδc c, hδ3, ← pow_mul]
      congr 2
      ring
    have hα2 : (MulAut.conj g * fieldActor σ δ) ^ 2 = 1 := by
      rw [← hgδ]
      exact hη2
    obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components hr hro K hK6
      σ hσ6 δ hδ6 g hα2
    refine ⟨e, by omega, δ, fun c => ?_, ψ, ?_⟩
    · rw [hδc c, hδ3]
    · rw [hgδ]
      exact hψ

theorem d4Q_no_outer_involution {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f + 1)
    (η : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hη2 : η ^ 2 = 1)
    (hηo : η ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hx : orderOf x = p) (hηx : η x = x) :
    False := by
  classical
  obtain ⟨e, hfe, δ, hδ, ψ, hψ⟩ := d4Q_involution_conj hℓ hf K hK σ hσ η hη2 hηo
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = ℓ ^ (3 * e * 2) := by
    rw [hK, hfe, ← pow_mul]
    congr 1
    ring
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (e * 2) := fun c => by
    rw [hσ, hfe]
    congr 2
    ring
  obtain ⟨-, -, hk0, hσ0, -, -, hFJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ he1 (le_refl 2)
      (by norm_num) K hK' σ hσ' δ hδ
  obtain ⟨F, hF⟩ : ∃ F : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      F = (fieldActor σ δ).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := ⟨_, rfl⟩
  rw [← hF] at hFJ
  have hFcard : Nat.card F = Nat.card (trialityFieldImage σ δ) := by
    rw [← hFJ, Subgroup.card_map_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective]
  have hJcard : Nat.card (trialityFieldImage σ δ) =
      Nat.card (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) := by
    unfold trialityFieldImage
    exact Subgroup.card_map_of_injective (baseChangeGL_injective _)
  have hK0 : Nat.card (fixSubfield δ) = (ℓ ^ e) ^ 3 := by
    rw [hk0, ← pow_mul, mul_comm]
  have hσ0' : ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ).toRingHom c = c ^ ((ℓ ^ e) ^ 2) := by
    intro c
    refine Subtype.ext ?_
    change (fixSubfieldRestrict σ δ c : K) = _
    rw [hσ0 c, hσ' c, SubmonoidClass.coe_pow, ← pow_mul]
  have hcard0 := (triality_both_orientations_exact_finite_order ℓ e hℓ he1 (fixSubfield δ) hK0 2
    (Or.inr rfl) (fixSubfieldRestrict σ δ).toRingHom hσ0').1
  have hy : fieldActor σ δ (ψ x) = ψ x := by
    have h1 := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
      φ (ψ x)) hψ
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    rw [← h1, hηx]
  have hyF : ψ x ∈ F := by
    rw [hF]
    exact hy
  have hord : orderOf (⟨ψ x, hyF⟩ : F) = p := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (ψ x) = p
    rw [MulEquiv.orderOf_eq, hx]
  have hdvd : p ∣ Nat.card F := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  rw [hFcard, hJcard, hcard0] at hdvd
  have hQ2 : 2 ≤ ℓ ^ e := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ e := Nat.pow_le_pow_right hℓ.pos he1
  refine d4Q_not_dvd_card_fixed hp hp3 hQ2 ?_ hdvd
  have : ℓ ^ f = (ℓ ^ e) ^ 2 := by rw [hfe, ← pow_mul, mul_comm]
  rw [← this]
  exact hpq

end CFSG.RankThree.PartOne.KGD
