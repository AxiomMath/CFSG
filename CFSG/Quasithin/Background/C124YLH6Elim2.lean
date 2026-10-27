module

public import CFSG.Quasithin.Background.C124YLH6Elim
public import CFSG.Quasithin.Background.C124YLH6Woff
public import CFSG.Quasithin.Background.C124YLInd

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.H6

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

namespace HatCtx

variable {W : Type*} [CommGroup W] [Finite W] {K : Type} [Field K] [Finite K]
  {Γ₀ : Subgroup (GL (Fin 3) K)} {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : HatCtx K Γ₀ Ls U Z)

include C in
theorem exists_center : ∃ (z0 : ↥Γ₀) (ω : K), z0 ∈ Subgroup.center ↥Γ₀ ∧ z0 ≠ 1 ∧ z0 ^ 3 = 1 ∧
    ω ≠ 1 ∧ ω ^ 3 = 1 ∧ mat Γ₀ z0 = ω • (1 : Matrix (Fin 3) (Fin 3) K) ∧
    ∀ γ ∈ Subgroup.center ↥Γ₀, γ = 1 ∨ γ = z0 ∨ γ = z0 * z0 := by
  have h3 : Nat.card (Subgroup.center ↥Γ₀) = 3 := C.hat.2.1
  have hfin : Finite ↥(Subgroup.center ↥Γ₀) := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥(Subgroup.center ↥Γ₀) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨z0, hz0c⟩, hz01⟩ := exists_ne (1 : ↥(Subgroup.center ↥Γ₀))
  have hz01' : z0 ≠ 1 := fun h => hz01 (Subtype.ext h)
  have hz3 : z0 ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥Γ₀)) (x := ⟨z0, hz0c⟩)
    rw [h3] at h
    exact congrArg Subtype.val h
  obtain ⟨ω, hω⟩ := C.hcen z0 hz0c
  have hωm : mat Γ₀ z0 = ω • (1 : Matrix (Fin 3) (Fin 3) K) := hω
  have hω1 : ω ≠ 1 := by
    intro h
    apply hz01'
    apply mat_injective
    rw [hωm, h, one_smul, mat_one]
  have hω3 : ω ^ 3 = 1 := by
    have h := congrArg (mat Γ₀) hz3
    rw [pow_three', mat_mul, mat_mul, hωm, mat_one] at h
    have h2 := congrFun (congrFun h 0) 0
    simpa [pow_succ, mul_assoc] using h2
  refine ⟨z0, ω, hz0c, hz01', hz3, hω1, hω3, hωm, fun γ hγ => ?_⟩
  have hord : orderOf z0 = 3 := by
    have hd : orderOf z0 ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hd) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz01'
    · exact h
  have hle : Subgroup.zpowers z0 ≤ Subgroup.center ↥Γ₀ := Subgroup.zpowers_le.2 hz0c
  have hcardz : Nat.card (Subgroup.zpowers z0) = 3 := by
    rw [Nat.card_zpowers, hord]
  have heq : Subgroup.zpowers z0 = Subgroup.center ↥Γ₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardz, h3])
  rw [← heq] at hγ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hγ
  have hn' : z0 ^ n = z0 ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3, _root_.zpow_add, _root_.zpow_mul]
    have : z0 ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
    rw [this, _root_.one_zpow, mul_one]
  rw [← hn, hn']
  have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hge : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  interval_cases h : n % 3
  · left
    rfl
  · right
    left
    simp
  · right
    right
    simp [pow_two]

theorem indHom_phi {c : ↥U →* Multiplicative (Fin 3 → K)} (hc : IsCoord U Z c)
    (hequiv : ∀ (γ : ↥Γ₀) (u : ↥U) (hu : C.phi γ (u : W) ∈ U),
      c ⟨C.phi γ (u : W), hu⟩ = natAct Γ₀ γ (c u))
    {Xs : Subgroup (MulAut W)} (hLX : Ls ≤ Xs) (hU : ∀ x ∈ Xs, ∀ u, u ∈ U ↔ x u ∈ U)
    (hZ : ∀ x ∈ Xs, ∀ z, z ∈ Z ↔ x z ∈ Z) (γ : ↥Γ₀) :
    indHom hc Xs hU hZ ⟨C.phi γ, hLX (C.phi_mem γ)⟩ = actHom γ := by
  refine MonoidHom.ext fun q => ?_
  obtain ⟨u, rfl⟩ := hc.surj q
  exact (indHom_apply hc Xs hU hZ _ u).trans (hequiv γ u (C.phi_stab γ u u.2))

theorem conj_center {Xs : Subgroup (MulAut W)} (hnorm : ∀ x ∈ Xs, x ∈ Subgroup.normalizer
      (Ls : Set (MulAut W))) {z0 : ↥Γ₀} (hz0 : z0 ∈ Subgroup.center ↥Γ₀) (hz01 : z0 ≠ 1)
    {r : MulAut W} (hr : r ∈ Xs) :
    ∃ γ' : ↥Γ₀, γ' ∈ Subgroup.center ↥Γ₀ ∧ γ' ≠ 1 ∧ r * C.phi z0 * r⁻¹ = C.phi γ' := by
  have hφ := C.phi_injective
  have hrN := Subgroup.mem_normalizer_iff.1 (hnorm r hr)
  have hrN' := Subgroup.mem_normalizer_iff.1 (hnorm r⁻¹ (Xs.inv_mem hr))
  have hyL : r * C.phi z0 * r⁻¹ ∈ Ls := (hrN _).1 (C.phi_mem z0)
  obtain ⟨γ', hγ'⟩ : r * C.phi z0 * r⁻¹ ∈ C.phi.range := C.phi_range.ge hyL
  refine ⟨γ', ?_, ?_, hγ'.symm⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    apply hφ
    rw [map_mul, map_mul, hγ']
    have hl : r⁻¹ * C.phi g * r ∈ Ls := by
      have := (hrN' (C.phi g)).1 (C.phi_mem g)
      simpa using this
    obtain ⟨g', hg'⟩ : r⁻¹ * C.phi g * r ∈ C.phi.range := C.phi_range.ge hl
    have hz : C.phi z0 * C.phi g' = C.phi g' * C.phi z0 := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz0 g']
    have e1 : C.phi g = r * C.phi g' * r⁻¹ := by
      rw [hg']
      group
    calc C.phi g * (r * C.phi z0 * r⁻¹) = r * (C.phi g' * C.phi z0) * r⁻¹ ^ 2 * r := by
          rw [e1]
          group
      _ = (r * C.phi z0 * r⁻¹) * C.phi g := by
          rw [← hz, e1]
          group
  · intro h
    rw [h, map_one] at hγ'
    apply hz01
    apply hφ
    have : C.phi z0 = r⁻¹ * (r * C.phi z0 * r⁻¹) * r := by group
    rw [this, ← hγ', map_one]
    group

end HatCtx

end CFSG.Quasithin.C124.YL.H6
