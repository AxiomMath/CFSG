module

public import CFSG.Quasithin.Vol2.GoldschmidtH11OutAux
public import CFSG.Quasithin.Vol2.GoldschmidtH11Hilb
public import CFSG.Quasithin.Vol2.GoldschmidtH11Schur
public import CFSG.Quasithin.Vol2.GoldschmidtH11TauL

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

omit [Finite F] [CharP F 2] in
theorem sl_map_map (ψ χ : F ≃+* F) (γ : SL(2, F)) :
    Matrix.SpecialLinearGroup.map ψ.toRingHom (Matrix.SpecialLinearGroup.map χ.toRingHom γ) =
      Matrix.SpecialLinearGroup.map (ψ * χ).toRingHom γ := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem outer_involution (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) (t : MulAut (HV F a))
    (ht2 : t * t = 1) (htn : t ∈ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a))))
    (htL : t ∉ Lh a h) : ∃ ℓ ∈ Lh a h, t = ℓ * tauAut a h * ℓ⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h1 : ∀ x : SL(2, F), ∃ y, actHom a h y = t * actHom a h x * t⁻¹ := fun x =>
    (Subgroup.mem_normalizer_iff.mp htn _).mp (actHom_mem_Lh x)
  have h2 : ∀ x : SL(2, F), ∃ y, actHom a h y = t⁻¹ * actHom a h x * t := fun x => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem htn) _).mp
      (actHom_mem_Lh x)
    rw [inv_inv] at this
    exact this
  obtain ⟨θ, hθ⟩ := exists_conj_aut (actHom a h) (actHom_injective a h) t h1 h2
  obtain ⟨ψ, h₀, hθf⟩ := exists_aut_formula θ
  have hθ2 : ∀ γ, θ (θ γ) = γ := fun γ => by
    apply actHom_injective a h
    rw [hθ, hθ, ht']
    calc t * (t * actHom a h γ * t) * t = (t * t) * actHom a h γ * (t * t) := by group
      _ = actHom a h γ := by rw [ht2]; simp
  obtain ⟨hψ, hz⟩ := eq_one_of_aut_formula (ψ * ψ)
    (h₀ * Matrix.SpecialLinearGroup.map ψ.toRingHom h₀) (fun γ => by
      have e : θ (θ γ) = (h₀ * Matrix.SpecialLinearGroup.map ψ.toRingHom h₀) *
          Matrix.SpecialLinearGroup.map (ψ * ψ).toRingHom γ *
          (h₀ * Matrix.SpecialLinearGroup.map ψ.toRingHom h₀)⁻¹ := by
        rw [hθf (θ γ), hθf γ]
        simp only [map_mul, map_inv, sl_map_map, mul_inv_rev, mul_assoc]
      rw [← e, hθ2])
  set T1 : MulAut (HV F a) := actHom a h h₀ * fieldAut a ψ with hT1
  have hT1c : ∀ γ, T1 * actHom a h γ * T1⁻¹ = t * actHom a h γ * t⁻¹ := fun γ => by
    rw [← hθ, hθf]
    calc T1 * actHom a h γ * T1⁻¹ = actHom a h h₀ * (fieldAut a ψ * actHom a h γ *
          (fieldAut a ψ)⁻¹) * (actHom a h h₀)⁻¹ := by rw [hT1]; group
      _ = _ := by rw [fieldAut_conj_actHom]; simp only [map_mul, map_inv]
  have hcomm : ∀ γ, (T1⁻¹ * t) * actHom a h γ = actHom a h γ * (T1⁻¹ * t) := fun γ => by
    calc (T1⁻¹ * t) * actHom a h γ = T1⁻¹ * (t * actHom a h γ * t⁻¹) * t := by group
      _ = T1⁻¹ * (T1 * actHom a h γ * T1⁻¹) * t := by rw [hT1c]
      _ = actHom a h γ * (T1⁻¹ * t) := by group
  obtain ⟨k, hkσ, hk⟩ := schur ha h (T1⁻¹ * t) (fun γ v => by
    have := congrArg (fun z : MulAut (HV F a) => z v) (hcomm γ)
    simpa using this)
  set c : MulAut (HV F a) := T1⁻¹ * t with hc
  have htc : t = T1 * c := by rw [hc]; group
  have hψk : ψ k = k := by
    rcases eq_one_or_eq_sgEquiv ha h ψ hψ with rfl | rfl
    · rfl
    · exact hkσ
  have hcψ := scalar_comm_fieldAut ψ k hψk c hk
  have hcπ : c * actHom a h h₀ = actHom a h h₀ * c := hcomm h₀
  have hcT1 : c * T1 = T1 * c := by
    rw [hT1, ← mul_assoc, hcπ, mul_assoc, hcψ, mul_assoc]
  have hT1sq : T1 * T1 = 1 := sq_actHom_mul_fieldAut_eq_one ψ h₀ hψ hz
  have hc2 : c * c = 1 := by
    calc c * c = T1 * T1 * (c * c) := by rw [hT1sq, one_mul]
      _ = T1 * (T1 * c) * c := by group
      _ = T1 * (c * T1) * c := by rw [hcT1]
      _ = (T1 * c) * (T1 * c) := by group
      _ = t * t := by rw [← htc]
      _ = 1 := ht2
  have hkk : k * k = 1 := by
    have e := congrArg (fun z : MulAut (HV F a) => hm a (z (e11 h))) hc2
    simp only [MulAut.mul_apply, hk, MulAut.one_apply, smul_smul, hm_e11] at e
    have := congrFun (congrFun e 0) 0
    simpa using this
  have hc1 : c = 1 := scalar_eq_one hkk c hk
  have htT : t = T1 := by rw [htc, hc1, mul_one]
  rcases eq_one_or_eq_sgEquiv ha h ψ hψ with hψ1 | hψσ
  · exfalso
    apply htL
    rw [htT, hT1, hψ1, fieldAut_one, mul_one]
    exact actHom_mem_Lh h₀
  · subst hψσ
    obtain ⟨k₂, hk₂⟩ := hilbert90 ha h h₀ hz
    refine ⟨actHom a h k₂, actHom_mem_Lh k₂, ?_⟩
    have e1 : actHom a h (sgMap h k₂) =
        tauAut a h * actHom a h k₂ * (tauAut a h)⁻¹ := (tau_conj_actHom h k₂).symm
    calc t = T1 := htT
      _ = actHom a h h₀ * tauAut a h := rfl
      _ = actHom a h (k₂ * (sgMap h k₂)⁻¹) * tauAut a h := by rw [← hk₂]
      _ = _ := by rw [map_mul, map_inv, e1]; group

end CFSG.Quasithin.H11
