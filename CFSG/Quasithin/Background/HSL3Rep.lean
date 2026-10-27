module

public import CFSG.Quasithin.Background.HSL3S77Model
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModules
public import CFSG.Quasithin.Background.HSL3Six

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H.SL3Rep

open Matrix Module CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

theorem finrank_V3 : finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by simp

theorem card_SL3 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

instance finite_linearEquiv : Finite ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  Finite.of_injective (fun f : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) =>
    (f : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))) fun _ _ h => LinearEquiv.toEquiv_injective h

@[expose] noncomputable def iota :
    SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toLin'
    (Matrix.SpecialLinearGroup.toLin'_injective.bijective_of_nat_card_le (by
      rw [card_SL3, natCard_linearEquiv finrank_V3]))

theorem iota_apply (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    iota g v = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := by
  show Matrix.SpecialLinearGroup.toLin' g v = _
  exact Matrix.SpecialLinearGroup.toLin'_apply g v

@[expose] noncomputable def tauT : SpecialLinearGroup (Fin 3) (ZMod 2) →*
    SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun g := ⟨((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ,
    by rw [Matrix.det_transpose]; exact (g⁻¹).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    show (((g * h)⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
        ((h⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

theorem coe_tauT (g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((tauT g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := rfl

@[expose] def c7 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def c7' : Matrix (Fin 3) (Fin 3) (ZMod 2) := (SL3Six.mul3 c7 c7 + 1)ᵀ

theorem c7_mul_inv : SL3Six.mul3 c7 (SL3Six.mul3 c7 c7 + 1) = 1 := by decide

@[expose] def det3 (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ZMod 2 :=
  M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 +
    M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0

theorem det3_eq (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : det3 M = M.det := by
  rw [Matrix.det_fin_three]
  rfl

theorem not_conj_c7 : ∀ P : Matrix (Fin 3) (Fin 3) (ZMod 2),
    SL3Six.mul3 P c7 = SL3Six.mul3 c7' P → det3 P = 0 := by
  decide +kernel

theorem not_inner_tauT (P : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ¬ ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2), P * g * P⁻¹ = tauT g := by
  intro h
  set c : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨c7, by decide⟩ with hc
  have h1 := h c
  have h2 : (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) * c7 = c7' * P := by
    have e := congrArg (fun A : SpecialLinearGroup (Fin 3) (ZMod 2) =>
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * P) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tauT] at e
    have e1 : ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)) * c7 *
        ((P⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) * P =
        (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) * c7 := by
      rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, mul_one]
    have e2 : ((c⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        SL3Six.mul3 c7 c7 + 1 := by
      have h3 : (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (SL3Six.mul3 c7 c7 + 1) = 1 := by
        rw [← SL3Six.mul3_eq]
        exact c7_mul_inv
      calc ((c⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
          = ((c⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
            ((c : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (SL3Six.mul3 c7 c7 + 1)) := by
              rw [h3, mul_one]
        _ = SL3Six.mul3 c7 c7 + 1 := by
              rw [← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                Matrix.SpecialLinearGroup.coe_one, one_mul]
    rw [← e1, e, e2]
    rfl
  have h3 := not_conj_c7 P (by rw [SL3Six.mul3_eq, SL3Six.mul3_eq]; exact h2)
  rw [det3_eq, P.2] at h3
  exact one_ne_zero h3

theorem natCard_eq_two_pow (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] [Finite E] :
    Nat.card E = 2 ^ finrank (ZMod 2) E := by
  classical
  let _ : Fintype E := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := E), ZMod.card]

theorem card_fix_eq_two {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (hU : Nat.card U = 8) (f : U ≃ₗ[ZMod 2] U) (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1) :
    Nat.card {u : U // f u = u} = 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Gf := Subgroup.zpowers f with hGf
  have hG : IsPGroup 3 Gf := fun g => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    have hg3 : (g : U ≃ₗ[ZMod 2] U) ^ 3 = 1 := by
      rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hf3,
        _root_.one_zpow]
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hg3
  have h1 := hG.card_modEq_card_fixedPoints U
  have hfix : MulAction.fixedPoints Gf U = {u : U | f u = u} := by
    ext u
    simp only [MulAction.mem_fixedPoints, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact h ⟨f, Subgroup.mem_zpowers f⟩
    · intro h g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      have hfk : ∀ n : ℤ, (f ^ n) u = u := by
        intro n
        induction n using Int.induction_on with
        | zero => simp
        | succ n ih =>
          rw [_root_.zpow_add_one, LinearEquiv.mul_apply, h, ih]
        | pred n ih =>
          have h2 : f.symm u = u := by
            conv_lhs => rw [← h]
            exact f.symm_apply_apply u
          rw [_root_.zpow_sub_one, LinearEquiv.mul_apply]
          have : ((f⁻¹ : U ≃ₗ[ZMod 2] U) : U → U) u = u := h2
          rw [this, ih]
      show (g : U ≃ₗ[ZMod 2] U) u = u
      rw [← hk]
      exact hfk k
  set K : Submodule (ZMod 2) U := LinearMap.ker (f.toLinearMap - LinearMap.id) with hK
  have hKeq : ∀ u, u ∈ K ↔ f u = u := fun u => by
    rw [hK, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero]
  have hcardK : Nat.card {u : U // f u = u} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => (hKeq u).symm)
  have h2 : Nat.card (MulAction.fixedPoints Gf U) = Nat.card K := by
    rw [hfix, ← hcardK]
    rfl
  rw [h2, hU] at h1
  have h3 : Nat.card K ∣ 8 := by
    rw [← hU]
    exact K.toAddSubgroup.card_addSubgroup_dvd_card
  have h4 : Nat.card K ≠ 8 := by
    intro h
    apply hf1
    have hKtop : K.toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by
      rw [show Nat.card K.toAddSubgroup = Nat.card K from rfl, h, hU])
    ext u
    have hu : u ∈ K.toAddSubgroup := hKtop ▸ AddSubgroup.mem_top u
    have := (hKeq u).1 hu
    simpa using this
  rw [hcardK]
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card K ∣ 2 ^ 3 from h3)
  rw [hk'] at h1 h4 ⊢
  interval_cases k
  · simp [Nat.ModEq] at h1
  · rfl
  · simp [Nat.ModEq] at h1
  · simp at h4

theorem false_of_twist {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (hU : Nat.card U = 8) (ψ : SpecialLinearGroup (Fin 3) (ZMod 2) →* (U ≃ₗ[ZMod 2] U))
    (hψ : Function.Injective ψ) (g₁ : SpecialLinearGroup (Fin 3) (ZMod 2))
    (τ : U ≃ₗ[ZMod 2] U) (hτ : ∀ g, τ * ψ g * τ⁻¹ = ψ (tauT (g₁ * g * g₁⁻¹))) : False := by
  have hfr : finrank (ZMod 2) U = 3 := by
    have h : 2 ^ finrank (ZMod 2) U = 2 ^ 3 := by rw [← natCard_eq_two_pow, hU]; norm_num
    exact Nat.pow_right_injective le_rfl h
  have : Finite (U ≃ₗ[ZMod 2] U) := Finite.of_injective (fun f : U ≃ₗ[ZMod 2] U =>
    (f : U ≃ U)) fun _ _ h => LinearEquiv.toEquiv_injective h
  have hbij : Function.Bijective ψ := hψ.bijective_of_nat_card_le (by
    rw [natCard_linearEquiv hfr, card_SL3])
  obtain ⟨P, hP⟩ := hbij.2 τ
  apply not_inner_tauT (P * g₁⁻¹)
  intro g
  apply hψ
  have h1 := hτ (g₁⁻¹ * g * g₁)
  rw [← hP, ← map_inv, ← map_mul, ← map_mul] at h1
  have e : g₁ * (g₁⁻¹ * g * g₁) * g₁⁻¹ = g := by group
  rw [e] at h1
  rw [show P * g₁⁻¹ * g * (P * g₁⁻¹)⁻¹ = P * (g₁⁻¹ * g * g₁) * P⁻¹ by group]
  exact h1

theorem card_comm_th0 : (Finset.univ.filter fun M : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    SL3Six.mul3 M (S77.th0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      SL3Six.mul3 (S77.th0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) M).card = 8 := by
  decide +kernel

instance finite_end : Finite (Module.End (ZMod 2) (Fin 3 → ZMod 2)) :=
  Finite.of_injective (fun f : Module.End (ZMod 2) (Fin 3 → ZMod 2) =>
    (f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective

instance finite_dual : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) (Fin 3 → ZMod 2) =>
    (f : (Fin 3 → ZMod 2) → ZMod 2)) DFunLike.coe_injective

theorem card_eq_eight_or {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (ρ : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) E)
    (hρ : ρ.IsIrreducible) (hnt : ∃ g v, ρ g v ≠ v) :
    Nat.card E = 8 ∨ 16 * Nat.card {v : E // ρ (iota S77.th0) v = v} ≤ Nat.card E := by
  classical
  let _ : Fintype (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) := Fintype.ofFinite _
  rcases exists_equiv_model finrank_V3 ρ hρ with h | h | h | h
  · exfalso
    obtain ⟨φ⟩ := h
    obtain ⟨g, v, hgv⟩ := hnt
    apply hgv
    apply φ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v
    rw [trivRep_apply] at h1
    exact h1
  · left
    obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toLinearEquiv.toEquiv, natCard_eq_two_pow, finrank_V3]
    norm_num
  · left
    obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toLinearEquiv.toEquiv, natCard_eq_two_pow, Subspace.dual_finrank_eq,
      finrank_V3]
    norm_num
  · right
    obtain ⟨φ⟩ := h
    have hE : Nat.card E = 256 := by
      rw [Nat.card_congr φ.toLinearEquiv.toEquiv, natCard_eq_two_pow,
        finrank_traceZeroEnd finrank_V3]
      norm_num
    rw [hE]
    set g₀ := iota S77.th0 with hg₀
    have hg₀m : LinearMap.toMatrix' (g₀ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) =
        (S77.th0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      have : (g₀ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) =
          Matrix.toLin' (S77.th0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl
      rw [this, LinearMap.toMatrix'_toLin']
    have hfix : Nat.card {v : E // ρ g₀ v = v} ≤ 8 := by
      rw [← card_comm_th0, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective (fun v => ⟨LinearMap.toMatrix'
        ((φ v.1 : traceZeroEnd (Fin 3 → ZMod 2)) : Module.End (ZMod 2) (Fin 3 → ZMod 2)), ?_⟩) ?_
      · have h1 := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g₀ v.1
        rw [v.2] at h1
        set X : Module.End (ZMod 2) (Fin 3 → ZMod 2) :=
          ((φ v.1 : traceZeroEnd (Fin 3 → ZMod 2)) : Module.End (ZMod 2) (Fin 3 → ZMod 2))
          with hX
        have h2 : X = (g₀ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) ∘ₗ X ∘ₗ
            (g₀.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) := by
          have h4 := congrArg (fun Y : traceZeroEnd (Fin 3 → ZMod 2) =>
            (Y : Module.End (ZMod 2) (Fin 3 → ZMod 2))) h1
          rw [adjRep_apply] at h4
          exact h4
        have h3 : X ∘ₗ (g₀ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) =
            (g₀ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) ∘ₗ X := by
          conv_lhs => rw [h2]
          ext w
          simp
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [SL3Six.mul3_eq, SL3Six.mul3_eq, ← hg₀m, ← LinearMap.toMatrix'_comp,
          ← LinearMap.toMatrix'_comp, h3]
      · intro v w hvw
        have h1 := congrArg Subtype.val hvw
        simp only at h1
        exact Subtype.ext (φ.toLinearEquiv.injective (Subtype.ext
          (LinearMap.toMatrix'.injective h1)))
    omega

end CFSG.Quasithin.H.SL3Rep
