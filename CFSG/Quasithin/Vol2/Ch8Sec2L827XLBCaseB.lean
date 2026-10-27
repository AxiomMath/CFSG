module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XDihedral
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCoreB
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic

public section

namespace CFSG.Quasithin.H13.L827X.LBCaseB

open CFSG.Quasithin.H13.L827X.LBCoreB

section Helpers

private theorem dihedral_general_caseB {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {n : ℕ} (hn : Odd n) (y t : Module.End (ZMod 2) W)
    (hy : y ^ n = 1) (ht : t * t = 1) (hty : t * y * t = y ^ (n - 1)) :
    Module.finrank (ZMod 2) (LinearMap.range (y - 1)) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (t - 1)) := by
  obtain ⟨d, ⟨e⟩⟩ : ∃ d : ℕ, Nonempty (W ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    ⟨_, ⟨(Module.finBasis (ZMod 2) W).equivFun⟩⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Module.End (ZMod 2) W ≃+* Module.End (ZMod 2) (Fin d → ZMod 2),
      ∀ g, Φ g = e.conj g := ⟨e.conjRingEquiv, fun g => rfl⟩
  have hrange : ∀ g : Module.End (ZMod 2) W,
      Module.finrank (ZMod 2) (LinearMap.range (Φ g)) =
        Module.finrank (ZMod 2) (LinearMap.range g) := by
    intro g
    have hmap : LinearMap.range (Φ g) =
        Submodule.map (e : W →ₗ[ZMod 2] (Fin d → ZMod 2)) (LinearMap.range g) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨g (e.symm v), ⟨e.symm v, rfl⟩, ?_⟩
        simp [hΦ]
      · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
        refine ⟨e w, ?_⟩
        simp [hΦ]
    rw [hmap, LinearEquiv.finrank_map_eq]
  have hy' : (Φ y) ^ n = 1 := by rw [← map_pow, hy, map_one]
  have ht' : Φ t * Φ t = 1 := by rw [← map_mul, ht, map_one]
  have hty' : Φ t * Φ y * Φ t = (Φ y) ^ (n - 1) := by
    rw [← map_mul, ← map_mul, hty, map_pow]
  have hdih := CFSG.Quasithin.H13.L827X.dihedral_rank_count hn (Φ y) (Φ t) hy' ht' hty'
  have e1 : Φ y - 1 = Φ (y - 1) := by rw [map_sub, map_one]
  have e2 : Φ t - 1 = Φ (t - 1) := by rw [map_sub, map_one]
  rw [e1, e2, hrange, hrange] at hdih
  exact hdih

private theorem exists_isPrimitiveRoot_galoisField_caseB (p : ℕ) [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) : ∃ ζ : GaloisField 2 (p - 1), IsPrimitiveRoot ζ p := by
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h'' := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h'
    omega
  have hferm : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hp2
  have hdvd : p ∣ 2 ^ (p - 1) - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rw [hferm, sub_self]
  have hcard : Nat.card (GaloisField 2 (p - 1)) = 2 ^ (p - 1) :=
    GaloisField.card 2 (p - 1) (by omega)
  have hdvdU : p ∣ Nat.card (GaloisField 2 (p - 1))ˣ := by
    rw [Nat.card_units, hcard]
    exact hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvdU
  refine ⟨(u : GaloisField 2 (p - 1)), ?_⟩
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hu]

private theorem finrank_range_baseChange_le_caseB {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (T : Module.End (ZMod 2) W) :
    Module.finrank F (LinearMap.range (LinearMap.baseChange F T)) ≤
      Module.finrank (ZMod 2) (LinearMap.range T) := by
  have hfac : (LinearMap.range T).subtype ∘ₗ T.rangeRestrict = T := LinearMap.ext fun _ => rfl
  have hfac2 : LinearMap.baseChange F T =
      LinearMap.baseChange F (LinearMap.range T).subtype ∘ₗ
        LinearMap.baseChange F T.rangeRestrict := by
    rw [← LinearMap.baseChange_comp, hfac]
  have hle : LinearMap.range (LinearMap.baseChange F T) ≤
      LinearMap.range (LinearMap.baseChange F (LinearMap.range T).subtype) := by
    rw [hfac2]
    exact LinearMap.range_comp_le_range _ _
  calc Module.finrank F (LinearMap.range (LinearMap.baseChange F T))
      ≤ Module.finrank F (LinearMap.range (LinearMap.baseChange F (LinearMap.range T).subtype)) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank F (TensorProduct (ZMod 2) F (LinearMap.range T)) :=
        LinearMap.finrank_range_le _
    _ = Module.finrank (ZMod 2) (LinearMap.range T) := Module.finrank_baseChange

private theorem fixed_free_baseChange_caseB {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {E : Type*} [AddCommGroup E] [Fintype E] (ρ : E → Module.End (ZMod 2) W)
    (hC : ∀ w : W, (∀ x : E, ρ x w = w) → w = 0) :
    ∀ m : TensorProduct (ZMod 2) F W,
      (∀ x : E, LinearMap.baseChange F (ρ x) m = m) → m = 0 := by
  classical
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : W →ₗ[ZMod 2] (E → W), ∀ w x, Φ w x = ρ x w - w :=
    ⟨LinearMap.pi (fun x => ρ x - 1), fun w x => by simp⟩
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hC w
    intro x
    have h : Φ w x = 0 := by simp [hw]
    rw [hΦ, sub_eq_zero] at h
    exact h
  have hΦinjF : Function.Injective (LinearMap.baseChange F Φ) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap Φ hΦinj
  have hid : ∀ (m : TensorProduct (ZMod 2) F W) (x : E),
      TensorProduct.piRight (ZMod 2) F F (fun _ : E => W) (LinearMap.baseChange F Φ m) x
        = LinearMap.baseChange F (ρ x) m - m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => intro x; simp
    | tmul f w => intro x; simp [hΦ, TensorProduct.tmul_sub]
    | add m n hm hn => intro x; simp only [map_add, Pi.add_apply, hm, hn]; abel
  intro m hm
  have h1 : TensorProduct.piRight (ZMod 2) F F (fun _ : E => W)
      (LinearMap.baseChange F Φ m) = 0 := by
    funext x
    rw [Pi.zero_apply, hid m x, hm x, sub_self]
  have h2 : LinearMap.baseChange F Φ m = 0 :=
    (TensorProduct.piRight (ZMod 2) F F (fun _ : E => W)).injective
      (h1.trans (map_zero _).symm)
  exact hΦinjF (h2.trans (map_zero _).symm)

private theorem sixteen_le_of_field_caseB {p : ℕ} [hp : Fact p.Prime]
    {F : Type*} [Field F] [Algebra (ZMod 2) F] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hpF : (p : F) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    {E : Type*} [AddCommGroup E] [Module (ZMod p) E] [Fintype E]
    (hE : Module.finrank (ZMod p) E = 2)
    {Γ : Type*} [Group Γ] [Finite Γ]
    (σ : Γ →* (E ≃ₗ[ZMod p] E)) (τ : Γ →* (W ≃ₗ[ZMod 2] W))
    (ρ : E → Module.End (ZMod 2) W) (hρ0 : ρ 0 = 1)
    (hρadd : ∀ x y, ρ (x + y) = ρ x * ρ y)
    (hcompat : ∀ (γ : Γ) (x : E),
      (τ γ : Module.End (ZMod 2) W) * ρ x = ρ (σ γ x) * (τ γ : Module.End (ZMod 2) W))
    (hC : ∀ w : W, (∀ x : E, ρ x w = w) → w = 0)
    (hO2 : ∀ f : Module.Dual (ZMod p) E, f ≠ 0 →
      24 ≤ Set.ncard {g | ∃ γ : Γ, dualAct (σ γ) f = g})
    (hO3 : ∀ f : Module.Dual (ZMod p) E, f ≠ 0 → ∀ y : E, y ≠ 0 →
      3 * Set.ncard ({g | ∃ γ : Γ, dualAct (σ γ) f = g} ∩ {g | g y = 0}) ≤
        Set.ncard {g | ∃ γ : Γ, dualAct (σ γ) f = g})
    {y : E} (hy : y ≠ 0) :
    16 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  obtain ⟨ρM, hρM⟩ : ∃ ρM : E → Module.End F (TensorProduct (ZMod 2) F W),
      ∀ x, ρM x = LinearMap.baseChange F (ρ x) :=
    ⟨fun x => LinearMap.baseChange F (ρ x), fun x => rfl⟩
  obtain ⟨τM, hτM⟩ : ∃ τM : Γ →* (TensorProduct (ZMod 2) F W ≃ₗ[F] TensorProduct (ZMod 2) F W),
      ∀ γ, ((τM γ : TensorProduct (ZMod 2) F W ≃ₗ[F] TensorProduct (ZMod 2) F W) :
          TensorProduct (ZMod 2) F W →ₗ[F] TensorProduct (ZMod 2) F W)
        = LinearMap.baseChange F ((τ γ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := by
    refine ⟨{ toFun := fun γ => (τ γ).baseChange (ZMod 2) F W W,
              map_one' := ?_, map_mul' := ?_ }, fun γ => rfl⟩
    · simp
    · intro γ δ
      simp [LinearEquiv.baseChange_mul]
  have hcompatM : ∀ (γ : Γ) (x : E),
      ((τM γ : TensorProduct (ZMod 2) F W ≃ₗ[F] TensorProduct (ZMod 2) F W) :
          TensorProduct (ZMod 2) F W →ₗ[F] TensorProduct (ZMod 2) F W) * ρM x
        = ρM (σ γ x) *
          ((τM γ : TensorProduct (ZMod 2) F W ≃ₗ[F] TensorProduct (ZMod 2) F W) :
          TensorProduct (ZMod 2) F W →ₗ[F] TensorProduct (ZMod 2) F W) := by
    intro γ x
    have h := congrArg (LinearMap.baseChange F) (hcompat γ x)
    rw [LinearMap.baseChange_mul, LinearMap.baseChange_mul] at h
    rw [hτM γ, hρM x, hρM (σ γ x)]
    exact h
  have hρ0M : ρM 0 = 1 := by
    simp only [hρM, hρ0, LinearMap.baseChange_one]
  have hρaddM : ∀ x y, ρM (x + y) = ρM x * ρM y := by
    intro x y
    simp only [hρM, hρadd, LinearMap.baseChange_mul]
  have hCM : ∀ m : TensorProduct (ZMod 2) F W, (∀ x : E, ρM x m = m) → m = 0 := by
    intro m hm
    apply fixed_free_baseChange_caseB ρ hC m
    intro x
    rw [← hρM x]
    exact hm x
  have hWpos : 0 < Module.finrank (ZMod 2) W :=
    (Module.finrank_pos_iff_of_free (ZMod 2) W).mpr inferInstance
  have hFpos : 0 < Module.finrank F (TensorProduct (ZMod 2) F W) := by
    rw [Module.finrank_baseChange]
    exact hWpos
  haveI : Nontrivial (TensorProduct (ZMod 2) F W) := Module.nontrivial_of_finrank_pos hFpos
  have hcore := core_sixteen_le hζ hpF hE σ τM ρM hρ0M hρaddM hcompatM hCM hO2 hO3 hy
  have hTM : ρM y - 1 = LinearMap.baseChange F (ρ y - 1) := by
    rw [hρM, LinearMap.baseChange_sub, LinearMap.baseChange_one]
  rw [hTM] at hcore
  exact le_trans hcore (finrank_range_baseChange_le_caseB (F := F) (ρ y - 1))

end Helpers

theorem caseB_eight_le {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    {E : Type*} [AddCommGroup E] [Module (ZMod p) E] [Fintype E]
    (hE : Module.finrank (ZMod p) E = 2)
    {Γ : Type*} [Group Γ] [Finite Γ]
    (σ : Γ →* (E ≃ₗ[ZMod p] E)) (τ : Γ →* (W ≃ₗ[ZMod 2] W))
    (ρ : E → Module.End (ZMod 2) W) (hρ0 : ρ 0 = 1) (hρadd : ∀ x y, ρ (x + y) = ρ x * ρ y)
    (hcompat : ∀ (γ : Γ) (x : E),
      (τ γ : Module.End (ZMod 2) W) * ρ x = ρ (σ γ x) * (τ γ : Module.End (ZMod 2) W))
    (hC : ∀ w : W, (∀ x : E, ρ x w = w) → w = 0)
    (hO2 : ∀ f : Module.Dual (ZMod p) E, f ≠ 0 →
      24 ≤ Set.ncard {g | ∃ γ : Γ, dualAct (σ γ) f = g})
    (hO3 : ∀ f : Module.Dual (ZMod p) E, f ≠ 0 → ∀ y : E, y ≠ 0 →
      3 * Set.ncard ({g | ∃ γ : Γ, dualAct (σ γ) f = g} ∩ {g | g y = 0}) ≤
        Set.ncard {g | ∃ γ : Γ, dualAct (σ γ) f = g})
    {y : E} (hy : y ≠ 0)
    {V : Module.End (ZMod 2) W} (hVV : V * V = 1) {g : E ≃ₗ[ZMod p] E}
    (hVg : ∀ x : E, V * ρ x = ρ (g x) * V) (hgy : g y = -y) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.range (V - 1)) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_galoisField_caseB p hp5
  have hpF : (p : GaloisField 2 (p - 1)) ≠ 0 := by
    intro h
    have h' := (CharP.cast_eq_zero_iff (GaloisField 2 (p - 1)) 2 p).mp h
    have h'' := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h'
    omega
  have h16 := sixteen_le_of_field_caseB hζ hpF hE σ τ ρ hρ0 hρadd hcompat hC hO2 hO3 hy
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hpow : ∀ (x : E) (n : ℕ), ρ (n • x) = ρ x ^ n := by
    intro x n
    induction n with
    | zero => rw [zero_nsmul, hρ0, pow_zero]
    | succ k ih => rw [succ_nsmul, hρadd, ih, pow_succ]
  have hyp : ρ y ^ p = 1 := by
    rw [← hpow y p, ← Nat.cast_smul_eq_nsmul (ZMod p) p y, ZMod.natCast_self, zero_smul, hρ0]
  have hp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hneg : (p - 1) • y = -y := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) (p - 1) y, hp1, neg_one_smul]
  have hVy : V * ρ y * V = ρ y ^ (p - 1) := by
    rw [hVg y, mul_assoc, hVV, mul_one, hgy, ← hneg, hpow]
  have hdih := dihedral_general_caseB hodd (ρ y) V hyp hVV hVy
  omega

end CFSG.Quasithin.H13.L827X.LBCaseB
