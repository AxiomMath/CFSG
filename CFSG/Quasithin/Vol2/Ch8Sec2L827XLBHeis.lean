module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.Quasithin.H13.L827X.LBHeis

section Helpers

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

private noncomputable def specProj (p : ℕ) (z : F) (A : Module.End F M) : Module.End F M :=
  (p : F)⁻¹ • ∑ i ∈ Finset.range p, (z⁻¹ • A) ^ i

private theorem specProj_mul_eig {p : ℕ} {z : F} (hz : z ≠ 0) (hzp : z ^ p = 1)
    {A : Module.End F M} (hA : A ^ p = 1) :
    (A - z • 1) * specProj p z A = 0 := by
  have hx : (z⁻¹ • A) ^ p = 1 := by
    rw [smul_pow, inv_pow, hzp, inv_one, hA, one_smul]
  have hgeom := mul_neg_geom_sum (z⁻¹ • A) p
  rw [hx, sub_self] at hgeom
  have hfac : A - z • (1 : Module.End F M) = z • (z⁻¹ • A - 1) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have h2 : (z⁻¹ • A - 1) * ∑ i ∈ Finset.range p, (z⁻¹ • A) ^ i = 0 := by
    rw [← neg_sub 1 (z⁻¹ • A), neg_mul, hgeom, neg_zero]
  unfold specProj
  rw [mul_smul_comm, hfac, smul_mul_assoc, h2, smul_zero, smul_zero]

private theorem specProj_apply_eig {p : ℕ} {z : F} (hz : z ≠ 0) (hzp : z ^ p = 1)
    {A : Module.End F M} (hA : A ^ p = 1) (m : M) :
    A (specProj p z A m) = z • specProj p z A m := by
  have h := congrArg (fun f : Module.End F M => f m) (specProj_mul_eig hz hzp hA)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, LinearMap.zero_apply] at h
  exact sub_eq_zero.mp h

private theorem sum_specProj {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (A : Module.End F M) :
    ∑ k ∈ Finset.range p, specProj p (ζ ^ k) A = 1 := by
  unfold specProj
  simp only [smul_pow]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hzero : ∀ b ∈ Finset.range p, b ≠ 0 →
      (∑ k ∈ Finset.range p, ((ζ ^ k)⁻¹) ^ b) • A ^ b = 0 := by
    intro b hb hb0
    have hbp : b < p := Finset.mem_range.mp hb
    have hb0' : 0 < b := Nat.pos_of_ne_zero hb0
    have hcop : Nat.Coprime b p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt hb0' hbp))
    have hprim : IsPrimitiveRoot (ζ ^ b)⁻¹ p := (hζ.pow_of_coprime b hcop).inv
    have hrw : ∀ k : ℕ, ((ζ ^ k)⁻¹) ^ b = ((ζ ^ b)⁻¹) ^ k := by
      intro k
      rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
    have hsum : ∑ k ∈ Finset.range p, ((ζ ^ k)⁻¹) ^ b = 0 := by
      simp only [hrw]
      exact hprim.geom_sum_eq_zero hp.one_lt
    rw [hsum, zero_smul]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hp.pos) hzero]
  have h0 : ∑ k ∈ Finset.range p, ((ζ ^ k)⁻¹) ^ 0 = (p : F) := by simp
  rw [h0, pow_zero, smul_smul, inv_mul_cancel₀ hpF, one_smul]

private theorem comm_pow {ζ : F} {A B : Module.End F M} (hAB : A * B = ζ • (B * A))
    (n : ℕ) : A * B ^ n = (ζ ^ n) • (B ^ n * A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc A * B ^ (n + 1) = (A * B ^ n) * B := by rw [pow_succ, mul_assoc]
      _ = (ζ ^ n) • ((B ^ n * A) * B) := by rw [ih, smul_mul_assoc]
      _ = (ζ ^ n) • (B ^ n * (A * B)) := by rw [mul_assoc]
      _ = (ζ ^ n) • (B ^ n * (ζ • (B * A))) := by rw [hAB]
      _ = (ζ ^ n) • (ζ • (B ^ n * (B * A))) := by rw [mul_smul_comm]
      _ = (ζ ^ (n + 1)) • (B ^ (n + 1) * A) := by
        rw [smul_smul, ← pow_succ, ← mul_assoc, ← pow_succ]

private theorem mem_eigenspace_pow {ζ : F} {A B : Module.End F M} (hAB : A * B = ζ • (B * A))
    (n : ℕ) {μ : F} {x : M} (hx : x ∈ Module.End.eigenspace A μ) :
    (B ^ n) x ∈ Module.End.eigenspace A (ζ ^ n * μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have h := congrArg (fun f : Module.End F M => f x) (comm_pow hAB n)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [h, hx, map_smul, smul_smul]

private theorem injective_pow {p : ℕ} {B : Module.End F M} (hB : B ^ p = 1) {n : ℕ}
    (hn : n ≤ p) : Function.Injective (B ^ n) := by
  intro x y hxy
  have h1 : ∀ z : M, (B ^ (p - n)) ((B ^ n) z) = z := fun z => by
    rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hn, hB, Module.End.one_apply]
  calc x = (B ^ (p - n)) ((B ^ n) x) := (h1 x).symm
    _ = (B ^ (p - n)) ((B ^ n) y) := by rw [hxy]
    _ = y := h1 y

private theorem finrank_eigenspace_mul [FiniteDimensional F M] {p : ℕ} (hp : p.Prime)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {A B : Module.End F M} (hB : B ^ p = 1)
    (hAB : A * B = ζ • (B * A)) (μ : F) :
    Module.finrank F (Module.End.eigenspace A μ) =
      Module.finrank F (Module.End.eigenspace A (ζ * μ)) := by
  have hBinj : Function.Injective B := by
    simpa using injective_pow hB hp.one_lt.le
  apply le_antisymm
  · have hmem : ∀ x ∈ Module.End.eigenspace A μ, B x ∈ Module.End.eigenspace A (ζ * μ) := by
      intro x hx
      simpa using mem_eigenspace_pow hAB 1 hx
    refine LinearMap.finrank_le_finrank_of_injective (f := B.restrict hmem) ?_
    intro x y hxy
    apply Subtype.ext
    apply hBinj
    have := congrArg Subtype.val hxy
    simpa using this
  · have hz : ζ ^ (p - 1) * ζ = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hζ.pow_eq_one]
    have hmem : ∀ x ∈ Module.End.eigenspace A (ζ * μ),
        (B ^ (p - 1)) x ∈ Module.End.eigenspace A μ := by
      intro x hx
      have h := mem_eigenspace_pow hAB (p - 1) hx
      rwa [← mul_assoc, hz, one_mul] at h
    refine LinearMap.finrank_le_finrank_of_injective (f := (B ^ (p - 1)).restrict hmem) ?_
    intro x y hxy
    apply Subtype.ext
    apply injective_pow hB (Nat.sub_le p 1)
    have := congrArg Subtype.val hxy
    simpa using this

private theorem finrank_eigenspace_pow [FiniteDimensional F M] {p : ℕ} (hp : p.Prime)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {A B : Module.End F M} (hB : B ^ p = 1)
    (hAB : A * B = ζ • (B * A)) (k : ℕ) :
    Module.finrank F (Module.End.eigenspace A (ζ ^ k)) =
      Module.finrank F (Module.End.eigenspace A 1) := by
  induction k with
  | zero => rw [pow_zero]
  | succ k ih =>
    rw [pow_succ', ← finrank_eigenspace_mul hp hζ hB hAB (ζ ^ k)]
    exact ih

end Helpers

theorem heis_finrank_ker_mul {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {A B : Module.End F M}
    (hA : A ^ p = 1) (hB : B ^ p = 1) (hAB : A * B = ζ • (B * A)) :
    p * Module.finrank F (LinearMap.ker (A - 1)) = Module.finrank F M := by
  have hζne : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpow : ∀ k : ℕ, (ζ ^ k) ^ p = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hinj : Function.Injective (fun k : Fin p => ζ ^ (k : ℕ)) := by
    intro i j hij
    exact Fin.ext (hζ.pow_inj i.isLt j.isLt hij)
  have hind : iSupIndep (fun k : Fin p => Module.End.eigenspace A (ζ ^ (k : ℕ))) :=
    (Module.End.eigenspaces_iSupIndep A).comp hinj
  have hspan : (⨆ k : Fin p, Module.End.eigenspace A (ζ ^ (k : ℕ))) = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have h1 : ∑ k : Fin p, specProj p (ζ ^ (k : ℕ)) A m =
        ∑ k ∈ Finset.range p, specProj p (ζ ^ k) A m :=
      Fin.sum_univ_eq_sum_range (fun k => specProj p (ζ ^ k) A m) p
    have h2 : (∑ k ∈ Finset.range p, specProj p (ζ ^ k) A) m =
        ∑ k ∈ Finset.range p, specProj p (ζ ^ k) A m :=
      LinearMap.sum_apply _ _ _
    rw [sum_specProj hp hpF hζ A, Module.End.one_apply] at h2
    have hm : ∑ k : Fin p, specProj p (ζ ^ (k : ℕ)) A m = m := by
      rw [h1, ← h2]
    rw [← hm]
    refine Submodule.sum_mem _ (fun k _ => Submodule.mem_iSup_of_mem k ?_)
    exact Module.End.mem_eigenspace_iff.mpr
      (specProj_apply_eig (pow_ne_zero _ hζne) (hpow k) hA m)
  have hint : DirectSum.IsInternal
      (fun k : Fin p => Module.End.eigenspace A (ζ ^ (k : ℕ))) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hind, hspan⟩
  have hfin := LinearEquiv.finrank_eq
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (fun k : Fin p => Module.End.eigenspace A (ζ ^ (k : ℕ)))) hint)
  rw [Module.finrank_directSum] at hfin
  have hconst : ∀ k : Fin p, Module.finrank F (Module.End.eigenspace A (ζ ^ (k : ℕ))) =
      Module.finrank F (Module.End.eigenspace A 1) :=
    fun k => finrank_eigenspace_pow hp hζ hB hAB k
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hfin
  have hker : LinearMap.ker (A - 1) = Module.End.eigenspace A 1 := by
    ext x
    simp [Module.End.mem_eigenspace_iff, sub_eq_zero]
  rw [hker]
  exact hfin

end CFSG.Quasithin.H13.L827X.LBHeis
