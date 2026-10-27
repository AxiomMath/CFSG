module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTvARatio

public section

namespace CFSG.StandardType.LinTvA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.Assembly TableB TypeA TypeANbrDvd

variable {d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
  {ψ : L' →* projectiveSL d K} {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem conjAut_apply_psi {A₀ : GL (Fin d) K} (hφ's : Function.Surjective φ')
    (hcompat : ∀ s, ψ (φ' s) =
      proj d K (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ s))
    {b : MulAut L'} {D : GL (Fin d) K}
    (hb : ∀ s, b (φ' s) = φ' (CatalogueBHigherLinearAction.slConjugation d K D s)) (l : L') :
    conjAut d K (A₀⁻¹ * D * A₀) (ψ l) = ψ (b l) := by
  obtain ⟨s, rfl⟩ := hφ's l
  rw [hb, hcompat, hcompat, conjAut_proj]
  congr 1
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

theorem conjAut_rel {A₀ : GL (Fin d) K} (hψs : Function.Surjective ψ)
    (hφ's : Function.Surjective φ')
    (hcompat : ∀ s, ψ (φ' s) =
      proj d K (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ s))
    {α b : MulAut L'} {φα : MulAut (projectiveSL d K)} (hφα : ∀ l, φα (ψ l) = ψ (α l))
    {D D' : GL (Fin d) K}
    (hb : ∀ s, b (φ' s) = φ' (CatalogueBHigherLinearAction.slConjugation d K D s))
    (hb' : ∀ s, (α * b * α⁻¹) (φ' s) =
      φ' (CatalogueBHigherLinearAction.slConjugation d K D' s)) :
    conjAut d K D' = (conjAut d K A₀ * φα * (conjAut d K A₀)⁻¹) * conjAut d K D *
      (conjAut d K A₀ * φα * (conjAut d K A₀)⁻¹)⁻¹ := by
  have hx := conjAut_apply_psi hφ's hcompat hb
  have hx' := conjAut_apply_psi hφ's hcompat hb'
  have hxx' : conjAut d K (A₀⁻¹ * D' * A₀) = φα * conjAut d K (A₀⁻¹ * D * A₀) * φα⁻¹ := by
    ext r
    obtain ⟨l, rfl⟩ := hψs r
    have h1 : ψ (α⁻¹ l) = φα⁻¹ (ψ l) := by
      apply φα.injective
      rw [hφα, MulAut.apply_inv_self]
      simp
    rw [hx' l]
    show ψ (α (b (α⁻¹ l))) = φα (conjAut d K (A₀⁻¹ * D * A₀) (φα⁻¹ (ψ l)))
    rw [← h1, hx, hφα]
  have e1 : ∀ E : GL (Fin d) K, conjAut d K E =
      conjAut d K A₀ * conjAut d K (A₀⁻¹ * E * A₀) * (conjAut d K A₀)⁻¹ := by
    intro E
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [e1 D', e1 D, hxx']
  group

theorem matrix_rel_of_conjAut_eq [Finite K] (M D' Dσ : GL (Fin d) K) {t' v : Fin d → K}
    (hD' : (D' : Matrix (Fin d) (Fin d) K) = diagonal t')
    (hDσ : (Dσ : Matrix (Fin d) (Fin d) K) = diagonal v)
    (h : conjAut d K D' = conjAut d K (M * Dσ * M⁻¹)) :
    ∃ c : K, (M : Matrix (Fin d) (Fin d) K) * diagonal v =
      diagonal (fun k => t' k * c) * (M : Matrix (Fin d) (Fin d) K) := by
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one (A := D'⁻¹ * (M * Dσ * M⁻¹))
    (by rw [map_mul, map_inv, h, inv_mul_cancel])
  refine ⟨c, ?_⟩
  have e : (M * Dσ : GL (Fin d) K) = D' * (D'⁻¹ * (M * Dσ * M⁻¹)) * M := by group
  have h2 : (M : Matrix (Fin d) (Fin d) K) * (Dσ : Matrix (Fin d) (Fin d) K) =
      (D' : Matrix (Fin d) (Fin d) K) * scalar (Fin d) c * (M : Matrix (Fin d) (Fin d) K) := by
    rw [← Units.val_mul, e, Units.val_mul, Units.val_mul, hc]
  rw [hDσ, hD', scalar_apply, diagonal_mul_diagonal] at h2
  exact h2

variable [Finite K] [CharP K 2]

theorem exists_normal_form (hd : 3 ≤ d) (φt : MulAut (projectiveSL d K)) :
    ∃ (M : GL (Fin d) K) (u : K →* K), Function.Injective u ∧
      ∀ (D D' : GL (Fin d) K) (t t' : Fin d → K), (D : Matrix (Fin d) (Fin d) K) = diagonal t →
        (D' : Matrix (Fin d) (Fin d) K) = diagonal t' →
        conjAut d K D' = φt * conjAut d K D * φt⁻¹ →
        ∃ c : K, (M : Matrix (Fin d) (Fin d) K) * diagonal (fun k => u (t k)) =
          diagonal (fun k => t' k * c) * (M : Matrix (Fin d) (Fin d) K) := by
  obtain ⟨M, σ, ε, hε, hφt⟩ := (automorphism_generation (K := K) hd).2 φt
  have htrans := standard_automorphism_transport (K := K) (n := d)
  have hδ : (dualAut d K)⁻¹ = dualAut d K := inv_eq_of_mul_eq_one_right htrans.2.2.2.1
  refine ⟨M, ?_⟩
  interval_cases ε
  · obtain ⟨u, hu⟩ : ∃ u : K →* K, ∀ x, u x = σ x := ⟨(σ : K →+* K).toMonoidHom, fun _ => rfl⟩
    refine ⟨u, fun x y hxy => σ.injective (by rw [← hu x, ← hu y]; exact hxy),
      fun D D' t t' hD hD' h => ?_⟩
    refine matrix_rel_of_conjAut_eq M D' (GeneralLinearGroup.map (σ : K →+* K) D) hD' ?_ ?_
    · rw [coe_map_GL, hD, diagonal_map (map_zero _)]
      simp [hu]
    · rw [← conjAut_semilinear_conj, h, hφt, pow_zero, mul_one]
  · obtain ⟨u, hu⟩ : ∃ u : K →* K, ∀ x, u x = (σ x)⁻¹ :=
      ⟨{ toFun := fun x => (σ x)⁻¹
         map_one' := by simp
         map_mul' := fun x y => by rw [map_mul σ, _root_.mul_inv] }, fun _ => rfl⟩
    refine ⟨u, fun x y hxy => σ.injective (inv_injective (by rw [← hu x, ← hu y]; exact hxy)),
      fun D D' t t' hD hD' h => ?_⟩
    refine matrix_rel_of_conjAut_eq M D'
      (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose D)) hD' ?_ ?_
    · rw [coe_map_GL, GeneralLinearGroup.coe_inverseTranspose, coe_inv_of_diagonal hD,
        diagonal_transpose, diagonal_map (map_zero _)]
      simp [hu]
    · rw [← conjAut_semilinear_conj, ← htrans.2.2.2.2.1 D, h, hφt, pow_one, _root_.mul_inv_rev, hδ]
      group

theorem ratAct_of_key {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) (hsc : GGTorusSelfCent p A)
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {α : MulAut L'}
    (hα : ∀ b ∈ A, α * b * α⁻¹ ∈ A) (M : GL (Fin d) K) (u : K →* K)
    (hu : Function.Injective u)
    (hkey : ∀ b ∈ A, ∀ t t' : Fin d → K, ActsDiag φ' b t → ActsDiag φ' (α * b * α⁻¹) t' →
      ∃ c : K, (M : Matrix (Fin d) (Fin d) K) * diagonal (fun k => u (t k)) =
        diagonal (fun k => t' k * c) * (M : Matrix (Fin d) (Fin d) K)) :
    ∃ (π : Equiv.Perm (Fin d)) (e : ℕ), RatAct φ' A α π e := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hu1 : IsPrimitiveRoot (u ζ) p := hζ.map_of_injective hu
  have hζ' : u ζ ≠ (u ζ)⁻¹ := ne_inv_of_isPrimitiveRoot hu1 hp hp2
  have hu_inv : ∀ x : K, x ≠ 0 → u x⁻¹ = (u x)⁻¹ := fun x hx =>
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hx, map_one])
  have hu_ne : ∀ x : K, x ≠ 0 → u x ≠ 0 := fun x hx h0 =>
    one_ne_zero (by rw [← map_one u, ← mul_inv_cancel₀ hx, map_mul, h0, zero_mul])
  have hurt : ∀ i j k : Fin d, u (rootT ζ i j k) = rootT (u ζ) i j k := by
    intro i j k
    unfold rootT
    split_ifs
    · rfl
    · exact hu_inv ζ hζ0
    · exact map_one u
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D : Fin d → K,
      (M : Matrix (Fin d) (Fin d) K) * diagonal (rootT (u ζ) i j) =
        diagonal D * (M : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    have hE := heartElt_mem hsc hdiag hζ0 hζ.pow_eq_one hij
    obtain ⟨t', ht'⟩ := hdiag _ (hα _ hE)
    obtain ⟨c, hc⟩ := hkey _ hE (rootT ζ i j) t' (heartElt_actsDiag hζ0 hij) ht'
    refine ⟨fun k => t' k * c, ?_⟩
    have e : (fun k => u (rootT ζ i j k)) = rootT (u ζ) i j := funext (hurt i j)
    rw [e] at hc
    exact hc
  obtain ⟨π, hπ⟩ := exists_perm_mul_diagonal hζ' M hmono
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ x : K, x ^ p = 1 → u x = x ^ e := by
    have h1 : (u ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨e, fun x hx => ?_⟩
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
    rw [← hi, map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨π, e, fun b hb r hr => ?_⟩
  obtain ⟨t, ht, hrt⟩ := hr
  obtain ⟨t', ht'⟩ := hdiag _ (hα b hb)
  obtain ⟨c, hc⟩ := hkey b hb t t' ht ht'
  rw [hπ] at hc
  have hc' := congrArg (· * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hc
  simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at hc'
  have hent : ∀ k, u (t (π k)) = t' k * c := fun k => by
    have := congrFun (congrFun hc' k) k
    simpa [diagonal_apply_eq] using this
  refine ⟨t', ht', fun k l => ?_⟩
  have hc0 : c ≠ 0 := fun h0 =>
    hu_ne (t (π k)) (ht.ne_zero (π k)) (by rw [hent k, h0, mul_zero])
  have hrp : (t (π k) * (t (π l))⁻¹) ^ p = 1 := ht.ratio_pow hφker (hAp b hb) (π k) (π l)
  beta_reduce
  rw [hrt (π k) (π l), ← he _ hrp, map_mul, hu_inv _ (ht.ne_zero (π l)), hent k, hent l]
  have := ht'.ne_zero l
  field_simp

theorem exists_ratAct {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 3 ≤ d)
    (hψs : Function.Surjective ψ) {A₀ : GL (Fin d) K} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    (hcompat : ∀ s, ψ (φ' s) =
      proj d K (CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ s))
    {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) (hsc : GGTorusSelfCent p A)
    {α : MulAut L'} (hα : ∀ b ∈ A, α * b * α⁻¹ ∈ A) {φα : MulAut (projectiveSL d K)}
    (hφα : ∀ l, φα (ψ l) = ψ (α l)) :
    ∃ (π : Equiv.Perm (Fin d)) (e : ℕ), RatAct φ' A α π e := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hp2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one hpK
  obtain ⟨M, u, hu, hnf⟩ := exists_normal_form hd (conjAut d K A₀ * φα * (conjAut d K A₀)⁻¹)
  refine ratAct_of_key hp hp2 hζ hAp hdiag hsc hφker hα M u hu fun b hb t t' ht ht' => ?_
  obtain ⟨D, hD, hbD⟩ := ht
  obtain ⟨D', hD', hbD'⟩ := ht'
  exact hnf D D' t t' hD hD' (conjAut_rel hψs hφ's hcompat hφα hbD hbD')

end CFSG.StandardType.LinTvA

end
