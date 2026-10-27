module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.ProjFive

open Module Module.End Subgroup

section Roots

variable {K : Type*} [Field K]

theorem pow_two_pow_inj {α : K} (hα : IsPrimitiveRoot α 5) {k l : ℕ} (hk : k < 4) (hl : l < 4)
    (h : α ^ (2 ^ k) = α ^ (2 ^ l)) : k = l := by
  rw [pow_eq_pow_mod (2 ^ k) hα.pow_eq_one, pow_eq_pow_mod (2 ^ l) hα.pow_eq_one] at h
  have h' := hα.pow_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h
  interval_cases k <;> interval_cases l <;> simp_all

theorem pow_two_pow_ne_one {α : K} (hα : IsPrimitiveRoot α 5) (k : ℕ) : α ^ (2 ^ k) ≠ 1 := by
  rw [Ne, hα.pow_eq_one_iff_dvd]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
  norm_num at this

theorem isPrimitiveRoot_of_pow_five {α : K} (h5 : α ^ 5 = 1) (h1 : α ≠ 1) : IsPrimitiveRoot α 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h5 h1)

end Roots

section Twist

variable {R : Type*} [Monoid R]

theorem pow_mul_twist {T M : R} (h : T * M = M * T ^ 2) (n : ℕ) : T ^ n * M = M * T ^ (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_add,
      show 2 * (n + 1) = 2 * n + 2 by ring]

theorem mul_pow_twist {T M : R} (h : T * M = M * T ^ 2) (k : ℕ) : T * M ^ k = M ^ k * T ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, pow_mul_twist h, ← mul_assoc, ← pow_succ,
      show 2 ^ (k + 1) = 2 * 2 ^ k by ring]

end Twist

section Eigen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pow_five_of_eigen {T : End K V} (hT : T ^ 5 = 1) {μ : K} {x : V} (hx : T.HasEigenvector μ x) :
    μ ^ 5 = 1 := by
  have h := hx.pow_apply 5
  rw [hT, Module.End.one_apply] at h
  have h0 : (μ ^ 5 - 1) • x = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx.2)

theorem exists_hasEigenvector_ne_one [IsAlgClosed K] [FiniteDimensional K V] (h5 : (5 : K) ≠ 0)
    {T : End K V} (hT : T ^ 5 = 1) (hT1 : T ≠ 1) : ∃ γ w, γ ≠ 1 ∧ T.HasEigenvector γ w := by
  set U := LinearMap.range (T - 1)
  have hUT : ∀ x ∈ U, T x ∈ U := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T y, by simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]⟩
  have hU : U ≠ ⊥ := by
    intro h
    apply hT1
    ext x
    have hx : (T - 1) x ∈ U := LinearMap.mem_range_self _ x
    rw [h, Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
  obtain ⟨γ, hγ⟩ := Module.End.exists_eigenvalue (T.restrict hUT)
  obtain ⟨w, hw⟩ := hγ.exists_hasEigenvector
  have hTw : T w = γ • (w : V) := by
    have := congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hw.1)
    simpa [LinearMap.restrict_coe_apply] using this
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwT : T.HasEigenvector γ w :=
    Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hTw, hw0⟩
  refine ⟨γ, w, ?_, hwT⟩
  intro hγ1
  obtain ⟨y, hy⟩ := w.2
  have key : (∑ i ∈ Finset.range 5, T ^ i) ((T - 1) y) = 0 := by
    rw [← Module.End.mul_apply, geom_sum_mul, hT, sub_self, LinearMap.zero_apply]
  rw [hy, LinearMap.sum_apply] at key
  simp only [hwT.pow_apply, hγ1, one_pow, one_smul, Finset.sum_const, Finset.card_range] at key
  have h5w : (5 : K) • (w : V) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul K] at key
    exact_mod_cast key
  exact hw0 ((smul_eq_zero.1 h5w).resolve_left h5)

theorem exists_common_eigen_ne_one [IsAlgClosed K] [FiniteDimensional K V] (h5 : (5 : K) ≠ 0)
    {A B : End K V} (hA : A ^ 5 = 1) (hA1 : A ≠ 1) (hAB : A * B = B * A) :
    ∃ α β v, α ≠ 1 ∧ A.HasEigenvector α v ∧ B.HasEigenvector β v := by
  obtain ⟨α, w, hα1, hw⟩ := exists_hasEigenvector_ne_one h5 hA hA1
  have hBE : ∀ x ∈ A.eigenspace α, B x ∈ A.eigenspace α := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, hAB, Module.End.mul_apply, hx, map_smul]
  haveI : Nontrivial (A.eigenspace α) := Submodule.nontrivial_iff_ne_bot.2
    (Module.End.hasEigenvalue_iff.1 (Module.End.hasEigenvalue_of_hasEigenvector hw))
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue (B.restrict hBE)
  obtain ⟨v, hv⟩ := hβ.exists_hasEigenvector
  have hBv : B v = β • (v : V) := by
    have := congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hv.1)
    simpa [LinearMap.restrict_coe_apply] using this
  have hv0 : (v : V) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  exact ⟨α, β, v, hα1, Module.End.hasEigenvector_iff.2 ⟨v.2, hv0⟩,
    Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hBv, hv0⟩⟩

theorem hasEigenvector_pow_twist {T M : End K V} (h : T * M = M * T ^ 2) (hM : Function.Injective M) {μ : K}
    {x : V} (hx : T.HasEigenvector μ x) (k : ℕ) : T.HasEigenvector (μ ^ (2 ^ k)) ((M ^ k) x) := by
  refine Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
  · rw [← Module.End.mul_apply, mul_pow_twist h k, Module.End.mul_apply, hx.pow_apply, map_smul]
  · have hMk : Function.Injective (M ^ k) := by
      rw [Module.End.coe_pow]
      exact hM.iterate k
    exact fun h0 => hx.2 (hMk (by rw [h0, map_zero]))

theorem four_le_finrank_of_mem [FiniteDimensional K V] {P : Submodule K V} {u : Fin 4 → V}
    (hu : LinearIndependent K u) (hP : ∀ k, u k ∈ P) : 4 ≤ finrank K P := by
  have hli : LinearIndependent K (fun k => (⟨u k, hP k⟩ : P)) :=
    LinearIndependent.of_comp P.subtype hu
  simpa using hli.fintype_card_le_finrank

theorem exists_pow_mul_pow_eq_one [IsAlgClosed K] [FiniteDimensional K V] (h5 : (5 : K) ≠ 0)
    (hV : finrank K V ≤ 7) {A B M : End K V} (hA : A ^ 5 = 1) (hB : B ^ 5 = 1) (hAB : A * B = B * A)
    (hM : Function.Injective M) (hMA : A * M = M * A ^ 2) (hMB : B * M = M * B ^ 2) :
    ∃ s t : ℕ, s < 5 ∧ t < 5 ∧ (s ≠ 0 ∨ t ≠ 0) ∧ A ^ s * B ^ t = 1 := by
  by_cases hA1 : A = 1
  · exact ⟨1, 0, by norm_num, by norm_num, Or.inl one_ne_zero, by simp [hA1]⟩
  obtain ⟨α, β, v, hα1, hAv, hBv⟩ := exists_common_eigen_ne_one h5 hA hA1 hAB
  have hαp := isPrimitiveRoot_of_pow_five (pow_five_of_eigen hA hAv) hα1
  obtain ⟨j, hj, hjβ⟩ := hαp.eq_pow_of_pow_eq_one (pow_five_of_eigen hB hBv)
  refine ⟨(5 - j) % 5, 1, Nat.mod_lt _ (by norm_num), by norm_num, Or.inr one_ne_zero, ?_⟩
  rw [pow_one]
  set s := (5 - j) % 5 with hs
  set g := A ^ s * B with hg
  have hgc : Commute (A ^ s) B := (Commute.pow_left hAB s)
  have hg5 : g ^ 5 = 1 := by
    rw [hg, hgc.mul_pow, ← pow_mul, mul_comm s 5, pow_mul, hA, one_pow, one_mul, hB]
  have hgM : g * M = M * g ^ 2 := by
    rw [hg, hgc.mul_pow, mul_assoc, hMB, ← mul_assoc, pow_mul_twist hMA s, ← pow_mul, mul_comm s 2,
      mul_assoc]
  have hgv : g.HasEigenvector 1 v := by
    refine Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, hAv.2⟩
    have hjs : α ^ (j + s) = 1 := by
      rw [hαp.pow_eq_one_iff_dvd]
      omega
    rw [hg, Module.End.mul_apply, hBv.apply_eq_smul, map_smul, hAv.pow_apply, smul_smul, ← hjβ, ← pow_add,
      hjs]
  by_contra hg1
  obtain ⟨γ, w, hγ1, hw⟩ := exists_hasEigenvector_ne_one h5 hg5 hg1
  have hγp := isPrimitiveRoot_of_pow_five (pow_five_of_eigen hg5 hw) hγ1
  have hli_u := Module.End.eigenvectors_linearIndependent' A (fun k : Fin 4 => α ^ (2 ^ (k : ℕ)))
    (fun k l h => Fin.ext (pow_two_pow_inj hαp k.2 l.2 h)) (fun k : Fin 4 => (M ^ (k : ℕ)) v)
    (fun k => hasEigenvector_pow_twist hMA hM hAv k)
  have hli_w := Module.End.eigenvectors_linearIndependent' g (fun k : Fin 4 => γ ^ (2 ^ (k : ℕ)))
    (fun k l h => Fin.ext (pow_two_pow_inj hγp k.2 l.2 h)) (fun k : Fin 4 => (M ^ (k : ℕ)) w)
    (fun k => hasEigenvector_pow_twist hgM hM hw k)
  have hker : 4 ≤ finrank K (LinearMap.ker (g - 1)) := by
    refine four_le_finrank_of_mem hli_u (fun k => ?_)
    have h := (hasEigenvector_pow_twist hgM hM hgv k).apply_eq_smul
    rw [one_pow, one_smul] at h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, h, Module.End.one_apply, sub_self]
  have hrange : 4 ≤ finrank K (LinearMap.range (g - 1)) := by
    refine four_le_finrank_of_mem hli_w (fun k => ?_)
    have h := (hasEigenvector_pow_twist hgM hM hw k).apply_eq_smul
    have hne : γ ^ (2 ^ (k : ℕ)) - 1 ≠ 0 := sub_ne_zero.2 (pow_two_pow_ne_one hγp _)
    have h' : (g - 1) ((M ^ (k : ℕ)) w) = (γ ^ (2 ^ (k : ℕ)) - 1) • (M ^ (k : ℕ)) w := by
      rw [LinearMap.sub_apply, h, Module.End.one_apply, sub_smul, one_smul]
    refine ⟨(γ ^ (2 ^ (k : ℕ)) - 1)⁻¹ • (M ^ (k : ℕ)) w, ?_⟩
    rw [map_smul, h', smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hsum := LinearMap.finrank_range_add_finrank_ker (g - 1)
  omega

end Eigen

section Matrix

theorem exists_pow_mul_pow_eq_one_GL {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) {d : ℕ} (hd : d ≤ 7)
    {A B M : Matrix.GeneralLinearGroup (Fin d) F} (hA : A ^ 5 = 1) (hB : B ^ 5 = 1) (hAB : A * B = B * A)
    (hMA : M * A * M⁻¹ = A ^ 2) (hMB : M * B * M⁻¹ = B ^ 2) :
    ∃ s t : ℕ, s < 5 ∧ t < 5 ∧ (s ≠ 0 ∨ t ≠ 0) ∧ A ^ s * B ^ t = 1 := by
  let L := AlgebraicClosure F
  let Φ : Matrix.GeneralLinearGroup (Fin d) F →* Module.End L (Fin d → L) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin d)).toAlgHom.toRingHom.toMonoidHom.comp
      ((algebraMap F L).mapMatrix.toMonoidHom.comp (Units.coeHom (Matrix (Fin d) (Fin d) F)))
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    exact Units.ext (Matrix.map_injective (algebraMap F L).injective (Matrix.toLinAlgEquiv'.injective hxy))
  have h5L : (5 : L) ≠ 0 := by
    intro h
    apply h5
    apply (algebraMap F L).injective
    rw [map_ofNat, h, map_zero]
  have htw : ∀ X : Matrix.GeneralLinearGroup (Fin d) F, M * X * M⁻¹ = X ^ 2 →
      Φ X * Φ M⁻¹ = Φ M⁻¹ * Φ X ^ 2 := by
    intro X hX
    rw [← map_mul, ← map_pow, ← map_mul, ← hX]
    congr 1
    group
  have hMinj : Function.Injective (Φ M⁻¹) := by
    intro x y hxy
    have h := congrArg (Φ M) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  obtain ⟨s, t, hs, ht, hst, h⟩ := exists_pow_mul_pow_eq_one h5L (by rwa [Module.finrank_fin_fun])
    (by rw [← map_pow, hA, map_one]) (by rw [← map_pow, hB, map_one]) (by rw [← map_mul, hAB, map_mul])
    hMinj (htw A hMA) (htw B hMB)
  refine ⟨s, t, hs, ht, hst, hΦ ?_⟩
  rw [map_mul, map_pow, map_pow, h, map_one]

end Matrix

section Lift

variable {G : Type*} [Group G]

theorem conj_pow_pow_of_central {A B c : G} (hc : ∀ g : G, Commute g c) (h : A * B * A⁻¹ = c * B)
    (i j : ℕ) : A ^ i * B ^ j * (A ^ i)⁻¹ = c ^ (i * j) * B ^ j := by
  have hj : A * B ^ j * A⁻¹ = c ^ j * B ^ j := by
    rw [← conj_pow, h, ((hc B).symm).mul_pow]
  induction i with
  | zero => simp
  | succ i ih =>
    calc A ^ (i + 1) * B ^ j * (A ^ (i + 1))⁻¹ = A * (A ^ i * B ^ j * (A ^ i)⁻¹) * A⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
      _ = c ^ (i * j) * (A * B ^ j * A⁻¹) := by
          rw [ih, ← mul_assoc, ((hc A).pow_right (i * j)).eq]
          simp only [mul_assoc]
      _ = c ^ ((i + 1) * j) * B ^ j := by
          rw [hj, ← mul_assoc, ← pow_add, add_mul, one_mul]

theorem exists_lift_twist {Z : Subgroup G} [Z.Normal] (hZ : Z ≤ center G) (M : G) {x : G ⧸ Z}
    (hx : (M : G ⧸ Z) * x * (M : G ⧸ Z)⁻¹ = x ^ 2) (hx5 : x ^ 5 = 1) :
    ∃ X : G, (X : G ⧸ Z) = x ∧ M * X * M⁻¹ = X ^ 2 ∧ X ^ 5 = 1 := by
  obtain ⟨X₀, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨μ, h1⟩ : ∃ μ : G, M * X₀ * M⁻¹ = μ * X₀ ^ 2 := ⟨M * X₀ * M⁻¹ * (X₀ ^ 2)⁻¹, by group⟩
  have hμZ : μ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, eq_mul_inv_of_mul_eq h1.symm, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, mul_inv_cancel]
  have hμc : ∀ g : G, Commute g μ := fun g => Subgroup.mem_center_iff.1 (hZ hμZ) g
  have hX : M * (μ * X₀) * M⁻¹ = (μ * X₀) ^ 2 := by
    calc M * (μ * X₀) * M⁻¹ = μ * (M * X₀ * M⁻¹) := by
          rw [← mul_assoc, (hμc M).eq]
          simp only [mul_assoc]
      _ = (μ * X₀) ^ 2 := by
          rw [h1, ((hμc X₀).symm).mul_pow, sq μ, mul_assoc]
  refine ⟨μ * X₀, ?_, hX, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff μ).2 hμZ, one_mul]
  · have hcZ : (μ * X₀) ^ 5 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff μ).2 hμZ, one_mul, hx5]
    have hcc : M * (μ * X₀) ^ 5 * M⁻¹ = (μ * X₀) ^ 5 := by
      rw [Subgroup.mem_center_iff.1 (hZ hcZ) M, mul_inv_cancel_right]
    have hc2 : M * (μ * X₀) ^ 5 * M⁻¹ = (μ * X₀) ^ 5 * (μ * X₀) ^ 5 := by
      rw [← conj_pow, hX, ← pow_mul, ← pow_add]
    rw [hcc] at hc2
    exact mul_eq_left.1 hc2.symm

theorem exists_lift_five {Z : Subgroup G} [Z.Normal] (hZ : Z ≤ center G) {a b m : G ⧸ Z} (hab : a * b = b * a)
    (ha : m * a * m⁻¹ = a ^ 2) (hb : m * b * m⁻¹ = b ^ 2) (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1) :
    ∃ A B M : G, (A : G ⧸ Z) = a ∧ (B : G ⧸ Z) = b ∧ (M : G ⧸ Z) = m ∧
      A * B = B * A ∧ M * A * M⁻¹ = A ^ 2 ∧ M * B * M⁻¹ = B ^ 2 ∧ A ^ 5 = 1 ∧ B ^ 5 = 1 := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective m
  obtain ⟨A, rfl, hMA, hA5⟩ := exists_lift_twist hZ M ha ha5
  obtain ⟨B, rfl, hMB, hB5⟩ := exists_lift_twist hZ M hb hb5
  refine ⟨A, B, M, rfl, rfl, rfl, ?_, hMA, hMB, hA5, hB5⟩
  obtain ⟨c, hABc⟩ : ∃ c : G, A * B * A⁻¹ = c * B := ⟨A * B * A⁻¹ * B⁻¹, by group⟩
  have hc : c = A * B * A⁻¹ * B⁻¹ := eq_mul_inv_of_mul_eq hABc.symm
  have hcZ : c ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, hc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, hab, mul_assoc, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel]
  have hcc : ∀ g : G, Commute g c := fun g => Subgroup.mem_center_iff.1 (hZ hcZ) g
  have h51 := conj_pow_pow_of_central hcc hABc 5 1
  simp only [hA5, inv_one, mul_one, one_mul, pow_one] at h51
  have hc5 : c ^ 5 = 1 := by
    have : c ^ 5 * B = 1 * B := by rw [one_mul]; exact h51.symm
    exact mul_right_cancel this
  have h22 := conj_pow_pow_of_central hcc hABc 2 2
  have hMc : M * c * M⁻¹ = c := by rw [(hcc M).eq, mul_inv_cancel_right]
  have hc4 : c = c ^ 4 := by
    have h : M * c * M⁻¹ = A ^ 2 * B ^ 2 * (A ^ 2)⁻¹ * (B ^ 2)⁻¹ := by
      rw [← hMA, ← hMB, hc]
      group
    rw [hMc, h22, mul_inv_cancel_right] at h
    exact h
  have hc3 : c ^ 3 = 1 := by
    have : c ^ 3 * c = 1 * c := by rw [← pow_succ, one_mul]; exact hc4.symm
    exact mul_right_cancel this
  have hc1 : c = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc5) (orderOf_dvd_of_pow_eq_one hc3)
    rw [show Nat.gcd 5 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  rw [hc1, one_mul] at hABc
  exact mul_inv_eq_iff_eq_mul.1 hABc

theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) {K : Subgroup Q}
    (hK : K.Normal) : K = ⊤ ∨ K ≤ center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hK.map (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' (center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : K ⊔ center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center Q)) K
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ K :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

end Lift

end CFSG.LocalAnalysis.UniquenessCase.UC6.ProjFive

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC6.ProjFive

theorem projRep_eq_one_of_five (J : Type*) [Group J] (hq : CFSG.Open.IsQuasisimple J) (N : Subgroup J)
    [N.Normal] (hN : N ≤ center J) (hZ : center (J ⧸ N) = ⊥) {a b ν : J ⧸ N} (hab : a * b = b * a)
    (ha : ν * a * ν⁻¹ = a ^ 2) (hb : ν * b * ν⁻¹ = b ^ 2) (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1)
    (hne : ∀ s t : ℕ, s < 5 → t < 5 → (s ≠ 0 ∨ t ≠ 0) → a ^ s * b ^ t ≠ 1) {F : Type*} [Field F]
    (h5 : (5 : F) ≠ 0) {d : ℕ} (hd : d ≤ 7)
    (f : J →* Matrix.GeneralLinearGroup (Fin d) F ⧸ center (Matrix.GeneralLinearGroup (Fin d) F)) :
    f = 1 := by
  obtain ⟨x, y, n, rfl, rfl, rfl, hxy, hnx, hny, hx5, hy5⟩ := exists_lift_five hN hab ha hb ha5 hb5
  obtain ⟨A, B, M, hA, hB, -, hAB, hMA, hMB, hA5, hB5⟩ :=
    exists_lift_five (Z := center (Matrix.GeneralLinearGroup (Fin d) F)) le_rfl (a := f x) (b := f y) (m := f n)
      (by rw [← map_mul, hxy, map_mul]) (by rw [← map_inv, ← map_mul, ← map_mul, hnx, map_pow])
      (by rw [← map_inv, ← map_mul, ← map_mul, hny, map_pow]) (by rw [← map_pow, hx5, map_one])
      (by rw [← map_pow, hy5, map_one])
  obtain ⟨s, t, hs, ht, hst, h1⟩ := exists_pow_mul_pow_eq_one_GL h5 hd hA5 hB5 hAB hMA hMB
  have hker : x ^ s * y ^ t ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_pow, map_pow, ← hA, ← hB, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
      ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one]
  rcases normal_eq_top_or_le_center hq f.normal_ker with h | h
  · ext z
    have hz : z ∈ f.ker := h ▸ Subgroup.mem_top z
    rw [MonoidHom.mem_ker] at hz
    rw [hz, MonoidHom.one_apply]
  · exfalso
    have hc : x ^ s * y ^ t ∈ center J := h hker
    have hcN : ((x ^ s * y ^ t : J) : J ⧸ N) ∈ center (J ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 hc z)]
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow] at hcN
    exact hne s t hs ht hst hcN

end CFSG.LocalAnalysis.UniquenessCase.UCK
