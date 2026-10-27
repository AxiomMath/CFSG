module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcTorus

public section

namespace CFSG.HardMathSupport.C14W1

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Torus
open scoped Matrix

theorem rootDiagUnit_mul' {τ : Tag} {K : Type} [Field K] (a b : Fin τ.rank → Kˣ) :
    rootDiagUnit τ (a * b) = rootDiagUnit τ a * rootDiagUnit τ b :=
  Units.ext (rootDiag_mul_rootDiag a b).symm

theorem rootDiagUnit_one' {τ : Tag} {K : Type} [Field K] :
    rootDiagUnit τ (1 : Fin τ.rank → Kˣ) = 1 :=
  Units.ext rootDiag_one

theorem rootDiagUnit_pow' {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ (a ^ n) = rootDiagUnit τ a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one']
  | succ n ih => rw [pow_succ, pow_succ, rootDiagUnit_mul', ih]

theorem rootDiag_apply_inr {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (w : RootModule τ K)
    (β : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    rootDiag a w (Sum.inr β) = (rootChar a β.1 : K) * w (Sum.inr β) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, Finsupp.add_apply, hu, hv, Finsupp.add_apply, mul_add]
  | single b c =>
    rw [← mul_one c, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
    congr 1
    rcases b with i | γ
    · rw [rootDiag_single_inl]; simp
    · rw [rootDiag_single_inr, Finsupp.smul_apply, smul_eq_mul]
      by_cases h : γ = β
      · subst h; simp [rootChar]
      · rw [Finsupp.single_eq_of_ne (by simpa using Ne.symm h), mul_zero, mul_zero]

theorem rootDiag_apply_inl {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (w : RootModule τ K) (i : Fin τ.rank) :
    rootDiag a w (Sum.inl i) = w (Sum.inl i) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, Finsupp.add_apply, hu, hv, Finsupp.add_apply]
  | single b c =>
    rw [← mul_one c, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Finsupp.smul_apply,
      Finsupp.smul_apply]
    congr 1
    rcases b with j | γ
    · rw [rootDiag_single_inl]
    · rw [rootDiag_single_inr]; simp

theorem rootDiagUnit_injective' {τ : Tag} {K : Type} [Field K] : Function.Injective (rootDiagUnit τ : (Fin τ.rank → Kˣ) → ModGL τ K) := by
  intro a b h
  refine ext_rootChar fun i => Units.ext ?_
  have hv := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))
    (Finsupp.single (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩) 1)
    (Sum.inr ⟨Pi.single i 1, isRoot_single τ i⟩)) h
  change rootDiag a _ _ = rootDiag b _ _ at hv
  rw [rootDiag_apply_inr, rootDiag_apply_inr, Finsupp.single_eq_same, mul_one, mul_one] at hv
  exact hv

theorem rootChar_update_one {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) (x : Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (Function.update (1 : Fin τ.rank → Kˣ) i x) v = x ^ v i := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem exists_unit_pow_ne_one {K : Type} [Field K] [Infinite K] {n : ℕ} (hn : n ≠ 0) : ∃ x : Kˣ, x ^ n ≠ 1 := by
  by_contra! h
  have hroot : ∀ x : K, (Polynomial.X ^ (n + 1) - Polynomial.X : Polynomial K).IsRoot x := by
    intro x
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    by_cases hx : x = 0
    · rw [hx, zero_pow (Nat.succ_ne_zero n)]
    · have := congrArg Units.val (h (Units.mk0 x hx))
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
      rw [pow_succ, this, one_mul]
  have h0 := Polynomial.eq_zero_of_infinite_isRoot (Polynomial.X ^ (n + 1) - Polynomial.X : Polynomial K)
    (by
      have hset : {x | (Polynomial.X ^ (n + 1) - Polynomial.X : Polynomial K).IsRoot x} = Set.univ :=
        Set.eq_univ_of_forall hroot
      rw [hset]; exact Set.infinite_univ)
  have := congrArg (fun P => Polynomial.coeff P 1) h0
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X_one,
    Polynomial.coeff_zero] at this
  rw [if_neg (by omega)] at this
  norm_num at this

theorem eq_of_rootChar_eq {τ : Tag} {K : Type} [Field K] [Infinite K] {u v : Fin τ.rank → ℤ}
    (h : ∀ t : Fin τ.rank → Kˣ, rootChar t u = rootChar t v) : u = v := by
  funext i
  by_contra hne
  have hd : (u i - v i).natAbs ≠ 0 := by omega
  obtain ⟨x, hx⟩ := exists_unit_pow_ne_one (K := K) hd
  apply hx
  have h1 := h (Function.update 1 i x)
  rw [rootChar_update_one, rootChar_update_one] at h1
  have h2 : x ^ (u i - v i) = 1 := by rw [zpow_sub, h1, mul_inv_cancel]
  rcases Int.natAbs_eq (u i - v i) with h3 | h3
  · rw [h3, zpow_natCast] at h2; exact h2
  · rw [h3, zpow_neg, zpow_natCast, inv_eq_one] at h2; exact h2

abbrev Roots (τ : Tag) : Type := {v : Fin τ.rank → ℤ // IsRoot τ v}

theorem exists_lattice_map {τ : Tag} {K : Type} [Field K] [Infinite K] (Q : ModGL τ K)
    (hQT : ∀ t, ∃ t', Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ t') :
    ∃ A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ,
      (∀ t, Q * rootDiagUnit τ t * Q⁻¹ = rootDiagUnit τ (tmap A t)) ∧
      (∀ α, IsRoot τ α → IsRoot τ (A *ᵥ α)) ∧ ∃ N : ℕ, 0 < N ∧ A ^ N = 1 := by
  classical
  choose c hc using hQT
  have hstep : ∀ α : Roots τ, ∃ β : Roots τ, ∀ t, rootChar (c t) β.1 = rootChar t α.1 := by
    intro α
    set w : RootModule τ K := (Q : Module.End K (RootModule τ K)) (Finsupp.single (Sum.inr α) 1)
    have hw0 : w ≠ 0 := by
      intro h0
      have := congrArg (fun x => ((Q⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) x) h0
      simp only [w, map_zero] at this
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply] at this
      exact Finsupp.single_ne_zero.2 one_ne_zero this
    have heig : ∀ t, rootDiag (c t) w = (rootChar t α.1 : K) • w := by
      intro t
      have e := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))) (hc t)
      change ((rootDiagUnit τ (c t) : ModGL τ K) : Module.End K (RootModule τ K)) w = _
      rw [← e, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
      simp only [w]
      rw [← Module.End.mul_apply (((Q⁻¹ : ModGL τ K)) : Module.End K (RootModule τ K)),
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
      change (Q : Module.End K (RootModule τ K)) (rootDiag t _) = _
      rw [rootDiag_single_inr, map_smul]
      rfl
    obtain ⟨b, hb⟩ := Finsupp.ne_iff.1 hw0
    rcases b with i | β
    · exfalso
      apply α.2.ne_zero
      refine eq_of_rootChar_eq (K := K) fun t => ?_
      have := congrArg (fun x => x (Sum.inl i)) (heig t)
      simp only [rootDiag_apply_inl, Finsupp.smul_apply, smul_eq_mul] at this
      rw [rootChar_zero]
      refine Units.ext ?_
      have h1 : ((rootChar t α.1 : K) - 1) * w (Sum.inl i) = 0 := by
        rw [sub_mul, one_mul, ← this, sub_self]
      rcases mul_eq_zero.1 h1 with h | h
      · rw [Units.val_one]; exact sub_eq_zero.1 h
      · exact absurd h hb
    · refine ⟨β, fun t => Units.ext ?_⟩
      have := congrArg (fun x => x (Sum.inr β)) (heig t)
      simp only [rootDiag_apply_inr, Finsupp.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hb this
  choose π hπ using hstep
  have hπinj : Function.Injective π := by
    intro α α' h
    apply Subtype.ext
    refine eq_of_rootChar_eq (K := K) fun t => ?_
    rw [← hπ α t, ← hπ α' t, h]
  have hπbij : Function.Bijective π := Finite.injective_iff_bijective.1 hπinj
  let σ : Equiv.Perm (Roots τ) := Equiv.ofBijective π hπbij
  have hσ : ∀ β : Roots τ, ∀ t, rootChar (c t) β.1 = rootChar t (σ.symm β).1 := by
    intro β t
    have := hπ (σ.symm β) t
    rwa [show π (σ.symm β) = β from σ.apply_symm_apply β] at this
  let e : Fin τ.rank → Roots τ := fun i => ⟨Pi.single i 1, isRoot_single τ i⟩
  let A : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := fun j i => (σ.symm (e i)).1 j
  have hcA : ∀ t, c t = tmap A t := by
    intro t
    funext i
    rw [← rootChar_single (c t) i]
    exact (hσ (e i) t)
  have hAβ : ∀ β : Roots τ, A *ᵥ β.1 = (σ.symm β).1 := by
    intro β
    refine eq_of_rootChar_eq (K := K) fun t => ?_
    rw [← rootChar_tmap, ← hcA, hσ]
  refine ⟨A, fun t => by rw [hc, hcA], fun α hα => ?_, ?_⟩
  · rw [hAβ ⟨α, hα⟩]; exact (σ.symm ⟨α, hα⟩).2
  · obtain ⟨N, hN0, hN⟩ := (isOfFinOrder_of_finite σ.symm).exists_pow_eq_one
    refine ⟨N, hN0, ?_⟩
    have hk : ∀ k : ℕ, ∀ β : Roots τ, (A ^ k) *ᵥ β.1 = ((σ.symm ^ k) β).1 := by
      intro k
      induction k with
      | zero => intro β; simp
      | succ k ih =>
        intro β
        rw [pow_succ, ← Matrix.mulVec_mulVec, hAβ, ih, pow_succ, Equiv.Perm.mul_apply]
    ext j i
    have := congrFun (hk N (e i)) j
    rw [hN] at this
    simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using this

end CFSG.HardMathSupport.C14W1
