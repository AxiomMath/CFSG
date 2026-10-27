module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

namespace CFSG.StandardType

private lemma l05nK6b_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private theorem l05nK6b_groupEquiv_of_eq {B : Type} {M M' : CoxeterMatrix B} (h : M = M') :
    ∃ φ : M.Group ≃* M'.Group, ∀ i, φ (M.simple i) = M'.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

private theorem l05nK6b_conj_reflection {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ}
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) (ψ : MulAut ↥Bs) :
    GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

private lemma l05nK6b_symm_swap_isReflection {p : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    (A : Subgroup (MulAut ↥Bs)) {N : ℕ} (hN : 3 ≤ N) (e : A ≃* Equiv.Perm (Fin N))
    (hrefl : ∀ r : A, GGIsReflection p (r : MulAut ↥Bs) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    (hgen : GGReflGenerated p A) (i j : Fin N) (hij : i ≠ j) :
    GGIsReflection p (((e.symm (Equiv.swap i j)) : A) : MulAut ↥Bs) := by
  have hex : ∃ r : A, GGIsReflection p (r : MulAut ↥Bs) := by
    by_contra h
    have hemp : {φ : MulAut ↥Bs | φ ∈ A ∧ GGIsReflection p φ} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro φ ⟨hφA, hφr⟩
      exact h ⟨⟨φ, hφA⟩, hφr⟩
    have hbot : A = ⊥ := by
      have hg : A = Subgroup.closure {φ : MulAut ↥Bs | φ ∈ A ∧ GGIsReflection p φ} := hgen
      rw [hg, hemp, Subgroup.closure_empty]
    let z : Fin N := ⟨0, by omega⟩
    let o : Fin N := ⟨1, by omega⟩
    have hzo : z ≠ o := fun hzo =>
      Nat.zero_ne_one (by simpa [z, o] using congrArg Fin.val hzo)
    have hz1 : e.symm (Equiv.swap z o) = 1 := by
      apply Subtype.ext
      have hmem : ((e.symm (Equiv.swap z o) : A) : MulAut ↥Bs) ∈
          (⊥ : Subgroup (MulAut ↥Bs)) := by
        rw [← hbot]
        exact (e.symm (Equiv.swap z o)).2
      simpa using (Subgroup.mem_bot.mp hmem)
    have hswap1 : Equiv.swap z o = 1 := by
      have h1 := congrArg e hz1
      simpa using h1
    have hz : (Equiv.swap z o) z = o := Equiv.swap_apply_left z o
    rw [hswap1] at hz
    exact hzo (by simpa using hz)
  obtain ⟨r0, hr0⟩ := hex
  obtain ⟨a, b, hab, hr0e⟩ := hrefl r0 hr0
  obtain ⟨σ, hσ⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hij)
  let x : A := e.symm σ
  let r' : A := x * r0 * x⁻¹
  have hr'_refl : GGIsReflection p (r' : MulAut ↥Bs) := by
    have hh := l05nK6b_conj_reflection hr0 (x : MulAut ↥Bs)
    simpa [r'] using hh
  have he_r' : e r' = Equiv.swap i j := by
    have h1 : e r' = e x * e r0 * (e x)⁻¹ := by
      change e (x * r0 * x⁻¹) = e x * e r0 * (e x)⁻¹
      rw [map_mul, map_mul, map_inv]
    have h2 : e x = σ := by
      change e (e.symm σ) = σ
      exact MulEquiv.apply_symm_apply e σ
    rw [h1, h2, hr0e, hσ]
  have hfin : e.symm (Equiv.swap i j) = r' := by
    rw [← he_r', MulEquiv.symm_apply_apply]
  rw [hfin]
  exact hr'_refl

theorem ggRC_weyl_of_perm {p : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    (A : Subgroup (MulAut ↥Bs)) {N : ℕ} (hN : 3 ≤ N) (e : A ≃* Equiv.Perm (Fin N))
    (hrefl : ∀ r : A, GGIsReflection p (r : MulAut ↥Bs) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    (hgen : GGReflGenerated p A) : GGWeylReflectionGroup p A := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ (n + 1) - 1 := by omega
  refine ⟨Fin ((n + 1) - 1), CoxeterMatrix.A ((n + 1) - 1), ?_, ?_⟩
  · refine Or.inl ⟨(n + 1) - 1, Equiv.refl _, hn, Or.inl ?_⟩
    exact (l05nK6b_reindex_refl _).symm
  · obtain ⟨φ, hφ⟩ := l05nK6b_groupEquiv_of_eq (coxeterMatrix_isFiniteType_A_eq n).symm
    let ee : (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)) :=
      φ.trans (typeAWeylEquiv n).symm
    have hee : ∀ k : Fin n,
        ee ((CoxeterMatrix.A n).simple k) = Equiv.swap k.castSucc k.succ := by
      intro k
      change (typeAWeylEquiv n).symm (φ ((CoxeterMatrix.A n).simple k)) =
        Equiv.swap k.castSucc k.succ
      rw [hφ k, ← typeAWeylEquiv_swap n k, MulEquiv.symm_apply_apply]
    refine ⟨ee.trans e.symm, ?_⟩
    intro k
    have hf : (ee.trans e.symm) ((CoxeterMatrix.A n).simple k) =
        e.symm (Equiv.swap k.castSucc k.succ) := by
      change e.symm (ee ((CoxeterMatrix.A n).simple k)) =
        e.symm (Equiv.swap k.castSucc k.succ)
      rw [hee k]
    change GGIsReflection p
      (((ee.trans e.symm) ((CoxeterMatrix.A n).simple k) : ↥A) : MulAut ↥Bs)
    rw [hf]
    exact l05nK6b_symm_swap_isReflection A hN e hrefl hgen k.castSucc k.succ
      (ne_of_lt (Fin.castSucc_lt_succ (i := k)))

end CFSG.StandardType
