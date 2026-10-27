module

public import CFSG.RankThree.PartOne.KFCL.SpPerm
public import CFSG.RankThree.PartOne.CTP.SeitzSymplectic

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p : ℕ}

theorem card_spTorus_le (hp : 0 < p) : Nat.card (spTorus p 3 K) ≤ p ^ 3 := by
  classical
  let R : Finset K := Polynomial.nthRootsFinset p (1 : K)
  have hR : R.card ≤ p := by
    have := Polynomial.card_nthRoots p (1 : K)
    exact (Multiset.toFinset_card_le _).trans this
  let f : spTorus p 3 K → (Fin 3 → R) := fun g i =>
    ⟨mat 3 K g.1 (Sum.inl i) (Sum.inl i), by
      rw [Polynomial.mem_nthRootsFinset hp]
      exact spTorus_pow g.2 _⟩
  have hf : Function.Injective f := by
    intro g g' h
    apply Subtype.ext
    apply mat_injective
    ext a b
    by_cases hab : a = b
    · subst hab
      rcases a with i | i
      · exact congrArg Subtype.val (congrFun h i)
      · have h1 := spTorus_par g.2 (Sum.inl i)
        have h2 := spTorus_par g'.2 (Sum.inl i)
        rw [par_inl] at h1 h2
        rw [h1, h2]
        exact congrArg (·⁻¹) (congrArg Subtype.val (congrFun h i))
    · rw [spTorus_apply_ne g.2 hab, spTorus_apply_ne g'.2 hab]
  calc Nat.card (spTorus p 3 K) ≤ Nat.card (Fin 3 → R) := Nat.card_le_card_of_injective f hf
    _ = Nat.card R ^ 3 := by rw [Nat.card_fun]; simp
    _ ≤ p ^ 3 := by
      apply Nat.pow_le_pow_left
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact hR

theorem exists_frame [Finite K] (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (E₀ : Subgroup (StatedSp 3 K)) (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x)
    (hpow : ∀ x ∈ E₀, x ^ p = 1) (hcard : Nat.card E₀ = p ^ 3) :
    ∃ A : StatedSp 3 K, E₀.map (MulAut.conj A).toMonoidHom = spTorus p 3 K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let e : TauCeti.GLSymplecticFin 3 K ≃* StatedSp 3 K :=
    CFSG.LieType.Universal.Symplectic.equivStatedSp 3 K
  let E₁ : Subgroup (TauCeti.GLSymplecticFin 3 K) := E₀.comap e.toMonoidHom
  have hmem : ∀ x : StatedSp 3 K, x ∈ E₀ → e.symm x ∈ E₁ := by
    intro x hx
    show e (e.symm x) ∈ E₀
    rw [MulEquiv.apply_symm_apply]
    exact hx
  have hcomm₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    apply e.injective
    rw [map_mul, map_mul]
    exact hcomm _ hx _ hy
  have hexp₁ : ∀ x ∈ E₁, x ^ p = 1 := by
    intro x hx
    apply e.injective
    rw [map_pow, map_one]
    exact hpow _ hx
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.CTP.exists_symplectic_conj_diagonal ⟨ζ, hζ⟩ E₁ hcomm₁ hexp₁
  refine ⟨e P⁻¹, ?_⟩
  have key : ∀ x ∈ E₀, MulAut.conj (e P⁻¹) x ∈ spTorus p 3 K := by
    intro x hx
    obtain ⟨u, hu⟩ := hP (e.symm x) (hmem x hx)
    have h1 : P⁻¹ * e.symm x * P = TauCeti.GLSymplecticFin.diagonal u := by
      rw [mul_assoc, hu, inv_mul_cancel_left]
    have h2 : MulAut.conj (e P⁻¹) x = e (TauCeti.GLSymplecticFin.diagonal u) := by
      rw [← h1, MulAut.conj_apply, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, inv_inv]
    have hpowu : (TauCeti.GLSymplecticFin.diagonal u) ^ p = 1 := by
      rw [← h1]
      have hy : (e.symm x) ^ p = 1 := hexp₁ _ (hmem x hx)
      calc (P⁻¹ * e.symm x * P) ^ p = (MulAut.conj P⁻¹ (e.symm x)) ^ p := by
            rw [MulAut.conj_apply, inv_inv]
        _ = MulAut.conj P⁻¹ ((e.symm x) ^ p) := (map_pow _ _ _).symm
        _ = 1 := by rw [hy, map_one]
    rw [h2]
    refine ⟨fun i => (u i : K), fun i => ?_, ?_⟩
    · have hu' : u ^ p = 1 := by
        apply TauCeti.GLSymplecticFin.diagonal_injective
        rw [map_pow, map_one]
        exact hpowu
      have := congrFun hu' i
      rw [Pi.pow_apply, Pi.one_apply] at this
      simpa using congrArg (fun z : Kˣ => (z : K)) this
    · rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_equiv_diagonal]
      congr 1
      funext c
      rcases c with i | i <;> simp [Units.val_inv_eq_inv_val]
  have hle : E₀.map (MulAut.conj (e P⁻¹)).toMonoidHom ≤ spTorus p 3 K := by
    rintro _ ⟨x, hx, rfl⟩
    exact key x hx
  have hcard1 : Nat.card (E₀.map (MulAut.conj (e P⁻¹)).toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (e P⁻¹)).injective]
    exact hcard
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1]; exact card_spTorus_le hp.pos)

end CFSG.RankThree.PartOne.KFCL.Sp
