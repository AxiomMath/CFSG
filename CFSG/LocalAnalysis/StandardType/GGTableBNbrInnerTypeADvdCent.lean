module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType.TypeANbrDvd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA

variable {d p : ℕ} {K : Type} [Field K]

theorem exists_perm_forall_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {R : Type*}
    [CommRing R] {M : Matrix n n R} (h : M.det ≠ 0) : ∃ σ : Equiv.Perm n, ∀ i, M (σ i) i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨i, hi⟩ := hcon σ
  rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i) hi, smul_zero]

theorem exists_ne_of_four (hd : 5 ≤ d) (a b c e : Fin d) :
    ∃ i, i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ e := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, e} : Finset (Fin d))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_four.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact ⟨i, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2⟩

theorem exists_ne_of_two (hd : 3 ≤ d) (a b : Fin d) : ∃ i, i ≠ a ∧ i ≠ b := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset (Fin d))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  exact ⟨i, hi.1, hi.2⟩

theorem isDiag_of_mul_diagonal_pairVec {s : Matrix (Fin d) (Fin d) K} (hs : s.det ≠ 0)
    (hd : 5 ≤ d) {ζ : K} (hζ : ζ ≠ ζ⁻¹)
    (h : ∀ k l : Fin d, k ≠ l → ∃ c : K,
      s * diagonal (ggPairVec k l ζ) = c • (diagonal (ggPairVec k l ζ) * s)) :
    s.IsDiag := by
  obtain ⟨π, hπ⟩ := exists_perm_forall_ne_zero hs
  intro a b hab
  by_contra hne
  obtain ⟨c, hc⟩ := h a b hab
  have key : ∀ i j, s i j ≠ 0 → ggPairVec a b ζ j = c * ggPairVec a b ζ i := by
    intro i j hij
    have h1 := congrFun (congrFun hc i) j
    rw [mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul] at h1
    apply mul_right_cancel₀ hij
    linear_combination h1
  have hv : ∀ m, m ≠ a → m ≠ b → ggPairVec a b ζ m = 1 := fun m hma hmb => by
    rw [ggPairVec_apply, ite_eq_right hma, ite_eq_right hmb, mul_one]
  obtain ⟨i, hia, hib, hia', hib'⟩ := exists_ne_of_four hd a b (π.symm a) (π.symm b)
  have hπa : π i ≠ a := fun h => hia' (by rw [← h, Equiv.symm_apply_apply])
  have hπb : π i ≠ b := fun h => hib' (by rw [← h, Equiv.symm_apply_apply])
  have hc1 : c = 1 := by
    have h1 := key (π i) i (hπ i)
    rw [hv i hia hib, hv (π i) hπa hπb, mul_one] at h1
    exact h1.symm
  have hva : ggPairVec a b ζ a = ζ := by
    rw [ggPairVec_apply, ite_eq_left rfl, ite_eq_right hab, mul_one]
  have hvb : ggPairVec a b ζ b = ζ⁻¹ := by
    rw [ggPairVec_apply, ite_eq_right (Ne.symm hab), ite_eq_left rfl, one_mul]
  have h2 := key a b hne
  rw [hva, hvb, hc1, one_mul] at h2
  exact hζ h2.symm

section Cover

variable {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem exists_scalar_of_map_conj_eq [Finite K] (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {g : SpecialLinearGroup (Fin d) K} (h : ∀ y, φ' (g * y * g⁻¹) = φ' y) :
    ∃ c : K, (g : Matrix (Fin d) (Fin d) K) = scalar (Fin d) c := by
  have h1 : conjAut d K (SpecialLinearGroup.toGL g) = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective d K x
    rw [conjAut_proj, slConjugation_toGL_eq, MulAut.one_apply, proj_eq_proj_iff]
    apply hφker
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact exists_scalar_of_conjAut_eq_one h1

theorem isDiag_of_conj_comm [Finite K] (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) (hd : 5 ≤ d)
    {ζ : K} (hζ : ζ ≠ ζ⁻¹) {s : SpecialLinearGroup (Fin d) K}
    (h : ∀ k l : Fin d, k ≠ l → ∀ D : SpecialLinearGroup (Fin d) K,
      (D : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l ζ) →
      MulAut.conj (φ' s) * MulAut.conj (φ' D) = MulAut.conj (φ' D) * MulAut.conj (φ' s)) :
    (s : Matrix (Fin d) (Fin d) K).IsDiag := by
  have hζ0 : ζ ≠ 0 := fun h0 => hζ (by rw [h0, _root_.inv_zero])
  refine isDiag_of_mul_diagonal_pairVec (by rw [s.2]; exact one_ne_zero) hd hζ fun k l hkl => ?_
  set D : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal (ggPairVec k l ζ), by rw [det_diagonal, prod_ggPairVec ζ hζ0]⟩ with hD
  have hDm : (D : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l ζ) := rfl
  have h1 : MulAut.conj (φ' s * φ' D) = MulAut.conj (φ' D * φ' s) := by
    rw [map_mul, map_mul, h k l hkl D hDm]
  set g : SpecialLinearGroup (Fin d) K := (D * s)⁻¹ * (s * D) with hg
  have hgφ : φ' g = (φ' D * φ' s)⁻¹ * (φ' s * φ' D) := by
    rw [hg, map_mul, map_inv, map_mul, map_mul]
  have hgy : ∀ y, φ' (g * y * g⁻¹) = φ' y := by
    intro y
    have h3 : (φ' s * φ' D) * φ' y * (φ' s * φ' D)⁻¹ =
        (φ' D * φ' s) * φ' y * (φ' D * φ' s)⁻¹ := by
      have := congrArg (fun f : MulAut L' => f (φ' y)) h1
      simpa only [MulAut.conj_apply] using this
    rw [map_mul, map_mul, map_inv, hgφ]
    calc (φ' D * φ' s)⁻¹ * (φ' s * φ' D) * φ' y * ((φ' D * φ' s)⁻¹ * (φ' s * φ' D))⁻¹
        = (φ' D * φ' s)⁻¹ * ((φ' s * φ' D) * φ' y * (φ' s * φ' D)⁻¹) * (φ' D * φ' s) := by
          group
      _ = (φ' D * φ' s)⁻¹ * ((φ' D * φ' s) * φ' y * (φ' D * φ' s)⁻¹) * (φ' D * φ' s) := by
          rw [h3]
      _ = φ' y := by group
  obtain ⟨c, hc⟩ := exists_scalar_of_map_conj_eq hφker hgy
  refine ⟨c, ?_⟩
  have h4 : s * D = D * s * g := by rw [hg]; group
  have h5 := congrArg (fun x : SpecialLinearGroup (Fin d) K => (x : Matrix (Fin d) (Fin d) K)) h4
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h5
  rw [hDm] at h5
  rw [h5, hc, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem conj_mem_of_selfCent {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) {D : SpecialLinearGroup (Fin d) K}
    {u : Fin d → K} (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal u) (hu : ∀ i, u i ^ p = 1) :
    MulAut.conj (φ' D) ∈ A := by
  refine hsc (φ' D) (fun a ha => ?_) ?_
  · obtain ⟨t, hat⟩ := hdiag a ha
    exact hat.apply_of_isDiag (by rw [hD]; exact isDiag_diagonal u)
  · rw [← map_pow, pow_eq_one_of_diagonal hD hu, map_one]

variable [CharP K 2]

theorem ActsDiag.eq_one_of_conj_perm_of_two_le (hd : 2 ≤ d)
    (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {b : MulAut L'} {t : Fin d → K}
    (hb : ActsDiag φ' b t)
    (hfix : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (φ' (permSL σ)) * b * (MulAut.conj (φ' (permSL σ)))⁻¹ = b) : b = 1 := by
  refine hb.eq_one (by omega) hφ's fun i j => ?_
  by_cases hij : i = j
  · rw [hij]
  have h1 := hb.conj_perm (Equiv.swap i j)
  rw [hfix] at h1
  have h2 := hb.ratio hφker h1 hij
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] at h2
  field_simp [hb.ne_zero i, hb.ne_zero j] at h2
  apply CharTwo.sq_inj.mp
  simpa only [sq] using h2

theorem ActsDiag.eq_one_of_conj_perm (hd : 3 ≤ d) (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {b : MulAut L'} {t : Fin d → K}
    (hb : ActsDiag φ' b t)
    (hfix : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (φ' (permSL σ)) * b * (MulAut.conj (φ' (permSL σ)))⁻¹ = b) : b = 1 :=
  hb.eq_one_of_conj_perm_of_two_le (by omega) hφ's hφker hfix

theorem conj_mem_of_invariant (hp : p.Prime) (hd : 0 < d) (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A A' : Subgroup (MulAut L')} (hA'A : A' ≤ A)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t)
    (hAp : ∀ a ∈ A, a ^ p = 1)
    (hA'inv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A',
      MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ ∈ A')
    {a₀ : MulAut L'} (ha₀ : a₀ ∈ A') (ha₀1 : a₀ ≠ 1) {D : SpecialLinearGroup (Fin d) K}
    {u : Fin d → K} (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal u) (hu : ∀ i, u i ^ p = 1) :
    MulAut.conj (φ' D) ∈ A' := by
  classical
  have := Fact.mk hp
  obtain ⟨t, hat⟩ := hdiag a₀ (hA'A ha₀)
  obtain ⟨i, j, hij⟩ : ∃ i j, t i ≠ t j := by
    by_contra hcon
    push Not at hcon
    exact ha₀1 (hat.eq_one hd hφ's hcon)
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  obtain ⟨lam, hlam⟩ : ∃ lam : K, t i * (t j)⁻¹ = lam := ⟨_, rfl⟩
  have hlam1 : lam ≠ 1 := by
    rw [← hlam]
    intro h
    exact hij ((mul_inv_eq_one₀ (hat.ne_zero j)).mp h)
  have hlamp : lam ^ p = 1 := by
    rw [← hlam]
    exact hat.ratio_pow hφker (hAp a₀ (hA'A ha₀)) i j
  have hlamprim : IsPrimitiveRoot lam p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hlamp hlam1)
  have hlam0 : lam ≠ 0 := hlamprim.ne_zero hp.ne_zero
  set τ := Equiv.swap i j with hτ
  set b := a₀ * (MulAut.conj (φ' (permSL τ)) * a₀ * (MulAut.conj (φ' (permSL τ)))⁻¹)⁻¹ with hb
  have hbA' : b ∈ A' := A'.mul_mem ha₀ (A'.inv_mem (hA'inv τ a₀ ha₀))
  have hbt : ActsDiag φ' b (ggPairVec i j lam) := by
    rw [← hlam, ← mul_inv_comp_swap hat.ne_zero hij']
    exact hat.mul (hat.conj_perm τ).inv
  set D₀ : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal (ggPairVec i j lam), by rw [det_diagonal, prod_ggPairVec lam hlam0]⟩ with hD₀
  have hD₀m : (D₀ : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i j lam) := rfl
  have hbD₀ : GGActsBy φ' b D₀ := ggActsBy_of_actsDiag hD₀m hbt
  have huniq : ∀ {a b : MulAut L'} {D E : SpecialLinearGroup (Fin d) K} {t : Fin d → K},
      (D : Matrix (Fin d) (Fin d) K) = diagonal t → (E : Matrix (Fin d) (Fin d) K) = diagonal t →
      GGActsBy φ' a D → GGActsBy φ' b E → a = b := by
    intro a b D E t hD hE ha hb
    have hDE : D = E := Subtype.ext (hD.trans hE.symm)
    subst hDE
    exact GGActsBy.unique hφ's ha hb
  have hconj : ∀ E : SpecialLinearGroup (Fin d) K, GGActsBy φ' (MulAut.conj (φ' E)) E :=
    fun E s => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hfull : ∀ v : Fin d → K, (∀ i, v i ^ p = 1) → ∏ i, v i = 1 →
      ∃ a ∈ A, ∃ E : SpecialLinearGroup (Fin d) K,
        (E : Matrix (Fin d) (Fin d) K) = diagonal v ∧ GGActsBy φ' a E := by
    intro v hv hvp
    exact ⟨_, conj_mem_of_selfCent hsc hdiag (D := ⟨diagonal v, by rw [det_diagonal, hvp]⟩) rfl hv,
      ⟨diagonal v, by rw [det_diagonal, hvp]⟩, rfl, hconj _⟩
  have hPv : ∀ k l : Fin d, k ≠ l → ∀ m : ℕ, ∀ c ∈ A, ∀ E : SpecialLinearGroup (Fin d) K,
      (E : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l (lam ^ m)) →
      GGActsBy φ' c E → c ∈ A' := by
    intro k l hkl m c _ E hE hcE
    obtain ⟨σ, hσk, hσl⟩ := exists_perm_pair hkl hij'
    have hpowmat : ((D₀ ^ m : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (ggPairVec i j (lam ^ m)) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, hD₀m, diagonal_pow, ← ggPairVec_pow]
      rfl
    have hσmat := coe_permSL_conj hpowmat σ
    rw [ggPairVec_comp_of hσk hσl] at hσmat
    rw [huniq hE hσmat hcE ((hbD₀.pow m).conj (permSL σ))]
    exact hA'inv σ _ (A'.pow_mem hbA' m)
  obtain ⟨c', -, hc'A', E', hE', hc'E'⟩ := exists_ggActsBy_of_gen hfull hlamprim hp hd
    (fun c => c ∈ A') A'.one_mem (fun a _ b _ ha hb => A'.mul_mem ha hb) hPv hu
    (by have h := D.2; rwa [hD, det_diagonal] at h)
  rw [huniq hD hE' (hconj D) hc'E']
  exact hc'A'

end Cover

end CFSG.StandardType.TypeANbrDvd

end
