module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LieType.Chevalley.RationalToralSignDiagramTheta
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootComb
public import CFSG.LieType.Chevalley.C2E6UnitaryFourCompound
public import CFSG.LieType.Chevalley.RootGramNull
public import CFSG.LocalAnalysis.StandardType.GGJ4dOrthogonalRank
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Pieces

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus


private theorem iform_self_E6
    {v : Fin Tag.E6.rank → ℤ} (hv : IsRoot Tag.E6 v) :
    iform v v = 2 :=
  CFSG.LieType.SeitzGeneration.ExcHighThree.kr_iform_self (Or.inr (Or.inl rfl)) hv

private theorem det_gram_four
    {a₁ a₂ b₁ b₂ : Fin Tag.E6.rank → ℤ}
    (ha : iform a₁ a₂ = -1) (hb : iform b₁ b₂ = -1)
    (hab : ∀ x ∈ ({a₁, a₂} : Finset (Fin Tag.E6.rank → ℤ)),
      ∀ y ∈ ({b₁, b₂} : Finset (Fin Tag.E6.rank → ℤ)), iform x y = 0)
    (n₁ : iform a₁ a₁ = 2) (n₂ : iform a₂ a₂ = 2) (n₃ : iform b₁ b₁ = 2)
    (n₄ : iform b₂ b₂ = 2) :
    (Matrix.of fun i j : Fin 4 => iform (![a₁, a₂, b₁, b₂] i) (![a₁, a₂, b₁, b₂] j)).det = 9 := by
  have hc : ∀ i j : Fin 4, iform (![a₁, a₂, b₁, b₂] i) (![a₁, a₂, b₁, b₂] j) =
      !![2, -1, 0, 0; -1, 2, 0, 0; 0, 0, 2, -1; 0, 0, -1, 2] i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [ha, hb, n₁, n₂, n₃, n₄, hab, iform_comm a₂ a₁, iform_comm b₁ a₁,
        iform_comm b₂ a₁, iform_comm b₁ a₂, iform_comm b₂ a₂, iform_comm b₂ b₁]
  rw [show (Matrix.of fun i j : Fin 4 => iform (![a₁, a₂, b₁, b₂] i) (![a₁, a₂, b₁, b₂] j)) =
      !![2, -1, 0, 0; -1, 2, 0, 0; 0, 0, 2, -1; 0, 0, -1, 2] from Matrix.ext hc]
  decide +kernel

private def gram5 (c₁ c₂ c₃ c₄ : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, -1, 0, 0, c₁; -1, 2, 0, 0, c₂; 0, 0, 2, -1, c₃; 0, 0, -1, 2, c₄;
    c₁, c₂, c₃, c₄, 2]

private theorem gram5_det (c₁ c₂ c₃ c₄ : ℤ) :
    (gram5 c₁ c₂ c₃ c₄).det =
      18 - 6 * (c₁ ^ 2 + c₁ * c₂ + c₂ ^ 2 + c₃ ^ 2 + c₃ * c₄ + c₄ ^ 2) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_one]
  simp only [gram5, CFSG.LieType.Chevalley.C2E6Overlap.det_fin_four, Matrix.submatrix_apply,
    Fin.succAbove, Fin.castSucc, Fin.succ]
  simp
  ring

private theorem gram_five_eq
    {a₁ a₂ b₁ b₂ δ : Fin Tag.E6.rank → ℤ}
    (ha : iform a₁ a₂ = -1) (hb : iform b₁ b₂ = -1)
    (hab : ∀ x ∈ ({a₁, a₂} : Finset (Fin Tag.E6.rank → ℤ)),
      ∀ y ∈ ({b₁, b₂} : Finset (Fin Tag.E6.rank → ℤ)), iform x y = 0)
    (n₁ : iform a₁ a₁ = 2) (n₂ : iform a₂ a₂ = 2) (n₃ : iform b₁ b₁ = 2)
    (n₄ : iform b₂ b₂ = 2) (n₅ : iform δ δ = 2) :
    (Matrix.of fun i j : Fin 5 =>
        iform (![a₁, a₂, b₁, b₂, δ] i) (![a₁, a₂, b₁, b₂, δ] j)) =
      gram5 (iform a₁ δ) (iform a₂ δ) (iform b₁ δ) (iform b₂ δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram5, ha, hb, n₁, n₂, n₃, n₄, n₅, hab, iform_comm a₂ a₁, iform_comm b₁ a₁,
      iform_comm b₂ a₁, iform_comm b₁ a₂, iform_comm b₂ a₂, iform_comm b₂ b₁,
      iform_comm δ a₁, iform_comm δ a₂, iform_comm δ b₁, iform_comm δ b₂]

private theorem compRank_union_two_eq_four
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {i₁ i₂ : KernelComponent χ}
    (hne : i₁ ≠ i₂) (h₁ : compRank (componentRoots χ i₁) = 2)
    (h₂ : compRank (componentRoots χ i₂) = 2) :
    compRank (componentRoots χ i₁ ∪ componentRoots χ i₂) = 4 := by
  classical
  let A := componentRoots χ i₁
  let B := componentRoots χ i₂
  let Ψ : Fin 2 → Set (Fin Tag.E6.rank → ℤ) := fun i => if i = 0 then A else B
  have horth : ∀ x ∈ A, ∀ y ∈ B, iform x y = 0 := by
    intro x hx y hy
    exact iform_eq_zero_of_mem_componentRoots hne (by simpa [A] using hx)
      (by simpa [B] using hy)
  have horthΨ : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      i ≠ j → ∀ x ∈ Ψ i, ∀ y ∈ Ψ j, iform x y = 0 := by
    intro i _ j _ hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [Ψ, A, B] using horth x hx y hy
    · simpa [Ψ, A, B, iform_comm] using horth y hy x hx
    · exact absurd rfl hij
  have hUnion : (⋃ i : Fin 2, Ψ i) = A ∪ B := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (by simpa [Ψ] using hi)
      · exact Or.inr (by simpa [Ψ] using hi)
    · rintro (hx | hx)
      · exact ⟨0, by simpa [Ψ] using hx⟩
      · exact ⟨1, by simpa [Ψ] using hx⟩
  have hadd := compRank_iUnion_finset_eq_sum (s := (Finset.univ : Finset (Fin 2))) Ψ horthΨ
  have h4 : compRank (A ∪ B) = 4 := by
    simpa [hUnion, Ψ, A, B, Fin.sum_univ_two, h₁, h₂] using hadd
  simpa [A, B] using h4

private theorem castSucc_five {α : Type*} (a₁ a₂ b₁ b₂ δ : α) :
    ∀ i : Fin 4, (![a₁, a₂, b₁, b₂, δ] : Fin 5 → α) i.castSucc = ![a₁, a₂, b₁, b₂] i := by
  intro i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl

private theorem no_int_sq_mul_9 {m d : ℤ} (hd : d = 4 ∨ d = 5) (h : 9 = m ^ 2 * d) : False := by
  have h1 : 1 < m ^ 2 := by rcases hd with rfl | rfl <;> nlinarith
  have h2 : m ^ 2 < 5 := by rcases hd with rfl | rfl <;> nlinarith
  have hlo : -2 ≤ m := by
    by_contra hlt
    have hm3 : m ≤ -3 := by omega
    nlinarith [sq_nonneg (m + 3)]
  have hhi : m ≤ 2 := by
    by_contra hlt
    have hm3 : 3 ≤ m := by omega
    nlinarith [sq_nonneg (m - 3)]
  interval_cases m <;> rcases hd with rfl | rfl <;> nlinarith

private theorem no_int_sq_four {m K : ℤ} (h : m ^ 2 * 4 = 18 - 6 * K) (h0 : 0 ≤ K)
    (h3 : K ≠ 3) : False := by
  have hKle : K ≤ 3 := by nlinarith [sq_nonneg m]
  have hK : K = 0 ∨ K = 1 ∨ K = 2 := by omega
  have hm1 : 1 < m ^ 2 := by rcases hK with rfl | rfl | rfl <;> nlinarith
  have hm5 : m ^ 2 < 5 := by rcases hK with rfl | rfl | rfl <;> nlinarith
  have hlo : -2 ≤ m := by
    by_contra hlt
    have hm3 : m ≤ -3 := by omega
    nlinarith [sq_nonneg (m + 3)]
  have hhi : m ≤ 2 := by
    by_contra hlt
    have hm3 : 3 ≤ m := by omega
    nlinarith [sq_nonneg (m - 3)]
  interval_cases m <;> rcases hK with rfl | rfl | rfl <;> nlinarith

private theorem exists_det_gram_eq_sq_mul_cartan
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ) (hne : Ψ.Nonempty)
    {k : ℕ} (e' : simpleRoots Ψ ≃ Fin k) (D : Fin k → Fin Tag.E6.rank → ℤ)
    (hD : ∀ i, D i ∈ Ψ) :
    ∃ (t : TauCeti.DynkinType) (m : ℤ), t.Valid ∧ t.IsSimplyLaced ∧
      (simpleRoots Ψ).card = t.rank ∧ Ψ.ncard = t.numRoots ∧
      (Matrix.of fun i j => iform (D i) (D j)).det = m ^ 2 * t.cartanMatrix.det := by
  classical
  obtain ⟨t, e, ht, hsl, hiform, hcard, hN⟩ :=
    exists_dynkinType (τ := Tag.E6) (Or.inr (Or.inl rfl)) hΨ hne
  obtain ⟨m, hm⟩ := exists_det_gram_eq_sq_mul (τ := Tag.E6) hΨ e' D hD
  have hmat : (Matrix.of fun i j : Fin k =>
      iform ((e'.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)
        ((e'.symm j : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)) =
      t.cartanMatrix.submatrix (e'.symm.trans e) (e'.symm.trans e) := by
    ext i j
    rw [Matrix.of_apply, Matrix.submatrix_apply, Equiv.trans_apply]
    exact hiform (e'.symm i) (e'.symm j)
  have hdet : (Matrix.of fun i j : Fin k =>
      iform ((e'.symm i : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)
        ((e'.symm j : simpleRoots Ψ) : Fin Tag.E6.rank → ℤ)).det = t.cartanMatrix.det := by
    rw [hmat, Matrix.det_submatrix_equiv_self]
  exact ⟨t, m, ht, hsl, hcard, hN, by rw [hm, hdet]⟩

private theorem false_of_rank_four
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h4 : compRank Ψ = 4)
    {a₁ a₂ b₁ b₂ : Fin Tag.E6.rank → ℤ} (ha₁ : a₁ ∈ Ψ) (ha₂ : a₂ ∈ Ψ)
    (hb₁ : b₁ ∈ Ψ) (hb₂ : b₂ ∈ Ψ)
    (hgram : (Matrix.of fun i j : Fin 4 =>
      iform (![a₁, a₂, b₁, b₂] i) (![a₁, a₂, b₁, b₂] j)).det = 9) : False := by
  classical
  have hcard : (simpleRoots Ψ).card = 4 :=
    (CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card (τ := Tag.E6) hΨ).symm.trans h4
  let e' : simpleRoots Ψ ≃ Fin 4 :=
    Fintype.equivFinOfCardEq (by simpa [Fintype.card_coe] using hcard)
  let D : Fin 4 → Fin Tag.E6.rank → ℤ := ![a₁, a₂, b₁, b₂]
  have hD : ∀ i, D i ∈ Ψ := by
    intro i
    fin_cases i
    · simpa [D] using ha₁
    · simpa [D] using ha₂
    · simpa [D] using hb₁
    · simpa [D] using hb₂
  obtain ⟨t, m, ht, hsl, hcardt, -, hdet⟩ :=
    exists_det_gram_eq_sq_mul_cartan hΨ ⟨a₁, ha₁⟩ e' D hD
  have hrank : t.rank = 4 := by omega
  have hgramD : (Matrix.of fun i j : Fin 4 => iform (D i) (D j)).det = 9 := by
    simpa [D] using hgram
  have hm : (9 : ℤ) = m ^ 2 * t.cartanMatrix.det := by rw [← hgramD]; exact hdet
  rcases det_cartanMatrix_of_isSimplyLaced ht hsl with
      ⟨-, hdA⟩ | ⟨-, -, hdD⟩ | ⟨hE6, hd6⟩ | ⟨hE7, hd7⟩ | ⟨hE8, hd8⟩
  · rw [hdA, hrank] at hm
    norm_num at hm
    exact no_int_sq_mul_9 (Or.inr rfl) hm
  · rw [hdD] at hm
    exact no_int_sq_mul_9 (Or.inl rfl) hm
  · rw [hE6, TauCeti.DynkinType.rank_E6] at hrank
    omega
  · rw [hE7, TauCeti.DynkinType.rank_E7] at hrank
    omega
  · rw [hE8, TauCeti.DynkinType.rank_E8] at hrank
    omega

private theorem toRat_mem_span_of_sum_smul_eq_zero
    {A B : Set (Fin Tag.E6.rank → ℤ)} {a₁ a₂ b₁ b₂ δ : Fin Tag.E6.rank → ℤ}
    (ha₁ : a₁ ∈ A ∪ B) (ha₂ : a₂ ∈ A ∪ B) (hb₁ : b₁ ∈ A ∪ B) (hb₂ : b₂ ∈ A ∪ B)
    {x : Fin 5 → ℤ} (hx4 : x (Fin.last 4) ≠ 0)
    (hrel : ∑ i, x i • ![a₁, a₂, b₁, b₂, δ] i = 0) :
    (fun i => (δ i : ℚ)) ∈
      Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) '' (A ∪ B)) := by
  classical
  have hsplit : (∑ i : Fin 4, x i.castSucc • ![a₁, a₂, b₁, b₂, δ] i.castSucc) +
      x (Fin.last 4) • ![a₁, a₂, b₁, b₂, δ] (Fin.last 4) = 0 := by
    rw [← Fin.sum_univ_castSucc (fun i : Fin 5 => x i • ![a₁, a₂, b₁, b₂, δ] i)]
    exact hrel
  have hQ : (∑ j : Fin 4, (x j.castSucc : ℚ) •
        (fun i => ((![a₁, a₂, b₁, b₂] j) i : ℚ))) +
      (x (Fin.last 4) : ℚ) • (fun i => (δ i : ℚ)) = 0 := by
    have h := congrArg (fun v : Fin Tag.E6.rank → ℤ => fun i => (v i : ℚ)) hsplit
    funext i
    have hi := congrFun h i
    simpa [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add,
      Int.cast_sum, Int.cast_mul, Int.cast_zero, castSucc_five] using hi
  have hδeq : (fun i => (δ i : ℚ)) = -(((x (Fin.last 4) : ℚ)⁻¹) •
      (∑ j : Fin 4, (x j.castSucc : ℚ) •
        (fun i => ((![a₁, a₂, b₁, b₂] j) i : ℚ)))) := by
    have hxq : (x (Fin.last 4) : ℚ) ≠ 0 := by exact_mod_cast hx4
    have h1 : (x (Fin.last 4) : ℚ) • (fun i => (δ i : ℚ)) = -(∑ j : Fin 4,
        (x j.castSucc : ℚ) • (fun i => ((![a₁, a₂, b₁, b₂] j) i : ℚ))) :=
      eq_neg_of_add_eq_zero_right hQ
    calc (fun i => (δ i : ℚ))
        = ((x (Fin.last 4) : ℚ)⁻¹ * (x (Fin.last 4) : ℚ)) • (fun i => (δ i : ℚ)) := by
          rw [inv_mul_cancel₀ hxq, one_smul]
      _ = ((x (Fin.last 4) : ℚ)⁻¹) • ((x (Fin.last 4) : ℚ) • (fun i => (δ i : ℚ))) := by
          rw [smul_smul]
      _ = ((x (Fin.last 4) : ℚ)⁻¹) • (-(∑ j : Fin 4, (x j.castSucc : ℚ) •
        (fun i => ((![a₁, a₂, b₁, b₂] j) i : ℚ)))) := by rw [h1]
      _ = -(((x (Fin.last 4) : ℚ)⁻¹) • (∑ j : Fin 4, (x j.castSucc : ℚ) •
        (fun i => ((![a₁, a₂, b₁, b₂] j) i : ℚ)))) := by rw [smul_neg]
  rw [hδeq]
  refine Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_)
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨![a₁, a₂, b₁, b₂] j, ?_, rfl⟩
  fin_cases j
  · simpa using ha₁
  · simpa using ha₂
  · simpa using hb₁
  · simpa using hb₂

private theorem mulVec_eq_zero_of_sum_smul_eq_zero
    {a₁ a₂ b₁ b₂ : Fin Tag.E6.rank → ℤ} {x : Fin 4 → ℤ}
    (hrel : ∑ i : Fin 4, x i • ![a₁, a₂, b₁, b₂] i = 0) :
    Matrix.mulVec (Matrix.of fun i j : Fin 4 =>
      iform (![a₁, a₂, b₁, b₂] i) (![a₁, a₂, b₁, b₂] j)) x = 0 := by
  funext j
  rw [Matrix.mulVec_apply_eq_sum]
  have hp : iform (![a₁, a₂, b₁, b₂] j) (∑ i : Fin 4, x i • ![a₁, a₂, b₁, b₂] i) = 0 := by
    rw [hrel]
    simp [iform]
  calc ∑ i : Fin 4,
        (Matrix.of fun i j : Fin 4 => iform (![a₁, a₂, b₁, b₂] i) (![a₁, a₂, b₁, b₂] j)) j i *
          x i
      = ∑ i : Fin 4, iform (![a₁, a₂, b₁, b₂] j) (x i • ![a₁, a₂, b₁, b₂] i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.of_apply, iform_smul_right]
        ring
    _ = iform (![a₁, a₂, b₁, b₂] j) (∑ i : Fin 4, x i • ![a₁, a₂, b₁, b₂] i) := by
        rw [iform_finset_sum_right]
    _ = 0 := hp

private theorem gram5_det_ne_zero
    {A B : Set (Fin Tag.E6.rank → ℤ)} {a₁ a₂ b₁ b₂ δ : Fin Tag.E6.rank → ℤ}
    (ha₁ : a₁ ∈ A ∪ B) (ha₂ : a₂ ∈ A ∪ B) (hb₁ : b₁ ∈ A ∪ B) (hb₂ : b₂ ∈ A ∪ B)
    (hδout : (fun i => (δ i : ℚ)) ∉
      Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) '' (A ∪ B)))
    (ha : iform a₁ a₂ = -1) (hb : iform b₁ b₂ = -1)
    (horth : ∀ x ∈ ({a₁, a₂} : Finset (Fin Tag.E6.rank → ℤ)),
      ∀ y ∈ ({b₁, b₂} : Finset (Fin Tag.E6.rank → ℤ)), iform x y = 0)
    (hn₁ : iform a₁ a₁ = 2) (hn₂ : iform a₂ a₂ = 2) (hn₃ : iform b₁ b₁ = 2)
    (hn₄ : iform b₂ b₂ = 2) (hn₅ : iform δ δ = 2) :
    (gram5 (iform a₁ δ) (iform a₂ δ) (iform b₁ δ) (iform b₂ δ)).det ≠ 0 := by
  classical
  intro hzero
  have hgram : (Matrix.of fun i j : Fin 5 =>
      iform (![a₁, a₂, b₁, b₂, δ] i) (![a₁, a₂, b₁, b₂, δ] j)) =
      gram5 (iform a₁ δ) (iform a₂ δ) (iform b₁ δ) (iform b₂ δ) :=
    gram_five_eq ha hb horth hn₁ hn₂ hn₃ hn₄ hn₅
  have hdet5 : (Matrix.of fun i j : Fin 5 =>
      iform (![a₁, a₂, b₁, b₂, δ] i) (![a₁, a₂, b₁, b₂, δ] j)).det = 0 := by
    rw [hgram]
    exact hzero
  obtain ⟨x, hxne, hrel⟩ := exists_sum_smul_eq_zero_of_det_gram_eq_zero
    (τ := Tag.E6) ![a₁, a₂, b₁, b₂, δ] hdet5
  have hsplit : (∑ i : Fin 4, x i.castSucc • ![a₁, a₂, b₁, b₂, δ] i.castSucc) +
      x (Fin.last 4) • ![a₁, a₂, b₁, b₂, δ] (Fin.last 4) = 0 := by
    rw [← Fin.sum_univ_castSucc (fun i : Fin 5 => x i • ![a₁, a₂, b₁, b₂, δ] i)]
    exact hrel
  by_cases hx4 : x (Fin.last 4) = 0
  · have hrel4 : ∑ i : Fin 4, x i.castSucc • ![a₁, a₂, b₁, b₂] i = 0 := by
      have h0 : x (Fin.last 4) • ![a₁, a₂, b₁, b₂, δ] (Fin.last 4) = 0 := by
        rw [hx4]
        simp
      rw [h0, add_zero] at hsplit
      simpa [castSucc_five] using hsplit
    have hx'ne : (fun i : Fin 4 => x i.castSucc) ≠ 0 := by
      intro h0
      apply hxne
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact congrFun h0 j
      · exact hx4
    have hmul := mulVec_eq_zero_of_sum_smul_eq_zero hrel4
    have hdet4 : (Matrix.of fun i j : Fin 4 =>
        iform (![a₁, a₂, b₁, b₂] i) (![a₁, a₂, b₁, b₂] j)).det ≠ 0 := by
      rw [det_gram_four ha hb horth hn₁ hn₂ hn₃ hn₄]
      norm_num
    exact hdet4 (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hx'ne, hmul⟩)
  · exact hδout (toRat_mem_span_of_sum_smul_eq_zero ha₁ ha₂ hb₁ hb₂ hx4 hrel)

private theorem gram5_K_bounds
    {A B : Set (Fin Tag.E6.rank → ℤ)} {a₁ a₂ b₁ b₂ δ : Fin Tag.E6.rank → ℤ}
    (ha₁ : a₁ ∈ A ∪ B) (ha₂ : a₂ ∈ A ∪ B) (hb₁ : b₁ ∈ A ∪ B) (hb₂ : b₂ ∈ A ∪ B)
    (hδout : (fun i => (δ i : ℚ)) ∉
      Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) '' (A ∪ B)))
    (ha : iform a₁ a₂ = -1) (hb : iform b₁ b₂ = -1)
    (horth : ∀ x ∈ ({a₁, a₂} : Finset (Fin Tag.E6.rank → ℤ)),
      ∀ y ∈ ({b₁, b₂} : Finset (Fin Tag.E6.rank → ℤ)), iform x y = 0)
    (hn₁ : iform a₁ a₁ = 2) (hn₂ : iform a₂ a₂ = 2) (hn₃ : iform b₁ b₁ = 2)
    (hn₄ : iform b₂ b₂ = 2) (hn₅ : iform δ δ = 2) :
    0 ≤ iform a₁ δ ^ 2 + iform a₁ δ * iform a₂ δ + iform a₂ δ ^ 2 +
        iform b₁ δ ^ 2 + iform b₁ δ * iform b₂ δ + iform b₂ δ ^ 2 ∧
      (iform a₁ δ ^ 2 + iform a₁ δ * iform a₂ δ + iform a₂ δ ^ 2 +
        iform b₁ δ ^ 2 + iform b₁ δ * iform b₂ δ + iform b₂ δ ^ 2) ≠ 3 := by
  constructor
  · nlinarith [sq_nonneg (iform a₁ δ + iform a₂ δ), sq_nonneg (iform a₁ δ),
      sq_nonneg (iform a₂ δ), sq_nonneg (iform b₁ δ + iform b₂ δ),
      sq_nonneg (iform b₁ δ), sq_nonneg (iform b₂ δ)]
  · intro hK
    exact gram5_det_ne_zero ha₁ ha₂ hb₁ hb₂ hδout ha hb horth hn₁ hn₂ hn₃ hn₄ hn₅
      (by rw [gram5_det, hK]; norm_num)

private theorem cartan_det_eq_of_rank_five
    {t : TauCeti.DynkinType} (ht : t.Valid) (hsl : t.IsSimplyLaced) (hr : t.rank = 5)
    {m K : ℤ} (hK0 : 0 ≤ K) (hK3 : K ≠ 3)
    (h : 18 - 6 * K = m ^ 2 * t.cartanMatrix.det) : t = .A 5 := by
  rcases det_cartanMatrix_of_isSimplyLaced ht hsl with
      ⟨hA, -⟩ | ⟨hD, -, hdD⟩ | ⟨hE6, -⟩ | ⟨hE7, -⟩ | ⟨hE8, -⟩
  · rw [hA, hr]
  · rw [hdD] at h
    exact (no_int_sq_four h.symm hK0 hK3).elim
  · rw [hE6, TauCeti.DynkinType.rank_E6] at hr
    omega
  · rw [hE7, TauCeti.DynkinType.rank_E7] at hr
    omega
  · rw [hE8, TauCeti.DynkinType.rank_E8] at hr
    omega

private theorem ncard_eq_thirty_of_rank_five
    {Ψ A B : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h5 : compRank Ψ = 5)
    (hA : A ⊆ Ψ) (hB : B ⊆ Ψ)
    {a₁ a₂ b₁ b₂ δ : Fin Tag.E6.rank → ℤ}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hδ : δ ∈ Ψ)
    (hδout : (fun i => (δ i : ℚ)) ∉
      Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) '' (A ∪ B)))
    (ha : iform a₁ a₂ = -1) (hb : iform b₁ b₂ = -1)
    (horth : ∀ x ∈ ({a₁, a₂} : Finset (Fin Tag.E6.rank → ℤ)),
      ∀ y ∈ ({b₁, b₂} : Finset (Fin Tag.E6.rank → ℤ)), iform x y = 0)
    (hn₁ : iform a₁ a₁ = 2) (hn₂ : iform a₂ a₂ = 2) (hn₃ : iform b₁ b₁ = 2)
    (hn₄ : iform b₂ b₂ = 2) (hn₅ : iform δ δ = 2) :
    Ψ.ncard = 30 := by
  classical
  have hcard : (simpleRoots Ψ).card = 5 :=
    (CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card (τ := Tag.E6) hΨ).symm.trans h5
  let e' : simpleRoots Ψ ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by simpa [Fintype.card_coe] using hcard)
  let D : Fin 5 → Fin Tag.E6.rank → ℤ := ![a₁, a₂, b₁, b₂, δ]
  have hD : ∀ i, D i ∈ Ψ := by
    intro i
    fin_cases i
    · simpa [D] using hA ha₁
    · simpa [D] using hA ha₂
    · simpa [D] using hB hb₁
    · simpa [D] using hB hb₂
    · simpa [D] using hδ
  obtain ⟨t, m, ht, hsl, hcardt, hN, hdet⟩ :=
    exists_det_gram_eq_sq_mul_cartan hΨ ⟨a₁, hA ha₁⟩ e' D hD
  have hrank : t.rank = 5 := by omega
  have hgram : (Matrix.of fun i j : Fin 5 => iform (D i) (D j)) =
      gram5 (iform a₁ δ) (iform a₂ δ) (iform b₁ δ) (iform b₂ δ) := by
    simpa [D] using gram_five_eq ha hb horth hn₁ hn₂ hn₃ hn₄ hn₅
  have hgram5det : (gram5 (iform a₁ δ) (iform a₂ δ) (iform b₁ δ) (iform b₂ δ)).det =
      18 - 6 * (iform a₁ δ ^ 2 + iform a₁ δ * iform a₂ δ + iform a₂ δ ^ 2 +
        iform b₁ δ ^ 2 + iform b₁ δ * iform b₂ δ + iform b₂ δ ^ 2) :=
    gram5_det _ _ _ _
  have hdet5 : (Matrix.of fun i j : Fin 5 => iform (D i) (D j)).det =
      18 - 6 * (iform a₁ δ ^ 2 + iform a₁ δ * iform a₂ δ + iform a₂ δ ^ 2 +
        iform b₁ δ ^ 2 + iform b₁ δ * iform b₂ δ + iform b₂ δ ^ 2) := by
    rw [hgram, hgram5det]
  obtain ⟨hK0, hK3⟩ := gram5_K_bounds (Or.inl ha₁) (Or.inl ha₂) (Or.inr hb₁)
    (Or.inr hb₂) hδout ha hb horth hn₁ hn₂ hn₃ hn₄ hn₅
  have hK : 18 - 6 * (iform a₁ δ ^ 2 + iform a₁ δ * iform a₂ δ + iform a₂ δ ^ 2 +
      iform b₁ δ ^ 2 + iform b₁ δ * iform b₂ δ + iform b₂ δ ^ 2) =
      m ^ 2 * t.cartanMatrix.det := by
    rw [← hdet5]
    exact hdet
  have htA5 : t = .A 5 :=
    cartan_det_eq_of_rank_five ht hsl hrank hK0 hK3 hK
  rw [htA5, TauCeti.DynkinType.numRoots_A] at hN
  norm_num at hN
  exact hN

theorem twE6_typeA5_of_two_A2
    {M N : Type*} [CommGroup M] [CommGroup N]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {χ' : Multiplicative (Fin Tag.E6.rank → ℤ) →* N}
    {i₁ i₂ : KernelComponent χ} (hne : i₁ ≠ i₂)
    (h₁ : compRank (componentRoots χ i₁) = 2) (h₂ : compRank (componentRoots χ i₂) = 2)
    {i' : KernelComponent χ'} (hs₁ : componentRoots χ i₁ ⊆ componentRoots χ' i')
    (hs₂ : componentRoots χ i₂ ⊆ componentRoots χ' i')
    (hproper : componentRoots χ' i' ≠ {α | IsRoot Tag.E6 α}) :
    compRank (componentRoots χ' i') = 5 ∧ (componentRoots χ' i').ncard = 30 := by
  classical
  have hA : IsRootComponent (componentRoots χ i₁) := isRootComponent_componentRoots i₁
  have hB : IsRootComponent (componentRoots χ i₂) := isRootComponent_componentRoots i₂
  have hC : IsRootComponent (componentRoots χ' i') := isRootComponent_componentRoots i'
  obtain ⟨a₁, ha₁, a₂, ha₂, hn₁, hn₂, ha⟩ :=
    exists_A2_of_compRank_eq_two (τ := Tag.E6) (Or.inr (Or.inl rfl)) hA h₁
  obtain ⟨b₁, hb₁, b₂, hb₂, hn₃, hn₄, hb⟩ :=
    exists_A2_of_compRank_eq_two (τ := Tag.E6) (Or.inr (Or.inl rfl)) hB h₂
  have horth : ∀ x ∈ ({a₁, a₂} : Finset (Fin Tag.E6.rank → ℤ)),
      ∀ y ∈ ({b₁, b₂} : Finset (Fin Tag.E6.rank → ℤ)), iform x y = 0 := by
    intro x hx y hy
    have hxA : x ∈ componentRoots χ i₁ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha₁
      · exact ha₂
    have hyB : y ∈ componentRoots χ i₂ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hb₁
      · exact hb₂
    exact iform_eq_zero_of_mem_componentRoots hne hxA hyB
  have horthAB : ∀ x ∈ componentRoots χ i₁, ∀ y ∈ componentRoots χ i₂, iform x y = 0 :=
    fun x hx y hy => iform_eq_zero_of_mem_componentRoots hne hx hy
  have hrankAB : compRank (componentRoots χ i₁ ∪ componentRoots χ i₂) = 4 :=
    compRank_union_two_eq_four hne h₁ h₂
  have hsubC : componentRoots χ i₁ ∪ componentRoots χ i₂ ⊆ componentRoots χ' i' :=
    Set.union_subset hs₁ hs₂
  have h4C : 4 ≤ compRank (componentRoots χ' i') := by
    rw [← hrankAB]
    exact compRank_mono hsubC
  have h6C : compRank (componentRoots χ' i') ≤ 6 := by
    simpa [Tag.rank] using
      CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_le (τ := Tag.E6)
        (componentRoots χ' i')
  have hcases : compRank (componentRoots χ' i') = 4 ∨ compRank (componentRoots χ' i') = 5 ∨
      compRank (componentRoots χ' i') = 6 := by omega
  rcases hcases with h4 | h5 | h6
  · exact (false_of_rank_four hC h4 (hsubC (Or.inl ha₁)) (hsubC (Or.inl ha₂))
      (hsubC (Or.inr hb₁)) (hsubC (Or.inr hb₂))
      (det_gram_four ha hb horth hn₁ hn₂ hn₃ hn₄)).elim
  · obtain ⟨δ, hδC, hδout⟩ := exists_mem_not_mem_span_of_compRank_lt (τ := Tag.E6)
      (Ψ := componentRoots χ' i') (Ψ' := componentRoots χ i₁ ∪ componentRoots χ i₂)
      (by rw [hrankAB, h5]; norm_num)
    exact ⟨h5, ncard_eq_thirty_of_rank_five hC h5 hs₁ hs₂ ha₁ ha₂ hb₁ hb₂ hδC hδout ha hb
      horth hn₁ hn₂ hn₃ hn₄ (iform_self_E6 (hC.isRoot δ hδC))⟩
  · exact absurd (eq_setOf_isRoot_of_compRank_eq_six hC h6) hproper

private theorem rootReflection_mem_componentWeylGroup_of_mem
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ Ψ) : rootReflection γ ∈ componentWeylGroup Ψ := by
  rcases mem_posRoots_or_mem_negRoots hΨ hγ with h | h
  · obtain ⟨w, hw, β, hβ, e⟩ := exists_smul_simpleRoot_of_pos hΨ h
    rw [e, rootReflection_smul_root w (simpleRoots_isRoot hβ)]
    exact mul_mem (mul_mem hw (rootReflection_mem_componentWeylGroup hβ)) (inv_mem hw)
  · obtain ⟨w, hw, β, hβ, e⟩ := exists_smul_simpleRoot_of_pos hΨ h
    have hγ' : γ = w • (-β) := by rw [smul_neg, ← e, neg_neg]
    rw [hγ', rootReflection_smul_root w (IsRoot.neg (simpleRoots_isRoot hβ)),
      rootReflection_neg (simpleRoots_isRoot hβ)]
    exact mul_mem (mul_mem hw (rootReflection_mem_componentWeylGroup hβ)) (inv_mem hw)

private theorem closure_rootReflection_le_componentWeylGroup
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} ≤
      componentWeylGroup Ψ :=
  (Subgroup.closure_le _).2 <| by
    rintro s ⟨γ, hγ, rfl⟩
    exact rootReflection_mem_componentWeylGroup_of_mem hΨ hγ

theorem twE6_not_twistInner_of_swap
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} (i : KernelComponent χ)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = permLattice (TwistTag.perm .E6) γ)
    {Ψ₁ Ψ₂ : Set (Fin Tag.E6.rank → ℤ)} (h₁ : Ψ₁ ⊆ componentRoots χ i)
    (h₂ : Ψ₂ ⊆ componentRoots χ i) (hne : Ψ₁.Nonempty) (hdisj : Disjoint Ψ₁ Ψ₂)
    (hswap : (fun u => ρ u) '' Ψ₁ = Ψ₂)
    (hstab : (fun u => ρ u) '' componentRoots χ i = componentRoots χ i) :
    ¬ twistInner (componentRoots χ i) (fun u => ρ u) := by
  classical
  rintro ⟨w, hw, hs⟩
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hwW : w ∈ componentWeylGroup (componentRoots χ i) :=
    closure_rootReflection_le_componentWeylGroup hΨ hw
  have hw1 : w = 1 := by
    by_contra hwne
    obtain ⟨β, hβ, hβneg⟩ := exists_smul_mem_negRoots hΨ hwW hwne
    have hβΨ : β ∈ componentRoots χ i := simpleRoots_subset hβ
    have hmem : (fun u => ρ u) β ∈ componentRoots χ i := by
      rw [← hstab]
      exact ⟨β, hβΨ, rfl⟩
    have hht : height ((fun u => ρ u) β) = height β := by
      show height (ρ β) = height β
      rw [hρ β (simpleRoots_isRoot hβ)]
      exact CFSG.LieType.Chevalley.ToralSign.height_permLattice (τ := Tag.E6) _ β
    have hpos : (fun u => ρ u) β ∈ posRoots (componentRoots χ i) := by
      refine ⟨hmem, ?_⟩
      rw [hht]
      exact simpleRoots_height_pos hβ
    rw [hs β hβΨ] at hpos
    exact not_mem_negRoots_of_mem_posRoots hpos hβneg
  have hsub : Ψ₁ ⊆ Ψ₂ := by
    intro x hx
    have hfix : (fun u => ρ u) x = x := by
      rw [hs x (h₁ hx), hw1, one_smul]
    rw [← hswap]
    exact ⟨x, hx, hfix⟩
  obtain ⟨x, hx⟩ := hne
  exact Set.disjoint_left.1 hdisj hx (hsub hx)

theorem twE6U7C1_holds :
    TwE6U7C1 := by
  intro M N _ _ χ χ' i₁ i₂ hne h₁ h₂ i' hs₁ hs₂ hproper
  exact twE6_typeA5_of_two_A2 hne h₁ h₂ hs₁ hs₂ hproper

theorem twE6U7C2_holds :
    TwE6U7C2 := by
  intro M _ χ i ρ hρ Ψ₁ Ψ₂ h₁ h₂ hne hdisj hswap hstab
  exact twE6_not_twistInner_of_swap i hρ h₁ h₂ hne hdisj hswap hstab

end CFSG.StandardType.LieKnownR2.ExcPos
