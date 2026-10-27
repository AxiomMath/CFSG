module

public import CFSG.RankThree.GF2n.Smith81.S81HO12Defs
public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthGraph

open Module QuadraticMap CFSG.RankThree.PartOne.StrongP

variable {n : ℕ} {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] noncomputable def ptorus (b : Basis (PIdx n) K V) : (Fin n → Kˣ) →* (V ≃ₗ[K] V) where
  toFun c := b.equiv (b.unitsSMul (pchar c)) (Equiv.refl _)
  map_one' := by
    refine b.ext' fun p => ?_
    show b.equiv (b.unitsSMul (pchar (1 : Fin n → Kˣ))) (Equiv.refl _) (b p) =
      (1 : V ≃ₗ[K] V) (b p)
    rw [Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply, pchar_one, one_smul]
    rfl
  map_mul' c d := by
    have h1 : ∀ (e : Fin n → Kˣ) (p : PIdx n),
        b.equiv (b.unitsSMul (pchar e)) (Equiv.refl _) (b p) = ((pchar e p : Kˣ) : K) • b p := by
      intro e p
      rw [Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply, Units.smul_def]
    refine b.ext' fun p => ?_
    show b.equiv (b.unitsSMul (pchar (c * d))) (Equiv.refl _) (b p) =
      (b.equiv (b.unitsSMul (pchar c)) (Equiv.refl _) *
        b.equiv (b.unitsSMul (pchar d)) (Equiv.refl _)) (b p)
    rw [LinearEquiv.mul_apply, h1 (c * d), h1 d, map_smul, h1 c, smul_smul, pchar_mul,
      Units.val_mul, mul_comm]

@[simp] theorem ptorus_apply_basis (b : Basis (PIdx n) K V) (c : Fin n → Kˣ) (p : PIdx n) :
    ptorus b c (b p) = ((pchar c p : Kˣ) : K) • b p := by
  simp [ptorus, Basis.equiv_apply, Basis.unitsSMul_apply, Units.smul_def]

theorem basisMat_ptorus (b : Basis (PIdx n) K V) (c : Fin n → Kˣ) :
    ((basisMat b (ptorus b c) : GL (PIdx n) K) : Matrix (PIdx n) (PIdx n) K) =
      Matrix.diagonal fun p => ((pchar c p : Kˣ) : K) := by
  ext p q
  rw [basisMat_apply, ptorus_apply_basis, map_smul, Basis.repr_self, Finsupp.smul_apply,
    Matrix.diagonal_apply, Finsupp.single_apply]
  by_cases h : p = q
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem ptorus_mem_orthogonalGroup {Q : QuadraticForm K V} {b : Basis (PIdx n) K V}
    (hb : IsPairBasis Q b) (c : Fin n → Kˣ) :
    ptorus b c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine mem_orthogonalGroup_of_basis b (ptorus b c) (fun p => ?_) (fun p q => ?_)
  · rw [ptorus_apply_basis, QuadraticMap.map_smul]
    rcases p with i | j | i
    · simp [hb.sing_v]
    · simp
    · simp [hb.sing_w]
  · rw [ptorus_apply_basis, ptorus_apply_basis, polar_smul_left, polar_smul_right, hb.polar_eq]
    by_cases h : q = pdual p
    · subst h
      simp [pchar_pdual]
    · simp [h]

private theorem exists_unit_mul_self_eq [Finite K] [CharP K 2] (a : Kˣ) :
    ∃ ν : Kˣ, ν * ν = a := by
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (a : K)
  have hu : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ a.isUnit)
  refine ⟨hu.unit, Units.ext ?_⟩
  rw [Units.val_mul, IsUnit.unit_spec]
  exact hs.symm

private noncomputable def swapV (b : Basis (PIdx n) K V) (i : Fin n) : V ≃ₗ[K] V :=
  b.equiv b (Equiv.swap (.inl i) (.inr (.inr i)))

private theorem swapV_apply (b : Basis (PIdx n) K V) (i : Fin n) (p : PIdx n) :
    swapV b i (b p) = b (Equiv.swap (.inl i) (.inr (.inr i)) p) := by
  simp [swapV, Basis.equiv_apply]

private theorem pdual_swap (i : Fin n) (p : PIdx n) :
    pdual (Equiv.swap (.inl i) (.inr (.inr i)) p) =
      Equiv.swap (.inl i) (.inr (.inr i)) (pdual p) := by
  rcases p with j | j | j
  · by_cases h : j = i
    · subst h
      simp [Equiv.swap_apply_def]
    · simp [Equiv.swap_apply_def, h]
  · simp [Equiv.swap_apply_def]
  · by_cases h : j = i
    · subst h
      simp [Equiv.swap_apply_def]
    · simp [Equiv.swap_apply_def, h]

private theorem swapV_mem {Q : QuadraticForm K V} {b : Basis (PIdx n) K V}
    (hb : IsPairBasis Q b) (i : Fin n) : swapV b i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine mem_orthogonalGroup_of_basis b (swapV b i) (fun p => ?_) (fun p q => ?_)
  · rw [swapV_apply]
    rcases p with j | j | j
    · by_cases h : j = i
      · subst h
        simp [Equiv.swap_apply_def, hb.sing_v, hb.sing_w]
      · simp [Equiv.swap_apply_def, h]
    · simp [Equiv.swap_apply_def]
    · by_cases h : j = i
      · subst h
        simp [Equiv.swap_apply_def, hb.sing_v, hb.sing_w]
      · simp [Equiv.swap_apply_def, h]
  · rw [swapV_apply, swapV_apply, hb.polar_eq, hb.polar_eq]
    simp only [pdual_swap, Equiv.apply_eq_iff_eq]

private theorem swapV_mul_ptorus (b : Basis (PIdx n) K V) (i : Fin n) (μ : Kˣ) :
    swapV b i * ptorus b (Pi.mulSingle i μ) = ptorus b (Pi.mulSingle i μ⁻¹) * swapV b i := by
  refine b.ext' fun p => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ptorus_apply_basis, map_smul, swapV_apply,
    ptorus_apply_basis]
  congr 1
  rcases p with j | j | j
  · by_cases h : j = i
    · subst h
      simp [Equiv.swap_apply_def]
    · simp [Equiv.swap_apply_def, h]
  · simp [Equiv.swap_apply_def]
  · by_cases h : j = i
    · subst h
      simp [Equiv.swap_apply_def]
    · simp [Equiv.swap_apply_def, h]

private theorem ptorus_mulSingle_mem [Finite K] [CharP K 2] {Q : QuadraticForm K V}
    {b : Basis (PIdx n) K V} (hb : IsPairBasis Q b) (i : Fin n) (a : Kˣ) :
    ptorus b (Pi.mulSingle i a) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨ν, hν⟩ := exists_unit_mul_self_eq a
  have e1 : (ptorus b (Pi.mulSingle i ν⁻¹))⁻¹ = ptorus b (Pi.mulSingle i ν) := by
    rw [← map_inv (ptorus b), ← Pi.mulSingle_inv, inv_inv]
  have h1 : swapV b i * ptorus b (Pi.mulSingle i ν⁻¹) * (swapV b i)⁻¹ *
      (ptorus b (Pi.mulSingle i ν⁻¹))⁻¹ = ptorus b (Pi.mulSingle i a) := by
    rw [swapV_mul_ptorus, mul_inv_cancel_right, e1, inv_inv, ← map_mul (ptorus b),
      ← Pi.mulSingle_mul, hν]
  have h2 : swapV b i * ptorus b (Pi.mulSingle i ν⁻¹) * (swapV b i)⁻¹ *
      (ptorus b (Pi.mulSingle i ν⁻¹))⁻¹ ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    Subgroup.commutator_mem_commutator (swapV_mem hb i)
      (ptorus_mem_orthogonalGroup hb (Pi.mulSingle i ν⁻¹))
  rwa [h1] at h2

theorem ptorus_mem_commutator [Finite K] [CharP K 2] {Q : QuadraticForm K V}
    {b : Basis (PIdx n) K V} (hb : IsPairBasis Q b) (c : Fin n → Kˣ) :
    ptorus b c ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hmem : ∏ i, (Pi.mulSingle i (c i) : Fin n → Kˣ) ∈
      (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).comap (ptorus b) :=
    Subgroup.prod_mem _ fun i _ => ptorus_mulSingle_mem hb i (c i)
  rw [Finset.univ_prod_mulSingle] at hmem
  exact hmem

theorem pchar_root_surjective [Finite K] [CharP K 2] {p q : PIdx n}
    (hpq : prank p < prank q) (hne : ¬ (p = .inr (.inl 0) ∧ q = .inr (.inl 1))) :
    Function.Surjective fun c : Fin n → Kˣ => pchar c p * (pchar c q)⁻¹ := by
  intro a
  rcases p with i | j | i <;> rcases q with k | l | m
  · have hik : k ≠ i := by
      simp only [prank_inl] at hpq
      intro h
      subst h
      omega
    exact ⟨Pi.mulSingle i a, by simp [hik]⟩
  · exact ⟨Pi.mulSingle i a, by simp⟩
  · by_cases him : i = m
    · obtain ⟨ν, hν⟩ := exists_unit_mul_self_eq a
      refine ⟨Pi.mulSingle i ν, ?_⟩
      subst him
      simp [hν]
    · exact ⟨Pi.mulSingle i a, by simp [Ne.symm him]⟩
  · exfalso
    have := k.isLt
    simp only [prank_inr_inl, prank_inl] at hpq
    omega
  · exfalso
    apply hne
    simp only [prank_inr_inl] at hpq
    have key : ∀ j l : Fin 2, (j : ℕ) < l → j = 0 ∧ l = 1 := by decide
    obtain ⟨rfl, rfl⟩ := key j l (by omega)
    exact ⟨rfl, rfl⟩
  · exact ⟨Pi.mulSingle m a, by simp⟩
  · exfalso
    have := i.isLt
    have := k.isLt
    simp only [prank_inr_inr, prank_inl] at hpq
    omega
  · exfalso
    have := i.isLt
    have := l.isLt
    simp only [prank_inr_inr, prank_inr_inl] at hpq
    omega
  · have hmi : i ≠ m := by
      simp only [prank_inr_inr] at hpq
      have := i.isLt
      have := m.isLt
      intro h
      subst h
      omega
    exact ⟨Pi.mulSingle m a, by simp [hmi]⟩

private theorem exists_unit_ne_one [Finite K] (hK : 4 ≤ Nat.card K) : ∃ e : Kˣ, e ≠ 1 := by
  have h1 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have h2 : 1 < Nat.card Kˣ := by omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h2
  exact exists_ne 1

private theorem repr_apply_eq_zero [Finite K] [CharP K 2] {b : Basis (PIdx n) K V}
    {e : Kˣ} (he : e ≠ 1) {g : V ≃ₗ[K] V} (hgu : IsUnitri prank (basisMat b g))
    (hgt : ∀ c : Fin n → Kˣ, g * ptorus b c = ptorus b c * g) {p q : PIdx n} (hpq : p ≠ q)
    (hne : ¬ (p = .inr (.inl 0) ∧ q = .inr (.inl 1))) : b.repr (g (b q)) p = 0 := by
  rw [← basisMat_apply]
  by_cases hlt : prank p < prank q
  · obtain ⟨c, hc⟩ := pchar_root_surjective hlt hne e
    have hc' : pchar c p * (pchar c q)⁻¹ = e := hc
    have hcomm := congrArg
      (fun x : V ≃ₗ[K] V => ((basisMat b x : GL (PIdx n) K) : Matrix (PIdx n) (PIdx n) K) p q)
      (hgt c)
    simp only [map_mul, Units.val_mul, basisMat_ptorus, Matrix.mul_diagonal,
      Matrix.diagonal_mul] at hcomm
    have hne' : ((pchar c q : Kˣ) : K) - (pchar c p : Kˣ) ≠ 0 := by
      intro h
      apply he
      have h1 : pchar c p = pchar c q := (Units.ext (sub_eq_zero.mp h)).symm
      rw [← hc', h1, mul_inv_cancel]
    have h0 : ((basisMat b g : GL (PIdx n) K) : Matrix (PIdx n) (PIdx n) K) p q *
        (((pchar c q : Kˣ) : K) - (pchar c p : Kˣ)) = 0 := by
      linear_combination hcomm
    exact (mul_eq_zero.mp h0).resolve_right hne'
  · by_contra hM
    apply hlt
    apply hgu p q
    rw [Matrix.sub_apply, Matrix.one_apply_ne hpq, sub_zero]
    exact hM

theorem card_le_two_of_commute [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {Q : QuadraticForm K V} {b : Basis (PIdx n) K V} (hb : IsPairBasis Q b)
    (C : Subgroup (V ≃ₗ[K] V)) (hCO : C ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hCu : ∀ g ∈ C, IsUnitri prank (basisMat b g))
    (hCt : ∀ g ∈ C, ∀ c : Fin n → Kˣ, g * ptorus b c = ptorus b c * g) :
    Nat.card C ≤ 2 := by
  classical
  obtain ⟨e, he⟩ := exists_unit_ne_one hK
  have huu' : (.inr (.inl 0) : PIdx n) ≠ .inr (.inl 1) := by simp
  have hdu' : pdual (.inr (.inl 1) : PIdx n) = .inr (.inl 0) := rfl
  have hrepr : ∀ g ∈ C, ∀ p q : PIdx n, p ≠ q →
      ¬ (p = .inr (.inl 0) ∧ q = .inr (.inl 1)) → b.repr (g (b q)) p = 0 :=
    fun g hg p q hpq hne => repr_apply_eq_zero he (hCu g hg) (hCt g hg) hpq hne
  have hdiag : ∀ g ∈ C, ∀ p, b.repr (g (b p)) p = 1 := fun g hg p => by
    rw [← basisMat_apply]
    exact (hCu g hg).diag p
  have hfix : ∀ g ∈ C, ∀ q : PIdx n, q ≠ .inr (.inl 1) → g (b q) = b q := by
    intro g hg q hq
    refine b.ext_elem fun p => ?_
    by_cases hpq : p = q
    · subst hpq
      rw [hdiag g hg, Basis.repr_self, Finsupp.single_eq_same]
    · rw [hrepr g hg p q hpq (fun h => hq h.2), Basis.repr_self, Finsupp.single_eq_of_ne hpq]
  have hmove : ∀ g ∈ C, g (b (.inr (.inl 1))) =
      b (.inr (.inl 1)) + (b.repr (g (b (.inr (.inl 1)))) (.inr (.inl 0))) • b (.inr (.inl 0)) := by
    intro g hg
    refine b.ext_elem fun p => ?_
    rw [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self,
      Basis.repr_self]
    by_cases h1 : p = .inr (.inl 1)
    · subst h1
      rw [hdiag g hg, Finsupp.single_eq_same, Finsupp.single_eq_of_ne' huu', smul_zero, add_zero]
    · by_cases h0 : p = .inr (.inl 0)
      · subst h0
        rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne huu', zero_add, smul_eq_mul, mul_one]
      · rw [hrepr g hg p _ h1 (fun h => h0 h.1), Finsupp.single_eq_of_ne h1,
          Finsupp.single_eq_of_ne h0, smul_zero, add_zero]
  have hiso : ∀ g ∈ C, (b.repr (g (b (.inr (.inl 1)))) (.inr (.inl 0))) *
      ((b.repr (g (b (.inr (.inl 1)))) (.inr (.inl 0))) * Q (b (.inr (.inl 0))) + 1) = 0 := by
    intro g hg
    have hl := hmove g hg
    have h1 : Q (g (b (.inr (.inl 1)))) = Q (b (.inr (.inl 1))) :=
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hCO hg) _
    generalize b.repr (g (b (.inr (.inl 1)))) (.inr (.inl 0)) = l at hl ⊢
    have h2 : polar Q (b (.inr (.inl 1))) (b (.inr (.inl 0))) = 1 := by
      rw [hb.polar_eq, hdu', if_pos rfl]
    rw [hl, QuadraticMap.map_add (Q : V → K), QuadraticMap.map_smul, polar_smul_right, h2] at h1
    simp only [smul_eq_mul, mul_one] at h1
    linear_combination h1
  have hmem : ∀ g : C, b.repr (g.1 (b (.inr (.inl 1)))) (.inr (.inl 0)) ∈
      ({0, -(Q (b (.inr (.inl 0))))⁻¹} : Finset K) := by
    intro g
    rcases mul_eq_zero.mp (hiso g.1 g.2) with h | h
    · simp [h]
    · have hq : Q (b (.inr (.inl 0))) ≠ 0 := by
        intro hq
        rw [hq, mul_zero, zero_add] at h
        exact one_ne_zero h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      field_simp
      linear_combination h
  have hinj : Function.Injective
      (fun g : C => b.repr (g.1 (b (.inr (.inl 1)))) (.inr (.inl 0))) := by
    intro g g' h
    have h' : b.repr (g.1 (b (.inr (.inl 1)))) (.inr (.inl 0)) =
        b.repr (g'.1 (b (.inr (.inl 1)))) (.inr (.inl 0)) := h
    refine Subtype.ext (b.ext' fun q => ?_)
    by_cases hq : q = .inr (.inl 1)
    · subst hq
      rw [hmove g.1 g.2, hmove g'.1 g'.2, h']
    · rw [hfix g.1 g.2 q hq, hfix g'.1 g'.2 q hq]
  let f : C → ({0, -(Q (b (.inr (.inl 0))))⁻¹} : Finset K) := fun g => ⟨_, hmem g⟩
  have hf : Function.Injective f := fun g g' h => hinj (congrArg Subtype.val h)
  calc Nat.card C ≤ Nat.card ({0, -(Q (b (.inr (.inl 0))))⁻¹} : Finset K) :=
        Nat.card_le_card_of_injective f hf
    _ ≤ 2 := by
        rw [Nat.card_eq_finsetCard]
        exact Finset.card_le_two

end CFSG.RankThree.GF2n.Smith81.OrthGraph
