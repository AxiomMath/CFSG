module

public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.RankThree.PartOne.KC.PlaneLifting
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane
open CFSG.RankThree.RegularUnipotent CFSG.ComponentClassification

variable {n : ℕ} {k : Type*} [Field k]

theorem exists_diag_entries_eq {p : ℕ} (hp : p.Prime) [Finite k]
    (E₀ : Subgroup (SpecialLinearGroup (Fin n) k)) [IsElementaryAbelian p E₀]
    (hE₀ : Nat.card E₀ = p ^ 2)
    (hdiag : ∀ x ∈ E₀, ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) k) i j = 0) (i j : Fin n) :
    ∃ a ∈ E₀, a ≠ 1 ∧ (a : Matrix (Fin n) (Fin n) k) i i = (a : Matrix (Fin n) (Fin n) k) j j := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hentry : ∀ (A B : Matrix (Fin n) (Fin n) k), (∀ i j, i ≠ j → A i j = 0) →
      (∀ i j, i ≠ j → B i j = 0) → ∀ l, (A * B) l l = A l l * B l l := by
    intro A B hA hB l
    rw [Matrix.mul_apply, Finset.sum_eq_single l]
    · intro m _ hm
      rw [hA l m (Ne.symm hm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ l) h
  have hmul : ∀ (l : Fin n) (x y : E₀),
      (((x * y : E₀) : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) l l =
        ((x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) l l *
          ((y : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) l l := by
    intro l x y
    have hmat : (((x * y : E₀) : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        ((x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *
          ((y : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by simp
    rw [hmat]
    exact hentry _ _ (hdiag x x.2) (hdiag y y.2) l
  let ψ : Fin n → E₀ →* k := fun l =>
    { toFun := fun x => (x : Matrix (Fin n) (Fin n) k) l l
      map_one' := by simp
      map_mul' := hmul l }
  let χ : E₀ →* kˣ := (ψ i).toHomUnits * ((ψ j).toHomUnits)⁻¹
  have hχp : ∀ x : E₀, χ x ^ p = 1 := fun x => by
    rw [← map_pow]
    have h1 : ((x : SpecialLinearGroup (Fin n) k)) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E₀)
        (x : SpecialLinearGroup (Fin n) k) x.2
    have : x ^ p = 1 := Subtype.ext h1
    rw [this, map_one]
  have hrange : χ.range ≤ rootsOfUnity p k := fun u ⟨x, hx⟩ => by
    rw [mem_rootsOfUnity, ← hx]; exact hχp x
  have hrcard : Nat.card χ.range ≤ p :=
    (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity k p)
  have hker : 1 < Nat.card χ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup χ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv, hE₀] at h1
    by_contra hle
    have hk1 : Nat.card χ.ker ≤ 1 := by omega
    have : p ^ 2 ≤ p * 1 := by
      rw [h1, mul_comm]
      exact Nat.mul_le_mul hk1 hrcard |>.trans (by simp)
    have := hp.one_lt
    nlinarith
  obtain ⟨⟨a, hχ⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot (H := χ.ker)).mp hker)
  refine ⟨(a : SpecialLinearGroup (Fin n) k), a.2, fun h => ha1 ?_, ?_⟩
  · apply Subtype.ext
    exact Subtype.ext h
  · have h1 : χ a = 1 := hχ
    have h2 : (ψ i).toHomUnits a = (ψ j).toHomUnits a := by
      have : (ψ i).toHomUnits a * ((ψ j).toHomUnits a)⁻¹ = 1 := h1
      exact mul_inv_eq_one.mp this
    have h3 := congrArg (fun u : kˣ => (u : k)) h2
    simpa [ψ] using h3

@[expose] noncomputable def innerOfSL (n : ℕ) (k : Type*) [Field k] :
    SpecialLinearGroup (Fin n) k →* MulAut (projectiveSL n k) :=
  (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k)

theorem coordBlock_transvection {J : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∈ J)
    (hj : j ∈ J) (c : k) : SpecialLinearGroup.transvection hij c ∈ coordBlockSL k J := by
  rw [mem_coordBlockSL_iff]
  intro a b hab
  have hne : ¬ (i = a ∧ j = b) := fun ⟨h1, h2⟩ => by
    rcases hab with h | h
    · exact h (h1 ▸ hi)
    · exact h (h2 ▸ hj)
  have h1 : ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) k) :
      Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b + Matrix.single i j c a b := by
    simp [SpecialLinearGroup.transvection_coe]
  have h2 : Matrix.single i j c a b = 0 := Matrix.single_apply_of_ne i j c a b hne
  by_cases h : a = b
  · subst h
    simp [h1, h2]
  · simp [h1, h2, h, Matrix.one_apply_ne h]

open CFSG.LinearGroups in
theorem autThetaT_diagonal_eq_bot {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ p) (hf : 1 ≤ f) (hn3 : 3 ≤ n) (hnp : n < p) [Finite k] [DecidableEq k]
    [CharP k ℓ] (hk : Nat.card k = ℓ ^ f) (hpq : p ∣ Nat.card k - 1)
    (E₀ : Subgroup (SpecialLinearGroup (Fin n) k)) [IsElementaryAbelian p E₀]
    (hE₀ : Nat.card E₀ = p ^ 2)
    (hdiag : ∀ x ∈ E₀, ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) k) i j = 0)
    (B : Subgroup (MulAut (projectiveSL n k)))
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B) :
    autThetaT p B (E₀.map (innerOfSL n k)) = ⊥ := by
  classical
  have hn0 : 0 < n := by omega
  have hinj := conj_injective_projectiveSL (k := k) hn3
  rw [eq_bot_iff]
  intro s hs
  have hs_tr : ∀ (i j : Fin n) (hij : i ≠ j) (c : k),
      s * innerOfSL n k (SpecialLinearGroup.transvection hij c) =
        innerOfSL n k (SpecialLinearGroup.transvection hij c) * s := by
    intro i j hij c
    obtain ⟨a, haE, ha1, haij⟩ := exists_diag_entries_eq hp E₀ hE₀ hdiag i j
    have hpow : a ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E₀) a haE
    have hΦa : innerOfSL n k a ≠ 1 := by
      intro h
      have h1 : proj n k a = 1 := hinj (by simpa [innerOfSL] using h)
      exact ha1 (eq_one_of_mem_scalars_of_pow hp hn0 hnp (proj_eq_one_iff.mp h1) hpow)
    have hsa : s ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k a)}) := by
      have := hs
      simp only [autThetaT, Subgroup.mem_iInf] at this
      exact this (innerOfSL n k a) (Subgroup.mem_map_of_mem _ haE) hΦa
    exact (linear_split_inner_plane_centralizer_cores_centralize_blocks hp hp3 hℓ hℓp hf hn3
      hnp hk hpq E₀ hE₀ hdiag B hB haE ha1).2 ((a : Matrix (Fin n) (Fin n) k) i i) s hsa _
      (coordBlock_transvection hij (by simp) (by simp [haij]) c)
  have hs_all : ∀ g : SpecialLinearGroup (Fin n) k,
      s * innerOfSL n k g = innerOfSL n k g * s := by
    have hle : Subgroup.closure (elementarySet n k) ≤
        (Subgroup.centralizer ({s} : Set (MulAut (projectiveSL n k)))).comap (innerOfSL n k) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hs_tr i j hij c).symm
    intro g
    have hg : g ∈ Subgroup.closure (elementarySet n k) := by
      rw [special_linear_elementary_generation]; exact Subgroup.mem_top g
    have := hle hg
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  have hs1 : s = 1 := by
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective n k x
    have h1 : s * MulAut.conj (proj n k g) = MulAut.conj (proj n k g) * s := hs_all g
    have h2 : MulAut.conj (s (proj n k g)) = MulAut.conj (proj n k g) := by
      rw [CFSG.RankThree.GroupTheory.SteinbergBY.mulAut_conj_apply_eq, h1, mul_assoc,
        mul_inv_cancel, mul_one]
    have := hinj h2
    simpa using this
  exact hs1 ▸ Subgroup.one_mem _

theorem exists_primitiveRoot_of_dvd_card_sub_one {p : ℕ} (hp : p.Prime) [Finite k]
    (hpq : p ∣ Nat.card k - 1) : ∃ ζ : k, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card kˣ := by
    have := Nat.card_units (α := k)
    simpa [this] using hpq
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨(u : k), IsPrimitiveRoot.coe_units_iff.mpr (hu ▸ IsPrimitiveRoot.orderOf u)⟩

theorem not_dvd_card_ker_innerOfSL {p : ℕ} (hp : p.Prime) (hn3 : 3 ≤ n) (hnp : n < p)
    [Finite k] : ¬ p ∣ Nat.card (innerOfSL n k).ker := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hinj := conj_injective_projectiveSL (k := k) hn3
  have hz1 : (z : SpecialLinearGroup (Fin n) k) ∈ (innerOfSL n k).ker := z.2
  have hpz : (z : SpecialLinearGroup (Fin n) k) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg Subtype.val this
  have hsc : (z : SpecialLinearGroup (Fin n) k) ∈ scalars n k := by
    have h1 : MulAut.conj (proj n k (z : SpecialLinearGroup (Fin n) k)) = 1 := hz1
    exact proj_eq_one_iff.mp (hinj (by simpa using h1))
  have : (z : SpecialLinearGroup (Fin n) k) = 1 :=
    eq_one_of_mem_scalars_of_pow hp (by omega) hnp hsc hpz
  have hz' : z = 1 := Subtype.ext this
  rw [hz', orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem innerOfSL_slConjugation (A : GL (Fin n) k) (g : SpecialLinearGroup (Fin n) k) :
    innerOfSL n k (CatalogueBHigherLinearAction.slConjugation n k A g) =
      conjAut n k A * innerOfSL n k g * (conjAut n k A)⁻¹ := by
  have h := conjAut_proj A g
  show MulAut.conj (proj n k (CatalogueBHigherLinearAction.slConjugation n k A g)) = _
  rw [← h, CFSG.RankThree.GroupTheory.SteinbergBY.mulAut_conj_apply_eq]
  rfl

theorem linear_split_inner_plane_local_core_products_trivial {p ℓ f : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hf : 1 ≤ f) (hn3 : 3 ≤ n) (hnp : n < p)
    [Finite k] [DecidableEq k] [CharP k ℓ] (hk : Nat.card k = ℓ ^ f)
    (hpq : p ∣ Nat.card k - 1) (B : Subgroup (MulAut (projectiveSL n k)))
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B)
    (E : Subgroup (MulAut (projectiveSL n k)))
    (hE : E ≤ (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range)
    [IsElementaryAbelian p E] (hEcard : Nat.card E = p ^ 2) {t : MulAut (projectiveSL n k)}
    (htE : t ∈ E) (ht1 : t ≠ 1) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}) ≤
        Subgroup.centralizer (E : Set (MulAut (projectiveSL n k))) ∧
      autThetaT p B E = ⊥ ∧ autPlaneProduct p B E t = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have hinj := conj_injective_projectiveSL (k := k) hn3
  have hE' : E ≤ (innerOfSL n k).range := fun x hx => by
    obtain ⟨y, rfl⟩ := hE hx
    obtain ⟨g, rfl⟩ := proj_surjective n k y
    exact ⟨g, rfl⟩
  have hfin : Finite (SpecialLinearGroup (Fin n) k) := inferInstance
  obtain ⟨E₀, hE₀el, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian (innerOfSL n k) hp
    (not_dvd_card_ker_innerOfSL hp hn3 hnp) E hE' hEcard
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_card_sub_one hp hpq
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy => by
    have := (IsMulCommutative.is_comm (M := E₀)).comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hpow : ∀ x ∈ E₀, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E₀) x hx
  obtain ⟨A, hA⟩ := exists_conj_diagonal_of_commuting_pow_eq_one hζ E₀ hcomm hpow
  set ψ : MulAut (projectiveSL n k) := conjAut n k A with hψ
  set φ : MulAut (MulAut (projectiveSL n k)) := MulAut.conj ψ with hφ
  set σ : SpecialLinearGroup (Fin n) k →* SpecialLinearGroup (Fin n) k :=
    (CatalogueBHigherLinearAction.slConjugation n k A).toMonoidHom with hσ
  set E₀' : Subgroup (SpecialLinearGroup (Fin n) k) := E₀.map σ with hE₀'
  have hφapp : ∀ x, φ.toMonoidHom x = ψ * x * ψ⁻¹ := fun x => rfl
  have hEmap : E.map φ.toMonoidHom = E₀'.map (innerOfSL n k) := by
    rw [← hE₀map, Subgroup.map_map, hE₀', Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, hφapp]
    exact (innerOfSL_slConjugation A g).symm
  have hσinj : Function.Injective σ := (CatalogueBHigherLinearAction.slConjugation n k A).injective
  have hE₀'card : Nat.card E₀' = p ^ 2 := by
    rw [hE₀', Subgroup.card_map_of_injective hσinj, hE₀card]
  have hE₀'el : IsElementaryAbelian p E₀' := by
    have := hE₀el
    exact IsElementaryAbelian.map σ
  have hdiag' : ∀ x ∈ E₀', ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) k) i j = 0 := by
    rintro _ ⟨x, hx, rfl⟩ i j hij
    have h1 := hA x hx i j hij
    have h2 : ((σ x : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (A : Matrix (Fin n) (Fin n) k) * (x : Matrix (Fin n) (Fin n) k) *
          ((A⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
      CatalogueBHigherLinearAction.slConjugation_matrix n k A x
    rw [h2]
    exact h1
  set B' : Subgroup (MulAut (projectiveSL n k)) := B.map φ.toMonoidHom with hB'def
  have hB' : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B' := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.conj (ψ⁻¹ x), hB ⟨ψ⁻¹ x, rfl⟩, ?_⟩
    rw [hφapp, ← CFSG.RankThree.GroupTheory.SteinbergBY.mulAut_conj_apply_eq]
    simp
  have hI : autThetaT p B E = ⊥ := by
    have h1 := autThetaT_diagonal_eq_bot hp hp3 hℓ hℓp hf hn3 hnp hk hpq E₀' hE₀'card hdiag' B'
      hB'
    rw [← hEmap, ← map_autThetaT_mulEquiv hp φ B E] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  have hc : inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}) ≤
      Subgroup.centralizer (E : Set (MulAut (projectiveSL n k))) := by
    intro s hs
    have h1 : φ s ∈ inSubgroup (aschbacherSolvableCore p) (B' ⊓ Subgroup.centralizer {φ t}) := by
      rw [← map_inSubgroup_theta_centralizer_mulEquiv hp φ B t]
      exact Subgroup.mem_map_of_mem _ hs
    have ht' : φ t ∈ E₀'.map (innerOfSL n k) := by
      rw [← hEmap]; exact Subgroup.mem_map_of_mem _ htE
    obtain ⟨a', ha'E, ha'⟩ := Subgroup.mem_map.mp ht'
    have ha'1 : a' ≠ 1 := fun h => ht1 (φ.injective (by rw [← ha', h, map_one, map_one]))
    have h2 := (linear_split_inner_plane_centralizer_cores_centralize_blocks hp hp3 hℓ hℓp hf hn3
      hnp hk hpq E₀' hE₀'card hdiag' B' hB' ha'E ha'1).1 (φ s) (by
        have : φ t = MulAut.conj (proj n k a') := ha'.symm
        rw [this] at h1
        exact h1)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : φ e ∈ E₀'.map (innerOfSL n k) := by
      rw [← hEmap]; exact Subgroup.mem_map_of_mem _ he
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp he'
    have h3 := h2 x hx
    apply φ.injective
    rw [map_mul, map_mul]
    have : φ e = MulAut.conj (proj n k x) := hxe.symm
    rw [this]
    exact h3.symm
  refine ⟨hc, hI, ?_⟩
  rw [autPlaneProduct, hI, sup_bot_eq]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc

end CFSG.RankThree.PartOne
