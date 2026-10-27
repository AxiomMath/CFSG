module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUStd
public import CFSG.ClassicalGroups.Symplectic.Model
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SumRootGeneration

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank GGOppRad TauCeti.GLSymplecticFin
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def finEquiv : TauCeti.GLSymplecticFin n K ≃* StatedSp n K :=
  (mulEquivGLSymplectic n K).trans (MulEquiv.subgroupCongr
    (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n) (K := K)).symm)

theorem coe_finEquiv (x : TauCeti.GLSymplecticFin n K) :
    ((finEquiv x : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      Equiv.reindexGL finSumFinEquiv.symm K (x : GL (Fin (n + n)) K) := by
  simp [finEquiv]

@[expose] def IsUpper {ι : Type*} [Fintype ι] [DecidableEq ι] (ℓ : ι → ℕ) (M : GL ι K) : Prop :=
  ∀ c a, ¬ ℓ c < ℓ a → (M : Matrix ι ι K) c a = (1 : Matrix ι ι K) c a

theorem IsUpper.mul [Finite K] {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ}
    {M N : GL ι K} (hM : IsUpper ℓ M) (hN : IsUpper ℓ N) : IsUpper ℓ (M * N) := by
  have e : ∀ X : GL ι K, IsUpper ℓ X →
      (⟨X, Subgroup.mem_top X⟩ : (⊤ : Subgroup (GL ι K))) ∈
        flagKernel (natRep (⊤ : Subgroup (GL ι K))) (stdFlag ℓ) :=
    fun X hX => mem_flagKernel_natRep_iff.mpr hX
  have h := mul_mem (e M hM) (e N hN)
  exact mem_flagKernel_natRep_iff.mp h

theorem isUpper_transvectionUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ}
    {p q : ι} (hpq : p ≠ q) (c : K) (h : ℓ p < ℓ q) :
    IsUpper ℓ (TauCeti.transvectionUnit hpq c) := by
  intro x y hxy
  rw [TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  have : ¬ (p = x ∧ q = y) := by
    rintro ⟨rfl, rfl⟩
    exact hxy h
  simp [this]

theorem mem_sup_of_coe_eq [Finite K] {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    {g : StatedSp n K} {p q p' q' : Fin n ⊕ Fin n} (hpq : p ≠ q) (hpq' : p' ≠ q') (c c' : K)
    (hg : (g : GL (Fin n ⊕ Fin n) K) =
      TauCeti.transvectionUnit hpq c * TauCeti.transvectionUnit hpq' c')
    (hp' : p' = Sum.swap q) (hq' : q' = Sum.swap p) (h : ℓ p ≠ ℓ q) :
    g ∈ spU n K ℓ ⊔ spU n K (ℓ ∘ Sum.swap) := by
  have h1 := hℓ.add_swap p
  have h2 := hℓ.add_swap q
  subst hp' hq'
  rcases lt_or_gt_of_ne h with hlt | hgt
  · refine Subgroup.mem_sup_left (mem_spU_iff.mpr ?_)
    rw [hg]
    exact (isUpper_transvectionUnit hpq c hlt).mul (isUpper_transvectionUnit hpq' c' (by omega))
  · refine Subgroup.mem_sup_right (mem_spU_iff.mpr ?_)
    rw [hg]
    refine (isUpper_transvectionUnit hpq c ?_).mul (isUpper_transvectionUnit hpq' c' ?_)
    · simp only [Function.comp_apply]
      omega
    · simp only [Function.comp_apply, Sum.swap_swap]
      omega

theorem mem_sup_of_coe_eq_single [Finite K] {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    {g : StatedSp n K} {p q : Fin n ⊕ Fin n} (hpq : p ≠ q) (c : K)
    (hg : (g : GL (Fin n ⊕ Fin n) K) = TauCeti.transvectionUnit hpq c)
    (hq : q = Sum.swap p) (h : ℓ p ≠ ℓ q) :
    g ∈ spU n K ℓ ⊔ spU n K (ℓ ∘ Sum.swap) := by
  have h1 := hℓ.add_swap p
  subst hq
  rcases lt_or_gt_of_ne h with hlt | hgt
  · refine Subgroup.mem_sup_left (mem_spU_iff.mpr ?_)
    rw [hg]
    exact isUpper_transvectionUnit hpq c hlt
  · refine Subgroup.mem_sup_right (mem_spU_iff.mpr ?_)
    rw [hg]
    refine isUpper_transvectionUnit hpq c ?_
    simp only [Function.comp_apply, Sum.swap_swap]
    omega

theorem coe_finEquiv_positiveLong (i : Fin n) (c : K) :
    ((finEquiv (positiveLongRootTransvectionUnit i c) : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      TauCeti.transvectionUnit (Sum.inl_ne_inr : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr i) c := by
  rw [coe_finEquiv, coe_positiveLongRootTransvectionUnit,
    reindexGL_transvectionUnit (Sum.inl i) (Sum.inr i) Sum.inl_ne_inr c]

theorem coe_finEquiv_negativeLong (i : Fin n) (c : K) :
    ((finEquiv (negativeLongRootTransvectionUnit i c) : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      TauCeti.transvectionUnit (Sum.inr_ne_inl : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inl i) c := by
  rw [coe_finEquiv, coe_negativeLongRootTransvectionUnit,
    reindexGL_transvectionUnit (Sum.inr i) (Sum.inl i) Sum.inr_ne_inl c]

theorem coe_finEquiv_difference {i j : Fin n} (hij : i ≠ j) (c : K) :
    ((finEquiv (differenceShortRootUnit hij c) : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      TauCeti.transvectionUnit (Sum.inl_injective.ne hij :
          (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inl j) c *
        TauCeti.transvectionUnit (Sum.inr_injective.ne hij.symm :
          (Sum.inr j : Fin n ⊕ Fin n) ≠ Sum.inr i) (-c) := by
  rw [coe_finEquiv, coe_differenceShortRootUnit, map_mul,
    reindexGL_transvectionUnit (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) c,
    reindexGL_transvectionUnit (Sum.inr j) (Sum.inr i) (Sum.inr_injective.ne hij.symm) (-c)]

theorem coe_finEquiv_positiveSum {i j : Fin n} (hij : i ≠ j) (c : K) :
    ((finEquiv (positiveSumShortRootUnit hij c) : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      TauCeti.transvectionUnit (Sum.inl_ne_inr : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr j) c *
        TauCeti.transvectionUnit (Sum.inl_ne_inr : (Sum.inl j : Fin n ⊕ Fin n) ≠ Sum.inr i) c := by
  rw [coe_finEquiv, coe_positiveSumShortRootUnit, map_mul,
    reindexGL_transvectionUnit (Sum.inl i) (Sum.inr j) Sum.inl_ne_inr c,
    reindexGL_transvectionUnit (Sum.inl j) (Sum.inr i) Sum.inl_ne_inr c]

theorem coe_finEquiv_negativeSum {i j : Fin n} (hij : i ≠ j) (c : K) :
    ((finEquiv (negativeSumShortRootUnit hij c) : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      TauCeti.transvectionUnit (Sum.inr_ne_inl : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inl j) c *
        TauCeti.transvectionUnit (Sum.inr_ne_inl : (Sum.inr j : Fin n ⊕ Fin n) ≠ Sum.inl i) c := by
  rw [coe_finEquiv, coe_negativeSumShortRootUnit, map_mul,
    reindexGL_transvectionUnit (Sum.inr i) (Sum.inl j) Sum.inr_ne_inl c,
    reindexGL_transvectionUnit (Sum.inr j) (Sum.inl i) Sum.inr_ne_inl c]

theorem commutatorElement_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem sup_spU_comp_swap [Finite K] {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ)
    (hne : ∃ c a, ℓ c < ℓ a) : spU n K ℓ ⊔ spU n K (ℓ ∘ Sum.swap) = ⊤ := by
  set N := spU n K ℓ ⊔ spU n K (ℓ ∘ Sum.swap) with hN
  set N' := N.comap (finEquiv (n := n) (K := K)).toMonoidHom with hN'
  have hmem : ∀ x, finEquiv x ∈ N → x ∈ N' := fun x hx => hx
  obtain ⟨k, hk⟩ : ∃ k, ℓ (Sum.inl k) ≠ ℓ (Sum.inr k) := by
    by_contra hall
    obtain ⟨c, a, hca⟩ := hne
    have h2 : ∀ b, 2 * ℓ b = M := by
      intro b
      have hb := hℓ.add_swap b
      have heq : ℓ b = ℓ (Sum.swap b) := by
        rcases b with t | t
        · by_contra h
          exact hall ⟨t, h⟩
        · by_contra h
          exact hall ⟨t, fun h' => h h'.symm⟩
      omega
    have := h2 c
    have := h2 a
    omega
  have hkM := hℓ k
  have hpos0 : ∀ i (c : K), ℓ (Sum.inl i) ≠ ℓ (Sum.inr i) →
      positiveLongRootTransvectionUnit i c ∈ N' := fun i c h =>
    hmem _ (mem_sup_of_coe_eq_single hℓ _ c (coe_finEquiv_positiveLong i c) rfl h)
  have hneg0 : ∀ i (c : K), ℓ (Sum.inr i) ≠ ℓ (Sum.inl i) →
      negativeLongRootTransvectionUnit i c ∈ N' := fun i c h =>
    hmem _ (mem_sup_of_coe_eq_single hℓ _ c (coe_finEquiv_negativeLong i c) rfl h)
  have hdiff0 : ∀ {i j : Fin n} (hij : i ≠ j) (c : K), ℓ (Sum.inl i) ≠ ℓ (Sum.inl j) →
      differenceShortRootUnit hij c ∈ N' := fun hij c h =>
    hmem _ (mem_sup_of_coe_eq hℓ _ _ c (-c) (coe_finEquiv_difference hij c) rfl rfl h)
  have hpsum0 : ∀ {i j : Fin n} (hij : i ≠ j) (c : K), ℓ (Sum.inl i) ≠ ℓ (Sum.inr j) →
      positiveSumShortRootUnit hij c ∈ N' := fun hij c h =>
    hmem _ (mem_sup_of_coe_eq hℓ _ _ c c (coe_finEquiv_positiveSum hij c) rfl rfl h)
  have hnsum0 : ∀ {i j : Fin n} (hij : i ≠ j) (c : K), ℓ (Sum.inr i) ≠ ℓ (Sum.inl j) →
      negativeSumShortRootUnit hij c ∈ N' := fun hij c h =>
    hmem _ (mem_sup_of_coe_eq hℓ _ _ c c (coe_finEquiv_negativeSum hij c) rfl rfl h)
  have hpos : ∀ (i : Fin n) (c : K), positiveLongRootTransvectionUnit i c ∈ N' := by
    intro i c
    by_cases hi : ℓ (Sum.inl i) = ℓ (Sum.inr i)
    · have hiM := hℓ i
      have hik : i ≠ k := by
        rintro rfl
        exact hk hi
      have hrel := commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit
        hik (1 : K) c
      rw [one_mul, one_pow, one_mul] at hrel
      have hc := commutatorElement_mem (hdiff0 hik (1 : K) (by omega)) (hpos0 k c hk)
      rw [hrel] at hc
      exact (N'.mul_mem_cancel_left (hpsum0 hik c (by omega))).mp hc
    · exact hpos0 i c hi
  have hneg : ∀ (i : Fin n) (c : K), negativeLongRootTransvectionUnit i c ∈ N' := by
    intro i c
    by_cases hi : ℓ (Sum.inr i) = ℓ (Sum.inl i)
    · have hiM := hℓ i
      have hki : k ≠ i := by
        rintro rfl
        exact hk hi.symm
      have hrel := commutatorElement_differenceShortRootUnit_negativeLongRootTransvectionUnit
        hki (1 : K) c
      rw [one_mul, one_pow, one_mul] at hrel
      have hc := commutatorElement_mem (hdiff0 hki (1 : K) (by omega))
        (hneg0 k c (Ne.symm hk))
      rw [hrel] at hc
      exact (N'.mul_mem_cancel_left (hnsum0 hki (-c) (by omega))).mp hc
    · exact hneg0 i c hi
  have hdiff : ∀ {i j : Fin n} (hij : i ≠ j) (c : K), differenceShortRootUnit hij c ∈ N' := by
    intro i j hij c
    by_cases hij' : ℓ (Sum.inl i) = ℓ (Sum.inl j)
    · have hiM := hℓ i
      have hjM := hℓ j
      by_cases hii : ℓ (Sum.inl i) = ℓ (Sum.inr i)
      · have hik : i ≠ k := by
          rintro rfl
          exact hk hii
        have hkj : k ≠ j := by
          rintro rfl
          exact hk (by omega)
        have hrel := commutatorElement_differenceShortRootUnit_differenceShortRootUnit
          hik hkj hij c (1 : K)
        rw [mul_one] at hrel
        rw [← hrel]
        exact commutatorElement_mem (hdiff0 hik c (by omega)) (hdiff0 hkj (1 : K) (by omega))
      · have hrel := commutatorElement_positiveSumShortRootUnit_negativeLongRootTransvectionUnit
          hij (1 : K) c
        rw [one_mul, one_pow, one_mul] at hrel
        have hc := commutatorElement_mem (hpsum0 hij (1 : K) (by omega)) (hneg j c)
        rw [hrel] at hc
        exact (N'.mul_mem_cancel_right (hpos i (-c))).mp hc
    · exact hdiff0 hij c hij'
  have htop : N' = ⊤ :=
    eq_top_of_root_subgroups N' (rootSubgroupHom_mem_of_difference_long N' hdiff hpos hneg)
  rw [eq_top_iff]
  intro g _
  have hg : finEquiv.symm g ∈ N' := by
    rw [htop]
    exact Subgroup.mem_top _
  have := hmem
  simpa [hN'] using hg

end GGOppRadSpU

end CFSG.StandardType
