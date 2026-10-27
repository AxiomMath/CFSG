module

public import CFSG.RankThree.PartTwo.Census.QuotientWitness
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven Matrix

section Quotient

variable {H : Type} [Group H]

theorem le_localRank_quotient_of_le_normalizer [Finite H] (N : Subgroup H) [N.Normal] {p k : ℕ}
    (hp : p.Prime) {E P : Subgroup H} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k)
    (hEN : E ⊓ N = ⊥) (hP2 : IsPGroup 2 P) (hPN : ¬ P ≤ N)
    (hEP : E ≤ Subgroup.normalizer (P : Set H)) : k ≤ localRank p (H ⧸ N) := by
  set π := QuotientGroup.mk' N
  have hP0 : P.map π ≠ ⊥ := by
    intro h
    apply hPN
    intro x hx
    have : π x ∈ P.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  exact le_localRank_of_le_normalizer hp hP0 (hP2.map π)
    (CFSG.SectionRank.isElemAbelian_map hE π)
    (by rw [card_map_mk_of_inf_eq_bot N hEN, hc])
    ((Subgroup.map_mono hEP).trans (Subgroup.le_normalizer_map π))

end Quotient

section TorusEntries

variable (G : Type*) [CommGroup G]

@[expose] def torusEntries (m n : ℕ) : (Fin m → G) →* (Fin n → G) where
  toFun s i := if h : i.val < m then s ⟨i, h⟩ else if i.val = m then (∏ j, s j)⁻¹ else 1
  map_one' := by
    funext i
    simp
  map_mul' s t := by
    funext i
    simp only [Pi.mul_apply]
    split_ifs
    · rfl
    · rw [Finset.prod_mul_distrib, mul_inv]
    · rw [mul_one]

variable {G}

theorem torusEntries_of_lt {m n : ℕ} (s : Fin m → G) {i : Fin n} (h : i.val < m) :
    torusEntries G m n s i = s ⟨i, h⟩ := by
  change (if h : i.val < m then s ⟨i, h⟩ else if i.val = m then (∏ j, s j)⁻¹ else 1) = _
  rw [dite_eq_left h]

theorem torusEntries_of_eq {m n : ℕ} (s : Fin m → G) {i : Fin n} (h : i.val = m) :
    torusEntries G m n s i = (∏ j, s j)⁻¹ := by
  change (if h : i.val < m then s ⟨i, h⟩ else if i.val = m then (∏ j, s j)⁻¹ else 1) = _
  rw [dite_eq_right (by omega), ite_eq_left h]

theorem torusEntries_of_gt {m n : ℕ} (s : Fin m → G) {i : Fin n} (h : m < i.val) :
    torusEntries G m n s i = 1 := by
  change (if h : i.val < m then s ⟨i, h⟩ else if i.val = m then (∏ j, s j)⁻¹ else 1) = _
  rw [dite_eq_right (by omega), ite_eq_right (by omega)]

theorem prod_torusEntries {m n : ℕ} (hm : m < n) (s : Fin m → G) :
    ∏ i, torusEntries G m n s i = 1 := by
  set g : ℕ → G := fun j => if h : j < m then s ⟨j, h⟩ else if j = m then (∏ i, s i)⁻¹ else 1
  have hg : ∀ i : Fin n, torusEntries G m n s i = g i := fun _ => rfl
  simp only [hg]
  rw [Fin.prod_univ_eq_prod_range g n, ← Finset.prod_range_mul_prod_Ico g hm,
    Finset.prod_range_succ]
  have h1 : ∏ j ∈ Finset.range m, g j = ∏ i, s i := by
    rw [← Fin.prod_univ_eq_prod_range g m]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [g, dite_eq_left i.2]
  have h2 : ∏ j ∈ Finset.Ico (m + 1) n, g j = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    have := (Finset.mem_Ico.mp hj).1
    simp only [g, dite_eq_right (show ¬ j < m by omega), ite_eq_right (show j ≠ m by omega)]
  have h3 : g m = (∏ i, s i)⁻¹ := by simp [g]
  rw [h1, h2, h3, mul_inv_cancel, one_mul]

theorem torusEntries_injective {m n : ℕ} (hm : m ≤ n) :
    Function.Injective (torusEntries G m n) := by
  intro s t h
  funext j
  have := congrFun h ⟨j, by omega⟩
  rwa [torusEntries_of_lt (n := n) s (i := ⟨j, by omega⟩) j.2,
    torusEntries_of_lt (n := n) t (i := ⟨j, by omega⟩) j.2] at this

end TorusEntries

section Roots

variable {K : Type} [Field K]

theorem rootsOfUnity_pow_eq_one {r : ℕ} (x : rootsOfUnity r K) : x ^ r = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity r (x : Kˣ)).mp x.2

theorem card_fun_rootsOfUnity {r m : ℕ} (hr : Nat.card (rootsOfUnity r K) = r) :
    Nat.card (Fin m → rootsOfUnity r K) = r ^ m := by
  rw [Nat.card_fun, hr, Nat.card_fin]

theorem card_rootsOfUnity_of_dvd [Finite K] {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card Kˣ) : Nat.card (rootsOfUnity r K) = r := by
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hprim : IsPrimitiveRoot ζ r := hζ ▸ IsPrimitiveRoot.orderOf ζ
  exact hprim.card_rootsOfUnity'

end Roots


theorem le_normalizer_of_conj_mem {H : Type} [Group H] {E P : Subgroup H}
    (h : ∀ x ∈ E, ∀ y ∈ P, x * y * x⁻¹ ∈ P) : E ≤ Subgroup.normalizer (P : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  refine fun y => ⟨h x hx y, fun hy => ?_⟩
  have := h x⁻¹ (inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem torusEntries_compLeft {G G' : Type*} [CommGroup G] [CommGroup G'] (φ : G →* G')
    {m n : ℕ} (s : Fin m → G) :
    torusEntries G' m n (φ.compLeft (Fin m) s) = φ.compLeft (Fin n) (torusEntries G m n s) := by
  funext i
  simp only [MonoidHom.compLeft_apply, Function.comp_apply]
  by_cases h1 : i.val < m
  · rw [torusEntries_of_lt _ h1, torusEntries_of_lt _ h1]
    rfl
  by_cases h2 : i.val = m
  · rw [torusEntries_of_eq _ h2, torusEntries_of_eq _ h2, map_inv, map_prod]
    rfl
  · rw [torusEntries_of_gt _ (by omega), torusEntries_of_gt _ (by omega), map_one]

section PSL

variable {K : Type} [Field K]

@[expose] noncomputable def torusSL (m n : ℕ) (hm : m < n) (K : Type) [Field K] :
    (Fin m → Kˣ) →* SpecialLinearGroup (Fin n) K where
  toFun s := ⟨diagonal fun i => ((torusEntries Kˣ m n s i : Kˣ) : K), by
    rw [det_diagonal, ← Units.coe_prod, prod_torusEntries hm, Units.val_one]⟩
  map_one' := Subtype.ext (by
    change diagonal (fun i => ((torusEntries Kˣ m n 1 i : Kˣ) : K)) = 1
    simp)
  map_mul' s t := Subtype.ext (by
    change diagonal (fun i => ((torusEntries Kˣ m n (s * t) i : Kˣ) : K)) =
      diagonal (fun i => ((torusEntries Kˣ m n s i : Kˣ) : K)) *
        diagonal (fun i => ((torusEntries Kˣ m n t i : Kˣ) : K))
    rw [diagonal_mul_diagonal, map_mul]
    rfl)

theorem coe_torusSL {m n : ℕ} (hm : m < n) (s : Fin m → Kˣ) :
    ((torusSL m n hm K s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => ((torusEntries Kˣ m n s i : Kˣ) : K) :=
  rfl

theorem torusSL_injective {m n : ℕ} (hm : m < n) : Function.Injective (torusSL m n hm K) := by
  intro s t h
  refine torusEntries_injective hm.le (funext fun i => Units.ext ?_)
  have := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h
  simpa only [coe_torusSL, diagonal_apply_eq] using this

@[expose] noncomputable def rootSL {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (K : Type) [Field K] : Multiplicative K →* SpecialLinearGroup ι K where
  toFun c := SpecialLinearGroup.transvection hij c.toAdd
  map_one' := SpecialLinearGroup.transvection_coeff_zero hij
  map_mul' _ _ := SpecialLinearGroup.transvection_add hij _ _

theorem diagonal_mul_transvection {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (d : ι → Kˣ) (c : K) :
    diagonal (fun l => (d l : K)) * Matrix.transvection i j c =
      Matrix.transvection i j ((d i : K) * c * ((d j)⁻¹ : Kˣ)) * diagonal (fun l => (d l : K)) := by
  ext a b
  simp only [Matrix.transvection, diagonal_mul, mul_diagonal, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [this]
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp only [hab, ite_false, zero_add, and_self, ite_true]
      rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]
    · simp [hab, h]

theorem isElemAbelian_range {A H : Type*} [CommGroup A] [Group H] {p : ℕ}
    (hA : ∀ a : A, a ^ p = 1) (φ : A →* H) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : H) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨v, rfl⟩ := hx
    rw [← map_pow, hA, map_one]

theorem le_localRank_PSL_torus [Finite K] [CharP K 2] {r m n : ℕ} (hr : r.Prime)
    (hrK : r ∣ Nat.card Kˣ) (hmn : m < n) (h1n : 1 < n) (hcen : m + 1 < n ∨ ¬ r ∣ n) :
    m ≤ localRank r (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set incl := (rootsOfUnity r K).subtype
  set φ := (torusSL m n hmn K).comp (incl.compLeft (Fin m))
  have hφ : Function.Injective φ :=
    (torusSL_injective hmn).comp fun s t hst => funext fun j =>
      Subtype.ext (congrFun hst j)
  have hentry : ∀ s i, ((φ s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      ((incl (torusEntries (rootsOfUnity r K) m n s i) : Kˣ) : K) := by
    intro s i
    change ((torusSL m n hmn K (incl.compLeft (Fin m) s) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i i = _
    rw [coe_torusSL, diagonal_apply_eq, torusEntries_compLeft]
    rfl
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, h1n⟩ := by simp
  set P := (rootSL h01 K).range
  refine le_localRank_quotient_of_le_normalizer _ hr (E := φ.range) (P := P)
    (isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) φ)
    ?_ ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxc⟩
    obtain ⟨c, hcn, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    rw [Fintype.card_fin] at hcn
    have hci : ∀ i, c = ((incl (torusEntries (rootsOfUnity r K) m n s i) : Kˣ) : K) := by
      intro i
      rw [← hentry, ← hc, scalar_apply, diagonal_apply_eq]
    have hc1 : c = 1 := by
      rcases hcen with h | h
      · rw [hci ⟨m + 1, h⟩, torusEntries_of_gt _ (by simp), map_one, Units.val_one]
      · have hcr : c ^ r = 1 := by
          rw [hci ⟨0, by omega⟩, ← Units.val_pow_eq_pow_val, ← map_pow,
            rootsOfUnity_pow_eq_one, map_one, Units.val_one]
        have hg : c ^ Nat.gcd r n = 1 := pow_gcd_eq_one.mpr ⟨hcr, hcn⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hr).mpr h), pow_one]
          at hg
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [← hc, hc1, map_one]
    rfl
  · intro y
    obtain ⟨c, hc⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hc, ← map_mul, OneMemClass.coe_one]
    change SpecialLinearGroup.transvection h01 (c.toAdd + c.toAdd) = 1
    rw [CharTwo.add_self_eq_zero, SpecialLinearGroup.transvection_coeff_zero]
  · intro hP
    have h1 : rootSL h01 K (Multiplicative.ofAdd 1) ∈ P := ⟨_, rfl⟩
    have := (SpecialLinearGroup.transvection_mem_center_iff h01 (1 : K)).mp (hP h1)
    exact one_ne_zero this
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨s, rfl⟩ _ ⟨c, rfl⟩
    set d := incl.compLeft (Fin n) (torusEntries (rootsOfUnity r K) m n s)
    refine ⟨Multiplicative.ofAdd ((d ⟨0, by omega⟩ : K) * c.toAdd *
      ((d ⟨1, h1n⟩)⁻¹ : Kˣ)), ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Subtype.ext ?_
    change Matrix.transvection _ _ _ * ((φ s : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((φ s : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * Matrix.transvection _ _ c.toAdd
    have hφs : ((φ s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        diagonal fun l => (d l : K) := by
      change ((torusSL m n hmn K (incl.compLeft (Fin m) s) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = _
      rw [coe_torusSL, torusEntries_compLeft]
    rw [hφs, diagonal_mul_transvection h01 d]
    rfl

end PSL

section PSU

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def diagGL (n : ℕ) (K : Type) [Field K] : (Fin n → Kˣ) →* GL (Fin n) K where
  toFun d := ⟨diagonal fun i => (d i : K), diagonal fun i => ((d i)⁻¹ : Kˣ), by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => Units.mul_inv _), by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => Units.inv_mul _)⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    change diagonal (fun i => ((a * b) i : K)) = diagonal (fun i => (a i : K)) *
      diagonal (fun i => (b i : K))
    rw [diagonal_mul_diagonal]
    rfl)

theorem coe_diagGL {n : ℕ} (d : Fin n → Kˣ) :
    ((diagGL n K d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => (d i : K) :=
  rfl

@[expose] def dupHom (G : Type*) [CommGroup G] (k : ℕ) :
    (Fin (k + 1) → G) →* (Fin (k + 2) → G) where
  toFun s j := s ⟨j.val - 1, by omega⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem dupHom_apply {G : Type*} [CommGroup G] {k : ℕ} (s : Fin (k + 1) → G) (j : Fin (k + 2)) :
    dupHom G k s j = s ⟨j.val - 1, by omega⟩ :=
  rfl

theorem dupHom_injective {G : Type*} [CommGroup G] (k : ℕ) :
    Function.Injective (dupHom G k) := by
  intro s t h
  funext j
  have := congrFun h ⟨j.val + 1, by omega⟩
  simpa [dupHom_apply] using this

@[expose] def swapBlock (n : ℕ) (K : Type) [Field K] : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if i.val < 2 ∧ j.val < 2 then 1 else 0

theorem swapBlock_mul_self [CharP K 2] {n : ℕ} (hn : 2 ≤ n) :
    swapBlock n K * swapBlock n K = 0 := by
  ext i j
  simp only [swapBlock, mul_apply, of_apply, Matrix.zero_apply]
  by_cases hij : i.val < 2 ∧ j.val < 2
  · have : ∀ l : Fin n, ((if i.val < 2 ∧ l.val < 2 then (1 : K) else 0) *
        if l.val < 2 ∧ j.val < 2 then 1 else 0) = if l.val < 2 then 1 else 0 := by
      intro l
      by_cases hl : l.val < 2 <;> simp [hl, hij.1, hij.2]
    rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_boole, Fin.card_filter_val_lt,
      min_eq_right hn]
    simp only [Nat.cast_ofNat, CharTwo.two_eq_zero]
  · refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hi : i.val < 2
    · have hj : ¬ j.val < 2 := fun hj => hij ⟨hi, hj⟩
      simp [hj]
    · simp [hi]

theorem swapBlock_transpose {n : ℕ} : (swapBlock n K)ᵀ = swapBlock n K := by
  ext i j
  simp only [swapBlock, transpose_apply, of_apply, and_comm]

theorem swapBlock_map {n : ℕ} (φ : K →+* K) : (swapBlock n K).map φ = swapBlock n K := by
  ext i j
  simp only [swapBlock, map_apply, of_apply]
  split_ifs <;> simp

theorem one_add_mul_one_add [CharP K 2] {n : ℕ} {N : Matrix (Fin n) (Fin n) K}
    (hN : N * N = 0) : (1 + N) * (1 + N) = 1 := by
  have hNN : N + N = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hN, add_zero, add_assoc, hNN,
    add_zero]

@[expose] def swapGL [CharP K 2] {n : ℕ} (hn : 2 ≤ n) : GL (Fin n) K :=
  ⟨1 + swapBlock n K, 1 + swapBlock n K, one_add_mul_one_add (swapBlock_mul_self hn),
    one_add_mul_one_add (swapBlock_mul_self hn)⟩

theorem coe_swapGL [CharP K 2] {n : ℕ} (hn : 2 ≤ n) :
    ((swapGL hn : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + swapBlock n K :=
  rfl

theorem eq_one_of_mul_self_eq_one [CharP K 2] {x : K} (hx : x * x = 1) : x = 1 := by
  have : (x - 1) * (x - 1) = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hx - (x - 1) * h2
  have := mul_self_eq_zero.mp this
  exact sub_eq_zero.mp this

theorem swapGL_mem_statedSU [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K) [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) : swapGL (K := K) hn ∈ StatedSU n (p ^ f) K := by
  refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
  · refine eq_one_of_mul_self_eq_one ?_
    rw [← det_mul, coe_swapGL, one_add_mul_one_add (swapBlock_mul_self hn), det_one]
  · rw [coe_swapGL, Matrix.map_add _ (map_add h.bar), swapBlock_map, transpose_add,
      swapBlock_transpose, Matrix.map_one _ (map_zero _) (map_one _), transpose_one]
    exact one_add_mul_one_add (swapBlock_mul_self hn)

theorem diagonal_mul_swap {n : ℕ} {d : Fin n → K} (hd : ∀ i j : Fin n, i.val < 2 → j.val < 2 →
    d i = d j) : diagonal d * (1 + swapBlock n K) = (1 + swapBlock n K) * diagonal d := by
  rw [mul_add, add_mul, mul_one, one_mul, add_right_inj]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  simp only [swapBlock, of_apply]
  split_ifs with hij
  · rw [hd i j hij.1 hij.2, mul_one, one_mul]
  · simp

theorem le_localRank_statedSU_torus [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K)
    [CharP K 2] {r k n : ℕ} (hr : r.Prime) (hrq : r ∣ p ^ f + 1) (hkn : k + 2 < n)
    (hcen : k + 3 < n ∨ ¬ r ∣ n) :
    k + 1 ≤ localRank r (StatedProj (StatedSU n (p ^ f) K)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hn2 : 2 ≤ n := by omega
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul', sq,
      show p ^ f * p ^ f - 1 = p ^ f * p ^ f - 1 * 1 by rw [mul_one],
      Nat.mul_self_sub_mul_self_eq]
    exact dvd_mul_of_dvd_left hrq _
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  set u : (Fin (k + 1) → μ) →* (Fin n → μ) := (torusEntries μ (k + 2) n).comp (dupHom μ k)
  set d : (Fin (k + 1) → μ) →* (Fin n → Kˣ) := (incl.compLeft (Fin n)).comp u
  set ψ := (diagGL n K).comp d
  have hd : ∀ s i, d s i = incl (u s i) := fun _ _ => rfl
  have hdr : ∀ s i, (d s i : K) ^ r = 1 := by
    intro s i
    rw [hd, ← Units.val_pow_eq_pow_val, ← map_pow, rootsOfUnity_pow_eq_one, map_one,
      Units.val_one]
  have hcoe : ∀ s, ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (d s i : K) := fun _ => rfl
  have hmem : ∀ s, ψ s ∈ StatedSU n (p ^ f) K := by
    intro s
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [hcoe, det_diagonal, ← Units.coe_prod]
      have : ∏ i, d s i = incl (∏ i, torusEntries μ (k + 2) n (dupHom μ k s) i) := by
        rw [map_prod]
        rfl
      rw [this, prod_torusEntries hkn, map_one, Units.val_one]
    · rw [hcoe, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one]
      refine congrArg diagonal (funext fun i => ?_)
      obtain ⟨m, hm⟩ := hrq
      rw [h.bar_apply, ← pow_succ, hm, pow_mul, hdr, one_pow]
  set ψ' : (Fin (k + 1) → μ) →* StatedSU n (p ^ f) K := ψ.codRestrict _ hmem
  have hψ' : Function.Injective ψ' := by
    intro s t hst
    have h1 : ψ s = ψ t := congrArg Subtype.val hst
    have h2 : d s = d t := by
      funext i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h1
      simp only [hcoe, diagonal_apply_eq] at this
      exact Units.ext this
    have h3 : u s = u t := funext fun i => Subtype.ext (congrFun h2 i)
    exact dupHom_injective k (torusEntries_injective hkn.le h3)
  set Z := (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)
  set t : StatedSU n (p ^ f) K := ⟨swapGL hn2, swapGL_mem_statedSU h hn2⟩
  refine le_localRank_quotient_of_commute Z hr (E := ψ'.range)
    (isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) ψ') ?_ ?_
    (t := t) ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ').toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxZ⟩
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hxZ)
    have hc' : GeneralLinearGroup.scalar (Fin n) c = ψ s := hc
    have hci : ∀ i, (c : K) = (d s i : K) := by
      intro i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) hc'
      simpa only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, hcoe]
        using this
    have hc1 : (c : K) = 1 := by
      rcases hcen with hlt | hndvd
      · rw [hci ⟨k + 3, hlt⟩, hd]
        change ((incl (torusEntries μ (k + 2) n (dupHom μ k s) ⟨k + 3, hlt⟩) : Kˣ) : K) = 1
        rw [torusEntries_of_gt _ (by simp), map_one, Units.val_one]
      · have hcr : (c : K) ^ r = 1 := by rw [hci ⟨0, by omega⟩, hdr]
        have hcn : (c : K) ^ n = 1 := by
          have hdet := ((mem_unitarySU_iff h).mp (hmem s)).1
          rw [← hc', GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
            Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
          exact hdet
        have hg : (c : K) ^ Nat.gcd r n = 1 := pow_gcd_eq_one.mpr ⟨hcr, hcn⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hr).mpr hndvd), pow_one]
          at hg
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    change ψ s = 1
    rw [← hc', show c = 1 from Units.ext hc1, map_one]
  · intro htZ
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp htZ
    have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
      ⟨1, by omega⟩) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, t, coe_swapGL, swapBlock,
      Matrix.add_apply, of_apply, Matrix.one_apply] at this
    simp at this
  · rw [show t ^ 2 = 1 from Subtype.ext (Units.ext (by
      rw [pow_two]
      exact one_add_mul_one_add (swapBlock_mul_self hn2)))]
    exact Z.one_mem
  · rintro _ ⟨s, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    change ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 + swapBlock n K) =
      (1 + swapBlock n K) * ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hcoe]
    refine diagonal_mul_swap fun i j hi hj => ?_
    have key : ∀ l : Fin n, l.val < 2 → (d s l : K) = ((incl (s ⟨0, by omega⟩) : Kˣ) : K) := by
      intro l hl
      rw [hd]
      change ((incl (torusEntries μ (k + 2) n (dupHom μ k s) l) : Kˣ) : K) = _
      rw [torusEntries_of_lt _ (by omega), dupHom_apply]
      congr 3
      ext
      simp only
      omega
    rw [key i hi, key j hj]

end PSU

end CFSG.RankThree.PartTwo.Census
