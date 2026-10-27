module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAux
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative CFSG.ComponentClassification

theorem eq_of_isComponentOf_le_of_isQuasisimple {G : Type} [Group G] {C Q J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J C) (hJQ : J ≤ Q) (hQC : Q ≤ C)
    (hQ : CFSG.Assembly.IsQuasisimple Q) : J = Q := by
  have hJQ' : CFSG.Assembly.IsSubnormal J Q := by
    have h := hJ.2.1.inf Q
    rwa [inf_eq_left.mpr hJQ, inf_eq_right.mpr hQC] at h
  have hsub : (J.subgroupOf Q).IsSubnormal :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJQ).mp hJQ'
  have hQn : CFSG.IsQuasisimple Q :=
    (AssemblyBPredicates.isQuasisimple_iff_native Q).mp hQ
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQn hsub with h | h
  · have htop : J.subgroupOf Q = ⊤ := h
    have hQJ : Q ≤ J := Subgroup.subgroupOf_eq_top.mp htop
    exact le_antisymm hJQ hQJ
  · exfalso
    refine LinSemisimple.false_of_isQuasisimple_of_commute hJ.2.2 ?_
    intro x hx y hy
    have hxZ : (⟨x, hJQ hx⟩ : Q) ∈ Subgroup.center Q :=
      h (show (⟨x, hJQ hx⟩ : Q) ∈ J.subgroupOf Q from hx)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨y, hJQ hy⟩)).symm

variable {F : Type} [Field F] {f m ε p : ℕ} {h : UnitaryFieldData 2 f F}

theorem exists_mem_hypSU_of_diagonal {d : HypIndex m ε → F}
    (_hne : ∀ x, d x ≠ 0) (hunit : ∀ x, h.bar (d x) * d (hypPartner x) = 1)
    (hdet : ∏ x, d x = 1) :
    ∃ g : hypSU h m ε,
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F) =
        diagonal d := by
  classical
  have hdetne : (diagonal d : Matrix (HypIndex m ε) (HypIndex m ε) F).det ≠ 0 := by
    rw [det_diagonal, hdet]
    exact one_ne_zero
  let g0 : GL (HypIndex m ε) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal d) hdetne
  have hcoe : ((g0 : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F) =
      diagonal d := by
    simp [g0]
  have hiso : ((diagonal d).map h.bar)ᵀ * hypGram m ε F * diagonal d = hypGram m ε F := by
    ext x y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, Matrix.diagonal_mul, hypGram_apply]
    split_ifs with hy
    · rw [hy]
      simpa using hunit x
    · ring
  refine ⟨⟨g0, mem_hypSU.mpr ⟨?_, ?_⟩⟩, ?_⟩
  · rw [hcoe]
    exact hiso
  · rw [hcoe, det_diagonal, hdet]
  · rw [hcoe]

@[expose] noncomputable def diagOne (i : Fin m) (c : F) : HypIndex m ε → F
  | .inl j => if j = i then c else 1
  | .inr (.inl _) => 1
  | .inr (.inr j) => if j = i then c⁻¹ else 1

@[simp] theorem diagOne_inl (i j : Fin m) (c : F) :
    diagOne (ε := ε) i c (.inl j) = if j = i then c else 1 := rfl

@[simp] theorem diagOne_z (i : Fin m) (c : F) (k : Fin ε) :
    diagOne (ε := ε) i c (.inr (.inl k)) = 1 := rfl

@[simp] theorem diagOne_inr (i j : Fin m) (c : F) :
    diagOne (ε := ε) i c (.inr (.inr j)) = if j = i then c⁻¹ else 1 := rfl

@[expose] noncomputable def diagTwo (i j : Fin m) (c : F) : HypIndex m ε → F
  | .inl k => if k = i then c else if k = j then c⁻¹ else 1
  | .inr (.inl _) => 1
  | .inr (.inr k) => if k = i then (h.bar c)⁻¹ else if k = j then h.bar c else 1

@[simp] theorem diagTwo_inl (i j k : Fin m) (c : F) :
    diagTwo (ε := ε) (h := h) i j c (.inl k) =
      if k = i then c else if k = j then c⁻¹ else 1 := rfl

@[simp] theorem diagTwo_z (i j : Fin m) (c : F) (k : Fin ε) :
    diagTwo (ε := ε) (h := h) i j c (.inr (.inl k)) = 1 := rfl

@[simp] theorem diagTwo_inr (i j k : Fin m) (c : F) :
    diagTwo (ε := ε) (h := h) i j c (.inr (.inr k)) =
      if k = i then (h.bar c)⁻¹ else if k = j then h.bar c else 1 := rfl

private theorem prod_ite_single_of_mem {ι : Type*} [DecidableEq ι] {s : Finset ι} {i : ι}
    (hi : i ∈ s) (c : F) : s.prod (fun j => if j = i then c else (1 : F)) = c := by
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [if_neg hj]) (fun h => absurd hi h)]
  simp

private theorem prod_ite_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (c : F) :
    (∏ j, (if j = i then c else (1 : F))) = c :=
  prod_ite_single_of_mem (Finset.mem_univ i) c

private theorem prod_ite_two {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (a b : F) :
    (∏ k, (if k = i then a else if k = j then b else (1 : F))) = a * b := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have h1 : ∀ k ∈ (Finset.univ.erase i),
      (if k = i then a else if k = j then b else (1 : F)) =
        if k = j then b else 1 := by
    intro k hk
    rw [if_neg (Finset.ne_of_mem_erase hk)]
  rw [Finset.prod_congr rfl h1,
    prod_ite_single_of_mem (s := Finset.univ.erase i) (i := j)
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) b]
  rw [if_pos rfl]
  ring

theorem exists_diagOne (i : Fin m) {c : F} (hc0 : c ≠ 0) (hcb : h.bar c = c) :
    ∃ g : hypSU h m ε,
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F) =
        diagonal (diagOne (ε := ε) i c) := by
  classical
  have hne : ∀ x, diagOne (ε := ε) i c x ≠ 0 := by
    intro x
    rcases x with j | k | j <;> simp only [diagOne_inl, diagOne_z, diagOne_inr]
    · by_cases hji : j = i <;> simp [hji, hc0]
    · exact one_ne_zero
    · by_cases hji : j = i <;> simp [hji, inv_eq_zero, hc0]
  have hunit : ∀ x, h.bar (diagOne (ε := ε) i c x) * diagOne (ε := ε) i c (hypPartner x) = 1 := by
    intro x
    rcases x with j | k | j
    · rw [hypPartner, diagOne_inl, diagOne_inr]
      by_cases hji : j = i
      · rw [if_pos hji, if_pos hji, hcb]
        exact mul_inv_cancel₀ hc0
      · rw [if_neg hji, if_neg hji]
        simp
    · rw [hypPartner, diagOne_z]
      simp
    · rw [hypPartner, diagOne_inr, diagOne_inl]
      by_cases hji : j = i
      · rw [if_pos hji, if_pos hji, map_inv₀, hcb]
        exact inv_mul_cancel₀ hc0
      · rw [if_neg hji, if_neg hji]
        simp
  have hdet : (∏ x, diagOne (ε := ε) i c x) = 1 := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [diagOne_inl, diagOne_inr, diagOne_z]
    rw [prod_ite_single i c, prod_ite_single i c⁻¹]
    simp [hc0]
  exact exists_mem_hypSU_of_diagonal hne hunit hdet


theorem exists_diagTwo (i j : Fin m) (hij : i ≠ j) {c : F} (hc0 : c ≠ 0) :
    ∃ g : hypSU h m ε,
      (((g : hypSU h m ε) : GL (HypIndex m ε) F) : Matrix (HypIndex m ε) (HypIndex m ε) F) =
        diagonal (diagTwo (h := h) (ε := ε) i j c) := by
  classical
  have hbarc : h.bar c ≠ 0 := by
    intro h0
    exact hc0 (by rw [← h.bar_bar c, h0, map_zero])
  have hne : ∀ x, diagTwo (h := h) (ε := ε) i j c x ≠ 0 := by
    intro x
    rcases x with k | l | k
    · simp only [diagTwo_inl]
      by_cases hki : k = i
      · rw [if_pos hki]
        exact hc0
      · by_cases hkj : k = j
        · rw [if_neg hki, if_pos hkj]
          exact inv_ne_zero hc0
        · rw [if_neg hki, if_neg hkj]
          exact one_ne_zero
    · rw [diagTwo_z]
      exact one_ne_zero
    · simp only [diagTwo_inr]
      by_cases hki : k = i
      · rw [if_pos hki]
        exact inv_ne_zero hbarc
      · by_cases hkj : k = j
        · rw [if_neg hki, if_pos hkj]
          exact hbarc
        · rw [if_neg hki, if_neg hkj]
          exact one_ne_zero
  have hunit : ∀ x, h.bar (diagTwo (h := h) (ε := ε) i j c x) *
      diagTwo (h := h) (ε := ε) i j c (hypPartner x) = 1 := by
    intro x
    rcases x with k | l | k
    · rw [hypPartner, diagTwo_inl, diagTwo_inr]
      by_cases hki : k = i
      · simp only [if_pos hki]
        exact mul_inv_cancel₀ hbarc
      · by_cases hkj : k = j
        · simp only [if_neg hki, if_pos hkj, map_inv₀]
          exact inv_mul_cancel₀ hbarc
        · simp only [if_neg hki, if_neg hkj]
          simp
    · rw [hypPartner, diagTwo_z]
      simp
    · rw [hypPartner, diagTwo_inr, diagTwo_inl]
      by_cases hki : k = i
      · simp only [if_pos hki, map_inv₀, h.bar_bar]
        exact inv_mul_cancel₀ hc0
      · by_cases hkj : k = j
        · simp only [if_neg hki, if_pos hkj, h.bar_bar]
          exact mul_inv_cancel₀ hc0
        · simp only [if_neg hki, if_neg hkj]
          simp
  have hdet : (∏ x, diagTwo (h := h) (ε := ε) i j c x) = 1 := by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [diagTwo_inl, diagTwo_inr, diagTwo_z]
    rw [prod_ite_two hij c c⁻¹, prod_ite_two hij (h.bar c)⁻¹ (h.bar c)]
    simp [mul_inv_cancel₀ hc0, inv_mul_cancel₀ hbarc]
  exact exists_mem_hypSU_of_diagonal hne hunit hdet

@[simp] theorem diagOne_inl_self (i : Fin m) (c : F) :
    diagOne (ε := ε) i c (.inl i : HypIndex m ε) = c := by simp [diagOne]

@[simp] theorem diagOne_z_apply (i : Fin m) (c : F) (k : Fin ε) :
    diagOne (ε := ε) i c (.inr (.inl k) : HypIndex m ε) = 1 := rfl

@[simp] theorem diagOne_inr_self (i : Fin m) (c : F) :
    diagOne (ε := ε) i c (.inr (.inr i) : HypIndex m ε) = c⁻¹ := by simp [diagOne]

@[simp] theorem diagTwo_inl_self (i j : Fin m) (c : F) :
    diagTwo (h := h) (ε := ε) i j c (.inl i : HypIndex m ε) = c := by simp [diagTwo]

@[simp] theorem diagTwo_inl_ne {i j : Fin m} (hij : i ≠ j) (c : F) :
    diagTwo (h := h) (ε := ε) i j c (.inl j : HypIndex m ε) = c⁻¹ := by
  simp [diagTwo, Ne.symm hij]

@[simp] theorem diagTwo_inr_self (i j : Fin m) (c : F) :
    diagTwo (h := h) (ε := ε) i j c (.inr (.inr i) : HypIndex m ε) = (h.bar c)⁻¹ := by
  simp [diagTwo]

@[simp] theorem diagTwo_inr_ne {i j : Fin m} (hij : i ≠ j) (c : F) :
    diagTwo (h := h) (ε := ε) i j c (.inr (.inr j) : HypIndex m ε) = h.bar c := by
  simp [diagTwo, Ne.symm hij]

theorem mem_centralizer_of_diagonal {d : HypIndex m ε → F} {g : hypSU h m ε}
    {ζ : F} {τ : Multiplicative (Fin m → ZMod p) →* hypSU h m ε}
    (hτ : IsSplitTorus h ζ τ)
    {E : Set (Multiplicative (Fin m → ZMod p))}
    (hg : (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) = diagonal d) :
    g ∈ Subgroup.centralizer (τ '' E) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨t, ht, rfl⟩
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hτt : (((τ t : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) =
      diagonal (splitEntries ζ (Multiplicative.toAdd t)) := hτ (Multiplicative.toAdd t)
  rw [hg, hτt]
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm (splitEntries ζ (Multiplicative.toAdd t) x) (d x)

theorem mem_hypBlock_of_diagonal {P : Set (HypIndex m ε)} {d : HypIndex m ε → F}
    (hd : ∀ x, x ∉ P → d x = 1) {g : hypSU h m ε}
    (hg : (((g : hypSU h m ε) : GL (HypIndex m ε) F) :
      Matrix (HypIndex m ε) (HypIndex m ε) F) = diagonal d) :
    g ∈ hypBlock h P := by
  rw [mem_hypBlock]
  intro a b hab
  rw [hg, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl]
    rcases hab with ha | hb
    · exact hd a ha
    · exact hd a hb
  · rw [if_neg h, if_neg h]

theorem diagOne_eq_one_of_not_mem {P : Set (HypIndex m ε)} {i : Fin m} {c : F}
    (hi : (.inl i : HypIndex m ε) ∈ P)
    (fi : (.inr (.inr i) : HypIndex m ε) ∈ P) {x : HypIndex m ε} (hx : x ∉ P) :
    diagOne (ε := ε) i c x = 1 := by
  rcases x with k | l | k
  · simp only [diagOne_inl]
    by_cases hki : k = i
    · exact absurd (hki ▸ hi) hx
    · rw [if_neg hki]
  · rw [diagOne_z]
  · simp only [diagOne_inr]
    by_cases hki : k = i
    · exact absurd (hki ▸ fi) hx
    · rw [if_neg hki]

theorem diagTwo_eq_one_of_not_mem {P : Set (HypIndex m ε)} {i j : Fin m} {c : F}
    (hi : (.inl i : HypIndex m ε) ∈ P)
    (hj : (.inl j : HypIndex m ε) ∈ P)
    (fi : (.inr (.inr i) : HypIndex m ε) ∈ P)
    (fj : (.inr (.inr j) : HypIndex m ε) ∈ P) {x : HypIndex m ε} (hx : x ∉ P) :
    diagTwo (h := h) (ε := ε) i j c x = 1 := by
  rcases x with k | l | k
  · simp only [diagTwo_inl]
    by_cases hki : k = i
    · exact absurd (hki ▸ hi) hx
    · by_cases hkj : k = j
      · exact absurd (hkj ▸ hj) hx
      · rw [if_neg hki, if_neg hkj]
  · rw [diagTwo_z]
  · simp only [diagTwo_inr]
    by_cases hki : k = i
    · exact absurd (hki ▸ fi) hx
    · by_cases hkj : k = j
      · exact absurd (hkj ▸ fj) hx
      · rw [if_neg hki, if_neg hkj]

theorem ne_inv_of_bar_ne {c : F} (hc : h.bar c ≠ c) : c ≠ c⁻¹ := by
  have : CharP F 2 := h.charP
  intro hinv
  have hsq : c ^ 2 = 1 := by
    have h2 : c * c⁻¹ = 1 := mul_inv_cancel₀ (fun h0 => hc (by rw [h0]; simp))
    rw [← hinv] at h2
    simpa [pow_two] using h2
  have h1 : c = 1 := (CharTwo.sq_inj (x := c) (y := 1)).mp (by simpa using hsq)
  exact hc (by rw [h1, map_one])

theorem ne_inv_of_bar_ne_bar {c : F} (hc : h.bar c ≠ c) : h.bar c ≠ (h.bar c)⁻¹ := by
  have hb : h.bar (h.bar c) ≠ h.bar c := by
    rw [h.bar_bar]
    exact Ne.symm hc
  exact ne_inv_of_bar_ne (h := h) hb

theorem inv_bar_ne_inv {c : F} (hc : h.bar c ≠ c) : (h.bar c)⁻¹ ≠ c⁻¹ := by
  intro hEq
  exact hc (inv_injective hEq)

end CFSG.StandardType.SuSplitRootGen
