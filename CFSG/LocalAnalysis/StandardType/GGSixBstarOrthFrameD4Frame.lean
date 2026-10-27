module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankOmega
public import CFSG.LocalAnalysis.StandardType.GGSixBstarOrthFrameD4Form
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDFour

public section

namespace CFSG.StandardType

namespace OrthD4

open Module Multiplicative CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.StandardType.D4Rank CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Supp

variable {r : ℕ}

@[expose] def supp (s : Fin r → ZMod 3) : Finset (Fin r) := Finset.univ.filter fun i => s i ≠ 0

theorem mem_supp {s : Fin r → ZMod 3} {i : Fin r} : i ∈ supp s ↔ s i ≠ 0 := by
  simp [supp]

theorem suppLE_iff_subset {s s' : Fin r → ZMod 3} : SuppLE s s' ↔ supp s ⊆ supp s' := by
  simp only [SuppLE, Finset.subset_iff, mem_supp]

theorem supp_update_zero (s : Fin r → ZMod 3) (i : Fin r) :
    supp (Function.update s i 0) = (supp s).erase i := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp [mem_supp]
  · simp [mem_supp, hj]

theorem supp_update_one (s : Fin r → ZMod 3) (i : Fin r) :
    supp (Function.update s i 1) = insert i (supp s) := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp [mem_supp]
  · simp [mem_supp, hj]

theorem supp_one : supp (fun _ : Fin r => (1 : ZMod 3)) = Finset.univ := by
  ext i
  simp [mem_supp]

end Supp

section Count

variable {r : ℕ}

theorem count_bounds (d : (Fin r → ZMod 3) → ℕ) (hle : ∀ s, d s ≤ 8)
    (hlt : ∀ s s', SuppLE s s' → ¬ SuppLE s' s → d s' + 2 ≤ d s) (s : Fin r → ZMod 3) :
    d s + 2 * (supp s).card ≤ 8 ∧ 2 * (r - (supp s).card) ≤ d s := by
  classical
  constructor
  ·
    suffices h : ∀ m, ∀ s : Fin r → ZMod 3, (supp s).card = m → d s + 2 * m ≤ 8 from h _ s rfl
    intro m
    induction m with
    | zero => intro s _; simpa using hle s
    | succ m ih =>
      intro s hs
      obtain ⟨i, hi⟩ : (supp s).Nonempty := Finset.card_pos.mp (by omega)
      have hcard : (supp (Function.update s i 0)).card = m := by
        rw [supp_update_zero, Finset.card_erase_of_mem hi, hs, Nat.add_sub_cancel]
      have h1 := ih _ hcard
      have h2 := hlt (Function.update s i 0) s
        (suppLE_iff_subset.mpr (by rw [supp_update_zero]; exact Finset.erase_subset _ _))
        (fun h => by
          have := suppLE_iff_subset.mp h hi
          rw [supp_update_zero] at this
          exact (Finset.notMem_erase i _) this)
      omega
  ·
    suffices h : ∀ m, ∀ s : Fin r → ZMod 3, r - (supp s).card = m → 2 * m ≤ d s from h _ s rfl
    intro m
    induction m with
    | zero => intro s _; omega
    | succ m ih =>
      intro s hs
      have hlt' : (supp s).card < r := by omega
      obtain ⟨i, hi⟩ : ∃ i, i ∉ supp s := by
        by_contra hcon
        push Not at hcon
        have : supp s = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon
        rw [this, Finset.card_univ, Fintype.card_fin] at hlt'
        omega
      have hcard : (supp (Function.update s i 1)).card = (supp s).card + 1 := by
        rw [supp_update_one, Finset.card_insert_of_notMem hi]
      have h1 := ih _ (by rw [hcard]; omega)
      have hmem : i ∈ supp (Function.update s i 1) := by
        rw [supp_update_one]
        exact Finset.mem_insert_self _ _
      have h2 := hlt s (Function.update s i 1)
        (suppLE_iff_subset.mpr (by rw [supp_update_one]; exact Finset.subset_insert _ _))
        (fun h => hi (suppLE_iff_subset.mp h hmem))
      omega

theorem count_eq (d : (Fin r → ZMod 3) → ℕ) (hle : ∀ s, d s ≤ 8)
    (hlt : ∀ s s', SuppLE s s' → ¬ SuppLE s' s → d s' + 2 ≤ d s) :
    r ≤ 4 ∧ (4 ≤ r → ∀ s, d s + 2 * (supp s).card = 8) := by
  have h1 := (count_bounds d hle hlt fun _ => 1).1
  rw [supp_one, Finset.card_univ, Fintype.card_fin] at h1
  refine ⟨by omega, fun hr s => ?_⟩
  have h2 := count_bounds d hle hlt s
  omega

end Count

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]

theorem exists_orthFrame {Bs : Subgroup G} (hBs : CFSG.Assembly.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h81 : 3 ^ 4 ≤ Nat.card Bs) (φ : Om8 K →* G) (hφ : Function.Injective φ)
    (hBφ : Bs ≤ φ.range) :
    ∃ ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K, Function.Injective (φ.comp ι₁) ∧
      (φ.comp ι₁).range = Bs ∧
      ∀ s : Fin 4 → ZMod 3, (omFixDim (ι₁ (ofAdd s)) = 0 ∨ omFixDim (ι₁ (ofAdd s)) = 6) ↔
        ∑ i, s i ^ 2 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hA := genMax_of_orth hnd hT Nat.prime_three (by norm_num) hBs hSC φ hφ hBφ
  obtain ⟨r, ι₀, hinj₀, hrange₀, hsupp₀⟩ := exists_genPieceFrame hA
  have hι₀A : ∀ s, ι₀ s ∈ (Bs.comap φ).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
    fun s => hrange₀ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hι₀Γ : ∀ s, ι₀ s ∈ matrixDerived (coordinateQuadPlus 4 K) := fun s => hA.le (hι₀A s)
  set ι₁ : Multiplicative (Fin r → ZMod 3) →* Om8 K := ι₀.codRestrict _ hι₀Γ with hι₁def
  have hι₁ : ∀ s, ((ι₁ s : Om8 K) : GL (Fin (2 * 4)) K) = ι₀ s := fun s => rfl
  have hinj : Function.Injective (φ.comp ι₁) := fun s t hst =>
    hinj₀ (by rw [← hι₁, ← hι₁, hφ hst])
  have hrange : (φ.comp ι₁).range = Bs := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨Y, hY, hYs⟩ := hι₀A s
      have hYι : Y = ι₁ s := Subtype.ext hYs
      rw [MonoidHom.comp_apply, ← hYι]
      exact hY
    · intro hb
      obtain ⟨Y, rfl⟩ := hBφ hb
      have hYA : (Y : GL (Fin (2 * 4)) K) ∈ ι₀.range := by rw [hrange₀]; exact ⟨Y, hb, rfl⟩
      obtain ⟨s, hs⟩ := hYA
      exact ⟨s, by rw [MonoidHom.comp_apply]; exact congrArg φ (Subtype.ext hs)⟩
  have hr4 : 4 ≤ r := by
    have hcard : Nat.card Bs = 3 ^ r := by
      rw [← hrange]
      exact NoOffUO.card_range_eq hinj
    rw [hcard] at h81
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h81
  set d : (Fin r → ZMod 3) → ℕ := fun s => omFixDim (ι₁ (ofAdd s)) with hd
  have hker : ∀ s v, v ∈ LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ↔
      glin (ι₀ (ofAdd s)) v = v := by
    intro s v
    rw [mem_ker_omRep_sub_one, glin_apply, hι₁]
  have hle8 : ∀ s, d s ≤ 8 := fun s => by
    have := Submodule.finrank_le (LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1))
    rwa [Module.finrank_fin_fun] at this
  have h3 : ∀ s, ι₁ s ^ 3 = 1 := fun s => Subtype.ext (by
    rw [SubgroupClass.coe_pow, hι₁, OneMemClass.coe_one]
    exact hA.pow _ (hι₀A s))
  have heven : ∀ s, Even (d s) := fun s => omFixDim_even _ (h3 _)
  have hlt : ∀ s s', SuppLE s s' → ¬ SuppLE s' s → d s' + 2 ≤ d s := by
    intro s s' h1 h2
    have hle : LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) ≤
        LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) := by
      intro v hv
      rw [hker] at hv ⊢
      exact (hsupp₀ s s').mpr h1 v hv
    have hne : ¬ LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ≤
        LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) := by
      intro h
      apply h2
      refine (hsupp₀ s' s).mp fun v hv => ?_
      rw [← hker] at hv ⊢
      exact h hv
    have hlt' : d s' < d s := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hne)
    obtain ⟨a, ha⟩ := heven s
    obtain ⟨b, hb⟩ := heven s'
    omega
  obtain ⟨hr, hcount⟩ := count_eq d hle8 hlt
  obtain rfl : r = 4 := le_antisymm hr hr4
  refine ⟨ι₁, hinj, hrange, fun s => ?_⟩
  rw [sum_sq_eq_one_iff]
  have h := hcount le_rfl s
  change d s = 0 ∨ d s = 6 ↔ _
  simp only [supp] at h
  omega

end Frame

end OrthD4

end CFSG.StandardType
