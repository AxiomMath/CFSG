module

public import CFSG.LieType.Steinberg.Classical.Symplectic
public import CFSG.LieType.Chevalley.RootOps.All
public import CFSG.LieType.Steinberg.Adjoint.ChevExtras
public import CFSG.LieType.Steinberg.Adjoint.ExtraPairs

public section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
open TauCeti.GLSymplecticFin Matrix

@[expose] def c3ToF4 : (Fin 3 → ℤ) →+ (Fin (Tag.rank .F4) → ℤ) where
  toFun v := (![0, v 2, v 1, v 0] : Fin 4 → ℤ)
  map_zero' := by
    funext i
    fin_cases i <;> rfl
  map_add' v w := by
    funext i
    fin_cases i <;> rfl

@[expose] def c3Node (k : Fin 3) : Fin (Tag.rank .F4) := (![3, 2, 1] : Fin 3 → Fin 4) k

theorem c3ToF4_apply (v : Fin 3 → ℤ) : c3ToF4 v = (![0, v 2, v 1, v 0] : Fin 4 → ℤ) := rfl

theorem c3ToF4_apply_zero (v : Fin 3 → ℤ) : c3ToF4 v ⟨0, by decide⟩ = 0 := rfl

theorem c3ToF4_apply_c3Node (v : Fin 3 → ℤ) (k : Fin 3) : c3ToF4 v (c3Node k) = v k := by
  fin_cases k <;> rfl

theorem c3ToF4_injective : Function.Injective c3ToF4 := fun v w h => funext fun k => by
  rw [← c3ToF4_apply_c3Node v k, ← c3ToF4_apply_c3Node w k, h]

theorem c3ToF4_single (k : Fin 3) : c3ToF4 (Pi.single k 1) = Pi.single (c3Node k) 1 := by
  fin_cases k <;> decide

theorem c3ToF4_reflection (k : Fin 3) (v : Fin 3 → ℤ) :
    c3ToF4 (reflection (cartanC 3) k v) = reflect .F4 (c3Node k) (c3ToF4 v) := by
  rw [← Chevalley.reflection_cartan]
  have key : c3ToF4.comp (reflection (cartanC 3) k).toAddMonoidHom =
      (reflection (Tag.cartan .F4) (c3Node k)).toAddMonoidHom.comp c3ToF4 := by
    refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_zsmul]
    congr 1
    rw [reflection_apply, reflection_apply]
    fin_cases k <;> fin_cases j <;> decide
  exact DFunLike.congr_fun key v

theorem isRoot_c3ToF4 {v : Fin 3 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 3) ∅) :
    IsRoot .F4 (c3ToF4 v) := by
  rcases hv with ⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩
  · obtain ⟨ω, rfl⟩ :=
      (coxeterMatrix (isFiniteType_cartanC 3)).toCoxeterSystem.wordProd_surjective w
    induction ω with
    | nil =>
      simpa [c3ToF4_single] using IsRoot.basis (τ := .F4) (c3Node j)
    | cons k ω ih =>
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
        c3ToF4_reflection]
      exact IsRoot.reflect _ ih
  · exact absurd hj (Set.notMem_empty j)

@[expose] def c3Roots : List (Fin 3 → ℤ) :=
  [![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, 1, 1], ![1, 1, 1], ![0, 2, 1],
    ![1, 2, 1], ![2, 2, 1], ![-1, 0, 0], ![0, -1, 0], ![0, 0, -1], ![-1, -1, 0], ![0, -1, -1],
    ![-1, -1, -1], ![0, -2, -1], ![-1, -2, -1], ![-2, -2, -1]]

@[expose] def rsi3 : List (RootSubgroupIndex 3) :=
  [.positiveLong 0, .positiveLong 1, .positiveLong 2, .negativeLong 0, .negativeLong 1,
    .negativeLong 2, .difference 0 1 (by decide), .difference 0 2 (by decide),
    .difference 1 0 (by decide), .difference 1 2 (by decide), .difference 2 0 (by decide),
    .difference 2 1 (by decide), .positiveSum 0 1 (by decide), .positiveSum 0 2 (by decide),
    .positiveSum 1 2 (by decide), .negativeSum 0 1 (by decide), .negativeSum 0 2 (by decide),
    .negativeSum 1 2 (by decide)]

theorem mem_rsi3 (r : RootSubgroupIndex 3) : r ∈ rsi3 := by
  cases r with
  | positiveLong i => fin_cases i <;> simp [rsi3]
  | negativeLong i => fin_cases i <;> simp [rsi3]
  | difference i j h =>
    fin_cases i <;> fin_cases j <;> first | exact absurd h (by decide) | simp [rsi3]
  | positiveSum i j h =>
    fin_cases i <;> fin_cases j <;> first | exact absurd h (by decide) | simp [rsi3]
  | negativeSum i j h =>
    fin_cases i <;> fin_cases j <;> first | exact absurd h (by decide) | simp [rsi3]

theorem c3Roots_check : ∀ v ∈ c3Roots, ∃ r ∈ rsi3, stdVec r = toStd 3 v := by
  decide

theorem f4Roots_check : ∀ u ∈ rootFinset .F4, u ⟨0, by decide⟩ = 0 →
    ∃ v ∈ c3Roots, c3ToF4 v = u := by
  decide

theorem mem_roots_of_mem_c3Roots {v : Fin 3 → ℤ} (hv : v ∈ c3Roots) :
    v ∈ roots (isFiniteType_cartanC 3) ∅ := by
  obtain ⟨r, -, hr⟩ := c3Roots_check v hv
  exact mem_roots_of_stdVec hr

theorem mem_c3Roots_of_isRoot {v : Fin 3 → ℤ} (hv : IsRoot .F4 (c3ToF4 v)) : v ∈ c3Roots := by
  obtain ⟨w, hw, he⟩ := f4Roots_check _ (mem_rootFinset.2 hv) (c3ToF4_apply_zero v)
  rwa [← c3ToF4_injective he]

theorem isRoot_c3ToF4_iff {v : Fin 3 → ℤ} :
    IsRoot .F4 (c3ToF4 v) ↔ v ∈ roots (isFiniteType_cartanC 3) ∅ :=
  ⟨fun h => mem_roots_of_mem_c3Roots (mem_c3Roots_of_isRoot h), isRoot_c3ToF4⟩

theorem mem_roots_iff_mem_c3Roots {v : Fin 3 → ℤ} :
    v ∈ roots (isFiniteType_cartanC 3) ∅ ↔ v ∈ c3Roots :=
  ⟨fun h => mem_c3Roots_of_isRoot (isRoot_c3ToF4 h), mem_roots_of_mem_c3Roots⟩

theorem c3Roots_sub_check : ∀ α ∈ c3Roots, ∀ β ∈ c3Roots, α + β ∈ c3Roots →
    (β - α ∈ c3Roots ↔ toStd 3 (α + β) ⬝ᵥ toStd 3 (α + β) = 4) := by
  decide

theorem sub_mem_roots_iff {α β : Fin 3 → ℤ} (hα : α ∈ roots (isFiniteType_cartanC 3) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hr : α + β ∈ roots (isFiniteType_cartanC 3) ∅) :
    β - α ∈ roots (isFiniteType_cartanC 3) ∅ ↔ toStd 3 (α + β) ⬝ᵥ toStd 3 (α + β) = 4 := by
  rw [mem_roots_iff_mem_c3Roots] at hα hβ hr ⊢
  exact c3Roots_sub_check α hα β hβ hr

theorem eq_one_of_nsmul_mem_roots {α : Fin 3 → ℤ} {k : ℕ}
    (h : k • α ∈ roots (isFiniteType_cartanC 3) ∅) : k = 1 := by
  rw [← isRoot_c3ToF4_iff, map_nsmul] at h
  exact Steinberg.Adjoint.eq_one_of_isRoot_nsmul h

open Steinberg.Sp in
theorem long_check : ∀ r ∈ rsi3, ∀ s ∈ rsi3, ∀ t ∈ rsi3, stdVec t = stdVec r + stdVec s →
    stdVec t ⬝ᵥ stdVec t = 4 → ((Ez r * Ez s - Ez s * Ez r) (pos1 t).1 (pos1 t).2).natAbs = 2 := by
  decide

open Steinberg.Sp in
theorem natAbs_commC_one_one_long {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hαβ : α + β ≠ 0) (hr : α + β ∈ roots (isFiniteType_cartanC 3) ∅)
    (h4 : toStd 3 (α + β) ⬝ᵥ toStd 3 (α + β) = 4) : (commC α β (1, 1)).natAbs = 2 := by
  obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
  rw [commC_one_one hαβ, Exz_eq hr', Exz_eq hs, entryAt_eq _ ht]
  refine long_check r (mem_rsi3 r) s (mem_rsi3 s) t (mem_rsi3 t) ?_ (by rw [ht]; exact h4)
  rw [ht, toStd_add', hr', hs]

open Steinberg.Sp in
theorem natAbs_commC_two_one {n : ℕ} {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC n) ∅) (hβ : β ∈ roots (isFiniteType_cartanC n) ∅)
    (hαβ : α + β ≠ 0) (hr : 2 • α + β ∈ roots (isFiniteType_cartanC n) ∅) :
    (commC α β (2, 1)).natAbs = 1 := by
  obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
  rw [commC_two_one hαβ, Exz_eq hr', Exz_eq hs, entryAt_eq _ ht, Matrix.neg_apply,
    Int.natAbs_neg]
  refine coeff21_spec (r := r) (s := s) (ht.trans (by rw [toStd_add', toStd_nsmul', hr', hs])) ?_
  rw [hr', hs]
  exact toStd_add_ne_zero hαβ

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem intCast_eq_one_of_natAbs {z : ℤ} (h : z.natAbs = 1) : (z : K) = 1 := by
  rcases Int.natAbs_eq_iff.1 h with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

theorem intCast_eq_zero_of_natAbs {z : ℤ} (h : z.natAbs = 2) : (z : K) = 0 := by
  rcases Int.natAbs_eq_iff.1 h with h | h <;> rw [h]
  · simpa using CharTwo.two_eq_zero
  · simpa using CharTwo.two_eq_zero

open Steinberg.Adjoint CFSG.LieType.Chevalley in
theorem cast_commC_eq {α β : Fin 3 → ℤ} (hα : α ∈ roots (isFiniteType_cartanC 3) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅) (hne : α ≠ β) (hαβ : α + β ≠ 0)
    {p : ℕ × ℕ} (hp : p ∈ pairs₀) (hr : p.1 • α + p.2 • β ∈ roots (isFiniteType_cartanC 3) ∅) :
    (Steinberg.Sp.commC α β p : K) =
      (Steinberg.Adjoint.commC (rootOperatorFamily .F4) f4Data_valid (c3ToF4 α) (c3ToF4 β) p :
        K) := by
  have hα' := isRoot_c3ToF4 hα
  have hβ' := isRoot_c3ToF4 hβ
  have hsum : c3ToF4 α + c3ToF4 β ≠ 0 := by
    rw [← map_add, ← map_zero c3ToF4]
    exact fun h => hαβ (c3ToF4_injective h)
  have hne' : c3ToF4 α ≠ c3ToF4 β := fun h => hne (c3ToF4_injective h)
  have hne'' : c3ToF4 α ≠ -c3ToF4 β := fun h => hsum (by rw [h, neg_add_cancel])
  simp only [pairs₀, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp only [one_smul] at hr
    rw [commC_11 hα' hβ' hsum, RootOperatorFamily'.coeff11]
    have hr' : IsRoot .F4 (c3ToF4 α + c3ToF4 β) := by
      rw [← map_add]
      exact isRoot_c3ToF4 hr
    have hn := RootOperatorFamily'.bracketCoeff_natAbs (rootOperatorFamily .F4) f4Data_valid
      (β := ⟨c3ToF4 α, hα'⟩) (γ := ⟨c3ToF4 β, hβ'⟩)
      (fun h => hsum (by change c3ToF4 β = -c3ToF4 α at h; rw [h, add_neg_cancel])) hr'
    by_cases hd : β - α ∈ roots (isFiniteType_cartanC 3) ∅
    · have h4 := (sub_mem_roots_iff hα hβ hr).1 hd
      have hd' : IsRoot .F4 (c3ToF4 β - c3ToF4 α) := by
        rw [← map_sub]
        exact isRoot_c3ToF4 hd
      rw [intCast_eq_zero_of_natAbs (natAbs_commC_one_one_long hα hβ hαβ hr h4),
        intCast_eq_zero_of_natAbs (hn.trans (stringNorm_of_isRoot hd'))]
    · have h2 : toStd 3 (α + β) ⬝ᵥ toStd 3 (α + β) = 2 := by
        obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
        rcases dot_stdVec t with h | h
        · rwa [ht] at h
        · exact absurd ((sub_mem_roots_iff hα hβ hr).2 (by rwa [ht] at h)) hd
      have hd' : ¬IsRoot .F4 (c3ToF4 β - c3ToF4 α) := by
        rw [← map_sub, isRoot_c3ToF4_iff]
        exact hd
      rw [intCast_eq_one_of_natAbs (Steinberg.Sp.natAbs_commC_one_one hα hβ hαβ hr h2),
        intCast_eq_one_of_natAbs (hn.trans (stringNorm_of_not_isRoot hd'))]
  · have hr' : IsRoot .F4 (c3ToF4 α + 2 • c3ToF4 β) := by
      rw [← map_nsmul, ← map_add]
      simpa only [one_smul] using isRoot_c3ToF4 hr
    rw [commC_12 hα' hβ' hsum, intCast_eq_one_of_natAbs
      (natAbs_coeff12 (rootOperatorFamily .F4) f4Data_valid noG2_F4 (α := ⟨_, hα'⟩)
        (β := ⟨_, hβ'⟩) hne' hne'' hr'),
      intCast_eq_one_of_natAbs (Steinberg.Sp.natAbs_commC_one_two hα hβ hαβ
        (by simpa only [one_smul] using hr))]
  · have hr' : IsRoot .F4 (2 • c3ToF4 α + c3ToF4 β) := by
      rw [← map_nsmul, ← map_add]
      simpa only [one_smul] using isRoot_c3ToF4 hr
    rw [commC_21 hα' hβ' hsum, intCast_eq_one_of_natAbs
      (natAbs_coeff21 (rootOperatorFamily .F4) f4Data_valid noG2_F4 (α := ⟨_, hα'⟩)
        (β := ⟨_, hβ'⟩) hne' hne'' hr'),
      intCast_eq_one_of_natAbs (natAbs_commC_two_one hα hβ hαβ
        (by simpa only [one_smul] using hr))]

end CharTwo

end CFSG.Timmesfeld.LieEmbed
