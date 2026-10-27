module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAAux
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCoord

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_smDual_apply {m : ℕ} (w v : SMV m) : smDual w v = smDot w v := by
  simp [smDual, smDot, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem hdRo7SmAAux_smDot_sub {m : ℕ} (w w' v : SMV m) :
    smDot (w - w') v = smDot w v - smDot w' v := by
  simp only [smDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem hdRo7SmAAux_smDot_single {m : ℕ} (a : Fin m) (v : SMV m) :
    smDot (Pi.single a (1 : ZMod 3)) v = v a := by
  rw [smDot, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro ha; exact absurd (Finset.mem_univ a) ha

theorem hdRo7SmAAux_smDual_diff {m : ℕ} (a b : Fin m) (v : SMV m) :
    smDual (Pi.single a (1 : ZMod 3) - Pi.single b 1) v = v a - v b := by
  rw [hdRo7SmAAux_smDual_apply, hdRo7SmAAux_smDot_sub, hdRo7SmAAux_smDot_single,
    hdRo7SmAAux_smDot_single]

@[expose] noncomputable def hdRo7SmAAux_permLin (m : ℕ) : Equiv.Perm (Fin m) →* SMGL m where
  toFun σ := LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) σ.symm
  map_one' := by ext v i; rfl
  map_mul' σ τ := by ext v i; rfl

theorem hdRo7SmAAux_permLin_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (v : SMV m) (i : Fin m) :
    (hdRo7SmAAux_permLin m σ v) i = v (σ.symm i) := rfl

theorem hdRo7SmAAux_permLin_injective (m : ℕ) :
    Function.Injective (hdRo7SmAAux_permLin m) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have h1 := congrFun (congrArg
    (fun (f : SMGL m) => f (Pi.single i (1 : ZMod 3) : SMV m)) h) (σ i)
  have h2 : (hdRo7SmAAux_permLin m σ (Pi.single i (1 : ZMod 3) : SMV m)) (σ i) = 1 := by
    rw [hdRo7SmAAux_permLin_apply, Equiv.symm_apply_apply, Pi.single_eq_same]
  rw [h2] at h1
  have h3 : (Pi.single i (1 : ZMod 3) : SMV m) (τ.symm (σ i)) = 1 := by
    rw [hdRo7SmAAux_permLin_apply] at h1
    exact h1.symm
  have h4 : τ.symm (σ i) = i := by
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h3
    exact (by decide : (0 : ZMod 3) ≠ 1) h3
  exact (Equiv.symm_apply_eq τ).mp h4

theorem hdRo7SmAAux_isPerm_permLin {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    SMIsPerm (hdRo7SmAAux_permLin m σ) :=
  ⟨σ, fun v i => hdRo7SmAAux_permLin_apply σ v i⟩

theorem hdRo7SmAAux_range_permLin (m : ℕ) :
    (hdRo7SmAAux_permLin m).range = smGroup m [] := by
  rw [smGroup]
  have hset : ({g : SMGL m | SMIsPerm g}) = (hdRo7SmAAux_permLin m).range := by
    ext g
    constructor
    · rintro ⟨σ, hσ⟩
      exact ⟨σ, by ext v i; rw [hdRo7SmAAux_permLin_apply, hσ]⟩
    · rintro ⟨σ, rfl⟩
      exact hdRo7SmAAux_isPerm_permLin σ
  have hemp : {r : SMGL m | ∃ q ∈ ([] : List (SMV m × SMV m)),
      SMRefl r q.1 (smDual q.2)} = ∅ := by
    ext r; simp
  rw [hset, hemp, Set.union_empty, Subgroup.closure_eq]

theorem hdRo7SmAAux_permLin_swap_isRefl (n : ℕ) (k : Fin n) :
    GGLinRefl (hdRo7SmAAux_permLin (n + 1) (Equiv.swap k.castSucc k.succ)) := by
  refine hdRo7SmAAux_isRefl_of_smRefl
    (u := Pi.single k.castSucc (1 : ZMod 3) - Pi.single k.succ 1)
    (φ := smDual (Pi.single k.castSucc (1 : ZMod 3) - Pi.single k.succ 1)) ?_
  refine ⟨?_, ?_⟩
  · rw [hdRo7SmAAux_smDual_diff]
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne
      (Fin.castSucc_lt_succ (i := k)).ne, Pi.single_eq_of_ne
      (Fin.castSucc_lt_succ (i := k)).ne.symm]
    norm_num
  · intro v
    ext i
    rw [hdRo7SmAAux_permLin_apply, Equiv.symm_swap, hdRo7SmAAux_smDual_diff]
    by_cases h1 : i = k.castSucc
    · subst h1
      rw [Equiv.swap_apply_left]
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_eq_same,
        Pi.single_eq_of_ne (Fin.castSucc_lt_succ (i := k)).ne]
      ring
    · by_cases h2 : i = k.succ
      · subst h2
        rw [Equiv.swap_apply_right]
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
          Pi.single_eq_of_ne (Fin.castSucc_lt_succ (i := k)).ne.symm, Pi.single_eq_same]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
          Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
        ring

theorem hdRo7SmAAux_linWeyl_perm (n : ℕ) (hn : 1 ≤ n) :
    ZS.LinWeyl 3 (smGroup (n + 1) []) := by
  rw [← hdRo7SmAAux_range_permLin (n + 1)]
  refine hdRo7SmAAux_linWeyl_of_perm _ n hn ?_ ?_
  · refine MulEquiv.ofBijective
      ((hdRo7SmAAux_permLin (n + 1)).codRestrict (hdRo7SmAAux_permLin (n + 1)).range
        (fun σ => MonoidHom.mem_range.mpr ⟨σ, rfl⟩)) ?_
    constructor
    · intro a b h
      exact hdRo7SmAAux_permLin_injective (n + 1) (Subtype.ext_iff.mp h)
    · rintro ⟨g, hg⟩
      obtain ⟨σ, hσ⟩ := hg
      exact ⟨σ, Subtype.ext hσ⟩
  · intro k
    change GGLinRefl ((hdRo7SmAAux_permLin (n + 1)) (Equiv.swap k.castSucc k.succ))
    exact hdRo7SmAAux_permLin_swap_isRefl n k

theorem hdRo7SmAAux_case1 : ZS.LinWeyl 3 (smGroup 7 []) :=
  hdRo7SmAAux_linWeyl_perm 6 (by norm_num)

theorem hdRo7SmAAux_case2 : ZS.LinWeyl 3 (smGroup 8 []) :=
  hdRo7SmAAux_linWeyl_perm 7 (by norm_num)

@[expose] noncomputable def hdRo7SmAAux_ext9 : SMV 8 →ₗ[ZMod 3] (Fin 9 → ZMod 3) where
  toFun v := fun j => if h : j.val < 8 then v ⟨j.val, h⟩ else 0
  map_add' := by intro a b; ext j; by_cases h : j.val < 8 <;> simp [h]
  map_smul' := by intro c v; ext j; by_cases h : j.val < 8 <;> simp [h]

@[expose] noncomputable def hdRo7SmAAux_proj9 : (Fin 9 → ZMod 3) →ₗ[ZMod 3] SMV 8 where
  toFun V := fun i => V (Fin.castSucc i) - V (Fin.last 8)
  map_add' := by intro a b; ext i; simp only [Pi.add_apply]; ring
  map_smul' := by intro c v; ext i; simp only [Pi.smul_apply, map_sub, RingHom.id_apply]; module

theorem hdRo7SmAAux_proj9_ext9 (v : SMV 8) : hdRo7SmAAux_proj9 (hdRo7SmAAux_ext9 v) = v := by
  ext i; simp [hdRo7SmAAux_proj9, hdRo7SmAAux_ext9]

theorem hdRo7SmAAux_ext9_proj9 (V : Fin 9 → ZMod 3) :
    hdRo7SmAAux_ext9 (hdRo7SmAAux_proj9 V) = V - V (Fin.last 8) • (1 : Fin 9 → ZMod 3) := by
  ext j
  by_cases h : j.val < 8
  · simp [hdRo7SmAAux_ext9, hdRo7SmAAux_proj9, h]
  · have hj : j = Fin.last 8 := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hj
    simp [hdRo7SmAAux_ext9, hdRo7SmAAux_proj9]

theorem hdRo7SmAAux_coordPerm_ones (σ : Equiv.Perm (Fin 9)) :
    coordPerm 3 8 σ (1 : Fin 9 → ZMod 3) = 1 := by
  ext j; simp [coordPerm_apply]

theorem hdRo7SmAAux_proj9_ones : hdRo7SmAAux_proj9 (1 : Fin 9 → ZMod 3) = 0 := by
  ext i; simp [hdRo7SmAAux_proj9]

theorem hdRo7SmAAux_proj9_T_ext9_proj9 (σ : Equiv.Perm (Fin 9)) (V : Fin 9 → ZMod 3) :
    hdRo7SmAAux_proj9 (coordPerm 3 8 σ (hdRo7SmAAux_ext9 (hdRo7SmAAux_proj9 V))) =
      hdRo7SmAAux_proj9 (coordPerm 3 8 σ V) := by
  have h2 : coordPerm 3 8 σ (hdRo7SmAAux_ext9 (hdRo7SmAAux_proj9 V))
      = coordPerm 3 8 σ V
        - V (Fin.last 8) • coordPerm 3 8 σ (1 : Fin 9 → ZMod 3) := by
    rw [hdRo7SmAAux_ext9_proj9]
    rw [map_sub, map_smul]
  rw [h2, hdRo7SmAAux_coordPerm_ones]
  rw [map_sub hdRo7SmAAux_proj9, map_smul hdRo7SmAAux_proj9, hdRo7SmAAux_proj9_ones,
    smul_zero]
  exact sub_zero _

@[expose] noncomputable def hdRo7SmAAux_q9 (σ : Equiv.Perm (Fin 9)) : SMGL 8 where
  toFun v := hdRo7SmAAux_proj9 (coordPerm 3 8 σ (hdRo7SmAAux_ext9 v))
  invFun v := hdRo7SmAAux_proj9 (coordPerm 3 8 σ⁻¹ (hdRo7SmAAux_ext9 v))
  map_add' := by intro a b; simp only [map_add]
  map_smul' := by intro c v; simp only [map_smul, RingHom.id_apply]
  left_inv := by
    intro v
    calc hdRo7SmAAux_proj9 (coordPerm 3 8 σ⁻¹
            (hdRo7SmAAux_ext9 (hdRo7SmAAux_proj9 (coordPerm 3 8 σ (hdRo7SmAAux_ext9 v)))))
        = hdRo7SmAAux_proj9 (coordPerm 3 8 σ⁻¹
            (coordPerm 3 8 σ (hdRo7SmAAux_ext9 v))) := by
          rw [hdRo7SmAAux_proj9_T_ext9_proj9]
      _ = hdRo7SmAAux_proj9 (coordPerm 3 8 (σ⁻¹ * σ) (hdRo7SmAAux_ext9 v)) := by
          simp [map_mul]
      _ = hdRo7SmAAux_proj9 (hdRo7SmAAux_ext9 v) := by simp
      _ = v := hdRo7SmAAux_proj9_ext9 v
  right_inv := by
    intro v
    calc hdRo7SmAAux_proj9 (coordPerm 3 8 σ
            (hdRo7SmAAux_ext9 (hdRo7SmAAux_proj9 (coordPerm 3 8 σ⁻¹ (hdRo7SmAAux_ext9 v)))))
        = hdRo7SmAAux_proj9 (coordPerm 3 8 σ
            (coordPerm 3 8 σ⁻¹ (hdRo7SmAAux_ext9 v))) := by
          rw [hdRo7SmAAux_proj9_T_ext9_proj9]
      _ = hdRo7SmAAux_proj9 (coordPerm 3 8 (σ * σ⁻¹) (hdRo7SmAAux_ext9 v)) := by
          simp [map_mul]
      _ = hdRo7SmAAux_proj9 (hdRo7SmAAux_ext9 v) := by simp
      _ = v := hdRo7SmAAux_proj9_ext9 v

@[expose] noncomputable def hdRo7SmAAux_q9Hom : Equiv.Perm (Fin 9) →* SMGL 8 where
  toFun := hdRo7SmAAux_q9
  map_one' := by
    ext v i
    simp [hdRo7SmAAux_q9, coordPerm_apply, hdRo7SmAAux_ext9, hdRo7SmAAux_proj9]
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    change hdRo7SmAAux_proj9 (coordPerm 3 8 (σ * τ) (hdRo7SmAAux_ext9 v)) =
      hdRo7SmAAux_proj9 (coordPerm 3 8 σ
        (hdRo7SmAAux_ext9 (hdRo7SmAAux_proj9 (coordPerm 3 8 τ (hdRo7SmAAux_ext9 v)))))
    rw [hdRo7SmAAux_proj9_T_ext9_proj9 σ (coordPerm 3 8 τ (hdRo7SmAAux_ext9 v))]
    rw [map_mul]
    rfl

theorem hdRo7SmAAux_proj9_single_castSucc (m : Fin 8) (c : ZMod 3) :
    hdRo7SmAAux_proj9 (Pi.single (Fin.castSucc m) c) = Pi.single m c := by
  ext k
  fin_cases k <;> fin_cases m <;> simp [hdRo7SmAAux_proj9]

theorem hdRo7SmAAux_proj9_single_last (c : ZMod 3) :
    hdRo7SmAAux_proj9 (Pi.single (Fin.last 8) c) = - (c • (1 : SMV 8)) := by
  ext k
  fin_cases k <;> simp [hdRo7SmAAux_proj9, smul_eq_mul] <;> ring

theorem hdRo7SmAAux_ext9_single (i : Fin 8) (c : ZMod 3) :
    hdRo7SmAAux_ext9 (Pi.single i c) = Pi.single (Fin.castSucc i) c := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [hdRo7SmAAux_ext9]

theorem hdRo7SmAAux_q9Hom_injective : Function.Injective hdRo7SmAAux_q9Hom := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ i : Fin 8, σ (Fin.castSucc i) = Fin.castSucc i := by
    intro i
    have hv : hdRo7SmAAux_proj9 (Pi.single (σ (Fin.castSucc i)) (1 : ZMod 3))
        = Pi.single i (1 : ZMod 3) := by
      have h1 : hdRo7SmAAux_q9Hom σ (Pi.single i (1 : ZMod 3)) = Pi.single i 1 := by
        rw [hσ]; rfl
      change hdRo7SmAAux_proj9 (coordPerm 3 8 σ (hdRo7SmAAux_ext9 (Pi.single i 1)))
        = Pi.single i 1 at h1
      rw [hdRo7SmAAux_ext9_single, coordPerm_single] at h1
      exact h1
    rcases Fin.eq_castSucc_or_eq_last (σ (Fin.castSucc i)) with ⟨m, hm⟩ | hlast
    · rw [hm, hdRo7SmAAux_proj9_single_castSucc] at hv
      have hmi : m = i := by
        by_contra hne
        have hm2 := congrFun hv m
        simp_all [Pi.single_eq_same, Pi.single_eq_of_ne]
      rw [hm, hmi]
    · rw [hlast, hdRo7SmAAux_proj9_single_last] at hv
      have hc := congrFun hv i
      simp only [Pi.neg_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Pi.single_eq_same] at hc
      exact absurd hc (by decide : ¬ ((-1 : ZMod 3) = 1))
  apply Equiv.ext
  intro j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · exact hfix i
  · rcases Fin.eq_castSucc_or_eq_last (σ (Fin.last 8)) with ⟨m, hm⟩ | hlast
    · exfalso
      have h1 : σ (Fin.castSucc m) = σ (Fin.last 8) := by rw [hfix m, hm]
      have h2 : Fin.castSucc m = Fin.last 8 := σ.injective h1
      exact (Fin.castSucc_ne_last m) h2
    · exact hlast

@[simp] theorem hdRo7SmAAux_proj9_apply (V : Fin 9 → ZMod 3) (i : Fin 8) :
    hdRo7SmAAux_proj9 V i = V (Fin.castSucc i) - V (Fin.last 8) := rfl

@[simp] theorem hdRo7SmAAux_ext9_apply (v : SMV 8) (j : Fin 9) :
    hdRo7SmAAux_ext9 v j = if h : j.val < 8 then v ⟨j.val, h⟩ else 0 := rfl

theorem hdRo7SmAAux_q9Hom_swap_perm (k : Fin 7) :
    hdRo7SmAAux_q9Hom
        (Equiv.swap (Fin.castSucc (Fin.castSucc k)) (Fin.succ (Fin.castSucc k))) =
      hdRo7SmAAux_permLin 8 (Equiv.swap (Fin.castSucc k) (Fin.succ k)) := by
  apply LinearEquiv.ext
  intro v
  ext i
  fin_cases k <;> fin_cases i <;>
    simp_all [hdRo7SmAAux_q9Hom, hdRo7SmAAux_q9, hdRo7SmAAux_proj9, hdRo7SmAAux_ext9,
      coordPerm_apply, hdRo7SmAAux_permLin_apply, Equiv.swap_apply_def]

theorem hdRo7SmAAux_q9Hom_swap_last :
    hdRo7SmAAux_q9Hom (Equiv.swap (Fin.castSucc (Fin.last 7)) (Fin.succ (Fin.last 7))) =
      kRefl 3 7 := by
  apply LinearEquiv.ext
  intro v
  ext i
  fin_cases i <;>
    simp [hdRo7SmAAux_q9Hom, hdRo7SmAAux_q9, hdRo7SmAAux_proj9, hdRo7SmAAux_ext9,
      coordPerm_apply, kRefl_apply, kRoot, kCoroot, Equiv.swap_apply_def]

theorem hdRo7SmAAux_kRefl_isRefl : GGLinRefl (kRefl 3 7) := by
  refine hdRo7SmAAux_isRefl_of_smRefl (u := kRoot 3 7) (φ := kCoroot 3 7)
    ⟨kCoroot_kRoot 3 7, ?_⟩
  intro v
  rw [kRefl_apply, kCoroot_apply]

theorem hdRo7SmAAux_q9Hom_swap_isRefl (k : Fin 8) :
    GGLinRefl (hdRo7SmAAux_q9Hom (Equiv.swap k.castSucc k.succ)) := by
  rcases Fin.eq_castSucc_or_eq_last k with ⟨m, rfl⟩ | rfl
  · rw [hdRo7SmAAux_q9Hom_swap_perm m]
    exact hdRo7SmAAux_permLin_swap_isRefl (n := 7) (k := m)
  · rw [hdRo7SmAAux_q9Hom_swap_last]
    exact hdRo7SmAAux_kRefl_isRefl

end CFSG.StandardType.HdRo7SU.Small
