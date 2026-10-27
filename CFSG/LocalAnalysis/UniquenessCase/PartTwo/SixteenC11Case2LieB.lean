module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.CycNodesStab
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubflag
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

noncomputable section

private theorem s16c11_case2lie_sp_eq_one_of_ne_zero {K : Type} [Field K] (hK : Nat.card K = 2)
    {x : K} (hx : x ≠ 0) : x = 1 := by
  have : Subsingleton Kˣ :=
    (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  exact congrArg Units.val (Subsingleton.elim (Units.mk0 x hx) 1)

private theorem s16c11_case2lie_sp_eq_zero_or_eq_one {K : Type} [Field K] (hK : Nat.card K = 2)
    (x : K) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (s16c11_case2lie_sp_eq_one_of_ne_zero hK hx)

private theorem s16c11_case2lie_sp_borel_eq_unipotent {r : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    SymplecticFlag.borelSubgroup r K = SymplecticFlag.unipotent r K := by
  refine (Subgroup.eq_of_le_of_card_ge SymplecticFlag.unipotent_le_borelSubgroup ?_).symm
  rw [SymplecticFlag.card_borelSubgroup, SymplecticFlag.card_unipotent, hK]
  simp

private theorem s16c11_case2lie_sp_e1_ne_zero {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] :
    (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl ⟨0, by omega⟩)
  simp at this

private theorem s16c11_case2lie_sp_e1_mem_isoFlag_one {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] :
    (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) ∈
      SymplecticFlag.isoFlag r K 1 :=
  Submodule.subset_span ⟨⟨0, by omega⟩, by simp, rfl⟩

private theorem s16c11_case2lie_sp_eq_smul_of_mem_isoFlag_one {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] {w : Fin r ⊕ Fin r → K} (hw : w ∈ SymplecticFlag.isoFlag r K 1) :
    w = w (Sum.inl ⟨0, by omega⟩) •
      (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) := by
  obtain ⟨hw1, hw2⟩ := SymplecticFlag.mem_isoFlag.mp hw
  funext x
  rcases x with j | j
  · by_cases hj : j = (⟨0, by omega⟩ : Fin r)
    · subst hj; simp
    · have hj1 : 1 ≤ (j : ℕ) := by
        have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
        omega
      rw [hw2 j hj1]
      simp [Pi.single_eq_of_ne (fun h => hj (Sum.inl.inj h))]
  · rw [hw1 j]; simp

private theorem s16c11_case2lie_sp_mulVec_mem_isoFlag_one {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] {g : StatedSp r K}
    (hgv : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K))
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ SymplecticFlag.isoFlag r K 1) :
    (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ∈ SymplecticFlag.isoFlag r K 1 := by
  rw [s16c11_case2lie_sp_eq_smul_of_mem_isoFlag_one hr hw]
  rw [Matrix.mulVec_smul, hgv]
  exact Submodule.smul_mem _ _ (s16c11_case2lie_sp_e1_mem_isoFlag_one hr)

theorem s16c11_case2lie_sp_unipotent_fixes {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) {g : StatedSp r K}
    (hg : g ∈ SymplecticFlag.unipotent r K) :
    (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) := by
  have hgB : g ∈ SymplecticFlag.borelSubgroup r K := SymplecticFlag.unipotent_le_borelSubgroup hg
  have hg1 : g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.isoFlag r K 1) :=
    SymplecticFlag.mem_borelSubgroup_iff_isoFlag.mp hgB 1 le_rfl (by omega)
  have hmem : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) ∈
      SymplecticFlag.isoFlag r K 1 := by
    have hmap := SymplecticFlag.mem_stabilizer.mp hg1
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨_, s16c11_case2lie_sp_e1_mem_isoFlag_one hr,
      by rw [Matrix.mulVecLin_apply]⟩
  have hgvne : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) ≠ 0 := by
    intro h0
    have h1 : (g⁻¹ : StatedSp r K) • ((g : StatedSp r K) •
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K)) =
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    have h2 : (g : StatedSp r K) •
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) = 0 := by
      change (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) = 0
      exact h0
    rw [h2, smul_zero] at h1
    exact s16c11_case2lie_sp_e1_ne_zero hr h1.symm
  have hw := s16c11_case2lie_sp_eq_smul_of_mem_isoFlag_one hr hmem
  have hc : ((((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K))
      (Sum.inl ⟨0, by omega⟩) ≠ 0 := by
    intro hc0
    exact hgvne (by rw [hw, hc0, zero_smul])
  rw [hw, s16c11_case2lie_sp_eq_one_of_ne_zero hK hc, one_smul]

private theorem s16c11_case2lie_sp_mem_unipotent_of_mem_flagStabilizer_of_fix {r : ℕ}
    (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {g : StatedSp r K}
    (hgX : g ∈ SymplecticHigher.flagStabilizer r K (Set.Icc 2 r))
    (hgv : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K)) :
    g ∈ SymplecticFlag.unipotent r K := by
  have hgv' : ((((g⁻¹ : StatedSp r K)) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) := by
    have h : (g⁻¹ : StatedSp r K) • ((g : StatedSp r K) •
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K)) =
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    have h2 : (g : StatedSp r K) •
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) =
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) := hgv
    rw [h2] at h
    exact h
  have hgB : g ∈ SymplecticFlag.borelSubgroup r K := by
    rw [SymplecticFlag.mem_borelSubgroup]
    intro i hi1 hir
    by_cases hi : i = 1
    · subst hi
      refine SymplecticFlag.mem_stabilizer_of_mulVec_mem (fun w hw => ?_) fun w hw => ?_
      · rw [SymplecticFlag.mem_flag_of_le (by omega : 1 ≤ r)] at hw ⊢
        exact s16c11_case2lie_sp_mulVec_mem_isoFlag_one hr hgv hw
      · rw [SymplecticFlag.mem_flag_of_le (by omega : 1 ≤ r)] at hw ⊢
        exact s16c11_case2lie_sp_mulVec_mem_isoFlag_one hr hgv' hw
    · have hi2 : 2 ≤ i := by omega
      exact SymplecticHigher.mem_flagStabilizer.mp hgX i ⟨hi2, hir⟩
  rwa [s16c11_case2lie_sp_borel_eq_unipotent hK] at hgB

private theorem s16c11_case2lie_sp_isoFlag_two_cases {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    (hK : Nat.card K = 2) {w : Fin r ⊕ Fin r → K} (hw : w ∈ SymplecticFlag.isoFlag r K 2)
    (hw0 : w ≠ 0) :
    w = Pi.single (Sum.inl ⟨0, by omega⟩) 1 ∨ w = Pi.single (Sum.inl ⟨1, by omega⟩) 1 ∨
      w = Pi.single (Sum.inl ⟨0, by omega⟩) 1 + Pi.single (Sum.inl ⟨1, by omega⟩) 1 := by
  obtain ⟨hw1, hw2⟩ := SymplecticFlag.mem_isoFlag.mp hw
  have hother : ∀ j : Fin r, j ≠ (⟨0, by omega⟩ : Fin r) → j ≠ (⟨1, by omega⟩ : Fin r) →
      w (Sum.inl j) = 0 := by
    intro j hj0 hj1
    apply hw2
    have h0 : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
    have h1 : (j : ℕ) ≠ 1 := fun h => hj1 (Fin.ext h)
    omega
  rcases s16c11_case2lie_sp_eq_zero_or_eq_one hK (w (Sum.inl ⟨0, by omega⟩)) with h0 | h0 <;>
    rcases s16c11_case2lie_sp_eq_zero_or_eq_one hK (w (Sum.inl ⟨1, by omega⟩)) with h1 | h1
  · exfalso
    apply hw0
    funext x
    rcases x with j | j
    · by_cases hj0 : j = (⟨0, by omega⟩ : Fin r)
      · subst hj0; simp [h0]
      · by_cases hj1 : j = (⟨1, by omega⟩ : Fin r)
        · subst hj1; simp [h1]
        · rw [hother j hj0 hj1]; rfl
    · rw [hw1 j]; rfl
  · right; left
    funext x
    rcases x with j | j
    · by_cases hj0 : j = (⟨0, by omega⟩ : Fin r)
      · subst hj0; simp [h0]
      · by_cases hj1 : j = (⟨1, by omega⟩ : Fin r)
        · subst hj1; simp [h1]
        · rw [hother j hj0 hj1]
          simp [Pi.single_eq_of_ne (fun h => hj1 (Sum.inl.inj h))]
    · rw [hw1 j]; simp
  · left
    funext x
    rcases x with j | j
    · by_cases hj0 : j = (⟨0, by omega⟩ : Fin r)
      · subst hj0; simp [h0]
      · by_cases hj1 : j = (⟨1, by omega⟩ : Fin r)
        · subst hj1
          simp [h1, Pi.single_eq_of_ne (fun h => hj0 (Sum.inl.inj h))]
        · rw [hother j hj0 hj1]
          simp [Pi.single_eq_of_ne (fun h => hj0 (Sum.inl.inj h))]
    · rw [hw1 j]; simp
  · right; right
    funext x
    rcases x with j | j
    · by_cases hj0 : j = (⟨0, by omega⟩ : Fin r)
      · subst hj0; simp [h0]
      · by_cases hj1 : j = (⟨1, by omega⟩ : Fin r)
        · subst hj1; simp [h1]
        · rw [hother j hj0 hj1]
          simp [Pi.single_eq_of_ne (fun h => hj0 (Sum.inl.inj h)),
            Pi.single_eq_of_ne (fun h => hj1 (Sum.inl.inj h))]
    · rw [hw1 j]; simp

private theorem s16c11_case2lie_sp_smul_mem_isoFlag_two {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] {g : StatedSp r K}
    (hgX : g ∈ SymplecticHigher.flagStabilizer r K (Set.Icc 2 r))
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ SymplecticFlag.isoFlag r K 2) :
    (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ∈ SymplecticFlag.isoFlag r K 2 := by
  have hmem : g ∈ SymplecticFlag.stabilizer r K (SymplecticFlag.flag r K 2) :=
    SymplecticHigher.mem_flagStabilizer.mp hgX 2 (by simp [Set.mem_Icc]; omega)
  have hwF : w ∈ SymplecticFlag.flag r K 2 := by
    rwa [SymplecticFlag.mem_flag_of_le (by omega : 2 ≤ r)]
  have hwmap : (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w ∈ SymplecticFlag.flag r K 2 := by
    have hmap := SymplecticFlag.mem_stabilizer.mp hmem
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨_, hwF, by rw [Matrix.mulVecLin_apply]⟩
  rwa [SymplecticFlag.mem_flag_of_le (by omega : 2 ≤ r)] at hwmap

private theorem s16c11_case2lie_sp_rho_mulVec_inl {r : ℕ} {K : Type} [Field K]
    {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) K) (l k : Fin r) :
    ((((SymplecticTorusWeyl.rho i j hij g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl l) (1 : K) : Fin r ⊕ Fin r → K)) (Sum.inl k) =
      (SymplecticTorusWeyl.pairMat i j (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (Pi.single l (1 : K) : Fin r → K)) k := by
  rw [SymplecticTorusWeyl.coe_rho', Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_inl]
  rw [Matrix.zero_mulVec, add_zero]
  congr 1
  funext x
  by_cases h : x = l
  · subst h; simp
  · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun hh => h (Sum.inl.inj hh))]

private theorem s16c11_case2lie_sp_zero_lt_iff {r m : ℕ} (hr : 2 ≤ r) (hm : 2 ≤ m) :
    ((⟨0, by omega⟩ : Fin r) : ℕ) < m ↔ ((⟨1, by omega⟩ : Fin r) : ℕ) < m := by
  have h0v : ((⟨0, by omega⟩ : Fin r) : ℕ) = 0 := rfl
  have h1v : ((⟨1, by omega⟩ : Fin r) : ℕ) = 1 := rfl
  rw [h0v, h1v]
  constructor <;> intro _ <;> omega

theorem s16c11_case2lie_sp_unipotent_relIndex_flagStabilizer {r : ℕ} (hr : 2 ≤ r)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    (SymplecticFlag.unipotent r K).relIndex
        (SymplecticHigher.flagStabilizer r K (Set.Icc 2 r)) = 3 := by
  classical
  set X := SymplecticHigher.flagStabilizer r K (Set.Icc 2 r) with hX
  set U := SymplecticFlag.unipotent r K with hU
  set v : Fin r ⊕ Fin r → K := Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) with hv
  have h01 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  set s : StatedSp r K := SymplecticTorusWeyl.rho (⟨0, by omega⟩ : Fin r)
    (⟨1, by omega⟩ : Fin r) h01 SymplecticTorusWeyl.sl2W with hs
  set t : StatedSp r K := SymplecticTorusWeyl.rho (⟨0, by omega⟩ : Fin r)
    (⟨1, by omega⟩ : Fin r) h01
    (SpecialLinearGroup.transvection (i := (⟨1, by omega⟩ : Fin 2))
      (j := (⟨0, by omega⟩ : Fin 2))
      (by intro h; have := congrArg Fin.val h; simp at this) (1 : K)) with ht
  have hstab : U.subgroupOf X = MulAction.stabilizer ↥X v := by
    ext x
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor
    · intro hx
      have hx' : (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = v :=
        s16c11_case2lie_sp_unipotent_fixes hr hK hx
      change (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = v
      exact hx'
    · intro hx
      change (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = v at hx
      exact s16c11_case2lie_sp_mem_unipotent_of_mem_flagStabilizer_of_fix hr hK x.2 hx
  have hsV : s ∈ X := by
    rw [hX, hs, SymplecticHigher.mem_flagStabilizer]
    intro m hm
    exact rho_mem_stabilizer (i := (⟨0, by omega⟩ : Fin r)) (j := (⟨1, by omega⟩ : Fin r))
      (Set.mem_Icc.mp hm).2 h01 (s16c11_case2lie_sp_zero_lt_iff hr (Set.mem_Icc.mp hm).1) _
  have htV : t ∈ X := by
    rw [hX, ht, SymplecticHigher.mem_flagStabilizer]
    intro m hm
    exact rho_mem_stabilizer (i := (⟨0, by omega⟩ : Fin r)) (j := (⟨1, by omega⟩ : Fin r))
      (Set.mem_Icc.mp hm).2 h01 (s16c11_case2lie_sp_zero_lt_iff hr (Set.mem_Icc.mp hm).1) _
  have hs0 : ((((s : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) (Sum.inl ⟨0, by omega⟩) = 0 := by
    rw [hv, hs, s16c11_case2lie_sp_rho_mulVec_inl, pairMat_mulVec h01]
    simp [SymplecticTorusWeyl.coe_sl2W, Pi.single_apply]
  have ht1 : ((((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) (Sum.inl ⟨1, by omega⟩) = 1 := by
    rw [hv, ht, s16c11_case2lie_sp_rho_mulVec_inl, pairMat_mulVec h01]
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]
  have ht0 : ((((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) (Sum.inl ⟨0, by omega⟩) = 1 := by
    rw [hv, ht, s16c11_case2lie_sp_rho_mulVec_inl, pairMat_mulVec h01]
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]
  have hv0 : v (Sum.inl ⟨0, by omega⟩) = 1 := by rw [hv]; simp
  have hv1 : v (Sum.inl ⟨1, by omega⟩) = 0 := by rw [hv]; simp
  have hsv : s • v ≠ v := by
    intro h
    have hh := congrFun h (Sum.inl ⟨0, by omega⟩)
    rw [show (s : StatedSp r K) • v = (((s : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v from rfl] at hh
    rw [hs0, hv0] at hh
    exact one_ne_zero hh.symm
  have htv : t • v ≠ v := by
    intro h
    have hh := congrFun h (Sum.inl ⟨1, by omega⟩)
    rw [show (t : StatedSp r K) • v = (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v from rfl] at hh
    rw [ht1, hv1] at hh
    exact one_ne_zero hh
  have hst : s • v ≠ t • v := by
    intro h
    have hh := congrFun h (Sum.inl ⟨0, by omega⟩)
    rw [show (s : StatedSp r K) • v = (((s : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v from rfl] at hh
    rw [show (t : StatedSp r K) • v = (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v from rfl] at hh
    rw [hs0, ht0] at hh
    exact one_ne_zero hh.symm
  have h1 : v ∉ ({s • v, t • v} : Set (Fin r ⊕ Fin r → K)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hsv.symm, htv.symm⟩
  have h2 : s • v ∉ ({t • v} : Set (Fin r ⊕ Fin r → K)) := by
    simpa [Set.mem_singleton_iff] using hst
  have h3 : ({v, s • v, t • v} : Set (Fin r ⊕ Fin r → K)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
  have hsub : ({v, s • v, t • v} : Set (Fin r ⊕ Fin r → K)) ⊆ MulAction.orbit ↥X v := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using MulAction.mem_orbit v (1 : ↥X)
    · exact ⟨⟨s, hsV⟩, rfl⟩
    · exact ⟨⟨t, htV⟩, rfl⟩
  let w0 : Fin r ⊕ Fin r → K := Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K)
  let w1 : Fin r ⊕ Fin r → K := Pi.single (Sum.inl ⟨1, by omega⟩) (1 : K)
  have hw00 : w0 (Sum.inl ⟨0, by omega⟩) = 1 := by simp [w0]
  have hw10 : w0 (Sum.inl ⟨1, by omega⟩) = 0 := by simp [w0]
  have hne01 : w0 ≠ w1 := by
    intro h
    have hh := congrFun h (Sum.inl ⟨0, by omega⟩)
    simp [w0, w1] at hh
  have hne02 : w0 ≠ w0 + w1 := by
    intro h
    have hh := congrFun h (Sum.inl ⟨1, by omega⟩)
    simp [w0, w1, Pi.single_apply] at hh
  have hne12 : w1 ≠ w0 + w1 := by
    intro h
    have hh := congrFun h (Sum.inl ⟨0, by omega⟩)
    simp [w0, w1, Pi.single_apply] at hh
  have hdrop1 : w0 ∉ ({w1, w0 + w1} : Set (Fin r ⊕ Fin r → K)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne01, hne02⟩
  have hdrop2 : w1 ∉ ({w0 + w1} : Set (Fin r ⊕ Fin r → K)) := by
    simpa [Set.mem_singleton_iff] using hne12
  have hthree : ({w0, w1, w0 + w1} : Set (Fin r ⊕ Fin r → K)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hdrop1, Set.ncard_insert_of_notMem hdrop2,
      Set.ncard_singleton]
  have hsub' : MulAction.orbit ↥X v ⊆ ({w0, w1, w0 + w1} : Set (Fin r ⊕ Fin r → K)) := by
    intro w hw
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp hw
    have hxF : (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ SymplecticFlag.isoFlag r K 2 := by
      rw [hv]
      exact s16c11_case2lie_sp_smul_mem_isoFlag_two hr x.2
        (Submodule.subset_span ⟨⟨0, by omega⟩, by simp, rfl⟩)
    have hxne : (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ≠ 0 := by
      intro h0
      have h1' : (x⁻¹ : StatedSp r K) • ((x : StatedSp r K) • v) = v := by
        rw [← mul_smul, inv_mul_cancel, one_smul]
      have h2 : (x : StatedSp r K) • v = 0 := by
        change (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = 0
        exact h0
      rw [h2, smul_zero] at h1'
      exact s16c11_case2lie_sp_e1_ne_zero hr (by rw [hv] at h1'; exact h1'.symm)
    have hx'' : (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = w := by
      change (((x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = w at hx
      exact hx
    rw [← hx'']
    rcases s16c11_case2lie_sp_isoFlag_two_cases hr hK hxF hxne with h | h | h
    · left; exact h
    · right; left; exact h
    · right; right; exact h
  have hOrbit : (MulAction.orbit ↥X v).ncard = 3 :=
    le_antisymm (hthree ▸ Set.ncard_le_ncard hsub') (h3 ▸ Set.ncard_le_ncard hsub)
  calc U.relIndex X = (U.subgroupOf X).index := rfl
    _ = (MulAction.stabilizer ↥X v).index := by rw [hstab]
    _ = (MulAction.orbit ↥X v).ncard := MulAction.index_stabilizer ↥X v
    _ = 3 := hOrbit

theorem s16c11_case2lie_sp_unipotent_le_flagStabilizer {r : ℕ} {K : Type} [Field K] :
    SymplecticFlag.unipotent r K ≤ SymplecticHigher.flagStabilizer r K (Set.Icc 2 r) :=
  SymplecticFlag.unipotent_le_borelSubgroup.trans
    (SymplecticHigher.borelSubgroup_le_flagStabilizer fun _ hi => (Set.mem_Icc.mp hi).2)

theorem s16c11_case2lie_sp_exists_moves {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) :
    ∃ g ∈ SymplecticHigher.flagStabilizer r K (Set.Icc 2 r),
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) ≠
        Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) := by
  have h01 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  refine ⟨SymplecticTorusWeyl.rho (⟨0, by omega⟩ : Fin r) (⟨1, by omega⟩ : Fin r) h01
    SymplecticTorusWeyl.sl2W, ?_, ?_⟩
  · rw [SymplecticHigher.mem_flagStabilizer]
    intro m hm
    exact rho_mem_stabilizer (i := (⟨0, by omega⟩ : Fin r)) (j := (⟨1, by omega⟩ : Fin r))
      (Set.mem_Icc.mp hm).2 h01 (s16c11_case2lie_sp_zero_lt_iff hr (Set.mem_Icc.mp hm).1) _
  · intro h
    have hh := congrFun h (Sum.inl ⟨0, by omega⟩)
    rw [s16c11_case2lie_sp_rho_mulVec_inl, pairMat_mulVec h01] at hh
    simp [SymplecticTorusWeyl.coe_sl2W, Pi.single_apply] at hh

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
