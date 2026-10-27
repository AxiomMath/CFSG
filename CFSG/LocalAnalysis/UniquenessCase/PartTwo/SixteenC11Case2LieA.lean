module

public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open Matrix
open CFSG.LocalAnalysis.ComponentInitial

noncomputable section

@[expose] noncomputable def s16c11_case2lie_slEquiv (m : ℕ) (K : Type) [Field K] :
    StatedSL m K ≃* SpecialLinearGroup (Fin m) K :=
  (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL m K)).trans
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem s16c11_case2lie_coe_slEquiv_symm (m : ℕ) (K : Type) [Field K]
    (g : SpecialLinearGroup (Fin m) K) :
    (((s16c11_case2lie_slEquiv m K).symm g : StatedSL m K) : GL (Fin m) K) =
      Matrix.SpecialLinearGroup.toGL g :=
  rfl

private theorem s16c11_case2lie_eq_one_of_ne_zero {K : Type} [Field K] (hK : Nat.card K = 2)
    {x : K} (hx : x ≠ 0) : x = 1 := by
  have : Subsingleton Kˣ :=
    (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  exact congrArg Units.val (Subsingleton.elim (Units.mk0 x hx) 1)

private theorem s16c11_case2lie_eq_zero_or_eq_one {K : Type} [Field K] (hK : Nat.card K = 2)
    (x : K) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · exact Or.inr (s16c11_case2lie_eq_one_of_ne_zero hK hx)

private theorem s16c11_case2lie_mulVec_single_apply (m : ℕ) {K : Type} [Field K]
    (M : Matrix (Fin m) (Fin m) K) (j k : Fin m) :
    (M *ᵥ (Pi.single j (1 : K) : Fin m → K)) k = M k j := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem s16c11_case2lie_zero_lt {m : ℕ} {k : Fin m} (hk : (k : ℕ) ≠ 0) :
    (⟨0, by omega⟩ : Fin m) < k := by
  rw [Fin.lt_def]
  show (0 : ℕ) < (k : ℕ)
  omega

private theorem s16c11_case2lie_flagSpace_eq_top_of_le {m i : ℕ} {K : Type} [Field K]
    (hi : m ≤ i) : LinearFlag.flagSpace m K i = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [LinearFlag.mem_flagSpace]
  intro j hj
  exact absurd (lt_of_lt_of_le j.isLt hi) (not_lt.mpr hj)

private theorem s16c11_case2lie_mem_flagSpace_two {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] :
    (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) ∈ LinearFlag.flagSpace m K 2 := by
  rw [LinearFlag.mem_flagSpace]
  intro j hj
  have h : j ≠ (⟨0, by omega⟩ : Fin m) := by
    intro h
    have h0 : (j : ℕ) = 0 := by simpa using congrArg Fin.val h
    omega
  simp [Pi.single_eq_of_ne h]

private theorem s16c11_case2lie_v_ne_zero {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] :
    (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) ≠ 0 := by
  intro h
  have := congrFun h ⟨0, by omega⟩
  simp at this

theorem s16c11_case2lie_unitriangular_mulVec_e1 {m : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] {u : SpecialLinearGroup (Fin m) K} (hu : u ∈ LinearFlag.unitriangular m K) :
    (u : Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) =
      Pi.single ⟨0, by omega⟩ 1 := by
  funext k
  rw [s16c11_case2lie_mulVec_single_apply]
  by_cases hk : k = (⟨0, by omega⟩ : Fin m)
  · subst hk
    simp [hu.2]
  · have hk0 : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    rw [hu.1 k (⟨0, by omega⟩ : Fin m) (s16c11_case2lie_zero_lt hk0)]
    simp [Pi.single_eq_of_ne hk]

private theorem s16c11_case2lie_mem_unitriangular_of_isUpperTriangular {m : ℕ} {K : Type}
    [Field K] (hK : Nat.card K = 2) {g : SpecialLinearGroup (Fin m) K}
    (hUT : (g : Matrix (Fin m) (Fin m) K).IsUpperTriangular) :
    g ∈ LinearFlag.unitriangular m K := by
  rw [LinearFlag.mem_unitriangular]
  refine ⟨fun i j hij => hUT hij, fun i => ?_⟩
  have hprod : ∏ k, (g : Matrix (Fin m) (Fin m) K) k k = 1 := by
    rw [← Matrix.det_of_isUpperTriangular hUT]
    exact g.2
  have hne : (g : Matrix (Fin m) (Fin m) K) i i ≠ 0 := by
    intro h0
    have hzero : ∏ k, (g : Matrix (Fin m) (Fin m) K) k k = 0 :=
      Finset.prod_eq_zero (s := Finset.univ)
        (f := fun k => (g : Matrix (Fin m) (Fin m) K) k k) (Finset.mem_univ i) h0
    rw [hzero] at hprod
    exact one_ne_zero hprod.symm
  exact s16c11_case2lie_eq_one_of_ne_zero hK hne

private theorem s16c11_case2lie_isUpperTriangular_of_mem_flagStabilizer_of_fix {m : ℕ}
    (hm : 2 ≤ m) {K : Type} [Field K] {g : SpecialLinearGroup (Fin m) K}
    (hgV : g ∈ LinearFlag.flagStabilizer m K {i : ℕ | 2 ≤ i ∧ i ≤ m - 1})
    (hgv : (g : Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) =
      Pi.single ⟨0, by omega⟩ 1) :
    (g : Matrix (Fin m) (Fin m) K).IsUpperTriangular := by
  intro k j hjk
  by_cases hj0 : j = (⟨0, by omega⟩ : Fin m)
  · rw [hj0] at hjk ⊢
    have h := congrFun hgv k
    simp only [s16c11_case2lie_mulVec_single_apply] at h
    have hk : k ≠ (⟨0, by omega⟩ : Fin m) := Ne.symm (Fin.ne_of_lt hjk)
    simpa [Pi.single_eq_of_ne hk] using h
  · have hjjk : (j : ℕ) < (k : ℕ) := by
      show (j : ℕ) < (k : ℕ)
      exact hjk
    have hj1 : 1 ≤ (j : ℕ) := by
      have : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
      omega
    have hi2 : 2 ≤ (j : ℕ) + 1 := by omega
    have hile : (j : ℕ) + 1 ≤ m - 1 := by
      have hjlt := j.isLt
      have hklt := k.isLt
      omega
    have hmem : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace m K ((j : ℕ) + 1)) :=
      LinearFlag.mem_flagStabilizer.mp hgV ((j : ℕ) + 1) ⟨hi2, hile⟩
    have hbase : (Pi.single j (1 : K) : Fin m → K) ∈
        LinearFlag.flagSpace m K ((j : ℕ) + 1) := by
      rw [LinearFlag.mem_flagSpace]
      intro l hl
      have h : l ≠ j := by
        intro h
        rw [h] at hl
        omega
      simp [Pi.single_eq_of_ne h]
    have hw : (g : Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single j (1 : K) : Fin m → K) ∈
        LinearFlag.flagSpace m K ((j : ℕ) + 1) := by
      have hmap := LinearFlag.mem_stabilizer.mp hmem
      rw [← hmap]
      exact Submodule.mem_map.mpr ⟨_, hbase, by rw [Matrix.mulVecLin_apply]⟩
    have hk : (j : ℕ) + 1 ≤ (k : ℕ) := by omega
    have hz := LinearFlag.mem_flagSpace.mp hw k hk
    simp only [s16c11_case2lie_mulVec_single_apply] at hz
    exact hz

private theorem s16c11_case2lie_mem_unitriangular_of_mem_flagStabilizer_of_fix {m : ℕ}
    (hm : 2 ≤ m) {K : Type} [Field K] (hK : Nat.card K = 2)
    {g : SpecialLinearGroup (Fin m) K}
    (hgV : g ∈ LinearFlag.flagStabilizer m K {i : ℕ | 2 ≤ i ∧ i ≤ m - 1})
    (hgv : (g : Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) =
      Pi.single ⟨0, by omega⟩ 1) :
    g ∈ LinearFlag.unitriangular m K :=
  s16c11_case2lie_mem_unitriangular_of_isUpperTriangular hK
    (s16c11_case2lie_isUpperTriangular_of_mem_flagStabilizer_of_fix hm hgV hgv)

theorem s16c11_case2lie_reflection_one_mulVec {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] :
    ((LinearFlag.reflection m K 1 le_rfl (by omega) : SpecialLinearGroup (Fin m) K) :
        Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) =
      Pi.single ⟨1, by omega⟩ 1 := by
  rw [LinearFlag.coe_reflection, LinearFlag.reflectionMatrix_eq 1 le_rfl (by omega)]
  have hd : (Matrix.diagonal (fun b : Fin m => if (b : ℕ) = 1 then (-1 : K) else 1)) *ᵥ
      (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) = Pi.single ⟨0, by omega⟩ 1 := by
    funext b
    rw [Matrix.mulVec_diagonal]
    by_cases hb : b = (⟨0, by omega⟩ : Fin m)
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]
  rw [← Matrix.mulVec_mulVec, hd, LinearFlag.permMatrix_mulVec_single]
  congr 1

private theorem s16c11_case2lie_transvection_mulVec {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K]
    {h01 : (⟨0, by omega⟩ : Fin m) < ⟨1, by omega⟩} :
    ((SpecialLinearGroup.transvection h01.ne (1 : K) : SpecialLinearGroup (Fin m) K) :
        Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨1, by omega⟩ 1 : Fin m → K) =
      Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 := by
  have h := Matrix.SpecialLinearGroup.transvection_smul_single_snd
    (i := (⟨0, by omega⟩ : Fin m)) (j := (⟨1, by omega⟩ : Fin m)) h01.ne (1 : K)
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h
  rw [show (Pi.single (⟨1, by omega⟩ : Fin m) (1 : K) : Fin m → K) +
      (1 : K) • Pi.single (⟨0, by omega⟩ : Fin m) (1 : K) =
      Pi.single (⟨0, by omega⟩ : Fin m) 1 + Pi.single (⟨1, by omega⟩ : Fin m) 1 by
    rw [one_smul, add_comm]] at h
  exact h

private theorem s16c11_case2lie_mem_flagSpace_two_cases {m : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] (hK : Nat.card K = 2) {w : Fin m → K}
    (hw : w ∈ LinearFlag.flagSpace m K 2) (hw0 : w ≠ 0) :
    w = Pi.single ⟨0, by omega⟩ 1 ∨ w = Pi.single ⟨1, by omega⟩ 1 ∨
      w = Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 := by
  have hvan : ∀ j : Fin m, 2 ≤ (j : ℕ) → w j = 0 := LinearFlag.mem_flagSpace.mp hw
  have hother : ∀ j : Fin m, j ≠ (⟨0, by omega⟩ : Fin m) →
      j ≠ (⟨1, by omega⟩ : Fin m) → w j = 0 := by
    intro j hj0 hj1
    apply hvan
    have h0 : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
    have h1 : (j : ℕ) ≠ 1 := fun h => hj1 (Fin.ext h)
    omega
  rcases s16c11_case2lie_eq_zero_or_eq_one hK (w ⟨0, by omega⟩) with h0 | h0 <;>
    rcases s16c11_case2lie_eq_zero_or_eq_one hK (w ⟨1, by omega⟩) with h1 | h1
  · exfalso
    apply hw0
    funext j
    by_cases hj0 : j = (⟨0, by omega⟩ : Fin m)
    · subst hj0; simp [h0]
    · by_cases hj1 : j = (⟨1, by omega⟩ : Fin m)
      · subst hj1; simp [h1]
      · rw [hother j hj0 hj1]; rfl
  · right; left
    funext j
    by_cases hj0 : j = (⟨0, by omega⟩ : Fin m)
    · subst hj0; simp [h0]
    · by_cases hj1 : j = (⟨1, by omega⟩ : Fin m)
      · subst hj1; simp [h1]
      · rw [hother j hj0 hj1]; simp [Pi.single_eq_of_ne hj1]
  · left
    funext j
    by_cases hj0 : j = (⟨0, by omega⟩ : Fin m)
    · subst hj0; simp [h0]
    · by_cases hj1 : j = (⟨1, by omega⟩ : Fin m)
      · subst hj1; simp [h1, Pi.single_eq_of_ne (Ne.symm hj0)]
      · rw [hother j hj0 hj1]; simp [Pi.single_eq_of_ne hj0]
  · right; right
    funext j
    by_cases hj0 : j = (⟨0, by omega⟩ : Fin m)
    · subst hj0; simp [h0]
    · by_cases hj1 : j = (⟨1, by omega⟩ : Fin m)
      · subst hj1; simp [h1]
      · rw [hother j hj0 hj1]
        simp [Pi.single_eq_of_ne hj0, Pi.single_eq_of_ne hj1]

private theorem s16c11_case2lie_smul_mem_flagSpace_two {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K]
    {g : SpecialLinearGroup (Fin m) K}
    (hgV : g ∈ LinearFlag.flagStabilizer m K {i : ℕ | 2 ≤ i ∧ i ≤ m - 1})
    {w : Fin m → K} (hw : w ∈ LinearFlag.flagSpace m K 2) :
    (g : Matrix (Fin m) (Fin m) K) *ᵥ w ∈ LinearFlag.flagSpace m K 2 := by
  by_cases hm3 : 3 ≤ m
  · have hmem : g ∈ LinearFlag.stabilizer (LinearFlag.flagSpace m K 2) :=
      LinearFlag.mem_flagStabilizer.mp hgV 2 ⟨le_rfl, by omega⟩
    have hmap := LinearFlag.mem_stabilizer.mp hmem
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨_, hw, by rw [Matrix.mulVecLin_apply]⟩
  · have hm2 : m = 2 := by omega
    subst hm2
    rw [s16c11_case2lie_flagSpace_eq_top_of_le (le_refl 2)]
    exact Submodule.mem_top

theorem s16c11_case2lie_unitriangular_relIndex_flagStabilizer {m : ℕ} (hm : 2 ≤ m)
    {K : Type} [Field K] (hK : Nat.card K = 2) :
    (LinearFlag.unitriangular m K).relIndex
        (LinearFlag.flagStabilizer m K {i : ℕ | 2 ≤ i ∧ i ≤ m - 1}) = 3 := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set V := LinearFlag.flagStabilizer m K {i : ℕ | 2 ≤ i ∧ i ≤ m - 1} with hV
  set U := LinearFlag.unitriangular m K with hU
  set v : Fin m → K := Pi.single ⟨0, by omega⟩ 1 with hv
  have h01 : (⟨0, by omega⟩ : Fin m) < ⟨1, by omega⟩ := by
    rw [Fin.lt_def]; show (0 : ℕ) < (1 : ℕ); norm_num
  set u : SpecialLinearGroup (Fin m) K := SpecialLinearGroup.transvection h01.ne (1 : K) with hu
  set s : SpecialLinearGroup (Fin m) K := LinearFlag.reflection m K 1 le_rfl (by omega) with hs
  set t : SpecialLinearGroup (Fin m) K := u * s with ht
  have hstab : U.subgroupOf V = MulAction.stabilizer ↥V v := by
    ext x
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor
    · intro hx
      change (x : SpecialLinearGroup (Fin m) K) • v = v
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
      exact s16c11_case2lie_unitriangular_mulVec_e1 hm hx
    · intro hx
      have hx' : ((x : SpecialLinearGroup (Fin m) K) :
          Matrix (Fin m) (Fin m) K) *ᵥ v = v := by
        simpa [Subgroup.smul_def, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
          using hx
      exact s16c11_case2lie_mem_unitriangular_of_mem_flagStabilizer_of_fix hm hK x.2 hx'
  have hsV : s ∈ V := by
    rw [hV, hs, LinearFlag.mem_flagStabilizer]
    intro i hi
    have hi2 : 2 ≤ i := hi.1
    have hi1 : i ≠ 1 := by omega
    exact LinearFlag.reflection_mem_stabilizer_of_ne (i := i) (j := 1) le_rfl (by omega) hi1
  have huV : u ∈ V := by
    rw [hV, hu, LinearFlag.mem_flagStabilizer]
    intro i _
    exact LinearFlag.mem_flagStabilizer.mp
      (LinearFlag.upperTriangular_le_flagStabilizer {i}
        (LinearFlag.unitriangular_le_upperTriangular m K
          (LinearFlag.transvection_mem_unitriangular h01 (1 : K)))) i (Set.mem_singleton i)
  have htV : t ∈ V := by
    rw [ht]
    exact V.mul_mem huV hsV
  have hs_act : s • v = Pi.single ⟨1, by omega⟩ 1 := by
    rw [hv, hs, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    exact s16c11_case2lie_reflection_one_mulVec hm
  have ht_act : t • v = Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 := by
    rw [hv, ht, mul_smul, hs_act]
    rw [hu, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    exact s16c11_case2lie_transvection_mulVec (h01 := h01) hm
  have h1 : v ∉ ({s • v, t • v} : Set (Fin m → K)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_⟩
    · intro h
      have hh := congrFun h (⟨0, by omega⟩ : Fin m)
      rw [hs_act, hv] at hh
      simpa using hh
    · intro h
      have hh := congrFun h (⟨1, by omega⟩ : Fin m)
      rw [ht_act, hv] at hh
      simpa using hh
  have h2 : s • v ∉ ({t • v} : Set (Fin m → K)) := by
    simp only [Set.mem_singleton_iff]
    intro h
    have hh := congrFun h (⟨0, by omega⟩ : Fin m)
    rw [hs_act, ht_act] at hh
    simpa using hh
  have h3 : ({v, s • v, t • v} : Set (Fin m → K)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
  have hsub : ({v, s • v, t • v} : Set (Fin m → K)) ⊆ MulAction.orbit ↥V v := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using MulAction.mem_orbit v (1 : ↥V)
    · exact ⟨⟨s, hsV⟩, rfl⟩
    · exact ⟨⟨t, htV⟩, rfl⟩
  have hsub' : MulAction.orbit ↥V v ⊆ ({v, s • v, t • v} : Set (Fin m → K)) := by
    intro w hw
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp hw
    have hxF : (x : SpecialLinearGroup (Fin m) K) • v ∈ LinearFlag.flagSpace m K 2 := by
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
      exact s16c11_case2lie_smul_mem_flagSpace_two hm x.2 (by
        rw [hv]; exact s16c11_case2lie_mem_flagSpace_two hm)
    have hxne : (x : SpecialLinearGroup (Fin m) K) • v ≠ 0 := by
      intro h0
      have h1' : (x : SpecialLinearGroup (Fin m) K)⁻¹ •
          ((x : SpecialLinearGroup (Fin m) K) • v) = v := by
        rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [h0, smul_zero] at h1'
      exact s16c11_case2lie_v_ne_zero hm h1'.symm
    have hx' : (x : SpecialLinearGroup (Fin m) K) • v = w := by
      simpa [Subgroup.smul_def] using hx
    rw [← hx']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases s16c11_case2lie_mem_flagSpace_two_cases hm hK hxF hxne with h | h | h
    · left; rw [h, hv]
    · right; left; rw [h, hs_act]
    · right; right; rw [h, ht_act]
  have hOrbit : (MulAction.orbit ↥V v).ncard = 3 :=
    le_antisymm (h3 ▸ Set.ncard_le_ncard hsub') (h3 ▸ Set.ncard_le_ncard hsub)
  calc U.relIndex V = (U.subgroupOf V).index := rfl
    _ = (MulAction.stabilizer ↥V v).index := by rw [hstab]
    _ = (MulAction.orbit ↥V v).ncard := MulAction.index_stabilizer ↥V v
    _ = 3 := hOrbit

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
