module

import CFSG.LocalAnalysis.StandardType.FF81.CentAModelBeta
public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin CFSG.SeitzReduction.F4Pilot

@[expose] def embIdx (k : ℕ) : BlkIdx 1 k → BlkIdx 1 (k + 2)
  | .inl i => .inl i
  | .inr (.inl j) => .inr (.inl (Fin.castAdd 2 j))
  | .inr (.inr i) => .inr (.inr i)

theorem embIdx_injective (k : ℕ) : Function.Injective (embIdx k) := by
  rintro (i | j | i) (i' | j' | i') h <;> simp_all [embIdx]

@[expose] noncomputable def embGL (k : ℕ) :
    GL (BlkIdx 1 k) (ZMod 2) →* GL (BlkIdx 1 (k + 2)) (ZMod 2) :=
  coordEmbedGL (embIdx k) (embIdx_injective k)

@[expose] def piPerm (k : ℕ) : Equiv.Perm (BlkIdx 1 (k + 2)) :=
  Equiv.swap (.inl 0) (.inr (.inl (Fin.last (k + 1)))) *
    Equiv.swap (.inr (.inr 0)) (.inr (.inl (Fin.last k).castSucc))

@[expose] noncomputable def piStd (k : ℕ) : GL (BlkIdx 1 (k + 2)) (ZMod 2) :=
  TauCeti.permutationGL (piPerm k)

theorem embGL_injective (k : ℕ) : Function.Injective (embGL k) :=
  coordEmbedGL_injective (embIdx_injective k)

private theorem caEmb_mem_range_inr_inl (k : ℕ) (m : Fin (k + 2)) :
    (Sum.inr (Sum.inl m) : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k) ↔ (m : ℕ) < k := by
  constructor
  · rintro ⟨x, hx⟩
    rcases x with a | b | c
    · simp [embIdx] at hx
    · have hb : Fin.castAdd 2 b = m := by simpa [embIdx] using hx
      rw [← hb]
      exact b.isLt
    · simp [embIdx] at hx
  · intro hm
    exact ⟨Sum.inr (Sum.inl ⟨m, hm⟩), by simp [embIdx]⟩

private def caEmb_extA (k : ℕ) (a : Matrix (Fin 1) (Fin k) (ZMod 2)) :
    Matrix (Fin 1) (Fin (k + 2)) (ZMod 2) :=
  Matrix.of fun i j => if h : (j : ℕ) < k then a i ⟨j, h⟩ else 0

private def caEmb_extB (k : ℕ) (b : Matrix (Fin k) (Fin 1) (ZMod 2)) :
    Matrix (Fin (k + 2)) (Fin 1) (ZMod 2) :=
  Matrix.of fun i j => if h : (i : ℕ) < k then b ⟨i, h⟩ j else 0

private theorem caEmb_extA_apply_of_le (k : ℕ) (a : Matrix (Fin 1) (Fin k) (ZMod 2))
    (i : Fin 1) {j : Fin (k + 2)} (hj : k ≤ (j : ℕ)) : caEmb_extA k a i j = 0 := by
  simp [caEmb_extA, Nat.not_lt.mpr hj]

private theorem caEmb_extB_apply_of_le (k : ℕ) (b : Matrix (Fin k) (Fin 1) (ZMod 2))
    {i : Fin (k + 2)} (hi : k ≤ (i : ℕ)) (j : Fin 1) : caEmb_extB k b i j = 0 := by
  simp [caEmb_extB, Nat.not_lt.mpr hi]

private theorem caEmb_extA_zero (k : ℕ) :
    caEmb_extA k (0 : Matrix (Fin 1) (Fin k) (ZMod 2)) = 0 := by
  ext i j
  by_cases h : (j : ℕ) < k <;> simp [caEmb_extA, h]

private theorem caEmb_extB_zero (k : ℕ) :
    caEmb_extB k (0 : Matrix (Fin k) (Fin 1) (ZMod 2)) = 0 := by
  ext i j
  by_cases h : (i : ℕ) < k <;> simp [caEmb_extB, h]

private theorem caEmb_embGL_uGL (k : ℕ) (a : Matrix (Fin 1) (Fin k) (ZMod 2))
    (b : Matrix (Fin k) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) :
    embGL k (uGL a b c) = uGL (caEmb_extA k a) (caEmb_extB k b) c := by
  apply Units.ext
  change ((coordEmbedGL (embIdx k) (embIdx_injective k) (uGL a b c) :
    GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
      Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2)) =
    ((uGL (caEmb_extA k a) (caEmb_extB k b) c : GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
      Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2))
  rw [coe_coordEmbedGL, coe_uGL, coe_uGL]
  ext i j
  rcases i with i | m | i <;> rcases j with j | m' | j
  · rw [show (Sum.inl i : BlkIdx 1 (k + 2)) = embIdx k (Sum.inl i) from rfl,
        show (Sum.inl j : BlkIdx 1 (k + 2)) = embIdx k (Sum.inl j) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
    simp [embIdx, uMat, blk]
  · by_cases hm : (m' : ℕ) < k
    · have hm' : (Fin.castAdd 2 (⟨m', hm⟩ : Fin k) : Fin (k + 2)) = m' := Fin.ext rfl
      rw [← hm']
      rw [show (Sum.inl i : BlkIdx 1 (k + 2)) = embIdx k (Sum.inl i) from rfl,
        show (Sum.inr (Sum.inl (Fin.castAdd 2 (⟨m', hm⟩ : Fin k))) : BlkIdx 1 (k + 2)) =
          embIdx k (Sum.inr (Sum.inl (⟨m', hm⟩ : Fin k))) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
      simp [embIdx, uMat, blk, caEmb_extA, hm]
    · have hnot : ¬ ((Sum.inl i : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k) ∧
          (Sum.inr (Sum.inl m') : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k)) := by
        rintro ⟨-, h2⟩
        rw [caEmb_mem_range_inr_inl] at h2
        exact hm h2
      rw [coordEmbedMat_apply_of_not_mem _ hnot]
      simp [uMat, blk, Matrix.one_apply, caEmb_extA_apply_of_le k a i (Nat.le_of_not_lt hm)]
  · rw [show (Sum.inl i : BlkIdx 1 (k + 2)) = embIdx k (Sum.inl i) from rfl,
        show (Sum.inr (Sum.inr j) : BlkIdx 1 (k + 2)) = embIdx k (Sum.inr (Sum.inr j)) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
    simp [embIdx, uMat, blk]
  · by_cases hm : (m : ℕ) < k
    · have hm1 : (Fin.castAdd 2 (⟨m, hm⟩ : Fin k) : Fin (k + 2)) = m := Fin.ext rfl
      rw [← hm1]
      rw [show (Sum.inr (Sum.inl (Fin.castAdd 2 (⟨m, hm⟩ : Fin k))) : BlkIdx 1 (k + 2)) =
          embIdx k (Sum.inr (Sum.inl (⟨m, hm⟩ : Fin k))) from rfl,
        show (Sum.inl j : BlkIdx 1 (k + 2)) = embIdx k (Sum.inl j) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
      simp [embIdx, uMat, blk]
    · have hnot : ¬ ((Sum.inr (Sum.inl m) : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k) ∧
          (Sum.inl j : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k)) := by
        rintro ⟨h1, -⟩
        rw [caEmb_mem_range_inr_inl] at h1
        exact hm h1
      rw [coordEmbedMat_apply_of_not_mem _ hnot]
      simp [uMat, blk, Matrix.one_apply]
  · by_cases hm : (m : ℕ) < k
    · by_cases hm' : (m' : ℕ) < k
      · have hm1 : (Fin.castAdd 2 (⟨m, hm⟩ : Fin k) : Fin (k + 2)) = m := Fin.ext rfl
        have hm2 : (Fin.castAdd 2 (⟨m', hm'⟩ : Fin k) : Fin (k + 2)) = m' := Fin.ext rfl
        rw [← hm1, ← hm2]
        rw [show (Sum.inr (Sum.inl (Fin.castAdd 2 (⟨m, hm⟩ : Fin k))) : BlkIdx 1 (k + 2)) =
            embIdx k (Sum.inr (Sum.inl (⟨m, hm⟩ : Fin k))) from rfl,
          show (Sum.inr (Sum.inl (Fin.castAdd 2 (⟨m', hm'⟩ : Fin k))) : BlkIdx 1 (k + 2)) =
            embIdx k (Sum.inr (Sum.inl (⟨m', hm'⟩ : Fin k))) from rfl,
          coordEmbedMat_apply_image (embIdx_injective k)]
        simp [embIdx, uMat, blk]
        have h1 : (1 : Matrix (Fin k) (Fin k) (ZMod 2)) ⟨↑m, hm⟩ ⟨↑m', hm'⟩ =
            (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))
              (Fin.castAdd 2 (⟨m, hm⟩ : Fin k)) (Fin.castAdd 2 (⟨m', hm'⟩ : Fin k)) := by
          simp [Matrix.one_apply, Fin.castAdd_inj, Fin.ext_iff]
        rw [h1, hm1, hm2]
      · have hnot : ¬ ((Sum.inr (Sum.inl m) : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k) ∧
            (Sum.inr (Sum.inl m') : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k)) := by
          rintro ⟨-, h2⟩
          rw [caEmb_mem_range_inr_inl] at h2
          exact hm' h2
        rw [coordEmbedMat_apply_of_not_mem _ hnot]
        simp [uMat, blk, Matrix.one_apply]
    · have hnot : ¬ ((Sum.inr (Sum.inl m) : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k) ∧
          (Sum.inr (Sum.inl m') : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k)) := by
        rintro ⟨h1, -⟩
        rw [caEmb_mem_range_inr_inl] at h1
        exact hm h1
      rw [coordEmbedMat_apply_of_not_mem _ hnot]
      simp [uMat, blk, Matrix.one_apply]
  · by_cases hm : (m : ℕ) < k
    · have hm1 : (Fin.castAdd 2 (⟨m, hm⟩ : Fin k) : Fin (k + 2)) = m := Fin.ext rfl
      rw [← hm1]
      rw [show (Sum.inr (Sum.inl (Fin.castAdd 2 (⟨m, hm⟩ : Fin k))) : BlkIdx 1 (k + 2)) =
          embIdx k (Sum.inr (Sum.inl (⟨m, hm⟩ : Fin k))) from rfl,
        show (Sum.inr (Sum.inr j) : BlkIdx 1 (k + 2)) = embIdx k (Sum.inr (Sum.inr j)) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
      simp [embIdx, uMat, blk, caEmb_extB, hm]
    · have hnot : ¬ ((Sum.inr (Sum.inl m) : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k) ∧
          (Sum.inr (Sum.inr j) : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k)) := by
        rintro ⟨h1, -⟩
        rw [caEmb_mem_range_inr_inl] at h1
        exact hm h1
      rw [coordEmbedMat_apply_of_not_mem _ hnot]
      simp [uMat, blk, Matrix.one_apply,
        caEmb_extB_apply_of_le k b (Nat.le_of_not_lt hm) j]
  · rw [show (Sum.inr (Sum.inr i) : BlkIdx 1 (k + 2)) = embIdx k (Sum.inr (Sum.inr i)) from rfl,
        show (Sum.inl j : BlkIdx 1 (k + 2)) = embIdx k (Sum.inl j) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
    simp [embIdx, uMat, blk]
  · by_cases hm : (m' : ℕ) < k
    · have hm' : (Fin.castAdd 2 (⟨m', hm⟩ : Fin k) : Fin (k + 2)) = m' := Fin.ext rfl
      rw [← hm']
      rw [show (Sum.inr (Sum.inr i) : BlkIdx 1 (k + 2)) = embIdx k (Sum.inr (Sum.inr i)) from rfl,
        show (Sum.inr (Sum.inl (Fin.castAdd 2 (⟨m', hm⟩ : Fin k))) : BlkIdx 1 (k + 2)) =
          embIdx k (Sum.inr (Sum.inl (⟨m', hm⟩ : Fin k))) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
      simp [embIdx, uMat, blk]
    · have hnot : ¬ ((Sum.inr (Sum.inr i) : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k) ∧
          (Sum.inr (Sum.inl m') : BlkIdx 1 (k + 2)) ∈ Set.range (embIdx k)) := by
        rintro ⟨-, h2⟩
        rw [caEmb_mem_range_inr_inl] at h2
        exact hm h2
      rw [coordEmbedMat_apply_of_not_mem _ hnot]
      simp [uMat, blk, Matrix.one_apply]
  · rw [show (Sum.inr (Sum.inr i) : BlkIdx 1 (k + 2)) = embIdx k (Sum.inr (Sum.inr i)) from rfl,
        show (Sum.inr (Sum.inr j) : BlkIdx 1 (k + 2)) = embIdx k (Sum.inr (Sum.inr j)) from rfl,
        coordEmbedMat_apply_image (embIdx_injective k)]
    simp [embIdx, uMat, blk]

theorem embGL_jGL (k : ℕ) : embGL k (jGL 1 k) = jGL 1 (k + 2) := by
  rw [jGL, jGL, caEmb_embGL_uGL, caEmb_extA_zero, caEmb_extB_zero]

private theorem caEmb_piPerm_mul_self (k : ℕ) : piPerm k * piPerm k = 1 := by
  let s : Equiv.Perm (BlkIdx 1 (k + 2)) :=
    Equiv.swap (Sum.inl 0) (Sum.inr (Sum.inl (Fin.last (k + 1))))
  let t : Equiv.Perm (BlkIdx 1 (k + 2)) :=
    Equiv.swap (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl ((Fin.last k).castSucc)))
  have hne : (Fin.last k).castSucc ≠ Fin.last (k + 1) :=
    (Fin.castSucc_lt_last (Fin.last k)).ne
  have hst : Commute s t := by
    refine (Equiv.Perm.disjoint_swap_swap ?_).commute
    simp [hne, Ne.symm hne]
  change s * t * (s * t) = 1
  calc s * t * (s * t) = s * (t * s) * t := by group
    _ = s * (s * t) * t := by rw [← hst.eq]
    _ = (s * s) * (t * t) := by group
    _ = 1 := by
      rw [show s * s = 1 from Equiv.swap_mul_self _ _,
        show t * t = 1 from Equiv.swap_mul_self _ _]
      exact mul_one 1

private theorem caEmb_piStd_mul_self (k : ℕ) : piStd k * piStd k = 1 := by
  rw [piStd, ← map_mul, caEmb_piPerm_mul_self, map_one]

private theorem caEmb_piStd_inv (k : ℕ) : (piStd k)⁻¹ = piStd k := by
  have h := caEmb_piStd_mul_self k
  calc (piStd k)⁻¹ = (piStd k)⁻¹ * 1 := by rw [mul_one]
    _ = (piStd k)⁻¹ * (piStd k * piStd k) := by rw [h]
    _ = piStd k := by group

private theorem caEmb_conj_apply (k : ℕ)
    (x : GL (BlkIdx 1 (k + 2)) (ZMod 2)) (i j : BlkIdx 1 (k + 2)) :
    ((piStd k * x * (piStd k)⁻¹ : GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
      Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2)) i j =
      (x : Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2)) (piPerm k i) (piPerm k j) := by
  have h1 : piStd k = (TauCeti.permutationGL (piPerm k))⁻¹ := by
    rw [piStd]
    exact (caEmb_piStd_inv k).symm
  rw [h1, inv_inv, TauCeti.coe_permutationGL_inv_mul_mul_permutationGL_apply]

private theorem caEmb_piPerm_A (k : ℕ) (a : Fin 1) :
    piPerm k (Sum.inl a) = Sum.inr (Sum.inl (Fin.last (k + 1))) := by
  have ha : a = 0 := Subsingleton.elim a 0
  subst ha
  simp [piPerm, Equiv.swap_apply_def, Fin.ext_iff]

private theorem caEmb_piPerm_BL (k : ℕ) :
    piPerm k (Sum.inr (Sum.inl (Fin.last (k + 1)))) = Sum.inl 0 := by
  simp [piPerm, Equiv.swap_apply_def, Fin.ext_iff]

private theorem caEmb_piPerm_C (k : ℕ) (c : Fin 1) :
    piPerm k (Sum.inr (Sum.inr c)) = Sum.inr (Sum.inl ((Fin.last k).castSucc)) := by
  have hc : c = 0 := Subsingleton.elim c 0
  subst hc
  simp [piPerm, Equiv.swap_apply_def, Fin.ext_iff]

private theorem caEmb_piPerm_BK (k : ℕ) :
    piPerm k (Sum.inr (Sum.inl ((Fin.last k).castSucc))) = Sum.inr (Sum.inr 0) := by
  simp [piPerm, Equiv.swap_apply_def, Fin.ext_iff]

private theorem caEmb_piPerm_fixed (k : ℕ) {m : Fin (k + 2)}
    (hm : m ≠ (Fin.last k).castSucc) (hm' : m ≠ Fin.last (k + 1)) :
    piPerm k (Sum.inr (Sum.inl m)) = Sum.inr (Sum.inl m) := by
  simp [piPerm, Equiv.swap_apply_def, Fin.ext_iff, hm, hm']

theorem piStd_conj_betaStd (k : ℕ) :
    piStd k * betaStd (k + 2) * (piStd k)⁻¹ = bStar (k + 2) := by
  have hne : (Fin.last k).castSucc ≠ Fin.last (k + 1) :=
    (Fin.castSucc_lt_last (Fin.last k)).ne
  apply Units.ext
  ext i j
  rw [caEmb_conj_apply]
  rcases i with a | m | c <;> rcases j with a' | m' | c'
  ·
    try fin_cases a
    try fin_cases a'
    try fin_cases c
    try fin_cases c'
    simp [caEmb_piPerm_A, betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
      CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne, Ne.symm hne]
  ·
    by_cases hm' : m' = (Fin.last k).castSucc
    · subst hm'
      try fin_cases a
      try fin_cases a'
      try fin_cases c
      try fin_cases c'
      simp [caEmb_piPerm_A, caEmb_piPerm_BK, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
        lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
        Ne.symm hne]
    · by_cases hm2' : m' = Fin.last (k + 1)
      · subst hm2'
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_A, caEmb_piPerm_BL, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
          lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
      ·
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_A, caEmb_piPerm_fixed k hm' hm2', hm', hm2', Ne.symm hm', Ne.symm hm2',
          betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
          CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
  ·
    try fin_cases a
    try fin_cases a'
    try fin_cases c
    try fin_cases c'
    simp [caEmb_piPerm_A, caEmb_piPerm_C, betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
      CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne, Ne.symm hne]
  ·
    by_cases hm : m = (Fin.last k).castSucc
    · subst hm
      try fin_cases a
      try fin_cases a'
      try fin_cases c
      try fin_cases c'
      simp [caEmb_piPerm_BK, caEmb_piPerm_A, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
        lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
        Ne.symm hne]
    · by_cases hm2 : m = Fin.last (k + 1)
      · subst hm2
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_BL, caEmb_piPerm_A, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
          lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
      ·
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_fixed k hm hm2, caEmb_piPerm_A, hm, hm2, Ne.symm hm, Ne.symm hm2,
          betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
          CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
  ·
    by_cases hm : m = (Fin.last k).castSucc
    · subst hm
      by_cases hm' : m' = (Fin.last k).castSucc
      · subst hm'
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_BK, betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
          CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
      · by_cases hm2' : m' = Fin.last (k + 1)
        · subst hm2'
          try fin_cases a
          try fin_cases a'
          try fin_cases c
          try fin_cases c'
          simp [caEmb_piPerm_BK, caEmb_piPerm_BL, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
            lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo,
            hne, Ne.symm hne]
        ·
          try fin_cases a
          try fin_cases a'
          try fin_cases c
          try fin_cases c'
          simp [caEmb_piPerm_BK, caEmb_piPerm_fixed k hm' hm2', hm', hm2', Ne.symm hm',
            Ne.symm hm2', betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
            CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
            Ne.symm hne]
    · by_cases hm2 : m = Fin.last (k + 1)
      · subst hm2
        by_cases hm' : m' = (Fin.last k).castSucc
        · subst hm'
          try fin_cases a
          try fin_cases a'
          try fin_cases c
          try fin_cases c'
          simp [caEmb_piPerm_BL, caEmb_piPerm_BK, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
            lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo,
            hne, Ne.symm hne]
        · by_cases hm2' : m' = Fin.last (k + 1)
          · subst hm2'
            try fin_cases a
            try fin_cases a'
            try fin_cases c
            try fin_cases c'
            simp [caEmb_piPerm_BL, betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
              CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
              Ne.symm hne]
          ·
            try fin_cases a
            try fin_cases a'
            try fin_cases c
            try fin_cases c'
            simp [caEmb_piPerm_BL, caEmb_piPerm_fixed k hm' hm2', hm', hm2', Ne.symm hm',
              Ne.symm hm2', betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
              CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
              Ne.symm hne]
      ·
        by_cases hm' : m' = (Fin.last k).castSucc
        · subst hm'
          try fin_cases a
          try fin_cases a'
          try fin_cases c
          try fin_cases c'
          simp [caEmb_piPerm_fixed k hm hm2, caEmb_piPerm_BK, hm, hm2, Ne.symm hm, Ne.symm hm2,
            betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
            CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
            Ne.symm hne]
        · by_cases hm2' : m' = Fin.last (k + 1)
          · subst hm2'
            try fin_cases a
            try fin_cases a'
            try fin_cases c
            try fin_cases c'
            simp [caEmb_piPerm_fixed k hm hm2, caEmb_piPerm_BL, hm, hm2, Ne.symm hm, Ne.symm hm2,
              betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
              CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
              Ne.symm hne]
          ·
            try fin_cases a
            try fin_cases a'
            try fin_cases c
            try fin_cases c'
            simp [caEmb_piPerm_fixed k hm hm2, caEmb_piPerm_fixed k hm' hm2', hm, hm2, hm', hm2',
              Ne.symm hm, Ne.symm hm2, Ne.symm hm', Ne.symm hm2', betaStd, bStar, leviOne,
              coe_pairGL, coe_levi, lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk,
              Matrix.one_apply, betaTwo, rhoTwo, hne, Ne.symm hne]
  ·
    by_cases hm : m = (Fin.last k).castSucc
    · subst hm
      try fin_cases a
      try fin_cases a'
      try fin_cases c
      try fin_cases c'
      simp [caEmb_piPerm_BK, caEmb_piPerm_C, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
        lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
        Ne.symm hne]
    · by_cases hm2 : m = Fin.last (k + 1)
      · subst hm2
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_BL, caEmb_piPerm_C, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
          lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
      ·
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_fixed k hm hm2, caEmb_piPerm_C, hm, hm2, Ne.symm hm, Ne.symm hm2,
          betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
          CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
  ·
    try fin_cases a
    try fin_cases a'
    try fin_cases c
    try fin_cases c'
    simp [caEmb_piPerm_C, caEmb_piPerm_A, betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
      CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne, Ne.symm hne]
  ·
    by_cases hm' : m' = (Fin.last k).castSucc
    · subst hm'
      try fin_cases a
      try fin_cases a'
      try fin_cases c
      try fin_cases c'
      simp [caEmb_piPerm_C, caEmb_piPerm_BK, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
        lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
        Ne.symm hne]
    · by_cases hm2' : m' = Fin.last (k + 1)
      · subst hm2'
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_C, caEmb_piPerm_BL, betaStd, bStar, leviOne, coe_pairGL, coe_levi,
          lastTwo, CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
      ·
        try fin_cases a
        try fin_cases a'
        try fin_cases c
        try fin_cases c'
        simp [caEmb_piPerm_C, caEmb_piPerm_fixed k hm' hm2', hm', hm2', Ne.symm hm', Ne.symm hm2',
          betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
          CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne,
          Ne.symm hne]
  ·
    try fin_cases a
    try fin_cases a'
    try fin_cases c
    try fin_cases c'
    simp [caEmb_piPerm_C, betaStd, bStar, leviOne, coe_pairGL, coe_levi, lastTwo,
      CFSG.LieType.Steinberg.Sp.blockMat, blk, Matrix.one_apply, betaTwo, rhoTwo, hne, Ne.symm hne]

private theorem caEmb_mem_range_iff (k : ℕ) (z : BlkIdx 1 (k + 2)) :
    z ∈ Set.range (embIdx k) ↔
      z ≠ Sum.inr (Sum.inl ((Fin.last k).castSucc)) ∧
        z ≠ Sum.inr (Sum.inl (Fin.last (k + 1))) := by
  rcases z with a | m | c
  · simp [embIdx]
  · rw [caEmb_mem_range_inr_inl]
    constructor
    · intro hm
      refine ⟨?_, ?_⟩ <;> intro h
      · have hm' : m = (Fin.last k).castSucc := by simpa using h
        have := congrArg Fin.val hm'
        simp at this
        omega
      · have hm' : m = Fin.last (k + 1) := by simpa using h
        have := congrArg Fin.val hm'
        simp at this
        omega
    · rintro ⟨h1, h2⟩
      by_contra hm
      have hmle : k ≤ (m : ℕ) := Nat.le_of_not_lt hm
      have hmlt : (m : ℕ) < k + 2 := m.isLt
      have hcases : (m : ℕ) = k ∨ (m : ℕ) = k + 1 := by omega
      rcases hcases with h | h
      · have hm' : m = (Fin.last k).castSucc := by
          apply Fin.ext
          simpa using h
        exact h1 (by rw [hm'])
      · have hm' : m = Fin.last (k + 1) := by
          apply Fin.ext
          simpa using h
        exact h2 (by rw [hm'])
  · simp [embIdx]

private theorem caEmb_piPerm_image (k : ℕ) :
    piPerm k '' {i : BlkIdx 1 (k + 2) | i ≠ Sum.inl 0 ∧ i ≠ Sum.inr (Sum.inr 0)} =
      Set.range (embIdx k) := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwA, hwC⟩, rfl⟩
    rcases w with a | m | c
    · fin_cases a
      exact (hwA rfl).elim
    · by_cases hm : m = (Fin.last k).castSucc
      · subst hm
        rw [caEmb_piPerm_BK, caEmb_mem_range_iff]
        simp
      · by_cases hm2 : m = Fin.last (k + 1)
        · subst hm2
          rw [caEmb_piPerm_BL, caEmb_mem_range_iff]
          simp
        · rw [caEmb_piPerm_fixed k hm hm2, caEmb_mem_range_iff]
          constructor
          · intro h
            exact hm (by simpa using h)
          · intro h
            exact hm2 (by simpa using h)
    · fin_cases c
      exact (hwC rfl).elim
  · intro hz
    rcases z with a | m | c
    · refine ⟨Sum.inr (Sum.inl (Fin.last (k + 1))), ⟨by simp, by simp⟩, ?_⟩
      rw [caEmb_piPerm_BL]
      congr
      exact Subsingleton.elim _ _
    · obtain ⟨h1, h2⟩ := (caEmb_mem_range_iff k (Sum.inr (Sum.inl m))).mp hz
      refine ⟨Sum.inr (Sum.inl m), ⟨by simp, by simp⟩, ?_⟩
      rw [caEmb_piPerm_fixed k (by simpa using h1) (by simpa using h2)]
    · refine ⟨Sum.inr (Sum.inl ((Fin.last k).castSucc)), ⟨by simp, by simp⟩, ?_⟩
      rw [caEmb_piPerm_BK]
      congr
      exact Subsingleton.elim _ _

private theorem caEmb_map_suppGL (k : ℕ) (S : Set (BlkIdx 1 (k + 2))) :
    (CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2) S).map
        (MulAut.conj (piStd k)).toMonoidHom =
      CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2) (piPerm k '' S) := by
  have hπ : ∀ i, piPerm k (piPerm k i) = i := by
    intro i
    have h := caEmb_piPerm_mul_self k
    simpa [Equiv.Perm.mul_apply] using
      congrArg (fun e : Equiv.Perm (BlkIdx 1 (k + 2)) => e i) h
  ext x
  constructor
  · rintro hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    change CFSG.SeitzReduction.SymplecticPilot.IsSuppMat (piPerm k '' S)
      (((MulAut.conj (piStd k)) g : GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
        Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2))
    intro i j hij
    rw [MulAut.conj_apply, caEmb_conj_apply]
    have hnot : ¬ (piPerm k i ∈ S ∧ piPerm k j ∈ S) := by
      rintro ⟨hi, hj⟩
      exact hij ⟨⟨piPerm k i, hi, hπ i⟩, ⟨piPerm k j, hj, hπ j⟩⟩
    rw [hg (piPerm k i) (piPerm k j) hnot]
    simp [Matrix.one_apply, (piPerm k).injective.eq_iff]
  · intro hx
    set φ : MulAut (GL (BlkIdx 1 (k + 2)) (ZMod 2)) := MulAut.conj (piStd k)
    have hφ2 : φ * φ = 1 := by
      change MulAut.conj (piStd k) * MulAut.conj (piStd k) = 1
      rw [← map_mul, caEmb_piStd_mul_self, map_one]
    have hφφ : φ (φ x) = x := by
      have h := congrArg (fun e : MulAut (GL (BlkIdx 1 (k + 2)) (ZMod 2)) => e x) hφ2
      simpa [MulAut.mul_apply] using h
    refine Subgroup.mem_map.mpr ⟨φ x, ?_, hφφ⟩
    change CFSG.SeitzReduction.SymplecticPilot.IsSuppMat S
      (((φ x : GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
        Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2)))
    intro i j hij
    have hnot : ¬ (piPerm k i ∈ piPerm k '' S ∧ piPerm k j ∈ piPerm k '' S) := by
      rintro ⟨⟨s, hs, hsi⟩, ⟨t, ht, htj⟩⟩
      exact hij ⟨(piPerm k).injective hsi ▸ hs, (piPerm k).injective htj ▸ ht⟩
    rw [show ((φ x : GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
        Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2)) i j =
        (x : Matrix (BlkIdx 1 (k + 2)) (BlkIdx 1 (k + 2)) (ZMod 2))
          (piPerm k i) (piPerm k j) from caEmb_conj_apply k x i j]
    rw [hx (piPerm k i) (piPerm k j) hnot]
    simp [Matrix.one_apply, (piPerm k).injective.eq_iff]

private theorem caEmb_range_embGL (k : ℕ) :
    (embGL k).range =
      CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2) (Set.range (embIdx k)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact coordEmbedGL_mem_suppGL (embIdx_injective k) g
  · intro hx
    obtain ⟨g, hg⟩ := exists_coordEmbedGL_eq_of_mem_suppGL (embIdx_injective k) hx
    exact ⟨g, hg⟩

theorem map_leviB_piStd (k : ℕ) :
    (leviB (k + 2)).map (MulAut.conj (piStd k)).toMonoidHom = (embGL k).range := by
  rw [leviB_eq_suppGL, caEmb_map_suppGL, caEmb_piPerm_image, caEmb_range_embGL]

theorem centralizer_bStar (k : ℕ) :
    Subgroup.centralizer ({bStar (k + 2)} : Set (GL (BlkIdx 1 (k + 2)) (ZMod 2))) =
      (embGL k).range ⊔ Subgroup.zpowers (bStar (k + 2)) := by
  have hmap : (Subgroup.centralizer ({betaStd (k + 2)} :
        Set (GL (BlkIdx 1 (k + 2)) (ZMod 2)))).map
        (MulAut.conj (piStd k)).toMonoidHom =
      Subgroup.centralizer ({bStar (k + 2)} : Set (GL (BlkIdx 1 (k + 2)) (ZMod 2))) := by
    rw [← piStd_conj_betaStd k]
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc x * MulAut.conj (piStd k) (betaStd (k + 2))
          = MulAut.conj (piStd k) ((MulAut.conj (piStd k)).symm x) *
              MulAut.conj (piStd k) (betaStd (k + 2)) := by
            rw [MulEquiv.apply_symm_apply]
        _ = MulAut.conj (piStd k) ((MulAut.conj (piStd k)).symm x * betaStd (k + 2)) := by
            rw [map_mul]
        _ = MulAut.conj (piStd k) (betaStd (k + 2) * (MulAut.conj (piStd k)).symm x) := by
            rw [h]
        _ = MulAut.conj (piStd k) (betaStd (k + 2)) *
              MulAut.conj (piStd k) ((MulAut.conj (piStd k)).symm x) := by
            rw [map_mul]
        _ = MulAut.conj (piStd k) (betaStd (k + 2)) * x := by
            rw [MulEquiv.apply_symm_apply]
    · intro h
      have h' : x * MulAut.conj (piStd k) (betaStd (k + 2)) =
          MulAut.conj (piStd k) (betaStd (k + 2)) * x := by
        simpa [MulAut.conj_apply] using h
      calc (MulAut.conj (piStd k)).symm x * betaStd (k + 2)
          = (MulAut.conj (piStd k)).symm x *
              (MulAut.conj (piStd k)).symm
                (MulAut.conj (piStd k) (betaStd (k + 2))) := by
            rw [MulEquiv.symm_apply_apply]
        _ = (MulAut.conj (piStd k)).symm
              (x * MulAut.conj (piStd k) (betaStd (k + 2))) := by
            rw [map_mul]
        _ = (MulAut.conj (piStd k)).symm
              (MulAut.conj (piStd k) (betaStd (k + 2)) * x) := by
            rw [h']
        _ = (MulAut.conj (piStd k)).symm
              (MulAut.conj (piStd k) (betaStd (k + 2))) *
              (MulAut.conj (piStd k)).symm x := by
            rw [map_mul]
        _ = betaStd (k + 2) * (MulAut.conj (piStd k)).symm x := by
            rw [MulEquiv.symm_apply_apply]
  rw [← hmap, centralizer_betaStd (k + 2), Subgroup.map_sup,
    map_leviB_piStd k, MonoidHom.map_zpowers]
  rw [show (MulEquiv.toMonoidHom (MulAut.conj (piStd k))) (betaStd (k + 2)) =
    bStar (k + 2) from piStd_conj_betaStd k]

end CFSG.StandardType.FF81.CentA

end
