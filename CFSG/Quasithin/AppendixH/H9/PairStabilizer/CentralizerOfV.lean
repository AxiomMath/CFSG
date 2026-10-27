module

public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.LeviEmbedding

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.PairStab

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH.AutPair

variable {m : ℕ}

theorem pairVec_ez_mul_pairVec_ez :
    pairVec (ez m) 0 * pairVec 0 (ez m) = pairVec (ez m) (ez m) := by
  rw [pairVec_mul]; simp

theorem mem_centSub_zpowers_iff {V : Type*} [CommGroup V] {g : MulAut V} {v : V} :
    g ∈ centSub (Subgroup.zpowers v) ↔ g v = v := by
  rw [mem_centSub]
  constructor
  · intro h; exact h v (Subgroup.mem_zpowers v)
  · intro h u hu
    rw [Subgroup.mem_zpowers_iff] at hu
    obtain ⟨k, rfl⟩ := hu
    rw [map_zpow, h]

theorem mem_centSub_zpowers_sup_iff {V : Type*} [CommGroup V] {g : MulAut V} {v w : V} :
    g ∈ centSub (Subgroup.zpowers v ⊔ Subgroup.zpowers w) ↔ g v = v ∧ g w = w := by
  constructor
  · intro h
    exact ⟨(mem_centSub.1 h) v (Subgroup.mem_sup_left (Subgroup.mem_zpowers v)),
      (mem_centSub.1 h) w (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))⟩
  · rintro ⟨hv, hw⟩
    have h1 : g ∈ centSub (Subgroup.zpowers v) := mem_centSub_zpowers_iff.2 hv
    have h2 : g ∈ centSub (Subgroup.zpowers w) := mem_centSub_zpowers_iff.2 hw
    rw [mem_centSub]
    intro u hu
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, (mem_centSub.1 h1) y hy, (mem_centSub.1 h2) z hz]

@[expose] noncomputable def leviAct (m : ℕ) : GL (Fin m) (ZMod 2) →* MulAut (PairN (m + 1)) :=
  (pairActN (m + 1)).comp (levi m)

theorem leviAct_apply (B : GL (Fin m) (ZMod 2)) :
    leviAct m B = pairActN (m + 1) (levi m B) := rfl

theorem leviAct_injective : Function.Injective (leviAct m) := by
  exact pairActN_injective.comp levi_injective

theorem leviAct_mem_Lg (B : GL (Fin m) (ZMod 2)) : leviAct m B ∈ Lg (m + 1) := by
  exact pairActN_mem_Lg _

theorem leviAct_pairVec_self (B : GL (Fin m) (ZMod 2)) :
    leviAct m B (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) := by
  rw [leviAct_apply, pairActN_pairVec, levi_mulVec_ez, dualGLn_levi, levi_mulVec_ez]

theorem leviAct_pairVec_ez_zero (B : GL (Fin m) (ZMod 2)) :
    leviAct m B (pairVec (ez m) 0) = pairVec (ez m) 0 := by
  rw [leviAct_apply, pairActN_pairVec, levi_mulVec_ez, Matrix.mulVec_zero]

theorem leviAct_pairVec_zero_ez (B : GL (Fin m) (ZMod 2)) :
    leviAct m B (pairVec 0 (ez m)) = pairVec 0 (ez m) := by
  rw [leviAct_apply, pairActN_pairVec, Matrix.mulVec_zero, dualGLn_levi, levi_mulVec_ez]

theorem swapN_pairVec_self {n : ℕ} (a : Fin n → ZMod 2) :
    swapN n (pairVec a a) = pairVec a a := by
  rw [swapN_pairVec]

theorem exists_levi_of_pairActN_fix {A : GL (Fin (m + 1)) (ZMod 2)}
    (h : pairActN (m + 1) A (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m)) :
    ∃ B : GL (Fin m) (ZMod 2), A = levi m B := by
  rw [pairActN_pairVec, pairVec_inj] at h
  exact exists_eq_levi h.1 h.2

theorem Lg_inf_centSub_eq_range :
    Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) = (leviAct m).range := by
  ext g
  constructor
  · rintro ⟨hL, hfix⟩
    obtain ⟨A, rfl⟩ := mem_Lg_iff.1 hL
    obtain ⟨B, rfl⟩ := exists_levi_of_pairActN_fix (mem_centSub_zpowers_iff.1 hfix)
    exact ⟨B, rfl⟩
  · rintro ⟨B, rfl⟩
    exact ⟨leviAct_mem_Lg B, mem_centSub_zpowers_iff.2 (leviAct_pairVec_self B)⟩

theorem mem_Mv_iff {g : MulAut (PairN (m + 1))} :
    g ∈ Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) ↔
      (∃ B : GL (Fin m) (ZMod 2), g = leviAct m B) ∨
        ∃ B : GL (Fin m) (ZMod 2), g = leviAct m B * swapN (m + 1) := by
  refine Subgroup.mem_inf.trans ?_
  constructor
  · rintro ⟨hMg, hfix⟩
    have hfix' : g (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) := mem_centSub_zpowers_iff.1 hfix
    rcases mem_Mg_iff.1 hMg with hL | ⟨A, rfl⟩
    · obtain ⟨A, rfl⟩ := mem_Lg_iff.1 hL
      obtain ⟨B, rfl⟩ := exists_levi_of_pairActN_fix hfix'
      exact Or.inl ⟨B, rfl⟩
    · have h2 : pairActN (m + 1) A (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) := by
        have : (pairActN (m + 1) A * swapN (m + 1)) (pairVec (ez m) (ez m)) =
            pairActN (m + 1) A (pairVec (ez m) (ez m)) := by
          rw [MulAut.mul_apply, swapN_pairVec_self]
        rw [← this]; exact hfix'
      obtain ⟨B, rfl⟩ := exists_levi_of_pairActN_fix h2
      exact Or.inr ⟨B, rfl⟩
  · rintro (⟨B, rfl⟩ | ⟨B, rfl⟩)
    · exact ⟨mem_Mg_iff.2 (Or.inl (leviAct_mem_Lg B)),
        mem_centSub_zpowers_iff.2 (leviAct_pairVec_self B)⟩
    · refine ⟨mem_Mg_iff.2 (Or.inr ⟨levi m B, rfl⟩), mem_centSub_zpowers_iff.2 ?_⟩
      change leviAct m B (swapN (m + 1) (pairVec (ez m) (ez m))) = pairVec (ez m) (ez m)
      rw [swapN_pairVec_self]
      exact leviAct_pairVec_self B

theorem swapN_mul_leviAct (X : GL (Fin m) (ZMod 2)) :
    swapN (m + 1) * leviAct m X = leviAct m (dualGLn m X) * swapN (m + 1) := by
  rw [leviAct_apply, leviAct_apply, swapN_mul_pairActN, dualGLn_levi]

@[expose] noncomputable def tInv (m : ℕ) : MulAut (PairN (m + 1)) :=
  leviAct m (revGL m) * swapN (m + 1)

theorem tInv_sq : tInv m ^ 2 = 1 := by
  have hJ : leviAct m (revGL m * revGL m) = 1 := by rw [revGL_mul_self, map_one]
  calc tInv m ^ 2 = leviAct m (revGL m) * swapN (m + 1) * (leviAct m (revGL m) * swapN (m + 1)) := by
        rw [pow_two]; rfl
    _ = leviAct m (revGL m) * (swapN (m + 1) * leviAct m (revGL m)) * swapN (m + 1) := by group
    _ = leviAct m (revGL m) * (leviAct m (dualGLn m (revGL m)) * swapN (m + 1)) * swapN (m + 1) := by
        rw [swapN_mul_leviAct]
    _ = leviAct m (revGL m * revGL m) * (swapN (m + 1) * swapN (m + 1)) := by
        rw [dualGLn_revGL, map_mul]; group
    _ = 1 := by rw [hJ, swapN_mul_self, one_mul]

theorem tInv_mem_Mg : tInv m ∈ Mg (m + 1) := by
  exact outer_mem_Mg (levi m (revGL m))

theorem tInv_not_mem_Lg : tInv m ∉ Lg (m + 1) := by
  exact outer_not_mem_Lg (Nat.succ_pos m) (levi m (revGL m))

theorem tInv_apply_v1 : tInv m (pairVec (ez m) 0) = pairVec 0 (ez m) := by
  rw [tInv, MulAut.mul_apply, swapN_pairVec, leviAct_pairVec_zero_ez]

theorem tInv_apply_v2 : tInv m (pairVec 0 (ez m)) = pairVec (ez m) 0 := by
  rw [tInv, MulAut.mul_apply, swapN_pairVec, leviAct_pairVec_ez_zero]

theorem tInv_apply_v : tInv m (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) := by
  rw [tInv, MulAut.mul_apply, swapN_pairVec_self, leviAct_pairVec_self]

theorem tInv_mem_Mv :
    tInv m ∈ Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) := by
  exact ⟨tInv_mem_Mg, mem_centSub_zpowers_iff.2 tInv_apply_v⟩

theorem tInv_mul_leviAct_mul_inv (B : GL (Fin m) (ZMod 2)) :
    tInv m * leviAct m B * (tInv m)⁻¹ = leviAct m (revGL m * dualGLn m B * revGL m) := by
  have hinv : (tInv m)⁻¹ = tInv m :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact tInv_sq)
  rw [hinv]
  calc tInv m * leviAct m B * tInv m
      = leviAct m (revGL m) * (swapN (m + 1) * leviAct m B) * leviAct m (revGL m) * swapN (m + 1) := by
        rw [tInv]; group
    _ = leviAct m (revGL m) * (leviAct m (dualGLn m B) * swapN (m + 1)) * leviAct m (revGL m) *
          swapN (m + 1) := by rw [swapN_mul_leviAct]
    _ = leviAct m (revGL m) * leviAct m (dualGLn m B) * (swapN (m + 1) * leviAct m (revGL m)) *
          swapN (m + 1) := by group
    _ = leviAct m (revGL m) * leviAct m (dualGLn m B) *
          (leviAct m (dualGLn m (revGL m)) * swapN (m + 1)) * swapN (m + 1) := by
        rw [swapN_mul_leviAct]
    _ = leviAct m (revGL m * dualGLn m B * revGL m) * (swapN (m + 1) * swapN (m + 1)) := by
        rw [dualGLn_revGL, map_mul, map_mul]; group
    _ = leviAct m (revGL m * dualGLn m B * revGL m) := by rw [swapN_mul_self, mul_one]

theorem leviAct_mul_swapN_eq (B : GL (Fin m) (ZMod 2)) :
    leviAct m B * swapN (m + 1) = leviAct m (B * revGL m) * tInv m := by
  have hJ : leviAct m (revGL m * revGL m) = 1 := by rw [revGL_mul_self, map_one]
  calc leviAct m B * swapN (m + 1)
      = leviAct m B * leviAct m (revGL m * revGL m) * swapN (m + 1) := by rw [hJ, mul_one]
    _ = leviAct m (B * revGL m) * tInv m := by rw [tInv, map_mul, map_mul]; group

end CFSG.ASVolI.ChH.PairStab
