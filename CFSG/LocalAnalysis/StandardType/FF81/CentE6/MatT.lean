module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatSStruct
public import CFSG.LargeExtraspecial.A2ModSLc
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKLin
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWFusion
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWZero
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open Matrix

private theorem det_one_add_vecMulVec_eq (v w : Fin 6 → ZMod 2) :
    (1 + Matrix.vecMulVec v w).det = 1 + w ⬝ᵥ v := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]

private theorem exists_tv_of_isTransvec {g : SL(6, ZMod 2)} (h : IsTransvec g) :
    ∃ p q : Fin 6 → ZMod 2, p ≠ 0 ∧ q ≠ 0 ∧ q ⬝ᵥ p = 0 ∧
      g = CFSG.LargeExtraspecial.A2Mod.tv p q := by
  change Matrix.rank ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) = 1 at h
  have hg1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1 ≠ 0 := by
    intro h0
    rw [h0, Matrix.rank_zero] at h
    exact one_ne_zero h.symm
  obtain ⟨p, q, hpq⟩ :=
    CFSG.Quasithin.H13.L829NK.exists_vecMulVec_of_rank_le_one
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) h.le
  have hp0 : p ≠ 0 := by
    intro hp; apply hg1; rw [hpq, hp, Matrix.zero_vecMulVec]
  have hq0 : q ≠ 0 := by
    intro hq; apply hg1; rw [hpq, hq, Matrix.vecMulVec_zero]
  have hgmat : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 + Matrix.vecMulVec p q := by
    rw [← hpq]; abel
  have hdet : q ⬝ᵥ p = 0 := by
    have h1 : (1 + Matrix.vecMulVec p q).det = 1 := by
      rw [← hgmat, Matrix.SpecialLinearGroup.det_coe]
    rw [det_one_add_vecMulVec_eq] at h1
    simpa using h1
  refine ⟨p, q, hp0, hq0, hdet, ?_⟩
  apply Subtype.ext
  rw [CFSG.LargeExtraspecial.A2Mod.coe_tv hdet, hgmat]

private theorem stdTransvection_eq_tv :
    CFSG.Holt.SL6.stdTransvection =
      CFSG.LargeExtraspecial.A2Mod.tv (Pi.single (0 : Fin 6) (1 : ZMod 2))
        (Pi.single (5 : Fin 6) (1 : ZMod 2)) := by
  have h : (Pi.single (5 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) ⬝ᵥ
      (Pi.single (0 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) = 0 := by
    rw [dotProduct_single_one]
    simp
  apply Subtype.ext
  rw [CFSG.Holt.SL6.coe_stdTransvection, CFSG.LargeExtraspecial.A2Mod.coe_tv h,
    Matrix.single_eq_single_vecMulVec_single]

private theorem isTransvec_of_mem_Sone {s : SL(6, ZMod 2)} (hs : s ∈ Sone) (h1 : s ≠ 1) :
    IsTransvec s := by
  rw [mem_Sone_iff] at hs
  obtain ⟨h00, hrest⟩ := hs
  change Matrix.rank ((s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) = 1
  have hmat : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1 =
      Matrix.vecMulVec (Pi.single (0 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2)
        (fun j => ((s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) 0 j) := by
    ext i j
    by_cases hi : i = 0
    · subst hi; simp [Matrix.sub_apply, Matrix.vecMulVec_apply]
    · have h2 : (Pi.single (0 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) i = 0 := by
        rw [Pi.single_apply, if_neg hi]
      rw [Matrix.sub_apply, Matrix.vecMulVec_apply, h2, hrest i j hi, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
  rw [hmat]
  apply CFSG.SeitzReduction.LinearPilot.rank_vecMulVec_eq_one (n := 6)
  · intro hh; have := congrFun hh 0; simp at this
  · intro hr
    apply h1
    apply Subtype.ext
    have hz : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1 = 0 := by
      rw [hmat, hr, Matrix.vecMulVec_zero]
    rwa [sub_eq_zero] at hz

private theorem isTransvec_of_mem_Ssix {s : SL(6, ZMod 2)} (hs : s ∈ Ssix) (h1 : s ≠ 1) :
    IsTransvec s := by
  rw [mem_Ssix_iff] at hs
  obtain ⟨h55, hrest⟩ := hs
  change Matrix.rank ((s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) = 1
  have hmat : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1 =
      Matrix.vecMulVec (fun i => ((s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) i 5)
        (Pi.single (5 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) := by
    ext i j
    by_cases hj : j = 5
    · subst hj; simp [Matrix.sub_apply, Matrix.vecMulVec_apply]
    · have h2 : (Pi.single (5 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) j = 0 := by
        rw [Pi.single_apply, if_neg hj]
      rw [Matrix.sub_apply, Matrix.vecMulVec_apply, h2, hrest i j hj, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
  rw [hmat]
  apply CFSG.SeitzReduction.LinearPilot.rank_vecMulVec_eq_one (n := 6)
  · intro hr
    apply h1
    apply Subtype.ext
    have hz : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1 = 0 := by
      rw [hmat, hr, Matrix.zero_vecMulVec]
    rwa [sub_eq_zero] at hz
  · intro hh; have := congrFun hh 5; simp at this

private theorem mem_Sone_or_mem_Ssix_of_isTransvec {s : SL(6, ZMod 2)} (hs : s ∈ Sgrp)
    (h : IsTransvec s) : s ∈ Sone ∨ s ∈ Ssix := by
  obtain ⟨p, q, hp, hq, hdet, hstv⟩ := exists_tv_of_isTransvec h
  have hsmat : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 + Matrix.vecMulVec p q := by
    rw [hstv, CFSG.LargeExtraspecial.A2Mod.coe_tv hdet]
  obtain ⟨h00, h55, hmid, hcol0, hrow5⟩ := (mem_Sgrp_iff s).mp hs
  have hs_ij : ∀ i j, (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j =
      (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j + p i * q j := fun i j => by
    rw [hsmat]; simp [Matrix.add_apply, Matrix.vecMulVec_apply]
  have hpq_mid : ∀ i j : Fin 6, 1 ≤ i.val → i.val ≤ 4 → 1 ≤ j.val → j.val ≤ 4 →
      p i * q j = 0 := by
    intro i j hi1 hi4 hj1 hj4
    have h1 := hmid i j hi1 hi4 hj1 hj4
    rw [hs_ij i j, Matrix.one_apply] at h1
    have h2 : (if i = j then (1 : ZMod 2) else 0) + p i * q j =
        (if i = j then (1 : ZMod 2) else 0) + 0 := by rw [add_zero]; exact h1
    exact add_left_cancel h2
  by_cases hu : ∃ j : Fin 6, 1 ≤ j.val ∧ j.val ≤ 4 ∧
      (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) 0 j ≠ 0
  · by_cases hv : ∃ i : Fin 6, 1 ≤ i.val ∧ i.val ≤ 4 ∧
        (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) i 5 ≠ 0
    · exfalso
      obtain ⟨j, hj1, hj4, huj⟩ := hu
      obtain ⟨i, hi1, hi4, hvi⟩ := hv
      have hj0 : (0 : Fin 6) ≠ j := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      have hi5ne : i ≠ (5 : Fin 6) := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      have h0j : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) 0 j = p 0 * q j := by
        rw [hs_ij 0 j, Matrix.one_apply, if_neg hj0, zero_add]
      have hi5 : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) i 5 = p i * q 5 := by
        rw [hs_ij i 5, Matrix.one_apply, if_neg hi5ne, zero_add]
      have hp0 : p 0 ≠ 0 := fun hh => huj (by rw [h0j, hh, zero_mul])
      have hqj : q j ≠ 0 := fun hh => huj (by rw [h0j, hh, mul_zero])
      have hpi : p i ≠ 0 := fun hh => hvi (by rw [hi5, hh, zero_mul])
      exact (mul_ne_zero hpi hqj) (hpq_mid i j hi1 hi4 hj1 hj4)
    · left
      rw [mem_Sone_iff]
      refine ⟨h00, ?_⟩
      intro i j hi
      push Not at hv
      by_cases hi5 : i = 5
      · subst hi5
        by_cases hj5 : j = 5
        · subst hj5; exact h55
        · rw [hrow5 j hj5]; simp [show ¬(5 : Fin 6) = j from fun h => hj5 h.symm]
      · have hiv0 : i.val ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
        have hiv5 : i.val ≠ 5 := fun h => hi5 (Fin.ext (by simpa using h))
        have hi1 : 1 ≤ i.val := by omega
        have hi4 : i.val ≤ 4 := by omega
        by_cases hj0 : j = 0
        · subst hj0; rw [hcol0 i hi]; simp [hi]
        · by_cases hj5 : j = 5
          · subst hj5
            rw [hv i hi1 hi4]; simp [hi5]
          · have hjv0 : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
            have hjv5 : j.val ≠ 5 := fun h => hj5 (Fin.ext (by simpa using h))
            have hj1 : 1 ≤ j.val := by omega
            have hj4 : j.val ≤ 4 := by omega
            rw [hmid i j hi1 hi4 hj1 hj4]
  · right
    rw [mem_Ssix_iff]
    refine ⟨h55, ?_⟩
    intro i j hj
    push Not at hu
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hj0 : j = 0
      · subst hj0; exact h00
      · have hjv0 : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
        have hjv5 : j.val ≠ 5 := fun h => hj (Fin.ext (by simpa using h))
        have hj1 : 1 ≤ j.val := by omega
        have hj4 : j.val ≤ 4 := by omega
        rw [hu j hj1 hj4]; simp [show ¬(0 : Fin 6) = j from fun h => hj0 h.symm]
    · by_cases hi5 : i = 5
      · subst hi5
        rw [hrow5 j hj]; simp [show ¬(5 : Fin 6) = j from fun h => hj h.symm]
      · have hiv0 : i.val ≠ 0 := fun h => hi0 (Fin.ext (by simpa using h))
        have hiv5 : i.val ≠ 5 := fun h => hi5 (Fin.ext (by simpa using h))
        have hi1 : 1 ≤ i.val := by omega
        have hi4 : i.val ≤ 4 := by omega
        by_cases hj0 : j = 0
        · subst hj0; rw [hcol0 i hi0]; simp [hi0]
        · have hjv0 : j.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
          have hjv5 : j.val ≠ 5 := fun h => hj (Fin.ext (by simpa using h))
          have hj1 : 1 ≤ j.val := by omega
          have hj4 : j.val ≤ 4 := by omega
          rw [hmid i j hi1 hi4 hj1 hj4]

theorem isConj_of_isTransvec {g : SL(6, ZMod 2)} (h : IsTransvec g) :
    IsConj CFSG.Holt.SL6.stdTransvection g := by
  obtain ⟨p, q, hp, hq, hdet, hgtv⟩ := exists_tv_of_isTransvec h
  have he0 : (Pi.single (0 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) ≠
      (0 : Fin 6 → ZMod 2) := by
    intro hh; have := congrFun hh 0; simp at this
  have he5 : (Pi.single (5 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) ≠
      (0 : Fin 6 → ZMod 2) := by
    intro hh; have := congrFun hh 5; simp at this
  have h' : (Pi.single (5 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) ⬝ᵥ
      (Pi.single (0 : Fin 6) (1 : ZMod 2) : Fin 6 → ZMod 2) = 0 := by
    rw [dotProduct_single_one]; simp
  rw [hgtv, stdTransvection_eq_tv]
  exact (CFSG.LargeExtraspecial.A2Mod.isConj_tv (n := 6)
    (v := p) (φ := q) (w := Pi.single (0 : Fin 6) (1 : ZMod 2))
    (ψ := Pi.single (5 : Fin 6) (1 : ZMod 2)) hp hq hdet he0 he5 h').symm

theorem isTransvec_iff_of_mem_Sgrp {s : SL(6, ZMod 2)} (hs : s ∈ Sgrp) (h1 : s ≠ 1) :
    IsTransvec s ↔ s ∈ Sone ∨ s ∈ Ssix := by
  constructor
  · intro h; exact mem_Sone_or_mem_Ssix_of_isTransvec hs h
  · rintro (h | h)
    · exact isTransvec_of_mem_Sone h h1
    · exact isTransvec_of_mem_Ssix h h1

theorem eq_Sone_or_eq_Ssix_of_transvec {E : Subgroup SL(6, ZMod 2)} (hE : E ≤ Sgrp)
    (hcard : Nat.card E = 32) (hT : ∀ g ∈ E, g ≠ 1 → IsTransvec g) : E = Sone ∨ E = Ssix := by
  have hUnion : ∀ g ∈ E, g ∈ Sone ∨ g ∈ Ssix := by
    intro g hg
    by_cases hg1 : g = 1
    · left; rw [hg1]; exact Sone.one_mem
    · exact (isTransvec_iff_of_mem_Sgrp (hE hg) hg1).mp (hT g hg hg1)
  have hsub : E ≤ Sone ∨ E ≤ Ssix := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hSone, hSsix⟩ := hcon
    obtain ⟨x, hxE, hxSone⟩ := Set.not_subset.mp hSone
    obtain ⟨y, hyE, hySsix⟩ := Set.not_subset.mp hSsix
    have hxSsix : x ∈ Ssix := (hUnion x hxE).resolve_left hxSone
    have hySone : y ∈ Sone := (hUnion y hyE).resolve_right hySsix
    have hxyE : x * y ∈ E := E.mul_mem hxE hyE
    rcases hUnion (x * y) hxyE with h | h
    · apply hxSone
      have hx : x = (x * y) * y⁻¹ := by group
      rw [hx]
      exact Sone.mul_mem h (Sone.inv_mem hySone)
    · apply hySsix
      have hy : y = x⁻¹ * (x * y) := by group
      rw [hy]
      exact Ssix.mul_mem (Ssix.inv_mem hxSsix) h
  rcases hsub with h | h
  · left; exact Subgroup.eq_of_le_of_card_ge h (by rw [card_Sone, hcard])
  · right; exact Subgroup.eq_of_le_of_card_ge h (by rw [card_Ssix, hcard])

end CFSG.StandardType.FF81.CentE6
