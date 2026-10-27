module

public import CFSG.Sporadic.Fi24.ExtCentralizer
public import CFSG.Sporadic.Fi24.OctadData

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem conj_mem_D24
    (r : R) {x : R} (hx : x ∈ D24) : r * x * r⁻¹ ∈ D24 :=
  (show IsConj tR x from hx).trans (isConj_iff.2 ⟨r, rfl⟩)

@[expose] noncomputable def conjPt
    (r : R) (k : Fin 306936) : Fin 306936 :=
  clsEquiv.symm ⟨r * cls k * r⁻¹, conj_mem_D24 r (cls_mem k)⟩

theorem cls_conjPt
    (r : R) (k : Fin 306936) : cls (conjPt r k) = r * cls k * r⁻¹ := by
  rw [← clsEquiv_apply]
  unfold conjPt
  rw [Equiv.apply_symm_apply]

@[expose, instance_reducible] noncomputable def rAction :
    MulAction R (Fin 306936) where
  smul := conjPt
  one_smul k := cls_injective (by
    show cls (conjPt 1 k) = cls k
    rw [cls_conjPt, one_mul, inv_one, mul_one])
  mul_smul r s k := cls_injective (by
    show cls (conjPt (r * s) k) = cls (conjPt r (conjPt s k))
    rw [cls_conjPt, cls_conjPt, cls_conjPt, mul_inv_rev]
    simp only [mul_assoc])

attribute [local instance] rAction

theorem cls_smul_R
    (r : R) (k : Fin 306936) : cls (r • k) = r * cls k * r⁻¹ := cls_conjPt r k

theorem jR_smul
    (g : J) (k : Fin 306936) : jR g • k = g • k :=
  cls_injective (by rw [cls_smul_R, cls_smul])

theorem tR_smul
    (k : Fin 306936) : tR • k = tPerm k :=
  cls_injective (by rw [cls_smul_R, cls_tPerm, tR_inv])

theorem tR_smul_root :
    tR • root = root := by rw [tR_smul, tPerm_root]

theorem cls_eq_conj_of_smul_root
    {x : R} {k : Fin 306936} (h : x • root = k) :
    cls k = x * tR * x⁻¹ := by
  rw [← h, cls_smul_R, cls_root]

theorem eq_one_of_smul_eq
    {x : R} (h : ∀ k : Fin 306936, x • k = k) : x = 1 := by
  have hc : ∀ y ∈ D24, y * x = x * y := by
    intro y hy
    obtain ⟨k, rfl⟩ := exists_cls hy
    have e := cls_smul_R x k
    rw [h k] at e
    calc cls k * x = x * cls k * x⁻¹ * x := by rw [← e]
      _ = x * cls k := by group
  have hcen : x ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure D24 := by rw [closure_D24]; trivial
    induction hg using Subgroup.closure_induction with
    | mem y hy => exact hc y hy
    | one => rw [one_mul, mul_one]
    | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
    | inv y _ hy =>
      calc y⁻¹ * x = y⁻¹ * (x * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * x) * y⁻¹ := by rw [hy]
        _ = x * y⁻¹ := by group
  rw [center_R, Subgroup.mem_bot] at hcen
  exact hcen

theorem idx_jR
    (g : J) (i : ℕ) : idx 306936 (jR g) i = idx 306936 g i := by
  by_cases hi : i < 306936
  · rw [idx_of_lt _ hi, idx_of_lt _ hi, jR_smul]
  · rw [idx_of_not_lt _ hi, idx_of_not_lt _ hi]

theorem rep_jR
    {P : Table} {g : J} (h : Rep 306936 P g) : Rep 306936 P (jR g) := by
  intro i hi
  rw [h i hi, idx_jR]

theorem idx_tR
    {i : ℕ} (hi : i < 306936) : idx 306936 tR i = (tPerm ⟨i, hi⟩).val := by
  rw [idx_of_lt _ hi, tR_smul]

theorem tPerm_val_of_tPOK
    {tA tB tP : Table} (hA : Rep 306936 tA nA) (hB : Rep 306936 tB nB)
    (h : tPOK orb tA tB tP = true) : ∀ p (hp : p < 306936), ap tP p = (tPerm ⟨p, hp⟩).val := by
  unfold tPOK at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h0, hall⟩ := h
  have hstep := allIn_eq_true.1 hall
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · rw [h0]
      exact (congrArg Fin.val tPerm_root).symm
    obtain ⟨hlt, hcase⟩ := tree_facts p hp hpos
    have hq : ap orb.par p < 306936 := lt_trans hlt hp
    have hs := hstep p hpos hp
    rw [beq_iff_eq] at hs
    rw [hs, ih _ hlt hq]
    rcases hcase with ⟨hl, ha⟩ | ⟨hl, hb⟩
    · rw [hl, ite_eq_left (by decide)]
      have e : a • (⟨ap orb.par p, hq⟩ : Fin 306936) = ⟨p, hp⟩ := by
        apply Fin.ext
        rw [← idx_of_lt a hq, ← rep_alpha _ hq, ha]
      rw [hA _ (tPerm _).isLt, idx_of_lt nA (tPerm _).isLt, ← e, tPerm_smul, tAut_a]
    · rw [hl, ite_eq_right (by decide)]
      have e : b • (⟨ap orb.par p, hq⟩ : Fin 306936) = ⟨p, hp⟩ := by
        apply Fin.ext
        rw [← idx_of_lt b hq, ← rep_beta _ hq, hb]
      rw [hB _ (tPerm _).isLt, idx_of_lt nB (tPerm _).isLt, ← e, tPerm_smul, tAut_b]

theorem rep_tR_of_tPOK
    {tA tB tP : Table} (hA : Rep 306936 tA nA) (hB : Rep 306936 tB nB)
    (h : tPOK orb tA tB tP = true) : Rep 306936 tP tR := by
  intro i hi
  rw [tPerm_val_of_tPOK hA hB h i hi, idx_tR hi]

theorem rep_letterJ {z : ℤ} (hz : z.natAbs ≤ 13) :
    Rep 306936 (letterJ letters z) (genLetterG z) := by
  have hsz : letters.size = 26 := by rw [letters_size, chainWords_size]
  unfold letterJ genLetterG
  by_cases hpos : 0 < z
  · rw [ite_eq_left hpos, ite_eq_left hpos]
    have h := rep_pairG_all (2 * (z.natAbs - 1)) (by omega)
    have e : pairG gs (2 * (z.natAbs - 1)) = gs (z.natAbs - 1) := by
      unfold pairG
      rw [ite_eq_left (by omega), show 2 * (z.natAbs - 1) / 2 = z.natAbs - 1 by omega]
    rwa [e] at h
  · rw [ite_eq_right hpos, ite_eq_right hpos]
    have h := rep_pairG_all (2 * (z.natAbs - 1) + 1) (by omega)
    have e : pairG gs (2 * (z.natAbs - 1) + 1) = (gs (z.natAbs - 1))⁻¹ := by
      unfold pairG
      rw [ite_eq_right (by omega), show (2 * (z.natAbs - 1) + 1) / 2 = z.natAbs - 1 by omega]
    rwa [e] at h

theorem rep_nA :
    Rep 306936 (wordT nPts (letterJ letters) normWords[0]!) nA :=
  Rep.wordT (by norm_num) _ fun z hz => rep_letterJ (normWords_letters (by norm_num) z hz).2

theorem rep_nB :
    Rep 306936 (wordT nPts (letterJ letters) normWords[1]!) nB :=
  Rep.wordT (by norm_num) _ fun z hz => rep_letterJ (normWords_letters (by norm_num) z hz).2

@[expose] noncomputable def genR
    (z : ℤ) : R := if z.natAbs = 14 then tR else jR (genLetterG z)

theorem rep_letterR
    {tP : Table} (htP : Rep 306936 tP tR) {z : ℤ} (hz : z.natAbs ≤ 14) :
    Rep 306936 (letterR letters tP z) (genR z) := by
  unfold letterR genR
  by_cases h14 : z.natAbs = 14
  · rw [ite_eq_left h14, ite_eq_left h14]
    exact htP
  · rw [ite_eq_right h14, ite_eq_right h14]
    exact rep_jR (rep_letterJ (by omega))

theorem rep_wordT_R
    {tP : Table} (htP : Rep 306936 tP tR) {w : List ℤ}
    (hw : ∀ z ∈ w, z.natAbs ≤ 14) :
    Rep 306936 (wordT nPts (letterR letters tP) w) (wordG genR w) :=
  Rep.wordT (by norm_num) w fun z hz => rep_letterR htP (hw z hz)

theorem rep_conjTab
    {tP W : Table} (htP : Rep 306936 tP tR) {x : R} (hW : Rep 306936 W x)
    (hinv : invOK nPts W (invT nPts W) = true) {k : Fin 306936} (hk : ap W 0 = k.val) :
    Rep 306936 (conjTab tP W) (cls k) := by
  have hroot : x • root = k := by
    apply Fin.ext
    rw [← hk, hW 0 (by norm_num), idx_of_lt x (by norm_num)]
  rw [cls_eq_conj_of_smul_root hroot, mul_assoc]
  exact hW.compT (htP.compT (Rep.inv_of_invOK hW hinv))

end CFSG.Sporadic.Fi24
