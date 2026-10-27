module

public import CFSG.Walter.Ree.Bombieri.Stage2Data
import CFSG.Walter.Ree.Bombieri.Stage2Cert1
import CFSG.Walter.Ree.Bombieri.Stage2Cert2
import CFSG.Walter.Ree.Bombieri.Stage2Cert3
import CFSG.Walter.Ree.Bombieri.Stage2Cert4
import CFSG.Walter.Ree.Bombieri.Stage2Cert5
import CFSG.Walter.Ree.Bombieri.Stage2Cert6

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

theorem Hs_ne_zero_of_mem
    {e : Entry} (he : e ∈ allBatches) :
    Elim.Hs e.k e.lam e.neg ≠ 0 := by
  simp only [allBatches, List.mem_append] at he
  rcases he with (((((he | he) | he) | he) | he) | he) | he
  · exact batch9_1_sound e he
  · exact batch9_2_sound e he
  · exact batch9_3_sound e he
  · exact batch9_4_sound e he
  · exact batch9_5_sound e he
  · exact batch8_sound e he
  · exact batch7_sound e he

end Spec

@[expose] def stage2Case (k lam : ℕ) (neg : Bool) : Bool :=
  k ≤ 3 && 1 ≤ lam && lam ≤ 9 && !(k % 2 == 1 && lam % 2 == 0) && !(k == 1 && lam == 1 && !neg)

@[expose] def coverCheck : Bool :=
  (List.range 4).all fun k => (List.range 10).all fun lam => [false, true].all fun neg =>
    !stage2Case k lam neg || (Spec.allBatches.map Spec.Entry.key).contains (k, lam, neg)

theorem coverCheck_eq : coverCheck = true := by decide +kernel

theorem stage2Case_mem {k lam : ℕ} {neg : Bool} (hk : k ≤ 3) (hlam : lam ≤ 9)
    (h : stage2Case k lam neg = true) : (k, lam, neg) ∈ Spec.allBatches.map Spec.Entry.key := by
  have hc := coverCheck_eq
  simp only [coverCheck, List.all_eq_true, List.mem_range] at hc
  have h2 := hc k (by omega) lam (by omega) neg (by cases neg <;> simp)
  rw [h, Bool.not_true, Bool.false_or] at h2
  exact List.contains_iff_mem.mp h2

theorem Hs_ne_zero
    {k lam : ℕ} {neg : Bool} (hk : k ≤ 3) (hlam : lam ≤ 9)
    (h : stage2Case k lam neg = true) : Elim.Hs k lam neg ≠ 0 := by
  obtain ⟨e, he, hkey⟩ := List.mem_map.mp (stage2Case_mem hk hlam h)
  simp only [Spec.Entry.key, Prod.mk.injEq] at hkey
  obtain ⟨rfl, rfl, rfl⟩ := hkey
  exact Spec.Hs_ne_zero_of_mem he

theorem Elim.H_ne_zero :
    Elim.H ≠ 0 :=
  Elim.H_ne_zero_of_Hs_ne_zero (Hs_ne_zero (k := 0) (lam := 1) (neg := false) (by norm_num)
    (by norm_num) (by decide))

end CFSG.Walter.Ree.Bombieri
