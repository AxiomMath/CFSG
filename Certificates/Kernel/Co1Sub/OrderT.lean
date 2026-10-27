module

public import Certificates.Kernel.Co1Sub.Order
public import CFSG.Certificates.Kernel.Co1Sub.OrbitSound

public section

namespace CFSG.KD.Co1Sub

open CFSG.KC.Co1Sub CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TabMatGrp CFSG.KC.Co1Fix
  CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co1.Native (co1Data)
open scoped Matrix

noncomputable abbrev chainS : Subgroup (J (co1Data ())) :=
  Subgroup.closure {g | g ∈ subG tI ∧ ∃ t < tW.length, MatP 24 (tM.getD t 0) = matOf φJ g}

theorem chainS_le : chainS ≤ subG tI := by
  rw [Subgroup.closure_le]
  rintro g ⟨hg, -⟩
  exact hg

theorem tM_length : tM.length = tW.length := (slpK_spec ch120801_chain).1

theorem chainS_fix : ∀ s ∈ chainS, vecOf x0 ᵥ* matOf φJ s = vecOf x0 := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨-, t, ht, e⟩ := hy
    have hm : tM.getD t 0 ∈ tM := by
      rw [List.getD_eq_getElem _ _ (by rw [tM_length]; exact ht)]
      exact List.getElem_mem _
    have hv : vmS (tM.getD t 0) x0 = x0 := CFSG.KC.Co1Sub.fixK_spec ch120801_fix _ hm
    calc vecOf x0 ᵥ* matOf φJ y = vecOf x0 ᵥ* MatP 24 (tM.getD t 0) := by rw [e]
      _ = vecOf (vmS (tM.getD t 0) x0) := (vecOf_vmS _ _).symm
      _ = vecOf x0 := by rw [hv]
  | one => rw [matOf_one, Matrix.vecMul_one]
  | mul y z _ _ hy hz => rw [matOf_mul, ← Matrix.vecMul_vecMul, hy, hz]
  | inv y _ hy =>
    calc vecOf x0 ᵥ* matOf φJ y⁻¹ = (vecOf x0 ᵥ* matOf φJ y) ᵥ* matOf φJ y⁻¹ := by rw [hy]
      _ = vecOf x0 := by rw [Matrix.vecMul_vecMul, ← matOf_mul, mul_inv_cancel, matOf_one,
          Matrix.vecMul_one]

theorem auxG_mem_subG {idx : List ℕ} {i : ℕ} (hi : i ∈ idx) : auxG i ∈ subG idx :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem card_chainS : 128 ≤ Nat.card chainS := by
  have h := tree_card (φ := φJ) chainS ⊥ bot_le (by decide)
    (fun s hs => by rw [Subgroup.mem_bot.1 hs, matOf_one, Matrix.vecMul_one]) ch120801_t1
    (fun i hi => by
      rw [tM_length] at hi
      obtain ⟨g, hg, e1, -⟩ := MatP_tM (subG tI) (fun i hi => auxG_mem_subG hi) i hi
      exact ⟨g, Subgroup.subset_closure ⟨hg, i, hi, e1⟩, e1⟩)
  rwa [Subgroup.card_bot, mul_one] at h

theorem card_subG_tI_ge : 16384 * Nat.card chainS ≤ Nat.card (subG tI) := by
  obtain ⟨-, hB, hK⟩ := pick_parts (idx := tI) (by decide) (subG tI) fun i hi => auxG_mem_subG hi
  exact tree_card (φ := φJ) (subG tI) chainS chainS_le (by decide) chainS_fix ch120801_t0
    fun i hi => ⟨_, hK i hi, (hB i hi).1⟩

theorem card_subG_tI : Nat.card (subG tI) = 2 ^ 21 :=
  le_antisymm (Nat.le_of_dvd (by norm_num) card_subG_tI_dvd)
    (by have := card_chainS; have := card_subG_tI_ge; omega)

end CFSG.KD.Co1Sub

end
