module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H16
public import CFSG.Quasithin.Vol2.Ch10SecQ9H19

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

theorem bot_smul {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))) (v : Fin (m + k) → ZMod 2)
    (i : Fin k) : (g • v) (Fin.natAdd m i) =
      (botB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *ᵥ
        (fun j => v (Fin.natAdd m j))) i := by
  rw [smul_eq_mulVec']
  simp only [mulVec, dotProduct, botB, submatrix_apply]
  rw [Fin.sum_univ_add]
  have h1 : ∑ a : Fin m, (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) (Fin.natAdd m i)
      (Fin.castAdd k a) * v (Fin.castAdd k a) = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hg i a, zero_mul]
  rw [h1, zero_add]

theorem top_smul_of_mem {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    {v : Fin (m + k) → ZMod 2} (hv : v ∈ stdE (m + k) m) (i : Fin m) :
    (g • v) (Fin.castAdd k i) =
      (topB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *ᵥ
        (fun j => v (Fin.castAdd k j))) i := by
  rw [smul_eq_mulVec']
  simp only [mulVec, dotProduct, topB, submatrix_apply]
  rw [Fin.sum_univ_add]
  have h2 : ∑ b : Fin k, (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) (Fin.castAdd k i)
      (Fin.natAdd m b) * v (Fin.natAdd m b) = 0 :=
    Finset.sum_eq_zero fun b _ => by
      rw [hv (Fin.natAdd m b) (by simp), mul_zero]
  rw [h2, add_zero]

theorem smul_eq_of_topB_one {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))
    (ht : topB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1)
    {v : Fin (m + k) → ZMod 2} (hv : v ∈ stdE (m + k) m) : g • v = v := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [top_smul_of_mem hv, ht, one_mulVec]
  · rw [bot_smul hg, hv (Fin.natAdd m b) (by simp)]
    have hz : (fun j => v (Fin.natAdd m j)) = 0 := funext fun j => hv _ (by simp)
    rw [hz, mulVec_zero]
    rfl

theorem smul_add_mem_of_botB_one {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))
    (hb : botB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1)
    (v : Fin (m + k) → ZMod 2) : g • v + v ∈ stdE (m + k) m := by
  intro i hi
  obtain ⟨b, rfl⟩ : ∃ b : Fin k, i = Fin.natAdd m b :=
    ⟨⟨(i : ℕ) - m, by omega⟩, Fin.ext (by simp; omega)⟩
  rw [Pi.add_apply, bot_smul hg, hb, one_mulVec]
  exact zmod2_add_self _

theorem presStd_of_smul_mem {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : ∀ j : Fin m, g • Pi.single (Fin.castAdd k j) (1 : ZMod 2) ∈ stdE (m + k) m) :
    PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) := by
  intro i j
  have h := hg j (Fin.natAdd m i) (by simp)
  rwa [smul_eq_mulVec', mulVec_single_one] at h

theorem castAdd_mem_stdE (j : Fin m) :
    Pi.single (Fin.castAdd k j) (1 : ZMod 2) ∈ stdE (m + k) m :=
  single_mem_stdE (by simp)

theorem card_eq_ker_mul_range {H G' : Type*} [Group H] [Group G'] [Finite H] (f : H →* G') :
    Nat.card H = Nat.card f.ker * Nat.card f.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
