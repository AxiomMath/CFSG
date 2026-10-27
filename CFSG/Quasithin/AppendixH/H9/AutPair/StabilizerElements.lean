module

public import CFSG.Quasithin.AppendixH.H9.SylowModel
public import CFSG.Quasithin.AppendixH.H9.AutPair.LeviEmbedding

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.AutPair

open CFSG.Quasithin CFSG.Open

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

theorem pairActN_levi_pairVec (B : GL (Fin m) (ZMod 2)) :
    pairActN (m + 1) (levi m B) (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) := by
  simp only [ez]
  rw [pairActN_pairVec, levi_mulVec_single, dualGLn_levi, levi_mulVec_single]

theorem swapN_pairVec_self {n : ℕ} (a : Fin n → ZMod 2) :
    swapN n (pairVec a a) = pairVec a a := by
  rw [swapN_pairVec]

theorem exists_levi_of_pairActN_fix {A : GL (Fin (m + 1)) (ZMod 2)}
    (h : pairActN (m + 1) A (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m)) :
    ∃ B : GL (Fin m) (ZMod 2), A = levi m B := by
  rw [pairActN_pairVec, pairVec_inj] at h
  exact exists_eq_levi h.1 h.2

theorem mem_Mv_iff {g : MulAut (PairN (m + 1))} :
    g ∈ Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0 * pairVec 0 (ez m))) ↔
      (∃ B : GL (Fin m) (ZMod 2), g = pairActN (m + 1) (levi m B)) ∨
        ∃ B : GL (Fin m) (ZMod 2), g = pairActN (m + 1) (levi m B) * swapN (m + 1) := by
  have hfix : g ∈ centSub (Subgroup.zpowers (pairVec (ez m) 0 * pairVec 0 (ez m))) ↔
      g (pairVec (ez m) (ez m)) = pairVec (ez m) (ez m) := by
    rw [pairVec_ez_mul_pairVec_ez]
    exact mem_centSub_zpowers_iff
  refine Subgroup.mem_inf.trans ((and_congr_right fun _ => hfix).trans ?_)
  rw [mem_Mg_iff]
  constructor
  · rintro ⟨hMg, hfix⟩
    rcases hMg with hL | ⟨A, rfl⟩
    · obtain ⟨A, rfl⟩ := mem_Lg_iff.1 hL
      obtain ⟨B, rfl⟩ := exists_levi_of_pairActN_fix hfix
      exact Or.inl ⟨B, rfl⟩
    · obtain ⟨B, rfl⟩ := exists_levi_of_pairActN_fix
        (by simpa [swapN_pairVec_self] using hfix : pairActN (m + 1) A (pairVec (ez m) (ez m)) =
          pairVec (ez m) (ez m))
      exact Or.inr ⟨B, rfl⟩
  · rintro (⟨B, rfl⟩ | ⟨B, rfl⟩)
    · exact ⟨Or.inl (pairActN_mem_Lg _), pairActN_levi_pairVec B⟩
    · exact ⟨Or.inr ⟨levi m B, rfl⟩, by simp [swapN_pairVec_self, pairActN_levi_pairVec B]⟩

theorem swapN_mul_pairActN_levi (X : GL (Fin m) (ZMod 2)) :
    swapN (m + 1) * pairActN (m + 1) (levi m X) =
      pairActN (m + 1) (levi m (dualGLn m X)) * swapN (m + 1) := by
  rw [swapN_mul_pairActN, dualGLn_levi]

end CFSG.ASVolI.ChH.AutPair
