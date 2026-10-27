module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXME
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXMG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

theorem w16g_three_tetracode_step (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1)
    (hQ3 : Nat.card ↥Q = 3) (he : (s13Supp X Q).ncard = 3)
    (hov : ∃ a ∈ A,
      (s13Supp X (Q.map (MulAut.conj a).toMonoidHom) ∩ s13Supp X Q).ncard = 2) :
    ∃ L : Subgroup (MulAut W), L ≤ X ∧ Q ≤ L ∧
      IsElemAbelianOfRank 3 2 ↥L ∧ rk ↥(commSub ⊤ L) = 8 ∧
      (∀ x ∈ L, x ≠ 1 → rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6) ∧
      sSupIndep (conjSubs A (commSub ⊤ L)) ∧
      L = s13XSupp X (s13Supp X L) := by
  obtain ⟨a, lam, q, r, u₁, u₂, c, d, F⟩ := w16g_tetra_frame h hQ3 he hov
  have hp3 : Nat.Prime 3 := by norm_num
  have hLX : Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W) ≤ X :=
    sup_le (Subgroup.zpowers_le.mpr q.2) (Subgroup.zpowers_le.mpr r.2)
  obtain ⟨hrank, hrk8, hrk6⟩ := w16g_tetra_ranks h hH0 hQ3 he F
  have hsupp := w16g_tetra_supp h hH0 hQ3 he F
  have hXD := w16g_tetra_XD h hH0 hQ3 he F
  have hblocks := w16g_tetra_blocks h hH0 hQ3 he F
  refine ⟨Subgroup.zpowers (q : MulAut W) ⊔ Subgroup.zpowers (r : MulAut W), hLX, ?_, hrank, hrk8,
    hrk6, ?_, ?_⟩
  · rw [F.hQq]
    exact le_sup_left
  · exact sSupIndep_conjSubs_of_s13Supp h.hW hp3 (by norm_num) h.hXe h.hXA hLX hblocks
  · rw [hsupp, hXD]

end CFSG.LocalAnalysis.WeakClosure81
