module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

theorem qtwoStdWin_commute {m a b k l : ℕ} (ha : a + k ≤ m + 1) (hb : b + l ≤ m + 1)
    (hab : a + k ≤ b ∨ b + l ≤ a) (A : Su K 2 1 k) (B : Su K 2 1 l) :
    qtwoStdWin (F := F) (K := K) m a k ha A * qtwoStdWin (F := F) (K := K) m b l hb B =
      qtwoStdWin (F := F) (K := K) m b l hb B * qtwoStdWin (F := F) (K := K) m a k ha A := by
  simp only [qtwoStdWin, MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, blockEmb_comm ha hb hab]

theorem qtwoStdWin_commute_tau (E : QuadExt F K (unitaryInvolution K 2 1)) {m a k : ℕ}
    (hak : a + k ≤ m) (A : Su K 2 1 k) :
    Commute (qtwoStdWin (F := F) (K := K) m a k (by omega) A) (stdTau E m) := by
  have hblk : a + k ≤ m + 1 := by omega
  have hl : ¬ (a ≤ (Fin.last m).val ∧ (Fin.last m).val < a + k) := by
    simp only [Fin.val_last]
    omega
  have hfix : blockEmb K 2 1 (m + 1) k a hblk A •
      (Pi.single (Fin.last m) (1 : K) : Fin (m + 1) → K) = Pi.single (Fin.last m) 1 :=
    blockEmb_smul_single_of_not_mem hblk A hl
  have hpres : ∀ x : Fin (m + 1) → K, x (Fin.last m) = 0 →
      (blockEmb K 2 1 (m + 1) k a hblk A • x) (Fin.last m) = 0 := by
    intro x hx
    rw [smul_def, coe_coe_blockEmb, blockMat_mulVec_of_not_mem _ _ hl]
    exact hx
  have hcomm :=
    suEndN_commute_tauAt E (blockEmb K 2 1 (m + 1) k a hblk A) (Fin.last m) hfix hpres
  unfold qtwoStdWin stdTau
  simpa only [MonoidHom.comp_apply] using hcomm

theorem qtwoStdConj_win (E : QuadExt F K (unitaryInvolution K 2 1)) {m a k : ℕ}
    (hak : a + k ≤ m) (A : Su K 2 1 k) :
    (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m a k (by omega) A) =
      qtwoStdWin (F := F) (K := K) m a k (by omega) A := by
  have hc := qtwoStdWin_commute_tau E hak A
  rw [stdConj]
  change MulAut.conj (stdTau E m) (qtwoStdWin (F := F) (K := K) m a k (by omega) A) =
    qtwoStdWin (F := F) (K := K) m a k (by omega) A
  rw [MulAut.conj_apply, ← hc, mul_assoc, mul_inv_cancel, mul_one]

theorem qtwoStd_comm_twist_win (E : QuadExt F K (unitaryInvolution K 2 1)) {m a k b l : ℕ}
    (ha : a + k ≤ m + 1) (hb : b + l ≤ m) (hab : a + k ≤ b ∨ b + l ≤ a)
    (x y : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hx : x ∈ (qtwoStdWin (F := F) (K := K) m a k ha).range.map (stdConj E m).toMonoidHom)
    (hy : y ∈ (qtwoStdWin (F := F) (K := K) m b l (by omega)).range) :
    x * y = y * x := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  obtain ⟨A, rfl⟩ := hu
  have hcy : (stdConj E m).toMonoidHom
      (qtwoStdWin (F := F) (K := K) m b l (by omega) B) =
      qtwoStdWin (F := F) (K := K) m b l (by omega) B :=
    qtwoStdConj_win E hb B
  have hcomm : qtwoStdWin (F := F) (K := K) m a k ha A *
      qtwoStdWin (F := F) (K := K) m b l (by omega) B =
      qtwoStdWin (F := F) (K := K) m b l (by omega) B *
        qtwoStdWin (F := F) (K := K) m a k ha A :=
    qtwoStdWin_commute ha (by omega) hab A B
  calc (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m a k ha A) *
        qtwoStdWin (F := F) (K := K) m b l (by omega) B
      = (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m a k ha A) *
          (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m b l (by omega) B) := by
        rw [hcy]
    _ = (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m a k ha A *
          qtwoStdWin (F := F) (K := K) m b l (by omega) B) := (map_mul _ _ _).symm
    _ = (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m b l (by omega) B *
          qtwoStdWin (F := F) (K := K) m a k ha A) := by rw [hcomm]
    _ = (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m b l (by omega) B) *
          (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m a k ha A) := map_mul _ _ _
    _ = qtwoStdWin (F := F) (K := K) m b l (by omega) B *
          (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m a k ha A) := by rw [hcy]

theorem qtwoStd_comm_win_win {m a k b l : ℕ} (ha : a + k ≤ m + 1) (hb : b + l ≤ m + 1)
    (hab : a + k ≤ b ∨ b + l ≤ a)
    (x y : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    (hx : x ∈ (qtwoStdWin (F := F) (K := K) m a k ha).range)
    (hy : y ∈ (qtwoStdWin (F := F) (K := K) m b l hb).range) :
    x * y = y * x := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  exact qtwoStdWin_commute ha hb hab A B

end CFSG.StandardType.QTwo

end
