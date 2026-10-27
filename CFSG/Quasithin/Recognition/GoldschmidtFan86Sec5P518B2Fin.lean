module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Arc

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem b2_of_ctx (S : B2Set F L T a) (hn : nOrb T a = 4) :
    zA L T a 0 • zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 1 := by
  obtain ⟨g, hg1, hg2, -, -, hg5, hg6⟩ := S.exists_arc_elt hn
  have hA0 : ∀ i : ℤ, zA L T a 0 • xv T a i = xv T a i ↔ -6 ≤ i ∧ i ≤ 6 := fun i => by
    simpa using S.zA_fix_iff 0 i
  have hv0 : valence Γ (xv T a 0) = 5 := by simpa using S.val_even 0
  have hv2 : valence Γ (xv T a 2) = 5 := by simpa using S.val_even 1
  have hv1 : valence Γ (xv T a 1) = 3 := by simpa using S.val_odd 0
  have hA0z : zA L T a 0 = L.z (xv T a 0) := by simp [zA]
  have hA1z : zA L T a 1 = L.z (xv T a 2) := by simp [zA]
  have a21 : Γ.Adj (xv T a 2) (xv T a 1) := (xv_adj_of T a (by norm_num : (2 : ℤ) = 1 + 1)).symm
  have a10 : Γ.Adj (xv T a 1) (xv T a 0) := (xv_adj_of T a (by norm_num : (1 : ℤ) = 0 + 1)).symm
  have n02 : xv T a 0 ≠ xv T a 2 := xv_ne_of T a (by norm_num)
  obtain ⟨x0', hbr', hne', hset⟩ :=
    exists_sibling F hv2 (show Br Γ (xv T a 2) (xv T a 1) (xv T a 0) from ⟨a21, a10, n02⟩)
  have hσ : g * zA L T a 0 * g⁻¹ = zA L T a 0 ∨
      g * zA L T a 0 * g⁻¹ = zA L T a 0 * zA L T a 1 := by
    have hmem : g • xv T a 0 ∈ Γ.neighborSet (xv T a 1) := by
      have := (F.adj_smul g (xv T a 0) (xv T a 1)).2
        (xv_adj_of T a (by norm_num : (1 : ℤ) = 0 + 1))
      rw [hg1] at this
      exact this.symm
    rw [hset] at hmem
    rcases hmem with h | h | h
    · exact absurd (MulAction.injective g (h.trans hg2.symm)) n02
    · left
      rw [hA0z, ← L.equivariant g _ hv0, h]
    · right
      have hprod := S.lab.hyp.prod (xv T a 1) (xv T a 2) (xv T a 0) x0' hv1 hset n02.symm
        hbr'.2.2.symm hne'.symm
      rw [hA0z, hA1z, ← L.equivariant g _ hv0, h]
      have h1 : L.z x0' = (L.z (xv T a 2) * L.z (xv T a 0))⁻¹ := eq_inv_of_mul_eq_one_right hprod
      rw [h1, mul_inv_rev, z_inv hv0, z_inv hv2]
  have hσmove : ∀ w : V, Γ.Adj (zA L T a 5 • xv T a 2) w → w ≠ zA L T a 5 • xv T a 3 →
      (g * zA L T a 0 * g⁻¹) • w ≠ w := by
    intro w hw hw3 h
    have hw' : Γ.Adj (xv T a 6) (g⁻¹ • w) := by
      have := (F.adj_smul g⁻¹ _ _).2 hw
      rwa [← hg6, inv_smul_smul] at this
    have hne : xv T a 5 ≠ g⁻¹ • w := fun h' => by
      apply hw3
      rw [← hg5, h', smul_inv_smul]
    have hfix : zA L T a 0 • g⁻¹ • w = g⁻¹ • w := by
      rw [mul_smul, mul_smul] at h
      have := congrArg (fun u => g⁻¹ • u) h
      simpa using this
    have h65 : Γ.Adj (xv T a 6) (xv T a 5) :=
      (xv_adj_of T a (by norm_num : (6 : ℤ) = 5 + 1)).symm
    have h67 : Γ.Adj (xv T a 6) (xv T a 7) := xv_adj_of T a (by norm_num)
    have h7 := F.frobenius_two (xv T a 6) (xv T a 5) (g⁻¹ • w) h65 hw' hne (zA L T a 0)
      (MulAction.mem_stabilizer_iff.2 ((hA0 6).2 ⟨by norm_num, by norm_num⟩))
      ((hA0 5).2 ⟨by norm_num, by norm_num⟩) hfix (xv T a 7) h67
    have := ((hA0 7).1 h7).2
    norm_num at this
  have h21 : Γ.Adj (zA L T a 5 • xv T a 2) (zA L T a 5 • xv T a 1) :=
    (F.adj_smul _ _ _).2 (xv_adj_of T a (by norm_num : (2 : ℤ) = 1 + 1)).symm
  have h13 : zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 3 := fun h =>
    xv_ne_of T a (by norm_num : (3 : ℤ) = 1 + 2) (MulAction.injective _ h)
  have hmove := hσmove _ h21 h13
  rcases hσ with h | h
  · rw [h] at hmove
    exact hmove
  · rw [h, mul_smul] at hmove
    have hA1 : zA L T a 1 ∈ ballStab Γ G 2 (zA L T a 5 • xv T a 2) := by
      have h6 : zA L T a 1 ∈ ballStab Γ G 2 (xv T a 6) := by simpa using S.claimA_fwd 1
      have := ballStab_conj F g h6
      rw [hg6] at this
      have e : g * zA L T a 1 * g⁻¹ = zA L T a 1 := by
        rw [hA1z, ← L.equivariant g _ hv2, hg2]
      rwa [e] at this
    have hd : Γ.dist (zA L T a 5 • xv T a 2) (zA L T a 5 • xv T a 1) ≤ 2 := by
      have : Γ.dist (zA L T a 5 • xv T a 2) (zA L T a 5 • xv T a 1) ≤ 1 := by
        simpa using SimpleGraph.dist_le (Walk.cons h21 Walk.nil)
      omega
    rwa [mem_ballStab.1 hA1 _ hd] at hmove

end P518

end CFSG.Quasithin.Fan86
