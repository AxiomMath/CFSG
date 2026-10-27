module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Fin

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem uE_ne_one (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a) : uE L T a ≠ 1 := by
  have hmove : ∀ i : ℤ, i ≤ 1 → zA L T a 4 • xv T a i ≠ xv T a i := fun i hi h =>
    absurd ((zA_fix C 4 i).1 h) (by omega)
  have hfix2 : zA L T a 4 • xv T a 2 = xv T a 2 := (zA_fix C 4 2).2 (by omega)
  have hbr : Br Γ (xv T a 2) (xv T a 1) (xv T a 0) := by simpa using xv_br_bwd T a 0
  have hbr' : Br Γ (xv T a 2) (zA L T a 4 • xv T a 1) (zA L T a 4 • xv T a 0) := by
    have := Br.smul F (zA L T a 4) hbr
    rwa [hfix2] at this
  have hd : Γ.dist (xv T a 0) (zA L T a 4 • xv T a 0) = 4 :=
    dist_four F hbr hbr' (fun h => hmove 1 le_rfl h.symm)
  have h5 : valence Γ (xv T a 0) = 5 := C.val5
  have h5' : valence Γ (zA L T a 4 • xv T a 0) = 5 := by
    rw [F.valence_smul_eq]
    exact h5
  have hne := H.hyp.dist _ _ (fun h => hmove 0 (by omega) h.symm) h5 h5' (Or.inr hd)
  have hQ : L.z (zA L T a 4 • xv T a 0) = zA L T a 4 * zA L T a 0 * zA L T a 4 := by
    rw [L.equivariant _ _ h5, ← zA_zero, inv_eq_of_mul_eq_one_right (zA_sq F C 4)]
  intro h
  apply hne
  rw [hQ, ← zA_zero]
  have h1 : zA L T a 0 * (zA L T a 4 * zA L T a 0 * zA L T a 4) = 1 := by
    unfold uE at h
    simpa [mul_assoc] using h
  rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right (zA_sq F C 0)]

theorem uE_mem_fixer (F : FanTree Γ G) (E : EG L T a) (hc : T.τ * uE L T a * T.τ⁻¹ = uE L T a) :
    uE L T a ∈ T.fixer := by
  have hfix4 : uE L T a • xv T a 4 = xv T a 4 := by
    have h0 := mem_ballStab.1 E.hA0 (xv T a 4) (by simp)
    have h4 := mem_ballStab.1 E.hA4 (xv T a 4) (by simp)
    unfold uE
    simp only [mul_smul, h0, h4]
  have hcomm : Commute T.τ (uE L T a) := by
    show T.τ * uE L T a = uE L T a * T.τ
    rw [mul_inv_eq_iff_eq_mul] at hc
    exact hc
  have hk : ∀ k : ℤ, uE L T a • xv T a (4 + 2 * k) = xv T a (4 + 2 * k) := fun k => by
    rw [← xv_smul, ← mul_smul, ← (hcomm.zpow_left k).eq, mul_smul, hfix4]
  have hall : ∀ j : ℤ, uE L T a • xv T a j = xv T a j := fun j => by
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, 4 + 2 * k ≤ j ∧ j ≤ 4 + 2 * (k + 1) :=
      ⟨(j - 4) / 2, by omega, by omega⟩
    exact Line.fixes_between F.isTree F.adj_smul T.line (i := a + 1 + (4 + 2 * k))
      (j := a + 1 + (4 + 2 * (k + 1))) (k := a + 1 + j) (by omega) (by omega) (hk k)
      (hk (k + 1))
  refine (T.mem_fixer).2 fun i => ?_
  have := hall (i - (a + 1))
  have e : xv T a (i - (a + 1)) = T.line.vert i := by
    show T.line.vert (a + 1 + (i - (a + 1))) = T.line.vert i
    congr 1
    ring
  rwa [e] at this

theorem b5 (F : FanTree Γ G) (H : Lab18 L) (E : EG L T a) (hT : T.fixer = ⊥)
    (hc : T.τ * uE L T a * T.τ⁻¹ = uE L T a) : False := by
  have hu := uE_mem_fixer F E hc
  rw [hT] at hu
  exact uE_ne_one F H E.ctx (Subgroup.mem_bot.1 hu)

end P518

end CFSG.Quasithin.Fan86
