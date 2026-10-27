module

public import CFSG.RankThree.PartOne.CTP.AsmRes
public import CFSG.RankThree.PartOne.CTP.AsmStep

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def tauC (σ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 5) :=
  Equiv.swap (σ 0) (σ 3) * Equiv.swap (σ 1) (σ 4)

omit [Group G] [Finite G] in
theorem tauC_mul_self (σ : Equiv.Perm (Fin 5)) : tauC σ * tauC σ = 1 := by
  have h : [σ 0, σ 3, σ 1, σ 4].Nodup := by
    simp [List.nodup_cons, σ.injective.eq_iff]
  have hc : Commute (Equiv.swap (σ 0) (σ 3)) (Equiv.swap (σ 1) (σ 4)) :=
    (Equiv.Perm.disjoint_swap_swap h).commute
  unfold tauC
  calc Equiv.swap (σ 0) (σ 3) * Equiv.swap (σ 1) (σ 4) *
        (Equiv.swap (σ 0) (σ 3) * Equiv.swap (σ 1) (σ 4))
      = Equiv.swap (σ 0) (σ 3) * (Equiv.swap (σ 1) (σ 4) * Equiv.swap (σ 0) (σ 3)) *
          Equiv.swap (σ 1) (σ 4) := by simp only [mul_assoc]
    _ = Equiv.swap (σ 0) (σ 3) * (Equiv.swap (σ 0) (σ 3) * Equiv.swap (σ 1) (σ 4)) *
          Equiv.swap (σ 1) (σ 4) := by rw [hc.eq]
    _ = 1 := by simp [← mul_assoc]

omit [Group G] [Finite G] in
theorem tauC_apply_zero (σ : Equiv.Perm (Fin 5)) : tauC σ (σ 0) = σ 3 := by
  have h1 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h2 : σ 0 ≠ σ 4 := σ.injective.ne (by decide)
  unfold tauC
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_left]

omit [Group G] [Finite G] in
theorem tauC_apply_one (σ : Equiv.Perm (Fin 5)) : tauC σ (σ 1) = σ 4 := by
  have h1 : σ 4 ≠ σ 0 := σ.injective.ne (by decide)
  have h2 : σ 4 ≠ σ 3 := σ.injective.ne (by decide)
  unfold tauC
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h1 h2]

section Comm

variable {L B K : Subgroup G} {f₀ : ℕ} {b : G} {c : G} {F : LFam L B f₀ b K} {I : Subgroup G}

theorem Asm.Msg_comm_Isg (A : Asm c F I) (σ : Equiv.Perm (Fin 5)) :
    ∀ y ∈ Msg F I (tauC σ * σ) 0 1, ∀ u ∈ Isg F I σ, y * u = u * y := by
  have hh : F.W (tauC σ) * F.W (tauC σ) = 1 := by
    rw [← map_mul, tauC_mul_self, map_one]
  have hK01 : F.J 0 1 ≤ K := by
    have : F.J 0 1 ≤ F.J 0 1 ⊔ F.J 1 2 := le_sup_left
    rwa [← F.K_eq] at this
  have hτσ0 : (tauC σ * σ) (e3 0) = σ 3 := by
    show tauC σ (σ 0) = σ 3
    exact tauC_apply_zero σ
  have hτσ1 : (tauC σ * σ) (e3 1) = σ 4 := by
    show tauC σ (σ 1) = σ 4
    exact tauC_apply_one σ
  have key := pairLayer_conj_centralizes (A.cfg σ) (A.facts σ) (h := F.W (tauC σ))
    (Isg_mem_theta F I A.hI σ) hh (A.h5norm σ) (a₀ := 0) (b₀ := 1) (by decide) ?_ ?_
  · intro y hy u hu
    rw [← conj_Msg] at hy
    exact key y hy u hu
  ·
    have e1 : conjBy (F.W (tauC σ)) (Jsg F σ 0 1) = F.J (σ 3) (σ 4) := by
      rw [conj_Jsg, Jsg_eq, hτσ0, hτσ1]
    rw [e1]
    have e2 : Ksg F σ = F.J (σ 0) (σ 1) ⊔ F.J (σ 1) (σ 2) := by
      have := congrArg (conjBy (F.W σ)) F.K_eq
      rw [conjBy_sup, conjBy_J, conjBy_J] at this
      exact this
    rw [e2, centralizer_sup]
    refine le_inf (F.disj _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) (F.disj _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) <;>
      exact σ.injective.ne (by decide)
  ·
    have e3' : BKsg F σ ⊓ Jsg F σ 0 1 = conjBy (F.W σ) (B ⊓ F.J 0 1) := by
      unfold BKsg Jsg
      rw [← conjBy_inf]
      congr 1
      show B ⊓ K ⊓ F.J 0 1 = B ⊓ F.J 0 1
      rw [inf_assoc, inf_eq_right.mpr hK01]
    rw [e3', conjBy_conjBy, ← map_mul, conjBy_B_inf_J,
      show (tauC σ * σ) 0 = σ 3 from hτσ0, show (tauC σ * σ) 1 = σ 4 from hτσ1, B_inf_J_sg]

theorem Asm.Msg_comm (A : Asm c F I) {σ τ : Equiv.Perm (Fin 5)} {x y x' y' : Fin 3}
    (hxy : x ≠ y) (hxy' : x' ≠ y') (h1 : τ (e3 x') = σ 3) (h2 : τ (e3 y') = σ 4) :
    ∀ m ∈ Msg F I τ x' y', ∀ n ∈ Msg F I σ x y, m * n = n * m := by
  intro m hm n hn
  have e : Msg F I τ x' y' = Msg F I (tauC σ * σ) 0 1 := by
    refine A.Msg_eq_of_pair hxy' (by decide) ?_ ?_
    · rw [h1]
      exact (tauC_apply_zero σ).symm
    · rw [h2]
      exact (tauC_apply_one σ).symm
  rw [e] at hm
  have hnI : n ∈ Isg F I σ := by
    have := (A.facts σ).M_le x y hxy
    exact this hn
  exact A.Msg_comm_Isg σ m hm n hnI

end Comm

end CFSG.RankThree.PartOne.CTP
