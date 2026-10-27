module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Step2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Ball

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Q_all (F : FanTree Γ G) (h40 : Fan40 F) {T : Track Γ G} {z : G} {a r : ℤ}
    (C : Ctx F T z a r) (hr0 : 0 ≤ r) : ∀ n : ℕ, 2 * (n : ℤ) + 2 ≤ r → Q T z a n := by
  intro n
  induction n with
  | zero =>
    intro _
    simpa using Q_zero F C
  | succ n ih =>
    intro h
    push_cast at h ⊢
    exact step F h40 C hr0 (m := n) (by positivity) (by omega) (ih (by omega))

theorem core (F : FanTree Γ G) (h40 : Fan40 F) {T : Track Γ G} {z : G} {a r : ℤ}
    (C : Ctx F T z a r) (hr0 : 0 ≤ r) {j : ℤ} (hj : 0 ≤ j) (hjr : 2 * j + 3 ≤ r) :
    lab T z j ∈ ballStab Γ G 2 (T.line.vert (a + 1)) := by
  set α := T.line.vert (a + 1) with hα
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  have hQ := Q_all F h40 C hr0 n (by omega)
  have hw := lab_mem_nbrStab F C hr0 (j := (n : ℤ)) hj (by omega)
  have hwα : lab T z n • α = α := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hw)
  have hcin : lab T z n ∈ Cinv G (T.line.vert (a + 1 + 2 * (n : ℤ))) := by
    rw [lab_eq_Lb C]
    exact Lb_cinv C.cinv ⟨T.τ ^ (n : ℤ), T.zpow_smul_vert (n : ℤ) (a + 1)⟩
  refine (F.mem_ballStab_two_iff).2 ⟨hw, fun γ hγ => ?_⟩
  refine mem_nbrStab.2 fun u hu => ?_
  by_cases huα : u = α
  · rw [huα]
    exact hwα
  · have hv3γ : valence Γ γ = 3 := valence_adj_three F C.val hγ
    obtain ⟨l', hset, hαl', hul'⟩ := exists_third_neighbor hv3γ hγ.symm hu (Ne.symm huα)
    have hu5 : valence Γ u = 5 := valence_adj_five F hv3γ hu
    have hfix : Lb z α u ∈ MulAction.stabilizer G (T.line.vert (a + 1 + 2 * (n : ℤ))) :=
      MulAction.mem_stabilizer_iff.2 (hQ γ u hγ hu huα)
    have hwc : lab T z n * Lb z α u = Lb z α u * lab T z n := (hcin.2.2.2 _ hfix).symm
    have hγl' : Γ.Adj γ l' := by
      have : l' ∈ Γ.neighborSet γ := by rw [hset]; simp
      exact this
    exact swap_fix F C.cinv C.val ⟨1, one_smul _ _⟩ hv3γ hγ.symm hu hγl' (Ne.symm huα) hαl'
      hul' C.f2 hwα (mem_nbrStab.1 hw γ hγ) hwc

end P515

end CFSG.Quasithin.Fan86
