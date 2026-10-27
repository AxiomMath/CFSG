module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoTrans

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W] {s : ℕ}

namespace RegData

variable (R : RegData Γ H s)

include R

theorem eq_of_agree (a : Arc Γ s) {g₁ g₂ : H}
    (h : ∀ j, j ≤ s → g₁ • a.vert j = g₂ • a.vert j) : g₁ = g₂ := by
  have : g₁⁻¹ * g₂ = 1 := by
    refine R.faith a _ fun j hj => ?_
    rw [mul_smul, ← h j hj, inv_smul_smul]
  exact inv_mul_eq_one.mp this

theorem exists_shift (a : Arc Γ s) {c : W} (hc : c ∈ extSet a) :
    ∃ g : H, (∀ j, j < s → g • a.vert j = a.vert (j + 1)) ∧ g • a.vert s = c := by
  obtain ⟨g, hg⟩ := R.trans a (a.fwd c hc.1 hc.2)
  refine ⟨g, fun j hj => ?_, ?_⟩
  · rw [hg j hj.le, Arc.fwd_vert_lt a c hc.1 hc.2 hj]
  · rw [hg s le_rfl, Arc.fwd_vert_last]

theorem shift_last_mem (hs : 2 ≤ s) (a : Arc Γ s) {g : H}
    (hg : ∀ j, j < s → g • a.vert j = a.vert (j + 1)) : g • a.vert s ∈ extSet a := by
  refine ⟨?_, fun _ hcontra => ?_⟩
  · have h1 := (R.adj g _ _).2 (a.adj (s - 1) (by omega))
    have hg' : g • a.vert (s - 1) = a.vert s := by
      have := hg (s - 1) (by omega)
      rwa [show s - 1 + 1 = s by omega] at this
    rw [show s - 1 + 1 = s by omega, hg'] at h1
    exact h1
  · have h2 : g • a.vert s = g • a.vert (s - 2) := by
      rw [hcontra, hg (s - 2) (by omega), show s - 2 + 1 = s - 1 by omega]
    have h3 := MulAction.injective g h2
    have := a.nb (s - 2) (by omega)
    rw [show s - 2 + 2 = s by omega] at this
    exact this h3.symm

theorem exists_rl (hs : 2 ≤ s) (a : Arc Γ s) :
    ∃ r l : H, (∀ j, j < s → r • a.vert j = a.vert (j + 1)) ∧
      (∀ j, j < s → l • a.vert j = a.vert (j + 1)) ∧ r ≠ l ∧
      ∀ g : H, (∀ j, j < s → g • a.vert j = a.vert (j + 1)) → g = r ∨ g = l := by
  have e : (if s = 0 then 3 else 2) = 2 := by split_ifs <;> omega
  obtain ⟨c₀, c₁, hne, hset⟩ := Set.ncard_eq_two.mp
    (by rw [extSet_ncard R.card3 a, e] : (extSet a).ncard = 2)
  have h0 : c₀ ∈ extSet a := by rw [hset]; simp
  have h1 : c₁ ∈ extSet a := by rw [hset]; simp
  obtain ⟨r, hr, hr'⟩ := R.exists_shift a h0
  obtain ⟨l, hl, hl'⟩ := R.exists_shift a h1
  refine ⟨r, l, hr, hl, fun hrl => hne ?_, fun g hg => ?_⟩
  · rw [← hr', ← hl', hrl]
  · have hm := R.shift_last_mem hs a hg
    rw [hset] at hm
    rcases hm with hm | hm
    · left
      refine R.eq_of_agree a fun j hj => ?_
      rcases Nat.lt_or_ge j s with hjs | hjs
      · rw [hg j hjs, hr j hjs]
      · have : j = s := by omega
        subst this
        rw [hm, hr']
    · right
      refine R.eq_of_agree a fun j hj => ?_
      rcases Nat.lt_or_ge j s with hjs | hjs
      · rw [hg j hjs, hl j hjs]
      · have : j = s := by omega
        subst this
        rw [Set.mem_singleton_iff.mp hm, hl']

theorem exists_xi (a : Arc Γ s) :
    ∃ ξ : H, (∀ j, j ≤ s → ξ • a.vert j = a.vert (s - j)) ∧ ξ * ξ = 1 := by
  obtain ⟨ξ, hξ⟩ := R.trans a a.rev
  have h : ∀ j, j ≤ s → ξ • a.vert j = a.vert (s - j) := by
    intro j hj
    rw [hξ j hj, Arc.rev_vert]
  refine ⟨ξ, h, R.faith a _ fun j hj => ?_⟩
  rw [mul_smul, h j hj, h (s - j) (by omega), show s - (s - j) = j by omega]

end RegData

end CFSG.Quasithin.Fan86.Tutte.Geo
