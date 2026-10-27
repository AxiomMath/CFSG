module

public import CFSG.Monster.Existence.Compat.GolayMap
public import CFSG.Monster.Code.LatticeBasic

public section

namespace CFSG.Monster.Existence.Compat

open CFSG.Monster CFSG.Monster.Code CFSG.Open

@[expose] def permZ : (Fin 24 → ℤ) ≃ₗ[ℤ] (Fin 24 → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ sigma.symm

theorem permZ_apply (u : Fin 24 → ℤ) (j : Fin 24) : permZ u j = u (sigma.symm j) := rfl

theorem permZ_symm_apply (x : Fin 24 → ℤ) (i : Fin 24) : permZ.symm x i = x (sigma i) := rfl

theorem sum_permZ (u : Fin 24 → ℤ) : ∑ j, permZ u j = ∑ i, u i :=
  Equiv.sum_comp sigma.symm u

theorem sum_permZ_mul (u v : Fin 24 → ℤ) : ∑ j, permZ u j * permZ v j = ∑ i, u i * v i :=
  Equiv.sum_comp sigma.symm fun i => u i * v i

theorem sum_permZ_sq (u : Fin 24 → ℤ) : ∑ j, permZ u j ^ 2 = ∑ i, u i ^ 2 :=
  Equiv.sum_comp sigma.symm fun i => u i ^ 2

private theorem bitLift_cases (t : ZMod 2) : (t = 0 ∧ bitLift t = 0) ∨ (t = 1 ∧ bitLift t = 1) := by
  fin_cases t
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem isLeechVector_permZ_iff (u : Fin 24 → ℤ) :
    MonsterIsLeechVector (permZ u) ↔ u ∈ codeLattice C := by
  constructor
  · rintro ⟨m, hpar, hgol, hsum⟩
    refine ⟨m % 2, by omega,
      permLin.symm (fun j => if permZ u j ≡ m % 2 + 2 [ZMOD 4] then 1 else 0), ?_, fun i => ?_, ?_⟩
    · rw [mem_C_iff_mem_golay]
      have h := hgol (m % 2 + 2)
      convert h using 1
      funext j
      simp [permLin_symm_apply]
    · have hp := hpar (sigma i)
      have hi : permZ u (sigma i) = u i := by
        rw [permZ_apply, Equiv.symm_apply_apply]
      rw [hi] at hp
      rw [permLin_symm_apply]
      rw [hi]
      by_cases hc : u i ≡ m % 2 + 2 [ZMOD 4]
      · simp only [hc, ite_true, bitLift, ZMod.val_one, Nat.cast_one]
        unfold Int.ModEq at hc hp ⊢
        omega
      · simp only [hc, ite_false, bitLift, ZMod.val_zero, Nat.cast_zero]
        unfold Int.ModEq at hc hp ⊢
        omega
    · rw [sum_permZ] at hsum
      unfold Int.ModEq at hsum ⊢
      omega
  · rintro ⟨m, hm, d, hd, hud, hus⟩
    have hdg : permLin d ∈ monsterGolayCode := (mem_C_iff_mem_golay d).1 hd
    refine ⟨m, fun j => ?_, fun k => ?_, ?_⟩
    · have h := hud (sigma.symm j)
      rw [permZ_apply]
      unfold Int.ModEq at h ⊢
      have := bitLift_cases (d (sigma.symm j))
      omega
    · by_cases h1 : k ≡ m + 2 [ZMOD 4]
      · convert hdg using 1
        funext j
        have h := hud (sigma.symm j)
        rw [permZ_apply, permLin_apply]
        rcases bitLift_cases (d (sigma.symm j)) with ⟨h0, hb⟩ | ⟨h0, hb⟩
        · rw [h0]
          have : ¬ u (sigma.symm j) ≡ k [ZMOD 4] := by
            unfold Int.ModEq at h h1 ⊢
            omega
          simp [this]
        · rw [h0]
          have : u (sigma.symm j) ≡ k [ZMOD 4] := by
            unfold Int.ModEq at h h1 ⊢
            omega
          simp [this]
      · by_cases h2 : k ≡ m [ZMOD 4]
        · have : (fun j => if permZ u j ≡ k [ZMOD 4] then (1 : ZMod 2) else 0) =
              (fun _ : Fin 24 => (1 : ZMod 2)) + permLin d := by
            funext j
            have h := hud (sigma.symm j)
            rw [permZ_apply, Pi.add_apply, permLin_apply]
            rcases bitLift_cases (d (sigma.symm j)) with ⟨h0, hb⟩ | ⟨h0, hb⟩
            · rw [h0]
              have : u (sigma.symm j) ≡ k [ZMOD 4] := by
                unfold Int.ModEq at h h2 ⊢
                omega
              simp [this]
            · rw [h0]
              have : ¬ u (sigma.symm j) ≡ k [ZMOD 4] := by
                unfold Int.ModEq at h h2 ⊢
                omega
              simp only [this, ite_false]
              decide
          rw [this]
          exact monsterGolayCode.add_mem allOnes_mem_golay hdg
        · have : (fun j => if permZ u j ≡ k [ZMOD 4] then (1 : ZMod 2) else 0) = 0 := by
            funext j
            have h := hud (sigma.symm j)
            rw [permZ_apply, Pi.zero_apply]
            have hn : ¬ u (sigma.symm j) ≡ k [ZMOD 4] := by
              have := bitLift_cases (d (sigma.symm j))
              unfold Int.ModEq at h h1 h2 ⊢
              omega
            simp [hn]
          rw [this]
          exact monsterGolayCode.zero_mem
    · rw [sum_permZ]
      exact hus

theorem isLeechVector_iff (x : Fin 24 → ℤ) :
    MonsterIsLeechVector x ↔ permZ.symm x ∈ codeLattice C := by
  rw [← isLeechVector_permZ_iff, LinearEquiv.apply_symm_apply]

theorem mem_monsterLeech_iff (x : Fin 24 → ℤ) : x ∈ monsterLeech ↔ permZ.symm x ∈ mogLattice := by
  constructor
  · intro hx
    have hle : monsterLeech ≤ mogLattice.comap permZ.symm.toLinearMap.toAddMonoidHom := by
      refine AddSubgroup.closure_le _ |>.2 ?_
      intro y hy
      exact (isLeechVector_iff y).1 hy
    exact hle hx
  · intro hx
    exact AddSubgroup.subset_closure ((isLeechVector_iff x).2 hx)

theorem mem_monsterLeech_iff_isLeechVector (x : Fin 24 → ℤ) :
    x ∈ monsterLeech ↔ MonsterIsLeechVector x :=
  (mem_monsterLeech_iff x).trans (isLeechVector_iff x).symm

theorem monsterLeech_eq_map : monsterLeech = mogLattice.map permZ.toLinearMap.toAddMonoidHom := by
  ext x
  rw [mem_monsterLeech_iff, AddSubgroup.mem_map]
  constructor
  · intro hx
    exact ⟨permZ.symm x, hx, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    simpa using hu

@[expose] def leechEquiv : mogLattice ≃+ monsterLeech :=
  (AddEquiv.addSubgroupMap permZ.toAddEquiv mogLattice).trans
    (AddEquiv.addSubgroupCongr monsterLeech_eq_map.symm)

theorem coe_leechEquiv (u : mogLattice) : ((leechEquiv u : monsterLeech) : Fin 24 → ℤ) = permZ u :=
  rfl

theorem coe_leechEquiv_symm (v : monsterLeech) :
    ((leechEquiv.symm v : mogLattice) : Fin 24 → ℤ) = permZ.symm v := rfl

end CFSG.Monster.Existence.Compat
