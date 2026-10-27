module

public import CFSG.Quasithin.Background.SmithB45MatIndM23Gen

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22
  CFSG.CharacterTheory.SteinbergBY Module

@[expose] def m23Xcol (i : ℕ) (z : Bool) (k : ℕ) : List ℕ :=
  matOf (m23Xd i) (m23Xc i (m23hArr z k))

theorem m23Xd_pos (i : ℕ) : 0 < m23Xd i := by
  unfold m23Xd
  split_ifs <;> norm_num

theorem m23K_eq (i : ℕ) (z : Bool) :
    m23K i z = indColsG 23 (m23Xd i) (m23pi z) (m23Xcol i z) := by
  unfold m23K indCols indColsG m23Xcol m23pi m23hArr
  rw [m23Ts_size]
  refine List.map_congr_left fun j _ => ?_
  rw [matOf, getD_map_range _ _ (Nat.mod_lt _ (m23Xd_pos i)), Nat.one_shiftLeft]

theorem m23Xcol_lt (i : ℕ) (z : Bool) (k : ℕ) :
    ∀ c < m23Xd i, (m23Xcol i z k).getD c 0 < 2 ^ m23Xd i := by
  intro c hc
  rw [m23Xcol, matOf, getD_map_range _ _ hc]
  unfold m23Xd m23Xc
  split_ifs with h0 h1
  · norm_num
  · exact actC10_lt _ _
  · exact act10_lt _ _

theorem m23Ns_zero : m23Ns 0 = [0, 11, 22, 23] := rfl

theorem m23Ns_one : m23Ns 1 = [0, 44, 55, 99, 219, 230] := rfl

theorem m23Ns_two : m23Ns 2 = [0, 120, 131, 175, 186, 230] := rfl

theorem m23Typs_zero : m23Typs 0 = [1, 2, 0] := rfl

theorem m23Typs_one : m23Typs 1 = [3, 2, 3, 5, 1] := rfl

theorem m23Typs_two : m23Typs 2 = [5, 2, 4, 1, 4] := rfl

theorem m23Ns_facts : ∀ i < 3, ∀ j < (m23Ns i).length - 1,
    (m23Ns i).getD (j + 1) 0 - (m23Ns i).getD j 0 = m23Dim ((m23Typs i).getD j 0) ∧
      (m23Typs i).getD j 0 < 6 := by
  intro i hi j hj
  interval_cases i
  · rw [m23Ns_zero] at hj ⊢
    rw [m23Typs_zero]
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> decide
  · rw [m23Ns_one] at hj ⊢
    rw [m23Typs_one]
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> decide
  · rw [m23Ns_two] at hj ⊢
    rw [m23Typs_two]
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> decide

theorem m23_exists_std
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) ↥mog23 X)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hne : Nontrivial X) {i : ℕ} (hi : i < 3) (ψ : Vec (m23Xd i) →ₗ[ZMod 2] X) (hψ0 : ψ ≠ 0)
    (hψ : ∀ z, ∀ k < 23, ∀ v, ψ (lin (m23Xd i) (m23Xcol i z k) v) = ρ (m23h z k) (ψ v)) :
    ∃ t < 6, ∃ d, d = m23Dim t ∧ ∃ Ψ : Vec d ≃ₗ[ZMod 2] X,
      ∀ z s, Ψ (lin d (m23Std t z) s) = ρ (m23g z) (Ψ s) := by
  have : Finite ↥mog23 := Subgroup.instFiniteSubtypeMem mog23
  have hK : ∀ z v, indMap ρ 23 (m23Xd i) m23t ψ (lin (23 * m23Xd i) (m23K i z) v) =
      ρ (m23g z) (indMap ρ 23 (m23Xd i) m23t ψ v) := by
    intro z v
    rw [m23K_eq]
    refine indMap_lin ρ m23t ψ (fun k hk => m23pi_lt z hk) (fun k _ => m23Xcol_lt i z k)
      (fun k hk w => ?_) v
    rw [hψ z k hk w, ← Module.End.mul_apply, ← map_mul, m23_coset_rel, map_mul,
      Module.End.mul_apply]
  have hsurj := indMap_surjective ρ closure_m23g hirr m23t ψ hK hψ0 (by norm_num)
  have hflag : m23FlagOK i = true := by
    obtain ⟨-, h0, h1, h2⟩ := m23_ind_checks
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
  have hWne : (⊤ : Submodule (ZMod 2) X) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    exact hx ((Submodule.mem_bot (ZMod 2)).1 (h ▸ Submodule.mem_top))
  obtain ⟨j, hj, Ψ, hΨ⟩ := exists_iso_of_flagOK hflag
    (fun j hj => by
      rw [(m23Ns_facts i hi j hj).1]
      exact irredPair_m23Std (m23Ns_facts i hi j hj).2)
    (fun z => ρ (m23g z)) (irredPair_of_irr ρ hirr) hWne _ hsurj hK
  exact ⟨_, (m23Ns_facts i hi j hj).2, _, (m23Ns_facts i hi j hj).1, Ψ, hΨ⟩

end CFSG.Quasithin.B45Mat.Ind
