module

public import CFSG.LocalAnalysis.StandardType.GGK0KacRow

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem k0E6_extRoot_coords :
    (k0Kac .E6).extRoot = fun x : Option (Fin 6) =>
      match x with
      | none => (-![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)
      | some j => Pi.single j 1 := by
  funext x
  cases x <;> rfl

private theorem k0E6_tau_perm : (k0DiagOf .E6).tau.Perm (List.range 7) :=
  tau0_perm .E6

private theorem k0E6_tau_mul_tau :
    k0pMul (k0DiagOf .E6).tau (k0DiagOf .E6).tau = k0pId 7 :=
  tau0_mul_tau0 .E6

private theorem k0E6_tau_getD_tau_getD {j : ℕ} (hj : j < 7) :
    (k0DiagOf .E6).tau.getD ((k0DiagOf .E6).tau.getD j 0) 0 = j := by
  have h := k0pMul_getD (k0DiagOf .E6).tau (k0DiagOf .E6).tau (i := j)
    (by rw [k0E6_tau_perm.length_eq, List.length_range]; exact hj)
  rw [k0E6_tau_mul_tau] at h
  rw [k0pId, List.getD_eq_getElem _ _ (by simp only [List.length_range]; exact hj),
    List.getElem_range] at h
  exact h.symm

theorem k0_permLattice_extRoot_E6
    (i : ℕ) (hi : i < (k0DiagOf .E6).marks.length) :
    permLattice (τ := absTag .E6) TwistTag.E6.perm
        ((k0Kac .E6).extRoot (idxNode (r := (absTag .E6).rank) i)) =
      (k0Kac .E6).extRoot (idxNode (r := (absTag .E6).rank) ((k0DiagOf .E6).tau.getD i 0)) := by
  have hi7 : i < 7 := hi
  rw [k0E6_extRoot_coords]
  interval_cases i <;> (funext j; fin_cases j <;> decide +kernel)

theorem k0_rat_twE6
    {ε : ℤ} {d : ℕ} (hεd : ε = 1 ∧ d = 1 ∨ ε = -1 ∧ d = 2) (w₁ : WeylGroup (absTag .E6))
    {rho : List ℕ} (hrho : rho.Perm (List.range (k0DiagOf .E6).marks.length))
    (hact : ∀ i, i < (k0DiagOf .E6).marks.length →
      ε • (w₁ • permLattice (τ := absTag .E6) TwistTag.E6.perm
        ((k0Kac .E6).extRoot (idxNode (r := (absTag .E6).rank) i))) =
        (k0Kac .E6).extRoot (idxNode (r := (absTag .E6).rank) (rho.getD i 0))) :
    ∃ a ∈ (k0DiagOf .E6).omega, rho = k0pMul a (k0Rho0 (k0DiagOf .E6) true d) := by
  have hd : d = 1 ∨ d = 2 := hεd.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have hrho' : (k0pMul rho (k0DiagOf .E6).tau).Perm
      (List.range (k0DiagOf .E6).marks.length) :=
    k0pMul_perm hrho k0E6_tau_perm
  have hact' : ∀ j, j < (k0DiagOf .E6).marks.length →
      ε • (w₁ • (k0Kac .E6).extRoot (idxNode (r := (absTag .E6).rank) j)) =
        (k0Kac .E6).extRoot
          (idxNode (r := (absTag .E6).rank) ((k0pMul rho (k0DiagOf .E6).tau).getD j 0)) := by
    intro j hj
    have hj7 : j < 7 := hj
    have htau_lt : (k0DiagOf .E6).tau.getD j 0 < (k0DiagOf .E6).marks.length :=
      k0_getD_lt_of_perm k0E6_tau_perm hj7
    have h := hact ((k0DiagOf .E6).tau.getD j 0) htau_lt
    rw [k0_permLattice_extRoot_E6 ((k0DiagOf .E6).tau.getD j 0) htau_lt,
      k0E6_tau_getD_tau_getD hj7] at h
    rw [← k0pMul_getD rho (k0DiagOf .E6).tau (i := j) (by
      rw [k0E6_tau_perm.length_eq, List.length_range]; exact hj7)] at h
    exact h
  obtain ⟨a, ha, hrho'a⟩ := k0_rat_untw .E6 hεd w₁ hrho' hact'
  refine ⟨a, ha, ?_⟩
  have hsplit : rho = k0pMul (k0pMul rho (k0DiagOf .E6).tau) (k0DiagOf .E6).tau := by
    calc rho = k0pMul rho (k0pId 7) := (k0pMul_id_right_perm .E6 hrho).symm
      _ = k0pMul rho (k0pMul (k0DiagOf .E6).tau (k0DiagOf .E6).tau) := by
            rw [k0E6_tau_mul_tau]
      _ = k0pMul (k0pMul rho (k0DiagOf .E6).tau) (k0DiagOf .E6).tau :=
            (k0pMul_assoc_perm .E6 hrho k0E6_tau_perm k0E6_tau_perm).symm
  have hkey : k0pMul (k0Rho0 (k0DiagOf .E6) false d) (k0DiagOf .E6).tau =
      k0Rho0 (k0DiagOf .E6) true d := by
    rcases hd with rfl | rfl
    · rw [k0Rho0_one, k0pMul_id_left_perm .E6 k0E6_tau_perm]
      rfl
    · rw [k0Rho0_two]
      rfl
  rw [hsplit, hrho'a,
    k0pMul_assoc_perm .E6 (omega_perm .E6 ha) (k0Rho0_perm .E6 d hd) k0E6_tau_perm, hkey]

end CFSG.StandardType.GGK0MarkedKacIface1587

end
