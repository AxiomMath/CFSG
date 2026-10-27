module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoP2

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem tab_mul (g h : M22) : tab (g * h) = tmul (tab g) (tab h) := by
  show Array.ofFn (fun x : Fin 22 => ((g * h : M22) : Equiv.Perm (Fin 22)) x) =
    Array.ofFn (fun x : Fin 22 => (tab g).getD ((tab h).getD x.val 0).val 0)
  refine congrArg (Array.ofFn (n := 22)) (funext fun x => ?_)
  rw [tab_getD, tab_getD, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem tab_one : tab 1 = tid := by
  show Array.ofFn (fun x : Fin 22 => ((1 : M22) : Equiv.Perm (Fin 22)) x) =
    Array.ofFn (fun x : Fin 22 => x)
  rfl

theorem tab_injective {g h : M22} (hgh : tab g = tab h) : g = h := by
  apply Subtype.ext
  ext x
  rw [← tab_getD, ← tab_getD, hgh]

theorem tab_evalW (F : Fin 5 → M22) (w : List (Fin 5 × Bool)) :
    tab (evalW F w) = evalT (fun i => tab (F i)) (fun i => tab (F i)⁻¹) w := by
  induction w with
  | nil =>
    rw [show evalW F [] = 1 from rfl, tab_one]
    rfl
  | cons x w ih =>
    have e : evalW F (x :: w) = cond x.2 (F x.1) (F x.1)⁻¹ * evalW F w := by
      simp [evalW]
    rw [e, tab_mul, ih]
    rcases x with ⟨i, b⟩
    cases b <;> rfl

theorem genTL_getD (i : Fin 5) : genTL.getD i tid = tab (gen i) := by
  fin_cases i <;> rfl

theorem genTiL_getD (i : Fin 5) : genTiL.getD i tid = tab (gen i)⁻¹ := by
  fin_cases i <;> rfl

theorem wtab_eq (s : String) : wtab genTL genTiL s = tab (evalW gen (word s)) := by
  rw [tab_evalW]
  unfold wtab
  simp only [genTL_getD, genTiL_getD]

theorem fixesF_tab {g : M22} : fixesF (tab g) = true ↔ g ∈ barA2 := by
  rw [mem_barA2]
  simp only [fixesF, List.all_eq_true, beq_iff_eq, tab_getD]

theorem presF_tab {g : M22} : presF (tab g) = true ↔
    ∀ p ∈ m22HexadL, (g : Equiv.Perm (Fin 22)) p ∈ m22HexadL := by
  simp only [presF, List.all_eq_true, List.contains_iff_mem, tab_getD]

theorem mem_ptHex_iff_tab {g : M22} : g ∈ m22PtHexStab ↔
    (tab g).getD 0 0 = 0 ∧ presF (tab g) = true := by
  rw [M22Witt.mem_m22PtHexStab_iff, presF_tab, show (0 : ℕ) = (0 : Fin 22).val from rfl,
    tab_getD]

theorem exists_bWord {σ : M22}
    (h1 : σ ∈ m22TwoStab) (h2 : σ ∈ m22PtHexStab) :
    ∃ s ∈ bWords, evalW gen (word s) = σ := by
  obtain ⟨h0, h11⟩ := mem_m22TwoStab_iff.mp h1
  have hh := (M22Witt.mem_m22PtHexStab_iff.mp h2).2
  have hc := not_of_count_eq_zero _ count_B σ
  simp only [not_and, not_not] at hc
  obtain ⟨T, hT, hσT⟩ := hc h0 h11 hh
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
  refine ⟨s, hs, ?_⟩
  apply Subtype.ext
  ext x
  rw [hσT x, tab_getD]

end CFSG.Quasithin.L34Amalgam
