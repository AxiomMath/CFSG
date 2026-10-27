module

public import CFSG.Quasithin.Background.HParabL34
public import CFSG.Quasithin.Background.HFL3Q

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Fischer Matrix CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34M
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem det_sM (p : ℕ) : (sM p).det = 1 := by
  simp [sM, um, Matrix.det_fin_three]

theorem fc_code (x : F4) : fc (x.code : ℕ) = x := f4_eq_of_code (by
  show (x.code : ℕ) % 4 = x.code
  exact Nat.mod_eq_of_lt x.code.2)

theorem sM_mem_Q2 (t : ℕ) : (⟨sM (4 * t), det_sM _⟩ : SpecialLinearGroup (Fin 3) F4) ∈
    CFSG.Quasithin.H.L3Nine.Q2 F4 := by
  have h0 : fc (4 * t) = 0 := f4_eq_of_code (by show 4 * t % 4 = 0; omega)
  refine ⟨mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [sM, um]
  · fin_cases i <;> simp [sM, um]
  · show um (fc (4 * t)) (fc (4 * t / 4)) (fc (4 * t / 16)) 0 1 = 0
    simp [um, h0]

theorem QW9_eq_Q2 :
    QW9 = (CFSG.Quasithin.H.L3Nine.Q2 F4).map (rho9.comp SpecialLinearGroup.toGL) := by
  apply le_antisymm
  · rintro _ ⟨g, ⟨t, -, rfl⟩, rfl⟩
    exact ⟨⟨sM (4 * t), det_sM _⟩, sM_mem_Q2 t, congrArg rho9 (Units.ext rfl)⟩
  · rintro _ ⟨x, ⟨hxU, hx01⟩, rfl⟩
    obtain ⟨x00, x11, x22, x10, x20, x21⟩ := CFSG.Quasithin.H.L3Nine.uni3_entries hxU
    set b := (x : Matrix (Fin 3) (Fin 3) F4) 0 2 with hb
    set c := (x : Matrix (Fin 3) (Fin 3) F4) 1 2 with hc
    refine mem_QW9.2 ⟨(b.code : ℕ) + 4 * (c.code : ℕ), by omega, ?_⟩
    show rho9 (vG _) = rho9 (SpecialLinearGroup.toGL x)
    refine congrArg rho9 (Units.ext ?_)
    show sM (4 * ((b.code : ℕ) + 4 * (c.code : ℕ))) = (x : Matrix (Fin 3) (Fin 3) F4)
    have e1 : fc (4 * ((b.code : ℕ) + 4 * (c.code : ℕ))) = 0 :=
      f4_eq_of_code (by show 4 * ((b.code : ℕ) + 4 * (c.code : ℕ)) % 4 = 0; omega)
    have e2 : fc (4 * ((b.code : ℕ) + 4 * (c.code : ℕ)) / 4) = b := by
      rw [show 4 * ((b.code : ℕ) + 4 * (c.code : ℕ)) / 4 = (b.code : ℕ) + 4 * (c.code : ℕ) by
        omega]
      refine f4_eq_of_code ?_
      show ((b.code : ℕ) + 4 * (c.code : ℕ)) % 4 = b.code
      have := b.code.2
      omega
    have e3 : fc (4 * ((b.code : ℕ) + 4 * (c.code : ℕ)) / 16) = c := by
      rw [show 4 * ((b.code : ℕ) + 4 * (c.code : ℕ)) / 16 = c.code by
        have := b.code.2
        omega]
      exact fc_code c
    show um _ _ _ = _
    rw [e1, e2, e3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [um, x00, x11, x22, x10, x20, x21, hx01, hb, hc]

end CFSG.Quasithin.H.L34Z
