module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8A6Data
public import CFSG.Quasithin.Background.GoldschmidtTDE68Bar

public section

namespace CFSG.Quasithin.E6.Alt.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Unc25A6 CFSG.Quasithin.E6.Bar

@[expose] def invCentD : List (List ℕ) :=
  Core.autL.filter fun c => Core.cmul c c == Core.cid && c != Core.cid &&
    Core.dLit.all fun d => Core.cmul c d == Core.cmul d c

theorem invCentD_length : invCentD.length = 3 := by decide +kernel

theorem invCentD_dvd : ∀ c ∈ invCentD, (Core.cpslList c).length ∣ 24 := by decide +kernel

theorem invCentD_gen : ∃ c₁ ∈ invCentD, ∃ c₂ ∈ invCentD, (Core.cpslList c₁).length = 24 ∧
    (Core.cpslList c₂).length = 24 ∧ ∃ x ∈ Core.cpslList c₂, x ∉ Core.cpslList c₁ := by
  decide +kernel

theorem exists_aut_of_code {c : List ℕ} (hc : c ∈ Core.autL) :
    ∃ x : P10, x ∈ A6Models.autA6 ∧ code x = c := by
  unfold Core.autL at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨y, hy, hc⟩ := hc
  rw [List.mem_map] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
  rw [← autRepsP_code, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  refine ⟨y' * r', A6Models.autA6.mul_mem (psl29_le_autA6 hy') ?_, code_mul _ _⟩
  rw [autA6_eq]
  exact autReps_mem_closure r' hr'

end CFSG.Quasithin.E6.Alt.A6
