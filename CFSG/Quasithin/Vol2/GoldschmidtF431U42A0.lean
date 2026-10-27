module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Norm
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair5

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

theorem center_eq_bot : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : z ∈ Subgroup.centralizer ({xY} : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subgroup.mem_center_iff.1 hz _
  rw [centralizer_x, mem_P1_iff] at hc
  refine Subgroup.mem_bot.2 (Subtype.ext (Equiv.ext fun j => ?_))
  obtain ⟨g, hg⟩ : j ∈ MulAction.orbit Y (0 : Fin 45) := by
    rw [orbit_zero]
    exact Set.mem_univ j
  have hg' : (g : P45) 0 = j := hg
  have hcomm := congrArg (fun w : Y => (w : P45) 0) (Subgroup.mem_center_iff.1 hz g)
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hc, hg'] at hcomm
  simpa using hcomm.symm

@[expose] noncomputable def A0 :
    LieAmalgamExt Y where
  Mbar := (MulAut.conj : Y →* MulAut Y).range
  TD := T
  P1 := P1
  P2 := P2
  inn_le := le_rfl
  yam := isYAmalgamPair
  diag := by
    rintro φ ⟨y, rfl⟩ h
    have hy : y ∈ Subgroup.normalizer (B0 : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      simpa [autStab, B0] using h b
    rw [normalizer_B0] at hy
    have hy1 : y ∈ P1 := B0_le_P1 hy
    have hy2 : y ∈ Subgroup.normalizer (P1 : Set Y) := Subgroup.le_normalizer hy1
    intro x
    simpa using Subgroup.mem_normalizer_iff.1 hy2 x

end CFSG.Quasithin.H13.F431.U42
