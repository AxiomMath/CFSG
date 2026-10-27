module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Forest
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuAdj

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

open scoped Pointwise

set_option linter.unusedSectionVars false

@[expose] def PFix (t : Equiv.Perm (Fin 1755)) (v : Fin 2925) : Prop := ∀ p ∈ titsLine v, t p = p

@[expose] def PLinked (t : Equiv.Perm (Fin 1755)) (v : Fin 2925) : Prop :=
  ∀ p ∈ titsLine v, ∃ w, PFix t w ∧ w ≠ v ∧ p ∈ titsLine w

theorem pfix_lineHom {t : Equiv.Perm (Fin 1755)} {c : ↥TA} (hc : c.1 * t = t * c.1)
    {w : Fin 2925} (hw : PFix t w) : PFix t (titsLineHom c w) := by
  intro p hp
  rw [titsLine_lineHom, Finset.mem_smul_finset] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have h1 : t (c.1 q) = c.1 (t q) := (congrArg (fun f => f q) hc).symm
  rw [Equiv.Perm.smul_def, h1, hw q hq]

theorem plinked_lineHom {t : Equiv.Perm (Fin 1755)} {c : ↥TA} (hc : c.1 * t = t * c.1)
    {v : Fin 2925} (hv : PLinked t v) : PLinked t (titsLineHom c v) := by
  intro p hp
  rw [titsLine_lineHom, Finset.mem_smul_finset] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨w, hw, hwv, hqw⟩ := hv q hq
  refine ⟨titsLineHom c w, pfix_lineHom hc hw, fun e => hwv ((titsLineHom c).injective e), ?_⟩
  rw [titsLine_lineHom]
  exact Finset.smul_mem_smul_finset hqw

theorem pfl_tEl : PFix tEl.1 0 ∧ PLinked tEl.1 0 ∧ ∀ v, PFix tEl.1 v → PLinked tEl.1 v → v = 0 := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate4180
  rw [tEl_eq]
  exact h

theorem smul_titsLine_zero {c : ↥TA} (hc : c.1 * tEl.1 = tEl.1 * c.1) :
    c.1 • titsLine 0 = titsLine 0 := by
  obtain ⟨h0, hl0, huniq⟩ := pfl_tEl
  rw [← titsLine_lineHom, huniq _ (pfix_lineHom hc h0) (plinked_lineHom hc hl0)]

theorem cent_t_model : Subgroup.centralizer ({tM} : Set ↥twoF4M) ≤ twoF4M2 := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hxA : x.1 ∈ TA := by
    rw [← twoF4M_eq_titsA]
    exact x.2
  have hc : (⟨x.1, hxA⟩ : ↥TA).1 * tEl.1 = tEl.1 * (⟨x.1, hxA⟩ : ↥TA).1 := congrArg Subtype.val hx
  have := smul_titsLine_zero hc
  exact (Subgroup.mem_subgroupOf).2 ((mem_twoF4N_iff hxA).2 this)

end CFSG.Quasithin.H13.F431.TwoF4
