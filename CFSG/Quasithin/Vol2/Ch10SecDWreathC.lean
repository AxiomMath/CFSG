module

public import CFSG.Quasithin.Vol2.Ch10SecDWreathB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin Equiv

@[expose] def wc1 : Perm (Fin 5) := swap 0 1 * swap 1 2

@[expose] def wc2 : Perm (Fin 5) := swap 2 3 * swap 3 4

theorem wc1_mem : wc1 ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem wc2_mem : wc2 ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem wc1_ne_one : wc1 ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem eq_one_of_comm_wc : ∀ x : Perm (Fin 5), x * wc1 = wc1 * x → x * wc2 = wc2 * x → x = 1 := by
  decide +kernel

theorem comm_of_comm_wrIota {f : Multiplicative (ZMod 2) → Perm (Fin 5)}
    {q : Multiplicative (ZMod 2)} {σ : Perm (Fin 5)}
    (h : wrIota q σ * wrBaseHom f = wrBaseHom f * wrIota q σ) : f q * σ = σ * f q := by
  rw [wrIota_eq, ← map_mul, ← map_mul] at h
  have := congrFun (wrBaseHom_injective h) q
  simp only [Pi.mul_apply, Pi.mulSingle_eq_same] at this
  exact this.symm

theorem centralizer_wrBase_eq_bot : Subgroup.centralizer (wrBase : Set SymFiveWrTwo) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hmem : ∀ q σ, σ ∈ alternatingGroup (Fin 5) → wrIota q σ ∈ wrBase := by
    intro q σ hσ
    refine ⟨rfl, fun x => ?_⟩
    show (Pi.mulSingle q σ : Multiplicative (ZMod 2) → Perm (Fin 5)) x ∈ alternatingGroup (Fin 5)
    by_cases hx : x = q
    · subst hx
      rw [Pi.mulSingle_eq_same]
      exact hσ
    · rw [Pi.mulSingle_eq_of_ne hx]
      exact one_mem _
  have hcomm : ∀ q σ, σ ∈ alternatingGroup (Fin 5) → wrIota q σ * z = z * wrIota q σ :=
    fun q σ hσ => Subgroup.mem_centralizer_iff.mp hz _ (hmem q σ hσ)
  have hr : z.right = 1 := by
    rcases zmod2_cases z.right with h | h
    · exact h
    · exfalso
      have h1 := congrArg (fun w : SymFiveWrTwo => w.left 1) (hcomm 1 wc1 wc1_mem)
      change (Pi.mulSingle 1 wc1 : Multiplicative (ZMod 2) → Perm (Fin 5)) 1 *
          z.left ((1 : Multiplicative (ZMod 2))⁻¹ * 1) =
        z.left 1 * (Pi.mulSingle 1 wc1 : Multiplicative (ZMod 2) → Perm (Fin 5))
          (z.right⁻¹ * 1) at h1
      have hne : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ * 1 ≠ 1 := by decide
      have e1 : (1 : Multiplicative (ZMod 2))⁻¹ * 1 = 1 := by decide
      rw [h, Pi.mulSingle_eq_of_ne hne, Pi.mulSingle_eq_same, e1, mul_one] at h1
      exact wc1_ne_one (mul_right_cancel (h1.trans (one_mul _).symm))
  rw [eq_wrBaseHom hr] at hcomm ⊢
  have hf : z.left = 1 := by
    funext q
    exact eq_one_of_comm_wc _ (comm_of_comm_wrIota (hcomm q wc1 wc1_mem))
      (comm_of_comm_wrIota (hcomm q wc2 wc2_mem))
  rw [hf, map_one]

end CFSG.Quasithin.Vol2.Ch10.SecD
