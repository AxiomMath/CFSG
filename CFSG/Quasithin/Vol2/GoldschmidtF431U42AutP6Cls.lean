module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bA
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bE16

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def e0B : Bh := fhB * xB

theorem t0A_sq : t0A * t0A = 1 := by
  have h : comp (Tl.getD 20 []) (Tl.getD 20 []) = idL := by decide +kernel
  have h1 : RepL (comp (Tl.getD 20 []) (Tl.getD 20 [])) (1 : P45) := by
    rw [h]
    exact repL_one 45
  exact Subtype.ext (eq_of_repL (repL_mul repL_t0A repL_t0A) h1)

theorem t0A_ne_one : t0A ≠ 1 := by
  have h : Tl.getD 20 [] ≠ idL := by decide +kernel
  intro h1
  exact h (repL_unique repL_t0A (h1 ▸ repL_one 45))

theorem comp_comm_of_comm {v g : Ah} {vL gL : PL} (hv : RepL vL (v : P45))
    (hg : RepL gL (g : P45)) (h : g * v = v * g) : comp gL vL = comp vL gL := by
  have h1 := repL_mul hg hv
  have h2 := repL_mul hv hg
  have : (g : P45) * (v : P45) = (v : P45) * (g : P45) := congrArg Subtype.val h
  rw [this] at h1
  exact repL_unique h1 h2

theorem comm_of_comp_comm {v g : Ah} {vL gL : PL} (hv : RepL vL (v : P45))
    (hg : RepL gL (g : P45)) (h : comp gL vL = comp vL gL) : g * v = v * g :=
  Subtype.ext (eq_of_repL (l := comp gL vL) (repL_mul hg hv) (h ▸ repL_mul hv hg))

theorem isGoodInv_of_conj_fhat {u g : Ah} (hu : u ∈ Bh)
    (hu2 : u * u = 1) (hg : g * u * g⁻¹ = fhatA) : IsGoodInv u := by
  have hneg : signA u = -1 := by
    have := signA_conj' g u
    rw [hg, signA_fhatA] at this
    exact this.symm
  refine ⟨hu, ?_, by rw [pow_two]; exact hu2, ?_⟩
  · intro h
    have := (signA_eq_one_iff u).2 h
    rw [hneg] at this
    exact absurd this (by decide)
  · have e : u = g⁻¹ * fhatA * g⁻¹⁻¹ := by
      rw [← hg]
      group
    rw [e, card_centralizer_conj fhatA g⁻¹]
    exact card_centralizer_fhat

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem AutCtx.comm_z (c : AutCtx G M₁ M₂ z) {h : G} (hh : h ∈ M₁ ⊓ M₂) : h * z = z * h :=
  Subgroup.mem_centralizer_iff.1 c.zc.2 h hh

end CFSG.Quasithin.H13.F431.U42Aut
