module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U8
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Rho

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

theorem u42AutRho :
    U42AutRho := by
  intro G _ _ M₁ M₂ z c R hR hTR hC h54 h55 ι h1 _
  have h : F55Ctx c R := F55Ctx.of_conf c hR hTR hC h54
  obtain ⟨hX, hE, -⟩ := h55
  have hE' : Nat.card ↥(Eg c) = 1440 := hE
  obtain ⟨qd⟩ := exists_QData c h
  obtain ⟨ρ, hρ, hρ2⟩ := exists_rho c h
  have hr : RhoCtx c R ρ := ⟨hρ, hρ2⟩
  have hρE : ρ ∉ Eg c := rho_not_mem_Eg c hr ι h1
  have hall : ∀ u : G, u * u = 1 → u ≠ 1 → IsConj u z ∨ IsConj u (c.iso.toG fhB) :=
    fun u hu2 hu1 => hC.2.2.2.2 u (by rw [pow_two]; exact hu2) hu1
  have hρQ := rho_cen_Q c h hr hρE hE' hall qd
  exact ⟨ρ, rho_not_mem_M0 c hr ι h1, by rw [pow_two]; exact hρ2,
    rho_five c h hr hρE hE' hX qd hρQ ι h1⟩

end CFSG.Quasithin.H13.F431.U42Aut
