module

public import CFSG.Quasithin.H13.GoldschmidtU43EAsm1
public import CFSG.Quasithin.H13.GoldschmidtU43EVR5
public import CFSG.Quasithin.H13.GoldschmidtU43EVSR6
public import CFSG.Quasithin.H13.GoldschmidtU43EVSR7

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

omit [Finite G] in
theorem A_sq : (S.A : G) ^ 2 = z := by
  rw [pow_two]
  exact congrArg Subtype.val S.hAA

theorem jwClose_of_rels (e : S.Nbar ≃* alternatingGroup (Fin 6)) {V₃ : Subgroup G}
    (hV : S.IsV3 V₃) (hAU : (S.A : G) ∈ Uz z)
    (h19 : ((S.u : G) * z * S.rho3 r.ρ) ^ 3 = 1)
    (h20 : ((S.u : G) * (S.v : G) * (S.rho3 r.ρ)⁻¹ * S.rho4 r.ρ) ^ 3 = 1) :
    JWClose (S.A : G) (S.σ₁ : G) (S.u : G) (S.v : G) r.ρ where
  r16 := S.rel_r16 r e hV hAU
  r17 := S.rel_r17 r e hV hAU
  r18 := S.rel_r18 r e hV hAU
  r19 := by
    rw [S.A_sq]
    exact h19
  r20 := h20

end JWSetup

theorem u43Closing : U43Closing := by
  intro G _ _ z S hAU he r
  obtain ⟨e⟩ := he
  obtain ⟨V₃, hV⟩ := S.exists_isV3 hAU
  exact S.jwClose_of_rels r e hV hAU (S.rel_r19 e hV hAU r) (S.rel_r20 e hV hAU r)

end CFSG.Quasithin.H13.U43
