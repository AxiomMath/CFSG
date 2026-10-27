module

public import CFSG.Quasithin.H13.GoldschmidtU43EData
public import CFSG.Quasithin.H13.GoldschmidtU43CGen
public import CFSG.Quasithin.H13.GoldschmidtU43CRel2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace Hyp

variable [Finite G] {z : G} (h : Hyp z)
include h

theorem exists_jwSetup_mem_U : ∃ S : JWSetup z, (S.A : G) ∈ Uz z := by
  obtain ⟨t, w, htU, htz, ht1, ht2, -⟩ := h.exists_swap
  have ht : t ∈ S z := ⟨htU, ht2, ht1, htz⟩
  obtain ⟨w, s⟩ := h.exists_swap_data ht
  obtain ⟨a₁, a₂, h₁, h₂, h12⟩ := s.exists_two_good
  have e : Two z t w a₁ a₂ := ⟨s, h₁, h₂, h12⟩
  obtain ⟨R, hR⟩ := h.exists_SylR
  obtain ⟨u, u', σ₁, x, n₁, d⟩ := e.exists_data hR
  have huv : u * (u * u') = u' := by rw [← mul_assoc, d.hu2, one_mul]
  have hqa : q (h.tv x) = 1 := by
    rw [d.hx]
    exact q_plane1 n₁ d.hn₁ d.hn₁0
  have hA2 : uK x * uK x = zK z := by
    rw [← uK_mul, h.mul_self_of_q_one hqa]
    rfl
  refine ⟨⟨t, w, a₁, a₂, e, R, hR, uK x, σ₁, u, u * u',
    jw13_of_data h hR d.hu d.hu' d.hu2 d.hu'2 d.hcomm d.hp d.hσR d.hρfix d.hn₁ d.hn₁0 d.hcn₁
      d.hrefl d.hx d.hsign, e.closure_eq_top hR d, hA2, d.hσR, d.hu, ?_,
    e.swap.lift_mem_Eg e.ha hR d.hu d.hact, ?_⟩, x.2⟩
  · rw [huv]
    exact d.hu'
  · rw [huv]
    exact e.swap.lift_mem_Eg e.ha' hR d.hu' d.hact'

end Hyp

end CFSG.Quasithin.H13.U43
