module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R1KBase
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Gen

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace R38K

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem odd_Opp_of_mem_B (h : FS79Hyp b t b₁ b₂ J) {β : H}
    (hβ : β ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) :
    Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers β)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine odd_Opp_of_no_two_sub (A := Subgroup.closure ({b, b₁, b₂} : Set H))
    (fun u hu => mem_Nor_zpowers_of_comm (h.B_comm hu hβ)) ?_ (fun R hR hBR => h.no_two R hR hBR)
  have hE := h.isElemAb_B
  haveI := hE.1
  exact IsElementaryAbelian.isPGroup 3 _

theorem conj_eq_of_comm' {g x : H} (hg : g * x = x * g) : g * x * g⁻¹ = x := by
  rw [hg]
  group

theorem conj_mul_of_comm {g x : H} (hg : g * b = b * g) :
    g * (b * x) * g⁻¹ = b * (g * x * g⁻¹) := by
  calc g * (b * x) * g⁻¹ = (g * b * g⁻¹) * (g * x * g⁻¹) := by group
    _ = b * (g * x * g⁻¹) := by rw [conj_eq_of_comm' hg]

theorem ctl_odd_of_conj {β target g : H} (hg : g * b = b * g) (hC : CtlEq b β)
    (hO : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers β))))) (e : g * β * g⁻¹ = target) :
    CtlEq b target ∧ Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers target)))) := by
  subst e
  exact ⟨Ctl34.ctlEq_conj hg hC, odd_Opp_conj hO⟩

theorem mul_mem_B {x : H} (hx : x ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) :
    b * x ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
  Subgroup.mul_mem _ (FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b)) hx

end R38K

end CFSG.RankThree.PartTwo.Sec21.FF81
