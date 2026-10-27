module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79NF

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace J6

def Cl1 (ρ : S6) : Prop := ∃ γ : S6, γ * ρ * γ⁻¹ = a2

def Cl3 (ρ : S6) : Prop := ∃ γ : S6, γ * ρ * γ⁻¹ = sg3

theorem cl1_e1 : Cl1 e1 := conj_e1_a2

theorem cl1_pp : Cl1 pp := conj_pp_a2

theorem cl1_qq : Cl1 qq := conj_qq_a2

theorem cl3_x1 : Cl3 (e1 * v1) := conj_x1_sg3

theorem cl3_x2 : Cl3 (e1 * v2) := conj_x2_sg3

theorem cl3_x3 : Cl3 (e1 * v3) := conj_x3_sg3

theorem cl3_y : Cl3 (e1 * pp * qq) := conj_y_sg3

end J6

namespace Std

variable (S : Std b t b₁ b₂ J)

include S

theorem hc_cl1 {ρ : J6.S6} (hρ : J6.Cl1 ρ) : HC (S.ι ρ) (S.ι J6.a2) := S.HC_ι hρ

theorem hc_cl3 {ρ : J6.S6} (hρ : J6.Cl3 ρ) : HC (S.ι ρ) (S.ι J6.sg3) := S.HC_ι hρ

theorem hc_t_cl1 {ρ : J6.S6} (hρ : J6.Cl1 ρ) : HC (t * S.ι ρ) (t * S.ι J6.a2) := S.HC_tι hρ

theorem hc_t_cl3 {ρ : J6.S6} (hρ : J6.Cl3 ρ) : HC (t * S.ι ρ) (t * S.ι J6.sg3) := S.HC_tι hρ

theorem nf_t_cl1 {ρ : J6.S6} (hρ : J6.Cl1 ρ) : ¬ HC t (S.ι ρ) :=
  fun hc => S.nf_t_a2 (hc.trans (S.hc_cl1 hρ))

theorem nf_t_cl3 {ρ : J6.S6} (hρ : J6.Cl3 ρ) : ¬ HC t (S.ι ρ) :=
  fun hc => S.nf_t_sg3 (hc.trans (S.hc_cl3 hρ))

theorem nf_cl1_cl3 {ρ ρ' : J6.S6} (hρ : J6.Cl1 ρ) (hρ' : J6.Cl3 ρ') : ¬ HC (S.ι ρ) (S.ι ρ') :=
  fun hc => S.nf_a2_sg3 ((S.hc_cl1 hρ).symm.trans (hc.trans (S.hc_cl3 hρ')))

theorem nf_tcl1_cl1 {ρ ρ' : J6.S6} (hρ : J6.Cl1 ρ) (hρ' : J6.Cl1 ρ') :
    ¬ HC (t * S.ι ρ) (S.ι ρ') :=
  fun hc => S.nf_a2_tia2 ((S.hc_t_cl1 hρ).symm.trans (hc.trans (S.hc_cl1 hρ')))

theorem nf_tcl3_cl3 (h34 : R34Stmt b b₁ b₂) {ρ ρ' : J6.S6} (hρ : J6.Cl3 ρ) (hρ' : J6.Cl3 ρ') :
    ¬ HC (t * S.ι ρ) (S.ι ρ') :=
  fun hc => S.nf_sg3_tisg3 h34 ((S.hc_t_cl3 hρ).symm.trans (hc.trans (S.hc_cl3 hρ')))

theorem nf_tcl1_cl3 {ρ ρ' : J6.S6} (hρ : J6.Cl1 ρ) (hρ' : J6.Cl3 ρ') :
    ¬ HC (t * S.ι ρ) (S.ι ρ') :=
  fun hc => S.nf_tia2_sg3 ((S.hc_t_cl1 hρ).symm.trans (hc.trans (S.hc_cl3 hρ')))

theorem nf_tcl3_cl1 {ρ ρ' : J6.S6} (hρ : J6.Cl3 ρ) (hρ' : J6.Cl1 ρ') :
    ¬ HC (t * S.ι ρ) (S.ι ρ') :=
  fun hc => S.nf_tisg3_a2 ((S.hc_t_cl3 hρ).symm.trans (hc.trans (S.hc_cl1 hρ')))

theorem nf_t_tcl1 {ρ : J6.S6} (hρ : J6.Cl1 ρ) : ¬ HC t (t * S.ι ρ) :=
  fun hc => S.nf_t_tia2 (hc.trans (S.hc_t_cl1 hρ))

theorem nf_t_tcl3 (h34 : R34Stmt b b₁ b₂) {ρ : J6.S6} (hρ : J6.Cl3 ρ) : ¬ HC t (t * S.ι ρ) :=
  fun hc => S.nf_t_tisg3 h34 (hc.trans (S.hc_t_cl3 hρ))

theorem nf_cen_cl1 {r : H} (hr : ∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H), y * r = r * y)
    {ρ : J6.S6} (hρ : J6.Cl1 ρ) : ¬ HC r (S.ι ρ) := fun hc =>
  S.hyp.nf_I' S.ι_a2_sq S.ι_a2_ne_one S.b₁_mem_B₁ S.b₁_ne_one hr (S.ι_comm_b J6.a2).symm
    S.b₁_comm_ι_a2 (hc.trans (S.hc_cl1 hρ))

theorem nf_cen_cl3 {r : H} (hr : ∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H), y * r = r * y)
    {ρ : J6.S6} (hρ : J6.Cl3 ρ) : ¬ HC r (S.ι ρ) := fun hc =>
  S.hyp.nf_I' S.ι_sg3_sq S.ι_sg3_ne_one S.d_mem_B₁ S.d_ne_one hr (S.ι_comm_b J6.sg3).symm
    S.d_comm_ι_sg3 (hc.trans (S.hc_cl3 hρ))

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
