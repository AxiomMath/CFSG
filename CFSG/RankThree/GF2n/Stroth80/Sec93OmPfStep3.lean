module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Step3

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem n12Lemma3_of_data (h34 : Stroth34Statement) {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs5 : Sec5Hyp hc n t)
    (hr : Sec7A hc t r)
    (hchi : IsChiIso Q (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
      (Vt M (LB M Q B) B Z t) Z t)
    (hdec : Wt Q (Vt M (LB M Q B) B Z t) ≤ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
    (hNW : ∀ s ∈ hc.CN t, ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅s, x⁆ ∈ Vt M (LB M Q B) B Z t) :
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ a ∈ Q, g * a * g⁻¹ ∈ Q) ∧
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ z ∈ Z, g * z * g⁻¹ = z) ∧
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ a ∈ Q, ⁅g, a⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
    (∀ g ∈ n12X hc t ∪ n12Y hc t r, ∀ a ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅g, a⁆ ∈ Vt M (LB M Q B) B Z t) ∧
    (∀ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∀ b ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), ⁅a, b⁆ = 1) ∧
    (∀ a ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∀ b ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t), ⁅a, b⁆ = 1) ∧
    Wt Q (Vt M (LB M Q B) B Z t) = QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) ⊔
      QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t) ⊔ Vt M (LB M Q B) B Z t := by
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hc' : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    Vt_le_Wt_of_34 h34 hc hs5
  have hSec : SecHyp (Rt M (LB M Q B) t) Q Z := n12l3_secHyp hc (hc.Rt_le_M t)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg a ha
    exact n12l3_normalizes_Q hc (n12l3_union_facts hc hrM hg).1 ha
  · intro g hg z hz
    exact n12l3_conj_eq_of_H0 (n12l3_union_facts hc hrM hg).2.1 hz
  · intro g hg a ha
    obtain ⟨hgR, hgV⟩ := Ctx.mem_CN.mp (n12l3_union_facts hc hrM hg).2.2
    exact n12l3_comm_mem_W hSec hchi (hc.Vt_le_Q t) (n12l3_Z_le_W hc t) le_sup_left hgR hgV ha
  · intro g hg a ha
    exact hNW g (n12l3_union_facts hc hrM hg).2.2 a ha
  · intro a ha b hb
    exact n12l3_comm_inf_QB hc a (n12l3_mem_inf_QB ha) b (n12l3_mem_inf_QB hb)
  · intro a ha b hb
    exact n12l3_comm_inf_QB hc' a (n12l3_mem_inf_QB ha) b (n12l3_mem_inf_QB hb)
  · exact le_antisymm hdec (sup_le (sup_le inf_le_right inf_le_right) hVW)

end CFSG.RankThree.GF2n.Stroth80
