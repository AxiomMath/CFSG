module

public import CFSG.RankThree.GF2n.Smith81.Lin28CondMain
public import CFSG.RankThree.GF2n.Smith81.Lin26Three

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} {x : G}

theorem Sit.mem_Lgen (h28c : Lin28CondStatement) (hb : Smith1981Below (Nat.card G))
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    (hne : Q ⊓ QB X ≠ ⊥) : x ∈ Lgen M (LB M Q B) := by
  obtain ⟨A, hA, hAle⟩ := h28c G M Q Z B X x n V₁ V₂ hb hc hS hn hs hne
  have hAQ : A ≤ Q := hAle.trans inf_le_left
  obtain ⟨hAZ, -, hXLA⟩ := lin29_of_sit hs hA hAQ (hAle.trans inf_le_right)
  have hcA : Ctx M Q Z A := ⟨hc.hyp, hA, hAQ, hAZ⟩
  rcases (LinSetup.transv_of_conj hc hS hn hcA).1 with hAV | hAV
  · exact LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hcA hAV (hXLA hs.mem)
  · exact LinSetup.LB_le_Lgen_of_le_V₁ hc hS.symm hn hcA hAV (hXLA hs.mem)

theorem lin212C7_conj_of_cent (h7 : Lin212C7Statement) (hb : Smith1981Below (Nat.card G))
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    (hne : Q ⊓ QB X ≠ ⊥) (hxL : x ∈ Lgen M (LB M Q B)) {a : G} (haM : a ∈ M)
    (ha : ∀ s ∈ Lgen M (LB M Q B), a * s * a⁻¹ * s⁻¹ ∈ Q) :
    ∃ q ∈ Q, a * x * a⁻¹ = q * x * q⁻¹ := by
  have hxM : x ∈ M := hs.memM
  have h1 : x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x⁻¹⁻¹ ∈ Q :=
    conj_mem_Q hc.hyp (M.inv_mem hxM) (ha x hxL)
  have e : x⁻¹ * (a * x * a⁻¹ * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * a * x * a⁻¹ := by group
  rw [e] at h1
  exact h7 G M Q Z B n V₁ V₂ hb hc hS hn X x hs hne a _ h1 (by group)

theorem lin212Compl_of_cond (h28c : Lin28CondStatement) : Lin212ComplStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn X x hs hne
  obtain ⟨p, hp, hp2, A, hQA, hAM, hAn, hpow, hAc, c, hcA, hfpf⟩ :=
    LinSetup.exists_scalar_normal hb hc hS hn
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ2 : IsPGroup 2 Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hxL := Sit.mem_Lgen h28c hb hc hS hn hs hne
  obtain ⟨K, hKM, hKQ, hKs, hxK⟩ := exists_compl_mem_of_frattini hp2 hQ2 hQA hAM
    hc.hyp.Q_normal.2 hAn hpow hcA hfpf hs.memM fun a ha =>
      lin212C7_conj_of_cent (lin212C7_of h28c) hb hc hS hn hs hne hxL (hAM ha) (hAc a ha)
  exact ⟨K, hKM, hKQ, hKs, 1, Q.one_mem, by simpa using hxK⟩

theorem lin212Compl_holds : Lin212ComplStatement :=
  lin212Compl_of_cond lin28CondStatement_holds

end CFSG.RankThree.GF2n.Smith81
