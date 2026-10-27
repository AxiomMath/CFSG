module

public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Out
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F438

set_option linter.unusedSectionVars false

@[expose] def burnsideF4j_OddIndexInput : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → Odd Gp.index

theorem burnsideF4j_F_4_38_inst {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hodd : Odd Gp.index)
    (hgen : oPPrime 2 Gp = Gp) {T : Subgroup M} (hT : ChF.IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε)) :
    T = SinM Gp β ε ∧ oPPrime 2 (⊤ : Subgroup E) = Gp ∧ Odd Gp.index := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set b := burnsideF4d_bOne β ε with hbdef
  have hb : Function.Injective b := burnsideF4j_bOne_injective hyp
  have hinter : MiOne β ε ⊓ MiTwo β ε = subImg b (M₁ ⊓ M₂) :=
    burnsideF4d_inter_eq β hyp.faithful ε hyp.inj
  have hT' : IsSylowTwoOf T (subImg b (M₁ ⊓ M₂)) := hinter ▸ hT
  obtain ⟨Tb, hTbY, hTbN, hTbeq⟩ := burnsideF4j_exists_preimage b hb hT'.1
  have hTbsyl : IsSylowTwoOf Tb (M₁ ⊓ M₂) :=
    (burnsideF4j_isSylow_subImg_iff b hb hTbN inf_le_left).1 (hTbeq ▸ hT')
  have h2el : ∀ x : E, (∃ n : ℕ, orderOf x = 2 ^ n) → x ∈ Gp := by
    rintro x ⟨n, hn⟩
    exact burnsideF4d_two_elt_mem hodd (k := n) (by rw [← hn]; exact pow_orderOf_eq_one x)
  have hTbG : Tb ≤ Gp := by
    intro x hx
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hTbsyl.2.1 ⟨x, hx⟩
    exact h2el x ⟨n, by rw [← Subgroup.orderOf_mk x hx]; exact hn⟩
  have hTbS : Tb = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    rw [← burnsideF4j_sylow_inf_Gp hyp.amalgam hTbsyl, inf_eq_left.mpr hTbG]
  refine ⟨?_, ?_, hodd⟩
  · rw [← hTbeq, hTbS, burnsideF4d_SinM_eq]
  · apply le_antisymm
    · refine (Subgroup.closure_le Gp).mpr ?_
      rintro x ⟨-, n, hn⟩
      exact h2el x ⟨n, hn⟩
    · rw [← hgen]
      exact Subgroup.closure_mono (fun x hx => ⟨Subgroup.mem_top x, hx.2⟩)

end F438

section OddF4

set_option linter.unusedSectionVars false

open CFSG.Quasithin.H13.F431.TwoF4 CFSG.ComponentClassification.OuterAutomorphisms

theorem burnsideF4j_odd_index_F4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) (hf : 3 ≤ f) : Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  have hmodel := burnsideF4g_lieModel_F4tw hf hyp.model
  obtain ⟨a, K, _, _, _, ha, hfa, hK0, ⟨e⟩⟩ := f4_model_data hmodel
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK0, hfa]
  have hm := f431ModelFacts_f4 f ↥Gp hmodel
  have hOut : Odd (Nat.card (Outer ↥Gp)) := by
    have h := Nat.card_congr (equivalence e).toEquiv
    rw [h, (outer_gm ha hK).2]
    exact odd_two_mul_add_one a
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hS : (MulAut.conj : ↥Gp →* MulAut ↥Gp).range ≤ (burnsideF4d_rho Gp).range := by
    rintro _ ⟨d, rfl⟩
    refine ⟨(d : E), ?_⟩
    ext x
    simp [burnsideF4d_rho_apply]
  have h := odd_card_div_of_outer hm.2 (burnsideF4d_rho Gp).range hS hOut
  have hcard : Nat.card ↥(burnsideF4d_rho Gp).range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hcard] at h
  have h2 := Subgroup.card_mul_index Gp
  have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
  rwa [show Nat.card E / Nat.card ↥Gp = Gp.index by
    rw [← h2, Nat.mul_div_cancel_left _ hpos]] at h

theorem burnsideF4j_odd_index_Tits {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits 2 f Gp M₁ M₂) : Odd Gp.index := by
  rw [hyp.canonical (Or.inr rfl), Subgroup.index_top]
  exact odd_one

end OddF4

section OddSp

theorem burnsideF4j_odd_index_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 3 ≤ f) (hfo : Odd f) : Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  have hyp4 := hyp.toHypF_4_4g
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp4
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamSp4 (f := f) (by omega) marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_Sp4 (by omega : 2 ≤ f) hyp.model
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp4.centralizer_trivial
  let X := burnsideF4d_lieExtE hyp4 hTD
  have hK : Nat.card ↥X.K = Nat.card E := by
    have : X.K = (burnsideF4d_rho Gp).range := burnsideF4d_K_eq hyp4 hTD
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  by_contra hnodd
  have hnodd' : ¬ Odd (Nat.card ↥X.K / Nat.card ↥Gp) := by
    rw [hK]
    have := Subgroup.card_mul_index Gp
    have hpos : 0 < Nat.card ↥Gp := Nat.card_pos
    rw [show Nat.card E / Nat.card ↥Gp = Gp.index by
      rw [← this, Nat.mul_div_cancel_left _ hpos]]
    exact hnodd
  obtain ⟨m, -, -, -, -, -, -, -, -, -, hfm, -⟩ :=
    CFSG.Quasithin.H13.F431.SpOut2.exists_outCtx hmodel X.toLieAmalgamExt hnodd'
  rw [hfm] at hfo
  exact (Nat.not_even_iff_odd.mpr hfo) (even_two_mul m)

end OddSp

end CFSG.ASVolI
