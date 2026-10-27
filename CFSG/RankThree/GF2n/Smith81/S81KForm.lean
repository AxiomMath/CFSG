module

public import CFSG.RankThree.GF2n.Smith81.S81KSchur
public import CFSG.RankThree.GF2n.Smith81.S81KFix
public import CFSG.RankThree.GF2n.Smith81.S81D6Model
public import CFSG.RankThree.GF2n.Smith81.S81XD6Geom
public import CFSG.RankThree.GF2n.Smith81.S81WIrrD6

public section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

section Nondeg


open CFSG.RankThree.GF2n.Smith81.E7Model

theorem betaWL_nondeg {K : Type} [Field K] (w : W K)
    (h : ∀ u : W K, D6X.betaWL K u w = 0) : w = 0 := by
  apply emb_injective
  rw [map_zero]
  refine beta_nondeg_V0 (v := emb K w) (fun b hb => emb_apply_of_not_mem w hb) ?_
  intro v hv
  obtain ⟨u, rfl⟩ := exists_emb_eq (mem_V0.2 fun b hb => hv b hb)
  have h1 := h u
  rw [D6X.betaWL_apply, betaW] at h1
  rw [beta_comm]
  exact h1

theorem EAut0_irreducible {K : Type} [Field K] [CharP K 2] (S : AddSubgroup (W K))
    (hS : ∀ g ∈ EAut0 K, ∀ s ∈ S, g s ∈ S) : S = ⊥ ∨ S = ⊤ :=
  LamW_irreducible_W S fun u hu s hs => hS (vAut0 K u) (Subgroup.mem_map_of_mem _ hu) s hs

end Nondeg

section D6Target

theorem smith24E4Form_holds :
    Smith24E4FormStatement := by
  intro G _ _ M Q Z B _ hc _ K _ _ γ M₀ hD ψ φ d
  obtain ⟨n, k, hn, -⟩ := hc.ctx.hyp.cp
  haveI : CharP K 2 := charP_two_of_natCard_pow_two (hD.card.trans hn)
  have hgeom := d6MinuscGeom (K := K)
  exact KSchur.form_of_uniform hc.ctx hD (D6X.betaWL K) betaWL_nondeg hgeom.p₀_ne
    (D6X.d6_fe2Geom (K := K)).β_inv hgeom.U₀_le hgeom.U₀_fix fix_rootRad0 EAut0_irreducible d

end D6Target

end CFSG.RankThree.GF2n.Smith81.D6Spin
