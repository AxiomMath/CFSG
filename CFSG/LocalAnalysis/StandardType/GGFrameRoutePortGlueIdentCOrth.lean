module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9OrthCover
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9OrthAut
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentC
import CFSG.LieType.ChevTwo.OrthogonalAutLarge
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.LieType.ChevTwo

theorem classical_D6_or_signedB6_of_orth_label
    {G : Type} [Group G] [Finite G]
    {S : ℕ → LargeEvenLabel → Prop} {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (_hNT : GGNoTransvection 3 Bs)
    (hS : ∀ lab, S 3 lab → (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K) (h2loc : CFSG.Open.twoLocalPrimeRank 3 G ≤ n)
    (W : Subgroup (MulAut ↥(ggGamma K hN).range))
    (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut ↥K)) (ggGamma K hN).range)
    (hWord : Nat.card W = if n = 7 then 23040 else 2903040) :
    n = 7 ∧ (GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) 3 Bs K ∨
      GGSignedB6At Bs z) := by
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
    have hz' : z ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
      rw [hker]
      exact Subgroup.mem_zpowers z
    exact hz'.2
  rcases native_orth_equiv_of_innerDiagOnLabel hBs hcard hn hz hz1 hN hker hBstar hS hK with
    ⟨a, ha, ⟨e⟩, hlab⟩ | ⟨a, ha, ⟨e⟩⟩
  ·
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hQ := goodQ_plus (n := b) (by omega)
    have hind := omegaTwoAutInduced_plus_of_four_le (n := b) (by omega)
    have hq := CFSG.LieType.Universal.Spin.coe_quadPlus (b + 1) (ZMod 2)
    have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (b + 1) (ZMod 2)
    have hι : Fintype.card (Fin (b + 1) ⊕ Fin (b + 1)) = 2 * (b + 1) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      ring
    obtain ⟨C, hpos, hsign⟩ :=
      exists_omCoord_of_native_orth hQ hind hq hnd hι (by omega) e hBs hN hker hBstar
    obtain ⟨s, T, hsC, hT, hrange, hupper, hlower⟩ :=
      native_orth_torus_action_data hQ hind hq hnd hι (by omega) e hBs hN hker hBstar hNK C
    have hrank := rank_eq_of_native_orth hQ hind e hBs hcard hz hz1 hN hker hBstar T hT hrange
    have heven : Even s := by
      rw [hsC]
      exact hsign.mp (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (ZMod 2) (b + 1))
    have hn7 : n = 7 := by
      rcases hn with h | h
      · exact h
      · exfalso
        have hs7 : s = 7 := by omega
        rw [hs7] at heven
        exact absurd heven (by decide)
    subst hn7
    refine ⟨rfl, ?_⟩
    have hs6 : s = 6 := by omega
    rcases hpos with ⟨-, hsa⟩ | ⟨hsa, hW0⟩
    ·
      left
      have hb : b + 1 = 6 := by omega
      rw [hb] at hlab
      exact hlab
    ·
      right
      have hlow := hlower hW0
      subst hs6
      have hsplit : Bs = Subgroup.zpowers z ⊔ T.range := by
        rw [hrange]
        exact bstar_eq_zpowers_sup_inf_of_native_orth hQ hind e hBs hN hker hBstar
      have hZK : Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G) := by
        rw [← hker]
        exact inf_le_right
      have hcomm : ∀ x ∈ Subgroup.zpowers z, ∀ y ∈ T.range, x * y = y * x := by
        intro x hx y hy
        rw [hrange] at hy
        exact ((Subgroup.mem_centralizer_iff.mp (hZK hx)) y hy.2).symm
      have hcenter : Subgroup.center K = ⊥ := by
        apply Subgroup.eq_bot_of_card_eq
        rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
          center_statedOmega_eq_bot_of_goodQ hQ, Subgroup.card_bot]
      have hdisj : Subgroup.zpowers z ⊓ T.range = ⊥ := by
        refine le_antisymm (fun x hx => ?_) bot_le
        have hxK : x ∈ K := (hrange ▸ hx.2).2
        have hxZ : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
          rw [Subgroup.mem_center_iff]
          exact fun k => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hZK hx.1)) k k.property)
        rw [hcenter, Subgroup.mem_bot] at hxZ
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)
      exact signedB6At_of_split_torus T hT hsplit hcomm hdisj hupper hlow
  ·
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hQ := goodQ_minus (n := b) (by omega)
    have hind := omegaTwoAutInduced_minus_of_three_le (n := b) (by omega)
    have hq := CFSG.LieType.Universal.Spin.coe_quadMinus (n := b + 1) (K := ZMod 2) 1 1
    have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (b + 1)
      (ZMod 2) hirr_one_one
    have hι : Fintype.card (Fin (b + 1 - 1) ⊕ Fin (b + 1 - 1) ⊕ Fin 2) = 2 * (b + 1) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    obtain ⟨C, -, hsign⟩ :=
      exists_omCoord_of_native_orth hQ hind hq hnd hι (by omega) e hBs hN hker hBstar
    obtain ⟨s, T, hsC, hT, hrange, -, -⟩ :=
      native_orth_torus_action_data hQ hind hq hnd hι (by omega) e hBs hN hker hBstar hNK C
    have hrank := rank_eq_of_native_orth hQ hind e hBs hcard hz hz1 hN hker hBstar T hT hrange
    have hodd : ¬ Even s := by
      rw [hsC]
      intro h
      exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := b + 1) (by omega)
        hirr_one_one (hsign.mpr h)
    exfalso
    rcases hn with rfl | rfl
    · have hs6 : s = 6 := by omega
      rw [hs6] at hodd
      exact hodd (by decide)
    · have hs7 : C.s = 7 := by omega
      have hdvd := card_automizer_native_orth_dvd hQ hind hq e hBs hN hker hBstar C
      rw [hs7] at hdvd
      exact P9_Wa_nonunitary_n8_false hW (by simpa using hWord) hdvd

end CFSG.StandardType.FrameRoute

end
