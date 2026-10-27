module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFour
public import CFSG.LocalAnalysis.StandardType.GGSixD4SmallVacuous

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal

theorem ggRCSLayer_POmegaPlus {G : Type} [Group G] [Finite G] {p n f : ℕ}
    (ψ : (ggU .POmegaPlus n f).K →* G) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K) {r : G}
    (hr : GGRootInvolution (ggU .POmegaPlus n f).D .POmegaPlus ψ r)
    (h23 : n = 4 → f = 1 → p ≠ 3) :
    GGRCSLayer p ψ.range (Subgroup.normalizer (ψ.range : Set G)) r := by
  obtain ⟨-, hf1, hn4⟩ := hadm
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hker hr
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn).le
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  have hx' : x ∈ ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t).range := by
    rw [← hX]
    exact hx
  obtain ⟨c₀, rfl⟩ := hx'
  have hc : Multiplicative.toAdd c₀ ≠ 0 := by
    intro h0
    have hc₀ : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0, ofAdd_zero]
    rw [hc₀, map_one, mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hσx : spinAction (quadPlus n (GaloisField 2 f))
      ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t c₀) =
      eichler (quadPlus n (GaloisField 2 f)) ((plusFrame n (GaloisField 2 f) hn).vec j t)
        (Multiplicative.toAdd c₀ • (plusFrame n (GaloisField 2 f) hn).vec i s) := by
    rw [← RootCentOmega.spinAction_longRoot_eq_eichler, ofAdd_toAdd]
  have hOE : CFSG.RankThree.Classical2.orthDerived (quadPlus n (GaloisField 2 f)) ≤
      elementaryGroup (quadPlus n (GaloisField 2 f)) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn]
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  ·
    obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := RCSTOm.exists_two_ne le_rfl i j
    have h23' : Nat.card (GaloisField 2 f) = 2 → p ≠ 3 := fun hK => by
      refine h23 rfl ?_
      rw [GaloisField.card 2 f (by omega)] at hK
      have h2 : (2 : ℕ) ^ f = 2 ^ 1 := by rw [hK, pow_one]
      exact Nat.pow_right_injective le_rfl h2
    exact RCSTOm.ggRCSLayer_frame_four hp hp2 (nondegenerate_polarBilin_quadPlus 4 _)
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE
      (plusFrame 4 (GaloisField 2 f) hn) (fun x hx => RootCentOmega.eq_zero_of_polar_plusVec hx)
      hij hik hil hjk hjl hkl s t hc h23' RootCentOmega.spinAction_quadPlus_injective
      (range_spinAction_quadPlus hn) hσx (RootCentOmega.centralizer_longRoot_plus_le hn4 hij s t hc)
      ψ hinj Subgroup.le_normalizer le_rfl u
  · obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne hn5 i j
    exact RCSTOm.ggRCSLayer_hypFrame_five (plusFrame n (GaloisField 2 f) hn) hp hp2
      (nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE hij hik hil him hjk hjl hjm
      hkl hkm hlm s t hc RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus hn)
      hσx (RootCentOmega.centralizer_longRoot_plus_le hn4 hij s t hc) ψ hinj
      Subgroup.le_normalizer le_rfl u

theorem ggRootCentSummandStructTag_POmegaPlus : GGRootCentSummandStructTag .POmegaPlus := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 s2 E r hch
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, -, ⟨hadm, -⟩, ⟨hrange, hker⟩, -⟩ := hctx.2
  have hlayer := ggRCSLayer_POmegaPlus ψ hp hp2 hadm hker hch.rootInvolution
    fun hn hf _ => by
      subst hn hf
      exact (ggSix_false_of_plusFour hctx s1
        (by rw [show 2 ^ 1 - 1 = 1 by norm_num]; exact hp.not_dvd_one)).elim
  rw [hrange] at hlayer
  exact ggRCSStructConcl_of_layer hp hp2 hlayer

end CFSG.StandardType
