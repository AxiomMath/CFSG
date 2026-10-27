module

public import CFSG.Quasithin.MS93.Burnside.SL3GZ461

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSL3G_uloc_inf_qv_eq_commutator_centerOf (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ¬ ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), Ltil h.le L α⁆ ≤ ZM _ α) :
    Uloc h.le L α' ⊓ Qv (puAmalgam h.le) α =
      ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), ZM (puAmalgam h.le) α'⁆ := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hC := h.centHyp
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα'ε := adj_geo_one_of_isCritical _ hb0 hc'
  obtain ⟨n, F, _, _, φ, hcard, hφs, hφ⟩ := exists_natural_flat h hU
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ψ, -, hψ⟩ := exists_natural_flat_at h hφs hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_flat_at h hφs hφ hc'.1
  obtain ⟨hf, -, hrel, hR, hwf, -⟩ := s35_core_flat h hU hC hcard hc hψ hψ'
  set N := centerOf (burnsideSL3G_vb (puAmalgam h.le) α) with hNdef
  set f := Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) with hfdef
  set w := Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) with hwdef
  have hw1 : w ≠ 0 := by
    intro hw0
    have hRne : critR (puAmalgam h.le) α α' ≠ ⊥ := ms22_ii _ h20 hb0 hC hc
    apply hRne
    rw [← Subgroup.card_eq_one, hR, hw0, pow_zero]
  have hf2 : f ≤ 2 := by
    by_contra hcon
    apply hc.2.2
    rw [← Subgroup.relIndex_eq_one, hrel, show 3 - f = 0 by omega, pow_zero]
  have hNY : N ≤ Qv _ (geo _ α' α 1) ⊓ flat h α' := burnsideSL3G_centerOf_vb_le_flat h hU hb hc
  have hNε : N ≤ Qv _ (geo _ α' α 1) := hNY.trans inf_le_left
  have hcardN : Nat.card ↥⁅Uloc h.le L α', N⁆ =
      Nat.card F ^ Module.finrank F (commN (natImage ψ' N)) := by
    rw [card_commutator_eq hψ' (hNY.trans inf_le_right), Module.natCard_eq_pow_finrank (K := F)]
  obtain ⟨hReq, hRle⟩ := critR_eq_commutator_uloc_right h hC hc
  have hRN : critR (puAmalgam h.le) α α' ≤ ⁅Uloc h.le L α', N⁆ := by
    rw [hReq]
    exact Subgroup.commutator_mono le_rfl (burnsideSL3G_zm_le_centerOf_vi h hc.1 (by omega))
  have hUN : ⁅Uloc h.le L α', N⁆ = ⁅N, ZM (puAmalgam h.le) α'⁆ := by
    rw [← commutator_zm_eq_commutator_uloc_of_le_qv h hc'.1 hα'ε hNε, Subgroup.commutator_comm]
  have hNW : ⁅Uloc h.le L α', N⁆ ≤
      Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
    rw [hUN]
    exact burnsideSL3G_commutator_centerOf_zm_le h hb hc
  have hcardW : Nat.card ↥(Uloc h.le L α' ⊓
      Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _)) = Nat.card F ^ f := by
    rw [card_inf_centralizer_eq hψ' (zm_le_flat h hU hc), card_fixN, hf]
  have : Finite ↥(Uloc h.le L α') := Finite.of_equiv _ (natCoord hψ').toEquiv.symm
  have hUfin : ∀ K : Subgroup (puAmalgam h.le).Universal, K ≤ Uloc h.le L α' → Finite ↥K :=
    fun K hK => Finite.of_injective _ (Subgroup.inclusion_injective hK)
  have := hUfin _ (hNW.trans inf_le_left)
  have := hUfin _ (inf_le_left : Uloc h.le L α' ⊓
    Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) ≤ Uloc h.le L α')
  set d := Module.finrank F (commN (natImage ψ' N)) with hddef
  have hwd : w ≤ d := by
    have := Subgroup.card_le_of_le hRN
    rw [hR, hcardN] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hdf : d ≤ f := by
    have := Subgroup.card_le_of_le hNW
    rw [hcardN, hcardW] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hdw : d ≠ w := by
    intro hdw
    apply hN
    refine burnsideSL3G_centerOf_ltil_le_of_commutator_le h hb hc ?_
    have heqR : ⁅Uloc h.le L α', N⁆ = critR (puAmalgam h.le) α α' :=
      (Subgroup.eq_of_le_of_card_ge hRN (by rw [hcardN, hR, hdw])).symm
    rw [← hUN, heqR]
    exact hRle.trans inf_le_right
  have hdf' : d = f := by omega
  have hUQ : Uloc h.le L α' ⊓ Qv (puAmalgam h.le) α =
      Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
    have hUZ : Uloc h.le L α' ≤ ZM (puAmalgam h.le) α' := uloc_le_zm' h hc'.1
    have heq := zm_inf_centralizer_eq_inf_qv _ h20 hb0 hC hc'
    calc Uloc h.le L α' ⊓ Qv (puAmalgam h.le) α
        = Uloc h.le L α' ⊓ (ZM (puAmalgam h.le) α' ⊓ Qv (puAmalgam h.le) α) := by
          rw [← inf_assoc, inf_eq_left.mpr hUZ]
      _ = Uloc h.le L α' ⊓ (ZM (puAmalgam h.le) α' ⊓
            Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _)) := by rw [heq]
      _ = Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
          rw [← inf_assoc, inf_eq_left.mpr hUZ]
  rw [hUQ, ← hUN]
  exact (Subgroup.eq_of_le_of_card_ge hNW (by rw [hcardN, hcardW, hdf'])).symm

theorem burnsideSL3G_uloc_inf_qv_le_centerOf (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ¬ ⁅centerOf (burnsideSL3G_vb (puAmalgam h.le) α), Ltil h.le L α⁆ ≤ ZM _ α) :
    Uloc h.le L α' ⊓ Qv (puAmalgam h.le) α ≤ centerOf (burnsideSL3G_vb (puAmalgam h.le) α) := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  rw [burnsideSL3G_uloc_inf_qv_eq_commutator_centerOf h hU hb hc hN]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_isCritical _ h.hyp20 hb0 hc).trans
      (burnsideSL3G_stab_le_normalizer_centerOf_vi h α _))

end CFSG.Quasithin.MS93.S4L
