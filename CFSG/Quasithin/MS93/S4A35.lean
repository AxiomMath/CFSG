module

public import CFSG.Quasithin.MS93.S4APair
public import CFSG.Quasithin.MS93.S4AEA

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s35_arith {f f' w : ℕ} (hw1 : 1 ≤ w) (hwf : w ≤ f) (hwf' : w ≤ f')
    (hf : f ≤ 2) (hf' : f' ≤ 2) (h1 : 3 - f' ≤ (3 - f) * w) (h2 : 3 - f ≤ (3 - f') * w) :
    f = f' := by
  rcases Nat.lt_or_ge w 2 with hw | hw
  · have : w = 1 := by omega
    subst this
    omega
  · omega

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem s35_core (h : PUHyp M T L) (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    {ψ : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ α) (Uloc h.le L α) ⊥ ψ false 1)
    {ψ' : ↥(stab (puAmalgam h.le) α') →* ↥(StatedSL 3 F)}
    (hψ' : IsSumOfNaturalModulesVia (stab _ α') (Uloc h.le L α') ⊥ ψ' false 1) :
    Module.finrank F (fixN (natImage ψ' (ZM (puAmalgam h.le) α))) =
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Nat.card ↥(natImage ψ' (ZM (puAmalgam h.le) α)) = (Qv _ α').relIndex (ZM _ α) ∧
      (Qv _ α').relIndex (ZM _ α) =
        Nat.card F ^ (3 - Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α')))) ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') =
        Nat.card F ^ Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤
        Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ∧
      natImage ψ (ZM (puAmalgam h.le) α') ≠ ⊥ := by
  have hb := h.critDist_pos
  have h20 := h.hyp20
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc' := ms22_iii _ h20 hb hC hc
  have hα := hc.1
  have hα' := hc'.1
  set E := natImage ψ' (ZM (puAmalgam h.le) α) with hE
  set E' := natImage ψ (ZM (puAmalgam h.le) α') with hE'
  set q := Nat.card F with hqdef
  have hcardE : Nat.card ↥E = (Qv _ α').relIndex (ZM _ α) := card_natImage_zm h hfull hC hc hψ'
  have hcardE' : Nat.card ↥E' = (Qv _ α).relIndex (ZM _ α') :=
    card_natImage_zm h hfull hC hc' hψ
  have hfix' : (Qv _ α').relIndex (ZM _ α) * Nat.card ↥(fixN E') = q ^ 3 :=
    relIndex_mul_card_fixN h hfull hC hc hψ
  have hfix : (Qv _ α).relIndex (ZM _ α') * Nat.card ↥(fixN E) = q ^ 3 :=
    relIndex_mul_card_fixN h hfull hC hc' hψ'
  have hcommE' : Nat.card ↥(commN E') = Nat.card ↥(critR (puAmalgam h.le) α α') :=
    card_commN_eq_card_critR h hfull hc hψ
  have hcommE : Nat.card ↥(commN E) = Nat.card ↥(critR (puAmalgam h.le) α α') := by
    rw [card_commN_eq_card_critR h hfull hc' hψ', critR, critR, Subgroup.commutator_comm]
  have hE2 := natImage_zm_sq h hα (ψ := ψ')
  have hEc := natImage_zm_comm h hα (ψ := ψ')
  have hE'2 := natImage_zm_sq h hα' (ψ := ψ)
  have hE'c := natImage_zm_comm h hα' (ψ := ψ)
  set f := Module.finrank F (fixN E) with hfdef
  set f' := Module.finrank F (fixN E') with hf'def
  set w := Module.finrank F (commN E) with hwdef
  set w' := Module.finrank F (commN E') with hw'def
  have hfixc : Nat.card ↥(fixN E) = q ^ f := card_fixN E
  have hfixc' : Nat.card ↥(fixN E') = q ^ f' := card_fixN E'
  have hcommc : Nat.card ↥(commN E) = q ^ w := Module.natCard_eq_pow_finrank
  have hcommc' : Nat.card ↥(commN E') = q ^ w' := Module.natCard_eq_pow_finrank
  have hww' : w = w' := by
    have : q ^ w = q ^ w' := by rw [← hcommc, ← hcommc', hcommE, hcommE']
    exact Nat.pow_right_injective hq this
  have hwf : w ≤ f := finrank_commN_le_finrank_fixN_of_elemAb hE2 hEc
  have hwf' : w' ≤ f' := finrank_commN_le_finrank_fixN_of_elemAb hE'2 hE'c
  have hf3 : f ≤ 3 := (Submodule.finrank_le (fixN E)).trans (by simp)
  have hf'3 : f' ≤ 3 := (Submodule.finrank_le (fixN E')).trans (by simp)
  have hpow : ∀ {a e : ℕ}, e ≤ 3 → a * q ^ e = q ^ 3 → a = q ^ (3 - e) := by
    intro a e he hae
    have hpos : 0 < q ^ e := pow_pos (by omega) e
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hae, ← pow_add, Nat.sub_add_cancel he]
  have haE : (Qv _ α').relIndex (ZM _ α) = q ^ (3 - f') := hpow hf'3 (hfixc' ▸ hfix')
  have haE' : (Qv _ α).relIndex (ZM _ α') = q ^ (3 - f) := hpow hf3 (hfixc ▸ hfix)
  have hne : (Qv (puAmalgam h.le) α').relIndex (ZM _ α) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact hc.2.2
  have hne' : (Qv (puAmalgam h.le) α).relIndex (ZM _ α') ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact hc'.2.2
  have hf2 : f ≤ 2 := by
    by_contra hcon
    apply hne'
    rw [haE', show 3 - f = 0 by omega, pow_zero]
  have hf'2 : f' ≤ 2 := by
    by_contra hcon
    apply hne
    rw [haE, show 3 - f' = 0 by omega, pow_zero]
  have hE'ne : E' ≠ ⊥ := by
    intro hbot
    apply hne'
    rw [← hcardE', hbot, Subgroup.card_bot]
  have hw'1 : 1 ≤ w' := by
    rw [Nat.one_le_iff_ne_zero, hw'def, Ne, Submodule.finrank_eq_zero]
    exact commN_ne_bot hE'ne
  have hb1 : 3 - f' ≤ (3 - f) * w := by
    have := card_le_of_elemAb hE2 hEc
    rw [hcardE, haE] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hb2 : 3 - f ≤ (3 - f') * w := by
    have := card_le_of_elemAb hE'2 hE'c
    rw [hcardE', haE', ← hw'def, ← hww'] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hff' : f = f' :=
    s35_arith (hww' ▸ hw'1) hwf (hww' ▸ hwf') hf2 hf'2 hb1 hb2
  exact ⟨hff', hcardE, haE, by rw [← hcommE', hcommc'], hwf', hE'ne⟩

end CFSG.Quasithin.MS93
