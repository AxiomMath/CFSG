module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3PStarA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenTenP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s168e3_seven_card_le {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hMs : D.M ≤ stabTil V₀ V)
    (hcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 7 ^ 3 * 3 * Nat.factorial 3) :
    Nat.card ↥D.T ≤ 2 * Nat.card ↥(D.T ⊓ F11.CTilde D.M V₀ V) := by
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hTst : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMs
  have hcf := s16h_z3_card_eq_barSub_mul hV D.sylowM.le hMn hTst
  rw [hcf]
  refine Nat.mul_le_mul_right _ ?_
  set b : ℕ := Nat.card ↥(barSub V₀ V hV D.T) with hb
  have hbM : b ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    rw [hb]
    exact Subgroup.card_dvd_of_le (barSub_mono V₀ V hV D.sylowM.le)
  have hbdvd : b ∣ 7 ^ 3 * 3 * Nat.factorial 3 := hbM.trans hcard
  have hbT : b ∣ Nat.card ↥D.T := by
    rw [hb]
    have h := Subgroup.card_map_dvd (H := D.T.subgroupOf (stabTil V₀ V)) (actTil V₀ V hV)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTst).toEquiv] at h
    exact h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 D.sylowM.isPGroup
  have hb2 : b ∣ 2 ^ n := by rw [← hn]; exact hbT
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hb2
  have hk_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
    have h4dvd : 4 ∣ 7 ^ 3 * 3 * Nat.factorial 3 := by
      rw [hk] at hbdvd
      rw [pow_add] at hbdvd
      exact dvd_trans (show (4 : ℕ) ∣ 2 ^ 2 * 2 ^ j from ⟨2 ^ j, by norm_num⟩) hbdvd
    norm_num at h4dvd
  have hb_le : b ≤ 2 := by
    interval_cases k <;> simp only [pow_zero, pow_one] at hk <;> omega
  simpa [hb] using hb_le

theorem s168e3_seven_cond_ii {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hMs : D.M ≤ stabTil V₀ V)
    (hcard : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 7 ^ 3 * 3 * Nat.factorial 3) {Y : Subgroup G}
    (hYM : Y ≤ D.M) (hYp : IsPGroup 7 Y) (hperm : Permutes Y D.T)
    (hYK : Y ⊓ F11.CTilde D.M V₀ V = ⊥) :
    ∃ a ∈ F11.Omega1p 2 D.T, F11.Omega1p 2 D.T =
      Subgroup.zpowers a ⊔ (F11.Omega1p 2 D.T ⊓ pCoreOf 2 (Y ⊔ D.T)) :=
  s168e3_seven_omega_eq (M := D.M) (K := F11.CTilde D.M V₀ V) (by norm_num) (by norm_num)
    uc22p22q_ctilde_le
    (fun _ hm _ hk => uc22p22q_ctilde_conj_mem (hMs.trans (stabTil_le_normalizer V₀ V))
      (hMs.trans (stabTil_le_normalizer₀ V₀ V)) hm hk)
    D.sylowM.le hYM D.sylowM.isPGroup hYp hperm hYK (s168e3_seven_card_le hMs hcard)

theorem s168e3_seven_barSub_conj {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Hyp125 D V₀ V) {X P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXM : D.M ≤ normalizer (X : Set G))
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) :
    ∀ g ∈ Mbar D.M V₀ V hV,
      (barSub V₀ V hV (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ X))).map (MulAut.conj g).toMonoidHom =
        barSub V₀ V hV (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ X)) := by
  intro g hg
  have hMt : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  set Y : Subgroup G := F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ X) with hY
  have hN : D.M ⊓ normalizer (P : Set G) ≤ normalizer (Y : Set G) := by
    rw [hY]
    exact (s11_TenP_inf_normalizer_le (M := D.M) (P := P) (X := X) (p := p) hXM).trans
      inf_le_right
  obtain ⟨m, hmM, hm_eq⟩ := (mem_barSub V₀ V hV D.M g).1 hg
  obtain ⟨u, huO, n, hnN, hgn⟩ :=
    s11_TenP_exists_mul (M := D.M) (P := P) hp hp2 hP (m : G) hmM
  have huM : u ∈ D.M := uc22p21c_pCoreOf_le D.M huO
  have hu_stab : u ∈ stabTil V₀ V := hMt huM
  have hn_stab : n ∈ stabTil V₀ V := hMt hnN.1
  have hker : actTil V₀ V hV ⟨u, hu_stab⟩ = 1 := by
    have hmem : actTil V₀ V hV ⟨u, hu_stab⟩ ∈ barSub V₀ V hV (pCoreOf 2 D.M) :=
      actTil_mem_barSub V₀ V hV huO hu_stab
    rw [barSub_pCoreOf_eq_bot_of_hyp125 h] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hprod : (m : stabTil V₀ V) = ⟨u, hu_stab⟩ * ⟨n, hn_stab⟩ :=
    Subtype.ext (by
      change (m : G) = u * n
      exact hgn)
  have hg_eq : g = actTil V₀ V hV ⟨n, hn_stab⟩ := by
    rw [← hm_eq, hprod, map_mul, hker, one_mul]
  rw [hg_eq]
  apply le_antisymm
  · intro x hx
    obtain ⟨ψ, hψ, hxeq⟩ := Subgroup.mem_map.1 hx
    rw [← hxeq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact s16h_z3_conj_mem_barSub hV hN hnN hψ
  · intro ψ hψ
    rw [Subgroup.mem_map]
    refine ⟨actTil V₀ V hV (⟨n, hn_stab⟩⁻¹) * ψ *
      (actTil V₀ V hV (⟨n, hn_stab⟩⁻¹))⁻¹,
      s16h_z3_conj_mem_barSub hV hN
        ((D.M ⊓ normalizer (P : Set G)).inv_mem hnN) hψ, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_inv]
    rw [← hg_eq]
    group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
