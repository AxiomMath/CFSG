module

public import CFSG.Monster.Existence.StdOdd.Seven
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThree
public import CFSG.Monster.Existence.StdOdd.Cert.ThreeLocalLemmas

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open Subgroup

open CFSG.LieType.Chevalley.C2E6Std (card_stdGroup)

open CFSG.Monster.Existence.StdOdd.P5 (E5 GL5 rk rkFibre Pbar IsExt card_of_equiv
  fixed_card_ge_of_pow_eleven)

private theorem finite_rgrp :
    Finite Rgrp :=
  Nat.finite_of_card_ne_zero (by rw [card_stdGroup]; norm_num)

private theorem card_Rgrp :
    Nat.card Rgrp = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by
  rw [card_stdGroup]
  norm_num

section Std

variable {P : Sylow 3 Rgrp} {E : Subgroup P} {ι : E ≃* Multiplicative E5} {ρ : P →* GL5}

theorem exists_conj_normalizer_sylow
    (hext : IsExt Pbar E ι ρ) (T : Subgroup Rgrp)
    (hT : Nat.card T = 3 ^ 9) {g : Rgrp} (hg : g ∈ normalizer (T : Set Rgrp)) :
    ∃ g' : Rgrp, g' ∈ normalizer ((P : Subgroup Rgrp) : Set Rgrp) ∧ orderOf g' = orderOf g := by
  have := finite_rgrp
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow P (IsPGroup.of_card hT)
  have hTP : T.map (MulAut.conj c).toMonoidHom = (P : Subgroup Rgrp) :=
    Subgroup.eq_of_le_of_card_ge hc (by
      rw [card_map_conjHom, hT]
      exact (hext.pbar_card : Nat.card P = 3 ^ 9).le)
  refine ⟨c * g * c⁻¹, ?_, orderOf_mul_mul_inv c g⟩
  have := mem_normalizer_map_conj c hg
  rwa [hTP] at this

theorem rank3_std
    (hext : IsExt Pbar E ι ρ) (A : Subgroup Rgrp) (h3 : ∀ a ∈ A, a ^ 3 = 1)
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A ≤ 3 ^ 5 := by
  have := finite_rgrp
  obtain ⟨c, B, hB, hB3, hBc, -⟩ := exists_conj_elemAbelian_sylow P A h3 hc
  rw [← hB]
  exact (hext.pbar_elemAbelian B hB3 hBc).1

theorem syl5_sylow
    (hext : IsExt Pbar E ι ρ) (hC : CentralizerFacts Rgrp) {g : Rgrp}
    (hg : g ∈ normalizer ((P : Subgroup Rgrp) : Set Rgrp)) (h5 : orderOf g = 5) : False := by
  have := finite_rgrp
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrank : Group.rank (P : Subgroup Rgrp) ≤ 3 := hext.pbar_groupRank_top
  have hle := le_centralizer_of_frattini (p := 3) (q := 5) (r := 3) (by norm_num)
    P.isPGroup' hrank (by decide) h5 hg
  have h1 := Subgroup.card_dvd_of_le hle
  rw [(hext.pbar_card : Nat.card P = 3 ^ 9)] at h1
  have := h1.trans (hC.c5 g h5)
  revert this
  norm_num

theorem syl5_std
    (hext : IsExt Pbar E ι ρ) (hC : CentralizerFacts Rgrp) (T : Subgroup Rgrp)
    (hT : Nat.card T = 3 ^ 9) {g : Rgrp} (hg : g ∈ normalizer (T : Set Rgrp)) :
    orderOf g ≠ 5 := fun h5 => by
  obtain ⟨g', hg', ho⟩ := exists_conj_normalizer_sylow hext T hT hg
  exact syl5_sylow hext hC hg' (ho.trans h5)

theorem syl13_sylow
    (hext : IsExt Pbar E ι ρ) (hC : CentralizerFacts Rgrp) {g : Rgrp}
    (hg : g ∈ normalizer ((P : Subgroup Rgrp) : Set Rgrp)) (h13 : orderOf g = 13) : False := by
  have := finite_rgrp
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let a : ↥(normalizer ((P : Subgroup Rgrp) : Set Rgrp)) := ⟨g, hg⟩
  let α : MulAut (P : Subgroup Rgrp) := (P : Subgroup Rgrp).normalizerMonoidHom a
  have hα : E.map α.toMonoidHom = E := hext.pbar_map_eq α
  let EG : Subgroup Rgrp := E.map (P : Subgroup Rgrp).subtype
  have hEG : g ∈ normalizer (EG : Set Rgrp) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨e, he, rfl⟩ := hn
    have h1 : α e ∈ E := by
      rw [← hα]
      exact Subgroup.mem_map_of_mem _ he
    exact ⟨α e, h1, Subgroup.normalizerMonoidHom_apply_apply_coe _ a e⟩
  have hmod := card_modEq_zpowers h13 hEG
  have hEc : Nat.card EG = 3 ^ 5 := by
    rw [Subgroup.card_map_of_injective (P : Subgroup Rgrp).subtype_injective]
    exact card_of_equiv ι
  have h1 : Nat.card ↥(EG ⊓ centralizer ({g} : Set Rgrp)) ∣ 13 := by
    rw [← hC.c13 g h13]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h2 : Nat.card ↥(EG ⊓ centralizer ({g} : Set Rgrp)) ∣ 3 ^ 5 := by
    rw [← hEc]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3 : Nat.card ↥(EG ⊓ centralizer ({g} : Set Rgrp)) = 1 :=
    Nat.dvd_one.1 (by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 13 (3 ^ 5) = 1 by norm_num] at this)
  rw [hEc, h3] at hmod
  revert hmod
  decide

theorem syl13_std
    (hext : IsExt Pbar E ι ρ) (hC : CentralizerFacts Rgrp) (T : Subgroup Rgrp)
    (hT : Nat.card T = 3 ^ 9) {g : Rgrp} (hg : g ∈ normalizer (T : Set Rgrp)) :
    orderOf g ≠ 13 := fun h13 => by
  obtain ⟨g', hg', ho⟩ := exists_conj_normalizer_sylow hext T hT hg
  exact syl13_sylow hext hC hg' (ho.trans h13)

theorem sub7_std
    (hext : IsExt Pbar E ι ρ) (hC : CentralizerFacts Rgrp) (F : Subgroup Rgrp)
    (hF : Nat.card F = 3 ^ 8) {g : Rgrp} (hg : g ∈ normalizer (F : Set Rgrp)) :
    orderOf g ≠ 7 := fun h7 => by
  have := finite_rgrp
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_conj_map_le_sylow P (IsPGroup.of_card hF)
  let F' : Subgroup Rgrp := F.map (MulAut.conj c).toMonoidHom
  have hF' : Nat.card F' = 3 ^ 8 := (card_map_conjHom c F).trans hF
  let B : Subgroup P := F'.subgroupOf P
  have hB : Nat.card B = 3 ^ 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc).toEquiv).trans hF'
  have hrank : Group.rank F' ≤ 4 := by
    rw [← Group.rank_congr (Subgroup.subgroupOfEquivOfLe hc)]
    exact hext.pbar_groupRank_eight B hB
  have hle := le_centralizer_of_frattini (p := 3) (q := 7) (r := 4) (by norm_num)
    (IsPGroup.of_card hF') hrank (by decide) ((orderOf_mul_mul_inv c g).trans h7)
    (mem_normalizer_map_conj c hg)
  have h1 := Subgroup.card_dvd_of_le hle
  rw [hF'] at h1
  have := h1.trans (hC.c7 _ ((orderOf_mul_mul_inv c g).trans h7))
  revert this
  norm_num

theorem seven_le_card_fixed
    (σ : Equiv.Perm E5) (h0 : σ 0 = 0) (h11 : σ ^ 11 = 1)
    (hrk : ∀ x, rk (σ x) = rk x) : 7 ≤ Nat.card {x : E5 // σ x = x} := by
  classical
  obtain ⟨h30, -, -⟩ := fixed_card_ge_of_pow_eleven σ h0 h11 hrk
  have h0A : (0 : E5) ∉ (rkFibre 30).filter fun x => σ x = x := fun h =>
    (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).2.1 rfl
  have hsub : insert 0 ((rkFibre 30).filter fun x => σ x = x) ⊆
      Finset.univ.filter fun x => σ x = x := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem h0A] at this
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem elem11_std
    (hext : IsExt Pbar E ι ρ)
    (hfix : ∀ x : E5, fixDim (((ι.symm (Multiplicative.ofAdd x) : E) : P) : Rgrp) = 6 + rk x)
    (hC : CentralizerFacts Rgrp) (X : Subgroup Rgrp) (h3 : ∀ a ∈ X, a ^ 3 = 1)
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hX : Nat.card X = 3 ^ 5) {g : Rgrp}
    (hg : g ∈ normalizer (X : Set Rgrp)) : orderOf g ≠ 11 := fun h11 => by
  have := finite_rgrp
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨c, B, hBX, hB3, hBc, hBmap⟩ := exists_conj_elemAbelian_sylow P X h3 hc
  have hBE : B = E := (hext.pbar_elemAbelian B hB3 hBc).2 (by rw [hBX, hX]; norm_num)
  rw [hBE] at hBmap
  let EG : Subgroup Rgrp := E.map (P : Subgroup Rgrp).subtype
  have hXE : X.map (MulAut.conj c).toMonoidHom = EG := hBmap.symm
  let g' : Rgrp := c * g * c⁻¹
  have hg' : g' ∈ normalizer (EG : Set Rgrp) := by
    have := mem_normalizer_map_conj c hg
    rwa [hXE] at this
  have ho : orderOf g' = 11 := (orderOf_mul_mul_inv c g).trans h11
  let φ : E ≃* EG :=
    E.equivMapOfInjective (P : Subgroup Rgrp).subtype (P : Subgroup Rgrp).subtype_injective
  let ιG : EG ≃* Multiplicative E5 := φ.symm.trans ι
  obtain ⟨σ, hσ0, hσpow, hσ, hcard⟩ := exists_perm_of_mem_normalizer EG ιG hg'
  have hσ11 : σ ^ 11 = 1 := hσpow 11 (by rw [← ho]; exact pow_orderOf_eq_one g')
  have hfixG : ∀ x : E5, fixDim ((ιG.symm (Multiplicative.ofAdd x) : EG) : Rgrp) = 6 + rk x := by
    intro x
    rw [← hfix x]
    rfl
  have hrk : ∀ x, rk (σ x) = rk x := by
    intro x
    have h1 := hfixG (σ x)
    have h2 := hfixG x
    have h3 : fixDim ((ιG.symm (Multiplicative.ofAdd (σ x)) : EG) : Rgrp) =
        fixDim ((ιG.symm (Multiplicative.ofAdd x) : EG) : Rgrp) := by
      have := congrArg fixDim (hσ x)
      rw [fixDim_conj] at this
      exact this
    omega
  have h7 := seven_le_card_fixed σ hσ0 hσ11 hrk
  have hEc : Nat.card EG = 3 ^ 5 := by rw [← hXE, card_map_conjHom, hX]
  have h1 : Nat.card ↥(EG ⊓ centralizer ({g'} : Set Rgrp)) ∣ 2 * 3 * 11 :=
    (Subgroup.card_dvd_of_le inf_le_right).trans (hC.c11 g' ho)
  have h2 : Nat.card ↥(EG ⊓ centralizer ({g'} : Set Rgrp)) ∣ 3 ^ 5 := by
    rw [← hEc]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3' : Nat.card ↥(EG ⊓ centralizer ({g'} : Set Rgrp)) ∣ 3 := by
    have := Nat.dvd_gcd h1 h2
    rwa [show Nat.gcd (2 * 3 * 11) (3 ^ 5) = 3 by norm_num] at this
  have := Nat.le_of_dvd (by norm_num) h3'
  omega

end Std

theorem threeLocalFacts_std
    (hC : CentralizerFacts Rgrp) : ThreeLocalFacts Rgrp := by
  obtain ⟨P, E, ι, ρ, hext, hfix, -⟩ := exists_sylow_isExt_fixDim
  exact ⟨rank3_std hext, syl5_std hext hC, syl13_std hext hC, sub7_std hext hC,
    fun X h3 hc hX g hg => elem11_std hext hfix hC X h3 hc hX hg⟩

theorem stdOddBounds3_std
    (hC : CentralizerFacts Rgrp) :
    (∀ M : Subgroup Rgrp, Odd (Nat.card M) → Nat.card M ≤ 54463) ∧
    (∀ M : Subgroup Rgrp, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 →
      Nat.card M ≤ 9477) ∧
    (∀ M : Subgroup Rgrp, Odd (Nat.card M) → Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 →
      Nat.card M ≤ 15309) := by
  have := finite_rgrp
  exact stdOddBounds3_of_facts card_Rgrp hC (threeLocalFacts_std hC)

end CFSG.Monster.Existence.StdOdd.Cert
