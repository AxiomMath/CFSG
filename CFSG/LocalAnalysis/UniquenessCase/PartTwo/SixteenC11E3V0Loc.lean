module

import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.OTwoFixedSquare
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.WeakClosure81.SixSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_ti_local (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {q : ℕ}
    (hq : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M) {I : Subgroup G} (hIV : I ≤ V)
    (hcent : V₀ ≠ ⊥ → ∀ w ∈ I, w ∉ V₀ → q ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G))) :
    ∀ g : G, g ∉ D.M → I ⊓ conjSubgroup V₀ g = ⊥ := by
  intro g hg
  by_cases hbot : V₀ = ⊥
  · rw [hbot, E3.conjSubgroup_bot]
    exact inf_bot_eq _
  · rcases h.1 with ⟨-, h0⟩ | ⟨hV₀0, -, -⟩
    · exact absurd h0 hbot
    · obtain ⟨hV₀cal, -, -, hTI, -, -, -⟩ := hV₀0
      have hnorm : Subgroup.normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV₀cal
      have h62 : Hyp62 D.M V₀ V := Hyp125.hyp62 h
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_bot]
      by_contra hw1
      obtain ⟨hwI, hwV₀⟩ := Subgroup.mem_inf.1 hw
      have hwV : w ∈ V := hIV hwI
      have hw0 : w ∉ V₀ := by
        intro hw0mem
        have hmeminf : w ∈ V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V₀ :=
          Subgroup.mem_inf.2 ⟨hw0mem, hwV₀⟩
        have hne : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V₀ ≠ ⊥ := fun hb =>
          hw1 (Subgroup.mem_bot.1 (hb ▸ hmeminf))
        have heq : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V₀ = V₀ :=
          (hTI g⁻¹).resolve_left hne
        have hle : V₀ ≤ conjSubgroup V₀ g := by
          calc V₀ = V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V₀ := heq.symm
            _ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ V₀ := inf_le_right
        have hEq : conjSubgroup V₀ g = V₀ :=
          (Subgroup.eq_of_le_of_card_ge hle (E3.card_conjSubgroup V₀ g).le).symm
        exact hg (by rw [← hnorm]; exact conjSubgroup_eq_iff_mem_normalizer.1 hEq)
      have huV₀ : g * w * g⁻¹ ∈ V₀ := mem_conjSubgroup_iff.1 hwV₀
      have hu1 : g * w * g⁻¹ ≠ 1 := by
        intro h1
        apply hw1
        have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
        rw [e, h1]; group
      have hcentu : centralizer ({g * w * g⁻¹} : Set G) ≤ D.M := by
        have hXV : Subgroup.zpowers (g * w * g⁻¹) ≤ V₀ := Subgroup.zpowers_le.2 huV₀
        have hX1 : Subgroup.zpowers (g * w * g⁻¹) ≠ ⊥ :=
          Subgroup.zpowers_ne_bot.mpr hu1
        have hN := h62.normalizer_le _ hXV hX1
        have hcent_eq : centralizer ({g * w * g⁻¹} : Set G) =
            centralizer (Subgroup.zpowers (g * w * g⁻¹) : Set G) := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact (le_of_eq hcent_eq).trans ((Subgroup.centralizer_le_normalizer _).trans hN)
      have hle : D.M ⊓ centralizer ({w} : Set G) ≤ D.M ⊓ conjSubgroup D.M g := by
        intro x hx
        obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.1 hx
        have hconj : g * x * g⁻¹ ∈ centralizer ({g * w * g⁻¹} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hxw' : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.1 hxc
          calc (g * x * g⁻¹) * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
            _ = g * (w * x) * g⁻¹ := by rw [hxw']
            _ = (g * w * g⁻¹) * (g * x * g⁻¹) := by group
        exact Subgroup.mem_inf.2 ⟨hxM, mem_conjSubgroup_iff.2 (hcentu hconj)⟩
      have hdvd : q ∣ Nat.card ↥(D.M ⊓ conjSubgroup D.M g) :=
        (hcent hbot w hwI hw0).trans (Subgroup.card_dvd_of_le hle)
      have hg'inv : g⁻¹ ∉ D.M := fun hh => hg (by simpa using D.M.inv_mem hh)
      exact hq.2.2 g⁻¹ hg'inv hdvd

private theorem s1611e3_sq_mem_centralizer_of_relIndex_le_two {V : Subgroup G} {t : G}
    (hV : IsElemAbelian 2 V) (ht : t ∈ Subgroup.normalizer (V : Set G))
    (hi : (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V ≤ 2) :
    t ^ 2 ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.sq_mem_centralizer_of_relIndex_le_two
    hV ht hi

theorem s1611e3_comm_mem_conj_of_hyperplane (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {g : G} (hAM : conjSubgroup V g ≤ D.M) (hm : MBarGT D.M V₀ V 1)
    (hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hγ : V₀ ⊓ conjSubgroup V g = ⊥ ∨ ((1 + mSub V₀ : ℕ) : ℕ∞) < gammaN 1 D.M V)
    {D' : Subgroup G} (hD' : D' ≤ conjSubgroup V g) (hD'1 : E3.mQuot (conjSubgroup V g) D' = 1)
    {u : G} (hu : u ∈ V) (huD : ∀ d ∈ D', ⁅u, d⁆ ∈ V₀) :
    ∀ a ∈ conjSubgroup V g, ⁅u, a⁆ ∈ conjSubgroup V₀ g := by
  have h62 : Hyp62 D.M V₀ V := Hyp125.hyp62 h
  have hV : IsElemAbelian 2 V := h62.isElemAbelian
  have hAel : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hD'M : D' ≤ conjSubgroup V g ⊓ D.M := le_inf hD' (hD'.trans hAM)
  have hD'st : D' ≤ stabTil V₀ V := h62.le_stabTil hD'M
  have hUmem : u ∈ preCTilde V₀ V D' hV := (mem_preCTilde_iff hV hD'st hu).2 huD
  have hr' : ((E3.mQuot (conjSubgroup V g) D' + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    rw [hD'1]; exact hr
  have huMg : u ∈ conjSubgroup D.M g := six_two_one h62 hD'M hr' hUmem
  have huN : u ∈ normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer, h62.normalizer_eq]
    exact huMg
  have hcomm : ⁅preCTilde V₀ V D' hV, D'⁆ = ⊥ := by
    rcases hγ with hTI | hγ'
    · have hUMg : preCTilde V₀ V D' hV ≤ conjSubgroup D.M g := six_two_one h62 hD'M hr'
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx d hd
      rw [Subgroup.mem_bot]
      have hxV : x ∈ V := preCTilde_le V₀ V D' hV hx
      have hxV₀ : ⁅x, d⁆ ∈ V₀ := (mem_preCTilde_iff hV hD'st hxV).1 hx d hd
      have hxN : x ∈ normalizer (conjSubgroup V g : Set G) := by
        rw [← E3.conjSubgroup_normalizer, h62.normalizer_eq]
        exact hUMg hx
      have hxA : ⁅x, d⁆ ∈ conjSubgroup V g := by
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hxN d).1 (hD' hd))
          (Subgroup.inv_mem _ (hD' hd))
      have hmem : ⁅x, d⁆ ∈ V₀ ⊓ conjSubgroup V g := Subgroup.mem_inf.2 ⟨hxV₀, hxA⟩
      rw [hTI, Subgroup.mem_bot] at hmem
      exact hmem
    · exact six_two_two h62 hD'M hr' (Or.inr (by rw [hD'1]; exact hγ'))
  have hcentD' : ∀ d ∈ D', u * d * u⁻¹ = d := by
    intro d hd
    have h1 : ⁅u, d⁆ = 1 := by
      have hmem : ⁅u, d⁆ ∈ ⁅preCTilde V₀ V D' hV, D'⁆ :=
        Subgroup.commutator_mem_commutator hUmem hd
      rw [hcomm, Subgroup.mem_bot] at hmem
      exact hmem
    rw [commutatorElement_eq_one_iff_mul_comm.1 h1]
    group
  have hD'rel : D'.relIndex (conjSubgroup V g) = 2 := by
    have h := E3.relIndex_eq_two_pow hAel.isPGroup D'
    rw [hD'1, pow_one] at h
    exact h
  have hD'le : D' ≤ conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G) := by
    refine le_inf hD' fun d hd => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 (hcentD' d hd)).symm
  have hrel : (conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)).relIndex
      (conjSubgroup V g) ≤ 2 := by
    have hdvd : (conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)).relIndex
        (conjSubgroup V g) ∣ D'.relIndex (conjSubgroup V g) :=
      Subgroup.relIndex_dvd_of_le_left (conjSubgroup V g) hD'le
    rw [hD'rel] at hdvd
    exact Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
  have hsqC_A : u ^ 2 ∈ Subgroup.centralizer (conjSubgroup V g : Set G) :=
    s1611e3_sq_mem_centralizer_of_relIndex_le_two hAel huN hrel
  have hsqC : CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) (u * u) := by
    intro v hv
    have hcomm' : (u * u) * v = v * (u * u) := by
      have h := Subgroup.mem_centralizer_iff.1 hsqC_A v hv
      rw [pow_two] at h
      exact h.symm
    have h1 : (u * u) * v * (u * u)⁻¹ = v := by
      rw [hcomm']; group
    rw [h1, mul_inv_cancel]
    exact (conjSubgroup V₀ g).one_mem
  have hCmod : CentralizesMod (conjSubgroup V₀ g) (conjSubgroup V g) u := by
    by_contra hnot
    have hGT : MBarGT (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) 1 :=
      (mBarGT_conj D.M V₀ V g 1).2 hm
    have hcard := hGT.1 u huMg hnot hsqC
    have hle_cent : D' ≤ centMod (conjSubgroup V₀ g) (conjSubgroup V g) u := by
      intro d hd
      refine ⟨hD' hd, ?_⟩
      have h1 : u * d * u⁻¹ = d := hcentD' d hd
      rw [h1, mul_inv_cancel]
      exact (conjSubgroup V₀ g).one_mem
    have hcardD'le : Nat.card D' ≤ Nat.card (centMod (conjSubgroup V₀ g) (conjSubgroup V g) u) :=
      Nat.card_mono (Set.toFinite _) hle_cent
    have hcardA : Nat.card (conjSubgroup V g) = 2 * Nat.card D' := by
      have h := E3.card_eq_two_pow_mul hAel.isPGroup hD'
      rw [hD'1, pow_one] at h
      exact h
    have hle : 4 * Nat.card D' ≤ 2 * Nat.card D' := by
      calc 4 * Nat.card D'
          = 2 ^ (1 + 1) * Nat.card D' := by norm_num
        _ ≤ 2 ^ (1 + 1) * Nat.card (centMod (conjSubgroup V₀ g) (conjSubgroup V g) u) :=
            Nat.mul_le_mul_left _ hcardD'le
        _ ≤ Nat.card (conjSubgroup V g) := hcard
        _ = 2 * Nat.card D' := hcardA
    have hpos : 0 < Nat.card D' := Nat.card_pos
    omega
  intro a ha
  simpa only [commutatorElement_def] using hCmod a ha

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
