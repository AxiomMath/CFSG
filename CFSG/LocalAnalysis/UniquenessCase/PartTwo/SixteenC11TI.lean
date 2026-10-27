module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

@[expose] def S16C11TI (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ g : G, g ∉ D.M → V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥

theorem s16c11_dvd_card_cent_of_dvd_cElt (D : Data G) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {w : G} (hw : w ∈ V) (hw0 : w ∉ V₀) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Nat.card ↥(F11.CElt D.M V₀ w)) :
    q ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨n, -, hn⟩ := r113_holds D V₀ V hH h4 w hw hw0
  have hq2' : ¬ 2 ∣ q := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h).symm
  have hcop : Nat.Coprime q (2 ^ n) := Nat.prime_two.coprime_pow_of_not_dvd hq2'
  have hcard : Nat.card ↥(F11.CElt D.M V₀ w) =
      (D.M ⊓ centralizer ({w} : Set G)).relIndex (F11.CElt D.M V₀ w) *
        Nat.card ↥((D.M ⊓ centralizer ({w} : Set G)) ⊓ F11.CElt D.M V₀ w) :=
    (Subgroup.relIndex_mul_card _ _).symm
  rw [hcard, hn] at hdvd
  exact (hcop.dvd_of_dvd_mul_left hdvd).trans (Subgroup.card_dvd_of_le inf_le_left)

theorem s16c11_dvd_card_cent_of_dvd_cTilde (D : Data G) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hK : q ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) {w : G} (hw : w ∈ V) (hw0 : w ∉ V₀) :
    q ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G)) := by
  have hle : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ w := fun c hc =>
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hc w)) hw
  exact s16c11_dvd_card_cent_of_dvd_cElt D hH h4 hw hw0 hq hq2
    (hK.trans (Subgroup.card_dvd_of_le hle))

theorem s16c11_dvd_card_cent_of_fixed_order (D : Data G) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) (h4 : Nat.card V₀ ≤ 4) (hV : IsElemAbelian 2 V) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {w : G} (hw : w ∈ V) (hw0 : w ∉ V₀)
    {φ : MulAut (Vtil V₀ V hV)} (hφM : φ ∈ Mbar D.M V₀ V hV) (hφq : orderOf φ = q)
    (hφw : φ (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) = mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) :
    q ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφM
  have hmem : (g : G) ∈ F11.CElt D.M V₀ w := by
    refine ⟨hgM, g.2.2, ?_⟩
    have h1 : actTil V₀ V hV g (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) =
        mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) := by rw [hgφ]; exact hφw
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
    simpa [IntMod.mk, IntMod.val] using h1
  have hdiv : q ∣ Nat.card ↥(F11.CElt D.M V₀ w) := by
    have h1 : q ∣ orderOf g := by
      rw [← hφq, ← hgφ]
      exact orderOf_map_dvd (actTil V₀ V hV) g
    rw [← Subgroup.orderOf_coe g] at h1
    exact h1.trans (Subgroup.orderOf_dvd_natCard _ hmem)
  exact s16c11_dvd_card_cent_of_dvd_cElt D hH h4 hw hw0 hq hq2 hdiv

theorem s16c11_tiConj_of_stronglyEmbedded (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {q : ℕ}
    (hq : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M)
    (hcent : V₀ ≠ ⊥ → ∀ w ∈ V, w ∉ V₀ → q ∣ Nat.card ↥(D.M ⊓ centralizer ({w} : Set G))) :
    S16C11TI D V₀ V := by
  intro g hg
  by_cases hbot : V₀ = ⊥
  · constructor
    · rw [hbot]; exact bot_inf_eq _
    · rw [hbot, E3.conjSubgroup_bot]; exact inf_bot_eq _
  · rcases h.1 with ⟨-, h0⟩ | ⟨hV₀0, -, -⟩
    · exact absurd h0 hbot
    · obtain ⟨hV₀cal, -, -, hTI, -, -, -⟩ := hV₀0
      have hnorm : Subgroup.normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV₀cal
      have h62 : Hyp62 D.M V₀ V := Hyp125.hyp62 h
      have hstar : ∀ g' : G, g' ∉ D.M → V ⊓ conjSubgroup V₀ g' = ⊥ := by
        intro g' hg'
        rw [eq_bot_iff]
        intro w hw
        rw [Subgroup.mem_bot]
        by_contra hw1
        obtain ⟨hwV, hwV₀⟩ := Subgroup.mem_inf.1 hw
        have hw0 : w ∉ V₀ := by
          intro hw0mem
          have hmeminf : w ∈ V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g'⁻¹ V₀ :=
            Subgroup.mem_inf.2 ⟨hw0mem, hwV₀⟩
          have hne : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g'⁻¹ V₀ ≠ ⊥ := fun hb =>
            hw1 (Subgroup.mem_bot.1 (hb ▸ hmeminf))
          have heq : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g'⁻¹ V₀ = V₀ :=
            (hTI g'⁻¹).resolve_left hne
          have hle : V₀ ≤ conjSubgroup V₀ g' := by
            calc V₀ = V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g'⁻¹ V₀ := heq.symm
              _ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g'⁻¹ V₀ := inf_le_right
          have hEq : conjSubgroup V₀ g' = V₀ :=
            (Subgroup.eq_of_le_of_card_ge hle (E3.card_conjSubgroup V₀ g').le).symm
          exact hg' (by rw [← hnorm]; exact conjSubgroup_eq_iff_mem_normalizer.1 hEq)
        have huV₀ : g' * w * g'⁻¹ ∈ V₀ := mem_conjSubgroup_iff.1 hwV₀
        have hu1 : g' * w * g'⁻¹ ≠ 1 := by
          intro h1
          apply hw1
          have e : w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
          rw [e, h1]; group
        have hcentu : centralizer ({g' * w * g'⁻¹} : Set G) ≤ D.M := by
          have hXV : Subgroup.zpowers (g' * w * g'⁻¹) ≤ V₀ := Subgroup.zpowers_le.2 huV₀
          have hX1 : Subgroup.zpowers (g' * w * g'⁻¹) ≠ ⊥ :=
            Subgroup.zpowers_ne_bot.mpr hu1
          have hN := h62.normalizer_le _ hXV hX1
          have hcent_eq : centralizer ({g' * w * g'⁻¹} : Set G) =
              centralizer (Subgroup.zpowers (g' * w * g'⁻¹) : Set G) := by
            rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          exact (le_of_eq hcent_eq).trans ((Subgroup.centralizer_le_normalizer _).trans hN)
        have hle : D.M ⊓ centralizer ({w} : Set G) ≤ D.M ⊓ conjSubgroup D.M g' := by
          intro x hx
          obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.1 hx
          have hconj : g' * x * g'⁻¹ ∈ centralizer ({g' * w * g'⁻¹} : Set G) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hxw' : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.1 hxc
            calc (g' * x * g'⁻¹) * (g' * w * g'⁻¹) = g' * (x * w) * g'⁻¹ := by group
              _ = g' * (w * x) * g'⁻¹ := by rw [hxw']
              _ = (g' * w * g'⁻¹) * (g' * x * g'⁻¹) := by group
          exact Subgroup.mem_inf.2 ⟨hxM, mem_conjSubgroup_iff.2 (hcentu hconj)⟩
        have hdvd : q ∣ Nat.card ↥(D.M ⊓ conjSubgroup D.M g') :=
          (hcent hbot w hwV hw0).trans (Subgroup.card_dvd_of_le hle)
        have hg'inv : g'⁻¹ ∉ D.M := fun hh => hg' (by simpa using D.M.inv_mem hh)
        exact hq.2.2 g'⁻¹ hg'inv hdvd
      constructor
      · rw [eq_bot_iff]
        intro w hw
        rw [Subgroup.mem_bot]
        obtain ⟨hwV₀, hwV⟩ := Subgroup.mem_inf.1 hw
        have hmem : g * w * g⁻¹ ∈ V ⊓ conjSubgroup V₀ g⁻¹ := by
          refine Subgroup.mem_inf.2 ⟨mem_conjSubgroup_iff.1 hwV, ?_⟩
          rw [mem_conjSubgroup_iff]
          have e : g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w := by group
          rw [e]; exact hwV₀
        have hg'inv : g⁻¹ ∉ D.M := fun hh => hg (by simpa using D.M.inv_mem hh)
        rw [hstar g⁻¹ hg'inv, Subgroup.mem_bot] at hmem
        have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
        rw [e, hmem]; group
      · exact hstar g hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
