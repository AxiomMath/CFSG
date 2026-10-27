module

public import CFSG.Timmesfeld.Transvection.QTwoSetup
public import CFSG.Fischer.Pairs

public section
namespace CFSG.OddTranspositions
open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open CFSG.Timmesfeld.Transvection.QTwo
open CFSG.Fischer

variable {H : Type} [Group H] {D : Set H}

theorem opposite_zpowers_of_orderOf_eq_three
    (hcls : ∀ d ∈ D, ∀ e : H, IsConj d e ↔ e ∈ D)
    (hmul : ∀ d ∈ D, d * d = 1) (hne : ∀ d ∈ D, d ≠ 1)
    {d e : H} (hd : d ∈ D) (he : e ∈ D)
    (hz : Subgroup.zpowers d ≠ Subgroup.zpowers e) (h3 : orderOf (d * e) = 3) :
    Opposite (Subgroup.zpowers d) (Subgroup.zpowers e) := by
  have hdd := hmul d hd
  have hee := hmul e he
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hp3 : (d * e) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have key : e * d * e⁻¹ = d * e * d⁻¹ := by
    have h1 : e * d * e = d⁻¹ * e⁻¹ * d⁻¹ := by
      calc e * d * e = d⁻¹ * ((d * e) * (d * e) * (d * e)) * e⁻¹ * d⁻¹ := by group
        _ = d⁻¹ * e⁻¹ * d⁻¹ := by rw [← pow_three', hp3]; group
    rw [hei, hdi, h1, hdi, hei]
  refine ⟨hz, fun a ha ha1 => ?_, fun b hb hb1 => ?_⟩
  · rcases eq_one_or_eq_of_mem_zpowers hdd ha with rfl | rfl
    · exact absurd rfl ha1
    refine ⟨e, Subgroup.mem_zpowers e, hne e he, ?_⟩
    rw [conjSub_zpowers, conjSub_zpowers, key]
  · rcases eq_one_or_eq_of_mem_zpowers hee hb with rfl | rfl
    · exact absurd rfl hb1
    refine ⟨d, Subgroup.mem_zpowers d, hne d hd, ?_⟩
    rw [conjSub_zpowers, conjSub_zpowers, key]

theorem transvectionHyp_of_qHyp (h : QHyp H D) :
    TransvectionHyp H {A | ∃ d ∈ D, A = Subgroup.zpowers d} := by
  set Δ : Set (Subgroup H) := {A | ∃ d ∈ D, A = Subgroup.zpowers d} with hΔ
  have hP := h.hyp.pair
  haveI : Finite H := hP.1
  have hmul : ∀ d ∈ D, d * d = 1 := fun d hd => Pair.mul_self hP hd
  have hne : ∀ d ∈ D, d ≠ 1 := fun d hd => Pair.ne_one hP hd
  have hcls : ∀ d ∈ D, ∀ e : H, IsConj d e ↔ e ∈ D := by
    intro d hd e
    exact ⟨fun hde => Pair.mem_of_isConj hP hd hde, fun he => Pair.isConj hP hd he⟩
  have hcardΔ : ∀ A ∈ Δ, Nat.card A = 2 := by
    rintro A ⟨d, hd, rfl⟩
    exact card_zpowers_eq_two (hmul d hd) (hne d hd)
  have hz_inj : ∀ {x y : H}, x ∈ D → y ∈ D →
      Subgroup.zpowers x = Subgroup.zpowers y → x = y := by
    intro x y hx hy hxy
    have hmem : x ∈ Subgroup.zpowers y := hxy ▸ Subgroup.mem_zpowers x
    rcases eq_one_or_eq_of_mem_zpowers (hmul y hy) hmem with h1 | h1
    · exact absurd h1 (hne x hx)
    · exact h1
  have hnebot : ∀ A ∈ Δ, A ≠ ⊥ := by
    rintro A ⟨d, hd, rfl⟩ hbot
    have hmem : d ∈ (⊥ : Subgroup H) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers d
    exact hne d hd (Subgroup.mem_bot.1 hmem)
  have hroot : IsRootClass Δ := by
    obtain ⟨d₀, hD₀⟩ := hP.2.1
    have hd₀ : d₀ ∈ D := by
      rw [hD₀]
      exact IsConj.refl d₀
    refine
      { conj_class := ?_
        ne_bot := hnebot
        mul_self := ?_
        rel := ?_
        gen := ?_ }
    · refine ⟨Subgroup.zpowers d₀, Set.ext fun A => ⟨?_, ?_⟩⟩
      · rintro ⟨d, hd, rfl⟩
        have hd' : IsConj d₀ d := by
          rw [hD₀] at hd
          exact hd
        obtain ⟨g, hg⟩ := isConj_iff.1 hd'
        exact ⟨g, by rw [conjSub_zpowers, hg]⟩
      · rintro ⟨g, rfl⟩
        refine ⟨g * d₀ * g⁻¹, ?_, by rw [conjSub_zpowers]⟩
        rw [hD₀]
        exact isConj_iff.2 ⟨g, rfl⟩
    · rintro A ⟨d, hd, rfl⟩ a ha
      rcases eq_one_or_eq_of_mem_zpowers (hmul d hd) ha with h1 | h1
      · rw [h1]
        exact one_mul 1
      · rw [h1]
        exact hmul d hd
    · rintro A ⟨d, hd, rfl⟩ B ⟨e, he, rfl⟩ hAB
      by_cases hc : d * e = e * d
      · exact Or.inl (commuting_zpowers_iff.2 hc)
      · exact Or.inr (Or.inl
          (opposite_zpowers_of_orderOf_eq_three hcls hmul hne hd he hAB
            (Pair.orderOf_mul_eq_three hP hd he hc)))
    · rw [eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
      intro d hd
      exact Subgroup.mem_iSup_of_mem (Subgroup.zpowers d)
        (Subgroup.mem_iSup_of_mem (show Subgroup.zpowers d ∈ Δ from ⟨d, hd, rfl⟩)
          (Subgroup.mem_zpowers d))
  have hnoSpecial : ∀ A ∈ Δ, ∀ B ∈ Δ, ¬ Special Δ A B := by
    intro A hA B hB hsp
    obtain ⟨d, hd, rfl⟩ := hA
    obtain ⟨e, he, rfl⟩ := hB
    have hdd := hmul d hd
    have hee := hmul e he
    by_cases hc : Commuting (Subgroup.zpowers d) (Subgroup.zpowers e)
    · have hmem : (⊥ : Subgroup H) ∈ Δ := by
        rw [← commuting_iff_commutator_eq_bot.1 hc]
        exact hsp.1
      exact hnebot ⊥ hmem rfl
    · have hde : d * e ≠ e * d := fun heq => hc (commuting_zpowers_iff.2 heq)
      have h3 : orderOf (d * e) = 3 := Pair.orderOf_mul_eq_three hP hd he hde
      have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
      have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
      letI : Bracket H H := commutatorElement
      have hcomm : ⁅d, e⁆ = (d * e) ^ 2 := by
        rw [commutatorElement_def, hdi, hei, pow_two]
        group
      set C : Subgroup H := ⁅Subgroup.zpowers d, Subgroup.zpowers e⁆ with hC
      have hmem : (d * e) ^ 2 ∈ C := by
        rw [hC, ← hcomm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers d)
          (Subgroup.mem_zpowers e)
      have hdvd : orderOf ((d * e) ^ 2) ∣ Nat.card C :=
        Subgroup.orderOf_dvd_natCard C hmem
      have hcard : Nat.card C = 2 :=
        hcardΔ C (by rw [hC]; exact hsp.1)
      have hord : orderOf ((d * e) ^ 2) = 3 := by
        rw [orderOf_pow, h3]
        norm_num
      rw [hcard, hord] at hdvd
      norm_num at hdvd
  refine
    { finite := hP.1
      cls := ⟨hroot, hnoSpecial⟩
      points := ?_
      center := h.hyp.center
      rank := ?_
      small := ?_ }
  · intro A hA B hB hAB
    obtain ⟨d, hd, rfl⟩ := hA
    obtain ⟨e, he, rfl⟩ := hB
    have hpoint : ∀ c ∈ D, c * d = d * c ↔ c * e = e * c := by
      intro c hc
      have hcc := hAB (Subgroup.zpowers c) (show Subgroup.zpowers c ∈ Δ from ⟨c, hc, rfl⟩)
      rw [commuting_zpowers_iff, commuting_zpowers_iff] at hcc
      exact ⟨fun h' => (hcc.mp h'.symm).symm, fun h' => (hcc.mpr h'.symm).symm⟩
    have hde : d = e := h.points d hd e he hpoint
    rw [hde]
  · obtain ⟨e, he, f, hf, hef, hc⟩ := h.rank
    exact ⟨Subgroup.zpowers e, ⟨e, he, rfl⟩, Subgroup.zpowers f, ⟨f, hf, rfl⟩,
      fun hEq => hef (hz_inj he hf hEq), commuting_zpowers_iff.2 hc⟩
  · intro _
    refine ⟨h.hyp.simple, ?_⟩
    intro A hA B hB hAB hcAB
    obtain ⟨e, he, rfl⟩ := hA
    obtain ⟨f, hf, rfl⟩ := hB
    have hef : e ≠ f := fun hEq => hAB (by rw [hEq])
    have hc : e * f = f * e := commuting_zpowers_iff.1 hcAB
    obtain ⟨g, hg, hge, hgf, hall⟩ := h.thick e he f hf hef hc
    refine ⟨Subgroup.zpowers g, ⟨g, hg, rfl⟩, ?_, ?_, ?_⟩
    · intro hEq
      exact hge (hz_inj hg he hEq)
    · intro hEq
      exact hgf (hz_inj hg hf hEq)
    · intro C hC hCA hCB
      obtain ⟨c, hc, rfl⟩ := hC
      exact commuting_zpowers_iff.2
        (hall c hc (commuting_zpowers_iff.1 hCA) (commuting_zpowers_iff.1 hCB))

end CFSG.OddTranspositions
