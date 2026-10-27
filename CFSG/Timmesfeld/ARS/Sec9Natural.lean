module

public import CFSG.Timmesfeld.ARS.CaseD4Frame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

theorem commuting_of_mem_lambdaSet_inter (h : Hyp G R) {A X Y Z : Subgroup G} (hA : A ∈ R)
    (hZ : Z ∈ R) (hZA : Z ≠ A) (hXZ : X ∈ lambdaSet R Z) (hYZ : Y ∈ lambdaSet R Z)
    (hXA : X ∈ lambdaSet R A) (hYA : Y ∈ lambdaSet R A) : Commuting X Y := by
  have := h.finite
  have h1 : ⁅X, Y⁆ ≤ Z := by
    rw [← (Q_eq_M h hZ).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hXZ) (QD.le_M hYZ)
  have h2 : ⁅X, Y⁆ ≤ A := by
    rw [← (Q_eq_M h hA).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hXA) (QD.le_M hYA)
  have h3 := le_inf h1 h2
  rw [inf_eq_bot h.root h.noIsolated hZ hA hZA] at h3
  exact commuting_iff_commutator_eq_bot.2 (le_bot_iff.1 h3)

theorem mem_lambdaSet_commutator_commutator (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) {E F B D : Subgroup G}
    (hEl : E ∈ leviSet R A A₀) (hFl : F ∈ leviSet R A A₀) (hEF : Opposite E F)
    (hB : B ∈ lambdaStar R A A₀) (hBE : B ∈ lambdaSet R E) (hFB : Special R F B)
    (hDl : D ∈ leviSet R A A₀) (hDP : ∀ x ∈ E ⊔ F, Special R (conjSub B x) D) :
    ⁅⁅F, B⁆, D⁆ ∈ lambdaSet R ⁅B, D⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hER : E ∈ R := hEl.1.1
  have hFR : F ∈ R := hFl.1.1
  have hDR : D ∈ R := hDl.1.1
  have hBR : B ∈ R := hB.1.1.1
  have hBψ : B ∈ psiSet R F := ⟨hBR, hFB⟩
  set Bb := ⁅F, B⁆ with hBbdef
  have hBbR : Bb ∈ R := hFB.1
  obtain ⟨x₀, hx₀, hBbx₀⟩ : ∃ x ∈ E ⊔ F, conjSub B x = Bb := by
    obtain ⟨p, hp, hp1⟩ := hR.exists_ne_one hBbR
    obtain ⟨x, hx, hpx⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hER hFR hEF hBE hBψ
      (Subgroup.mem_sup_right hp) hp1
    exact ⟨x, hx, Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hBR x) hBbR hpx hp hp1⟩
  have hBbst : Bb ∈ lambdaStar R A A₀ :=
    hBbx₀ ▸ conjSub_mem_lambdaStar_of_mem_levi hR hB (sup_le (le_gen hEl) (le_gen hFl) hx₀)
  have hBD : Special R B D := by
    have := hDP 1 (Subgroup.one_mem _)
    rwa [conjSub_one] at this
  have hBbD : Special R Bb D := hBbx₀ ▸ hDP x₀ hx₀
  set C₁ := ⁅B, D⁆ with hC₁def
  set C₂ := ⁅Bb, D⁆ with hC₂def
  have hC₁R : C₁ ∈ R := hBD.1
  have hC₂R : C₂ ∈ R := hBbD.1
  have hC₁st : C₁ ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hDl hB hBD).1 C₁ hC₁R le_sup_right
  have hC₂st : C₂ ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hDl hBbst hBbD).1 C₂ hC₂R le_sup_right
  have hC₁D : C₁ ∈ lambdaSet R D :=
    mem_lambdaSet_comm hC₁R (mem_lambdaSet_commutator hR hiso hBR hDR hBD).2
  have hC₂D : C₂ ∈ lambdaSet R D :=
    mem_lambdaSet_comm hC₂R (mem_lambdaSet_commutator hR hiso hBbR hDR hBbD).2
  have hC12 : Commuting C₁ C₂ :=
    commuting_of_mem_lambdaSet_inter h hA hDR hDl.1.2.1 hC₁D hC₂D hC₁st.1 hC₂st.1
  have hBbB : Bb ∈ lambdaSet R B :=
    mem_lambdaSet_comm hBbR (mem_lambdaSet_commutator hR hiso hFR hBR hFB).2
  have hC₁B : C₁ ∈ lambdaSet R B :=
    mem_lambdaSet_comm hC₁R (mem_lambdaSet_commutator hR hiso hBR hDR hBD).1
  have hBbC₁ : Commuting Bb C₁ :=
    commuting_of_mem_lambdaSet_inter h hA hBR hB.1.1.2.1 hBbB hC₁B hBbst.1 hC₁st.1
  have hBBb : B ≠ Bb := by
    have := hFB.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm B F] at this
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  have hC12ne : C₁ ≠ C₂ := by
    intro e
    obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
    have hbd : ⁅b, d⁆ ∈ C₂ := e ▸ Subgroup.commutator_mem_commutator hb hd
    obtain ⟨b', hb', hbb'⟩ := (bijOn_commutator_left hR hiso hBbR hDR hBbD hd hd1).surjOn hbd
    have hbb'' : ⁅b', d⁆ = ⁅b, d⁆ := hbb'
    have hcomm : Commute (b⁻¹ * b') d := by
      rw [commutatorElement_def, commutatorElement_def] at hbb''
      have : b' * d * b'⁻¹ = b * d * b⁻¹ := mul_right_cancel hbb''
      change b⁻¹ * b' * d = d * (b⁻¹ * b')
      calc b⁻¹ * b' * d = b⁻¹ * (b' * d * b'⁻¹) * b' := by group
        _ = b⁻¹ * (b * d * b⁻¹) * b' := by rw [this]
        _ = d * (b⁻¹ * b') := by group
    have hn : b⁻¹ * b' ∈ B ⊔ Bb :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (B.inv_mem hb)) (Subgroup.mem_sup_right hb')
    have hn1 : b⁻¹ * b' ≠ 1 := by
      intro e1
      rw [inv_mul_eq_one] at e1
      subst e1
      have : b ∈ B ⊓ Bb := ⟨hb, hb'⟩
      rw [inf_eq_bot hR hiso hBR hBbR hBBb, Subgroup.mem_bot] at this
      exact hb1 this
    obtain ⟨x, hx, hnx⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hER hFR hEF hBE hBψ hn hn1
    exact hd1 (eq_one_of_commute_of_special hR hiso (hR.conjSub_mem hBR x) hDR (hDP x hx) hnx
      hn1 hd hcomm)
  have hBN' : Bb ≤ Subgroup.normalizer ((B : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun b hb => (hBbB.1.2.2 b hb y hy).symm)
  have hmulN : ∀ n ∈ B ⊔ Bb, ∃ b ∈ B, ∃ b' ∈ Bb, b * b' = n := fun n hn => by
    have hn' : n ∈ ((B ⊔ Bb : Subgroup G) : Set G) := hn
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBN'] at hn'
    obtain ⟨b, hb, b', hb', e⟩ := hn'
    exact ⟨b, hb, b', hb', e⟩
  have hcommN : ∀ n ∈ B ⊔ Bb, ∀ d' ∈ D, ⁅n, d'⁆ ∈ C₁ ⊔ C₂ := by
    intro n hn d' hd'
    obtain ⟨b, hb, b', hb', rfl⟩ := hmulN n hn
    have hbb' : Commute b b' := hBbB.1.2.2 b hb b' hb'
    have h1 : ⁅b * b', d'⁆ = ⁅b, d'⁆ * ⁅b', d'⁆ := by
      rw [hbb'.eq]
      exact Plane.commutatorElement_mul_left_of_commute
        (hBbC₁ b' hb' _ (Subgroup.commutator_mem_commutator hb hd'))
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hb hd'))
      (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hb' hd'))
  refine ⟨⟨hC₂R, hC12ne.symm, hC12⟩, fun c hc hc1 => ?_⟩
  have hC₂N : C₂ ≤ Subgroup.normalizer ((C₁ : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun c hc => (hC12 c hc y hy).symm)
  have hc' : c ∈ ((C₁ ⊔ C₂ : Subgroup G) : Set G) := hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hC₂N] at hc'
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hc'
  simp only at hc1 ⊢
  obtain ⟨b, hb, hbc⟩ := (bijOn_commutator_left hR hiso hBR hDR hBD hd hd1).surjOn hc₁
  obtain ⟨b', hb', hb'c⟩ := (bijOn_commutator_left hR hiso hBbR hDR hBbD hd hd1).surjOn hc₂
  have hbc' : ⁅b, d⁆ = c₁ := hbc
  have hb'c' : ⁅b', d⁆ = c₂ := hb'c
  have he : ⁅b * b', d⁆ = c₁ * c₂ := by
    rw [← hbc', ← hb'c', (hBbB.1.2.2 b hb b' hb').eq]
    exact Plane.commutatorElement_mul_left_of_commute
      (hBbC₁ b' hb' _ (Subgroup.commutator_mem_commutator hb hd))
  have hn : b * b' ∈ B ⊔ Bb :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hb')
  have hn1 : b * b' ≠ 1 := fun e => hc1 (by rw [← he, e, commutatorElement_one_left])
  obtain ⟨x, hx, hnx⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hER hFR hEF hBE hBψ hn hn1
  refine ⟨⁅conjSub B x, D⁆, (hDP x hx).1, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro p hp d' hd'
    refine hcommN p ?_ d' hd'
    rw [← Sec3.conjSub_sup_commutator_eq hR hiso hER hFR hEF hBE hBψ hx]
    exact Subgroup.map_mono le_sup_left hp
  · rw [← he]
    exact Subgroup.commutator_mem_commutator hnx hd

end Sec9

end CFSG.Timmesfeld.ARS
