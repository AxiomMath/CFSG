module

public import CFSG.Quasithin.EmptyFaithful.F918C14
public import CFSG.Quasithin.Background.F918C12
public import CFSG.Quasithin.Background.F918C4

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

section Case2

variable {W : Type} [CommGroup W]

structure Case2Data (L L' : Subgroup (MulAut W)) (V : Subgroup W) (σ : MulAut W) : Prop where
  card : Nat.card ↥V = 8
  irr : XMod.IsIrr ↥L V
  direct : IsIntDirect V (V.map σ.toMonoidHom) (commV L)
  perp : commV L ≤ fixV L'

theorem Case2Data.conj {L L' : Subgroup (MulAut W)} {V : Subgroup W} {σ : MulAut W}
    (h : Case2Data L L' V σ) (c : MulAut W) :
    Case2Data (conjAutSub c L) (conjAutSub c L') (V.map c.toMonoidHom) (c * σ * c⁻¹) := by
  refine ⟨?_, isIrr_map_conj c h.irr, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective c.injective]
    exact h.card
  · have h1 : (V.map c.toMonoidHom).map (c * σ * c⁻¹).toMonoidHom =
        (V.map σ.toMonoidHom).map c.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      show (c * σ * c⁻¹) (c x) = c (σ x)
      simp [MulAut.mul_apply]
    rw [h1, ← map_commV_conj]
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.map_sup, h.direct.1]
    · rw [← Subgroup.map_inf _ _ _ c.injective, h.direct.2, Subgroup.map_bot]
  · rw [← map_commV_conj, ← map_fixV_conj]
    exact Subgroup.map_mono h.perp

theorem case2_iii [Finite W] {M Mp T L : Subgroup (MulAut W)}
    {V : Subgroup W} {t σ : MulAut W}
    (hD : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L) (hσT : σ ∈ T)
    (hσL : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hL32 : IsPSL 3 2 1 ↥L)
    (hout : ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹))
    (hF : ModFiveIii Mp T L V t) : Case2Data L (conjAutSub t L) V σ := by
  obtain ⟨hsum, hfix, hcases⟩ := hF
  have hW2 := hD.hyp.exp
  have hTM : T ≤ M := hD.hyp.sylow.1
  have hσMp : σ ∈ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.hyp.Mp_normal (hTM hσT)
  have hσL' : ∀ x ∈ L, σ * x * σ⁻¹ ∈ L := fun x hx => (Subgroup.mem_normalizer_iff.1 hσL x).1 hx
  rcases hcases with ⟨hA, -⟩ | hB | hC | hDD
  ·
    exfalso
    have hnat := modFiveA_l32 hL32 hA
    have hVc : commV L = V := hA.1
    have hσV : V.map σ.toMonoidHom = V := by
      have := map_commV_eq_of_normalizes hσL
      rwa [hVc] at this
    exact hout (A6Twist.inner_of_stable_nat3 hnat hσL hσV (A6Twist.map_inf_fixV_eq hσMp hσV))
  ·
    obtain ⟨-, ⟨s₁, hs₁T, hs₁N, hs₁V⟩, hall, hcardV⟩ := hB
    have hdir₁ := hall s₁ hs₁T hs₁N hs₁V
    have hVle : V ≤ commV L := hdir₁.1 ▸ le_sup_left
    have hVfix : ∀ y ∈ conjAutSub t L, ∀ v ∈ V, y v = v := fun y hy v hv => hfix (hVle hv) y hy
    have hirrMp := hD.irrT.1.2
    have hVinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V := fun x hx v hv =>
      hirrMp.1 ⟨x, hMp ▸ Subgroup.mem_sup_left hx⟩ v hv
    have hcommL : XMod.commOf ↥L V = V := by
      refine commOf_eq_of_trivial hVinv hVfix ?_
      rw [← hMp]
      exact hirrMp.2.1
    have hcard8 : Nat.card ↥V = 8 := by simpa using hcardV
    have hVne : V ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcard8
      omega
    have hnt : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := by
      by_contra hcon
      push Not at hcon
      have hbot : XMod.commOf ↥L V ≤ ⊥ := by
        rw [XMod.commOf_le_iff]
        intro a l hl
        have : (a : MulAut W) l = l := hcon a a.2 l hl
        show (a : MulAut W) l * l⁻¹ ∈ (⊥ : Subgroup W)
        rw [Subgroup.mem_bot, this, mul_inv_cancel]
      rw [hcommL] at hbot
      exact hVne (le_bot_iff.mp hbot)
    have hnstab : σ ∉ stabSub V := fun hst =>
      hout (inner_of_stable_card_eight hW2 hL32 hVinv hcard8 hnt hσL' hst)
    refine ⟨hcard8, ⟨fun a v hv => hVinv a a.2 v hv, bot_lt_iff_ne_bot.mpr hVne,
      fun J hJinv _ hJV => rank3_irr hL32 hVinv hcard8 hcommL J hJV
        (fun x hx j hj => hJinv ⟨x, hx⟩ j hj)⟩, hall σ hσT hσL hnstab, hfix⟩
  ·
    exfalso
    obtain ⟨-, I, π, -, -, hsum', hreal⟩ := hC
    have hX : (⨆ i, I i) = commV L := by simpa using hsum'
    refine hout (inner_of_stable_isotypic (F := ZMod 2) (by simp) hW2 I hreal hσL ?_)
    rw [hX]
    exact map_commV_eq_of_normalizes hσL
  ·
    exfalso
    obtain ⟨n, hn, -⟩ := hDD
    exact not_isPSL_two_two_of_isPSL_three_two hL32 hn

@[expose] def TensorTwistL32 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (Mp L L' : Subgroup (MulAut W)) (σ : MulAut W),
    IsPSL 3 2 1 ↥L → IsPSL 3 2 1 ↥L' → Mp = L ⊔ L' → (∀ x ∈ L, ∀ y ∈ L', x * y = y * x) →
    TensorNatL32 (autSub Mp (⊤ : Subgroup W)) →
    σ ∈ Subgroup.normalizer (L : Set (MulAut W)) → σ ∈ Subgroup.normalizer (Mp : Set (MulAut W)) →
    ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹)

theorem conj_mem_normalizer_conjAutSub {L : Subgroup (MulAut W)} {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (t : MulAut W) :
    t * σ * t⁻¹ ∈ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjAutSub_iff, mem_conjAutSub_iff]
  have e : t⁻¹ * (t * σ * t⁻¹ * y * (t * σ * t⁻¹)⁻¹) * t = σ * (t⁻¹ * y * t) * σ⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.1 hσ _

theorem isPSL_conjAutSub {L : Subgroup (MulAut W)} (t : MulAut W) {n p e : ℕ} (h : IsPSL n p e ↥L) :
    IsPSL n p e ↥(conjAutSub t L) :=
  isPSL_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective) h

theorem not_inner_conj {L : Subgroup (MulAut W)} {σ : MulAut W} (t : MulAut W)
    (hout : ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹)) :
    ¬ ∃ l₀ ∈ conjAutSub t L, ∀ x ∈ conjAutSub t L,
      ((t * σ * t⁻¹) * l₀⁻¹) * x = x * ((t * σ * t⁻¹) * l₀⁻¹) := by
  rintro ⟨l₀', hl₀', h⟩
  apply hout
  refine ⟨t⁻¹ * l₀' * t, mem_conjAutSub_iff.mp hl₀', fun x hx => ?_⟩
  have hx' : t * x * t⁻¹ ∈ conjAutSub t L := by
    rw [mem_conjAutSub_iff]
    simpa [mul_assoc] using hx
  have h1 := h _ hx'
  have e1 : (t * σ * t⁻¹ * l₀'⁻¹) * (t * x * t⁻¹) = t * ((σ * (t⁻¹ * l₀' * t)⁻¹) * x) * t⁻¹ := by group
  have e2 : (t * x * t⁻¹) * (t * σ * t⁻¹ * l₀'⁻¹) = t * (x * (σ * (t⁻¹ * l₀' * t)⁻¹)) * t⁻¹ := by group
  rw [e1, e2] at h1
  have h2 := mul_left_cancel (mul_right_cancel h1)
  exact h2

theorem conjAutSub_inv_eq {L : Subgroup (MulAut W)} {t : MulAut W}
    (htt : t * t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    conjAutSub t⁻¹ L = conjAutSub t L := by
  ext x
  rw [mem_conjAutSub_iff, mem_conjAutSub_iff]
  have e : t⁻¹⁻¹ * x * t⁻¹ = (t * t) * (t⁻¹ * x * t) * (t * t)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 htt _).symm

theorem case2_core
    [Finite W] (hT : TensorTwistL32) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t σ : MulAut W} (hD : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L) (ht : t ∈ T)
    (htt : t * t ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hLL : ∀ x ∈ L, ∀ y ∈ conjAutSub t L, x * y = y * x) (hσT : σ ∈ T)
    (hσL : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) (hL32 : IsPSL 3 2 1 ↥L)
    (hout : ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹))
    (hF : ModFive M Mp T L V t) :
    ∃ V' : Subgroup W, Case2Data L (conjAutSub t L) V' σ ∧
      (V' = V ∨ V' = V.map t⁻¹.toMonoidHom) := by
  have hTM : T ≤ M := hD.hyp.sylow.1
  have hσMp : σ ∈ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.hyp.Mp_normal (hTM hσT)
  have hL32' : IsPSL 3 2 1 ↥(conjAutSub t L) := isPSL_conjAutSub t hL32
  rcases hF with ⟨hVtop, -, n, hn, -⟩ | ⟨hVtop, -, -, hTens⟩ | hF3 | hF4
  · exfalso
    exact not_isPSL_two_two_of_isPSL_three_two hL32 (isPSL_of_autSub_top hVtop hn)
  · exfalso
    subst hVtop
    exact hout (hT W Mp L (conjAutSub t L) σ hL32 hL32' hMp hLL hTens hσL hσMp)
  · exact ⟨V, case2_iii hD hMp hσT hσL hL32 hout hF3, Or.inl rfl⟩
  ·
    have hD' : D3Std M Mp T (conjAutSub t L) V := ⟨hD.hyp.conj ht, hD.qhat, hD.irrT⟩
    have hMp' : Mp = conjAutSub t L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := by
      rw [conjAutSub_inv_conjAutSub, sup_comm]
      exact hMp
    have hσ'T : t * σ * t⁻¹ ∈ T := T.mul_mem (T.mul_mem ht hσT) (T.inv_mem ht)
    have h1 := case2_iii hD' hMp' hσ'T (conj_mem_normalizer_conjAutSub hσL t) hL32'
      (not_inner_conj t hout) hF4
    have h2 := h1.conj t⁻¹
    rw [conjAutSub_inv_conjAutSub, conjAutSub_inv_eq htt] at h2
    have e2 : t⁻¹ * (t * σ * t⁻¹) * t⁻¹⁻¹ = σ := by group
    rw [e2] at h2
    exact ⟨V.map t⁻¹.toMonoidHom, h2, Or.inr rfl⟩

end Case2

end CFSG.Quasithin
