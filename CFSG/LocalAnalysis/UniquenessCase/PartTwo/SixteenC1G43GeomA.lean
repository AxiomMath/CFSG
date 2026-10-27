module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c1G43_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  intro x y h
  rw [mkTil_eq_iff, Subgroup.mem_bot, mul_inv_eq_one] at h
  exact IntMod.val_injective h

theorem s16c1G43_fixed_mem {D : Data G} (h42 : R16_42 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L)
    {B : Subgroup G} {g : G} (hBM : B ≤ D.M) (hBg : B ≤ conjSubgroup V g)
    (hm : E3.mQuot (conjSubgroup V g) B = 1) (hB16 : Nat.card (barSub ⊥ V hV B) = 16)
    {b : G} (hb : b ∈ B) (hbV : b ∉ centralizer (V : Set G)) {v : G} (hv : v ∈ V)
    (hbv : b * v * b⁻¹ = v) : v ∈ conjSubgroup D.M g := by
  have hMstab : D.M ≤ stabTil ⊥ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hBst : B ≤ stabTil ⊥ V := hBM.trans hMstab
  have hB2 : IsElemAbelian2 (barSub ⊥ V hV B) := s16c1G44_isElemAbelian2_barSub hBg hBst
  have hbst : b ∈ stabTil ⊥ V := hBst hb
  set β : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨b, hbst⟩ with hβdef
  have hβB : β ∈ barSub ⊥ V hV B := actTil_mem_barSub ⊥ V hV hb hbst
  have hβne : β ≠ 1 := by
    intro h1
    apply hbV
    rw [Subgroup.mem_centralizer_iff]
    intro v' hv'
    have h2 := Subgroup.mem_bot.1 ((actTil_eq_one_iff ⊥ V hV ⟨b, hbst⟩).1 h1 v' hv')
    calc v' * b = (b * v' * b⁻¹ * v'⁻¹) * v' * b := by rw [h2]; group
      _ = b * v' := by group
  have hβ2 : β ^ 2 = 1 := hB2.2 β hβB
  set Z : Subgroup (MulAut (Vtil ⊥ V hV)) := Subgroup.zpowers β with hZdef
  have hZcard : Nat.card Z = 2 := by
    rw [hZdef, Nat.card_zpowers]
    exact orderOf_eq_prime hβ2 hβne
  set X : Subgroup G := B ⊓ preBarSub D.M ⊥ V hV Z with hXdef
  set X₀ : Subgroup G := B ⊓ preBarSub D.M ⊥ V hV ⊥ with hX₀def
  have hXB : X ≤ B := inf_le_left
  have hXM : X ≤ D.M := hXB.trans hBM
  have hXg : X ≤ conjSubgroup V g := hXB.trans hBg
  have hXst : X ≤ stabTil ⊥ V := hXM.trans hMstab
  have hbX : b ∈ X :=
    Subgroup.mem_inf.2 ⟨hb, (mem_preBarSub D.M ⊥ V hV Z).2 ⟨hBM hb, hbst, Subgroup.mem_zpowers β⟩⟩
  have hXbar : barSub ⊥ V hV X = Z := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨a, haX, rfl⟩ := (mem_barSub ⊥ V hV X φ).1 hφ
      obtain ⟨-, hpre⟩ := Subgroup.mem_inf.1 haX
      obtain ⟨-, hst, hact⟩ := (mem_preBarSub D.M ⊥ V hV Z).1 hpre
      exact hact
    · rw [hZdef, Subgroup.zpowers_le]
      exact actTil_mem_barSub ⊥ V hV hbX hbst
  have hX₀X : X₀ ≤ X := by
    intro a ha
    obtain ⟨haB, hpre⟩ := Subgroup.mem_inf.1 ha
    obtain ⟨haM, hst, hact⟩ := (mem_preBarSub D.M ⊥ V hV ⊥).1 hpre
    refine Subgroup.mem_inf.2 ⟨haB, (mem_preBarSub D.M ⊥ V hV Z).2 ⟨haM, hst, ?_⟩⟩
    rw [Subgroup.mem_bot.1 hact]
    exact Subgroup.one_mem _
  have hrelB : X₀.relIndex B = 16 := by
    rw [← hB16]
    exact s16c1G44_relIndex_inf_preBarSub_eq_card_barSub (V₀ := ⊥) (V := V) (hV := hV) hBM hBst
  have hX₀eq : X ⊓ preBarSub D.M ⊥ V hV ⊥ = X₀ := by
    ext a
    constructor
    · rintro ⟨⟨haB, _⟩, hpre⟩
      exact ⟨haB, hpre⟩
    · rintro ⟨haB, hpre⟩
      exact ⟨hX₀X ⟨haB, hpre⟩, hpre⟩
  have hX₀rel : X₀.relIndex X = 2 := by
    rw [← hX₀eq,
      s16c1G44_relIndex_inf_preBarSub_eq_card_barSub (V₀ := ⊥) (V := V) (hV := hV) hXM hXst,
      hXbar]
    exact hZcard
  have hXB8 : X.relIndex B = 8 := by
    have h := Subgroup.relIndex_mul_relIndex X₀ X B hX₀X hXB
    rw [hX₀rel, hrelB] at h
    omega
  have hmQ : E3.mQuot B X = 3 := by
    unfold E3.mQuot
    rw [hXB8, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hmX : E3.mQuot (conjSubgroup V g) X = 4 := by
    rw [E3.mQuot_add hXB hBg, hmQ, hm]
  have hXgam : X ∈ E3.gammaSet V 4 D.M := ⟨hXM, g, hXg, hmX⟩
  have hr : (((4 : ℕ) + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
    have hms : mSub (⊥ : Subgroup G) = 0 := by simp only [mSub, rk_bot]
    rw [hms, Nat.add_zero]
    exact (h42 ⊥ V L hV hS hc).2.2 rfl
  have h23 := sixteen_twentyThree_one_bot D hS.setting.hyp16 hXgam hXg hr
  have hvc : v ∈ centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a haX
    obtain ⟨-, hpre⟩ := Subgroup.mem_inf.1 haX
    obtain ⟨-, hst, hact⟩ := (mem_preBarSub D.M ⊥ V hV Z).1 hpre
    have hβx : β (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩)) = mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩) := by
      rw [hβdef, actTil_mk]
      congr 1
      apply IntMod.val_injective
      rw [actStab_apply_val]
      exact hbv
    have hs : β • mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩) = mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩) := by
      simpa [MulAut.smul_def] using hβx
    have hax := smul_eq_self_of_mem_zpowers hact hs
    have hax' : actTil ⊥ V hV ⟨a, hst⟩ (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩)) =
        mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩) := by
      simpa [MulAut.smul_def] using hax
    rw [actTil_mk] at hax'
    have h2 := congrArg IntMod.val (s16c1G43_mkTil_bot_injective hV hax')
    rw [actStab_apply_val] at h2
    calc a * v = (a * v * a⁻¹) * a := by group
      _ = v * a := by rw [show a * v * a⁻¹ = v from h2]
  exact h23.2.2 (Subgroup.mem_inf.2 ⟨hv, hvc⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
