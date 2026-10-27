module

public import CFSG.Quasithin.Background.F918V2Defs
public import CFSG.Quasithin.EmptyFaithful.S153ZK

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] def ThreeCopies (Λ : Subgroup Γ) (Vq : Subgroup Q) : Prop :=
  ∃ S₀ S₁ : Subgroup Q, XMod.IsIrr ↥Λ S₀ ∧ XMod.IsIrr ↥Λ S₁ ∧ XMod.Iso ↥Λ S₀ Vq ∧
    XMod.Iso ↥Λ S₁ Vq ∧ Vq ⊓ S₀ = ⊥ ∧ (Vq ⊔ S₀) ⊓ S₁ = ⊥

theorem v2c_exists_isIrr_le [Finite Q] {A : Type*} [Group A] [MulDistribMulAction A Q]
    {J : Subgroup Q} (hJ : XMod.IsInv A J) (hne : J ≠ ⊥) :
    ∃ R : Subgroup Q, R ≤ J ∧ XMod.IsIrr A R := by
  classical
  induction' hn : Nat.card J using Nat.strong_induction_on with n ih generalizing J
  by_cases hirr : XMod.IsIrr A J
  · exact ⟨J, le_rfl, hirr⟩
  · have h : ∃ K : Subgroup Q, XMod.IsInv A K ∧ K ≤ J ∧ K ≠ ⊥ ∧ K ≠ J := by
      by_contra hcon
      push Not at hcon
      refine hirr ⟨hJ, bot_lt_iff_ne_bot.2 hne, fun K hK _ hKJ => ?_⟩
      by_cases hK0 : K = ⊥
      · exact Or.inl hK0
      · exact Or.inr (hcon K hK hKJ hK0)
    obtain ⟨K, hK, hKJ, hK0, hKne⟩ := h
    have hlt : K < J := lt_of_le_of_ne hKJ hKne
    have hcard : Nat.card K < Nat.card J := Subgroup.card_lt_of_lt hlt
    obtain ⟨R, hRK, hR⟩ := ih (Nat.card K) (hn ▸ hcard) hK hK0 rfl
    exact ⟨R, hRK.trans hKJ, hR⟩

theorem v2c_inf_eq_bot_or_le {A : Type*} [Group A] [MulDistribMulAction A Q] {R J : Subgroup Q}
    (hR : XMod.IsIrr A R) (hJ : XMod.IsInv A J) : R ⊓ J = ⊥ ∨ R ≤ J := by
  rcases hR.2.2 (R ⊓ J) (hR.1.inf hJ) bot_le inf_le_left with h | h
  · exact Or.inl h
  · exact Or.inr (inf_eq_left.1 h)

theorem v2c_exists_iso_of_le_iSup {A : Type*} [Group A] [MulDistribMulAction A Q] {ι : Type*}
    {S : ι → Subgroup Q} (hS : ∀ i, XMod.IsIrr A (S i)) {V : Subgroup Q} (hV : XMod.IsIrr A V)
    (hle : V ≤ ⨆ i, S i) : ∃ i, XMod.Iso A V (S i) := by
  have hinv : ∀ i, XMod.IsInv A (S i) := fun i => (hS i).1
  have hP : XMod.IsInv A (⨆ i, S i) := XMod.isInv_iSup hinv
  have h1 : XMod.toSubmod hV.1 ≤ ⨆ i, XMod.toSubmod (hinv i) := by
    rw [← XMod.toSubmod_iSup hinv]
    exact (XMod.toSubmod_le_iff (hL := hV.1) (hL' := hP)).2 hle
  rw [← sSup_range] at h1
  have hsimple : ∀ m : ↥(Set.range fun i => XMod.toSubmod (hinv i)),
      IsSimpleModule ↥(XMod.opRing A Q)
        ↥(m : Submodule ↥(XMod.opRing A Q) (Additive Q)) := by
    rintro ⟨_, i, rfl⟩
    exact (XMod.isIrr_iff (hinv i)).1 (hS i)
  have hVs : IsSimpleModule ↥(XMod.opRing A Q) ↥(XMod.toSubmod hV.1) :=
    (XMod.isIrr_iff hV.1).1 hV
  obtain ⟨S', ⟨i, rfl⟩, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup (XMod.toSubmod hV.1) _ h1
  exact ⟨i, (XMod.iso_iff hV.1 (hinv i)).2 ⟨e⟩⟩

@[expose] def v2cCopies (Λ : Subgroup Γ) (W : Subgroup Q) : Subgroup Q :=
  ⨆ R : {R : Subgroup Q // XMod.IsIrr ↥Λ R ∧ XMod.Iso ↥Λ R W}, (R : Subgroup Q)

theorem v2c_le_copies {Λ : Subgroup Γ} {W R : Subgroup Q} (hR : XMod.IsIrr ↥Λ R)
    (hiso : XMod.Iso ↥Λ R W) : R ≤ v2cCopies Λ W :=
  le_iSup (fun R' : {R' : Subgroup Q // XMod.IsIrr ↥Λ R' ∧ XMod.Iso ↥Λ R' W} =>
    (R' : Subgroup Q)) ⟨R, hR, hiso⟩

theorem v2c_isInv_copies {Λ : Subgroup Γ} (W : Subgroup Q) :
    XMod.IsInv ↥Λ (v2cCopies Λ W) :=
  XMod.isInv_iSup fun R => R.2.1.1

theorem v2c_iso_of_le_copies {Λ : Subgroup Γ} {W R : Subgroup Q} (hR : XMod.IsIrr ↥Λ R)
    (hle : R ≤ v2cCopies Λ W) : XMod.Iso ↥Λ R W := by
  obtain ⟨R', hiso⟩ := v2c_exists_iso_of_le_iSup
    (S := fun R' : {R' : Subgroup Q // XMod.IsIrr ↥Λ R' ∧ XMod.Iso ↥Λ R' W} =>
      (R' : Subgroup Q)) (fun R' => R'.2.1) hR hle
  exact hiso.trans R'.2.2

theorem v2c_smul_iSup {ι : Sort*} (g : Γ) (R : ι → Subgroup Q) :
    g • (⨆ i, R i) = ⨆ i, g • R i := by
  have h : ∀ T : Subgroup Q, g • T = T.map (MulDistribMulAction.toMonoidHom Q g) := fun T => rfl
  rw [h, Subgroup.map_iSup]
  exact iSup_congr fun i => (h (R i)).symm

theorem v2c_smul_copies {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (g : Γ)
    (W : Subgroup Q) : g • v2cCopies Λ W = v2cCopies Λ (g • W) := by
  have hN : XMod.Normalizes ↥Λ Γ Q := normalizes_whole Λ hΛ
  unfold v2cCopies
  rw [v2c_smul_iSup]
  apply le_antisymm
  · refine iSup_le fun R => ?_
    exact le_iSup (fun R' : {R' : Subgroup Q // XMod.IsIrr ↥Λ R' ∧ XMod.Iso ↥Λ R' (g • W)} =>
      (R' : Subgroup Q)) ⟨g • R.1, isIrr_smul hN g R.2.1, XMod.iso_smul hN g R.2.2⟩
  · refine iSup_le fun R' => ?_
    have hR : XMod.IsIrr ↥Λ (g⁻¹ • R'.1) := isIrr_smul hN g⁻¹ R'.2.1
    have hiso : XMod.Iso ↥Λ (g⁻¹ • R'.1) W := by
      have := XMod.iso_smul hN g⁻¹ R'.2.2
      rwa [inv_smul_smul] at this
    calc (R'.1 : Subgroup Q) = g • (g⁻¹ • R'.1) := (smul_inv_smul g R'.1).symm
      _ ≤ ⨆ R : {R : Subgroup Q // XMod.IsIrr ↥Λ R ∧ XMod.Iso ↥Λ R W}, g • (R : Subgroup Q) :=
        le_iSup (fun R : {R : Subgroup Q // XMod.IsIrr ↥Λ R ∧ XMod.Iso ↥Λ R W} =>
          g • (R : Subgroup Q)) ⟨g⁻¹ • R'.1, hR, hiso⟩

theorem v2c_copies_inf_eq_bot [Finite Q] {Λ : Subgroup Γ} {W W' : Subgroup Q}
    (h : ¬ XMod.Iso ↥Λ W W') : v2cCopies Λ W ⊓ v2cCopies Λ W' = ⊥ := by
  by_contra hne
  have hinv : XMod.IsInv ↥Λ (v2cCopies Λ W ⊓ v2cCopies Λ W') :=
    (v2c_isInv_copies W).inf (v2c_isInv_copies W')
  obtain ⟨R, hRle, hR⟩ := v2c_exists_isIrr_le hinv hne
  have h1 : XMod.Iso ↥Λ R W := v2c_iso_of_le_copies hR (hRle.trans inf_le_left)
  have h2 : XMod.Iso ↥Λ R W' := v2c_iso_of_le_copies hR (hRle.trans inf_le_right)
  exact h ((XMod.Iso.symm hR.1 h1).trans h2)

section TwoTypeLemmas

variable {Λ T₀ : Subgroup Γ} {Vq : Subgroup Q} {t : Γ}

theorem v2c_normalizes (hD : TwoTypeBase Λ T₀ Vq t) : XMod.Normalizes ↥Λ Γ Q :=
  normalizes_whole Λ hD.normal

theorem v2c_isIrr_smul (hD : TwoTypeBase Λ T₀ Vq t) (g : Γ) : XMod.IsIrr ↥Λ (g • Vq) :=
  isIrr_smul (v2c_normalizes hD) g hD.irr

theorem v2c_inf_tVq (hD : TwoTypeBase Λ T₀ Vq t) : Vq ⊓ t • Vq = ⊥ := by
  rcases v2c_inf_eq_bot_or_le hD.irr (v2c_isIrr_smul hD t).1 with h | h
  · exact h
  · exfalso
    rcases (v2c_isIrr_smul hD t).2.2 Vq hD.irr.1 bot_le h with h0 | h1
    · exact hD.irr.2.1.ne' h0
    · exact hD.tmove h1.symm

theorem v2c_smul_t_smul_t (hD : TwoTypeBase Λ T₀ Vq t) : t • t • Vq = Vq := by
  have h := hD.stab (t * t) (T₀.mul_mem hD.tT hD.tT)
  rw [mul_smul] at h
  rcases h with h | h
  · exact h
  · exact absurd (MulAction.injective t h) hD.tmove

theorem v2c_fix_fix (hD : TwoTypeBase Λ T₀ Vq t) {s : Γ} (hs : s ∈ T₀) (h : s • Vq = Vq) :
    s • t • Vq = t • Vq := by
  have h1 := hD.stab (s * t) (T₀.mul_mem hs hD.tT)
  rw [mul_smul] at h1
  rcases h1 with h1 | h1
  · exact absurd (MulAction.injective s (h1.trans h.symm)) hD.tmove
  · exact h1

theorem v2c_swap (hD : TwoTypeBase Λ T₀ Vq t) {s : Γ} (hs : s ∈ T₀) (h : s • Vq = t • Vq) :
    s • t • Vq = Vq := by
  have h1 := hD.stab (s * t) (T₀.mul_mem hs hD.tT)
  rw [mul_smul] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd (MulAction.injective s (h1.trans h.symm)) hD.tmove

theorem v2c_smul_X (hD : TwoTypeBase Λ T₀ Vq t) : t • (Vq ⊔ t • Vq) = Vq ⊔ t • Vq := by
  rw [Subgroup.smul_sup, v2c_smul_t_smul_t hD, sup_comm]

theorem v2c_copies_sup_eq_top (hD : TwoType Λ T₀ Vq t) :
    v2cCopies Λ Vq ⊔ v2cCopies Λ (t • Vq) = ⊤ := by
  rw [eq_top_iff, ← hD.gen]
  refine iSup_le fun g => ?_
  have hirr : XMod.IsIrr ↥Λ (g • Vq) := v2c_isIrr_smul hD.toTwoTypeBase g
  rcases hD.types g with h | h
  · exact (v2c_le_copies hirr h).trans le_sup_left
  · exact (v2c_le_copies hirr h).trans le_sup_right

theorem v2c_copies_inf_eq_bot_tVq [Finite Q] (hD : TwoTypeBase Λ T₀ Vq t) :
    v2cCopies Λ Vq ⊓ v2cCopies Λ (t • Vq) = ⊥ :=
  v2c_copies_inf_eq_bot hD.noniso

theorem v2c_smul_copies_fix (hD : TwoTypeBase Λ T₀ Vq t) {s : Γ} (hs : s ∈ T₀)
    (h : s • Vq = Vq) :
    s • v2cCopies Λ Vq = v2cCopies Λ Vq ∧ s • v2cCopies Λ (t • Vq) = v2cCopies Λ (t • Vq) := by
  refine ⟨?_, ?_⟩
  · rw [v2c_smul_copies hD.normal, h]
  · rw [v2c_smul_copies hD.normal, v2c_fix_fix hD hs h]

theorem v2c_smul_copies_swap (hD : TwoTypeBase Λ T₀ Vq t) {s : Γ} (hs : s ∈ T₀)
    (h : s • Vq = t • Vq) :
    s • v2cCopies Λ Vq = v2cCopies Λ (t • Vq) ∧ s • v2cCopies Λ (t • Vq) = v2cCopies Λ Vq := by
  refine ⟨?_, ?_⟩
  · rw [v2c_smul_copies hD.normal, h]
  · rw [v2c_smul_copies hD.normal, v2c_swap hD hs h]

theorem v2c_second_copy (hD : TwoType Λ T₀ Vq t)
    (hnot : ∃ g : Γ, ¬ g • Vq ≤ Vq ⊔ t • Vq) :
    ∃ S₀ : Subgroup Q, XMod.IsIrr ↥Λ S₀ ∧ XMod.Iso ↥Λ S₀ Vq ∧ Vq ⊓ S₀ = ⊥ ∧
      ¬ S₀ ≤ Vq ⊔ t • Vq := by
  have hB := hD.toTwoTypeBase
  obtain ⟨g, hg⟩ := hnot
  obtain ⟨g', hiso, hg'⟩ : ∃ g' : Γ, XMod.Iso ↥Λ (g' • Vq) Vq ∧ ¬ g' • Vq ≤ Vq ⊔ t • Vq := by
    rcases hD.types g with h | h
    · exact ⟨g, h, hg⟩
    · refine ⟨t⁻¹ * g, ?_, ?_⟩
      · have := XMod.iso_smul (v2c_normalizes hB) t⁻¹ h
        rwa [inv_smul_smul, ← mul_smul] at this
      · intro hle
        apply hg
        have h1 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t)).2 hle
        rw [← mul_smul, mul_inv_cancel_left, v2c_smul_X hB] at h1
        exact h1
  have hirr : XMod.IsIrr ↥Λ (g' • Vq) := v2c_isIrr_smul hB g'
  refine ⟨g' • Vq, hirr, hiso, ?_, hg'⟩
  rcases v2c_inf_eq_bot_or_le hD.irr hirr.1 with h | h
  · exact h
  · exfalso
    rcases hirr.2.2 Vq hD.irr.1 bot_le h with h0 | h1
    · exact hD.irr.2.1.ne' h0
    · exact hg' (h1.symm.le.trans le_sup_left)

theorem two_type_struct [Finite Γ] [Finite Q] {Λ T₀ : Subgroup Γ} {Vq : Subgroup Q} {t : Γ}
    (hD : TwoType Λ T₀ Vq t) (hnot : ∃ g : Γ, ¬ g • Vq ≤ Vq ⊔ t • Vq)
    (h3 : ¬ ThreeCopies Λ Vq) :
    ∃ S₀ : Subgroup Q, XMod.IsIrr ↥Λ S₀ ∧ XMod.Iso ↥Λ S₀ Vq ∧ Vq ⊓ S₀ = ⊥ ∧
      (Vq ⊔ S₀) ⊔ t • (Vq ⊔ S₀) = ⊤ ∧ (Vq ⊔ S₀) ⊓ t • (Vq ⊔ S₀) = ⊥ ∧
      (∀ R : Subgroup Q, XMod.IsIrr ↥Λ R → XMod.Iso ↥Λ R Vq → R ≤ Vq ⊔ S₀) := by
  obtain ⟨S₀, hS₀, hiso, hdisj, -⟩ := v2c_second_copy hD hnot
  have hall : ∀ R : Subgroup Q, XMod.IsIrr ↥Λ R → XMod.Iso ↥Λ R Vq → R ≤ Vq ⊔ S₀ := by
    intro R hR hRiso
    rcases v2c_inf_eq_bot_or_le hR (hD.irr.1.sup hS₀.1) with h | h
    · exact (h3 ⟨S₀, R, hS₀, hR, hiso, hRiso, hdisj, by rw [inf_comm]; exact h⟩).elim
    · exact h
  have hQ0 : v2cCopies Λ Vq = Vq ⊔ S₀ := by
    apply le_antisymm
    · exact iSup_le fun R => hall R.1 R.2.1 R.2.2
    · exact sup_le (v2c_le_copies hD.irr (XMod.Iso.refl Vq)) (v2c_le_copies hS₀ hiso)
  have hQ1 : v2cCopies Λ (t • Vq) = t • (Vq ⊔ S₀) := by
    rw [← hQ0, v2c_smul_copies hD.normal]
  refine ⟨S₀, hS₀, hiso, hdisj, ?_, ?_, hall⟩
  · have := v2c_copies_sup_eq_top hD
    rwa [hQ1, hQ0] at this
  · have := v2c_copies_inf_eq_bot_tVq hD.toTwoTypeBase
    rwa [hQ1, hQ0] at this

end TwoTypeLemmas

end CFSG.Quasithin.Z391
