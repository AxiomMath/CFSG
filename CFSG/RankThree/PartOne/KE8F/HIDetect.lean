module

public import CFSG.RankThree.PartOne.KE8F.HICharpoly
public import CFSG.RankThree.PartOne.KE8F.HIRootFacts
public import CFSG.RankThree.PartOne.KE8F.E8Kernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Count

theorem exists_unique_of_count_eq_one {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β)
    (v : β) (h : Multiset.count v (Multiset.map g Finset.univ.val) = 1) :
    ∃ l, ∀ l', g l' = v ↔ l' = l := by
  rw [Multiset.count_map] at h
  have h' : (Finset.univ.filter (fun a => v = g a)).card = 1 := by
    rw [Finset.card_def, Finset.filter_val]
    exact h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h'
  refine ⟨a, fun l' => ?_⟩
  have := Finset.ext_iff.1 ha l'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at this
  rw [eq_comm]
  exact this

theorem count_eq_one_of_unique {α β : Type*} [Fintype α] [DecidableEq β] (g : α → β) (v : β)
    (l : α) (h : ∀ l', g l' = v ↔ l' = l) :
    Multiset.count v (Multiset.map g Finset.univ.val) = 1 := by
  rw [Multiset.count_map]
  have : Finset.univ.filter (fun a => v = g a) = {l} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [eq_comm, h a]
  rw [← Finset.filter_val, ← Finset.card_def, this]
  rfl

end Count

section Eigen

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem evLabel_pairGauss {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ}
    (hpq : p ∣ q * q + 1) {ζ : Lˣ} (hζ : ζ ^ p = 1)
    (γ : {v : Fin Tag.E8.rank → ℤ // IsRoot .E8 v}) :
    evLabel (pairGauss q 0 1 ζ 1) (Sum.inr γ) = ((ζ ^ gE q γ.1 0 : Lˣ) : L) := by
  have h := rootChar_pairGauss hFr hpq (show (0 : Fin 4) ≠ 1 by decide) hζ (one_pow p) γ.1
  rw [_root_.one_zpow, mul_one] at h
  exact congrArg (fun u : Lˣ => (u : L)) h

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem zpow_eq_zpow_iff_dvd {ζ : Lˣ} {p : ℕ} (hζ : orderOf ζ = p) (e e' : ℤ) :
    ζ ^ e = ζ ^ e' ↔ (p : ℤ) ∣ e - e' := by
  rw [← hζ, orderOf_dvd_iff_zpow_eq_one, _root_.zpow_sub, mul_inv_eq_one]

theorem eq_two_of_dvd {p : ℕ} (hp16 : 16 < p) {q : ℕ} (hpq : (p : ℤ) ∣ (q : ℤ) * q + 1)
    {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot .E8 γ) (h : (p : ℤ) ∣ gE q γ 0 - 2) :
    gA γ 0 = 2 ∧ gB γ 0 = 0 := by
  rcases rootFact_two hγ with h2 | ⟨h1, h4⟩
  · exact h2
  · exfalso
    unfold gE at h
    have hid : (gA γ 0 - 2) ^ 2 + (gB γ 0) ^ 2 =
        (gA γ 0 + (q : ℤ) * gB γ 0 - 2) * (gA γ 0 - 2 - (q : ℤ) * gB γ 0) +
          ((q : ℤ) * q + 1) * (gB γ 0 * gB γ 0) := by ring
    have hdvd : (p : ℤ) ∣ (gA γ 0 - 2) ^ 2 + (gB γ 0) ^ 2 := by
      rw [hid]
      exact dvd_add (Dvd.dvd.mul_right h _) (Dvd.dvd.mul_right hpq _)
    have := Int.le_of_dvd (by omega) hdvd
    have hp16' : (16 : ℤ) < p := by exact_mod_cast hp16
    omega

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem val_pow_zpow_natCast (ζ : Lˣ) (e : ℤ) (n : ℕ) :
    (((ζ ^ e : Lˣ) : L)) ^ n = ((ζ ^ (e * (n : ℤ)) : Lˣ) : L) := by
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul]

theorem arith_contra {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (w : F) (hw : w ^ 4 + 1 = 0)
    (h : (2 * w = 2) ∨ (-2 * w = 2) ∨ (2 * (w * w) * w = 2) ∨ (-2 * (w * w) * w = 2)) :
    False := by
  have h22 : (2 : F) = 0 := by
    rcases h with h | h | h | h
    · have h1 : w = 1 := mul_left_cancel₀ h2 (by rw [h]; ring)
      rw [h1] at hw
      linear_combination hw
    · have h1 : w = -1 := mul_left_cancel₀ h2 (by linear_combination -h)
      rw [h1] at hw
      linear_combination hw
    · have h3 : w ^ 3 = 1 := mul_left_cancel₀ h2 (by linear_combination h)
      have h4 : w = -1 := by linear_combination hw - w * h3 + 0 * h3
      rw [h4] at h3
      linear_combination -h3
    · have h3 : w ^ 3 = -1 := mul_left_cancel₀ h2 (by linear_combination -h)
      have h4 : w = 1 := by linear_combination -hw + w * h3 + 0 * h3
      rw [h4] at h3
      linear_combination h3
  exact h2 h22

omit [IsAlgClosed L] in
theorem not_stable {Fr : L →+* L} {q q₀ : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq : q = q₀ * q₀)
    {p : ℕ} (hp : p.Prime) (hp16 : 16 < p) (hpq : p ∣ q * q + 1) {ζ : Lˣ} (hζ : orderOf ζ = p)
    (hstable : Multiset.map (fun l => (evLabel (pairGauss q 0 1 ζ 1) l) ^ q₀) Finset.univ.val =
      Multiset.map (evLabel (pairGauss q 0 1 ζ 1)) Finset.univ.val) : False := by
  classical
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hpq' : (p : ℤ) ∣ (q : ℤ) * q + 1 := by exact_mod_cast hpq
  have hev := evLabel_pairGauss (Fr := Fr) hFr hpq hζp
  set b := pairGauss q 0 1 ζ 1 with hb
  set v : L := ((ζ ^ (2 : ℤ) : Lˣ) : L) with hv
  have hv1 : v ≠ 1 := by
    intro h
    have h1 : ζ ^ (2 : ℤ) = 1 := Units.ext h
    have h2 : (p : ℤ) ∣ 2 := by
      have := (zpow_eq_zpow_iff_dvd hζ 2 0).1 (by rw [h1, _root_.zpow_zero])
      simpa using this
    have h3 : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
    have h4 : (16 : ℤ) < p := by exact_mod_cast hp16
    omega
  obtain ⟨γ₂, hγ₂, hγ₂a, hγ₂b⟩ := rootFact_exists
  have hB : Multiset.count v (Multiset.map (evLabel b) Finset.univ.val) = 1 := by
    refine count_eq_one_of_unique _ v (Sum.inr ⟨γ₂, hγ₂⟩) fun l' => ?_
    rcases l' with i | γ
    · simp [evLabel, hv1.symm]
    · rw [hev γ]
      constructor
      · intro h
        have h1 : ζ ^ gE q γ.1 0 = ζ ^ (2 : ℤ) := Units.ext h
        have h2 := (zpow_eq_zpow_iff_dvd hζ _ _).1 h1
        obtain ⟨ha, hb'⟩ := eq_two_of_dvd hp16 hpq' γ.2 h2
        have := rootFact_unique γ.2 hγ₂ ha hb' hγ₂a hγ₂b
        exact congrArg Sum.inr (Subtype.ext this)
      · intro h
        have hγ : γ.1 = γ₂ := congrArg Subtype.val (Sum.inr.inj h)
        have : gE q γ.1 0 = 2 := by simp [gE, hγ, hγ₂a, hγ₂b]
        rw [this]
  have hC : Multiset.count v
      (Multiset.map (fun l => (evLabel b l) ^ q₀) Finset.univ.val) = 1 := by
    rw [hstable]
    exact hB
  obtain ⟨l₂, hl₂⟩ := exists_unique_of_count_eq_one _ v hC
  have hl₂v : (evLabel b l₂) ^ q₀ = v := (hl₂ l₂).2 rfl
  rcases l₂ with i | γ₃
  · exfalso
    simp [evLabel] at hl₂v
    exact hv1 hl₂v.symm
  · rw [hev γ₃, val_pow_zpow_natCast] at hl₂v
    have h1 : ζ ^ (gE q γ₃.1 0 * (q₀ : ℤ)) = ζ ^ (2 : ℤ) := Units.ext hl₂v
    have h2 := (zpow_eq_zpow_iff_dvd hζ _ _).1 h1
    rcases rootFact_fiber γ₃.2 with ⟨hn4, hz⟩ | ⟨γ₄, hγ₄, hne, hA, hB'⟩
    · have : Fact p.Prime := ⟨hp⟩
      have h2' : ((gE q γ₃.1 0 * (q₀ : ℤ) - 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h2
      have hqw : (q : ZMod p) = (q₀ : ZMod p) * (q₀ : ZMod p) := by rw [hq]; push_cast; rfl
      have hqq : (q : ZMod p) * q + 1 = 0 := by
        have := (ZMod.natCast_eq_zero_iff (q * q + 1) p).2 hpq
        push_cast at this
        exact this
      have hw4 : (q₀ : ZMod p) ^ 4 + 1 = 0 := by
        have : (q₀ : ZMod p) ^ 4 = (q : ZMod p) * q := by rw [hqw]; ring
        rw [this]
        exact hqq
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).1 h')
        omega
      have hE : gE q γ₃.1 0 = 2 ∨ gE q γ₃.1 0 = -2 ∨ gE q γ₃.1 0 = 2 * (q : ℤ) ∨
          gE q γ₃.1 0 = -2 * (q : ℤ) := by
        unfold gE
        rcases hz with ha | hb0
        · rw [ha] at hn4 ⊢
          have : gB γ₃.1 0 = 2 ∨ gB γ₃.1 0 = -2 := by
            have : (gB γ₃.1 0 - 2) * (gB γ₃.1 0 + 2) = 0 := by nlinarith
            rcases mul_eq_zero.1 this with h | h
            · left; linarith
            · right; linarith
          rcases this with h | h
          · right; right; left; rw [h]; ring
          · right; right; right; rw [h]; ring
        · rw [hb0] at hn4 ⊢
          have : gA γ₃.1 0 = 2 ∨ gA γ₃.1 0 = -2 := by
            have : (gA γ₃.1 0 - 2) * (gA γ₃.1 0 + 2) = 0 := by nlinarith
            rcases mul_eq_zero.1 this with h | h
            · left; linarith
            · right; linarith
          rcases this with h | h
          · left; rw [h]; ring
          · right; left; rw [h]; ring
      refine arith_contra h2ne (q₀ : ZMod p) hw4 ?_
      rcases hE with h | h | h | h
      · left
        rw [h] at h2'
        push_cast at h2'
        linear_combination h2'
      · right; left
        rw [h] at h2'
        push_cast at h2'
        linear_combination h2'
      · right; right; left
        rw [h] at h2'
        push_cast at h2'
        linear_combination h2' - 2 * (q₀ : ZMod p) * hqw
      · right; right; right
        rw [h] at h2'
        push_cast at h2'
        linear_combination h2' + 2 * (q₀ : ZMod p) * hqw
    · exfalso
      have := (hl₂ (Sum.inr ⟨γ₄, hγ₄⟩)).1 (by
        show (evLabel b (Sum.inr ⟨γ₄, hγ₄⟩)) ^ q₀ = v
        rw [hev ⟨γ₄, hγ₄⟩, val_pow_zpow_natCast]
        have : gE q γ₄ 0 = gE q γ₃.1 0 := by simp only [gE, hA, hB']
        rw [this]
        exact hl₂v)
      exact hne (congrArg Subtype.val (Sum.inr.inj this))

end Eigen

end CFSG.RankThree.PartOne.KE8F
