module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrRowFilter
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

section Arith

theorem succ_dvd_six_of_factorial_succ_dvd_six_mul_factorial {n : ℕ}
    (h : (n + 1).factorial ∣ 6 * n.factorial) : n + 1 ∣ 6 := by
  rw [Nat.factorial_succ] at h
  exact Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos n) h

theorem eq_five_of_factorial_succ_dvd_six_mul_factorial {n : ℕ} (hn : 3 ≤ n)
    (h : (n + 1).factorial ∣ 6 * n.factorial) : n = 5 := by
  have h1 : n + 1 ∣ 6 := succ_dvd_six_of_factorial_succ_dvd_six_mul_factorial h
  have h2 : n + 1 ≤ 6 := Nat.le_of_dvd (by norm_num) h1
  have h3 : n ≤ 5 := by omega
  interval_cases n
  · norm_num at h1
  · norm_num at h1
  · rfl

theorem not_factorial_add_two_dvd_six_mul_factorial {n : ℕ} (hn : 3 ≤ n) :
    ¬ (n + 2).factorial ∣ 6 * n.factorial := by
  intro h
  have h1 : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [h1] at h
  have h2 : (n + 2) * (n + 1) ∣ 6 :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos n) h
  have h3 : 6 < (n + 2) * (n + 1) := by
    calc 6 < 4 * 5 := by norm_num
      _ ≤ (n + 1) * (n + 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = (n + 2) * (n + 1) := Nat.mul_comm _ _
  have h4 : (n + 2) * (n + 1) ≤ 6 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_two_pow_mul_factorial_dvd_six_mul_factorial {n : ℕ} (hn : 3 ≤ n) :
    ¬ 2 ^ n * n.factorial ∣ 6 * n.factorial := by
  intro h
  have h2 : 2 ^ n ∣ 6 := Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos n) h
  have h3 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_two_pow_pred_mul_factorial_dvd_six_mul_factorial {n : ℕ} (hn : 4 ≤ n) :
    ¬ 2 ^ (n - 1) * n.factorial ∣ 6 * n.factorial := by
  intro h
  have h2 : 2 ^ (n - 1) ∣ 6 := Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos n) h
  have h3 : 8 ≤ 2 ^ (n - 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (n - 1) ≤ 6 := Nat.le_of_dvd (by norm_num) h2
  omega

theorem not_dvd_six_mul_factorial_E :
    ¬ 51840 ∣ 6 * (6 : ℕ).factorial ∧ ¬ 2903040 ∣ 6 * (7 : ℕ).factorial ∧
      ¬ 696729600 ∣ 6 * (8 : ℕ).factorial ∧ ¬ 696729600 ∣ 6 * (9 : ℕ).factorial := by
  decide

end Arith

theorem ggTypeANbr_false_of_card_dvd (hCD : GGTypeACompatDiagBInput)
    (hRig : GGLabelRigidInput) (hTB : GGNbrTableBWeylInput) (hC : GGNbrTableBCardInput)
    (hO : GGNbrTableBOrderRestInput) (hF : GGNbrFrameInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (h : GGTypeANbrCfg p B Bs x L D J n f y K) (hTP : GGNbrTablePConfig p B Bs x L D J)
    {y' : G} {K' : Subgroup G} (hK' : GGNbr p B x D J y' K') {m : ℕ}
    (hgate : GGWeylOfType p (CoxeterMatrix.A m) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs))
    (hp3 : p = 3) (hpn : p ∣ n + 3)
    (hdvd : Nat.card ↥(ggAutomizer K' Bs) ∣ 6 * n.factorial) : False := by
  obtain ⟨φ₁, -, -, hk₁, -, -, hJ, -, -⟩ := hCD G p B Bs x L D J n f y K h
  have hcfg : GGConfig p B Bs x L D J := h.1
  have hInn : GGInnerDiagAll p B Bs x L D J := h.2.2.1
  have hInnK' : GGInnerDiagOn Bs K' := hInn.2 y' K' hK'
  have hp : p.Prime := h.prime
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hpf : p ∣ 2 ^ f - 1 := h.dvd_two_pow_sub_one
  have hn : 3 ≤ n := h.three_le
  have hf : 2 ≤ f := by
    have hf0 : 1 ≤ f := h.one_le_f
    by_contra hf2
    have hf1 : f = 1 := by omega
    subst hf1
    norm_num at hpf
    exact hp.ne_one hpf
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hBsAb, -, -, -⟩ := hcfg.tableB_facts
  have hKA : ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K' Bs := le_sup_right
  have hsplit : ∀ t : LargeEvenLieTag, LargeEvenUntwisted t → ∀ (r : ℕ),
      GGNbrSplitLabel p ⟨t, r, f⟩ := fun t ht r => ⟨ht, hf, hpf⟩
  have hcardA : ∀ r : ℕ, LargeEvenInLambda2 ⟨.A, r, f⟩ →
      GGHasLabel ⟨.A, r, f⟩ (K' ⧸ Subgroup.center K') →
      (r + 1).factorial ∣ Nat.card ↥(ggAutomizer K' Bs) := fun r hΛ hhas =>
    ggNbr_card_dvd_of_label hRig hcfg hK' hInnK' hΛ hhas
      (hTB p hp hp2 _ hΛ (hsplit .A trivial r).halfSplit (hsplit .A trivial r))
      (ggNbrLabelAll_mono (fun _ _ _ _ ⟨r', hl, hcard⟩ => ⟨r', hl, hcard.toDvd⟩)
        (hC p hp hp2 r f hΛ hpf))
  have hcardO : ∀ (lab : LargeEvenLabel) (N : ℕ), lab.n = f → LargeEvenUntwisted lab.tag →
      LargeEvenInLambda2 lab → GGHasLabel lab (K' ⧸ Subgroup.center K') →
      GGTableBOrderRest lab N → N ∣ Nat.card ↥(ggAutomizer K' Bs) :=
    fun lab N hlf hu hΛ hhas hN =>
    have hs : GGNbrSplitLabel p lab := ⟨hu, hlf ▸ hf, hlf ▸ hpf⟩
    ggNbr_card_dvd_of_label hRig hcfg hK' hInnK' hΛ hhas
      (hTB p hp hp2 lab hΛ hs.halfSplit hs) (hO p hp hp2 lab N hΛ hs hN)
  have hframe : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (K' ⧸ Subgroup.center K') → GGFrameLabel p lab → False :=
    fun lab hΛ hhas hfl => by
      obtain ⟨c₁, hc₁, c₂, hc₂, r₁, r₂, h4⟩ :=
        ggNbr_exists_frame_pair hRig hcfg hK' hInnK' hΛ hhas (hF.1 p hp hp2 lab hΛ hfl)
      exact ggWeylOfType_A_no_frame hp2 hBsAb hgate (hKA hc₁) (hKA hc₂) r₁ r₂ h4
  have hlabJ := ggHasLabel_J_of_lift hn h.one_le_f hk₁ hJ
  have hΛJ : LargeEvenInLambda2 ⟨.A, n - 1, f⟩ :=
    ⟨by show 1 ≤ f; omega, by show 1 ≤ n - 1; omega, fun h1 => by omega⟩
  obtain ⟨labK, hΛK, hhasK, -⟩ := largeEvenMarking_exists_hasLabel hInnK'
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hhasJ', hhasK'⟩ :=
    hTP hcfg hInn y' K' hK' _ _ hΛJ hΛK hlabJ hhasK
  have hJ' : labJ' = ⟨.A, n - 1, f⟩ ∨ (n = 4 ∧ labJ' = ⟨.D, 3, f⟩) := by
    rcases ggLabelIso_typeA_cases hRig (r := n - 1) (by omega) hΛJ' hΛJ hhasJ' hlabJ with
      h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨by omega, h2⟩
  have hcls := ggTablePRow_typeA hp hp2 hn hf hpf hJ' hrow
  unfold GGTypeARowClass at hcls
  rcases hcls with hA | ⟨hX, -⟩ | hX | ⟨hX, h4⟩ | ⟨h6, hX⟩ | ⟨h7, hX⟩ | ⟨h8, -, hX⟩ |
    ⟨h9, -, hX⟩ | hX | ⟨htag, hrk, h2n, hdv⟩ | ⟨h3, htag, hrk, h2n, hdv⟩ | ⟨h3, hf3, hp7, hX⟩
  ·
    have hhasA : GGHasLabel ⟨.A, n, f⟩ (K' ⧸ Subgroup.center K') := by
      rcases hA with rfl | ⟨rfl, rfl⟩
      · exact hhasK'
      · exact hhasK'
    have hΛA : LargeEvenInLambda2 ⟨.A, n, f⟩ :=
      ⟨by show 1 ≤ f; omega, by show 1 ≤ n; omega, fun h1 => by omega⟩
    have hn5 : n = 5 :=
      eq_five_of_factorial_succ_dvd_six_mul_factorial hn ((hcardA n hΛA hhasA).trans hdvd)
    have h38 : 3 ∣ 8 := by simpa [hp3, hn5] using hpn
    norm_num at h38
  ·
    subst hX
    exact (not_factorial_add_two_dvd_six_mul_factorial hn
      ((hcardA (n + 1) hΛK' hhasK').trans hdvd)).elim
  ·
    subst hX
    exact (not_two_pow_mul_factorial_dvd_six_mul_factorial hn
      ((hcardO ⟨.C, n, f⟩ _ rfl trivial hΛK' hhasK' (Or.inl ⟨rfl, rfl⟩)).trans hdvd)).elim
  ·
    subst hX
    exact (not_two_pow_pred_mul_factorial_dvd_six_mul_factorial h4
      ((hcardO ⟨.D, n, f⟩ _ rfl trivial hΛK' hhasK'
        (Or.inr (Or.inl ⟨rfl, rfl⟩))).trans hdvd)).elim
  ·
    subst hX
    subst h6
    exact (not_dvd_six_mul_factorial_E.1
      ((hcardO ⟨.E6, 0, f⟩ _ rfl trivial hΛK' hhasK'
        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))).trans hdvd)).elim
  ·
    subst hX
    subst h7
    exact (not_dvd_six_mul_factorial_E.2.1
      ((hcardO ⟨.E7, 0, f⟩ _ rfl trivial hΛK' hhasK'
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))).trans hdvd)).elim
  ·
    subst hX
    subst h8
    exact (not_dvd_six_mul_factorial_E.2.2.1
      ((hcardO ⟨.E8, 0, f⟩ _ rfl trivial hΛK' hhasK'
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))).trans hdvd)).elim
  ·
    subst hX
    subst h9
    exact (not_dvd_six_mul_factorial_E.2.2.2
      ((hcardO ⟨.E8, 0, f⟩ _ rfl trivial hΛK' hhasK'
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))).trans hdvd)).elim
  ·
    subst hX
    exact (hframe _ hΛK' hhasK' (Or.inl ⟨rfl, by show 4 ≤ n + 1; omega, hpf⟩)).elim
  ·
    exact (hframe _ hΛK' hhasK'
      (Or.inr (Or.inl ⟨htag, by rcases hrk with h1 | h1 <;> omega, hdv⟩))).elim
  ·
    exact (hframe _ hΛK' hhasK' (Or.inr (Or.inr ⟨htag, hrk, hdv⟩))).elim
  ·
    omega

end CFSG.StandardType

end
