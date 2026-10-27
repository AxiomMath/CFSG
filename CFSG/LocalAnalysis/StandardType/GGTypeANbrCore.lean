module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrArith
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrGate
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrRowFilter
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open TableB

variable {G : Type} [Group G] [Finite G]

private theorem two_le_of_dvd_two_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : p ∣ 2 ^ f - 1) : 2 ≤ f := by
  by_contra hf2
  have : f = 1 := by omega
  subst this
  norm_num at h
  exact hp.ne_one h

theorem ggTypeANbr_core (hCD : GGTypeACompatDiagBInput) (hRig : GGLabelRigidInput)
    (hTB : GGNbrTableBWeylInput) (hC : GGNbrTableBCardInput) (hO : GGNbrTableBOrderRestInput)
    (hF : GGNbrFrameInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {y : G} {K : Subgroup G} (h : GGTypeANbrCfg p B Bs x L D J n f y K)
    (hTP : GGNbrTablePConfig p B Bs x L D J) {y' : G} {K' : Subgroup G}
    (hK' : GGNbr p B x D J y' K') {m : ℕ} (hm : n ≤ m ∧ m ≤ n + 1)
    (hgate : GGWeylOfType p (CoxeterMatrix.A m) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs)) :
    m = n + 1 ∧ StatedClassicalModel (K' ⧸ Subgroup.center K') .PSL (n + 1) 2 f := by
  obtain ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc, hdiag⟩ := hCD G p B Bs x L D J n f y K h
  have hCtx := ggFarCtx_of_cfg h hL hk₁ hK hk₂ hc hdiag
  have hcfg : GGConfig p B Bs x L D J := h.1
  have hInn : GGInnerDiagAll p B Bs x L D J := h.2.2.1
  have hInnK' : GGInnerDiagOn Bs K' := hInn.2 y' K' hK'
  have hp : p.Prime := h.prime
  have hp2 : p ≠ 2 := hCtx.odd
  have hpf : p ∣ 2 ^ f - 1 := h.dvd_two_pow_sub_one
  have hn : 3 ≤ n := h.three_le
  have hf : 2 ≤ f := two_le_of_dvd_two_pow_sub_one hp h.one_le_f hpf
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hBsAb, -, -, -⟩ := hcfg.tableB_facts
  have hcard𝒜 : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K' Bs) = (m + 1).factorial :=
    ggWeylOfType_A_card hgate
  have hKA : ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K' Bs := le_sup_right
  have hdvd : Nat.card ↥(ggAutomizer K' Bs) ∣ (n + 2).factorial := by
    have h1 : Nat.card ↥(ggAutomizer K' Bs) ∣
        Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K' Bs) :=
      Subgroup.card_dvd_of_le hKA
    rw [hcard𝒜] at h1
    exact h1.trans (Nat.factorial_dvd_factorial (by omega))
  have hnotle : ¬ ggAutomizer L Bs ≤ ggAutomizer K' Bs :=
    hCtx.not_automizer_le hcfg hL h.mem_zpowers_x_of_comm_L rfl hK'
  have hsq : ¬ (m + 1).factorial ∣ Nat.card ↥(ggAutomizer K' Bs) := by
    intro hd
    apply hnotle
    rw [← hcard𝒜] at hd
    have heq : ggAutomizer K' Bs = ggAutomizer L Bs ⊔ ggAutomizer K' Bs :=
      Subgroup.eq_of_le_of_card_ge hKA (Nat.le_of_dvd Nat.card_pos hd)
    rw [heq]
    exact le_sup_left
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
    refine ⟨?_, statedClassicalModel_of_hasLabel_typeA hΛA hhasA⟩
    by_contra hmn
    apply hsq
    have : m = n := by omega
    rw [this]
    exact hcardA n hΛA hhasA
  ·
    subst hX
    exact (hsq ((Nat.factorial_dvd_factorial (by omega)).trans (hcardA (n + 1) hΛK' hhasK'))).elim
  ·
    subst hX
    exact (not_dvd_two_pow_mul_factorial_C hn
      ((hcardO ⟨.C, n, f⟩ _ rfl trivial hΛK' hhasK' (Or.inl ⟨rfl, rfl⟩)).trans hdvd)).elim
  ·
    subst hX
    exact (not_dvd_two_pow_mul_factorial_D h4
      ((hcardO ⟨.D, n, f⟩ _ rfl trivial hΛK' hhasK'
        (Or.inr (Or.inl ⟨rfl, rfl⟩))).trans hdvd)).elim
  ·
    subst hX
    subst h6
    exact (not_dvd_E.1 ((hcardO ⟨.E6, 0, f⟩ _ rfl trivial hΛK' hhasK'
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))).trans hdvd)).elim
  ·
    subst hX
    subst h7
    exact (not_dvd_E.2.1 ((hcardO ⟨.E7, 0, f⟩ _ rfl trivial hΛK' hhasK'
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))).trans hdvd)).elim
  ·
    subst hX
    subst h8
    exact (not_dvd_E.2.2.1 ((hcardO ⟨.E8, 0, f⟩ _ rfl trivial hΛK' hhasK'
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))).trans hdvd)).elim
  ·
    subst hX
    subst h9
    exact (not_dvd_E.2.2.2 ((hcardO ⟨.E8, 0, f⟩ _ rfl trivial hΛK' hhasK'
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
    subst hX
    subst hp7
    subst h3
    obtain ⟨c, hc, h9⟩ := ggNbr_exists_order_nine hRig hcfg hK' hInnK' hΛK' hhasK' (hF.2)
    exact (ggWeylOfType_A_no_order_nine (by omega) hgate (hKA hc) h9).elim

end CFSG.StandardType

end
