module

public import CFSG.Quasithin.Recognition.WBN.Statement
public import CFSG.Quasithin.Recognition.WBN.Weyl
public import CFSG.Quasithin.Recognition.F112IdentW
public import CFSG.Quasithin.Recognition.Stroth.IdSzL2W
import CFSG.Quasithin.Recognition.WBN.L3
import CFSG.Quasithin.Recognition.WBN.Sp4
import CFSG.Quasithin.Recognition.WBN.G2
import CFSG.Quasithin.Recognition.WBN.D4
import CFSG.Quasithin.Recognition.WBN.U4Ext
import CFSG.Quasithin.Recognition.WBN.F4
import CFSG.Quasithin.Vol2.GoldschmidtF112TD
import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Quasithin.WBN

private theorem bigB_le_sup {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S :=
  sup_le (sup_le ((F1.borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
    ((F1.borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right

private theorem sup_bigB_le {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S) ≤ L1 ⊔ L2 ⊔ S := by
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact le_sup_left.trans le_sup_left
  · exact bigB_le_sup L1 L2 S
  · exact le_sup_right.trans le_sup_left
  · exact bigB_le_sup L1 L2 S

private theorem le_bigB_comm {G : Type} [Group G] {L1 L2 S E : Subgroup G}
    (hE : E ≤ bigB L1 L2 S) : E ≤ bigB L2 L1 S := by
  rwa [bigB_comm]

private theorem bigB_le_both {G : Type} [Group G] (L1 L2 S : Subgroup G) :
    bigB L1 L2 S ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) :=
  le_inf le_sup_right le_sup_right

private theorem exists_inv_swap {G : Type} [Group G] {L1 L2 S E : Subgroup G}
    (h : ∃ w ∈ L2 ⊔ L1 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹) :
    ∃ w ∈ L1 ⊔ L2 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹ := by
  obtain ⟨w, hw, hinv⟩ := h
  exact ⟨w, by rwa [← sup_comm L1 L2] at hw, hinv⟩

private theorem exists_inv_of_iso_amalgam {G : Type} [Group G] {L1 L2 S : Subgroup G}
    {P : ∀ (Y : Type) [Group Y], Prop} {m : ℕ}
    (hA : IsAmalgamOfGroup (F112R.f112Amalgam L1 L2 S) P) (hW : AllInvertsByWeyl P m)
    {E : Subgroup G} (hE : E ≤ bigB L1 L2 S) (hm : ∀ e ∈ E, e ^ m = 1) :
    ∃ w ∈ L1 ⊔ L2 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹ := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨Φ⟩⟩ := hA
  have hE' : E ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) :=
    hE.trans (bigB_le_both L1 L2 S)
  obtain ⟨w, hw, hinv⟩ := (hW Y hY T M₁ M₂ hpair).exists_inv_of_iso Φ hE' hm
  exact ⟨w, sup_bigB_le L1 L2 S hw, hinv⟩

theorem exists_inv_of_isAmalgamOfGroup {G : Type} [Group G] {L1 L2 S : Subgroup G}
    {P : ∀ (Y : Type) [Group Y], Prop} {m : ℕ}
    (hA : CFSG.Quasithin.IsAmalgamOfGroup (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S) P)
    (hW : AllInvertsByWeyl P m) {E : Subgroup G} (hE : E ≤ CFSG.Quasithin.bigB L1 L2 S)
    (hm : ∀ e ∈ E, e ^ m = 1) :
    ∃ w ∈ L1 ⊔ L2 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹ :=
  exists_inv_of_iso_amalgam hA hW hE hm

theorem exists_inv_of_isU4ExtTwo {G : Type} [Group G] {L1 L2 S : Subgroup G} {f : ℕ}
    (hf : 2 ≤ f) (hA : CFSG.Quasithin.IsU4ExtTwo f (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S))
    {E : Subgroup G} (hE : E ≤ CFSG.Quasithin.bigB L1 L2 S)
    (hm : ∀ e ∈ E, e ^ (2 ^ f - 1) = 1) :
    ∃ w ∈ L1 ⊔ L2 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹ := by
  obtain ⟨Y, _, Ŷ, _, ι, hY, hι, hidx, T, M₁, M₂, hpair, ⟨Φ⟩⟩ := hA
  have hE' : E ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) :=
    hE.trans (bigB_le_both L1 L2 S)
  obtain ⟨w, hw, hinv⟩ :=
    (invertsByWeyl_u4ExtTwo hf hY ι hι hidx hpair).exists_inv_of_iso Φ hE' hm
  exact ⟨w, sup_bigB_le L1 L2 S hw, hinv⟩

private theorem wbn_inversion_a5a5
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hH : Hyp111 L1 L2 S) (hW : F112HypW L1 L2 S) (hA : F112R.IdA5A5W)
    (h1 : IsL2Quot 2 (oTwoQuot ↥L1)) (h2 : IsL2Quot 2 (oTwoQuot ↥L2)) :
    (∀ E : Subgroup G, E ≤ bigB L1 L2 S →
        (∀ e ∈ E, e ^ (2 ^ 2 - 1) = 1 ∧ e ^ (2 ^ 2 - 1) = 1) →
        ∃ w ∈ L1 ⊔ L2 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹) ∨
      CFSG.Open.pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
        Subgroup.centralizer (L1 : Set G) = ⊥ := by
  rcases hA G L1 L2 S hW h1 h2 with h3 | hSp | hG2
  · exact Or.inr (pCoreOf_inf_centralizer_eq_bot_of_psl3 hH le_rfl h1 h2 h3)
  · refine Or.inl ?_
    intro E hE hmE
    exact exists_inv_of_isAmalgamOfGroup hSp
      (allInvertsByWeyl_sp4 le_rfl
        (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := 2) (by norm_num)))
      hE (fun e he => (hmE e he).1)
  · refine Or.inl ?_
    intro E hE hmE
    exact exists_inv_of_isAmalgamOfGroup hG2
      (allInvertsByWeyl_g2 le_rfl
        (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := 2) (by norm_num)))
      hE (fun e he => (hmE e he).1)

private theorem wbn_inversion_l2l2_gen
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f1 f2 : ℕ}
    (hL : F112R.IdL2L2GenW) (hH : Hyp111 L1 L2 S) (hW : F112HypW L1 L2 S)
    (hf1 : 2 ≤ f1) (hf2 : 2 ≤ f2) (h22 : ¬ (f1 = 2 ∧ f2 = 2))
    (h1 : IsL2Quot f1 (oTwoQuot ↥L1)) (h2 : IsL2Quot f2 (oTwoQuot ↥L2)) :
    (∀ E : Subgroup G, E ≤ bigB L1 L2 S →
        (∀ e ∈ E, e ^ (2 ^ f1 - 1) = 1 ∧ e ^ (2 ^ f2 - 1) = 1) →
        ∃ w ∈ L1 ⊔ L2 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹) ∨
      CFSG.Open.pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
        Subgroup.centralizer (L1 : Set G) = ⊥ := by
  rcases hL G L1 L2 S f1 f2 hW hf1 hf2 h22 h1 h2 with
    ⟨hff, hrest⟩ | ⟨h3f, hD4⟩ | ⟨h3f, hD4⟩ | ⟨h2f, hU4⟩ | ⟨h2f, hU4⟩
  · subst f1
    rcases hrest with h3 | hSp | hG2
    · exact Or.inr (pCoreOf_inf_centralizer_eq_bot_of_psl3 hH hf2 h1 h2 h3)
    · refine Or.inl ?_
      intro E hE hmE
      exact exists_inv_of_isAmalgamOfGroup hSp
        (allInvertsByWeyl_sp4 hf2
          (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := f2) (by omega)))
        hE (fun e he => (hmE e he).1)
    · refine Or.inl ?_
      intro E hE hmE
      exact exists_inv_of_isAmalgamOfGroup hG2
        (allInvertsByWeyl_g2 hf2
          (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := f2) (by omega)))
        hE (fun e he => (hmE e he).1)
  · refine Or.inl ?_
    intro E hE hmE
    exact exists_inv_of_isAmalgamOfGroup hD4
      (allInvertsByWeyl_d4 (by omega : 1 ≤ f2)
        (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := f2) (by omega)))
      hE (fun e he => (hmE e he).2)
  · refine Or.inl ?_
    intro E hE hmE
    exact exists_inv_swap (exists_inv_of_isAmalgamOfGroup hD4
      (allInvertsByWeyl_d4 (by omega : 1 ≤ f1)
        (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := f1) (by omega)))
      (le_bigB_comm hE) (fun e he => (hmE e he).1))
  · rcases hU4 with hU4 | hU4E
    · refine Or.inl ?_
      intro E hE hmE
      exact exists_inv_of_isAmalgamOfGroup hU4 (allInvertsByWeyl_u4 hf1) hE
        (fun e he => (hmE e he).1)
    · refine Or.inl ?_
      intro E hE hmE
      exact exists_inv_of_isU4ExtTwo hf1 hU4E hE (fun e he => (hmE e he).1)
  · rcases hU4 with hU4 | hU4E
    · refine Or.inl ?_
      intro E hE hmE
      exact exists_inv_swap (exists_inv_of_isAmalgamOfGroup hU4
        (allInvertsByWeyl_u4 hf2) (le_bigB_comm hE) (fun e he => (hmE e he).2))
    · refine Or.inl ?_
      intro E hE hmE
      exact exists_inv_swap (exists_inv_of_isU4ExtTwo hf2 hU4E (le_bigB_comm hE)
        (fun e he => (hmE e he).2))

private theorem wbn_inversion_sz
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f2 a : ℕ}
    (hS : Stroth.IdSzL2W) (hW : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* ↥(CFSG.Open.Sz a)))
    (hf2 : 2 ≤ f2) (h2 : IsL2Quot f2 (oTwoQuot ↥L2)) :
    (∀ E : Subgroup G, E ≤ bigB L1 L2 S →
        (∀ e ∈ E, e ^ (2 ^ (2 * a + 1) - 1) = 1 ∧ e ^ (2 ^ f2 - 1) = 1) →
        ∃ w ∈ L1 ⊔ L2 ⊔ S, ∀ e ∈ E, w * e * w⁻¹ = e⁻¹) ∨
      CFSG.Open.pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ⊓
        Subgroup.centralizer (L1 : Set G) = ⊥ := by
  obtain ⟨-, hF4⟩ := hS G L1 L2 S a hW ha hSz
    (vBig_of_isL2Quot hf2 h2) ⟨f2, h2⟩
  refine Or.inl ?_
  intro E hE hmE
  exact exists_inv_of_isAmalgamOfGroup hF4
    (allInvertsByWeyl_twistedF4 ha
      (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (a := 2 * a + 1) (by omega)))
    hE (fun e he => (hmE e he).1)

theorem wbnInversionL2_of_ident
    (hL : CFSG.Quasithin.F112R.IdL2L2GenW) (hA : CFSG.Quasithin.F112R.IdA5A5W)
    (hS : CFSG.Quasithin.Stroth.IdSzL2W) : WBNInversionL2 := by
  intro G₀ _ _ L₁ L₂ S f₁ f₂ hH hN hf₁ h₁ hf₂ h₂
  have hW : F112HypW L₁ L₂ S := ⟨hH, Or.inr hN⟩
  rcases h₁ with h1Q | ⟨a, rfl, hSz⟩
  · by_cases h22 : f₁ = 2 ∧ f₂ = 2
    · obtain ⟨hf1eq, hf2eq⟩ := h22
      subst f₁
      subst f₂
      exact wbn_inversion_a5a5 hH hW hA h1Q h₂
    · exact wbn_inversion_l2l2_gen hL hH hW hf₁ hf₂ h22 h1Q h₂
  · exact wbn_inversion_sz hS hW (by omega) hSz hf₂ h₂

end CFSG.Quasithin.WBN
