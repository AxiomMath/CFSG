module

public import CFSG.Quasithin.EmptyFaithful.E22NParam
public import CFSG.Quasithin.Vol2.Ch11SecBE111Main

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def E111CoreMultiQn (Q : GrpPred) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G),
    ASInputs.E111Hyp G n → SecAll G Q →
    (∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G → ASInputs.E111Hyp G' n →
      SecAll G' Q → E1.InE n (⊤ : Subgroup G')) →
    E111Reduced G X T → ¬ IsSimpleGroup ↥X → E1.InEFor n ⊤ T

@[expose] def E111CoreMultiQ (Q : GrpPred) : Prop := ∀ n : ℕ, 1 ≤ n → E111CoreMultiQn Q n

@[expose] def E111CoreMultiK : Prop := E111CoreMultiQ TypeK

@[expose] def E111CoreMultiOne : Prop := E111CoreMultiQn (fun X _ => TypeOne X) 1

theorem inE_of_e111Hyp_Q {Q : GrpPred} (hQ : IsoInv Q) {n : ℕ} (hn : 1 ≤ n)
    (hMulti : E111CoreMultiQn Q n) :
    ∀ (k : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ k → ASInputs.E111Hyp G n →
      SecAll G Q → E1.InE n (⊤ : Subgroup G) := by
  intro k
  induction k with
  | zero =>
    intro G _ _ h _
    exact absurd h (by have := Nat.card_pos (α := G); omega)
  | succ k ih =>
    intro G _ _ hk hH hK
    have hIH : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G →
        ASInputs.E111Hyp G' n → SecAll G' Q → E1.InE n (⊤ : Subgroup G') :=
      fun G' _ _ hlt hH' hK' => ih G' (by omega) hH' hK'
    by_cases hsub : Subsingleton G
    · refine E1.inE_of_odd ?_
      rw [Subgroup.card_top, Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩]
      exact odd_one
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsec := (e111Hyp_iff_secAll n).mp hH
    intro T hT
    have hquot : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → (∀ Ω : Set (Subgroup G),
        E1.IsInvColl ⊤ Ω → N ≤ E1.eGen n ⊤ T Ω ⊔
          (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G))) → E1.InEFor n ⊤ T := by
      intro N hN hN1 hNM
      have : N.Normal := hN
      have hlt : Nat.card (G ⧸ N) < Nat.card G := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN1
        have h3 := Nat.card_pos (α := G ⧸ N)
        nlinarith
      have hHq : ASInputs.E111Hyp (G ⧸ N) n :=
        (e111Hyp_iff_secAll n).mpr (secAll_quotient (isoInv_e111Prop n) N hsec)
      exact E1.inEFor_of_quotient (hIH _ hlt hHq (secAll_quotient hQ N hK)) hT hNM
    have hTM : ∀ Ω : Set (Subgroup G), E1.IsInvColl ⊤ Ω → T ≤ E1.eGen n ⊤ T Ω ⊔
        (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) := fun Ω hΩ x hx =>
      Subgroup.mem_sup_right ⟨Subgroup.mem_top x, E1.le_normalizer_weakClosure hΩ hx⟩
    by_cases hsol : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
        (∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N) ∧ Group.IsSolvable ↥N
    ·
      obtain ⟨N, hN, hN1, hmin, hNs⟩ := hsol
      have : N.Normal := hN
      have : CFSG.IsMinimalNormal N := ⟨fun K hK hKN => hmin K hK hKN⟩
      obtain ⟨r, hr, hEA⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
      have hNp : IsPGroup r N := CFSG.IsElementaryAbelian.isPGroup r N
      refine hquot N hN hN1 fun Ω hΩ => ?_
      by_cases hr2 : r = 2
      · subst hr2
        exact (hT.le_of_normal le_top (Subgroup.normal_subgroupOf) hNp).trans (hTM Ω hΩ)
      · exact E1.normal_pGroup_le hr hr2 hT hNp hΩ
          ((E1.eGen_mono hn ⊤ T Ω).trans le_sup_left)
          (fun x hx => Subgroup.mem_sup_right ⟨Subgroup.mem_top x, hx⟩)
    obtain ⟨N, hN, -, hN1, hNmin⟩ := CFSG.exists_minimal_normal_le (⊤ : Subgroup G) inferInstance
      (bot_ne_top : (⊥ : Subgroup G) ≠ ⊤).symm
    have : N.Normal := hN
    have hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N := fun K hK hKN => by
      by_cases hK1 : K = ⊥
      · exact Or.inl hK1
      · exact Or.inr (hNmin K hK hKN hK1)
    have hNns : ¬ Group.IsSolvable ↥N := fun h => hsol ⟨N, hN, hN1, hmin, h⟩
    have hnab : ∃ a b : ↥N, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      exact hNns (Group.isSolvable_of_comm hc)
    by_cases hNT : N ⊔ T = ⊤
    ·
      have hC : Subgroup.centralizer (N : Set G) = ⊥ := by
        by_contra hC1
        have hCn : (Subgroup.centralizer (N : Set G)).Normal := inferInstance
        obtain ⟨N', hN', hN'C, hN'1, hN'min⟩ := CFSG.exists_minimal_normal_le _ hCn hC1
        have hmin' : ∀ K : Subgroup G, K.Normal → K ≤ N' → K = ⊥ ∨ K = N' := fun K hK hKN => by
          by_cases hK1 : K = ⊥
          · exact Or.inl hK1
          · exact Or.inr (hN'min K hK hKN hK1)
        have : N'.Normal := hN'
        have hinf : N' ⊓ N = ⊥ := by
          rcases hmin (N' ⊓ N) inferInstance inf_le_right with h | h
          · exact h
          · exfalso
            apply hNns
            refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
            have hb : (b : G) ∈ N' := (h ▸ inf_le_left : N ≤ N') b.2
            exact (Subgroup.mem_centralizer_iff.mp (hN'C hb) a a.2)
        have hN'2 : IsPGroup 2 ↥N' := by
          intro x
          obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hT.2.1 (x : G) (hNT ▸ Subgroup.mem_top _)
          refine ⟨e, Subtype.ext ?_⟩
          have hxe : (x : G) ^ 2 ^ e ∈ N' ⊓ N := ⟨N'.pow_mem x.2 _, he⟩
          rw [hinf, Subgroup.mem_bot] at hxe
          simpa using hxe
        have := hN'2.isNilpotent
        exact hsol ⟨N', hN', hN'1, hmin', inferInstance⟩
      have hR : E111Reduced G N T := ⟨hN, hN1, hmin, hnab, hC, hT, hNT⟩
      by_cases hNs : IsSimpleGroup ↥N
      · exact inEFor_of_reduced_simple hn hR hNs hH
      · exact hMulti G N T hH hK hIH hR hNs
    ·
      refine hquot N hN hN1 fun Ω hΩ => ?_
      set Y := N ⊔ T with hY
      have hYlt : Nat.card ↥Y < Nat.card G :=
        lt_of_le_of_ne (Subgroup.card_le_card_group Y)
          fun h => hNT ((Subgroup.card_eq_iff_eq_top Y).mp h)
      have hHY : ASInputs.E111Hyp ↥Y n :=
        (e111Hyp_iff_secAll n).mpr (secAll_sup_of_normal (isoInv_e111Prop n) hT.2.1 hsec)
      have hInEY : E1.InE n Y := (E1.inE_subgroupOf n Y).mpr
        (hIH _ hYlt hHY (secAll_sup_of_normal hQ hT.2.1 hK))
      have hTY : IsSylowIn 2 T Y := by
        refine ⟨le_sup_right, hT.2.1, fun h2 => hT.2.2 ?_⟩
        have := Subgroup.relIndex_mul_relIndex T Y ⊤ le_sup_right le_top
        rw [← this]
        exact Dvd.dvd.mul_right h2 _
      exact le_sup_left.trans (le_of_inEFor_sub hT le_sup_right (hInEY T hTY) hΩ)

theorem e111ForQn_of_core {Q : GrpPred} (hQ : IsoInv Q) {n : ℕ} (hn : 1 ≤ n)
    (hMulti : E111CoreMultiQn Q n) : E111ForQn Q n := by
  intro G _ _ hH hK
  have h := inE_of_e111Hyp_Q hQ hn hMulti (Nat.card G) G le_rfl hH hK
  rw [E1.nParam_le_iff (by omega)]
  exact h

theorem e111ForQ_of_core {Q : GrpPred} (hQ : IsoInv Q) (hMulti : E111CoreMultiQ Q) :
    E111ForQ Q :=
  fun n hn => e111ForQn_of_core hQ hn (hMulti n hn)

theorem e111ForK_of_core (hMulti : E111CoreMultiK) : E111ForK :=
  e111ForQ_of_core typeK_isoInv hMulti

theorem e111CoreMultiQn_of_e111 (Q : GrpPred) {n : ℕ} (hn : 1 ≤ n) (h : ASInputs.AS_E_1_11) :
    E111CoreMultiQn Q n := by
  intro G _ _ X T hH _ _ hR _
  exact (E1.nParam_le_iff (by omega)).mp (h G n hn hH) T hR.2.2.2.2.2.1

theorem e111CoreMultiQ_of_e111 (Q : GrpPred) (h : ASInputs.AS_E_1_11) : E111CoreMultiQ Q :=
  fun _ hn => e111CoreMultiQn_of_e111 Q hn h

theorem e111CoreMultiK_of_e111 (h : ASInputs.AS_E_1_11) : E111CoreMultiK :=
  e111CoreMultiQ_of_e111 TypeK h

theorem e111ForOne_of_core (hMulti : E111CoreMultiOne) :
    E111ForQn (fun X _ => TypeOne X) 1 :=
  e111ForQn_of_core typeOne_isoInv le_rfl hMulti

theorem e111CoreMultiOne_of_e111 (h : ASInputs.AS_E_1_11) : E111CoreMultiOne :=
  e111CoreMultiQn_of_e111 _ le_rfl h

end CFSG.Quasithin.E2.E22N
