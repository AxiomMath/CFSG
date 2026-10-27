module

public import CFSG.Quasithin.Vol2.Ch11SecBE111Core
public import CFSG.Quasithin.Background.E1ElevenLift
public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin.A1b

theorem le_of_inEFor_sub {G : Type} [Group G] [Finite G] {i : ℕ} {Y T : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hTY : T ≤ Y) (hY : E1.InEFor i Y T) {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl ⊤ Ω) :
    Y ≤ E1.eGen i ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) := by
  set Ω' : Set (Subgroup G) := {B | B ∈ Ω ∧ B ≤ Y} with hΩ'def
  have hΩ' : E1.IsInvColl Y Ω' := by
    refine ⟨fun B hB => hB.2, fun B hB => hΩ.isElemAbelian B hB.1, fun B hB h hh => ?_⟩
    refine ⟨hΩ.conj B hB.1 h (Subgroup.mem_top h), fun x hx => ?_⟩
    rw [mem_conjSub_iff] at hx
    have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [e]
    exact Y.mul_mem (Y.mul_mem hh (hB.2 hx)) (Y.inv_mem hh)
  have hW : E1.weakClosure T Ω' = E1.weakClosure T Ω := by
    apply le_antisymm
    · exact iSup₂_le fun A hA => iSup_le fun hAT => E1.le_weakClosure hA.1 hAT
    · exact iSup₂_le fun A hA => iSup_le fun hAT =>
        E1.le_weakClosure ⟨hA, hAT.trans hTY⟩ hAT
  have hTY' : IsSylowIn 2 T Y := by
    refine ⟨hTY, hT.2.1, fun h2 => hT.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T Y ⊤ hTY le_top
    rw [← this]
    exact Dvd.dvd.mul_right h2 _
  rw [← hY Ω' hΩ', hW]
  refine sup_le_sup ?_ (inf_le_inf_right _ le_top)
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  have hTY'' : T ⊓ Y = T := inf_eq_left.mpr hTY
  have hK' : E1.IsE i Y (T ⊓ Y) A K := by rw [hTY'']; exact hK
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ Y := by
    rw [hTY'']
    exact fun t ht => ht.1
  have hS : IsSylowIn 2 (T ⊓ Y) Y := by rw [hTY'']; exact hTY'
  exact E1.le_eGen hA.1 hAT
    (E1.eight_two hT hAT (hΩ.isElemAbelian A hA.1) le_top hτ hS hK')

theorem inE_of_e111Hyp (hMulti : E111CoreMulti) {n : ℕ} (hn : 1 ≤ n) :
    ∀ (k : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ k → ASInputs.E111Hyp G n →
      E1.InE n (⊤ : Subgroup G) := by
  intro k
  induction k with
  | zero =>
    intro G _ _ h
    exact absurd h (by have := Nat.card_pos (α := G); omega)
  | succ k ih =>
    intro G _ _ hk hH
    have hIH : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G →
        ASInputs.E111Hyp G' n → E1.InE n (⊤ : Subgroup G') :=
      fun G' _ _ hlt hH' => ih G' (by omega) hH'
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
      exact E1.inEFor_of_quotient (hIH _ hlt hHq) hT hNM
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
      · exact hMulti G n N T hn hH hIH hR hNs
    ·
      refine hquot N hN hN1 fun Ω hΩ => ?_
      set Y := N ⊔ T with hY
      have hYlt : Nat.card ↥Y < Nat.card G :=
        lt_of_le_of_ne (Subgroup.card_le_card_group Y)
          fun h => hNT ((Subgroup.card_eq_iff_eq_top Y).mp h)
      have hHY : ASInputs.E111Hyp ↥Y n :=
        (e111Hyp_iff_secAll n).mpr (secAll_sup_of_normal (isoInv_e111Prop n) hT.2.1 hsec)
      have hInEY : E1.InE n Y := (E1.inE_subgroupOf n Y).mpr (hIH _ hYlt hHY)
      have hTY : IsSylowIn 2 T Y := by
        refine ⟨le_sup_right, hT.2.1, fun h2 => hT.2.2 ?_⟩
        have := Subgroup.relIndex_mul_relIndex T Y ⊤ le_sup_right le_top
        rw [← this]
        exact Dvd.dvd.mul_right h2 _
      exact le_sup_left.trans (le_of_inEFor_sub hT le_sup_right (hInEY T hTY) hΩ)

theorem AS_E_1_11_of_core (hMulti : E111CoreMulti) : ASInputs.AS_E_1_11 := by
  intro G _ _ n hn hH
  have h := inE_of_e111Hyp hMulti hn (Nat.card G) G le_rfl hH
  rw [E1.nParam_le_iff (by omega)]
  exact h

theorem e111CoreMulti_of_AS_E_1_11 (h : ASInputs.AS_E_1_11) : E111CoreMulti := by
  intro G _ _ n X T hn hH _ hR _
  exact (E1.nParam_le_iff (by omega)).mp (h G n hn hH) T hR.2.2.2.2.2.1

theorem AS_E_1_11_iff_core : ASInputs.AS_E_1_11 ↔ E111CoreMulti :=
  ⟨e111CoreMulti_of_AS_E_1_11, AS_E_1_11_of_core⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
