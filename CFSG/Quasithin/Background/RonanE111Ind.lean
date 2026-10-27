module

public import CFSG.Quasithin.Background.RonanE111Sub
public import CFSG.Quasithin.Vol2.Ch11SecBE111Main

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def E111CoreT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G) (n : ℕ), 1 ≤ n → HypT n G T →
    E111Reduced G X T → E1.InEFor n ⊤ T

theorem inEFor_of_hypT (hcore : E111CoreT) {n : ℕ} (hn : 1 ≤ n) :
    ∀ (k : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ k → ∀ T : Subgroup G,
      IsSylowIn 2 T ⊤ → HypT n G T → E1.InEFor n ⊤ T := by
  intro k
  induction k with
  | zero =>
    intro G _ _ h
    exact absurd h (by have := Nat.card_pos (α := G); omega)
  | succ k ih =>
    intro G _ _ hk T hT hH
    have hIH : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G →
        ∀ T' : Subgroup G', IsSylowIn 2 T' ⊤ → HypT n G' T' → E1.InEFor n ⊤ T' :=
      fun G' _ _ hlt T' hT' hH' => ih G' (by omega) T' hT' hH'
    by_cases hsub : Subsingleton G
    · refine E1.inEFor_of_odd hT ?_
      rw [Subgroup.card_top, Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩]
      exact odd_one
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
      have hTb : IsSylowIn 2 (T.map (QuotientGroup.mk' N)) ⊤ :=
        E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective N) hT
      have hIHq := hIH _ hlt _ hTb (hH.quotient (N := N))
      exact E1.inEFor_of_quotient ((E1.inE_iff_inEFor hTb).mpr hIHq) hT hNM
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
      exact hcore G N T n hn hH hR
    ·
      refine hquot N hN hN1 fun Ω hΩ => ?_
      set Y := N ⊔ T with hY
      have hYlt : Nat.card ↥Y < Nat.card G :=
        lt_of_le_of_ne (Subgroup.card_le_card_group Y)
          fun h => hNT ((Subgroup.card_eq_iff_eq_top Y).mp h)
      have hTY : IsSylowIn 2 T Y := by
        refine ⟨le_sup_right, hT.2.1, fun h2 => hT.2.2 ?_⟩
        have := Subgroup.relIndex_mul_relIndex T Y ⊤ le_sup_right le_top
        rw [← this]
        exact Dvd.dvd.mul_right h2 _
      have hTY' : IsSylowIn 2 (T.subgroupOf Y) ⊤ := by
        rw [← E1.isSylowIn_map_of_injective Y.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le le_sup_right, Subgroup.map_top,
          Subgroup.range_subtype]
        exact hTY
      have hIHY := hIH ↥Y hYlt (T.subgroupOf Y) hTY' (hH.sup hT.2.1)
      have hInEY : E1.InEFor n Y T := by
        have := (E1.inEFor_map_subtype_iff n Y (T.subgroupOf Y)).mpr hIHY
        rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_right] at this
      exact le_sup_left.trans (le_of_inEFor_sub hT le_sup_right hInEY hΩ)

theorem nParam_le_of_hypT (hcore : E111CoreT) {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 1 ≤ n)
    {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hH : HypT n G T) :
    E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞) := by
  rw [E1.nParam_le_iff (by omega)]
  exact (E1.inE_iff_inEFor hT).mpr (inEFor_of_hypT hcore hn (Nat.card G) G le_rfl T hT hH)

end CFSG.Quasithin.RonanE111
