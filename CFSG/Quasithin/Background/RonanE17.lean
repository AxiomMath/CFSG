module

public import CFSG.Quasithin.EmptyFaithful.E111RMain
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin.RonanE17

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB CFSG.Quasithin.E2.E22N

section Stabilization

variable {G : Type*} [Group G] [Finite G]

theorem card_le_two_pow_twoRank {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ^ twoRank G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x.1 x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (CFSG.SectionRank.le_pRank one_lt_two le_top hA hk)

theorem card_map_subgroupOf_le {A : Subgroup G} (hA : IsElemAbelian 2 A) (K : Subgroup G)
    {Q : Type*} [Group Q] (f : ↥K →* Q) :
    Nat.card ((A.subgroupOf K).map f) ≤ 2 ^ twoRank G := by
  refine (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (A.subgroupOf K) f)).trans ?_
  refine le_trans ?_ (card_le_two_pow_twoRank hA)
  refine Nat.card_le_card_of_injective (fun x : ↥(A.subgroupOf K) => (⟨((x : ↥K) : G), x.2⟩ : ↥A))
    fun x y h => ?_
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

theorem isE_twoRank {i : ℕ} {H T A K : Subgroup G} (hA : IsElemAbelian 2 A)
    (h : E1.IsE i H T A K) : E1.IsE (twoRank G) H T A K := by
  obtain ⟨h1, h2, h3, h4 | h4⟩ := h
  · exact ⟨h1, h2, h3, Or.inl ⟨h4.1, card_map_subgroupOf_le hA K _⟩⟩
  · exact ⟨h1, h2, h3, Or.inr ⟨h4.1, card_map_subgroupOf_le hA K _⟩⟩

theorem eGen_le_eGen_twoRank {i : ℕ} {H T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) : E1.eGen i H T Ω ≤ E1.eGen (twoRank G) H T Ω := by
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  exact le_iSup₂_of_le A hA (le_iSup_of_le hAT
    (le_iSup₂_of_le K (isE_twoRank (hΩ.isElemAbelian A hA) hK) le_rfl))

theorem InEFor.twoRank {i : ℕ} {H T : Subgroup G} (h : E1.InEFor i H T) :
    E1.InEFor (CFSG.Open.twoRank G) H T := fun Ω hΩ =>
  le_antisymm (sup_le (E1.eGen_le _ H T Ω) inf_le_left)
    ((h Ω hΩ).symm.le.trans (sup_le_sup_right (eGen_le_eGen_twoRank hΩ) _))

theorem twoRank_pos (h : ¬ Odd (Nat.card G)) : 0 < twoRank G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h))
  have hel : IsElemAbelian 2 (Subgroup.zpowers x) := ⟨inferInstance, fun y hy =>
    orderOf_dvd_iff_pow_eq_one.mp (hx ▸ orderOf_dvd_of_mem_zpowers hy)⟩
  have hcard : Nat.card (Subgroup.zpowers x) = 2 ^ 1 := by rw [Nat.card_zpowers, hx, pow_one]
  exact CFSG.SectionRank.le_pRank one_lt_two le_top hel hcard

end Stabilization

theorem exists_involution_of_isSimpleGroup {J : Type*} [Group J] [Finite J] [IsSimpleGroup J]
    (h : ∃ a b : J, a * b ≠ b * a) : ∃ x : J, x ≠ 1 ∧ x ^ 2 = 1 := by
  have heven : Even (Nat.card J) := by
    by_contra hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
    obtain ⟨a, b, hab⟩ := h
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  refine ⟨x, fun h1 => ?_, hx ▸ pow_orderOf_eq_one x⟩
  rw [h1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem card_subgroup_mulAut_le {J : Type*} [Group J] [Finite J] (B : Subgroup (MulAut J)) :
    Nat.card B ≤ Nat.card J ^ Nat.card J := by
  have hinj : Function.Injective (fun φ : MulAut J => (φ : J → J)) :=
    fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite (MulAut J) := Finite.of_injective _ hinj
  calc Nat.card B ≤ Nat.card (MulAut J) := Subgroup.card_le_card_group B
    _ ≤ Nat.card (J → J) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card J ^ Nat.card J := Nat.card_fun

theorem secAll_autRankLe (G : Type) [Group G] [Finite G] :
    SecAll G (AutRankLe (Nat.card G ^ Nat.card G)) := by
  intro H₁ N _ _ hs hnab
  refine ⟨exists_involution_of_isSimpleGroup hnab, fun B _ => ?_⟩
  have hJ : Nat.card (↥H₁ ⧸ N) ≤ Nat.card G :=
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N)).trans
      (Subgroup.card_le_card_group H₁)
  have hJ0 : 0 < Nat.card G := Nat.card_pos
  calc Nat.card B ≤ Nat.card (↥H₁ ⧸ N) ^ Nat.card (↥H₁ ⧸ N) := card_subgroup_mulAut_le B
    _ ≤ Nat.card G ^ Nat.card (↥H₁ ⧸ N) := Nat.pow_le_pow_left hJ _
    _ ≤ Nat.card G ^ Nat.card G := Nat.pow_le_pow_right hJ0 hJ
    _ ≤ 2 ^ (Nat.card G ^ Nat.card G) := Nat.lt_two_pow_self.le

theorem inE_of_secAll_autRankLe {n : ℕ} (hn : 1 ≤ n) :
    ∀ (k : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ k →
      SecAll G (AutRankLe n) → E1.InE n (⊤ : Subgroup G) := by
  have hQ := autRankLe_isoInv n
  intro k
  induction k with
  | zero =>
    intro G _ _ h
    exact absurd h (by have := Nat.card_pos (α := G); omega)
  | succ k ih =>
    intro G _ _ hk hK
    have hIH : ∀ (G' : Type) [Group G'] [Finite G'], Nat.card G' < Nat.card G →
        SecAll G' (AutRankLe n) → E1.InE n (⊤ : Subgroup G') :=
      fun G' _ _ hlt hK' => ih G' (by omega) hK'
    by_cases hsub : Subsingleton G
    · refine E1.inE_of_odd ?_
      rw [Subgroup.card_top, Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩]
      exact odd_one
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
      exact E1.inEFor_of_quotient (hIH _ hlt (secAll_quotient hQ N hK)) hT hNM
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
      refine E111R.inEFor_of_reduced_autRankLe hR hn fun S hS => ?_
      have hsub : S.IsSubnormal :=
        Subgroup.IsSubnormal.trans hS.le hS.2.1.isSubnormal hR.1.isSubnormal
      have := hS.simple
      have hq : IsSimpleGroup (↥S ⧸ (⊥ : Subgroup ↥S)) :=
        (MulEquiv.isSimpleGroup_congr QuotientGroup.quotientBot).mpr this
      have hP := hK S ⊥ hsub hq (nonabelian_of_mulEquiv QuotientGroup.quotientBot hS.nonabelian)
      exact hQ _ _ QuotientGroup.quotientBot.symm hP
    ·
      refine hquot N hN hN1 fun Ω hΩ => ?_
      set Y := N ⊔ T with hY
      have hYlt : Nat.card ↥Y < Nat.card G :=
        lt_of_le_of_ne (Subgroup.card_le_card_group Y)
          fun h => hNT ((Subgroup.card_eq_iff_eq_top Y).mp h)
      have hInEY : E1.InE n Y := (E1.inE_subgroupOf n Y).mpr
        (hIH _ hYlt (secAll_sup_of_normal hQ hT.2.1 hK))
      have hTY : IsSylowIn 2 T Y := by
        refine ⟨le_sup_right, hT.2.1, fun h2 => hT.2.2 ?_⟩
        have := Subgroup.relIndex_mul_relIndex T Y ⊤ le_sup_right le_top
        rw [← this]
        exact Dvd.dvd.mul_right h2 _
      exact le_sup_left.trans (le_of_inEFor_sub hT le_sup_right (hInEY T hTY) hΩ)

theorem inE_top (G : Type) [Group G] [Finite G] :
    E1.InE (Nat.card G ^ Nat.card G) (⊤ : Subgroup G) :=
  inE_of_secAll_autRankLe (Nat.one_le_pow _ _ Nat.card_pos) (Nat.card G) G le_rfl
    (secAll_autRankLe G)

theorem nParam_top_le_twoRank (G : Type) [Group G] [Finite G] :
    E1.nParam (⊤ : Subgroup G) ≤ (twoRank G : ℕ∞) := by
  by_cases hodd : Odd (Nat.card G)
  · have h : Odd (Nat.card (⊤ : Subgroup G)) := by rwa [Subgroup.card_top]
    unfold E1.nParam
    rw [if_pos h]
    exact zero_le
  · rw [E1.nParam_le_iff (twoRank_pos hodd)]
    exact fun T hT => InEFor.twoRank (inE_top G T hT)

end CFSG.Quasithin.RonanE17
