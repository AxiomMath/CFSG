module

public import CFSG.Quasithin.H13.A5V1367b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

local notation "StSL" => Assembly.LowTwoRank.StatedSL

variable {V : Type} [CommGroup V] [Finite V]

theorem not_case124_of_two_components {J N N' : Subgroup (MulAut V)} (hN : IsComponentOf N J)
    (hN' : IsComponentOf N' J) (hne : N ≠ N') :
    ¬ B56Case1 J ∧ ¬ B56Case2 J ∧ ¬ B56Case4 J := by
  have hq := B1Red.isQuasisimple_of_open hN.2.2
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h4 => ?_⟩
  · obtain ⟨hqF, -, -⟩ := h1
    have hFJ : quasithinGenFitting J ≤ J := quasithinGenFitting_le J
    have hFsub : IsSubnormal (quasithinGenFitting J) J :=
      IsSubnormal.step hFJ ((Subgroup.normal_subgroupOf_iff_le_normalizer hFJ).2
        (le_normalizer_quasithinGenFitting J)) (IsSubnormal.refl J)
    have key : ∀ {M : Subgroup (MulAut V)}, IsComponentOf M J → M = quasithinGenFitting J :=
      fun {M} hM => by
        have hqM := B1Red.isQuasisimple_of_open hM.2.2
        have hMF : M ≤ quasithinGenFitting J := by
          rcases B113.component_le_or_commutator_eq_bot hM hFsub with h | h
          · exact h
          · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
            exact (le_inf hM.1 h).trans (centralizer_quasithinGenFitting_le J)
        exact eq_of_subnormal_qs (A3.subnormal_of_le_of_le hM.2.1 hMF hFJ) hqM hqF
    exact hne ((key hN).trans (key hN').symm)
  · obtain ⟨⟨e⟩, -, -⟩ := h2
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact not_qs_of_le_solvable hN.1
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hq
  · obtain ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, h3, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
    have hMJ : G₁ ⊔ G₂ ≤ J := hJt ▸ le_sup_left
    have hs : IsSimpleGroup ↥G₁ :=
      @MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) e₁
    have hcard : Nat.card ↥G₁ = 360 := by
      rw [Nat.card_congr e₁.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hqG : CFSG.IsQuasisimple ↥G₁ :=
      S153L.comp_quasisimple_of_simple hs (by rw [hcard]; norm_num)
    have key : ∀ {M : Subgroup (MulAut V)}, IsComponentOf M J → M = G₁ := fun {M} hM => by
      have hqM := B1Red.isQuasisimple_of_open hM.2.2
      obtain ⟨hp, -⟩ := qs_perfect_ne_bot hqM
      have hMM : M ≤ G₁ ⊔ G₂ := by
        rw [← hp]
        exact (Subgroup.commutator_mono hM.1 hM.1).trans
          (commutator_le_of_zpowers hJt (mem_normalizer_sup ht₁ ht₂))
      rcases le_or_le_of_component rfl hc (isComponentOf_of_le hM hMM hMJ) with h | h
      · exact eq_of_subnormal_qs (A3.subnormal_of_le_of_le hM.2.1 h (le_sup_left.trans hMJ))
          hqM hqG
      · exfalso
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have : IsCyclic ↥G₂ := isCyclic_of_prime_card h3
        exact not_qs_of_le_solvable h inferInstance hqM
    exact hne ((key hN).trans (key hN').symm)

omit [Finite V] in
theorem inf_centralizer_eq {J A B N : Subgroup (MulAut V)} (hsup : A ⊔ B = J)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hNA : N ≤ A)
    (hAN : A ⊓ Subgroup.centralizer (N : Set (MulAut V)) = ⊥) :
    J ⊓ Subgroup.centralizer (N : Set (MulAut V)) = B := by
  apply le_antisymm
  · rintro x ⟨hx, hxN⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul hc (hsup ▸ hx)
    have haN : a ∈ A ⊓ Subgroup.centralizer (N : Set (MulAut V)) := by
      refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxN m hm
      have h2 := hc m (hNA hm) b hb
      have h3 : m * a * b = a * m * b := by
        calc m * a * b = m * (a * b) := by group
          _ = a * b * m := h1
          _ = a * (b * m) := by group
          _ = a * (m * b) := by rw [h2]
          _ = a * m * b := by group
      exact mul_right_cancel h3
    rw [hAN, Subgroup.mem_bot] at haN
    rw [haN, one_mul]
    exact hb
  · intro b hb
    refine ⟨hsup ▸ Subgroup.mem_sup_right hb, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
    exact hc m (hNA hm) b hb

omit [Finite V] in
theorem false_of_injective_four {G₁ : Subgroup (MulAut V)} {F : Type} [Field F] [CharP F 2]
    (e : ↥G₁ ≃* ↥(StSL 2 F)) {X : Type} [Group X] {π : X →* ↥G₁} (hπ : Function.Injective π)
    {x : X} (hx : orderOf x = 4) : False :=
  orderOf_ne_four_of_equiv e (π x) (by rw [orderOf_injective π hπ]; exact hx)

omit [Finite V] in
theorem piece_natural {G₁ : Subgroup (MulAut V)} {W C : Subgroup V} {F : Type} [Field F]
    [CharP F 2] (e : ↥G₁ ≃* ↥(StSL 2 F)) (hp : B56Piece G₁ W C) :
    W = commV G₁ ⊔ C ∧ ∀ g ∈ G₁, ∀ w ∈ W, w ∉ C → g w * w⁻¹ ∈ C → g * g = 1 := by
  rcases hp with ⟨hW, ⟨k, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩⟩ |
    ⟨-, m, K, _, _, hK, I, π, -, -, -, hreal⟩ | ⟨⟨e₃⟩, -⟩
  · have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    exact ⟨hW, fun g hg w hw hwC hfix => mul_self_eq_one_of_fix_natural hπ hg hw hwC hfix⟩
  · exact (false_of_injective_four e (FFC.injective_of_faithful_sec (FFC.symDn_faithful le_rfl) hπ)
      orderOf_cycle4).elim
  · have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := K)
    exact (false_of_injective_four e
      (FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ) hγ).elim
  · have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
    obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := K)
    exact (false_of_injective_four e
      (FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0)) hγ).elim
  · obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := ZMod 2)
    exact (false_of_injective_four e (π := e₃.symm.toMonoidHom) e₃.symm.injective hγ).elim

theorem case3_core {J G₁ G₂ A B N N' : Subgroup (MulAut V)} {WA WB : Subgroup V}
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥G₁ ≃* ↥(StSL 2 F)) (hsup : G₁ ⊔ G₂ = J) (hinf : G₁ ⊓ G₂ = ⊥)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hNG : N = G₁) (hN : IsComponentOf N J)
    (hN' : IsComponentOf N' J)
    (hAB : A ⊔ B = J) (hABi : A ⊓ B = ⊥) (hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hfA : B56FactorList ↥A) (hfB : B56FactorList ↥B) (hNA : N ≤ A) (hN'B : N' ≤ B)
    (hIA : XMod.IsInv ↥J WA) (hIB : XMod.IsInv ↥J WB)
    (hWsup : WA ⊔ WB = ⊤) (hWinf : WA ⊓ WB = fixV J) (hpA : B56Piece A WA (fixV J))
    (hpB : B56Piece B WB (fixV J)) :
    ∃ W₁ W₂ : Subgroup V, W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV J ∧ (∀ g ∈ J, ∀ w ∈ W₁, g w ∈ W₁) ∧
      (∀ g ∈ J, ∀ w ∈ W₂, g w ∈ W₂) ∧ W₁ = commV G₁ ⊔ fixV J ∧ commV G₂ ≤ W₂ ∧
      (∀ g ∈ G₁, ∀ w ∈ W₁, w ∉ fixV J → g w * w⁻¹ ∈ fixV J → g * g = 1) ∧
      G₂ ⊓ Subgroup.centralizer (N' : Set (MulAut V)) = ⊥ := by
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
  subst hNG
  have hAJ : A ≤ J := hAB ▸ le_sup_left
  have hNJ : N ≤ J := hsup ▸ le_sup_left
  have hNA' : IsComponentOf N A := isComponentOf_of_le hN hNA hAJ
  obtain ⟨hCA, -⟩ := factor_kind hfA hNA'
  have hCN : N ⊓ Subgroup.centralizer (N : Set (MulAut V)) = ⊥ := by
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hs : IsSimpleGroup ↥N :=
      @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4) e
    exact (centralizer_eq_bot_of_simple hs (isComponentOf_of_le hN le_rfl hNJ)).2
  have hB : J ⊓ Subgroup.centralizer (N : Set (MulAut V)) = B :=
    inf_centralizer_eq hAB hcAB hNA hCA
  have hG₂ : J ⊓ Subgroup.centralizer (N : Set (MulAut V)) = G₂ :=
    inf_centralizer_eq hsup hc le_rfl hCN
  have hBG : B = G₂ := hB.symm.trans hG₂
  subst hBG
  have hcard : Nat.card ↥A = Nat.card ↥N := by
    have h1 := card_sup_eq_mul_of_commute hABi hcAB
    have h2 := card_sup_eq_mul_of_commute hinf hc
    rw [hAB] at h1
    rw [hsup, h1] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hAN : N = A := Subgroup.eq_of_le_of_card_ge hNA hcard.le
  subst hAN
  obtain ⟨hW, hN1⟩ := piece_natural e hpA
  have hBJ : B ≤ J := hsup ▸ le_sup_right
  obtain ⟨hCB, -⟩ := factor_kind hfB (isComponentOf_of_le hN' hN'B hBJ)
  exact ⟨WA, WB, hWsup, hWinf, fun g hg w hw => hIA ⟨g, hg⟩ w hw,
    fun g hg w hw => hIB ⟨g, hg⟩ w hw, hW, G64.B56Piece.commV_le hpB, hN1, hCB⟩

theorem swap_case3 {J G₁ G₂ N N' : Subgroup (MulAut V)}
    (h : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J)
    (hsup : G₁ ⊔ G₂ = J) (hinf : G₁ ⊓ G₂ = ⊥) (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hN : IsComponentOf N J) (hN' : IsComponentOf N' J) (hne : N ≠ N') (hNG : N ≤ G₁)
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥G₁ ≃* ↥(StSL 2 F)) (e' : ↥N' ≃* ↥N) :
    ∃ W₁ W₂ : Subgroup V, W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV J ∧ (∀ g ∈ J, ∀ w ∈ W₁, g w ∈ W₁) ∧
      (∀ g ∈ J, ∀ w ∈ W₂, g w ∈ W₂) ∧ W₁ = commV G₁ ⊔ fixV J ∧ commV G₂ ≤ W₂ ∧
      (∀ g ∈ G₁, ∀ w ∈ W₁, w ∉ fixV J → g w * w⁻¹ ∈ fixV J → g * g = 1) ∧
      G₂ ⊓ Subgroup.centralizer (N' : Set (MulAut V)) = ⊥ := by
  have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
  have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hs : IsSimpleGroup ↥G₁ :=
    @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo h4) e
  have hNeq : N = G₁ := (centralizer_eq_bot_of_simple hs (isComponentOf_of_le hN hNG hG₁J)).1
  have eN : ↥N ≃* ↥(StSL 2 F) := (MulEquiv.subgroupCongr hNeq).trans e
  obtain ⟨h1, h2, h4'⟩ := not_case124_of_two_components hN hN' hne
  rcases h with h1' | h2' | h3 | h4'' | h5
  · exact absurd h1' h1
  · exact absurd h2' h2
  · obtain ⟨A, B, hAB, hABi, hcAB, hfA, hfB, WA, WB, -, -, hIA, hIB, hWsup, hWinf, hpA, hpB⟩ :=
      h3
    have hAJ : A ≤ J := hAB ▸ le_sup_left
    have hBJ : B ≤ J := hAB ▸ le_sup_right
    rcases le_or_le_of_component hAB hcAB hN with hNA | hNB
    · have hN'B : N' ≤ B := by
        rcases le_or_le_of_component hAB hcAB hN' with h' | h'
        · exact (hne (eq_of_components_le_factor hfA (isComponentOf_of_le hN hNA hAJ)
            (isComponentOf_of_le hN' h' hAJ))).elim
        · exact h'
      exact case3_core hn hF e hsup hinf hc hNeq hN hN' hAB hABi hcAB hfA hfB hNA hN'B hIA hIB
        hWsup hWinf hpA hpB
    · have hN'A : N' ≤ A := by
        rcases le_or_le_of_component hAB hcAB hN' with h' | h'
        · exact h'
        · exact (hne (eq_of_components_le_factor hfB (isComponentOf_of_le hN hNB hBJ)
            (isComponentOf_of_le hN' h' hBJ))).elim
      exact case3_core hn hF e hsup hinf hc hNeq hN hN' (by rw [sup_comm]; exact hAB)
        (by rw [inf_comm]; exact hABi) (fun a ha b hb => (hcAB b hb a ha).symm) hfB hfA hNB hN'A
        hIB hIA (by rw [sup_comm]; exact hWsup) (by rw [inf_comm]; exact hWinf) hpB hpA
  · exact absurd h4'' h4'
  · obtain ⟨A, B, hAB, hABi, hcAB, -, ⟨eA⟩, -, -, hB⟩ := h5
    have hAJ : A ≤ J := hAB ▸ le_sup_left
    have hsA : IsSimpleGroup ↥A :=
      @MulEquiv.isSimpleGroup _ _ _ _
        (NQRigid.isSimpleGroup_statedSL_three_odd (F := ZMod 2) (m := 1) (by simp) odd_one) eA
    obtain ⟨γ, hγ⟩ := exists_orderOf_four_statedSL3 (K := ZMod 2)
    have hfB : B56FactorList ↥B := by
      rcases hB with ⟨⟨e₂⟩, -⟩ | ⟨k, K, _, _, hK, π, hπ⟩
      · exact factorList_of_sl3_two e₂
      · have hi := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
        let e₂ := MulEquiv.ofBijective π ⟨hi, hπ.1⟩
        exact Or.inl ⟨k, K, inferInstance, inferInstance, two_le_of_field hK, hK, ⟨e₂.symm⟩⟩
    rcases le_or_le_of_component hAB hcAB hN with hNA | hNB
    · have hNA' : N = A := (centralizer_eq_bot_of_simple hsA (isComponentOf_of_le hN hNA hAJ)).1
      exact (false_of_injective_four eN
        (π := (eA.symm.trans (MulEquiv.subgroupCongr hNA'.symm)).toMonoidHom)
        (MulEquiv.injective _) hγ).elim
    · rcases le_or_le_of_component hAB hcAB hN' with hN'A | hN'B
      · have hN'A' : N' = A :=
          (centralizer_eq_bot_of_simple hsA (isComponentOf_of_le hN' hN'A hAJ)).1
        exact (false_of_injective_four eN
          (π := ((eA.symm.trans (MulEquiv.subgroupCongr hN'A'.symm)).trans e').toMonoidHom)
          (MulEquiv.injective _) hγ).elim
      · have hBJ : B ≤ J := hAB ▸ le_sup_right
        exact (hne (eq_of_components_le_factor hfB (isComponentOf_of_le hN hNB hBJ)
          (isComponentOf_of_le hN' hN'B hBJ))).elim

end CFSG.Quasithin.H13.A5
