module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5f

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.G3

@[expose] def Rank2NoSL25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), IsRank2LieChar2 ↥L →
    IsMaxParabolic2 L P → ¬ IsSL25Group ↥(perfectCore P)

theorem noSL25Norm_sub {G : Type} [Group G] [Finite G] {L T B : Subgroup G}
    (h : NoSL25Norm ↥L) (hT : IsSylowTwoOf T L) (hBL : B ≤ L)
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) : ¬ IsSL25Group ↥B := by
  intro hD
  have hT' : IsSylowTwoOf (T.subgroupOf L) (⊤ : Subgroup ↥L) := isSylowTwoOf_top_subgroupOf hT
  have hD' : IsSL25Group ↥(B.subgroupOf L) :=
    hD.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  exact h _ _ hT' (subgroupOf_le_normalizer hTB) hD'

theorem not_isAlt_five_of_sl25 {X : Type} [Group X] [Finite X] (hD : IsSL25Group X)
    (h : IsAlt 5 X) : False := by
  have h1 := A314.card_isAlt_five h
  have h2 := hD.card
  omega

theorem not_extraspecial_of_sl25 {B : Type} [Group B] [Finite B] (hD : IsSL25Group B)
    (V : Subgroup B) [V.Normal] (hV : IsExtraspecial2 2 ↥V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hV.1
  have hV2 : IsPGroup 2 ↥V := CFSG.IsExtraspecial.isPGroup 2 ↥V
  have hle : V ≤ CFSG.pCore 2 B := le_sSup ⟨inferInstance, hV2⟩
  have hVc : Nat.card ↥V = 32 := by rw [hV.2]; norm_num
  have heq : V = CFSG.pCore 2 B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hD.card_pCore, hVc])
  have hcen : Subgroup.center ↥V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hD.comm _ (heq ▸ y.2) _ (heq ▸ x.2)
  have h2 := CFSG.IsExtraspecial.center_order_p 2 ↥V
  rw [hcen, Subgroup.card_top, hVc] at h2
  omega

theorem not_ext_e16_a5_of_sl25 {X : Type} [Group X] [Finite X] (hD : IsSL25Group X)
    (h : IsExt X (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) : False := by
  obtain ⟨V, hVn, hV, hY⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [card_of_isElemAbelianOfRank hV, A314.card_isAlt_five hY, hD.card] at h1
  omega

theorem not_a312Case_of_sl25 {G : Type} [Group G] [Finite G] {T B L : Subgroup G}
    (hM : A314ModelFacts) (hR2 : Rank2NoSL25)
    (hJ4 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .J4 X → NoSL25Norm X)
    (hD : IsSL25Group ↥B) (hTL : IsSylowTwoOf T L) (hBL : B ≤ L)
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) (hcase : A312Case B L) : False := by
  have hA : IsAlt 5 (↥B ⧸ CFSG.solvableRadical ↥B) := hD.isAlt_modRadical
  have hcard := hD.card
  have hPV4 : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → Group.IsSolvable V :=
    fun V _ _ h => A314.solvable_isE2 4 V h
  unfold A312Case at hcase
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨-, hrk, P, hP, hBP⟩ := h
    subst hBP
    exact hR2 G L P hrk hP hD
  ·
    obtain ⟨f, hf, -⟩ := h
    exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hf⟩))))) hA
  ·
    obtain ⟨hB3, -⟩ := h
    exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _) (Or.inl hB3) hA
  ·
    obtain ⟨hB4, -⟩ := h
    exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
      (Or.inr (Or.inl hB4)) hA
  ·
    obtain ⟨hB5 | hB3, -⟩ := h
    · exact not_isAlt_five_of_sl25 hD hB5
    · exact A314.excl_model_self hM (Or.inl hB3) hA
  ·
    rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
    · exact A314.excl_alt_self (by norm_num) (by norm_num) hB hA
    · exact A314.excl_hat_self hB A314.hS_alt_six hA
  ·
    rcases h with ⟨p, hp, hp3, hBp, -⟩ | ⟨hB5, -⟩
    · obtain ⟨hs, hna, -⟩ := hM.2.2 p hp hp3 ↥B hBp
      exact not_isAlt_five_of_sl25 hD (A314.isAlt_of_simple hs hna hA)
    · exact not_isAlt_five_of_sl25 hD hB5
  ·
    rcases h with ⟨s, p, hp, hp3, hBp, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · have hp5 : p = 5 := by
        let e : ↥B ⧸ (⊥ : Subgroup ↥B) ≃* ↥B := QuotientGroup.quotientBot
        exact A314.p_eq_five_of_sl2 (V := ⊥)
          (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _) hp hp3
          (IsSL2.of_mulEquiv e.symm hBp) hA
      subst hp5
      have := card_isSL2_five hBp
      omega
    · exact A314.excl_alt_self (by norm_num) (by norm_num) hB hA
    · exact A314.excl_hat_self hB A314.hS_alt_six hA
  ·
    obtain ⟨p, hp, hp3, hBext, -⟩ := h
    have hp5 : p = 5 := by
      obtain ⟨V, hVn, hV, hY⟩ := hBext
      exact A314.p_eq_five_of_sl2 (A314.solvable_of_isElemAbelianOfRank hV) hp hp3 hY hA
    subst hp5
    obtain ⟨V, hVn, hV, hY⟩ := hBext
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [card_of_isElemAbelianOfRank hV, card_isSL2_five hY, hcard] at h1
    omega
  ·
    exact A314.excl_alt_self (by norm_num) (by norm_num) h.1 hA
  ·
    rcases h with ⟨hB | hB, -⟩ | ⟨hB | hB, -⟩
    · exact not_ext_e16_a5_of_sl25 hD hB
    · exact A314.excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) hA
    · exact not_ext_e16_a5_of_sl25 hD hB
    · exact A314.excl_hat_ext hB hPV4 (fun Y _ hY => hY) A314.hS_alt_six hA
  ·
    have hPV3 : ∀ (V : Type) [Group V] [Finite V], IsE2 3 V → Group.IsSolvable V :=
      fun V _ _ h => A314.solvable_isE2 3 V h
    obtain ⟨hB | hB | hB | hB | hB | hB | hB, -⟩ := h
    · exact A314.excl_model_self hM (Or.inr (Or.inr (Or.inr (Or.inl hB)))) hA
    · exact A314.excl_model_self hM (Or.inr (Or.inr (Or.inl hB))) hA
    · exact A314.excl_alt_ext (n := 7) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) hA
    · exact A314.excl_model_ext hM hB hPV4 (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_model_ext hM hB hPV3 (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) hA
    · exact not_ext_e16_a5_of_sl25 hD hB
  ·
    obtain ⟨hB | hB | hB | hB, -⟩ := h
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_isE2 4 V h)
        (fun Y _ hY => Or.inr (Or.inl hY)) hA
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_isE2 6 V h)
        (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_of_isExtraspecial2 h)
        (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_hat_ext hB (fun V _ _ h => A314.solvable_isE2 6 V h) (fun Y _ hY => hY)
        A314.hS_alt_six hA
  ·
    exact not_isAlt_five_of_sl25 hD h.1
  ·
    obtain ⟨⟨V, hVn, hV, -⟩, -⟩ := h
    exact not_extraspecial_of_sl25 hD V hV
  ·
    obtain ⟨hL, hB | hB | hB | hB | hB | hB⟩ := h
    · exact A314.excl_hat_ext hB (fun V _ _ h => A314.solvable_of_isExtraspecial2 h)
        (fun Y _ hY => hY) (A314.hS_m22 hM) hA
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_isE2 11 V h)
        (fun Y _ hY => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hY))))) hA
    · exact noSL25Norm_sub (hJ4 ↥L hL) hTL hBL hTB hD
    · exact A314.excl_hat (V := CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _) hB A314.hS_alt_six hA
    · exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
        (Or.inr (Or.inl hB)) hA
    · exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
        (Or.inl hB) hA
  ·
    obtain ⟨hB | hB, -⟩ := h
    · obtain ⟨V, hVn, hV, hY⟩ := hB
      obtain ⟨Z, E, hZ4, -, hE, -, -, hZE⟩ := hV
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
      rw [A314.card_isAlt_five hY, hcard] at h1
      have hVc : Nat.card ↥V = 32 := by omega
      have hEc : Nat.card ↥E = 32 := by rw [hE.2]; norm_num
      have hEtop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [hEc, hVc])
      rw [hEtop, inf_top_eq, hZ4] at hZE
      omega
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_of_isZ4Cubed h)
        (fun Y _ hY => Or.inl hY) hA
  ·
    obtain ⟨hB | hB, -⟩ := h
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_of_isExtraspecial2 h)
        (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_hat_ext hB (fun V _ _ h => A314.solvable_isE2 6 V h) (fun Y _ hY => hY)
        A314.hS_alt_six hA
  ·
    obtain ⟨hB | hB, h11, -⟩ := h
    · have := hD.card_pCore
      rw [h11] at this
      omega
    · exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
        (Or.inl hB) hA

theorem noSL25In_of_a312Case {X : Type} [Group X] [Finite X] (hM : A314ModelFacts)
    (hR2 : Rank2NoSL25)
    (hJ4 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .J4 X → NoSL25Norm X)
    (hX : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ → A312Case B ⊤) :
    NoSL25In X := by
  intro T hT B hB hne hTB hD
  exact not_a312Case_of_sl25 hM hR2 hJ4 hD hT le_top hTB (hX T hT B hB hne)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
