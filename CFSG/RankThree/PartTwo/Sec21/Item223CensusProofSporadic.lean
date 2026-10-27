module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofFamilies
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.He
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J2
public import CFSG.RankThree.Asc83Table.M24
public import CFSG.RankThree.Asc83Table.He
public import CFSG.RankThree.Asc83Table.Ru
public import CFSG.RankThree.Asc83Table.J4
public import CFSG.RankThree.Asc83Table.E27
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

namespace Item223CensusProof

theorem census223Fact_of_not_dvd {S : Type} [Group S] [Finite S] (h : ¬ 3 ^ 3 ∣ Nat.card S) :
    Census223Fact S := by
  refine Or.inl (pRank_le_two_of_card_le_nine fun F hF => ?_)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
  have hdvd : Nat.card F ∣ Nat.card S :=
    (Subgroup.card_subgroup_dvd_card F).trans (Subgroup.index_dvd_card _)
  rw [hk] at hdvd ⊢
  by_contra h9
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact h ((Nat.pow_dvd_pow 3 hk3).trans hdvd)

theorem two_pow_sub_one_dvd_card {S : Type} [Group S] [Finite S] {Kb : Subgroup S} {m : ℕ}
    (hm : 1 ≤ m) (eK : Kb ≃* projSL 2 (GaloisField 2 m)) : 2 ^ m - 1 ∣ Nat.card S := by
  have hcard : Nat.card Kb = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr eK.toEquiv, card_projSL_two m hm]
  have h1 : 2 ^ m - 1 ∣ (2 ^ m) ^ 2 - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (x := 2 ^ m) (y := 1) (n := 2)
  exact (h1.trans (Dvd.intro_left _ hcard.symm)).trans (Subgroup.card_subgroup_dvd_card Kb)

theorem census223Fact_of_card_dvd {S : Type} [Group S] [Finite S] {N b : ℕ}
    (hN : Nat.card S ∣ N) (hN0 : 0 < N) (hb : N < 2 ^ b - 1)
    (hcheck : ∀ m < b, 1 < m → Odd m → ¬ 2 ^ m - 1 ∣ N) : Census223Fact S := by
  refine Or.inr fun Kb m a ⟨eK⟩ hm1 hmo _ _ _ => ?_
  have hdvd := (two_pow_sub_one_dvd_card (by omega) eK).trans hN
  by_cases hmb : m < b
  · exact hcheck m hmb hm1 hmo hdvd
  · have h1 : 2 ^ b ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.le_of_dvd hN0 hdvd
    omega

theorem census223Fact_of_isExtOf_not_dvd {Y S : Type} [Group Y] [Finite Y] [Group S]
    [Group.IsPerfect S] (h : Sec4.IsExtOf Y S (Multiplicative (ZMod 3)))
    (hS : ¬ 3 ^ 3 ∣ Nat.card S) : Census223Fact Y := by
  refine Or.inl (pRank_le_two_of_card_le_nine fun F hF => ?_)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
  have hdvd : Nat.card F ∣ Nat.card S :=
    (Subgroup.card_subgroup_dvd_card F).trans (card_quotient_center_dvd_of_isExtOf h)
  rw [hk] at hdvd ⊢
  by_contra h9
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hS ((Nat.pow_dvd_pow 3 hk3).trans hdvd)

theorem card_of_isExtOf_three {Y S : Type} [Group Y] [Group S]
    (h : Sec4.IsExtOf Y S (Multiplicative (ZMod 3))) : Nat.card Y = Nat.card S * 3 := by
  obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := h
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
    Nat.card_congr eN.toEquiv, h3]

theorem census223Fact_of_simple_pRank {S : Type} [Group S] [IsSimpleGroup S]
    (hnp : ¬ (Nat.card S).Prime) (h : CFSG.pRank 3 S ≤ 2) : Census223Fact S := by
  have hZ : Subgroup.center S = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S)).resolve_right
      fun htop => hnp ?_
    have : IsMulCommutative S := ⟨⟨fun a b =>
      Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a⟩⟩
    exact Group.is_simple_iff_prime_card.mp inferInstance
  exact Or.inl (by
    rw [CFSG.RankThree.Asc83Table.pRank_congr (Sec4.quotientCenterEquivOfBot hZ)]
    exact h)

theorem pRank_le_two_of_extraspecial {S : Type} [Group S] [Finite S]
    (hP : ∀ P : Sylow 3 S, IsExtraspecialPGroup 3 (P : Subgroup S) ∧
      Nat.card (P : Subgroup S) = 27) : CFSG.pRank 3 S ≤ 2 := by
  refine pRank_le_two_of_card_le_nine fun F hF => ?_
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hFP⟩ := (Sec4.isPGroup_of_isElemAbelian hF).exists_le_sylow
  obtain ⟨hext, h27⟩ := hP P
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
  have hdvd : Nat.card F ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hFP
  rw [hk] at hdvd ⊢
  have hk3 : k ≤ 3 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    by_contra hk3
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_contra h9
  have hk3' : k = 3 := by
    by_contra hne
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hk3'
  have hFeq : F = P := Subgroup.eq_of_le_of_card_ge hFP (by rw [hk, h27]; norm_num)
  have hc := hext.2.2.2
  have htop : Subgroup.center (P : Subgroup S) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := hF.1.1.comm ⟨y, hFeq ▸ y.2⟩ ⟨x, hFeq ▸ x.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  rw [htop, Subgroup.card_top, h27] at hc
  omega

end Item223CensusProof

open Item223CensusProof

@[expose] def Census223SporadicRest : Prop :=
  Census223Fact (NativeSporadic.Carrier .McL) ∧
  ∀ (Y : Type) [Group Y] [Finite Y],
    (Sec4.IsExtOf Y (NativeSporadic.Carrier .McL) (Multiplicative (ZMod 3)) ∨
      Sec4.IsExtOf Y (NativeSporadic.Carrier .ONan) (Multiplicative (ZMod 3))) →
    Census223Fact Y

theorem census223Sporadic_of
    (h : Census223SporadicRest) : Census223Sporadic := by
  have hM22 : Nat.card (NativeSporadic.Carrier .M22) = 443520 :=
    KFacts.KS14.card_nativeM22
  have hJ3 : Nat.card (NativeSporadic.Carrier .J3) = 50232960 := CFSG.Sporadic.J3.card_J3
  refine ⟨fun s hs => ?_, fun s hs Y _ _ hY => ?_⟩
  · simp only [Sec4.sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have h1 : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
      have : Finite (NativeSporadic.Carrier .M11) :=
        Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      exact census223Fact_of_not_dvd (by rw [h1]; norm_num)
    ·
      have h1 : Nat.card (NativeSporadic.Carrier .M12) = 95040 := KFacts.KS14.card_nativeM12
      have : Finite (NativeSporadic.Carrier .M12) :=
        Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      exact census223Fact_of_card_dvd (N := 95040) (b := 17) (by rw [h1]) (by norm_num)
        (by norm_num) (by decide)
    ·
      have : Finite (NativeSporadic.Carrier .M22) :=
        Nat.finite_of_card_ne_zero (by rw [hM22]; norm_num)
      exact census223Fact_of_not_dvd (by rw [hM22]; norm_num)
    ·
      have h1 : Nat.card (NativeSporadic.Carrier .M23) = 10200960 :=
        (CFSG.Sporadic.Schreier.fam_m23_order).choose_spec.2.2.2.choose_spec.2.2.2.2
      have : Finite (NativeSporadic.Carrier .M23) :=
        Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      exact census223Fact_of_not_dvd (by rw [h1]; norm_num)
    ·
      have : IsSimpleGroup (NativeSporadic.Carrier .M24) :=
        CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
      have h1 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 :=
        CFSG.Sporadic.Mathieu.card_M24
      exact census223Fact_of_simple_pRank (by rw [h1]; norm_num)
        (CFSG.RankThree.Asc83Table.M24.table ⟨MulEquiv.refl _⟩).2.1.le
    ·
      have h1 : Nat.card (NativeSporadic.Carrier .J1) = 175560 := CFSG.Sporadic.J1.card_J1
      have : Finite (NativeSporadic.Carrier .J1) :=
        Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      exact census223Fact_of_not_dvd (by rw [h1]; norm_num)
    ·
      have : IsSimpleGroup (NativeSporadic.Carrier .J2) := CFSG.Sporadic.J2.isSimpleGroup_J2
      have h1 : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
      have : Finite (NativeSporadic.Carrier .J2) :=
        Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      refine census223Fact_of_simple_pRank (by rw [h1]; norm_num)
        (pRank_le_two_of_extraspecial fun P => ?_)
      have h415 := (Sec4.Sporadic.rank3II_4_15 (NativeSporadic.Carrier .J2) ⟨MulEquiv.refl _⟩ P _
        rfl _ rfl).1.1
      exact ⟨h415.1, h415.2.1⟩
    ·
      have : Finite (NativeSporadic.Carrier .J3) :=
        Nat.finite_of_card_ne_zero (by rw [hJ3]; norm_num)
      exact census223Fact_of_card_dvd (N := 50232960) (b := 26) (by rw [hJ3]) (by norm_num)
        (by norm_num) (by decide)
    ·
      have : IsSimpleGroup (NativeSporadic.Carrier .J4) := CFSG.Sporadic.J4.isSimpleGroup_J4
      have h1 : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
        CFSG.Sporadic.J4.card_J4
      exact census223Fact_of_simple_pRank (by rw [h1]; norm_num)
        (CFSG.RankThree.Asc83Table.J4.table ⟨MulEquiv.refl _⟩).2.1.le
    ·
      exact h.1
    ·
      have h1 : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
      have : Finite (NativeSporadic.Carrier .HS) :=
        Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      exact census223Fact_of_not_dvd (by rw [h1]; norm_num)
    ·
      have : IsSimpleGroup (NativeSporadic.Carrier .He) := CFSG.Sporadic.He.isSimpleGroup_He
      have h1 : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
      exact census223Fact_of_simple_pRank (by rw [h1]; norm_num)
        (CFSG.RankThree.Asc83Table.He.table ⟨MulEquiv.refl _⟩).2.1.le
    ·
      have : IsSimpleGroup (NativeSporadic.Carrier .Ru) := CFSG.Sporadic.Ru.isSimpleGroup_Ru
      have h1 : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
      exact census223Fact_of_simple_pRank (by rw [h1]; norm_num)
        (CFSG.RankThree.Asc83Table.Ru.table ⟨MulEquiv.refl _⟩).2.1.le
  · simp only [Sec4.sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    ·
      have hs : IsSimpleGroup (NativeSporadic.Carrier .M22) :=
        CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
      have : Group.IsPerfect (NativeSporadic.Carrier .M22) := by
        refine isPerfect_of_isSimpleGroup ?_
        by_contra hc
        push Not at hc
        have : IsMulCommutative (NativeSporadic.Carrier .M22) := ⟨⟨hc⟩⟩
        have hprime := Group.is_simple_iff_prime_card.mp hs
        rw [hM22] at hprime
        norm_num at hprime
      exact census223Fact_of_isExtOf_not_dvd hY (by rw [hM22]; norm_num)
    ·
      have h1 := card_of_isExtOf_three hY
      rw [hJ3] at h1
      exact census223Fact_of_card_dvd (N := 150698880) (b := 28) (by rw [h1]) (by norm_num)
        (by norm_num) (by decide)
    ·
      exact h.2 Y (Or.inl hY)
    ·
      exact h.2 Y (Or.inr hY)

end CFSG.RankThree.PartTwo.Sec21
