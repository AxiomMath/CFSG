module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Center
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit
public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofOuter

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

variable {Γ : Type} [Group Γ] [Finite Γ]

section Bar

theorem exists_cq_bar {L K : Subgroup Γ} (hZL : IsPGroup 3 (Subgroup.center ↥L)) (hKL : K ≤ L)
    (hKq : IsQuasisimple ↥K) {z : Γ} (hzK : z ∈ K) (hKz : K ≤ Subgroup.centralizer {z})
    (hz3 : orderOf z = 3)
    (hO3 : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) = Subgroup.zpowers z)
    (hLz : ¬ L ≤ Subgroup.centralizer {z}) :
    ∃ hz : z ∈ L, K.subgroupOf L ⊓ Subgroup.center ↥L = ⊥ ∧
      orderOf (((⟨z, hz⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)) = 3 ∧
      (((⟨z, hz⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)) ∈
        (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ∧
      (K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
        Subgroup.centralizer {(((⟨z, hz⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L))} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzL : z ∈ L := hKL hzK
  have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
  have hinf : K.subgroupOf L ⊓ Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxZ⟩
    rw [Subgroup.mem_bot]
    have hxK' : (x : Γ) ∈ K := hxK
    have hxC : (x : Γ) ∈ Subgroup.centralizer (K : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxZ) ⟨k, hKL hk⟩)
    obtain ⟨k, hk⟩ := hZL ⟨x, hxZ⟩
    have hxk : (x : Γ) ^ 3 ^ k = 1 := by
      have := congrArg (fun y : Subgroup.center ↥L => ((y : ↥L) : Γ)) hk
      simpa using this
    have hxP := mem_pCore_center_of_pow hxK' hxC hxk
    rw [hO3] at hxP
    by_contra hx1
    have hx1' : (x : Γ) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hzx : z ∈ Subgroup.zpowers (x : Γ) := by
      have hle : Subgroup.zpowers (x : Γ) ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hxP
      have hcard : Nat.card (Subgroup.zpowers z) ≤ Nat.card (Subgroup.zpowers (x : Γ)) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hz3]
        have hdvd : orderOf (x : Γ) ∣ 3 := by
          rw [← hz3, ← Nat.card_zpowers, ← Nat.card_zpowers]
          exact Subgroup.card_dvd_of_le hle
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1'
        · omega
      exact (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ Subgroup.mem_zpowers z
    apply hLz
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzx
    rw [← hm]
    have hxl : (x : Γ) * l = l * x :=
      (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxZ) ⟨l, hl⟩)).symm
    exact ((Commute.zpow_left hxl m)).symm.eq
  refine ⟨hzL, hinf, ?_, ⟨⟨z, hzL⟩, hzK, rfl⟩, ?_⟩
  · have hs1 : (((⟨z, hzL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)) ≠ 1 :=
      fun h => hLz ((mk_eq_one_iff hzL).mp h)
    refine orderOf_eq_prime ?_ hs1
    rw [← QuotientGroup.mk_pow]
    have : (⟨z, hzL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hz3')
    rw [this, QuotientGroup.mk_one]
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKz hl))

end Bar

@[expose] def ConclH2 (L : Type) [Group L] : Prop :=
  Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
    Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
    Sec4.IsTripleCover L CFSG.Blueprint.NativeSporadic.ON

@[expose] def RowH2 (S : Type) [Group S] : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (C : Subgroup Γ), SectionFourHyp ↥C →
    aschbacherSolvableCore 3 ↥C = ⊥ → partTwoE ↥C = partTwoF ↥C →
    ∀ (A L K : Subgroup Γ) (d : Γ), Late.IsE27 A → L ⊔ A = C → d ∈ A → d ≠ 1 →
      (∀ g ∈ C, g ∈ Subgroup.normalizer (A : Set Γ) →
        g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set Γ)) →
      IsQuasisimple ↥L → C ≤ Subgroup.normalizer (L : Set Γ) →
      ¬ L ≤ Subgroup.centralizer {d} → K ≤ L ⊓ Subgroup.centralizer {d} →
      (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal → IsQuasisimple ↥K →
      A ≤ Subgroup.normalizer (K : Set Γ) →
      Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)) →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* S) →
      ¬ inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) ≤
        Subgroup.centralizer (L : Set Γ) →
      ConclH2 ↥L

@[expose] def RowOfH2 (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → RowH2 S

section NoCQ


theorem isPGroup_center_of_normal {C L : Subgroup Γ} (hCθ : aschbacherSolvableCore 3 ↥C = ⊥)
    (hLC : L ≤ C) (hCL : C ≤ Subgroup.normalizer (L : Set Γ)) (hLq : IsQuasisimple ↥L) :
    IsPGroup 3 (Subgroup.center ↥L) := by
  let eL : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  have hL₀n : (L.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hCL
  have hL₀c : IsComponent (L.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq, hL₀n.isSubnormal⟩
  exact (isPGroup_center_of_isComponent hCθ hL₀c).of_equiv (Subgroup.centerCongr eL)

theorem rowH2_of_noCQ {S : Type} [Group S] [Finite S] (h : NoCQ425 S) : RowH2 S := by
  intro Γ _ _ C hC4 hCθ _ A L K d hA hLA hdA hd1 _ hLq hCL _ hKM _ hKq _ hA6 ⟨e⟩ hZL
  exfalso
  have hLC : L ≤ C := hLA ▸ le_sup_left
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hZ3 := isPGroup_center_of_normal hCθ hLC hCL hLq
  obtain ⟨z, hzK, hKz, hz3, hZ⟩ := exists_pCore_center_eq_zpowers hKq hA6.1
  have hLz : ¬ L ≤ Subgroup.centralizer {z} := by
    intro hLz
    apply hZL
    rw [hZ, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLz hl)
  obtain ⟨hz, hinf, ho, hmem, hle⟩ := exists_cq_bar hZ3 hKL hKq hzK hKz hz3 hZ hLz
  let eB : ↥K ≃* ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) :=
    equivBar hKL hinf
  have hBq := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hKq
  have hBt : IsType425 (↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⧸
      aschbacherSolvableCore 3 ↥((K.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))) :=
    isType425_theta_congr eB (Or.inr (Or.inl hA6.isExtOf))
  exact NoCQ425.of_mulEquiv e h _ _ ho hmem hle hBq hBt

end NoCQ

structure KH2Rows : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowOfH2 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOfH2 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOfH2 (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOfH2 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOfH2 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOfH2 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOfH2 (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowOfH2 (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowOfH2 (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowOfH2 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowOfH2 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowOfH2 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowOfH2 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOfH2 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowOfH2 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowOfH2 (projSU 5 2 1)
  eight_SL6 : RowOfH2 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowOfH2 (projSU 6 2 1)
  eight_SL7 : RowOfH2 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowOfH2 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowOfH2 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowOfH2 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowOfH2 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowOfH2 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowOfH2 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowOfH2 (projSU 5 2 2)
  eight_SU5_8 : RowOfH2 (projSU 5 2 3)
  eight_F4 : RowOfH2 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOfH2 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOfH2 (projSU 3 3 e)
  nine_G2 : RowOfH2 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowOfH2 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowOfH2 (projSU 4 3 1)

namespace KH2Rows

variable {S : Type} [Group S] [Finite S]

theorem row_of_list42 (R : KH2Rows) (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Census.List42 S) : RowH2 S := by
  rcases h with ⟨p, e, hp, h2, he, hf⟩ | ⟨p, e, hp, h3, he, he2, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p, hp, h3, ⟨q, hqp, hqe, hq, hf⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ |
    ⟨s, hsp, hf⟩ | h7 | h8 | h9
  · exact R.one p e h2 he S hs hna hf
  · exact R.two_SL p e h3 he he2 S hs hna hf
  · exact R.two_SU p e h3 he he2 S hs hna hf
  · exact R.three hr S hs hna hf
  · exact R.four_G2 p h3 q hqp hqe hq S hs hna hf
  · exact R.four_Sp p h3 S hs hna hf
  · exact R.four_SL p h3 S hs hna hf
  · exact R.four_SU p h3 S hs hna hf
  · exact R.five n hn5 hn12 S hs hna hf
  · exact R.six s hsp S hs hna hf
  · rcases h7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hq, hf⟩ |
      ⟨q, hq, hq2, hf⟩ | ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    · exact R.seven_SL2 n hn S hs hna hf
    · exact R.seven_SL3 n hn S hs hna hf
    · exact R.seven_SU3 n hn S hs hna hf
    · exact R.seven_Sp4 n hn S hs hna hf
    · exact R.seven_SU4 n hn S hs hna hf
    · exact R.seven_G2 q hq2 hq S hs hna hf
    · exact R.seven_D4 q hq hq2 S hs hna hf
    · exact R.seven_Sz m hm S hs hna hf
    · exact R.seven_F4 m hm S hs hna hf
    · exact R.seven_Tits ht S hs hna hf
  · rcases h8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf |
      hf | hf | hf | hf
    · exact R.eight_SL5 S hs hna hf
    · exact R.eight_SU5 S hs hna hf
    · exact R.eight_SL6 S hs hna hf
    · exact R.eight_SU6 S hs hna hf
    · exact R.eight_SL7 S hs hna hf
    · exact R.eight_Sp6 S hs hna hf
    · exact R.eight_Sp8 S hs hna hf
    · exact R.eight_OmegaPlus S hs hna hf
    · exact R.eight_OmegaMinus b c hbc S hs hna hf
    · exact R.eight_SL4 S hs hna hf
    · exact R.eight_Sp6_4 S hs hna hf
    · exact R.eight_SU5_4 S hs hna hf
    · exact R.eight_SU5_8 S hs hna hf
    · exact R.eight_F4 S hs hna hf
  · rcases h9 with ⟨e, he, he3, hf | hf⟩ | hf | hf | hf
    · exact R.nine_SL3 e he he3 S hs hna hf
    · exact R.nine_SU3 e he he3 S hs hna hf
    · exact R.nine_G2 S hs hna hf
    · exact R.nine_SL4 S hs hna hf
    · exact R.nine_SU4 S hs hna hf

end KH2Rows

section Main


theorem kf148HJA6Outer_of_rows (h426 : Sec4.Item4_26ThetaA6) (R : KH2Rows) : KF148HJA6Outer := by
  intro Γ _ _ C hC4 hCθ hEF A L K d hA hLA hdA hd1 hW hLq hCL hLd hKM hKsn hKq hAK hA6
  by_cases hZL : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) ≤
      Subgroup.centralizer (L : Set Γ)
  · exact Or.inr (Or.inr (isTripleCover_ON_of_center h426 hC4 hCθ hA hLA hdA hd1 hLq hCL hLd
      hKM hKsn hKq hAK hA6 hZL))
  · have hLC : L ≤ C := hLA ▸ le_sup_left
    have hSL : SectionFourHyp ↥L :=
      Census.sectionFourHyp_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC)
        (sectionFourHyp_subgroup hC4 (L.subgroupOf C))
    have hlist := RonanK432.list42_quotient_center hLq hSL
    exact R.row_of_list42 hLq.2.1 hLq.2.2 hlist Γ C hC4 hCθ hEF A L K d hA hLA hdA hd1 hW hLq hCL
      hLd hKM hKsn hKq hAK hA6 ⟨MulEquiv.refl _⟩ hZL

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
