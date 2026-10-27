module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SBasic
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofFix

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def Concl425 {G : Type} [Group G] (A L : Subgroup G) (c : G)
    (K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)) (K' : Subgroup G) : Prop :=
  (IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
      Nonempty (L ≃* Blueprint.NativeSporadic.J2)) ∨
    (∃ p f : ℕ, IsSLThreePiAt K (p ^ f) ∧
      (Blueprint.ChevalleyExceptionalModel L .G2 p f ∨
        Blueprint.ChevalleyExceptionalModel L .trialityD4 p f)) ∨
    (((IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
          Nonempty (L ≃* Blueprint.NativeSporadic.M24)) ∨
        (IsExtOf K (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)) ∧
          Nonempty (L ≃* Blueprint.NativeSporadic.He))) ∧
      ∃ E : Subgroup G, E ≤ K' ⊔ (A ⊓ Subgroup.centralizer (K' : Set G)) ∧ Late.IsE27 E ∧
        ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def Row425 (S : Type) [Group S] : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G, Late.IsE27 A →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3 → aschbacherSolvableCore 3 G = ⊥ →
    ∀ L : Subgroup G, IsComponent L → Nonempty (L ⧸ Subgroup.center L ≃* S) →
    ∀ c : G, ¬ L ≤ Subgroup.centralizer {c} →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
    ∀ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype →
      IsType425 (K ⧸ aschbacherSolvableCore 3 K) →
      A ⊓ (K' ⊓ Subgroup.centralizer (K' : Set G)) = Subgroup.zpowers c →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      Concl425 A L c K K'

@[expose] def RowOf425 (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → Row425 S

structure K425Rows : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowOf425 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf425 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf425 (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowOf425 (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowOf425 (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowOf425 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowOf425 (projSU 5 2 1)
  eight_SL6 : RowOf425 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowOf425 (projSU 6 2 1)
  eight_SL7 : RowOf425 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowOf425 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowOf425 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowOf425 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowOf425 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowOf425 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowOf425 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowOf425 (projSU 5 2 2)
  eight_SU5_8 : RowOf425 (projSU 5 2 3)
  eight_F4 : RowOf425 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOf425 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOf425 (projSU 3 3 e)
  nine_G2 : RowOf425 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowOf425 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowOf425 (projSU 4 3 1)

namespace K425Rows

variable {S : Type} [Group S] [Finite S]

theorem row_of_list42 (R : K425Rows) (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Census.List42 S) : Row425 S := by
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

end K425Rows

section Main

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_centralizer {L : Subgroup G} (hL : IsComponent L) {c : G}
    (hLc : L ≤ Subgroup.centralizer {c})
    {K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)} (hK : IsComponent K)
    {K' : Subgroup G} (hK' : K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype) : K' = L := by
  have hM : L ⊓ Subgroup.centralizer ({c} : Set G) = L := inf_eq_left.mpr hLc
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {c} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  let eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  haveI : Group.IsPerfect K' := hK'q.1
  have hnt : Nontrivial K' := by
    obtain ⟨a, b, hab⟩ := hK'q.2.2
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => rw [Subsingleton.elim a b]
  let e : (L ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) ≃* L := MulEquiv.subgroupCongr hM
  have hsn : (K'.subgroupOf L).IsSubnormal := by
    have hmap := hK.2.map (f := (e : (L ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) →* L))
      e.surjective
    have heq : K.map (e : (L ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) →* L) =
        K'.subgroupOf L := by
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe, hK']
      constructor
      · rintro ⟨k, hk, hkx⟩
        refine ⟨k, hk, ?_⟩
        have := congrArg Subtype.val hkx
        exact this
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
    rwa [heq] at hmap
  exact Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hK'L hL.1 inferInstance hnt hsn

end Main

section MainCerts

variable {G : Type} [Group G] [Finite G]

theorem item4_25Fix_of_rows (R : K425Rows) : Item4_25Fix := by
  intro G _ _ hG A hA h3 hθ L hL c K hK K' hK' htype hAZ hN
  by_cases hLc : L ≤ Subgroup.centralizer {c}
  · exact Or.inl (eq_of_le_centralizer hL hLc hK hK')
  · right
    have hq : IsQuasisimple L := hL.1
    have hlist := RonanK432.list42_quotient_center hq (sectionFourHyp_subgroup hG L)
    exact R.row_of_list42 hq.2.1 hq.2.2 hlist G hG A hA h3 hθ L hL ⟨MulEquiv.refl _⟩ c hLc K hK
      K' hK' htype hAZ hN

end MainCerts

section NoCC

theorem row425_of_noCC {S : Type} [Group S] [Finite S] (h : NoCC425 S) : Row425 S := by
  intro G _ _ hG A hA h3 hθ L hL ⟨e⟩ c hLc K hK K' hK' htype hAZ hN
  obtain ⟨hc, -, hcc⟩ := exists_cc425 hθ hA hL hLc hK hK' htype hAZ
  exact absurd (hcc.map e) (h _ _)

theorem rowOf425_of_noCC {X : Type} [Group X]
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → NoCC425 S) : RowOf425 X :=
  fun S _ _ hs hna hX => row425_of_noCC (h S hs hna hX)

end NoCC

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
