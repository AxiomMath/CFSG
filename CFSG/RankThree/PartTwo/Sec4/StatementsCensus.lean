module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def IsoGTwo (X : Type) [Group X] (q : TauCeti.PrimePower) : Prop :=
  ∃ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def IsChevTwoRankTwo (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧
    (Nonempty (X ≃* projSL 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 3 2 n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 4 2 n))) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ IsoGTwo X q) ∨
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group)) ∨
  (∃ ht : TauCeti.LieTypeIndex.tits.Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group))

@[expose] def sporadics42 : List TauCeti.SporadicName :=
  [.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .McL, .Ly, .HS, .He, .Suz, .Ru, .ONan, .Co3,
    .Co2, .HN, .Th]

theorem q8D8_mem_center : (QuaternionGroup.a 2, DihedralGroup.r 2) ∈
    Subgroup.center (QuaternionGroup 2 × DihedralGroup 4) := by
  rw [Subgroup.mem_center_iff]
  decide

@[expose] def q8D8Kernel : Subgroup (QuaternionGroup 2 × DihedralGroup 4) :=
  Subgroup.zpowers (QuaternionGroup.a 2, DihedralGroup.r 2)

instance q8D8Kernel_normal : q8D8Kernel.Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr q8D8_mem_center)

abbrev Q8D8 : Type := (QuaternionGroup 2 × DihedralGroup 4) ⧸ q8D8Kernel

theorem quaternion_mul_center (q : QuaternionGroup 2) :
    q * QuaternionGroup.a 2 = QuaternionGroup.a 2 * q := by
  revert q
  decide

@[expose] def z4Q8Q8Kernel :
    Subgroup (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) :=
  Subgroup.closure {(Multiplicative.ofAdd 2, QuaternionGroup.a 2, 1),
    (Multiplicative.ofAdd 2, 1, QuaternionGroup.a 2)}

instance z4Q8Q8Kernel_normal : z4Q8Q8Kernel.Normal := by
  refine Subgroup.normal_of_le_center ((Subgroup.closure_le _).mpr ?_)
  rintro g (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_center_iff] <;>
    rintro ⟨g1, g2, g3⟩ <;> simp only [Prod.mk_mul_mk, Prod.mk.injEq]
  · exact ⟨mul_comm _ _, quaternion_mul_center g2, by rw [mul_one, one_mul]⟩
  · exact ⟨mul_comm _ _, by rw [mul_one, one_mul], quaternion_mul_center g3⟩

abbrev Z4Q8Q8 : Type :=
  (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) ⧸ z4Q8Q8Kernel

instance oTwoFitting_normal (X : Type*) [Group X] : (oTwoFitting X).Normal :=
  Subgroup.Normal.comap inferInstance _

instance oTwoP_normal (p : ℕ) (X : Type*) [Group X] : (oTwoP p X).Normal :=
  Subgroup.Normal.comap (CFSG.pCore_normal (p := p)) _

@[expose] def Item4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
      Nonempty (G ≃* projSL 2 (GaloisField p e))) ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (Nonempty (G ≃* projSL 3 (GaloisField p e)) ∨ Nonempty (G ≃* projSU 3 p e))) ∨
    (∃ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group)) ∨
    (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoGTwo G q) ∨
        Nonempty (G ≃* projSp 2 (GaloisField p 1)) ∨
        Nonempty (G ≃* projSL 4 (GaloisField p 1)) ∨ Nonempty (G ≃* projSU 4 p 1))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 12 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    (∃ s ∈ sporadics42, Nonempty (G ≃* Spor s)) ∨
    IsChevTwoRankTwo G ∨
    (Nonempty (G ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 5 2 1) ∨
      Nonempty (G ≃* projSL 6 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSU 6 2 1) ∨
      Nonempty (G ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 1)) ∨
      Nonempty (G ≃* projSp 4 (GaloisField 2 1)) ∨
      Nonempty (G ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
      (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
      Nonempty (G ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (G ≃* projSp 3 (GaloisField 2 2)) ∨
      Nonempty (G ≃* projSU 5 2 2) ∨ Nonempty (G ≃* projSU 5 2 3) ∨
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)) ∨
    ((∃ e : ℕ, 1 ≤ e ∧ e ≤ 3 ∧
        (Nonempty (G ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (G ≃* projSU 3 3 e))) ∨
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) ∨
      Nonempty (G ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (G ≃* projSU 4 3 1))

@[expose] def Item4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → Group.IsPerfect G →
    ∀ (K : Subgroup G) [K.Normal], Group.IsSolvable K → IsSimpleGroup (G ⧸ K) →
      IsQuasisimple (G ⧸ CFSG.pCore 2 G) ∨
      Nonempty (G ⧸ oTwoFitting G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧
        Nonempty (G ⧸ oTwoP p G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) ∨
      (Nonempty (G ⧸ oTwoP 3 G ≃* projSL 3 (GaloisField 3 1)) ∨
        IsExtOf (G ⧸ oTwoP 3 G) (alternatingGroup (Fin 5)) Q8D8) ∨
      (CFSG.pCore 2 G = ⊥ ∧ (¬ 3 ∣ Nat.card K →
        (CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 2 ∧
            (IsQuasisimple (G ⧸ CFSG.oddCore G) ∨
              IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 5)) Q8D8)) ∨
          (CFSG.Open.pRank 2 (⊤ : Subgroup G) = 3 ∧
            (IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 5)) Q8D8 ∨
              IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 5)) Z4Q8Q8 ∨
              IsExtOf (G ⧸ CFSG.oddCore G) (alternatingGroup (Fin 6)) Z4Q8Q8))))

@[expose] def omegaOneCenterThree {G : Type*} [Group G] (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ P ∧ x ∈ Subgroup.centralizer (P : Set G) ∧ x ^ 3 = 1}

@[expose] def Item4_40 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M Q : Subgroup G), Ctx434 G A M Q →
    haveI : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic;
    ∃ a ∈ A, a ∉ Subgroup.centralizer (layer G : Set G) ∧
      (∃ X ∈ invariantPiSubgroups
          (Subgroup.centralizer
            {QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)) a})
          (A.map (QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)))) (piCompl 3),
        X ≠ ⊥) ∧
      inSubgroup generalizedFitting (Subgroup.centralizer
          {QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)) a}) ≠
        inSubgroup (CFSG.pCore 3) (Subgroup.centralizer
          {QuotientGroup.mk' (Subgroup.centralizer (layer G : Set G)) a}) ∧
      (3 < CFSG.Open.pRank 3 (Subgroup.centralizer {a}) →
        ∀ P : Sylow 3 (Subgroup.centralizer {a}),
          Subgroup.zpowers a =
            omegaOneCenterThree ((P : Subgroup (Subgroup.centralizer {a})).map
              (Subgroup.centralizer {a}).subtype))

end CFSG.RankThree.PartTwo.Sec4
