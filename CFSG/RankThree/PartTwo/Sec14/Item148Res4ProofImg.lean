module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofImg
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofA10Gen
import CFSG.RankThree.PartTwo.Sec14.Closure
import CFSG.RankThree.PartTwo.Sec14.LBNatural

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Steps

@[expose] def Step148RankImgGeField : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        letI := ker148_normal hY.2
        img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y)

end Steps

namespace Item148Res4

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_img148_deltaZero {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    {n : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hn : n ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    n ∈ Subgroup.normalizer (img148 A Y (deltaZero A (lB A) Y) :
      Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  have hT : IsPGroup 3 ↥(A.subgroupOf (Y ⊔ A)) := by
    refine isPGroup_three_of_pow148 fun b hb => ?_
    exact Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp hb))
  have : Fact (IsPGroup 3 ↥(A.subgroupOf (Y ⊔ A))) := ⟨hT⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (ker148 A Y)) := by
    rw [ker148, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((pPrimeCoreOf_le 3 Y).trans le_sup_left)).toEquiv]
    exact coprime_card_pPrimeCoreOf 3 Y
  have hlift := CFSG.normalizer_map_quotient_eq_map_normalizer 3 (A.subgroupOf (Y ⊔ A))
    (ker148 A Y) inferInstance hcop
  have hn' : n ∈ (Subgroup.normalizer ((A.subgroupOf (Y ⊔ A) : Subgroup ↥(Y ⊔ A)) :
      Set ↥(Y ⊔ A))).map (QuotientGroup.mk' (ker148 A Y)) := by
    rw [← hlift]
    exact hn
  obtain ⟨m, hm, rfl⟩ := hn'
  have hmA : (m : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 := (Subgroup.mem_normalizer_iff.mp hm ⟨a, Subgroup.mem_sup_right ha⟩).mp
        (Subgroup.mem_subgroupOf.mpr ha)
      simpa using Subgroup.mem_subgroupOf.mp h1
    · intro ha
      have haM : a ∈ Y ⊔ A := by
        have h2 : (m : G)⁻¹ * ((m : G) * a * (m : G)⁻¹) * (m : G) ∈ Y ⊔ A :=
          (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem m.2) (Subgroup.mem_sup_right ha)) m.2
        rwa [show (m : G)⁻¹ * ((m : G) * a * (m : G)⁻¹) * (m : G) = a by group] at h2
      have h1 := (Subgroup.mem_normalizer_iff.mp hm ⟨a, haM⟩).mpr
        (Subgroup.mem_subgroupOf.mpr (by simpa using ha))
      exact Subgroup.mem_subgroupOf.mp h1
  have hmY : (m : G) ∈ Subgroup.normalizer (Y : Set G) :=
    (sup_le Subgroup.le_normalizer hAY : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G)) m.2
  have hmX := mem_normalizer_deltaZero (isNaturalFamily_lB A) hmA hmY
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨g, hg, hgX, rfl⟩ := mem_img148_iff.mp hz
    refine mem_img148_iff.mpr ⟨(m : G) * g * (m : G)⁻¹,
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem m.2 hg) ((Y ⊔ A).inv_mem m.2),
      (Subgroup.mem_normalizer_iff.mp hmX g).mp hgX, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  · intro hz
    obtain ⟨g, hg, hgX, hgz⟩ := mem_img148_iff.mp hz
    have hgM : (m : G)⁻¹ * g * (m : G) ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem m.2) hg) m.2
    have hgX' : (m : G)⁻¹ * g * (m : G) ∈ deltaZero A (lB A) Y := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hmX) g).mp hgX
      simpa using this
    refine mem_img148_iff.mpr ⟨(m : G)⁻¹ * g * (m : G), hgM, hgX', ?_⟩
    have e1 : QuotientGroup.mk' (ker148 A Y) m * z * (QuotientGroup.mk' (ker148 A Y) m)⁻¹ =
        QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ := hgz.symm
    have e2 : z = (QuotientGroup.mk' (ker148 A Y) m)⁻¹ * QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ *
        QuotientGroup.mk' (ker148 A Y) m := by
      rw [← e1]
      group
    rw [e2, ← map_inv, ← map_mul, ← map_mul]
    rfl

end Item148Res4

open Item148Res4

section Steps

theorem step148RankImgGe_of (hF : Step148RankImgGeField) : Step148RankImgGe := by
  intro G _ _ A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hA
  rcases halt with hTen | hField
  swap
  · exact hF G A c L hstd Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hField hA
  have := ker148_normal hY.2
  have hAF : A ∈ partTwoF G := hstd.mem_partTwoF
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hstd.toSec13Data.mem_partTwoE
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) := hP.2.2.2.2.2.1
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) := hKYC.trans inf_le_right
  have hKX : K ≤ deltaZero A (lB A) Y :=
    hP.2.2.2.2.2.2.1.le.trans (deltaZero_mono148 (hKYC.trans inf_le_left))
  have hle : img148 A Y A ≤ img148 A Y J :=
    Item148Rank.img148_le_of_lift148Ten148 hAF hAY he hK hKJ hJY hAJ hkt.1 hTen
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  obtain ⟨⟨φK⟩, ⟨φJ⟩⟩ := hTen
  set Q' := ↥(Y ⊔ A) ⧸ ker148 A Y
  set Jb := img148 A Y J with hJb
  set Kb := img148 A Y K with hKb
  set Ab := img148 A Y A with hAb
  set Xb := img148 A Y (deltaZero A (lB A) Y) with hXb
  have hKJb : Kb ≤ Jb := img148_mono hKJ
  set E := Ab.subgroupOf Jb with hE
  set K' := Kb.subgroupOf Jb with hK'
  set M := Xb.subgroupOf Jb with hM
  obtain ⟨hAbE, hAb27⟩ := img148_isE27 (Y := Y) hA27
  have hE27 : Nat.card E = 27 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hAb27]
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have h := congrArg Subtype.val (hAbE.1.is_comm.comm
        ⟨((x : ↥Jb) : Q'), Subgroup.mem_subgroupOf.mp x.2⟩
        ⟨((y : ↥Jb) : Q'), Subgroup.mem_subgroupOf.mp y.2⟩)
      simpa using h
    · apply Subtype.ext
      have h := hAbE.2 ((x : ↥Jb) : Q') (Subgroup.mem_subgroupOf.mp hx)
      simpa using h
  have heJ : alpha148 A Y e he ∈ Jb := hle (alpha148_mem_img148 he)
  set x : ↥Jb := ⟨alpha148 A Y e he, heJ⟩ with hx
  have hxE : x ∈ E := Subgroup.mem_subgroupOf.mpr (alpha148_mem_img148 he)
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : alpha148 A Y e he = alpha148 A Y 1 A.one_mem := by
      have h3 : alpha148 A Y e he = 1 := congrArg Subtype.val h1
      rw [h3, alpha148_eq_mk']
      exact (map_one _).symm
    exact he1 (alpha148_injective hA3 he A.one_mem h2)
  have hK'x : K' ≤ Subgroup.centralizer ({x} : Set ↥Jb) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨g, hg, hgK, hgz⟩ := mem_img148_iff.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (z : Q') * alpha148 A Y e he = alpha148 A Y e he * (z : Q')
    rw [← hgz, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKC hgK))
  have hK'7 : Nonempty (↥K' ≃* alternatingGroup (Fin 7)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hKJb).trans φK⟩
  have hK'M : K' ≤ M := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (img148_mono hKX (Subgroup.mem_subgroupOf.mp hz))
  have hNM : Subgroup.normalizer (E : Set ↥Jb) ≤ Subgroup.normalizer (M : Set ↥Jb) := by
    intro n hn
    have hnQ : (n : Q') ∈ Subgroup.normalizer (Ab : Set Q') := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hle hy⟩).mp
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hy
        have hy' : y ∈ Jb := by
          have h2 : (n : Q')⁻¹ * ((n : Q') * y * (n : Q')⁻¹) * (n : Q') ∈ Jb :=
            Jb.mul_mem (Jb.mul_mem (Jb.inv_mem n.2) (hle hy)) n.2
          rwa [show (n : Q')⁻¹ * ((n : Q') * y * (n : Q')⁻¹) * (n : Q') = y by group] at h2
        have h1 := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hy'⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hy)
        exact Subgroup.mem_subgroupOf.mp h1
    have hnX := mem_normalizer_img148_deltaZero hA3 hAY hnQ
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hnX z
  have hMtop := kf148A10Gen_holds ↥Jb ⟨φJ⟩ E K' M x hEab hE27 hxE hx1 hK'x hK'7 hK'M hNM
  intro z hz
  have : (⟨z, hz⟩ : ↥Jb) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end Steps

end CFSG.RankThree.PartTwo.Sec14
