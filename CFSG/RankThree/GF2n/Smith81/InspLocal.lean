module

public import CFSG.RankThree.GF2n.Smith81.Sec220Local
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld

variable {G : Type} [Group G]

abbrev classIn (z : G) : Set ↥(Subgroup.normalClosure ({z} : Set G)) :=
  {x | IsConj z (x : G)}

abbrev selfIn (z : G) : ↥(Subgroup.normalClosure ({z} : Set G)) :=
  ⟨z, Subgroup.subset_normalClosure rfl⟩

theorem mem_normalClosure_of_isConj {z w : G} (hw : IsConj z w) :
    w ∈ Subgroup.normalClosure ({z} : Set G) :=
  Subgroup.conjugatesOfSet_subset_normalClosure (Group.mem_conjugatesOfSet_iff.mpr ⟨z, rfl, hw⟩)

theorem image_classIn (z : G) :
    (Subgroup.normalClosure ({z} : Set G)).subtype '' classIn z = {g : G | IsConj z g} := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hg
    exact ⟨⟨g, mem_normalClosure_of_isConj hg⟩, hg, rfl⟩

theorem card_rootGroup_classIn (z : G) (x : ↥(Subgroup.normalClosure ({z} : Set G))) :
    Nat.card (rootGroup (classIn z) x) = Nat.card (rootGroup {g : G | IsConj z g} (x : G)) := by
  rw [← image_classIn z]
  exact (card_rootGroup_image _ (Subgroup.normalClosure ({z} : Set G)).subtype_injective _ x).symm

theorem hyp_classIn [Finite G] {z : G}
    (hroot : Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g})
    (hconj : ∀ w : G, IsConj z w →
      ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹)
    (hodd : pPrimeCore 2 G = ⊥) (hO2 : pCore 2 G = ⊥)
    (hnondeg : ∃ d e : G, IsConj z d ∧ IsConj z e ∧ orderOf (d * e) = 4) :
    Hyp ↥(Subgroup.normalClosure ({z} : Set G)) (classIn z) := by
  classical
  set X := Subgroup.normalClosure ({z} : Set G) with hXdef
  haveI : X.Normal := Subgroup.normalClosure_normal
  have hzX : z ∈ X := Subgroup.subset_normalClosure rfl
  have hCX : ∀ w : G, IsConj z w → w ∈ X := fun w hw => mem_normalClosure_of_isConj hw
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨⟨z, hzX⟩, Set.ext fun x => ?_⟩
    simp only [classIn, Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨c, hcX, hc⟩ := hconj x hx
      exact isConj_iff.mpr ⟨⟨c, hcX⟩, Subtype.ext (by simp [hc])⟩
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      exact isConj_iff.mpr ⟨c, by simpa using congrArg Subtype.val hc⟩
  ·
    refine ⟨fun d hd => ?_, fun d hd e he => ?_, fun d hd e he h4 => ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact hroot.1 _ hd
    · have := hroot.2.1 _ hd _ he
      simpa [← Subgroup.orderOf_coe] using this
    · have h4' : orderOf ((d : G) * (e : G)) = 4 := by
        simpa [← Subgroup.orderOf_coe] using h4
      have := hroot.2.2 _ hd _ he h4'
      show IsConj z (((d * e) ^ 2 : ↥X) : G)
      simpa using this
  ·
    have h1 : (Subgroup.closure (classIn z)).map X.subtype = X := by
      rw [MonoidHom.map_closure, image_classIn, closure_conjClass_eq_normalClosure]
    apply Subgroup.map_injective X.subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  ·
    intro N hN hNodd
    have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hNodd
    have hle : N ≤ pPrimeCore 2 ↥X := le_sSup ⟨hN, hcop⟩
    have hnorm : ((pPrimeCore 2 ↥X).map X.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hcard : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥X).map X.subtype)) := by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact pPrimeCore_coprime_card
    have hle2 : (pPrimeCore 2 ↥X).map X.subtype ≤ pPrimeCore 2 G := le_sSup ⟨hnorm, hcard⟩
    rw [hodd, le_bot_iff] at hle2
    have hbot := (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hle2
    exact le_bot_iff.mp (hbot ▸ hle)
  ·
    intro N hN hNp
    have hle : N ≤ pCore 2 ↥X := le_sSup ⟨hN, hNp⟩
    have hnorm : ((pCore 2 ↥X).map X.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hp : IsPGroup 2 ((pCore 2 ↥X).map X.subtype) :=
      (pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
    have hle2 : (pCore 2 ↥X).map X.subtype ≤ pCore 2 G := le_sSup ⟨hnorm, hp⟩
    rw [hO2, le_bot_iff] at hle2
    have hbot := (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hle2
    exact le_bot_iff.mp (hbot ▸ hle)
  ·
    obtain ⟨d, e, hd, he, h4⟩ := hnondeg
    exact ⟨⟨d, hCX d hd⟩, hd, ⟨e, hCX e he⟩, he, by
      rw [← Subgroup.orderOf_coe]
      simpa using h4⟩

section Local

variable [Finite G] {M Q Z : Subgroup G}

theorem isPGroup_Q (H : StrothHyp M Q Z) : IsPGroup 2 Q := by
  rw [H.hQ]
  exact (inSubgroup_pCore_two M).1

theorem card_Q_le_pCoreOf (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Nat.card Q ≤ Nat.card (pCoreOf 2 (Subgroup.centralizer ({selfIn z} : Set
      ↥(Subgroup.normalClosure ({z} : Set G))))) := by
  set X := Subgroup.normalClosure ({z} : Set G) with hXdef
  set C := Subgroup.centralizer ({selfIn z} : Set ↥X) with hCdef
  have hQX : Q ≤ X := Q_le_normalClosure H hz hz1
  have hzQ : ∀ q ∈ Q, Commute q z := by
    intro q hq
    have hzc : z ∈ Subgroup.centralizer (Q : Set G) := by
      rw [H.centralizer_Q]
      exact hz
    exact Subgroup.mem_centralizer_iff.mp hzc q hq
  set Q₁ : Subgroup ↥X := Q.subgroupOf X with hQ₁
  have hQ₁C : Q₁ ≤ C := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hzQ q hq).eq
  set Q₂ : Subgroup ↥C := Q₁.subgroupOf C with hQ₂
  have hQ₂2 : IsPGroup 2 Q₂ := by
    have h1 : IsPGroup 2 Q₁ :=
      (isPGroup_Q H).comap_of_injective X.subtype X.subtype_injective
    exact h1.comap_of_injective C.subtype C.subtype_injective
  have hQ₂n : Q₂.Normal := by
    refine ⟨fun a ha c => ?_⟩
    have hcM : ((c : ↥X) : G) ∈ M := by
      apply centralizer_le_M H hz hz1
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp c.2
      exact congrArg Subtype.val this
    have haQ : ((a : ↥X) : G) ∈ Q := ha
    show (((c * a * c⁻¹ : ↥C) : ↥X) : G) ∈ Q
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hcM) _).mp haQ
  have hle : Q₂ ≤ pCore 2 ↥C := le_sSup ⟨hQ₂n, hQ₂2⟩
  have hcardQ₂ : Nat.card Q₂ = Nat.card Q := by
    have h1 : Nat.card Q₂ = Nat.card Q₁ := by
      rw [hQ₂]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₁C).toEquiv
    rw [h1, hQ₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv
  calc Nat.card Q = Nat.card Q₂ := hcardQ₂.symm
    _ ≤ Nat.card (pCore 2 ↥C) := Subgroup.card_le_of_le hle
    _ = Nat.card (pCoreOf 2 C) := by
      rw [pCoreOf, Subgroup.card_map_of_injective C.subtype_injective]

theorem Lgen_le_normalClosure {B : Subgroup G} (hc : Ctx M Q Z B) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : Lgen M (LB M Q B) ≤ Subgroup.normalClosure ({z} : Set G) := by
  have H := hc.hyp
  have hX : (Subgroup.normalClosure ({z} : Set G)).Normal := Subgroup.normalClosure_normal
  have hQX := Q_le_normalClosure H hz hz1
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B ≤ Subgroup.normalClosure ({z} : Set G) := by
    rw [hg, QB_conj_eq H g]
    intro x hx
    have hx' : g⁻¹ * x * g ∈ Q := mem_conjSubgroup.mp hx
    have := hX.conj_mem _ (hQX hx') g
    simpa [mul_assoc] using this
  have hLB : LB M Q B ≤ Subgroup.normalClosure ({z} : Set G) :=
    sup_le hQX (inf_le_left.trans hQB)
  unfold Lgen
  refine iSup₂_le fun m _ x hx => ?_
  have hx' : m⁻¹ * x * m ∈ LB M Q B := mem_conjSubgroup.mp hx
  have := hX.conj_mem _ (hLB hx') m
  simpa [mul_assoc] using this

theorem card_Lgen_dvd_centralizer {B : Subgroup G} (hc : Ctx M Q Z B) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    Nat.card (Lgen M (LB M Q B)) ∣ Nat.card (Subgroup.centralizer ({selfIn z} : Set
      ↥(Subgroup.normalClosure ({z} : Set G)))) := by
  set X := Subgroup.normalClosure ({z} : Set G)
  set C := Subgroup.centralizer ({selfIn z} : Set ↥X)
  have hLX := Lgen_le_normalClosure hc hz hz1
  have hLC : (Lgen M (LB M Q B)).subgroupOf X ≤ C := by
    intro x hx
    have hxH : (x : G) ∈ H0 M Z := Lgen_le_H0 hc hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hxH.2 z hz
    exact this.symm
  have h1 : Nat.card (Lgen M (LB M Q B)) = Nat.card ((Lgen M (LB M Q B)).subgroupOf X) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv).symm
  rw [h1]
  exact Subgroup.card_dvd_of_le hLC

end Local

end CFSG.RankThree.GF2n.Smith81.Insp
