module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4BorelQuotient
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.GroupTheory.LiftPermutes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise
open CFSG.Quasithin (IsSylowIn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof

variable {G : Type} [Group G] [Finite G]

section Certified


private theorem s19_shape_PSU3 : IsChar2LieShape .PSU 3 := by
  unfold IsChar2LieShape; simp
private theorem s19_shape_PSU5 : IsChar2LieShape .PSU 5 := by
  unfold IsChar2LieShape; simp

private theorem false_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel X t n 2 f) (hshape : IsChar2LieShape t n)
    {t' : StatedLieTag} {n' f' : ℕ} (h' : LieModel X t' n' 2 f')
    (hne : ¬ (t' = t ∧ n' = n)) : False := by
  have hh := lieModel_eq_of_isChar2LieShape h hshape h'
  exact hne ⟨hh.1, hh.2.1⟩

private theorem simple_bar2_of_isU3 {X : Subgroup G} {m : ℕ} (h : IsU3 (Bar2 X) m) :
    IsSimpleGroup (Bar2 X) :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

private theorem simple_bar2_of_isL2 {X : Subgroup G} {m : ℕ} (h : IsL2 (Bar2 X) m) :
    IsSimpleGroup (Bar2 X) :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

private theorem simple_bar2_of_isSp4 {X : Subgroup G} {m : ℕ} (h : IsSp4 (Bar2 X) m) :
    IsSimpleGroup (Bar2 X) :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

private theorem simple_bar2_of_isU4 {X : Subgroup G} {m : ℕ} (h : IsU4 (Bar2 X) m) :
    IsSimpleGroup (Bar2 X) :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

private theorem simple_bar2_of_isU5 {X : Subgroup G} {m : ℕ} (h : IsU5 (Bar2 X) m) :
    IsSimpleGroup (Bar2 X) :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

private theorem conjClosure_eq_of_simple {D : Data G} {p : ℕ} {L : Subgroup G}
    (hL : L ∈ S17.calLp D p)
    (hs : IsSimpleGroup (Bar2 (conjClosure D.M L))) : conjClosure D.M L = L :=
  conjClosure_eq_self_of_isSimpleGroup_bar2 (S17.calLp_subset_calC D p hL) hs

theorem conjClosure_eq_and_shape_of_R17_67 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (hV : Hyp19 D V₀ V p L) (h1767 : S17.R17_67At D V₀ V) {n : ℕ}
    (hn : (IsU5 (Bar2 L) n ∧ n = 2) ∨ IsU4 (Bar2 L) n) :
    conjClosure D.M L = L ∧ (n = 2 ∨ (IsU4 (Bar2 L) n ∧ IsPowTwo n)) := by
  have hV0 : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub hV.big
  have hXmem : conjClosure D.M L ∈ S17.calL0Star D p := hV.hX
  have h67 := h1767 hV0 p hV.hp L hV.hL (conjClosure D.M L) rfl hXmem
  rcases hn with ⟨hU5, rfl⟩ | hU4
  · rcases h67 with h1 | h2 | h3 | h4 | h5
    ·
      exact ⟨conjClosure_eq_of_simple hV.hL (simple_bar2_of_isU5 h1), Or.inl rfl⟩
    ·
      obtain ⟨m, -, hU4m⟩ := h2
      have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isU4 hU4m)
      exfalso
      rw [← hXL] at hU5
      exact absurd (false_of_lieModel (t := .PSU) (n := 4) (f := m) hU4m
        S17.isChar2LieShape_PSU_four hU5
        (by rintro ⟨-, h⟩; omega)) (by simp)
    ·
      obtain ⟨m, hSp, -⟩ := h3
      have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isSp4 hSp)
      exfalso
      rw [← hXL] at hU5
      exact absurd (false_of_lieModel (t := .PSp) (n := 2) (f := m) hSp S17.isChar2LieShape_PSp hU5
        (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
    ·
      exfalso
      obtain ⟨-, m, hL2 | hSz⟩ := h4
      · exact absurd (false_of_lieModel (t := .PSL) (n := 2) (f := m) hL2
          S17.isChar2LieShape_PSL hU5
          (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
      · exact absurd (false_of_lieModel (t := .twistedB2) (n := 0) (f := m) hSz
          S17.isChar2LieShape_twistedB2 hU5
          (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
    ·
      exfalso
      obtain ⟨m, -, hL2 | hU3⟩ := h5
      · have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isL2 hL2)
        rw [← hXL] at hU5
        exact absurd (false_of_lieModel (t := .PSL) (n := 2) (f := m) hL2
          S17.isChar2LieShape_PSL hU5
          (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
      · have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isU3 hU3)
        rw [← hXL] at hU5
        exact absurd (false_of_lieModel (t := .PSU) (n := 3) (f := m) hU3 s19_shape_PSU3 hU5
          (by rintro ⟨-, h⟩; omega)) (by simp)
  · rcases h67 with h1 | h2 | h3 | h4 | h5
    ·
      have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isU5 h1)
      exfalso
      rw [← hXL] at hU4
      exact absurd (false_of_lieModel (t := .PSU) (n := 5) (f := 2) h1 s19_shape_PSU5 hU4
        (by rintro ⟨-, h⟩; omega)) (by simp)
    ·
      obtain ⟨m, hpow, hU4m⟩ := h2
      have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isU4 hU4m)
      have hU4X : IsU4 (Bar2 (conjClosure D.M L)) n := by
        rw [hXL]
        exact hU4
      have hmn : n = m :=
        (lieModel_eq_of_isChar2LieShape hU4m S17.isChar2LieShape_PSU_four hU4X).2.2
      exact ⟨hXL, Or.inr ⟨hU4, by simpa [hmn] using hpow⟩⟩
    ·
      obtain ⟨m, hSp, -⟩ := h3
      have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isSp4 hSp)
      exfalso
      rw [← hXL] at hU4
      exact absurd (false_of_lieModel (t := .PSp) (n := 2) (f := m) hSp S17.isChar2LieShape_PSp hU4
        (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
    ·
      exfalso
      obtain ⟨-, m, hL2 | hSz⟩ := h4
      · exact absurd (false_of_lieModel (t := .PSL) (n := 2) (f := m) hL2
          S17.isChar2LieShape_PSL hU4
          (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
      · exact absurd (false_of_lieModel (t := .twistedB2) (n := 0) (f := m) hSz
          S17.isChar2LieShape_twistedB2 hU4
          (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
    ·
      exfalso
      obtain ⟨m, -, hL2 | hU3⟩ := h5
      · have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isL2 hL2)
        rw [← hXL] at hU4
        exact absurd (false_of_lieModel (t := .PSL) (n := 2) (f := m) hL2
          S17.isChar2LieShape_PSL hU4
          (by rintro ⟨h, -⟩; exact absurd h (by decide))) (by simp)
      · have hXL := conjClosure_eq_of_simple hV.hL (simple_bar2_of_isU3 hU3)
        rw [← hXL] at hU4
        exact absurd (false_of_lieModel (t := .PSU) (n := 3) (f := m) hU3 s19_shape_PSU3 hU4
          (by rintro ⟨-, h⟩; omega)) (by simp)

end Certified

theorem cartanQuotient_of_bar2 {Y : Subgroup G} (Sg : Sylow 2 ↥Y)
    (hcart : ∀ S : Sylow 2 (Bar2 Y),
      IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (S : Subgroup (Bar2 Y))) ∧
        ∃ E : Subgroup (TauCeti.Subgroup.normalizerQuotient (S : Subgroup (Bar2 Y))),
          IsElemAbelian 3 E ∧ Nat.card E = 9) :
    IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (Sg : Subgroup ↥Y)) ∧
      ∃ E : Subgroup (TauCeti.Subgroup.normalizerQuotient (Sg : Subgroup ↥Y)),
        IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  let N : Subgroup ↥Y := CFSG.pCore 2 ↥Y
  have hNS : N ≤ (Sg : Subgroup ↥Y) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).le_sylow_of_normal Sg
  let Sbar : Sylow 2 (Bar2 Y) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) Sg
  have hSbarCoe : (Sbar : Subgroup (Bar2 Y)) = Sg.map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N) Sg
  let e := (CFSG.GroupTheory.normalizerQuotient_quotientEquiv N Sg hNS).trans
    (TauCeti.Subgroup.normalizerQuotientCongr hSbarCoe.symm)
  obtain ⟨hcomm, Ebar, hEbar, hEcard⟩ := hcart Sbar
  refine ⟨⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hcomm.is_comm.comm _ _)⟩⟩,
    Ebar.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hEbar e.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hEcard]

theorem cartanQuotient_of_KU4U5 {D : Data G} {L : Subgroup G} {n : ℕ}
    (hK : Inputs1719.KU4U5CartanQuotient)
    (hn : (IsU5 (Bar2 L) n ∧ n = 2) ∨ IsU4 (Bar2 L) n) (hn2 : 2 ≤ n) (hnEven : Even n)
    (hSylL : IsSylowIn 2 (D.T ⊓ L) L) :
    let Sg : Sylow 2 ↥L := hSylL.toSylow
    IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (Sg : Subgroup ↥L)) ∧
      ∃ E : Subgroup (TauCeti.Subgroup.normalizerQuotient (Sg : Subgroup ↥L)),
        IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  intro Sg
  refine cartanQuotient_of_bar2 Sg (hK (Bar2 L) n hn2 hnEven ?_)
  rcases hn with ⟨h5, rfl⟩ | h4
  · exact Or.inr h5
  · exact Or.inl ⟨n, h4, rfl⟩

theorem not_isStronglyPEmbedded_of_normalizerQuotient {D : Data G} {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) (hV0 : V₀ ≠ ⊥) (h171 : S17.R17_1At D V₀ V h125)
    {Y : Subgroup G} (hYM : Y ≤ D.M) (hTY : D.T ≤ normalizer (Y : Set G))
    (hSyl : IsSylowIn 2 (D.T ⊓ Y) Y)
    (hQcomm : ∀ a b : TauCeti.Subgroup.normalizerQuotient (hSyl.toSylow : Subgroup ↥Y),
      a * b = b * a)
    {E9 : Subgroup (TauCeti.Subgroup.normalizerQuotient (hSyl.toSylow : Subgroup ↥Y))}
    (hE9 : IsElemAbelian 3 E9) (hE9card : Nat.card E9 = 9) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  intro hstr
  let S : Subgroup G := D.T ⊓ Y
  let Sg : Sylow 2 ↥Y := hSyl.toSylow
  have hScoe : (Sg : Subgroup ↥Y) = S.subgroupOf Y := IsSylowIn.coe_toSylow hSyl
  let Q := TauCeti.Subgroup.normalizerQuotient (Sg : Subgroup ↥Y)
  let A : Subgroup Q :=
    { carrier := {x | x ^ 3 = 1}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change x ^ 3 = 1 at hx
        change y ^ 3 = 1 at hy
        change (x * y) ^ 3 = 1
        have hxy : Commute x y := hQcomm x y
        rw [hxy.mul_pow 3, hx, hy, one_mul]
      inv_mem' := by
        intro x hx
        change x ^ 3 = 1 at hx
        change (x⁻¹) ^ 3 = 1
        rw [inv_pow, hx, inv_one] }
  have hAel : IsElemAbelian 3 A := by
    refine ⟨?_, fun x hx => hx⟩
    exact ⟨⟨fun x y => Subtype.ext (hQcomm (x : Q) (y : Q))⟩⟩
  have hE9leA : E9 ≤ A := by
    intro x hx
    change x ^ 3 = 1
    exact hE9.2 x hx
  have hA9 : 9 ≤ Nat.card A := by
    rw [← hE9card]
    exact Subgroup.card_le_of_le hE9leA
  have hAnc : ¬ IsCyclic A := uc22p22n_not_isCyclic_of_card Nat.prime_three hAel hA9
  have hAp : IsPGroup 3 A := hAel.isPGroup
  let B : Subgroup ↥Y := Subgroup.normalizer (Sg : Set ↥Y)
  let Ssub : Subgroup B := (Sg : Subgroup ↥Y).subgroupOf B
  have : Ssub.Normal := Subgroup.normal_in_normalizer
  let f : B →* Q := TauCeti.Subgroup.normalizerQuotientMk (Sg : Subgroup ↥Y)
  have hSsub : IsPGroup 2 Ssub := by
    have hmap : Ssub.map B.subtype = (Sg : Subgroup ↥Y) := by
      rw [show Ssub = (Sg : Subgroup ↥Y).subgroupOf B from rfl,
        Subgroup.map_subgroupOf_eq_of_le
          (show (Sg : Subgroup ↥Y) ≤ B from Subgroup.le_normalizer)]
    exact Sg.isPGroup'.of_equiv
      ((Subgroup.equivMapOfInjective Ssub B.subtype B.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap)).symm
  have hker_eq : f.ker = Ssub :=
    TauCeti.Subgroup.normalizerQuotientMk_ker (Sg : Subgroup ↥Y)
  have hker : f.ker ≤ Ssub := le_of_eq hker_eq
  have hSmap : Ssub.map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    rw [hker_eq]
  have hperm : (A : Set Q) * (Ssub.map f : Set Q) = (Ssub.map f : Set Q) * A := by
    rw [hSmap, Subgroup.coe_bot]
    simp
  obtain ⟨E, hEp, hEmap, ⟨eEA⟩, hES⟩ :=
    CFSG.GroupTheory.exists_permutes_lift f
      (TauCeti.Subgroup.normalizerQuotientMk_surjective (Sg : Subgroup ↥Y))
      hSsub hker (p := 3) (by norm_num) hAp hperm
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have h2 : (⟨x, hx⟩ : E) ^ 3 = 1 := by
      have hA : (eEA ⟨x, hx⟩ : A) ^ 3 = 1 :=
        Subtype.ext (hAel.2 (eEA ⟨x, hx⟩) (eEA ⟨x, hx⟩).2)
      have h' := congrArg (fun z : A => eEA.symm z) hA
      rw [map_one] at h'
      simpa using h'
    simpa [Subgroup.coe_pow] using congrArg (fun z : E => (z : B)) h2
  have hEnc : ¬ IsCyclic E := by
    intro hcyc
    exact hAnc (isCyclic_of_surjective eEA.toMonoidHom eEA.surjective)
  let E1 : Subgroup B := A.comap f
  have hE1eq : E1 = E ⊔ Ssub := by
    calc E1 = (E.map f).comap f := by rw [hEmap]
      _ = E ⊔ f.ker := Subgroup.comap_map_eq f E
      _ = E ⊔ Ssub := by
          rw [show f.ker = Ssub from TauCeti.Subgroup.normalizerQuotientMk_ker (Sg : Subgroup ↥Y)]
  have hE1set : (E1 : Set B) = (E : Set B) * (Ssub : Set B) := by
    calc (E1 : Set B) = ((E ⊔ Ssub : Subgroup B) : Set B) := by rw [hE1eq]
      _ = ((Ssub ⊔ E : Subgroup B) : Set B) := by rw [sup_comm]
      _ = (Ssub : Set B) * (E : Set B) := Subgroup.normal_mul Ssub E
      _ = (E : Set B) * (Ssub : Set B) := hES.symm
  let ι : B →* G := Y.subtype.comp B.subtype
  let EG : Subgroup G := E.map ι
  let SG : Subgroup G := Ssub.map ι
  let E1G : Subgroup G := E1.map ι
  have hι : Function.Injective ι := by
    simpa [ι] using Y.subtype_injective.comp B.subtype_injective
  have hSG_eq : SG = S := by
    calc SG = (Ssub.map B.subtype).map Y.subtype := by
          dsimp only [SG, ι]
          rw [Subgroup.map_map]
      _ = (Sg : Subgroup ↥Y).map Y.subtype := by
          rw [show Ssub.map B.subtype = (Sg : Subgroup ↥Y) from by
            rw [show Ssub = (Sg : Subgroup ↥Y).subgroupOf B from rfl,
              Subgroup.map_subgroupOf_eq_of_le
                (show (Sg : Subgroup ↥Y) ≤ B from Subgroup.le_normalizer)]]
      _ = (S.subgroupOf Y).map Y.subtype := by rw [hScoe]
      _ = S := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hSG_le_T : SG ≤ D.T := by
    rw [hSG_eq]
    exact inf_le_left
  have hE1Gset : (E1G : Set G) = (EG : Set G) * (SG : Set G) := by
    calc (E1G : Set G) = ι '' (E1 : Set B) := Subgroup.coe_map ι E1
      _ = ι '' ((E : Set B) * (Ssub : Set B)) := by rw [hE1set]
      _ = (ι '' (E : Set B)) * (ι '' (Ssub : Set B)) := Set.image_mul ι
      _ = (EG : Set G) * (SG : Set G) := by rw [Subgroup.coe_map, Subgroup.coe_map]
  have hEGSG : (EG : Set G) * (SG : Set G) = (SG : Set G) * (EG : Set G) := by
    dsimp only [EG, SG]
    rw [Subgroup.coe_map, Subgroup.coe_map]
    calc (ι '' (E : Set B)) * (ι '' (Ssub : Set B))
        = ι '' ((E : Set B) * (Ssub : Set B)) := (Set.image_mul ι).symm
      _ = ι '' ((Ssub : Set B) * (E : Set B)) := by rw [hES]
      _ = (ι '' (Ssub : Set B)) * (ι '' (E : Set B)) := Set.image_mul ι
  have hT_S : D.T ≤ Subgroup.normalizer (S : Set G) := by
    have h1 : D.T ≤ Subgroup.normalizer (D.T : Set G) := Subgroup.le_normalizer
    exact (le_inf h1 hTY).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hB_eq : B = (Subgroup.normalizer (S : Set G)).subgroupOf Y := by
    rw [Subgroup.subgroupOf_normalizer_eq inf_le_right]
    rfl
  have hSg_mem : ∀ y : ↥Y, y ∈ Sg ↔ (y : G) ∈ S := by
    intro y
    change y ∈ (S.subgroupOf Y) ↔ (y : G) ∈ S
    exact Subgroup.mem_subgroupOf
  have hx3S_of_mem : ∀ x ∈ E1G, x ^ 3 ∈ S := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
    have hbA : f b ∈ A := by
      have := hb
      rwa [show E1 = A.comap f from rfl, Subgroup.mem_comap] at this
    have hb3ker : (b : B) ^ 3 ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hbA
    have hb3Ssub : (b : B) ^ 3 ∈ Ssub := by
      rwa [hker_eq] at hb3ker
    have hb3Sg : (((b : B) ^ 3 : B) : ↥Y) ∈ Sg := by
      change (((b : B) ^ 3 : B) : ↥Y) ∈ Sg
      exact hb3Ssub
    have hb3S : ((((b : B) ^ 3 : B) : ↥Y) : G) ∈ S := (hSg_mem _).mp hb3Sg
    simpa [ι] using hb3S
  have hforward : ∀ t ∈ D.T, ∀ x ∈ E1G, t * x * t⁻¹ ∈ E1G := by
    intro t ht x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
    have htY : t ∈ Subgroup.normalizer (Y : Set G) := hTY ht
    have htS : t ∈ Subgroup.normalizer (S : Set G) := hT_S ht
    have hbS : (((b : B) : ↥Y) : G) ∈ Subgroup.normalizer (S : Set G) := by
      have hbB' : ((b : B) : ↥Y) ∈
          (Subgroup.normalizer (S : Set G)).subgroupOf Y := by
        rw [← hB_eq]
        exact b.2
      rw [Subgroup.mem_subgroupOf] at hbB'
      exact hbB'
    have hx3S : (((b : B) : ↥Y) : G) ^ 3 ∈ S :=
      hx3S_of_mem _ (Subgroup.mem_map_of_mem ι hb)
    have hyY : t * (((b : B) : ↥Y) : G) * t⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp htY _).mp ((b : B) : ↥Y).2
    let y : ↥Y := ⟨t * (((b : B) : ↥Y) : G) * t⁻¹, hyY⟩
    have hyNS : (y : G) ∈ Subgroup.normalizer (S : Set G) := by
      have h : t * (((b : B) : ↥Y) : G) * t⁻¹ ∈
          Subgroup.normalizer (S : Set G) :=
        (Subgroup.normalizer (S : Set G)).mul_mem
          ((Subgroup.normalizer (S : Set G)).mul_mem htS hbS)
          ((Subgroup.normalizer (S : Set G)).inv_mem htS)
      simpa [y] using h
    have hyB : y ∈ B := by
      rw [hB_eq, Subgroup.mem_subgroupOf]
      exact hyNS
    have hy3S : (y : G) ^ 3 ∈ S := by
      have hy3eq : (y : G) ^ 3 = t * (((b : B) : ↥Y) : G) ^ 3 * t⁻¹ := by
        simp only [y, Subgroup.coe_mk]
        rw [show t * (((b : B) : ↥Y) : G) * t⁻¹ =
          MulAut.conj t (((b : B) : ↥Y) : G) from by simp [MulAut.conj_apply]]
        rw [← map_pow]
        simp [MulAut.conj_apply]
      rw [hy3eq]
      exact (Subgroup.mem_normalizer_iff.mp htS _).mp hx3S
    have hy3Ssub : (⟨y, hyB⟩ : B) ^ 3 ∈ Ssub := by
      change ((((⟨y, hyB⟩ : B) ^ 3 : B) : ↥Y)) ∈ Sg
      exact (hSg_mem _).mpr (by simpa using hy3S)
    have hyE1 : (⟨y, hyB⟩ : B) ∈ E1 := by
      rw [show E1 = A.comap f from rfl, Subgroup.mem_comap]
      change (f ⟨y, hyB⟩) ^ 3 = 1
      rw [← map_pow]
      change ((⟨y, hyB⟩ : B) ^ 3) ∈ f.ker
      rw [hker_eq]
      exact hy3Ssub
    exact Subgroup.mem_map.mpr ⟨⟨y, hyB⟩, hyE1, by simp [ι, y]⟩
  have hT_E1G : D.T ≤ Subgroup.normalizer (E1G : Set G) :=
    Subgroup.le_normalizer_iff.2 hforward
  have hpermE1 : (E1G : Set G) * (D.T : Set G) = (D.T : Set G) * (E1G : Set G) :=
    (Subgroup.set_mul_normalizer_comm (D.T : Set G) E1G hT_E1G).symm
  have hST : (SG : Set G) * (D.T : Set G) = D.T := by
    apply Set.Subset.antisymm
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      exact D.T.mul_mem (hSG_le_T hs) ht
    · intro t ht
      exact ⟨1, SG.one_mem, t, ht, by simp⟩
  have hTS : (D.T : Set G) * (SG : Set G) = D.T := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, ht, s, hs, rfl⟩
      exact D.T.mul_mem ht (hSG_le_T hs)
    · intro t ht
      exact ⟨t, ht, 1, SG.one_mem, by simp⟩
  have hpermEG : (EG : Set G) * (D.T : Set G) = (D.T : Set G) * (EG : Set G) := by
    calc (EG : Set G) * (D.T : Set G)
        = (EG : Set G) * ((SG : Set G) * (D.T : Set G)) := by rw [hST]
      _ = ((EG : Set G) * (SG : Set G)) * (D.T : Set G) := by rw [mul_assoc]
      _ = (E1G : Set G) * (D.T : Set G) := by rw [hE1Gset]
      _ = (D.T : Set G) * (E1G : Set G) := hpermE1
      _ = (D.T : Set G) * ((EG : Set G) * (SG : Set G)) := by rw [hE1Gset]
      _ = (D.T : Set G) * ((SG : Set G) * (EG : Set G)) := by rw [hEGSG]
      _ = ((D.T : Set G) * (SG : Set G)) * (EG : Set G) := by rw [mul_assoc]
      _ = (D.T : Set G) * (EG : Set G) := by rw [hTS]
  have hEM : EG ≤ D.M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
    exact hYM ((b : B) : ↥Y).2
  have hEpEG : IsPGroup 3 EG := hEp.map ι
  have hexpEG : ∀ x ∈ EG, x ^ 3 = 1 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
    have hxeq : ι b = (((b : B) : ↥Y) : G) := rfl
    rw [hxeq]
    simpa [Subgroup.coe_pow] using
      congrArg (fun z : B => (((z : ↥Y) : G))) (hexpE b hb)
  have hEncEG : ¬ IsCyclic EG := by
    intro hcyc
    have eEG := Subgroup.equivMapOfInjective E ι hι
    exact hEnc (isCyclic_of_surjective eEG.symm eEG.symm.surjective)
  have hP11 : F11.InP11 D EG :=
    inP11_of_strongly (p := 3) (by norm_num) (by norm_num) hstr hEM hEpEG hexpEG hEncEG
      hpermEG
  have hPStar : InPStar D V₀ EG := (inPStar_iff_of_ne_bot hV0 EG).mpr hP11
  exact h171.1 EG hPStar

theorem hyp19_v0_le_pCore {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp19 D V₀ V p L) : V₀ ≤ pCoreOf 2 D.M := by
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.big
  have hV0 : InCalV D.M V₀ := by
    rcases h.hyp125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact absurd h0 hne
    · exact h0.1
  obtain ⟨-, hV0M, hV0N, hV0el⟩ := hV0
  exact CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hV0M
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hV0M).2 hV0N) hV0el.isPGroup

theorem not_isStronglyPEmbedded_of_KU4U5 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (hV : Hyp19 D V₀ V p L) (hV0 : V₀ ≠ ⊥)
    (h171 : S17.R17_1At D V₀ V hV.hyp125)
    (hXL : conjClosure D.M L = L)
    (hK : Inputs1719.KU4U5CartanQuotient) {n : ℕ}
    (hn : (IsU5 (Bar2 L) n ∧ n = 2) ∨ IsU4 (Bar2 L) n)
    (hn2 : 2 ≤ n) (hnEven : Even n) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hLM : L ≤ D.M := (S17.calLp_subset_calC D p hV.hL).1.le
  have hLn : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 (by
      rw [← hXL]
      exact TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hTM : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hSylL : IsSylowIn 2 (D.T ⊓ L) L := hTM.inf_normal hLM hLn
  have hTY : D.T ≤ normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLn)
  obtain ⟨hQcomm, E9, hE9, hE9card⟩ := cartanQuotient_of_KU4U5 hK hn hn2 hnEven hSylL
  exact not_isStronglyPEmbedded_of_normalizerQuotient hV.hyp125 hV0 h171 hLM hTY hSylL
    hQcomm.is_comm.comm hE9 hE9card

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
