module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Sect
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Bender

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {Y : Type} [Group Y] [Finite Y]

theorem isSolvable_quotient_subgroupOf {E : Subgroup Y} [E.Normal]
    (hq : Group.IsSolvable (Y ⧸ E)) (X : Subgroup Y) :
    Group.IsSolvable (↥X ⧸ E.subgroupOf X) := by
  let φ : ↥X →* Y ⧸ E := (QuotientGroup.mk' E).comp X.subtype
  have hker : φ.ker = E.subgroupOf X := by
    ext x
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  haveI : Group.IsSolvable (↥X ⧸ φ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective φ)
  exact Group.isSolvable_of_surjective (f := (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom)
    (QuotientGroup.quotientMulEquivOfEq hker).surjective

theorem isCompositionFactor_subgroupOf_of_isSolvable_quot {E : Subgroup Y} [E.Normal]
    (hq : Group.IsSolvable (Y ⧸ E)) {X : Subgroup Y} {L : Type} [Group L]
    (h : E1.IsCompositionFactor ↥X L) (hnab : ∃ a b : L, a * b ≠ b * a) :
    E1.IsCompositionFactor ↥(E.subgroupOf X) L := by
  haveI : (E.subgroupOf X).Normal := Subgroup.normal_subgroupOf
  rcases isCompositionFactor_of_normal (E.subgroupOf X) h with h1 | h2
  · exact h1
  · exfalso
    haveI := isSolvable_quotient_subgroupOf hq X
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      inferInstance h2 a b)

@[expose] def subgroupOfToNormal (E X : Subgroup Y) : ↥(E.subgroupOf X) →* ↥E where
  toFun x := ⟨((x : ↥X) : Y), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem subgroupOfToNormal_injective (E X : Subgroup Y) :
    Function.Injective (subgroupOfToNormal E X) := fun x y hxy => by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ↥E => (z : Y)) hxy

theorem not_hasCompFactor_of_sectionalTwoRankLE_two {Q : Type} [Group Q] [Finite Q]
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    (X : Subgroup Q) (hX : CFSG.GH74.SectionalTwoRankLE ↥X 2) : ¬ HasCompFactor X P := by
  rintro ⟨L, _, hcf, hL⟩
  haveI : Finite L := isCompositionFactor_finite hcf
  obtain ⟨N, M, hNM, -, -, -, -, ⟨e⟩⟩ := hcf
  haveI := hNM
  exact hP L hL
    (CFSG.GH74.SectionalTwoRankLE.of_mulEquiv e (sectionalTwoRankLE_section hX M (N.subgroupOf M)))

theorem not_hasCompFactor_of_sectionalTwoRankLE {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {E : Subgroup Y} [E.Normal] (hq : Group.IsSolvable (Y ⧸ E))
    (hE : CFSG.GH74.SectionalTwoRankLE ↥E 2) (X : Subgroup Y) : ¬ HasCompFactor X P := by
  rintro ⟨L, _, hcf, hL⟩
  haveI : Finite L := isCompositionFactor_finite hcf
  have h1 := isCompositionFactor_subgroupOf_of_isSolvable_quot hq hcf (hP L hL).1
  have hS : CFSG.GH74.SectionalTwoRankLE ↥(E.subgroupOf X) 2 :=
    CFSG.GH74.SectionalTwoRankLE.of_injective _ (subgroupOfToNormal_injective E X) hE
  exact not_hasCompFactor_of_sectionalTwoRankLE_two (fun L _ _ h => (hP L h).2)
    (⊤ : Subgroup ↥(E.subgroupOf X)) (CFSG.GH74.SectionalTwoRankLE.subgroup ⊤ hS)
    ⟨L, inferInstance, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      Subgroup.topEquiv).2 h1, hL⟩

theorem not_hasCompFactor_isCalL1_of_sectionalTwoRankLE {E : Subgroup Y} [E.Normal]
    (hq : Group.IsSolvable (Y ⧸ E)) (hE : CFSG.GH74.SectionalTwoRankLE ↥E 2) (X : Subgroup Y) :
    ¬ HasCompFactor X IsCalL1 :=
  not_hasCompFactor_of_sectionalTwoRankLE
    (fun _ _ _ hL => ⟨exists_mul_ne_of_isCalL1 hL, not_sectionalTwoRankLE_two_of_isCalL1 hL⟩)
    hq hE X

theorem isCompositionFactor_of_bender {E : Subgroup Y} [E.Normal]
    (hB : fusionIsBenderGroup ↥E) (hq : Group.IsSolvable (Y ⧸ E)) {T X : Subgroup Y}
    (hT : IsSylowIn 2 T ⊤) (hTX : T ≤ X) {L : Type} [Group L] (hcf : E1.IsCompositionFactor ↥X L)
    (hL : IsCalL1 L) : E1.IsCompositionFactor Y L := by
  haveI : Finite L := isCompositionFactor_finite hcf
  have hnab := exists_mul_ne_of_isCalL1 hL
  rcases isSolvable_or_le_of_bender hB hq hT hTX with hs | hEX
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      hs hcf a b)
  · have h1 := isCompositionFactor_subgroupOf_of_isSolvable_quot hq hcf hnab
    have h2 : E1.IsCompositionFactor ↥E L :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hEX)).1 h1
    exact kbr_isCompositionFactor_of_normal_subgroup E h2

theorem lGen_eq_top_of_not_hasUniqueMaxOver {P : ∀ (X : Type) [Group X], Prop} {T : Subgroup Y}
    (hall : ∀ X : Subgroup Y, T ≤ X → X < ⊤ → ¬ HasCompFactor X P) (hT : T < ⊤)
    (hnu : ¬ HasUniqueMaxOver T) : lGen P ⊤ T = ⊤ := by
  by_contra hne
  have hlt : lGen P ⊤ T < ⊤ := lt_top_iff_ne_top.2 hne
  refine hnu ⟨lGen P ⊤ T, hlt, fun X hTX hX => ?_⟩
  exact le_iSup₂_of_le X ⟨hTX, hX, hall X hTX hX⟩ le_rfl

end CFSG.LocalAnalysis.WeakClosure81

end
