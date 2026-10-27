module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecJ
public import CFSG.LocalAnalysis.SectionRank.SQTKTransport

public section

namespace CFSG.Quasithin.H13.P31Sec

section Map

variable {S : Type} [Group S] {Q : Type} [Group Q]

theorem allNS_of_map_solvable (N : Subgroup Q) [N.Normal] (hN : Group.IsSolvable ↥N)
    (Y : Subgroup Q) (h : AllNS S ↥(Y.map (QuotientGroup.mk' N))) : AllNS S ↥Y := by
  let φ : ↥Y →* Q ⧸ N := (QuotientGroup.mk' N).comp Y.subtype
  have hrange : φ.range = Y.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Group.IsSolvable ↥φ.ker := by
    let f : ↥φ.ker →* ↥N :=
      { toFun := fun x => ⟨((x : ↥Y) : Q), (QuotientGroup.eq_one_iff _).1 x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
    have h := congrArg (fun x : ↥N => (x : Q)) hab
    exact Subtype.ext (Subtype.ext h)
  exact AllNS.of_range_solvable_ker φ hker (AllNS.of_mulEquiv (MulEquiv.subgroupCongr hrange.symm) h)

end Map

@[expose] def SimpleSectionSQT : Prop :=
  ∀ {X : Type} [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
    ∀ (H : Subgroup X) (N : Subgroup ↥H) [N.Normal] [IsSimpleGroup (↥H ⧸ N)],
      (∃ a b : ↥H ⧸ N, a * b ≠ b * a) → CFSG.IsStronglyQuasithin (↥H ⧸ N)

theorem isStronglyQuasithin_of_simple_image (hSec : SimpleSectionSQT) {Q : Type} [Group Q]
    [Finite Q] (hQ : CFSG.SectionRank.IsSQTKCat Q) (Y : Subgroup Q) {W : Type} [Group W]
    [hW : IsSimpleGroup W] (hnab : ∃ a b : W, a * b ≠ b * a) (φ : ↥Y →* W)
    (hφ : Function.Surjective φ) : CFSG.IsStronglyQuasithin W := by
  haveI : φ.ker.Normal := φ.normal_ker
  let e : (↥Y ⧸ φ.ker) ≃* W := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  haveI : IsSimpleGroup (↥Y ⧸ φ.ker) := e.isSimpleGroup
  have h := hSec hQ Y φ.ker (by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩)
  haveI : Finite W := Finite.of_surjective φ hφ
  exact CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm h

end CFSG.Quasithin.H13.P31Sec
