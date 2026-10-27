module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartOne.FIVES

variable {J : Type} [Group J] [Finite J]

@[expose] noncomputable def quotAut (γ : MulAut J) : MulAut (J ⧸ Subgroup.center J) :=
  QuotientGroup.congr (Subgroup.center J) (Subgroup.center J) γ (Subgroup.map_center_eq γ)

omit [Finite J] in
@[simp] theorem quotAut_mk (γ : MulAut J) (x : J) :
    quotAut γ (QuotientGroup.mk x) = QuotientGroup.mk (γ x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem exists_lift_two_subgroup (Q : Subgroup (J ⧸ Subgroup.center J)) (hQ : IsPGroup 2 Q) :
    ∃ U : Subgroup J, IsPGroup 2 U ∧ U.map (QuotientGroup.mk' (Subgroup.center J)) = Q ∧
      ∀ γ : MulAut J, (Q.comap (QuotientGroup.mk' (Subgroup.center J))).map γ.toMonoidHom =
        Q.comap (QuotientGroup.mk' (Subgroup.center J)) → U.map γ.toMonoidHom = U := by
  classical
  set π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J) with hπ
  set R : Subgroup J := Q.comap π with hR
  let fR : ↥R →* ↥Q := (π.comp R.subtype).codRestrict Q (fun x => x.2)
  have hfR_coe : ∀ x : ↥R, ((fR x : ↥Q) : J ⧸ Subgroup.center J) = π (x : J) := fun x => rfl
  have hfR_surj : Function.Surjective fR := by
    intro q
    obtain ⟨j, hj⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) (q : J ⧸ Subgroup.center J)
    have hjR : j ∈ R := by
      rw [hR, Subgroup.mem_comap]
      rw [hπ]
      show QuotientGroup.mk' (Subgroup.center J) j ∈ Q
      rw [hj]
      exact q.2
    exact ⟨⟨j, hjR⟩, Subtype.ext hj⟩
  have hfR_ker : fR.ker ≤ Subgroup.center ↥R := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : π (x : J) = 1 := by
      have := congrArg (fun y : ↥Q => (y : J ⧸ Subgroup.center J)) hx
      simpa [hfR_coe] using this
    have h2 : (x : J) ∈ Subgroup.center J := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp h2) (y : J))
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have : Group.IsNilpotent ↥R := Subgroup.isNilpotent_of_ker_le_center fR hfR_ker
  let P₂ : Sylow 2 ↥R := Sylow.nonempty.some
  have hPchar : (P₂ : Subgroup ↥R).Characteristic :=
    Sylow.characteristic_of_normal P₂ inferInstance
  refine ⟨(P₂ : Subgroup ↥R).map R.subtype, P₂.isPGroup'.map _, ?_, ?_⟩
  · apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact y.2
    · intro q hq
      let Q₂ : Sylow 2 ↥Q := P₂.mapSurjective hfR_surj
      have hQ₂ : (Q₂ : Subgroup ↥Q) = ⊤ := by
        have := Q₂.is_maximal' (Q := ⊤) (hQ.to_subgroup ⊤) le_top
        exact this.symm
      have hmem : (⟨q, hq⟩ : ↥Q) ∈ (P₂ : Subgroup ↥R).map fR := by
        have : (⟨q, hq⟩ : ↥Q) ∈ (Q₂ : Subgroup ↥Q) := by rw [hQ₂]; exact Subgroup.mem_top _
        simpa [Q₂] using this
      obtain ⟨x, hxP, hxq⟩ := Subgroup.mem_map.mp hmem
      refine Subgroup.mem_map.mpr ⟨(x : J), Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩, ?_⟩
      have := congrArg (fun y : ↥Q => (y : J ⧸ Subgroup.center J)) hxq
      simpa [hfR_coe] using this
  · intro γ hγ
    let γR : ↥R ≃* ↥R := (γ.subgroupMap R).trans (MulEquiv.subgroupCongr hγ)
    have hγR : ∀ x : ↥R, ((γR x : ↥R) : J) = γ (x : J) := fun x => rfl
    have h1 := Subgroup.characteristic_iff_map_eq.mp hPchar γR
    have hcomp : γ.toMonoidHom.comp R.subtype = R.subtype.comp γR.toMonoidHom := by
      ext x
      exact (hγR x).symm
    calc ((P₂ : Subgroup ↥R).map R.subtype).map γ.toMonoidHom
        = (P₂ : Subgroup ↥R).map (γ.toMonoidHom.comp R.subtype) := Subgroup.map_map _ _ _
      _ = (P₂ : Subgroup ↥R).map (R.subtype.comp γR.toMonoidHom) := by rw [hcomp]
      _ = ((P₂ : Subgroup ↥R).map γR.toMonoidHom).map R.subtype := (Subgroup.map_map _ _ _).symm
      _ = (P₂ : Subgroup ↥R).map R.subtype := by rw [h1]

end CFSG.RankThree.PartOne.FIVES
