module

public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.RestrictedPreimageSylow

theorem exists_lift
    {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (C Q : Subgroup G) (himage : C.map f = ⊤)
    (hQp : IsPGroup p Q) (hQC : Q ≤ C) (hQker : Q ≤ f.ker)
    (hmax : ∀ T : Subgroup G, T ≤ f.ker → IsPGroup p T → T ≤ Q)
    (V : Subgroup H) (hV : IsPGroup p V) :
    ∃ B : Subgroup G, IsPGroup p B ∧ Q ≤ B ∧ B ≤ C ∧
      B.map f = V ∧ B ⊓ f.ker = Q := by
  let fC : C →* H := f.comp C.subtype
  have hfC : Function.Surjective fC := by
    intro h
    have hh : h ∈ C.map f := by rw [himage]; trivial
    obtain ⟨g, hg, he⟩ := hh
    exact ⟨⟨g, hg⟩, he⟩
  let L := V.comap fC
  let QC := Q.subgroupOf C
  have hQCL : QC ≤ L := by
    intro q hq
    change f q.val ∈ V
    have hz : f q.val = 1 := hQker hq
    rw [hz]
    exact V.one_mem
  have hQCp : IsPGroup p QC := hQp.comap_subtype
  have hQLp : IsPGroup p (QC.subgroupOf L) := hQCp.comap_subtype
  obtain ⟨P, hP⟩ := hQLp.exists_le_sylow
  let BC := SylowPreimageNormalizer.ambient fC V P
  let B := BC.map C.subtype
  have hBCp : IsPGroup p BC := P.isPGroup'.map L.subtype
  have hBp : IsPGroup p B := hBCp.map C.subtype
  have hQB : Q ≤ B := by
    intro q hq
    let qC : C := ⟨q, hQC hq⟩
    have hqQC : qC ∈ QC := hq
    exact ⟨qC, ⟨⟨qC, hQCL hqQC⟩, hP hqQC, rfl⟩, rfl⟩
  have hBC : B ≤ C := by
    rintro b ⟨c, hc, rfl⟩
    exact c.property
  have hmap : B.map f = V := by
    change (BC.map C.subtype).map f = V
    rw [Subgroup.map_map]
    exact SylowPreimageNormalizer.ambient_map fC hfC V hV P
  have hker : B ⊓ f.ker = Q := le_antisymm
    (hmax (B ⊓ f.ker) inf_le_right hBp.to_inf_left)
    (le_inf hQB hQker)
  exact ⟨B, hBp, hQB, hBC, hmap, hker⟩

end FiveTransitive.RestrictedPreimageSylow

end CFSG
