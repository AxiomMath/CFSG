module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

private lemma spUFix_congr_conj {L L' : Type} [Group L] [Group L'] (φ : L ≃* L') (g : L) :
    MulAut.congr φ (MulAut.conj g) = MulAut.conj (φ g) := by
  ext y
  simp [MulAut.congr]

private lemma spUFix_congr_symm_conj {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (x' : L') : MulAut.congr φ.symm (MulAut.conj x') = MulAut.conj (φ.symm x') := by
  ext y
  simp [MulAut.congr]

private lemma spUFix_congr_symm_congr {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (α : MulAut L) : MulAut.congr φ.symm (MulAut.congr φ α) = α := by
  ext y
  simp [MulAut.congr]

private lemma spUFix_map_symm_map {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (A : Subgroup L) : (A.map φ.toMonoidHom).map φ.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have h : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id L := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private lemma spUFix_map_symm_map' {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (A : Subgroup L') : (A.map φ.symm.toMonoidHom).map φ.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have h : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id L' := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private lemma spUFix_map_map_congr {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (α : MulAut L) (K : Subgroup L) :
    (K.map φ.toMonoidHom).map (MulAut.congr φ α).toMonoidHom
      = (K.map α.toMonoidHom).map φ.toMonoidHom := by
  have hhom : (MulAut.congr φ α).toMonoidHom.comp φ.toMonoidHom
      = φ.toMonoidHom.comp α.toMonoidHom := by
    ext y
    simp [MulAut.congr]
  simp only [Subgroup.map_map]
  rw [hhom]

private lemma spUFix_conjSubgroup_map {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (K : Subgroup L) (g : L) :
    conjSubgroup (K.map φ.toMonoidHom) (φ g) = (conjSubgroup K g).map φ.toMonoidHom := by
  have hhom : (MulAut.conj ((φ g)⁻¹)).toMonoidHom.comp φ.toMonoidHom
      = φ.toMonoidHom.comp (MulAut.conj (g⁻¹)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply]
  unfold conjSubgroup
  simp only [Subgroup.map_map]
  rw [hhom]

private lemma spUFix_conjSubgroup_map_symm {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    (A : Subgroup L) (x' : L') :
    (conjSubgroup (A.map φ.toMonoidHom) x').map φ.symm.toMonoidHom
      = conjSubgroup A (φ.symm x') := by
  have hf : conjSubgroup (A.map φ.toMonoidHom) x'
      = (conjSubgroup A (φ.symm x')).map φ.toMonoidHom := by
    simpa using spUFix_conjSubgroup_map φ A (φ.symm x')
  calc (conjSubgroup (A.map φ.toMonoidHom) x').map φ.symm.toMonoidHom
      = ((conjSubgroup A (φ.symm x')).map φ.toMonoidHom).map φ.symm.toMonoidHom := by
        rw [hf]
    _ = conjSubgroup A (φ.symm x') := spUFix_map_symm_map φ _

private lemma spUFix_rootGroupsIn_map_mem {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    {R Sy : Subgroup L} {X' : Subgroup L'}
    (hX' : X' ∈ rootGroupsIn (R.map φ.toMonoidHom) (Sy.map φ.toMonoidHom)) :
    X'.map φ.symm.toMonoidHom ∈ rootGroupsIn R Sy := by
  obtain ⟨hconj, hle⟩ := hX'
  obtain ⟨x', hx'⟩ := hconj
  refine ⟨⟨φ.symm x', ?_⟩, ?_⟩
  · rw [hx']
    exact spUFix_conjSubgroup_map_symm φ R x'
  · calc X'.map φ.symm.toMonoidHom
        ≤ (Sy.map φ.toMonoidHom).map φ.symm.toMonoidHom := Subgroup.map_mono hle
      _ = Sy := spUFix_map_symm_map φ Sy

theorem spUFixConclusion_of_mulEquiv {L L' : Type} [Group L] [Group L'] (φ : L ≃* L')
    {R Sy : Subgroup L}
    (h : SpUFixConclusion L' (R.map φ.toMonoidHom) (Sy.map φ.toMonoidHom)) :
    SpUFixConclusion L R Sy := by
  intro α g hg hg2 hα2 hαg hαSy hαR hfix
  let α' : MulAut L' := MulAut.congr φ α
  let g' : L' := φ g
  have hα'm : α' = MulAut.congr φ α := rfl
  have hg'm : g' = φ g := rfl
  have hg'mem : g' ∈ Sy.map φ.toMonoidHom := by
    rw [hg'm]
    exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  have hg'2 : g' * g' = 1 := by
    rw [hg'm, ← map_mul, hg2, map_one]
  have hα'2 : α' * α' = 1 := by
    rw [hα'm, ← map_mul, hα2, map_one]
  have hconj : MulAut.conj g' = MulAut.congr φ (MulAut.conj g) := by
    rw [hg'm]
    exact (spUFix_congr_conj φ g).symm
  have hcomm : α' * MulAut.conj g' = MulAut.conj g' * α' := by
    calc α' * MulAut.conj g'
        = MulAut.congr φ (α * MulAut.conj g) := by rw [hα'm, hconj, ← map_mul]
      _ = MulAut.congr φ (MulAut.conj g * α) := by rw [hαg]
      _ = MulAut.conj g' * α' := by rw [hα'm, hconj, map_mul]
  have hmapSy : Subgroup.map α'.toMonoidHom (Sy.map φ.toMonoidHom)
      = Sy.map φ.toMonoidHom := by
    rw [hα'm, spUFix_map_map_congr, hαSy]
  have hmapR : Subgroup.map α'.toMonoidHom (R.map φ.toMonoidHom)
      = R.map φ.toMonoidHom := by
    rw [hα'm, spUFix_map_map_congr, hαR]
  have hfix' : ∀ X' ∈ rootGroupsIn (R.map φ.toMonoidHom) (Sy.map φ.toMonoidHom),
      Subgroup.map α'.toMonoidHom X' = X' ↔ conjSubgroup X' g' = X' := by
    intro X' hX'
    let X : Subgroup L := X'.map φ.symm.toMonoidHom
    have hXm : X = X'.map φ.symm.toMonoidHom := rfl
    have hXmem : X ∈ rootGroupsIn R Sy := by
      rw [hXm]
      exact spUFix_rootGroupsIn_map_mem φ hX'
    have hXmap : X.map φ.toMonoidHom = X' := by
      rw [hXm]
      exact spUFix_map_symm_map' φ X'
    have hmapinj : Function.Injective (Subgroup.map φ.toMonoidHom) :=
      Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    have hαX : Subgroup.map α'.toMonoidHom X'
        = (Subgroup.map α.toMonoidHom X).map φ.toMonoidHom := by
      rw [hα'm, ← hXmap]
      exact spUFix_map_map_congr φ α X
    have hcX : conjSubgroup X' g' = (conjSubgroup X g).map φ.toMonoidHom := by
      rw [← hXmap, hg'm]
      exact spUFix_conjSubgroup_map φ X g
    rw [hαX, hcX, ← hXmap]
    simp only [hmapinj.eq_iff]
    exact hfix X hXmem
  obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp
    (h α' g' hg'mem hg'2 hα'2 hcomm hmapSy hmapR hfix')
  refine ⟨φ.symm x', ?_⟩
  have h1 : MulAut.congr φ.symm (MulAut.conj x') = MulAut.conj (φ.symm x') :=
    spUFix_congr_symm_conj φ x'
  have h2 : MulAut.congr φ.symm α' = α := by
    rw [hα'm]
    exact spUFix_congr_symm_congr φ α
  rw [← h1, hx', h2]

end CFSG.LocalAnalysis.WeakClosure81

end
