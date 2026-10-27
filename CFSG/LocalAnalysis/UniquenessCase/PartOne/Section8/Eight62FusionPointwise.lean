module

public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem exists_mem_forall_aux
    {G : Type} [Group G] [Finite G] {M P Z X : Subgroup G}
    (hmax : CFSG.Open.rankThreeIsMaxTwoLocal M) (hPp : IsPGroup 3 P)
    (hZP : Z ≤ P) (hZcent : Z ≤ (Subgroup.center ↥P).map P.subtype)
    (hZU : Z ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M)
    (hX : X ≤ P) {g : G} (hg : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ P) :
    ∃ c ∈ Subgroup.centralizer (X.map (MulAut.conj g⁻¹).toMonoidHom : Set G), g * c ∈ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Xg : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom
  let H : Subgroup G := Subgroup.centralizer (Xg : Set G)
  have hZcomm : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z := by
    intro z hz p hp
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp (hZcent hz)
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (⟨p, hp⟩ : ↥P))).symm
  have hZgH : Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    change (MulAut.conj g⁻¹) z ∈ Subgroup.centralizer (Xg : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    have h := congrArg (MulAut.conj g⁻¹) (hZcomm z hz x0 (hX hx0))
    simpa [map_mul] using h.symm
  have hZCH : Z ≤ P ⊓ H := by
    refine le_inf hZP ?_
    intro z hz
    change z ∈ Subgroup.centralizer (Xg : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hZcomm z hz x (hg hx)).symm
  have hCH3 : IsPGroup 3 ((P ⊓ H).subgroupOf H) :=
    (hPp.to_inf_left (K := H)).comap_subtype
  obtain ⟨Qh, hCHQh⟩ := hCH3.exists_le_sylow
  let Q : Subgroup G := (Qh : Subgroup H).map H.subtype
  have hCQ : P ⊓ H ≤ Q := by
    calc P ⊓ H = ((P ⊓ H).subgroupOf H).map H.subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
      _ ≤ (Qh : Subgroup H).map H.subtype := Subgroup.map_mono hCHQh
  have hZQ : Z ≤ Q := hZCH.trans hCQ
  have hQ3 : IsPGroup 3 Q := Qh.isPGroup'.map H.subtype
  have hQM : Q ≤ M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      hmax hZU hZQ hQ3
  have hQis : CFSG.ABGLocalTools.IsSylowOf 3 Q H := ⟨Qh, rfl⟩
  have hZg3 : IsPGroup 3 (Z.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (hPp.to_le hZP).map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨c, hcH, hcQ⟩ :=
    CFSG.GH74.GLS.C3.Layer2.exists_mem_conj_le_of_isSylowOf hQis hZgH hZg3
  have hZgcQ : (Z.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj c⁻¹).toMonoidHom ≤ Q := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    simpa [MulAut.conj_apply] using hcQ z hz
  have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      (MulAut.conj (g * c)⁻¹).toMonoidHom := by
    ext z
    simp [mul_assoc]
  have hZgcM : Z.map (MulAut.conj (g * c)⁻¹).toMonoidHom ≤ M := by
    have h1 : (Z.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj c⁻¹).toMonoidHom ≤ M := hZgcQ.trans hQM
    rwa [Subgroup.map_map, hcomp] at h1
  have hZ_conj_le : Z ≤ M.map (MulAut.conj (g * c)).toMonoidHom := by
    have h2 : (Z.map (MulAut.conj (g * c)⁻¹).toMonoidHom).map
        (MulAut.conj (g * c)).toMonoidHom ≤ M.map (MulAut.conj (g * c)).toMonoidHom :=
      Subgroup.map_mono hZgcM
    have hleft : (Z.map (MulAut.conj (g * c)⁻¹).toMonoidHom).map
        (MulAut.conj (g * c)).toMonoidHom = Z := by
      rw [Subgroup.map_map]
      have hcomp' : (MulAut.conj (g * c)).toMonoidHom.comp
          (MulAut.conj (g * c)⁻¹).toMonoidHom = MonoidHom.id G := by
        ext z
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp', Subgroup.map_id]
    rwa [hleft] at h2
  have hMconj : M.map (MulAut.conj (g * c)).toMonoidHom = M := hZU.2 (g * c) hZ_conj_le
  have hmM : g * c ∈ M := by
    have hnorm : g * c ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMconj
    rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hmax] at hnorm
  exact ⟨c, hcH, hmM⟩

theorem exists_mem_conj_forall_of_center
    {G : Type} [Group G] [Finite G] {M P Z X : Subgroup G}
    (hmax : CFSG.Open.rankThreeIsMaxTwoLocal M) (hPp : IsPGroup 3 P)
    (hZP : Z ≤ P) (hZcent : Z ≤ (Subgroup.center ↥P).map P.subtype)
    (hZU : Z ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M)
    (hX : X ≤ P) {g : G} (hg : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ P) :
    ∃ m ∈ M, ∀ x ∈ X, g⁻¹ * x * g = m⁻¹ * x * m := by
  obtain ⟨c, hcH, hmM⟩ := exists_mem_forall_aux hmax hPp hZP hZcent hZU hX hg
  refine ⟨g * c, hmM, ?_⟩
  intro x hx
  have hmem : g⁻¹ * x * g ∈ X.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.mem_map]
    exact ⟨x, hx, by simp⟩
  have hcomm : (g⁻¹ * x * g) * c = c * (g⁻¹ * x * g) :=
    (Subgroup.mem_centralizer_iff.mp hcH) (g⁻¹ * x * g) hmem
  have hmid : c⁻¹ * (g⁻¹ * x * g) * c = g⁻¹ * x * g := by
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  calc g⁻¹ * x * g = c⁻¹ * (g⁻¹ * x * g) * c := hmid.symm
    _ = (g * c)⁻¹ * x * (g * c) := by group

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
