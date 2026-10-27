module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

private theorem k89wc_map_conj_mul {G : Type} [Group G] (H : Subgroup G) (x y : G) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      H.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext h
  simp [MulAut.conj_apply, mul_assoc]

private theorem k89wc_map_conj_inv {G : Type} [Group G] (H : Subgroup G) (x : G) :
    (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [h, Subgroup.map_id]

private theorem k89wc_map_conj_inv' {G : Type} [Group G] (H : Subgroup G) (x : G) :
    (H.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [h, Subgroup.map_id]

theorem s889_weak_closed {G : Type} [Group G] [Finite G]
    (D : Data G) (h882 : R882 D) (h885 : R885 D) (h886 : R886 D) (h887 : R887 D)
    (h888 : R888 D) : S889WeakClosed D := by
  intro L P ω hω g hg
  have hS : Set880 D L P := hω.set880
  let Z : Subgroup G := ZOf (P ⊓ L)
  change Z.map (MulAut.conj g).toMonoidHom = Z
  change Z.map (MulAut.conj g).toMonoidHom ≤ normalizer (Z : Set G) at hg
  have hZgM : Z.map (MulAut.conj g).toMonoidHom ≤ D.M := hg.trans (h887 L P hS)
  have hZ_le_Mg : Z ≤ D.M.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hZgM
    rwa [k89wc_map_conj_inv] at h
  have hMg : D.M.map (MulAut.conj g⁻¹).toMonoidHom = D.M :=
    (h888 L P hS).2 g⁻¹ hZ_le_Mg
  have hgM : g ∈ D.M := by
    have h1 : g⁻¹ ∈ normalizer (D.M : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMg
    have h2 : g ∈ normalizer (D.M : Set G) := by simpa using inv_mem h1
    rw [← CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
    exact h2
  have hcardZ : Nat.card Z = 3 := (h886 L P hS).1
  have hZ3 : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hcardZ, pow_one])
  have hZg3 : IsPGroup 3 (Z.map (MulAut.conj g).toMonoidHom) :=
    IsPGroup.of_card (n := 1) (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardZ, pow_one])
  have hQ3 : IsPGroup 3 ↥(Z ⊔ Z.map (MulAut.conj g).toMonoidHom) := by
    have h := r889_isPGroup_sup hZg3 hZ3 hg
    rwa [sup_comm] at h
  have hPLM : P ⊓ L ≤ D.M := inf_le_left.trans hS.sylow.le
  have hZM : Z ≤ D.M := inf_le_left.trans hPLM
  have hQM : Z ⊔ Z.map (MulAut.conj g).toMonoidHom ≤ D.M := sup_le hZM hZgM
  have hQ3sub : IsPGroup 3 ((Z ⊔ Z.map (MulAut.conj g).toMonoidHom).subgroupOf D.M) :=
    hQ3.comap_subtype
  obtain ⟨S, hQS⟩ := hQ3sub.exists_le_sylow
  let P' : Subgroup G := (S : Subgroup D.M).map D.M.subtype
  have hP'syl : IsSylowOf 3 P' D.M := ⟨S, rfl⟩
  have hQP' : Z ⊔ Z.map (MulAut.conj g).toMonoidHom ≤ P' := by
    have hQeq : ((Z ⊔ Z.map (MulAut.conj g).toMonoidHom).subgroupOf D.M).map D.M.subtype =
        Z ⊔ Z.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQM]
    rw [← hQeq]
    exact Subgroup.map_mono hQS
  obtain ⟨a, haM, hconj⟩ := hS.sylow.exists_mem_conj hP'syl
  have hQa : Z ⊔ Z.map (MulAut.conj g).toMonoidHom ≤
      P.map (MulAut.conj a).toMonoidHom := by
    intro x hx
    have h1 : a⁻¹ * x * a ∈ P := (hconj x).mp (hQP' hx)
    exact Subgroup.mem_map.mpr ⟨a⁻¹ * x * a, h1, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hML : D.M ≤ normalizer (L : Set G) := r889_normalizes_of_inputs h882 h885 hS
  have hZL : Z ≤ L := inf_le_left.trans inf_le_right
  have hZgL : Z.map (MulAut.conj g).toMonoidHom ≤ L := by
    have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hML hgM)
    calc Z.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hZL
      _ = L := hLmap
  have hQL : Z ⊔ Z.map (MulAut.conj g).toMonoidHom ≤ L := sup_le hZL hZgL
  have hQLa : Z ⊔ Z.map (MulAut.conj g).toMonoidHom ≤
      L ⊓ P.map (MulAut.conj a).toMonoidHom := le_inf hQL hQa
  have haM : a⁻¹ ∈ D.M := D.M.inv_mem haM
  have hQmap_le : (Z ⊔ Z.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj a⁻¹).toMonoidHom ≤ P ⊓ L := by
    have h1 : (Z ⊔ Z.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom ≤ P := by
      calc _ ≤ (P.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom :=
            Subgroup.map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) (le_inf_iff.mp hQLa).2
        _ = P := k89wc_map_conj_inv P a
    have h2 : (Z ⊔ Z.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom ≤ L := by
      calc _ ≤ L.map (MulAut.conj a⁻¹).toMonoidHom :=
            Subgroup.map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) (le_inf_iff.mp hQLa).1
        _ = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hML haM)
    exact le_inf h1 h2
  have hZa' : Z.map (MulAut.conj a⁻¹).toMonoidHom ≤ P ⊓ L :=
    (Subgroup.map_mono (f := (MulAut.conj a⁻¹).toMonoidHom)
      (le_sup_left : Z ≤ Z ⊔ Z.map (MulAut.conj g).toMonoidHom)).trans hQmap_le
  have hZga' : (Z.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj a⁻¹).toMonoidHom ≤ P ⊓ L :=
    (Subgroup.map_mono (f := (MulAut.conj a⁻¹).toMonoidHom)
      (le_sup_right : Z.map (MulAut.conj g).toMonoidHom ≤
        Z ⊔ Z.map (MulAut.conj g).toMonoidHom)).trans hQmap_le
  have hZag : Z.map (MulAut.conj (a⁻¹ * g)).toMonoidHom ≤ P ⊓ L := by
    simpa only [k89wc_map_conj_mul] using hZga'
  have hwc := (h886 L P hS).2.2.1
  have heq_a' : Z.map (MulAut.conj a⁻¹).toMonoidHom = Z := hwc a⁻¹ haM hZa'
  have heq_ag : Z.map (MulAut.conj (a⁻¹ * g)).toMonoidHom = Z :=
    hwc (a⁻¹ * g) (D.M.mul_mem haM hgM) hZag
  have hconj_eq : (Z.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj a⁻¹).toMonoidHom = Z.map (MulAut.conj a⁻¹).toMonoidHom := by
    rw [k89wc_map_conj_mul, heq_ag, heq_a']
  calc Z.map (MulAut.conj g).toMonoidHom
      = ((Z.map (MulAut.conj g).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom).map
          (MulAut.conj a).toMonoidHom :=
        (k89wc_map_conj_inv' (Z.map (MulAut.conj g).toMonoidHom) a).symm
    _ = (Z.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
          rw [hconj_eq]
    _ = Z := k89wc_map_conj_inv' Z a

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
