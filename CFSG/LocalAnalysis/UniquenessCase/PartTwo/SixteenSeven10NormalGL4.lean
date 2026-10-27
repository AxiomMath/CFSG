module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W]

private theorem s16c1610_normal_le_center_or_eq_top {Q : Type*} [Group Q]
    (hperf : _root_.commutator Q = ⊤) (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  let q : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  haveI hNq : (N.map q).Normal :=
    (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map q) with hbot | htop
  · left
    have hle : N ≤ q.ker := (Subgroup.map_eq_bot_iff (f := q) N).mp hbot
    rwa [QuotientGroup.ker_mk'] at hle
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have h := Subgroup.comap_map_eq (f := q) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have hcomm : _root_.commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hcomm
    exact le_antisymm le_top hcomm

private theorem s16c1610_card_center_SL_four_dvd {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2))) ∣ 3 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have h1 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2))) =
      Nat.card (rootsOfUnity (max (Fintype.card (Fin m)) 1) (GaloisField 2 2)) :=
    Nat.card_congr Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.toEquiv
  rw [h1]
  have h2 := Subgroup.card_dvd_of_le
    (le_top : rootsOfUnity (max (Fintype.card (Fin m)) 1) (GaloisField 2 2) ≤ ⊤)
  rw [Subgroup.card_top] at h2
  have h3 : Nat.card (GaloisField 2 2)ˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by norm_num)]
    norm_num
  rwa [h3] at h2

private theorem s16c1610_SL_four_perfect_simple {m : ℕ} (hm : 2 ≤ m) :
    _root_.commutator (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) = ⊤ ∧
      IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2))) := by
  have h4 : ∃ s : Finset (GaloisField 2 2), s.card = 4 := by
    letI : Fintype (GaloisField 2 2) := Fintype.ofFinite (GaloisField 2 2)
    exact ⟨Finset.univ, by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num⟩
  exact ⟨(CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField 2 2) (n := m)
      hm (Or.inr h4)).commutator_eq_top,
    (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 2) (n := m)
      hm (Or.inr h4)).2.1⟩

private theorem s16c1610_normal_GL_four {m : ℕ} (hm : 2 ≤ m)
    (N : Subgroup (Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2))) (hN : N.Normal) :
    Nat.card N ∣ 9 ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) ∣ Nat.card N := by
  classical
  haveI := hN
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2)) :=
    Matrix.GeneralLinearGroup.det.ker
  let Ns : Subgroup (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) :=
    N.comap (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2) →*
        Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2))
  haveI hSnormal : S.Normal := inferInstance
  haveI hNsnormal : Ns.Normal := inferInstance
  have hNs_card : Nat.card Ns = Nat.card (S.subgroupOf N) := by
    have hmap : Ns.map (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2) →*
          Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2)) =
        (S ⊓ N : Subgroup (Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2))) := by
      rw [Subgroup.map_comap_eq, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    have h1 : Nat.card Ns =
        Nat.card (S ⊓ N : Subgroup (Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2))) := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective (K := Ns)
        (f := (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2) →*
            Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2)))
        Matrix.SpecialLinearGroup.toGL_injective).symm
    have h2 : Nat.card (S.subgroupOf N) =
        Nat.card (S ⊓ N : Subgroup (Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2))) := by
      rw [← Subgroup.subgroupOf_map_subtype S N]
      exact (Subgroup.card_subtype N (S.subgroupOf N)).symm
    exact h1.trans h2.symm
  have hSindex : S.index = 3 := by
    have h1 : S.index = Nat.card (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2) →* (GaloisField 2 2)ˣ).range :=
      Subgroup.index_ker (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2) →* (GaloisField 2 2)ˣ)
    rw [MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective,
      Subgroup.card_top] at h1
    rw [h1, Nat.card_units, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hindex : (S.subgroupOf N).index ∣ 3 := by
    have h : S.relIndex N ∣ S.index :=
      Subgroup.relIndex_dvd_index_of_normal (H := S) (K := N)
    rw [hSindex] at h
    exact h
  have hZ3 := s16c1610_card_center_SL_four_dvd hm
  obtain ⟨hperf, hs⟩ := s16c1610_SL_four_perfect_simple hm
  rcases s16c1610_normal_le_center_or_eq_top hperf hs Ns with hNsZ | hNstop
  · left
    have h1 : Nat.card Ns ∣ 3 := (Subgroup.card_dvd_of_le hNsZ).trans hZ3
    have h2 : Nat.card (S.subgroupOf N) ∣ 3 := hNs_card ▸ h1
    have h3 : Nat.card N = Nat.card (S.subgroupOf N) * (S.subgroupOf N).index :=
      (Subgroup.card_mul_index (S.subgroupOf N)).symm
    rw [h3]
    simpa using mul_dvd_mul h2 hindex
  · right
    have hSLcard : Nat.card Ns =
        Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) := by
      rw [hNstop, Subgroup.card_top]
    have hMcard : Nat.card (S.subgroupOf N) =
        Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) :=
      hNs_card.symm.trans hSLcard
    have h3 : Nat.card N = Nat.card (S.subgroupOf N) * (S.subgroupOf N).index :=
      (Subgroup.card_mul_index (S.subgroupOf N)).symm
    rw [h3, hMcard]
    exact dvd_mul_right _ _

theorem s16c1610_not_isNatGL4_of_normal {G X N : Subgroup (MulAut W)} {m : ℕ} (hm : 2 ≤ m)
    (hNH : N ≤ G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h9 : ¬ Nat.card N ∣ 9)
    (hSL : ¬ Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) ∣ Nat.card N) :
    ¬ IsNatGL4 W (G ⊓ Subgroup.centralizer (X : Set (MulAut W))) m := by
  rintro ⟨φ, -, -⟩
  let H : Subgroup (MulAut W) := G ⊓ Subgroup.centralizer (X : Set (MulAut W))
  have hNH' : N ≤ H := hNH
  have hNnH : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH').mpr
      ((inf_le_left : H ≤ G).trans (Subgroup.le_normalizer_iff.mpr hNn))
  let Nc : Subgroup (Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2)) :=
    (N.subgroupOf H).map φ.toMonoidHom
  have hNc : Nc.Normal := hNnH.map φ.toMonoidHom φ.surjective
  have hcardNc : Nat.card Nc = Nat.card N := by
    have h1 : Nat.card (N.subgroupOf H) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH').toEquiv
    have h2 : Nat.card Nc = Nat.card (N.subgroupOf H) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (N.subgroupOf H) φ.toMonoidHom
        φ.injective).toEquiv).symm
    exact h2.trans h1
  rcases s16c1610_normal_GL_four hm Nc hNc with h9' | hSL'
  · exact h9 (hcardNc ▸ h9')
  · exact hSL (hcardNc ▸ hSL')

private theorem s16c1610_normal_SL_four {m : ℕ} (hm : 2 ≤ m)
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2))) (hN : N.Normal) :
    Nat.card N ∣ 3 ∨
      Nat.card N = Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) := by
  haveI := hN
  obtain ⟨hperf, hs⟩ := s16c1610_SL_four_perfect_simple hm
  rcases s16c1610_normal_le_center_or_eq_top hperf hs N with hNZ | hNtop
  · exact Or.inl ((Subgroup.card_dvd_of_le hNZ).trans (s16c1610_card_center_SL_four_dvd hm))
  · exact Or.inr (by rw [hNtop, Subgroup.card_top])

theorem s16c1610_not_isNatSL4_of_normal {G X N : Subgroup (MulAut W)} {m : ℕ} (hm : 2 ≤ m)
    (hNH : N ≤ G ⊓ Subgroup.centralizer (X : Set (MulAut W)))
    (hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h9 : ¬ Nat.card N ∣ 9)
    (hSL : ¬ Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) ∣ Nat.card N) :
    ¬ IsNatSL4 W (G ⊓ Subgroup.centralizer (X : Set (MulAut W))) m := by
  rintro ⟨φ, -, -⟩
  let H : Subgroup (MulAut W) := G ⊓ Subgroup.centralizer (X : Set (MulAut W))
  have hNH' : N ≤ H := hNH
  have hNnH : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH').mpr
      ((inf_le_left : H ≤ G).trans (Subgroup.le_normalizer_iff.mpr hNn))
  let Nc : Subgroup (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) :=
    (N.subgroupOf H).map φ.toMonoidHom
  have hNc : Nc.Normal := hNnH.map φ.toMonoidHom φ.surjective
  have hcardNc : Nat.card Nc = Nat.card N := by
    have h1 : Nat.card (N.subgroupOf H) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH').toEquiv
    have h2 : Nat.card Nc = Nat.card (N.subgroupOf H) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (N.subgroupOf H) φ.toMonoidHom
        φ.injective).toEquiv).symm
    exact h2.trans h1
  rcases s16c1610_normal_SL_four hm Nc hNc with h3 | hfull
  · exact h9 (hcardNc ▸ h3.trans (by norm_num))
  · have heq : Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) = Nat.card N :=
      hfull.symm.trans hcardNc
    exact hSL (heq ▸ dvd_refl _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
