module

public import CFSG.RankThree.PartTwo.Sec21.Item233RootsL44

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] {K : Type} [Group K]

@[expose] noncomputable def thetaK {I H : Subgroup G} (hHI : H ≤ I) (Φ : I ≃* K) {C : Subgroup K}
    (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) : H ≃* C :=
  (Subgroup.subgroupOfEquivOfLe hHI).symm.trans
    ((MulEquiv.subgroupMap Φ (H.subgroupOf I)).trans (MulEquiv.subgroupCongr hΦH))

theorem normalizer_of_map_equiv {I T : Subgroup G} (hTI : T ≤ I) (Φ : I ≃* K) {e : K}
    (he : e ∈ Subgroup.normalizer (((T.subgroupOf I).map Φ.toMonoidHom : Subgroup K) : Set K)) :
    ((Φ.symm e : I) : G) ∈ Subgroup.normalizer (T : Set G) := by
  set g : I := Φ.symm e with hg
  have hΦg : Φ g = e := Φ.apply_symm_apply e
  rw [Subgroup.mem_normalizer_iff] at he ⊢
  intro h
  by_cases hhI : h ∈ I
  · set h' : I := ⟨h, hhI⟩ with hh'
    have key := he (Φ h')
    have e1 : e * Φ h' * e⁻¹ = Φ (g * h' * g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hΦg]
    rw [e1] at key
    have m1 : ∀ y : I, (y : G) ∈ T ↔
        Φ y ∈ ((T.subgroupOf I).map Φ.toMonoidHom : Subgroup K) := fun y =>
      (Subgroup.mem_subgroupOf (H := T) (K := I) (h := y)).symm.trans
        (Subgroup.mem_map_iff_mem (f := Φ.toMonoidHom) Φ.injective).symm
    have e2 : (((g * h' * g⁻¹ : I)) : G) = (g : G) * h * (g : G)⁻¹ := rfl
    rw [← e2]
    exact (m1 h').trans (key.trans (m1 (g * h' * g⁻¹)).symm)
  · have hn1 : h ∉ T := fun hT => hhI (hTI hT)
    have hn2 : (g : G) * h * (g : G)⁻¹ ∉ T := by
      intro hT
      apply hhI
      have hI : (g : G) * h * (g : G)⁻¹ ∈ I := hTI hT
      have e : (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * (g : G) = h := by group
      rw [← e]
      exact I.mul_mem (I.mul_mem (I.inv_mem g.2) hI) g.2
    exact ⟨fun hT => absurd hT hn1, fun hT => absurd hT hn2⟩

theorem exists_E16_of_model {I B Xm : Subgroup G} (hBI : B ≤ I) (hXI : Xm ≤ I) (Φ : I ≃* K)
    {E₀ : Subgroup K} (hab : IsElemAbelian 2 E₀) (hcard : Nat.card E₀ = 2 ^ 4)
    (hB : E₀ ≤ Subgroup.normalizer (((B.subgroupOf I).map Φ.toMonoidHom : Subgroup K) : Set K))
    (hX : E₀ ≤ Subgroup.normalizer (((Xm.subgroupOf I).map Φ.toMonoidHom : Subgroup K) : Set K)) :
    ∃ E : Subgroup G, E ≤ I ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
      E ≤ Subgroup.normalizer (B : Set G) ∧ E ≤ Subgroup.normalizer (Xm : Set G) := by
  refine ⟨(E₀.map Φ.symm.toMonoidHom).map I.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · exact CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map
      (CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map hab _) _
  · rw [Subgroup.card_map_of_injective I.subtype_injective,
      Subgroup.card_map_of_injective Φ.symm.injective, hcard]
  · rintro _ ⟨y, ⟨e, he, rfl⟩, rfl⟩
    exact normalizer_of_map_equiv hBI Φ (hB he)
  · rintro _ ⟨y, ⟨e, he, rfl⟩, rfl⟩
    exact normalizer_of_map_equiv hXI Φ (hX he)

theorem map_subgroupOf_zpowers {I : Subgroup G} {b : G} (hb : b ∈ I) (Φ : I ≃* K) :
    ((((Subgroup.zpowers b : Subgroup G)).subgroupOf I).map Φ.toMonoidHom : Subgroup K) =
      Subgroup.zpowers (Φ ⟨b, hb⟩) := by
  have h2 : (Subgroup.zpowers (⟨b, hb⟩ : I)).map I.subtype = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]
    rfl
  have h1 : (Subgroup.zpowers b : Subgroup G).subgroupOf I = Subgroup.zpowers (⟨b, hb⟩ : I) := by
    rw [← h2]
    exact Subgroup.comap_map_eq_self_of_injective I.subtype_injective _
  rw [h1, MonoidHom.map_zpowers]
  rfl

theorem map_subgroupOf_map_subtype {I H : Subgroup G} (hHI : H ≤ I) (Φ : I ≃* K)
    {C : Subgroup K} (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) (X : Subgroup H) :
    (((X.map H.subtype).subgroupOf I).map Φ.toMonoidHom : Subgroup K) =
      (X.map (thetaK hHI Φ hΦH).toMonoidHom).map C.subtype := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
    refine ⟨thetaK hHI Φ hΦH x, ⟨x, hx, rfl⟩, ?_⟩
    have : (⟨(x : G), hHI x.2⟩ : I) = y := Subtype.ext hxy
    change Φ ⟨(x : G), hHI x.2⟩ = Φ.toMonoidHom y
    rw [this]
    rfl
  · rintro ⟨c, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨(x : G), hHI x.2⟩, ⟨x, hx, rfl⟩, rfl⟩

theorem transport_E16 {I : Subgroup G} (Φ : I ≃* K) {b : G} (hbI : b ∈ I)
    (X : Subgroup (I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) :
      Subgroup G))
    {E₀ : Subgroup K} (hab : IsElemAbelian 2 E₀) (hcard : Nat.card E₀ = 2 ^ 4)
    (hB : E₀ ≤ Subgroup.normalizer ((Subgroup.zpowers (Φ ⟨b, hbI⟩) : Subgroup K) : Set K))
    (hX : E₀ ≤ Subgroup.normalizer
      (((X.map (thetaK (inf_le_left : I ⊓ Subgroup.centralizer
        ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ I) Φ
        (map_inf_centralizer_zpowers Φ hbI)).toMonoidHom).map
          (Subgroup.centralizer ({Φ ⟨b, hbI⟩} : Set K)).subtype : Subgroup K) : Set K)) :
    ∃ E : Subgroup G, E ≤ I ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
      E ≤ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) ∧
      E ≤ Subgroup.normalizer ((X.map (I ⊓ Subgroup.centralizer
        ((Subgroup.zpowers b : Subgroup G) : Set G)).subtype : Subgroup G) : Set G) := by
  have hBI : (Subgroup.zpowers b : Subgroup G) ≤ I := Subgroup.zpowers_le.mpr hbI
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hXI : (X.map (I ⊓ Subgroup.centralizer
      ((Subgroup.zpowers b : Subgroup G) : Set G)).subtype : Subgroup G) ≤ I :=
    (Subgroup.map_subtype_le X).trans hHI
  refine exists_E16_of_model hBI hXI Φ hab hcard ?_ ?_
  · rw [map_subgroupOf_zpowers hbI Φ]
    exact hB
  · rw [map_subgroupOf_map_subtype hHI Φ (map_inf_centralizer_zpowers Φ hbI) X]
    exact hX

end CFSG.RankThree.PartTwo.Sec21.Hering233i
