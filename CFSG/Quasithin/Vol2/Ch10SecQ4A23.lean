module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Lift1
public import CFSG.Quasithin.Vol2.Ch10SecQ4A9

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G : Type} [Group G] [Finite G] {T L I K J X : Subgroup G}

theorem T1_le_normalizer_of_isLi (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (hK : Ch10.IsLi T L K) :
    Ch10.T1 T L ≤ Subgroup.normalizer (K : Set G) := by
  rcases hK with rfl | ⟨t, ht, -, rfl⟩
  · exact inf_le_right
  · exact SecE.T1_le_normalizer_conjugate h37 h38 hyp ht

@[expose] noncomputable def conjK (K : Subgroup G) (t : G) : ↥K →* G :=
  (MulAut.conj t).toMonoidHom.comp K.subtype

omit [Finite G] in
theorem conjK_injective (t : G) : Function.Injective (conjK K t) :=
  (MulAut.conj t).injective.comp K.subtype_injective

omit [Finite G] in
theorem range_conjK (t : G) : (conjK (CFSG.conjugate L t) t).range = L := by
  rw [conjK, MonoidHom.range_comp, Subgroup.range_subtype, CFSG.conjugate, Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : ((MulAut.conj t).toMonoidHom.comp (MulAut.conj t⁻¹).toMonoidHom) y = y := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [Finite G] in
theorem imgL_conjK (t : G) {A : Subgroup G} (hA : A ≤ K) :
    imgL (conjK K t) A = A.map (MulAut.conj t).toMonoidHom := by
  rw [imgL, conjK, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hA]

theorem commutator_fsuVM_le_blockU (h113 : ASInputs.AS_C_1_13) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) (hK : Ch10.IsLi T L K) (hKs : IsShort2 K)
    (hKa : IsAltType K 5) : ⁅fsuVM T L I, K⁆ ≤ blockU K := by
  rcases hK with rfl | ⟨t, ht, -, rfl⟩
  · rw [(SecE.blockU_eq_fsuUL h113 hyp h2 ⟨hKs, hKa⟩).1]
  · set K := CFSG.conjugate L t
    set f := conjK K t
    have hkQ : ∀ x : ↥K, f x = 1 → (x : G) ∈ blockQ K := fun x hx => by
      rw [(injective_iff_map_eq_one f).mp (conjK_injective t) x hx]
      exact Subgroup.one_mem _
    have hkU : ∀ x : ↥K, f x = 1 → (x : G) ∈ blockU K → (x : G) = 1 := fun x hx _ => by
      rw [(injective_iff_map_eq_one f).mp (conjK_injective t) x hx]
      rfl
    have hLs : IsShort2 L := by
      have h := isShort2_range f hkQ hkU hKs hKa
      rwa [range_conjK] at h
    have hLa : IsAltType L 5 := by
      have h := isAltType_range f hkQ hkU hKs hKa
      rwa [range_conjK] at h
    have hUL := (SecE.blockU_eq_fsuUL h113 hyp h2 ⟨hLs, hLa⟩).1
    have hUK : blockU K ≤ K := hKs.2.2.1.1.trans (inf_le_left.trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
    have h1 : blockU L = (blockU K).map (MulAut.conj t).toMonoidHom := by
      rw [← imgL_conjK t hUK, ← blockU_range f hkQ, range_conjK]
    rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
    show CFSG.conjugate (fsuUL T L I) t ≤ blockU K
    rw [← hUL, h1, CFSG.conjugate, Subgroup.map_map]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have e : ((MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom) y = y := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy

omit [Finite G] in
theorem eq_oPrimeResidualOf_of_subgroupOf (hJX : J ≤ X)
    (h : J.subgroupOf X = oPrimeResidualOf 3 (⊤ : Subgroup ↥X)) : J = oPrimeResidualOf 3 X := by
  have h1 : J = (J.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hJX).symm
  rw [h1, h, oPrimeResidualOf, oPrimeResidualOf, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨-, k, hk⟩, rfl⟩
    exact ⟨y.2, k, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]; exact hk⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨Subgroup.mem_top _, k, by rw [Subgroup.orderOf_mk]; exact hk⟩, rfl⟩

omit [Finite G] in
theorem mem_of_orderOf_three {x : G} (hx : x ∈ X) (hx3 : orderOf x = 3)
    (h : J.subgroupOf X = oPrimeResidualOf 3 (⊤ : Subgroup ↥X) ∨
      J.subgroupOf X = thetaOf (⊤ : Subgroup ↥X)) : x ∈ J := by
  have hx3' : orderOf (⟨x, hx⟩ : ↥X) = 3 := by rw [Subgroup.orderOf_mk]; exact hx3
  suffices hmem : (⟨x, hx⟩ : ↥X) ∈ J.subgroupOf X from Subgroup.mem_subgroupOf.mp hmem
  rcases h with h | h
  · rw [h]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [pow_one]; exact hx3'⟩
  · rw [h]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, hx3'⟩

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
