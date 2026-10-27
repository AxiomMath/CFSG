module

public import CFSG.Quasithin.MS93.Amalgam

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ

universe u

abbrev Hol (K : Type u) [Group K] : Type u := K ⋊[MonoidHom.id (MulAut K)] MulAut K

namespace Hol

variable {K : Type u} [Group K]

instance instFinite [Finite K] : Finite (Hol K) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem inr_mul_inl_mul_inr_inv (φ : MulAut K) (k : K) :
    (SemidirectProduct.inr φ * SemidirectProduct.inl k * (SemidirectProduct.inr φ)⁻¹ : Hol K) =
      SemidirectProduct.inl (φ k) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem range_inl_normal : (SemidirectProduct.inl : K →* Hol K).range.Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem normal_map_inl_iff (L : Subgroup K) :
    (L.map (SemidirectProduct.inl : K →* Hol K)).Normal ↔ L.Characteristic := by
  constructor
  · intro hN
    rw [Subgroup.characteristic_iff_map_le]
    rintro φ _ ⟨l, hl, rfl⟩
    have h := hN.conj_mem _ ⟨l, hl, rfl⟩ (SemidirectProduct.inr φ)
    rw [inr_mul_inl_mul_inr_inv] at h
    obtain ⟨l', hl', he⟩ := h
    rw [SemidirectProduct.inl_inj] at he
    show φ l ∈ L
    rw [← he]
    exact hl'
  · intro hL
    have hLn : L.Normal := Subgroup.normal_of_characteristic L
    refine ⟨?_⟩
    rintro _ ⟨l, hl, rfl⟩ x
    have hφ : x.right l ∈ L := by
      have h : l ∈ L.comap x.right.toMonoidHom := by rw [hL.fixed]; exact hl
      exact h
    refine ⟨x.left * x.right l * x.left⁻¹, hLn.conj_mem _ hφ _, ?_⟩
    conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    calc (SemidirectProduct.inl (x.left * x.right l * x.left⁻¹) : Hol K)
        = SemidirectProduct.inl x.left * SemidirectProduct.inl (x.right l) *
            (SemidirectProduct.inl x.left)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = SemidirectProduct.inl x.left * (SemidirectProduct.inr x.right *
            SemidirectProduct.inl l * (SemidirectProduct.inr x.right)⁻¹) *
            (SemidirectProduct.inl x.left)⁻¹ := by rw [inr_mul_inl_mul_inr_inv]
      _ = _ := by group

end Hol

variable {G : Type u} [Group G] {T M : Subgroup G}

@[expose] def puAmalgam (hTM : T ≤ M) : GoldAmalgam ↥M ↥T (Hol ↥T) where
  toA := Subgroup.inclusion hTM
  toB := SemidirectProduct.inl
  toA_injective := Subgroup.inclusion_injective hTM
  toB_injective := SemidirectProduct.inl_injective

variable (hTM : T ≤ M)

@[simp] theorem puAmalgam_toA : (puAmalgam hTM).toA = Subgroup.inclusion hTM := rfl

@[simp] theorem puAmalgam_toB : (puAmalgam hTM).toB = SemidirectProduct.inl := rfl

theorem puAmalgam_edgeA : (puAmalgam hTM).edgeA = T.subgroupOf M :=
  Subgroup.inclusion_range hTM

theorem puAmalgam_edgeB :
    (puAmalgam hTM).edgeB = (SemidirectProduct.inl : ↥T →* Hol ↥T).range := rfl

theorem PU.map_inclusion_eq_subgroupOf (L : Subgroup ↥T) :
    L.map (Subgroup.inclusion hTM) = (L.map T.subtype).subgroupOf M := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, hlx⟩
    exact ⟨l, hl, Subtype.ext hlx⟩

theorem isFaithful_puAmalgam_iff : (puAmalgam hTM).IsFaithful ↔
    ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      ¬ M ≤ Subgroup.normalizer (C : Set G) := by
  constructor
  · intro hf C hCT hC1 hchar hnorm
    apply hC1
    have hA : ((C.subgroupOf T).map (puAmalgam hTM).toA).Normal := by
      rw [puAmalgam_toA, PU.map_inclusion_eq_subgroupOf, Subgroup.map_subgroupOf_eq_of_le hCT]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hCT.trans hTM)).2 hnorm
    have hB : ((C.subgroupOf T).map (puAmalgam hTM).toB).Normal :=
      (Hol.normal_map_inl_iff _).2 hchar
    have h := hf _ hA hB
    rw [← Subgroup.map_subgroupOf_eq_of_le hCT, h, Subgroup.map_bot]
  · intro hP K hA hB
    by_contra hK
    have hchar : K.Characteristic := (Hol.normal_map_inl_iff K).1 hB
    have hCT : K.map T.subtype ≤ T := Subgroup.map_subtype_le K
    have hsub : (K.map T.subtype).subgroupOf T = K :=
      Subgroup.comap_map_eq_self_of_injective T.subtype_injective K
    refine hP (K.map T.subtype) hCT ?_ (by rw [hsub]; exact hchar) ?_
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective]
    · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (hCT.trans hTM),
        ← PU.map_inclusion_eq_subgroupOf hTM]
      exact hA

theorem hyp20_puAmalgam [Finite G] (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hP : ∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      ¬ M ≤ Subgroup.normalizer (C : Set G)) :
    Hyp20 (puAmalgam hTM) where
  finite_edge := inferInstance
  nontrivial_edge := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  isPGroup_edge := hT
  normal_edgeB := Hol.range_inl_normal
  faithful := (isFaithful_puAmalgam_iff hTM).2 hP

end CFSG.Quasithin.MS93
