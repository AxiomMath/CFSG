module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixB
public import CFSG.LocalAnalysis.WeakClosure81.Twelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsPairAt.kerMOf_le_of_commutator_le (hMult : SchurMultiplierInput)
    {M X A C : Subgroup G} (h : IsPairAt M X A) (hA2 : IsPGroup 2 A)
    (hCn : (C.subgroupOf X).Normal) (hCK : C ≤ kerMOf M X)
    (hodd : Odd (C.relIndex (kerMOf M X))) (hcomm : ⁅A, kerMOf M X⁆ ≤ C)
    (hAK : A ⊓ kerMOf M X ≤ C) (hgen : conjClosure A X ⊔ C = X)
    (htype : ∃ n : ℕ, 1 < n ∧ (CFSG.Quasithin.IsPSL 2 2 n (KerQuot M X) ∨
      CFSG.Quasithin.IsSz n (KerQuot M X))) :
    kerMOf M X ≤ C := by
  haveI : (C.subgroupOf X).Normal := hCn
  haveI : ((kerMOf M X).subgroupOf X).Normal := normal_subgroupOf_kerMOf M X
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  have hCX : C ≤ X := hCK.trans hKX
  have hconj : conjClosure A X ≤ X :=
    conjClosure_le fun h' hh' z hz => X.mul_mem (X.mul_mem hh' (h.A_le hz)) (X.inv_mem hh')
  set Kq : Subgroup (↥X ⧸ (C.subgroupOf X)) :=
    ((kerMOf M X).subgroupOf X).map (QuotientGroup.mk' (C.subgroupOf X)) with hKq
  set Aq : Subgroup (↥X ⧸ (C.subgroupOf X)) :=
    (A.subgroupOf X).map (QuotientGroup.mk' (C.subgroupOf X)) with hAq
  have hA2sub : IsPGroup 2 (A.subgroupOf X) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe h.A_le).symm
  have hA2q : IsPGroup 2 Aq := by
    rw [hAq]
    exact IsPGroup.map hA2sub (QuotientGroup.mk' (C.subgroupOf X))
  have hKodd : Odd (Nat.card Kq) := by
    rw [hKq]
    rw [← Subgroup.relIndex_ker (K := (kerMOf M X).subgroupOf X)
      (f := QuotientGroup.mk' (C.subgroupOf X))]
    rw [QuotientGroup.ker_mk']
    rw [Subgroup.relIndex_subgroupOf (H := C) (K := kerMOf M X) (L := X) hKX]
    exact hodd
  have hcommAq : ∀ a ∈ Aq, ∀ k ∈ Kq, a * k = k * a := by
    intro a ha k hk
    rw [hAq] at ha
    rw [hKq] at hk
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.mp hk
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [Subgroup.mem_subgroupOf]
    exact hcomm (commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hα)
      (Subgroup.mem_subgroupOf.mp hκ))
  have hAKq : Aq ⊓ Kq = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [hAq] at hx
    rw [hKq] at hx
    obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨α, hα, hαx⟩ := Subgroup.mem_map.mp hxA
    obtain ⟨κ, hκ, hκx⟩ := Subgroup.mem_map.mp hxK
    rw [← hαx, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hker : α⁻¹ * κ ∈ C.subgroupOf X := by
      have h1 : (QuotientGroup.mk' (C.subgroupOf X)) (α⁻¹ * κ) = 1 := by
        rw [map_mul, map_inv, hαx, hκx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (N := C.subgroupOf X) (α⁻¹ * κ)).mp h1
    have hkerK : α⁻¹ * κ ∈ (kerMOf M X).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr (hCK (Subgroup.mem_subgroupOf.mp hker))
    have hαK : α ∈ (kerMOf M X).subgroupOf X := by
      have h1 : κ * (α⁻¹ * κ)⁻¹ = α := by group
      rw [← h1]
      exact ((kerMOf M X).subgroupOf X).mul_mem hκ
        (((kerMOf M X).subgroupOf X).inv_mem hkerK)
    exact Subgroup.mem_subgroupOf.mpr (hAK (Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp hα, Subgroup.mem_subgroupOf.mp hαK⟩))
  haveI : ((conjClosure A X).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_conjClosure A X)
  have hN_eq : Subgroup.normalClosure (((A.subgroupOf X : Subgroup ↥X) : Set ↥X))
      = (conjClosure A X).subgroupOf X := by
    refine le_antisymm ?_ ?_
    · refine Subgroup.normalClosure_le_normal ?_
      intro z hz
      exact Subgroup.mem_subgroupOf.mpr (le_conjClosure A X (Subgroup.mem_subgroupOf.mp hz))
    · have hle : conjClosure A X ≤
          (Subgroup.normalClosure (((A.subgroupOf X : Subgroup ↥X) : Set ↥X))).map X.subtype := by
        refine conjClosure_le (Z := A) (H := X) ?_
        intro h' hh' z hz
        refine Subgroup.mem_map.mpr
          ⟨(⟨h', hh'⟩ : ↥X) * (⟨z, h.A_le hz⟩ : ↥X) * (⟨h', hh'⟩ : ↥X)⁻¹, ?_, ?_⟩
        · exact (inferInstance : (Subgroup.normalClosure
            (((A.subgroupOf X : Subgroup ↥X) : Set ↥X))).Normal).conj_mem
            (⟨z, h.A_le hz⟩ : ↥X)
            (Subgroup.subset_normalClosure (show (⟨z, h.A_le hz⟩ : ↥X) ∈
              ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) from hz))
            (⟨h', hh'⟩ : ↥X)
        · rfl
      calc (conjClosure A X).subgroupOf X
          ≤ ((Subgroup.normalClosure (((A.subgroupOf X : Subgroup ↥X) : Set ↥X))).map
              X.subtype).subgroupOf X := Subgroup.subgroupOf_mono X hle
        _ = Subgroup.normalClosure (((A.subgroupOf X : Subgroup ↥X) : Set ↥X)) :=
            Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hsub : (conjClosure A X).subgroupOf X ⊔ (C.subgroupOf X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := conjClosure A X) (A' := C) (B := X) hconj hCX]
    rw [hgen, Subgroup.subgroupOf_self]
  have hNsup : Subgroup.normalClosure (((A.subgroupOf X : Subgroup ↥X) : Set ↥X)) ⊔
      (C.subgroupOf X) = ⊤ := by
    rw [hN_eq]
    exact hsub
  have hgenAq : Subgroup.normalClosure (Aq : Set (↥X ⧸ (C.subgroupOf X))) = ⊤ := by
    have hmap := Subgroup.map_normalClosure (((A.subgroupOf X : Subgroup ↥X) : Set ↥X))
      (QuotientGroup.mk' (C.subgroupOf X)) (QuotientGroup.mk'_surjective (C.subgroupOf X))
    have hAq_coe : (Aq : Set (↥X ⧸ (C.subgroupOf X))) =
        (QuotientGroup.mk' (C.subgroupOf X)) '' ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [hAq, Subgroup.coe_map]
    rw [hAq_coe, ← hmap]
    rw [← MonoidHom.range_eq_top_of_surjective (QuotientGroup.mk' (C.subgroupOf X))
      (QuotientGroup.mk'_surjective _), Subgroup.map_eq_range_iff, codisjoint_iff,
      QuotientGroup.ker_mk']
    exact hNsup
  have hKcen : Kq ≤ Subgroup.center (↥X ⧸ (C.subgroupOf X)) := by
    have hAq_le : Aq ≤ Subgroup.centralizer (Kq : Set (↥X ⧸ (C.subgroupOf X))) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcommAq a ha k hk).symm
    have htop : (⊤ : Subgroup (↥X ⧸ (C.subgroupOf X))) ≤
        Subgroup.centralizer (Kq : Set (↥X ⧸ (C.subgroupOf X))) := by
      rw [← hgenAq]
      exact Subgroup.normalClosure_le_normal hAq_le
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro q
    exact (Subgroup.mem_centralizer_iff.mp (htop trivial) k hk).symm
  have hsub_CK : C.subgroupOf X ≤ (kerMOf M X).subgroupOf X :=
    fun c hc => hCK (Subgroup.mem_subgroupOf.mp hc)
  have htype' : ∃ n : ℕ, 1 < n ∧
      (CFSG.Quasithin.IsPSL 2 2 n ((↥X ⧸ (C.subgroupOf X)) ⧸ Kq) ∨
        CFSG.Quasithin.IsSz n ((↥X ⧸ (C.subgroupOf X)) ⧸ Kq)) := by
    obtain ⟨n, hn, hcase⟩ := htype
    refine ⟨n, hn, ?_⟩
    have e : ((↥X ⧸ (C.subgroupOf X)) ⧸ Kq) ≃* KerQuot M X :=
      (QuotientGroup.quotientQuotientEquivQuotient (C.subgroupOf X)
        ((kerMOf M X).subgroupOf X) hsub_CK).trans
        (QuotientGroup.quotientMulEquivOfEq (subgroupOf_kerMOf M X))
    rcases hcase with hP | hS
    · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hP)
    · exact Or.inr (CFSG.SectionRank.suzukiModel_of_mulEquiv e hS)
  have hKq_bot : Kq = ⊥ :=
    twelveSix hMult (K := Kq) (A := Aq) hKcen hKodd hA2q hAKq htype' hgenAq
  rw [hKq] at hKq_bot
  have hle : (kerMOf M X).subgroupOf X ≤ C.subgroupOf X := by
    have h1 : (kerMOf M X).subgroupOf X ≤ (QuotientGroup.mk' (C.subgroupOf X)).ker :=
      (Subgroup.map_eq_bot_iff ((kerMOf M X).subgroupOf X)).mp hKq_bot
    rwa [QuotientGroup.ker_mk'] at h1
  intro k hk
  have hkX : k ∈ X := hKX hk
  have h1 : (⟨k, hkX⟩ : ↥X) ∈ (kerMOf M X).subgroupOf X := hk
  exact Subgroup.mem_subgroupOf.mp (hle h1)

end CFSG.LocalAnalysis.WeakClosure81

end
