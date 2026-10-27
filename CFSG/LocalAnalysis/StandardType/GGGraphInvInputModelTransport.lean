module

public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelDefs
public import CFSG.LocalAnalysis.StandardType.GGOuterInvGraphInv

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

@[expose] def GGGraphInvInputModelAt
    (t : StatedLieTag) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C), Function.Surjective π ∧
      π.ker = Subgroup.center (ggU t n f).K ∧ GGGraphInvInputModel C

private noncomputable def ggOmW6a_phi
    {C G : Type} [Group C] [Group G] (H₀ M : Subgroup G)
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G)) (Θ : C ≃* H₀) :
    M →* MulAut C :=
  ((MulAut.congr Θ).symm.toMonoidHom).comp
    ((Subgroup.normalizerMonoidHom H₀).comp (Subgroup.inclusion hMnorm))

private noncomputable def ggOmW6a_alpha
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G} (Θ : C ≃* H₀)
    (r : G) (hr : r ∈ Subgroup.normalizer (H₀ : Set G)) : MulAut C :=
  (Θ.trans (Subgroup.normalizerMonoidHom H₀ ⟨r, hr⟩)).trans Θ.symm

private theorem ggOmW6aA_phi_eq
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G)) (Θ : C ≃* H₀)
    (x : M) (g : C) :
    (ggOmW6a_phi H₀ M hMnorm Θ x) g =
      Θ.symm ((Subgroup.normalizerMonoidHom H₀) (Subgroup.inclusion hMnorm x) (Θ g)) :=
  rfl

private theorem ggOmW6a_phi_apply
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G)) (Θ : C ≃* H₀)
    (x : M) (g : C) :
    (Θ ((ggOmW6a_phi H₀ M hMnorm Θ x) g) : G) = (x : G) * Θ g * (x : G)⁻¹ := by
  rw [ggOmW6aA_phi_eq (H₀ := H₀) (M := M) hMnorm Θ x g, MulEquiv.apply_symm_apply,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [Subgroup.coe_inclusion]

private theorem ggOmW6a_phi_injective
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G)) (Θ : C ≃* H₀)
    (hC : Subgroup.centralizer (H₀ : Set G) = ⊥) :
    Function.Injective (ggOmW6a_phi H₀ M hMnorm Θ) := by
  intro x y hxy
  have hcomm : ((y : M) : G)⁻¹ * (x : G) ∈ Subgroup.centralizer (H₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨g, hg⟩ := Θ.surjective ⟨h, hh⟩
    have hg' : (Θ g : G) = h := congrArg Subtype.val hg
    have hxyg : (Θ ((ggOmW6a_phi H₀ M hMnorm Θ x) g) : G) =
        (Θ ((ggOmW6a_phi H₀ M hMnorm Θ y) g) : G) := by rw [hxy]
    have hx := ggOmW6a_phi_apply hMnorm Θ x g
    have hy := ggOmW6a_phi_apply hMnorm Θ y g
    have key : (y : G) * h * (y : G)⁻¹ = (x : G) * h * (x : G)⁻¹ := by
      rw [← hg', ← hy, ← hx, hxyg]
    calc
      h * (((y : M) : G)⁻¹ * (x : G))
          = ((y : M) : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (x : G) := by group
      _ = ((y : M) : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * (x : G) := by rw [key]
      _ = (((y : M) : G)⁻¹ * (x : G)) * h := by group
  have hz : ((y : M) : G)⁻¹ * (x : G) = 1 := by
    have hmem := hcomm
    rw [hC, Subgroup.mem_bot] at hmem
    exact hmem
  have hxy' : (x : G) = (y : G) := by
    calc (x : G) = (y : G) * ((y : G)⁻¹ * (x : G)) := by group
      _ = (y : G) * 1 := by rw [hz]
      _ = (y : G) := mul_one _
  exact Subtype.ext hxy'

private theorem ggOmW6aA_mem_of_phi_mem_range
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G)) (Θ : C ≃* H₀)
    (hC : Subgroup.centralizer (H₀ : Set G) = ⊥)
    (x : M)
    (hx : ggOmW6a_phi H₀ M hMnorm Θ x ∈ (MulAut.conj : C →* MulAut C).range) :
    (x : G) ∈ H₀ := by
  rw [MonoidHom.mem_range] at hx
  obtain ⟨c, hc⟩ := hx
  have hrel : ∀ g : C, (x : G) * (Θ g : G) * (x : G)⁻¹ =
      (Θ c : G) * (Θ g : G) * (Θ c : G)⁻¹ := by
    intro g
    simp only [← ggOmW6a_phi_apply hMnorm Θ x g, ← hc, MulAut.conj_apply, map_mul,
      map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hcomm : (Θ c : G)⁻¹ * (x : G) ∈ Subgroup.centralizer (H₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨g, hg⟩ := Θ.surjective ⟨h, hh⟩
    have hg' : (Θ g : G) = h := congrArg Subtype.val hg
    rw [← hg']
    have key : (Θ c : G)⁻¹ * (x : G) * (Θ g : G) =
        (Θ g : G) * ((Θ c : G)⁻¹ * (x : G)) := by
      calc
        (Θ c : G)⁻¹ * (x : G) * (Θ g : G)
            = (Θ c : G)⁻¹ * ((x : G) * (Θ g : G) * (x : G)⁻¹) * (x : G) := by
              group
        _ = (Θ c : G)⁻¹ * ((Θ c : G) * (Θ g : G) * (Θ c : G)⁻¹) * (x : G) := by
              rw [hrel g]
        _ = (Θ g : G) * ((Θ c : G)⁻¹ * (x : G)) := by group
    exact key.symm
  have hz : (Θ c : G)⁻¹ * (x : G) = 1 := by
    have hmem := hcomm
    rw [hC, Subgroup.mem_bot] at hmem
    exact hmem
  have hxeq : (x : G) = (Θ c : G) := by
    calc (x : G) = (Θ c : G) * ((Θ c : G)⁻¹ * (x : G)) := by group
      _ = (Θ c : G) * 1 := by rw [hz]
      _ = (Θ c : G) := mul_one _
  rw [hxeq]
  exact (Θ c).2

private theorem ggOmW6aA_phi_mem_range_of_mem
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G)) (Θ : C ≃* H₀)
    (x : M) (hx : (x : G) ∈ H₀) :
    ggOmW6a_phi H₀ M hMnorm Θ x ∈ (MulAut.conj : C →* MulAut C).range := by
  rw [MonoidHom.mem_range]
  refine ⟨Θ.symm ⟨x, hx⟩, ?_⟩
  ext g
  apply Θ.injective
  apply Subtype.ext
  simp only [ggOmW6a_phi_apply hMnorm Θ x g, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]

private theorem ggOmW6a_phi_mem_inn_iff
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G)) (Θ : C ≃* H₀)
    (hC : Subgroup.centralizer (H₀ : Set G) = ⊥) (x : M) :
    ggOmW6a_phi H₀ M hMnorm Θ x ∈ (MulAut.conj : C →* MulAut C).range ↔
      (x : G) ∈ H₀ := by
  constructor
  · exact ggOmW6aA_mem_of_phi_mem_range hMnorm Θ hC x
  · intro hx
    exact ggOmW6aA_phi_mem_range_of_mem hMnorm Θ x hx

private theorem ggOmW6a_index_eq
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G))
    (Θ : C ≃* H₀) (hC : Subgroup.centralizer (H₀ : Set G) = ⊥)
    (Q : Subgroup G) (hQM : Q ≤ M) :
    (H₀.subgroupOf Q).index =
      (((MulAut.conj : C →* MulAut C).range).subgroupOf
        ((Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ))).index := by
  have hφinj : Function.Injective (ggOmW6a_phi H₀ M hMnorm Θ) :=
    ggOmW6a_phi_injective hMnorm Θ hC
  have hInn : (MulAut.conj : C →* MulAut C).range ⊓
      (Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ) =
      ((H₀.subgroupOf M) ⊓ (Q.subgroupOf M)).map
        (ggOmW6a_phi H₀ M hMnorm Θ) := by
    ext y
    constructor
    · rintro ⟨hyInn, hyP⟩
      obtain ⟨x, hxQ, rfl⟩ := Subgroup.mem_map.mp hyP
      refine Subgroup.mem_map.mpr ⟨x, Subgroup.mem_inf.mpr ⟨?_, hxQ⟩, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact (ggOmW6a_phi_mem_inn_iff hMnorm Θ hC (x : M)).mp hyInn
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxH, hxQ⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_subgroupOf] at hxH
      exact ⟨(ggOmW6a_phi_mem_inn_iff hMnorm Θ hC (x : M)).mpr hxH,
        Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩⟩
  have key : (MulAut.conj : C →* MulAut C).range.relIndex
      ((Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ)) = H₀.relIndex Q := by
    calc (MulAut.conj : C →* MulAut C).range.relIndex
          ((Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ))
        = ((MulAut.conj : C →* MulAut C).range ⊓
            (Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ)).relIndex
            ((Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ)) :=
          (Subgroup.inf_relIndex_right
            (H := (MulAut.conj : C →* MulAut C).range)
            (K := (Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ))).symm
      _ = (((H₀.subgroupOf M) ⊓ (Q.subgroupOf M)).map
            (ggOmW6a_phi H₀ M hMnorm Θ)).relIndex
            ((Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ)) := by rw [hInn]
      _ = ((H₀.subgroupOf M) ⊓ (Q.subgroupOf M)).relIndex (Q.subgroupOf M) :=
          Subgroup.relIndex_map_map_of_injective
            (f := ggOmW6a_phi H₀ M hMnorm Θ)
            ((H₀.subgroupOf M) ⊓ (Q.subgroupOf M)) (Q.subgroupOf M) hφinj
      _ = (H₀.subgroupOf M).relIndex (Q.subgroupOf M) :=
          Subgroup.inf_relIndex_right (H := H₀.subgroupOf M) (K := Q.subgroupOf M)
      _ = H₀.relIndex Q :=
          Subgroup.relIndex_subgroupOf (H := H₀) (K := Q) (L := M) hQM
  show (H₀.subgroupOf Q).index = (MulAut.conj : C →* MulAut C).range.relIndex
      ((Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ))
  rw [key]
  rfl

private theorem ggOmW6a_index_le
    {C G : Type} [Group C] [Group G] {H₀ M : Subgroup G}
    (hMnorm : M ≤ Subgroup.normalizer (H₀ : Set G))
    (Θ : C ≃* H₀) (hC : Subgroup.centralizer (H₀ : Set G) = ⊥)
    (hOut : GGOutTwoPartLeTwo C)
    (Q : Subgroup G) (hQM : Q ≤ M) (hQ2 : IsPGroup 2 Q) :
    (H₀.subgroupOf Q).index ≤ 2 := by
  have hQ2' : IsPGroup 2 (Q.subgroupOf M) := IsPGroup.comap_subtype hQ2 (K := M)
  have hP2 : IsPGroup 2 ((Q.subgroupOf M).map (ggOmW6a_phi H₀ M hMnorm Θ)) :=
    IsPGroup.map hQ2' (ggOmW6a_phi H₀ M hMnorm Θ)
  rw [ggOmW6a_index_eq hMnorm Θ hC Q hQM]
  exact hOut _ hP2

private theorem ggOmW6aC_alpha_apply
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G}
    (Θ : C ≃* H₀) {r : G} (hr : r ∈ Subgroup.normalizer (H₀ : Set G)) (c : C) :
    ggOmW6a_alpha Θ r hr c =
      Θ.symm ((Subgroup.normalizerMonoidHom H₀ ⟨r, hr⟩) (Θ c)) := rfl

private theorem ggOmW6a_mem_fixSubgroup_iff
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G}
    (Θ : C ≃* H₀) {r : G} (hr : r ∈ Subgroup.normalizer (H₀ : Set G)) (c : C) :
    c ∈ ggFixSubgroup (ggOmW6a_alpha Θ r hr) ↔
      (Θ c : G) ∈ Subgroup.centralizer {r} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hc
    change ggOmW6a_alpha Θ r hr c = c at hc
    have h1 : (Subgroup.normalizerMonoidHom H₀ ⟨r, hr⟩) (Θ c) = Θ c := by
      have h := congrArg Θ hc
      rw [ggOmW6aC_alpha_apply, MulEquiv.apply_symm_apply] at h
      exact h
    have h2 := congrArg (fun z : H₀ => (z : G)) h1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  · intro hc
    change ggOmW6a_alpha Θ r hr c = c
    apply Θ.injective
    rw [ggOmW6aC_alpha_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr hc.symm

private theorem ggOmW6a_transport_normal
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G}
    (Θ : C ≃* H₀) {r : G} (hr : r ∈ Subgroup.normalizer (H₀ : Set G))
    (hNormal : ∀ N' : Subgroup C, N' ≤ ggFixSubgroup (ggOmW6a_alpha Θ r hr) →
        IsPGroup 2 N' →
        (∀ y ∈ N', ∀ z ∈ ggFixSubgroup (ggOmW6a_alpha Θ r hr), z * y * z⁻¹ ∈ N') →
        N' = ⊥) :
    ∀ N : Subgroup G, N ≤ H₀ ⊓ Subgroup.centralizer {r} → IsPGroup 2 N →
      (∀ y ∈ N, ∀ z ∈ H₀ ⊓ Subgroup.centralizer {r}, z * y * z⁻¹ ∈ N) → N = ⊥ := by
  intro N hN hN2 hnorm
  let N' : Subgroup C := (N.subgroupOf H₀).map Θ.symm.toMonoidHom
  have hN'fix : N' ≤ ggFixSubgroup (ggOmW6a_alpha Θ r hr) := by
    intro c hc
    rw [ggOmW6a_mem_fixSubgroup_iff]
    obtain ⟨a, haN, hac⟩ := Subgroup.mem_map.mp hc
    rw [← hac]
    change (Θ (Θ.symm a) : G) ∈ Subgroup.centralizer {r}
    rw [MulEquiv.apply_symm_apply]
    exact (hN (show (a : G) ∈ N from haN)).2
  have hN'2 : IsPGroup 2 N' :=
    IsPGroup.map (IsPGroup.comap_of_injective hN2 H₀.subtype H₀.subtype_injective)
      Θ.symm.toMonoidHom
  have hN'norm : ∀ y ∈ N', ∀ z ∈ ggFixSubgroup (ggOmW6a_alpha Θ r hr),
      z * y * z⁻¹ ∈ N' := by
    intro y hy z hz
    obtain ⟨a, haN, hay⟩ := Subgroup.mem_map.mp hy
    rw [← hay]
    have hzK : (Θ z : G) ∈ H₀ ⊓ Subgroup.centralizer {r} :=
      ⟨(Θ z).2, (ggOmW6a_mem_fixSubgroup_iff Θ hr z).mp hz⟩
    have hmem : ((Θ z) * a * (Θ z)⁻¹ : H₀) ∈ N.subgroupOf H₀ := by
      change ((Θ z : G) * (a : G) * (Θ z : G)⁻¹) ∈ N
      exact hnorm (a : G) (show (a : G) ∈ N from haN) (Θ z) hzK
    refine Subgroup.mem_map.mpr ⟨(Θ z) * a * (Θ z)⁻¹, hmem, ?_⟩
    apply Θ.injective
    change Θ (Θ.symm (Θ z * a * (Θ z)⁻¹)) = Θ (z * Θ.symm a * z⁻¹)
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hN'bot : N' = ⊥ := hNormal N' hN'fix hN'2 hN'norm
  apply le_bot_iff.mp
  intro g hg
  rw [Subgroup.mem_bot]
  have hgH : g ∈ H₀ := (hN hg).1
  have hmem : Θ.symm (⟨g, hgH⟩ : H₀) ∈ N' :=
    Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, hg, rfl⟩
  rw [hN'bot, Subgroup.mem_bot] at hmem
  have hone : (⟨g, hgH⟩ : H₀) = 1 := by
    apply Θ.symm.injective
    rw [hmem, map_one]
  exact Subtype.ext_iff.mp hone

private theorem ggOmW6aC_fix_map_le
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G}
    (Θ : C ≃* H₀) {r : G} (hr : r ∈ Subgroup.normalizer (H₀ : Set G)) :
    (ggFixSubgroup (ggOmW6a_alpha Θ r hr)).map (H₀.subtype.comp Θ.toMonoidHom) ≤
      H₀ ⊓ Subgroup.centralizer {r} := by
  intro y hy
  obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
  rw [← hcy]
  change (Θ c : G) ∈ H₀ ⊓ Subgroup.centralizer {r}
  exact ⟨(Θ c).2, (ggOmW6a_mem_fixSubgroup_iff Θ hr c).mp hc⟩

private theorem ggOmW6aC_fix_comap_eq
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G}
    (Θ : C ≃* H₀) {r : G} (hr : r ∈ Subgroup.normalizer (H₀ : Set G)) :
    (H₀ ⊓ Subgroup.centralizer {r}).comap (H₀.subtype.comp Θ.toMonoidHom) =
      ggFixSubgroup (ggOmW6a_alpha Θ r hr) := by
  ext c
  constructor
  · intro hc
    rw [Subgroup.mem_comap] at hc
    exact (ggOmW6a_mem_fixSubgroup_iff Θ hr c).mpr hc.2
  · intro hc
    rw [Subgroup.mem_comap]
    exact ⟨(Θ c).2, (ggOmW6a_mem_fixSubgroup_iff Θ hr c).mp hc⟩

private theorem ggOmW6a_transport_notPGroup
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G}
    (Θ : C ≃* H₀) {r : G} (hr : r ∈ Subgroup.normalizer (H₀ : Set G))
    (hNot2 : ¬ IsPGroup 2 ↥(ggFixSubgroup (ggOmW6a_alpha Θ r hr))) :
    ¬ IsPGroup 2 ↥(H₀ ⊓ Subgroup.centralizer {r}) := by
  intro h2
  have hinj : Function.Injective (H₀.subtype.comp Θ.toMonoidHom) :=
    fun a b h => Θ.injective (Subtype.ext h)
  have h := IsPGroup.comap_of_injective h2 (H₀.subtype.comp Θ.toMonoidHom) hinj
  rw [ggOmW6aC_fix_comap_eq Θ hr] at h
  exact hNot2 h

private theorem ggOmW6a_transport_centralizer
    {C G : Type} [Group C] [Group G] {H₀ : Subgroup G}
    (Θ : C ≃* H₀) {r : G} (hr : r ∈ Subgroup.normalizer (H₀ : Set G))
    (hCC : Subgroup.centralizer
        ((ggFixSubgroup (ggOmW6a_alpha Θ r hr) : Subgroup C) : Set C) = ⊥) :
    H₀ ⊓ Subgroup.centralizer
      ((H₀ ⊓ Subgroup.centralizer {r} : Subgroup G) : Set G) = ⊥ := by
  have hle : H₀ ⊓ Subgroup.centralizer
      ((H₀ ⊓ Subgroup.centralizer {r} : Subgroup G) : Set G) ≤
      (Subgroup.centralizer ((ggFixSubgroup (ggOmW6a_alpha Θ r hr) : Subgroup C) : Set C)).map
        (H₀.subtype.comp Θ.toMonoidHom) := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨Θ.symm ⟨y, hy.1⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply Θ.injective
      apply Subtype.ext
      have hsK : (Θ s : G) ∈ H₀ ⊓ Subgroup.centralizer {r} :=
        ggOmW6aC_fix_map_le Θ hr (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
      have hcomm := (Subgroup.mem_centralizer_iff.mp hy.2) (Θ s) hsK
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] using hcomm
    · simp
  rw [hCC, Subgroup.map_bot] at hle
  exact le_bot_iff.mp hle

private noncomputable def ggOmW6a_modelEquiv
    {U C G : Type*} [Group U] [Group C] [Group G]
    (ψ : U →* G) (π : U →* C) (hπ : Function.Surjective π)
    (hker : π.ker = ψ.ker) : C ≃* ψ.range :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange ψ))

private theorem ggOmW6a_ker_eq_center
    {U G : Type*} [Group U] [Group G] (ψ : U →* G)
    (hker : ψ.ker ≤ Subgroup.center U)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ψ.ker = Subgroup.center U := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

private theorem ggOmW6a_diagInner
    {t : StatedLieTag} (hI : GGInnerTag t) :
    GGPsiDiagInnerAt t :=
  ggPsiDiagInnerAt_of_ggInnerTag t hI

theorem ggGraphInvInputAt_of_model
    {t : StatedLieTag} (hI : GGInnerTag t)
    (h : GGGraphInvInputModelAt t) : GGGraphInvInputAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b L₁ hb hb1 hL₁ r hrM hr2 hrb hrG₀ hle
  obtain ⟨C, _, π, hπ, hπker, hmodel⟩ := h n f hctx.2.2.2.1.1 hctx.2.2.2.1.2
  have hpsi : GGPsiDiagInnerAt t := ggOmW6a_diagInner hI
  have hBsG0 : Bs ≤ ggG0 p B x L D J := fun y hy =>
    ggG1_le_ggG0_of_diagInner hpsi hctx s1 (ggBs_le_ggG1 hctx hy)
  have hbG0 : b ∈ ggG0 p B x L D J := hBsG0 hb
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]; exact s1.1
  have hψ : ψ.ker = Subgroup.center (ggU t n f).K :=
    ggOmW6a_ker_eq_center ψ hctx.2.2.2.2.1.2 hC'
  let Θ : C ≃* ↥(ggG0 p B x L D J) :=
    (ggOmW6a_modelEquiv ψ π hπ (hπker.trans hψ.symm)).trans
      (MulEquiv.subgroupCongr hctx.range_eq)
  let b' : C := Θ.symm ⟨b, hbG0⟩
  have hb'Θ : Θ b' = ⟨b, hbG0⟩ := Θ.apply_symm_apply _
  have hb'1 : b' ≠ 1 := by
    intro h1
    rw [h1, map_one] at hb'Θ
    exact hb1 (Subtype.ext_iff.mp hb'Θ.symm)
  have hb'p : b' ^ p = 1 := by
    apply Θ.injective
    rw [map_pow, map_one, hb'Θ]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hctx.bstar.2.1.2 b hb
  have hrr : r * r = 1 := by
    have hh := pow_orderOf_eq_one r
    rw [hr2, pow_two] at hh
    exact hh
  let φr : MulAut ↥(ggG0 p B x L D J) :=
    Subgroup.normalizerMonoidHom (ggG0 p B x L D J) ⟨r, hrM⟩
  have hφr2 : φr * φr = 1 := by
    change Subgroup.normalizerMonoidHom (ggG0 p B x L D J) ⟨r, hrM⟩ *
      Subgroup.normalizerMonoidHom (ggG0 p B x L D J) ⟨r, hrM⟩ = 1
    rw [← map_mul]
    have h2 : (⟨r, hrM⟩ : ↥(Subgroup.normalizer (ggG0 p B x L D J : Set G))) *
        ⟨r, hrM⟩ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact hrr
    rw [h2, map_one]
  let α : MulAut C := ggOmW6a_alpha Θ r hrM
  have hα2 : α * α = 1 := by
    ext g
    rw [MulAut.mul_apply, MulAut.one_apply]
    change Θ.symm (φr (Θ (Θ.symm (φr (Θ g))))) = g
    rw [MulEquiv.apply_symm_apply, ← MulAut.mul_apply, hφr2, MulAut.one_apply,
      MulEquiv.symm_apply_apply]
  have hφrb : φr ⟨b, hbG0⟩ = ⟨b, hbG0⟩ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hrb' : r * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp hrb
    rw [hrb', mul_assoc, mul_inv_cancel, mul_one]
  have hαb' : α b' = b' := by
    change Θ.symm (φr (Θ b')) = b'
    rw [hb'Θ, hφrb]
  have hαout : ∀ c : C, α ≠ MulAut.conj c := by
    intro c hc
    have hrel : ∀ z : C, φr (Θ z) = Θ c * Θ z * (Θ c)⁻¹ := by
      intro z
      have h1 : α z = MulAut.conj c z := congrArg (fun f : MulAut C => f z) hc
      calc φr (Θ z) = Θ (α z) := by
            change φr (Θ z) = Θ (Θ.symm (φr (Θ z)))
            rw [MulEquiv.apply_symm_apply]
        _ = Θ (MulAut.conj c z) := by rw [h1]
        _ = Θ c * Θ z * (Θ c)⁻¹ := by
            rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hcentral : (Θ c : G)⁻¹ * r ∈
        Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hz := hrel (Θ.symm ⟨y, hy⟩)
      rw [MulEquiv.apply_symm_apply] at hz
      have hz' : r * y * r⁻¹ = (Θ c : G) * y * (Θ c : G)⁻¹ := by
        have hh := congrArg (fun z : ↥(ggG0 p B x L D J) => (z : G)) hz
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hh
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hh
        exact hh
      have hconj : ((Θ c : G)⁻¹ * r) * y * ((Θ c : G)⁻¹ * r)⁻¹ = y := by
        have h1 : ((Θ c : G)⁻¹ * r) * y * ((Θ c : G)⁻¹ * r)⁻¹ =
            (Θ c : G)⁻¹ * (r * y * r⁻¹) * (Θ c : G) := by group
        rw [h1, hz']
        group
      have hu : ((Θ c : G)⁻¹ * r) * y = y * ((Θ c : G)⁻¹ * r) := by
        calc ((Θ c : G)⁻¹ * r) * y =
              ((Θ c : G)⁻¹ * r) * y * ((Θ c : G)⁻¹ * r)⁻¹ *
                ((Θ c : G)⁻¹ * r) := by group
          _ = y * ((Θ c : G)⁻¹ * r) := by rw [hconj]
      exact hu.symm
    rw [s1.1, Subgroup.mem_bot] at hcentral
    apply hrG₀
    have hr_eq : r = (Θ c : G) := by
      calc r = (Θ c : G) * ((Θ c : G)⁻¹ * r) := by group
        _ = (Θ c : G) * 1 := by rw [hcentral]
        _ = (Θ c : G) := mul_one _
    rw [hr_eq]
    exact (Θ c).2
  have hmapK : ((ggG0 p B x L D J ⊓ Subgroup.centralizer {b}).subgroupOf
      (ggG0 p B x L D J)).map Θ.symm.toMonoidHom = Subgroup.centralizer {b'} := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Θ.injective
      change Θ (Θ.symm y * b') = Θ (b' * Θ.symm y)
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb'Θ]
      apply Subtype.ext
      have hy' : (y : G) * b = b * (y : G) := by
        have hmem : (y : G) ∈ Subgroup.centralizer {b} := by
          have hy2 := hy
          change (y : G) ∈ ggG0 p B x L D J ⊓ Subgroup.centralizer {b} at hy2
          exact hy2.2
        exact Subgroup.mem_centralizer_singleton_iff.mp hmem
      simpa only [Subgroup.coe_mul] using hy'
    · intro hg
      refine ⟨Θ g, ?_, Θ.symm_apply_apply g⟩
      change (Θ g : G) ∈ ggG0 p B x L D J ⊓ Subgroup.centralizer {b}
      refine ⟨(Θ g).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hh := congrArg (fun x : C => Θ x) hg
      rw [map_mul, map_mul, hb'Θ] at hh
      simpa only [Subgroup.coe_mul] using Subtype.ext_iff.mp hh
  have hcomp : ∃ L₁' : Subgroup C, IsComponentOf L₁' (Subgroup.centralizer {b'}) := by
    refine ⟨(L₁.subgroupOf (ggG0 p B x L D J)).map Θ.symm.toMonoidHom, ?_⟩
    have hKQ : IsComponentOf (L₁.subgroupOf (ggG0 p B x L D J))
        ((ggG0 p B x L D J ⊓ Subgroup.centralizer {b}).subgroupOf
          (ggG0 p B x L D J)) := ggIsComponentOf_subgroupOf hL₁ inf_le_left
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := Θ.symm.toMonoidHom) Θ.symm.injective).2 hKQ
    rw [hmapK] at h1
    exact h1
  have hfix : ∀ g ∈ Subgroup.centralizer {b'}, α g = g := by
    intro g hg
    have hgG0 : (Θ g : G) ∈ ggG0 p B x L D J := (Θ g).2
    have hgb : (Θ g : G) ∈ Subgroup.centralizer {b} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have hh := congrArg (fun x : C => Θ x) hg
      rw [map_mul, map_mul, hb'Θ] at hh
      simpa only [Subgroup.coe_mul] using Subtype.ext_iff.mp hh
    have hgr : (Θ g : G) ∈ Subgroup.centralizer {r} :=
      hle (Subgroup.mem_inf.mpr ⟨hgG0, hgb⟩)
    have hfixφ : φr (Θ g) = Θ g := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hcomm : r * (Θ g : G) = (Θ g : G) * r :=
        Subgroup.mem_centralizer_iff.mp hgr r (Set.mem_singleton r)
      calc r * (Θ g : G) * r⁻¹ = (Θ g : G) * r * r⁻¹ := by rw [hcomm]
        _ = (Θ g : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]
    change Θ.symm (φr (Θ g)) = g
    rw [hfixφ, MulEquiv.symm_apply_apply]
  obtain ⟨hOut, hNormal, hNot2, hCC⟩ :=
    hmodel p b' α hctx.prime hctx.ne_two hb'1 hb'p hα2 hαout hαb' hcomp hfix
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q hQ hQ2
    exact ggOmW6a_index_le (M := ggM p B x L D J)
      le_rfl Θ s1.1 hOut Q hQ hQ2
  · intro N hN hN2 hnorm
    exact ggOmW6a_transport_normal (H₀ := ggG0 p B x L D J) Θ hrM hNormal N hN hN2 hnorm
  · exact ggOmW6a_transport_notPGroup (H₀ := ggG0 p B x L D J) Θ hrM hNot2
  · exact ggOmW6a_transport_centralizer (H₀ := ggG0 p B x L D J) Θ hrM hCC

end CFSG.StandardType
