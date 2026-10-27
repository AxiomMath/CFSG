module

public import CFSG.Monster.B.Fischer.DesignRecognition

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.Mathieu

section Transport

variable {X : Type*} (η : X ≃ X₀)

theorem map_symm_map_eq (B : Finset X₀) : (B.map η.symm.toEmbedding).map η.toEmbedding = B := by
  ext i
  simp

theorem map_map_subtype (T : Finset X) :
    (T.map η.toEmbedding).map (Function.Embedding.subtype (· ∈ X₀)) =
      T.image fun x => (η x : Fin 24) := by
  rw [Finset.map_map, Finset.map_eq_image]
  rfl

theorem map_permCongr (τ : Equiv.Perm X) (B : Finset X₀) :
    B.map (η.permCongr τ).toEmbedding =
      ((B.map η.symm.toEmbedding).map τ.toEmbedding).map η.toEmbedding := by
  rw [Finset.map_map, Finset.map_map]
  rfl

theorem permCongr_mem_designAut {𝒟 : Finset (Finset X)}
    (h𝒟 : ∀ T : Finset X, T ∈ 𝒟 ↔ T.image (fun x => (η x : Fin 24)) ∈ ℬ₀)
    {τ : Equiv.Perm X} (hτ : τ ∈ designAut 𝒟) : η.permCongr τ ∈ designAut ℬ₀X := by
  have key : ∀ T : Finset X, T.map η.toEmbedding ∈ ℬ₀X ↔ T ∈ 𝒟 := fun T => by
    rw [mem_ℬ₀X, map_map_subtype, h𝒟]
  intro B
  rw [map_permCongr, key, (mem_designAut.1 hτ) _, ← key, map_symm_map_eq]

end Transport

theorem psiHom_P0inEquiv (p : P0in) :
    psiHom (P0inEquiv p : Equiv.Perm (Fin 22)) = pPerm (p : Ppair) := by
  rw [← coe_m22EquivP0]
  have h : m22EquivP0 (P0inEquiv p) = Subgroup.subgroupOfEquivOfLe P0_le_Ppair p :=
    m22EquivP0.apply_symm_apply _
  rw [h]
  rfl

theorem isSimpleGroup_P0in :
    IsSimpleGroup P0in :=
  (MulEquiv.isSimpleGroup_congr P0inEquiv).2 fam_m22_simplicity.2.2

theorem natCard_P0in' :
    Nat.card P0in = 443520 := by
  rw [Nat.card_congr P0inEquiv.toEquiv, card_M22]

theorem eq_P0in_of_natCard
    {K : Subgroup Ppair} (hK : Nat.card K = 443520) : K = P0in := by
  have hindex : K.index = 2 := by
    have h := K.card_mul_index
    rw [hK, natCard_Ppair] at h
    omega
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hindex
  have : IsSimpleGroup P0in := isSimpleGroup_P0in
  have hle : P0in ≤ K := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf P0in) with h | h
    · exfalso
      have h1 : K.relIndex P0in ≤ K.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top
        (by rw [Subgroup.relIndex_top_right, hindex]; norm_num)
      rw [Subgroup.relIndex_top_right, hindex, Subgroup.relIndex, h, Subgroup.index_bot,
        natCard_P0in'] at h1
      omega
    · exact Subgroup.subgroupOf_eq_top.1 h
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hK, natCard_P0in'])).symm

section Image

variable {G X : Type*} [Group G] (ρ : G →* Equiv.Perm X) (η : X ≃ X₀)

@[expose] def conjRep : G →* Equiv.Perm X₀ := η.permCongrHom.toMonoidHom.comp ρ

theorem conjRep_apply (g : G) (x : X) : conjRep ρ η g (η x) = η (ρ g x) := by
  change η (ρ g (η.symm (η x))) = η (ρ g x)
  rw [Equiv.symm_apply_apply]

theorem ker_conjRep : (conjRep ρ η).ker = ρ.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, conjRep, MonoidHom.comp_apply]
  exact MulEquiv.map_eq_one_iff η.permCongrHom

theorem natCard_range_conjRep : Nat.card (conjRep ρ η).range = Nat.card ρ.range := by
  rw [conjRep, MonoidHom.range_comp]
  exact Subgroup.card_map_of_injective η.permCongrHom.injective

variable {ρ η}

theorem exists_resHom_eq
    (hρ : ∀ g, η.permCongr (ρ g) ∈ designAut ℬ₀X) {σ : Equiv.Perm X₀}
    (hσ : σ ∈ (conjRep ρ η).range) : ∃ p, resHom p = σ := by
  obtain ⟨g, rfl⟩ := hσ
  obtain ⟨p, hp⟩ := resAut_bijective.2 ⟨_, hρ g⟩
  exact ⟨p, congrArg Subtype.val hp⟩

theorem range_conjRep_eq
    (hρ : ∀ g, η.permCongr (ρ g) ∈ designAut ℬ₀X)
    (hcard : Nat.card ρ.range = 443520) : (conjRep ρ η).range = P0in.map resHom := by
  have hmap : ((conjRep ρ η).range.comap resHom).map resHom = (conjRep ρ η).range := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun σ hσ => ?_
    obtain ⟨p, hp⟩ := exists_resHom_eq hρ hσ
    exact ⟨p, by rw [SetLike.mem_coe, Subgroup.mem_comap, hp]; exact hσ, hp⟩
  have hK : Nat.card ((conjRep ρ η).range.comap resHom) = 443520 := by
    rw [← Subgroup.card_map_of_injective resHom_injective, hmap, natCard_range_conjRep, hcard]
  rw [← hmap, eq_P0in_of_natCard hK]

theorem exists_mulEquiv_M22
    (hρ : ∀ g, η.permCongr (ρ g) ∈ designAut ℬ₀X)
    (hcard : Nat.card ρ.range = 443520) :
    ∃ θ : G ⧸ ρ.ker ≃* CFSG.Blueprint.NativeSporadic.M22,
      (∀ g x, (η (ρ g x) : Fin 24) = psiHom (θ g) (η x)) ∧
      ∀ σ : Equiv.Perm X₀, σ ∈ P0in.map resHom ↔ ∃ g, ∀ x, σ (η x) = η (ρ g x) := by
  have hr := range_conjRep_eq hρ hcard
  let θ : G ⧸ ρ.ker ≃* CFSG.Blueprint.NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq (ker_conjRep ρ η).symm).trans
      ((QuotientGroup.quotientKerEquivRange (conjRep ρ η)).trans ((MulEquiv.subgroupCongr hr).trans
        ((P0in.equivMapOfInjective resHom resHom_injective).symm.trans P0inEquiv)))
  refine ⟨θ, fun g x => ?_, fun σ => ?_⟩
  · set p : P0in := (P0in.equivMapOfInjective resHom resHom_injective).symm
      ⟨conjRep ρ η g, hr ▸ ⟨g, rfl⟩⟩ with hp
    have hθ : θ g = P0inEquiv p := rfl
    have hres : resHom (p : Ppair) = conjRep ρ η g := by
      have := (P0in.equivMapOfInjective resHom resHom_injective).apply_symm_apply
        ⟨conjRep ρ η g, hr ▸ ⟨g, rfl⟩⟩
      exact congrArg Subtype.val this
    rw [hθ, psiHom_P0inEquiv, ← resHom_apply, hres, conjRep_apply]
  · rw [← hr]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, conjRep_apply ρ η g⟩
    · rintro ⟨g, hg⟩
      refine ⟨g, Equiv.ext fun i => ?_⟩
      rw [← η.apply_symm_apply i, conjRep_apply, hg]

end Image

end CFSG.Monster.B.TwoA.Fischer
