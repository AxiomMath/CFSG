module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3b
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecIn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem exists_subgroups_of_innAut_data {W : Type} [Group W] {X₁ X₂ S : Subgroup (MulAut W)}
    (hS₁ : S ≤ X₁) (hS₂ : S ≤ X₂) (h₁ : ¬ innAutOf W ≤ X₁) (h₂ : ¬ innAutOf W ≤ X₂)
    (hsup : (X₁ ⊓ innAutOf W) ⊔ (X₂ ⊓ innAutOf W) = innAutOf W) :
    ∃ M₁ M₂ : Subgroup W, M₁ ≠ ⊥ ∧ M₂ ≠ ⊥ ∧ M₁ ≠ ⊤ ∧ M₂ ≠ ⊤ ∧ M₁ ⊔ M₂ = ⊤ ∧
      (∀ σ ∈ S, ∀ w : W, σ w ∈ M₁ ↔ w ∈ M₁) ∧ (∀ σ ∈ S, ∀ w : W, σ w ∈ M₂ ↔ w ∈ M₂) := by
  let c : W →* MulAut W := MulAut.conj
  let M₁ : Subgroup W := X₁.comap c
  let M₂ : Subgroup W := X₂.comap c
  have hcrange : c.range = innAutOf W := rfl
  have hcomapRange : (innAutOf W).comap c = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [Subgroup.mem_comap]
    change c w ∈ c.range
    exact MonoidHom.mem_range.2 ⟨w, rfl⟩
  have hMtop₁ : M₁ ≠ ⊤ := by
    intro htop
    apply h₁
    rw [← hcrange]
    intro α hα
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hα
    have hw : w ∈ M₁ := by rw [htop]; exact Subgroup.mem_top w
    exact Subgroup.mem_comap.1 hw
  have hMtop₂ : M₂ ≠ ⊤ := by
    intro htop
    apply h₂
    rw [← hcrange]
    intro α hα
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hα
    have hw : w ∈ M₂ := by rw [htop]; exact Subgroup.mem_top w
    exact Subgroup.mem_comap.1 hw
  have hMsup : M₁ ⊔ M₂ = ⊤ := by
    have hle₁ : X₁ ⊓ innAutOf W ≤ c.range := by rw [hcrange]; exact inf_le_right
    have hle₂ : X₂ ⊓ innAutOf W ≤ c.range := by rw [hcrange]; exact inf_le_right
    have h := Subgroup.comap_sup_eq_of_le_range (f := c) hle₁ hle₂
    rw [Subgroup.comap_inf, Subgroup.comap_inf, hcomapRange, inf_top_eq, inf_top_eq] at h
    change M₁ ⊔ M₂ = ((X₁ ⊓ innAutOf W) ⊔ (X₂ ⊓ innAutOf W)).comap c at h
    rw [hsup, hcomapRange] at h
    exact h
  have hMbot₁ : M₁ ≠ ⊥ := by
    intro hbot
    apply hMtop₂
    rw [← hMsup, hbot, bot_sup_eq]
  have hMbot₂ : M₂ ≠ ⊥ := by
    intro hbot
    apply hMtop₁
    rw [← hMsup, hbot, sup_bot_eq]
  have hconj : ∀ (σ : MulAut W) (w : W), c (σ w) = σ * c w * σ⁻¹ := by
    intro σ w
    change MulAut.conj (σ w) = σ * MulAut.conj w * σ⁻¹
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hinv₁ : ∀ σ ∈ S, ∀ w : W, σ w ∈ M₁ ↔ w ∈ M₁ := by
    intro σ hσ w
    have hσX : σ ∈ X₁ := hS₁ hσ
    have hσiX : σ⁻¹ ∈ X₁ := X₁.inv_mem hσX
    have hc : c (σ w) ∈ X₁ ↔ c w ∈ X₁ := by
      rw [hconj]
      constructor
      · intro h
        have h' : σ⁻¹ * (σ * c w * σ⁻¹) * σ ∈ X₁ :=
          X₁.mul_mem (X₁.mul_mem hσiX h) hσX
        rwa [show σ⁻¹ * (σ * c w * σ⁻¹) * σ = c w by group] at h'
      · intro h
        exact X₁.mul_mem (X₁.mul_mem hσX h) hσiX
    show c (σ w) ∈ X₁ ↔ c w ∈ X₁
    exact hc
  have hinv₂ : ∀ σ ∈ S, ∀ w : W, σ w ∈ M₂ ↔ w ∈ M₂ := by
    intro σ hσ w
    have hσX : σ ∈ X₂ := hS₂ hσ
    have hσiX : σ⁻¹ ∈ X₂ := X₂.inv_mem hσX
    have hc : c (σ w) ∈ X₂ ↔ c w ∈ X₂ := by
      rw [hconj]
      constructor
      · intro h
        have h' : σ⁻¹ * (σ * c w * σ⁻¹) * σ ∈ X₂ :=
          X₂.mul_mem (X₂.mul_mem hσiX h) hσX
        rwa [show σ⁻¹ * (σ * c w * σ⁻¹) * σ = c w by group] at h'
      · intro h
        exact X₂.mul_mem (X₂.mul_mem hσX h) hσiX
    show c (σ w) ∈ X₂ ↔ c w ∈ X₂
    exact hc
  exact ⟨M₁, M₂, hMbot₁, hMbot₂, hMtop₁, hMtop₂, hMsup, hinv₁, hinv₂⟩

@[expose] def AlmostSimpleOvergroupPair (L₀ : Type) [Group L₀] : Prop :=
  ∀ A S : Subgroup (MulAut L₀), AlmostSimpleData L₀ A S →
    ∃ X₁ X₂ : Subgroup (MulAut L₀),
      S ≤ X₁ ∧ S ≤ X₂ ∧ X₁ ≤ A ∧ X₂ ≤ A ∧
      ¬ innAutOf L₀ ≤ X₁ ∧ ¬ innAutOf L₀ ≤ X₂ ∧
      (X₁ ⊓ innAutOf L₀) ⊔ (X₂ ⊓ innAutOf L₀) = innAutOf L₀

theorem exists_subgroups_of_almostSimple_overgroups
    {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (hOver : AlmostSimpleOvergroupPair ↥L) (hT : IsPGroup 2 T) :
    ∃ M₁ M₂ : Subgroup G, M₁ ≤ L ∧ M₂ ≤ L ∧ M₁ ≠ ⊥ ∧ M₂ ≠ ⊥ ∧ M₁ ≠ L ∧ M₂ ≠ L ∧
      M₁ ⊔ M₂ = L ∧
      (∀ t ∈ T, conjSub t L = L → conjSub t M₁ = M₁ ∧ conjSub t M₂ = M₂) := by
  let B : Subgroup G := T ⊓ Subgroup.normalizer (L : Set G)
  have hB : IsPGroup 2 B := hT.to_le inf_le_left
  let ρ : ↥B →* MulAut ↥L :=
    { toFun := fun t => H13.P31Sec.conjOn L t.2.2
      map_one' := by
        refine MulEquiv.ext fun m => Subtype.ext ?_
        simp [H13.P31Sec.coe_conjOn]
      map_mul' := by
        intro g h
        refine MulEquiv.ext fun m => Subtype.ext ?_
        simp [H13.P31Sec.coe_conjOn, mul_assoc] }
  have hρS₀ : IsPGroup 2 ρ.range :=
    IsPGroup.of_surjective hB ρ.rangeRestrict ρ.rangeRestrict_surjective
  let A : Subgroup (MulAut ↥L) := innAutOf ↥L ⊔ ρ.range
  haveI : Finite (MulAut ↥L) :=
    Finite.of_injective (fun f : MulAut ↥L => (f : ↥L → ↥L)) DFunLike.coe_injective
  obtain ⟨S, hSylowOf, hρS⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_isSylowOf_ge_of_isPGroup hρS₀
      (le_sup_right : ρ.range ≤ A)
  have hSylowIn : IsSylowIn 2 S A := isSylowOf_two_iff_isSylowIn.mp hSylowOf
  have hASD : AlmostSimpleData ↥L A S := by
    refine ⟨le_sup_left, hSylowIn, ?_⟩
    refine le_antisymm (sup_le le_sup_left hSylowIn.1) ?_
    exact sup_le_sup_left hρS _
  obtain ⟨X₁, X₂, hS₁, hS₂, hX₁A, hX₂A, hX₁, hX₂, hXsup⟩ := hOver A S hASD
  obtain ⟨M₁', M₂', hne₁', hne₂', hlt₁', hlt₂', hsup', hinv₁, hinv₂⟩ :=
    exists_subgroups_of_innAut_data (W := ↥L) hS₁ hS₂ hX₁ hX₂ hXsup
  let M₁ : Subgroup G := M₁'.map L.subtype
  let M₂ : Subgroup G := M₂'.map L.subtype
  have hM₁le : M₁ ≤ L := Subgroup.map_subtype_le M₁'
  have hM₂le : M₂ ≤ L := Subgroup.map_subtype_le M₂'
  have hMbot₁ : M₁ ≠ ⊥ := by
    intro hbot
    apply hne₁'
    apply Subgroup.map_injective L.subtype_injective
    rw [show M₁'.map L.subtype = (⊥ : Subgroup G) from hbot, Subgroup.map_bot]
  have hMbot₂ : M₂ ≠ ⊥ := by
    intro hbot
    apply hne₂'
    apply Subgroup.map_injective L.subtype_injective
    rw [show M₂'.map L.subtype = (⊥ : Subgroup G) from hbot, Subgroup.map_bot]
  have hMlt₁ : M₁ ≠ L := by
    intro h
    apply hlt₁'
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact h
  have hMlt₂ : M₂ ≠ L := by
    intro h
    apply hlt₂'
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact h
  have hMsup : M₁ ⊔ M₂ = L := by
    change M₁'.map L.subtype ⊔ M₂'.map L.subtype = L
    rw [← Subgroup.map_sup (M₁') (M₂') L.subtype, hsup', Subgroup.map_top,
      Subgroup.range_subtype]
  have hnorm : ∀ t ∈ T, conjSub t L = L → conjSub t M₁ = M₁ ∧ conjSub t M₂ = M₂ := by
    intro t htT htL
    have htn : t ∈ Subgroup.normalizer (L : Set G) :=
      A1b.conjSub_eq_iff_mem_normalizer.mp htL
    let t' : ↥B := ⟨t, htT, htn⟩
    have hσS : ρ t' ∈ S := hρS (MonoidHom.mem_range.2 ⟨t', rfl⟩)
    have hσcoe : ∀ w : ↥L, ((ρ t' w : ↥L) : G) = t * (w : G) * t⁻¹ := by
      intro w
      change ((H13.P31Sec.conjOn L t'.2.2 w : ↥L) : G) = t * (w : G) * t⁻¹
      rw [H13.P31Sec.coe_conjOn]
    have hconj_eq (M' : Subgroup ↥L) (M : Subgroup G) (hM : M = M'.map L.subtype)
        (hinv : ∀ σ ∈ S, ∀ w : ↥L, σ w ∈ M' ↔ w ∈ M') : conjSub t M = M := by
      rw [hM]
      have hmemM : ∀ w : ↥L, (w : G) ∈ M'.map L.subtype ↔ w ∈ M' := by
        intro w
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨m, hm, hmw⟩
          rwa [show m = w from Subtype.ext hmw] at hm
        · intro hw
          exact ⟨w, hw, rfl⟩
      apply le_antisymm
      · intro x hx
        rw [A1b.mem_conjSub_iff] at hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨w, hw, hwx⟩ := hx
        have hxw : x = ((ρ t' w : ↥L) : G) := by
          rw [hσcoe, show (w : G) = t⁻¹ * x * t from hwx]
          group
        rw [hxw]
        exact (hmemM (ρ t' w)).2 ((hinv (ρ t') hσS w).mpr hw)
      · intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨m, hm, hmx⟩ := hx
        rw [A1b.mem_conjSub_iff]
        let w : ↥L := (ρ t')⁻¹ m
        have hσw : (ρ t') w = m := by simp [w]
        have hwM : w ∈ M' := (hinv (ρ t') hσS w).mp (by rw [hσw]; exact hm)
        have hxw : t⁻¹ * x * t = (w : G) := by
          have hx_eq : x = ((ρ t') w : ↥L) := by rw [hσw]; exact hmx.symm
          rw [hx_eq, hσcoe w]
          group
        rw [hxw]
        exact (hmemM w).2 hwM
    exact ⟨hconj_eq M₁' M₁ (by rfl) hinv₁, hconj_eq M₂' M₂ (by rfl) hinv₂⟩
  exact ⟨M₁, M₂, hM₁le, hM₂le, hMbot₁, hMbot₂, hMlt₁, hMlt₂, hMsup, hnorm⟩

end CFSG.LocalAnalysis.WeakClosure81
