module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZI

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

abbrev imgZ (Y J : Subgroup G) : Subgroup (↥Y ⧸ Subgroup.center ↥Y) :=
  (J.subgroupOf Y).map (QuotientGroup.mk' (Subgroup.center ↥Y))

omit [Finite G] in
theorem mem_center_of_mem {Y J J' : Subgroup G} (hJY : J ≤ Y) (hY : Y ≤ J ⊔ J')
    (h12 : ⁅J, J'⁆ = ⊥) {z : G} (hz : z ∈ J) (hzc : z ∈ Subgroup.centralizer (J : Set G)) :
    (⟨z, hJY hz⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
  have hle : J ⊔ J' ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzc x hx
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h12 hz) x hx)
  rw [Subgroup.mem_center_iff]
  intro y
  have := hle (hY y.2)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact Subtype.ext this

omit [Finite G] in
theorem exists_proj {Y J L : Subgroup G} (hJY : J ≤ Y)
    (hZ : ∀ z (hz : z ∈ J), z ∈ Subgroup.centralizer (J : Set G) →
      (⟨z, hJY hz⟩ : ↥Y) ∈ Subgroup.center ↥Y)
    (hinn : ∀ ℓ ∈ L, ∃ j ∈ J, j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G)) :
    ∃ τ : ↥L →* ↥Y ⧸ Subgroup.center ↥Y,
      (∀ (ℓ : ↥L) (j : G) (hj : j ∈ J), j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G) →
        τ ℓ = QuotientGroup.mk (⟨j, hJY hj⟩ : ↥Y)) ∧
      (∀ ℓ : ↥L, τ ℓ = 1 ↔ (ℓ : G) ∈ Subgroup.centralizer (J : Set G)) := by
  classical
  have hwd : ∀ (ℓ : G) (j j' : G) (hj : j ∈ J) (hj' : j' ∈ J),
      j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G) → j'⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G) →
      (QuotientGroup.mk (⟨j, hJY hj⟩ : ↥Y) : ↥Y ⧸ Subgroup.center ↥Y) =
        QuotientGroup.mk ⟨j', hJY hj'⟩ := by
    intro ℓ j j' hj hj' hc hc'
    rw [QuotientGroup.eq]
    have hmem : j⁻¹ * j' ∈ J := J.mul_mem (J.inv_mem hj) hj'
    have hcent : j⁻¹ * j' ∈ Subgroup.centralizer (J : Set G) := by
      have e : j⁻¹ * j' = (j⁻¹ * ℓ) * (j'⁻¹ * ℓ)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc')
    have := hZ _ hmem hcent
    convert this using 1
  let jf : ↥L → G := fun ℓ => Classical.choose (hinn ℓ ℓ.2)
  have hjf : ∀ ℓ : ↥L, jf ℓ ∈ J ∧ (jf ℓ)⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G) :=
    fun ℓ => Classical.choose_spec (hinn ℓ ℓ.2)
  have hprod : ∀ (ℓ₁ ℓ₂ : G) (j₁ j₂ : G), j₂ ∈ J →
      j₁⁻¹ * ℓ₁ ∈ Subgroup.centralizer (J : Set G) →
      j₂⁻¹ * ℓ₂ ∈ Subgroup.centralizer (J : Set G) →
      (j₁ * j₂)⁻¹ * (ℓ₁ * ℓ₂) ∈ Subgroup.centralizer (J : Set G) := by
    intro ℓ₁ ℓ₂ j₁ j₂ hj₂ h₁ h₂
    have hc : j₂⁻¹ * (j₁⁻¹ * ℓ₁) = (j₁⁻¹ * ℓ₁) * j₂⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp h₁ _ (J.inv_mem hj₂))
    have e : (j₁ * j₂)⁻¹ * (ℓ₁ * ℓ₂) = (j₁⁻¹ * ℓ₁) * (j₂⁻¹ * ℓ₂) := by
      calc (j₁ * j₂)⁻¹ * (ℓ₁ * ℓ₂) = (j₂⁻¹ * (j₁⁻¹ * ℓ₁)) * ℓ₂ := by group
        _ = (j₁⁻¹ * ℓ₁) * j₂⁻¹ * ℓ₂ := by rw [hc]
        _ = _ := by group
    rw [e]
    exact Subgroup.mul_mem _ h₁ h₂
  let τ : ↥L →* ↥Y ⧸ Subgroup.center ↥Y :=
    { toFun := fun ℓ => QuotientGroup.mk (⟨jf ℓ, hJY (hjf ℓ).1⟩ : ↥Y)
      map_one' := by
        have := hwd 1 (jf 1) 1 (hjf 1).1 J.one_mem (hjf 1).2 (by simp)
        rw [this]
        rfl
      map_mul' := fun ℓ₁ ℓ₂ => by
        have h := hwd ((ℓ₁ : G) * ℓ₂) (jf (ℓ₁ * ℓ₂)) (jf ℓ₁ * jf ℓ₂) (hjf (ℓ₁ * ℓ₂)).1
          (J.mul_mem (hjf ℓ₁).1 (hjf ℓ₂).1) (hjf (ℓ₁ * ℓ₂)).2
          (hprod ℓ₁ ℓ₂ _ _ (hjf ℓ₂).1 (hjf ℓ₁).2 (hjf ℓ₂).2)
        show (QuotientGroup.mk (⟨jf (ℓ₁ * ℓ₂), _⟩ : ↥Y) : ↥Y ⧸ Subgroup.center ↥Y) = _
        rw [h]
        rfl }
  refine ⟨τ, fun ℓ j hj hc => hwd ℓ (jf ℓ) j (hjf ℓ).1 hj (hjf ℓ).2 hc, fun ℓ => ?_⟩
  constructor
  · intro h1
    have h1' : (QuotientGroup.mk (⟨jf ℓ, hJY (hjf ℓ).1⟩ : ↥Y) : ↥Y ⧸ Subgroup.center ↥Y) = 1 :=
      h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at h1'
    have hjc : jf ℓ ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val (h1' ⟨x, hJY hx⟩)
    have e : (ℓ : G) = jf ℓ * ((jf ℓ)⁻¹ * ℓ) := by group
    rw [e]
    exact Subgroup.mul_mem _ hjc (hjf ℓ).2
  · intro hℓ
    have := hwd ℓ (jf ℓ) 1 (hjf ℓ).1 J.one_mem (hjf ℓ).2 (by simpa using hℓ)
    exact this.trans (QuotientGroup.eq_one_iff _ |>.mpr (Subgroup.one_mem _))

omit [Finite G] in
theorem commute_imgZ {Y J₁ J₂ : Subgroup G} (h12 : ⁅J₁, J₂⁆ = ⊥) {a b : ↥Y ⧸ Subgroup.center ↥Y}
    (ha : a ∈ imgZ Y J₁) (hb : b ∈ imgZ Y J₂) : a * b = b * a := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hxy : (x : G) * y = y * x := (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h12 (Subgroup.mem_subgroupOf.mp hx)) y
    (Subgroup.mem_subgroupOf.mp hy)).symm
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext hxy)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
