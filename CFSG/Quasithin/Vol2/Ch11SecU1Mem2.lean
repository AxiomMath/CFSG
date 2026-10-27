module

public import CFSG.Quasithin.Background.E1Sec6
public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.Comp

open CFSG.Open CFSG.Quasithin

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_sup {T L₀ τ : Subgroup G} (hT2 : IsPGroup 2 T) (hτT : τ ≤ T)
    (hτN : τ ≤ Subgroup.normalizer (L₀ : Set G)) (hL : IsSylowIn 2 (T ⊓ L₀) L₀) :
    IsSylowIn 2 (T ⊓ (L₀ ⊔ τ)) (L₀ ⊔ τ) := by
  have hS₀T : T ⊓ L₀ ⊔ τ ≤ T := sup_le inf_le_left hτT
  have hS₀N : T ⊓ L₀ ⊔ τ ≤ Subgroup.normalizer (L₀ : Set G) :=
    sup_le (inf_le_right.trans Subgroup.le_normalizer) hτN
  have hS₀2 : IsPGroup 2 ↥(T ⊓ L₀ ⊔ τ) := hT2.to_le hS₀T
  have h1 : IsSylowIn 2 ((T ⊓ L₀ ⊔ τ) ⊓ L₀) L₀ :=
    E1.isSylowIn_two_of_le hL (le_inf le_sup_left inf_le_right) inf_le_right
      (hS₀2.to_le inf_le_left)
  have h2 := E1.isSylowIn_two_of_sup_inf hS₀N hS₀2 h1
  have heq : L₀ ⊔ (T ⊓ L₀ ⊔ τ) = L₀ ⊔ τ :=
    le_antisymm (sup_le le_sup_left (sup_le (inf_le_right.trans le_sup_left) le_sup_right))
      (sup_le_sup_left le_sup_right _)
  rw [heq] at h2
  exact E1.isSylowIn_two_of_le h2 (le_inf hS₀T h2.1) inf_le_right (hT2.to_le inf_le_left)

end Sylow

section Quotient

variable {Q : Type} [Group Q] [Finite Q] {L C : Subgroup Q}

omit [Finite Q] in
theorem isPGroup_two (hLC : L ⊓ C = ⊥) (htwo : ∀ q : Q, ∃ k : ℕ, q ^ 2 ^ k ∈ L) :
    IsPGroup 2 C := by
  intro c
  obtain ⟨k, hk⟩ := htwo c
  refine ⟨k, Subtype.ext ?_⟩
  have h : (c : Q) ^ 2 ^ k ∈ L ⊓ C := ⟨hk, C.pow_mem c.2 _⟩
  rw [hLC, Subgroup.mem_bot] at h
  simpa using h

omit [Finite Q] in
theorem almostSimple_map [hLn : L.Normal] [C.Normal] [IsSimpleGroup ↥L]
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hLC : L ⊓ C = ⊥)
    (hcent : ∀ q : Q, (∀ l ∈ L, l * q = q * l) → q ∈ C)
    (htwo : ∀ q : Q, ∃ k : ℕ, q ^ 2 ^ k ∈ L) :
    SecE3.AlmostSimple (L.map (QuotientGroup.mk' C)) := by
  set φ := QuotientGroup.mk' C with hφdef
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective C
  have hinj : Function.Injective (φ.comp L.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h : (x : Q) ∈ L ⊓ C := ⟨x.2, hx⟩
    rw [hLC, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext h)
  have hrange : (φ.comp L.subtype).range = L.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥L ≃* ↥(L.map φ) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨hLn.map φ hφ, e.symm.isSimpleGroup, ?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  · refine le_bot_iff.mp fun z hz => ?_
    obtain ⟨q, rfl⟩ := hφ z
    have hq : q ∈ C := by
      refine hcent q fun l hl => ?_
      have h1 : φ l * φ q = φ q * φ l :=
        Subgroup.mem_centralizer_iff.mp hz (φ l) (Subgroup.mem_map_of_mem φ hl)
      have h2 : q * l * q⁻¹ * l⁻¹ ∈ C := by
        rw [← QuotientGroup.eq_one_iff]
        change φ (q * l * q⁻¹ * l⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      have h3 : q * l * q⁻¹ * l⁻¹ ∈ L := L.mul_mem (hLn.conj_mem l hl q) (L.inv_mem hl)
      have h4 : q * l * q⁻¹ * l⁻¹ ∈ L ⊓ C := ⟨h3, h2⟩
      rw [hLC, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
      exact h4.symm
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff q).mpr hq
  · intro z
    obtain ⟨q, rfl⟩ := hφ z
    obtain ⟨k, hk⟩ := htwo q
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map_of_mem φ hk⟩

end Quotient

end CFSG.Quasithin.Vol2.Ch11.SecU1.Comp
