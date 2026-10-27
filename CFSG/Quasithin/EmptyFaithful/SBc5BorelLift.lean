module

public import CFSG.Quasithin.EmptyFaithful.SBc5BlockAux
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc5

section Lift

variable {X : Type} [Group X] [Finite X] {Y : Type} [Group Y]

omit [Finite X] in
theorem exists_sylow_of_borel_image {L B : Subgroup X} (hBL : B ≤ L) (ψ : ↥L →* Y)
    (hker2 : IsPGroup 2 ψ.ker) {Ps : Subgroup Y} (hPs : IsSylowTwoOf Ps ψ.range)
    (hB : ∀ r : Y, r ∈ ψ.range ⊓ Subgroup.normalizer (Ps : Set Y) ↔
      ∃ b : ↥L, (b : X) ∈ B ∧ ψ b = r)
    (hkerB : ∀ x : ↥L, ψ x = 1 → (x : X) ∈ B) :
    ∃ P : Subgroup X, IsSylowTwoOf P L ∧ B = L ⊓ Subgroup.normalizer (P : Set X) := by
  classical
  obtain ⟨hPsR, hPs2, hPsidx⟩ := hPs
  set P'' : Subgroup ↥L := Ps.comap ψ with hP''
  have hmemP'' : ∀ y : ↥L, y ∈ P'' ↔ ψ y ∈ Ps := fun y => Iff.rfl
  have hP''2 : IsPGroup 2 ↥P'' := hPs2.comap_of_ker_isPGroup ψ hker2
  have hP''idx : ¬ 2 ∣ P''.index := by
    have h1 : P'' = (Ps.subgroupOf ψ.range).comap ψ.rangeRestrict := by
      ext y
      simp [hP'', Subgroup.mem_subgroupOf]
    rw [h1, Subgroup.index_comap_of_surjective _ ψ.rangeRestrict_surjective]
    exact hPsidx
  have hP''S : IsSylowTwoOf P'' (⊤ : Subgroup ↥L) := by
    refine ⟨le_top, hP''2, ?_⟩
    rw [show (P''.subgroupOf (⊤ : Subgroup ↥L)).index = P''.index from
      Subgroup.relIndex_top_right _]
    exact hP''idx
  have hPL : P''.map L.subtype ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hnorm : ∀ x : ↥L, (x : X) ∈ Subgroup.normalizer ((P''.map L.subtype : Subgroup X) : Set X) ↔
      x ∈ Subgroup.normalizer (P'' : Set ↥L) := fun x => by
    have := mem_normalizer_subgroupOf_iff (P := P''.map L.subtype) (L := L) hPL (x := x)
    have e : (P''.map L.subtype).subgroupOf L = P'' :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective P''
    rw [e] at this
    exact this.symm
  refine ⟨P''.map L.subtype, ?_, ?_⟩
  · have h1 := (SBd3T.isSylowTwoOf_map_iff L.subtype L.subtype_injective P'' ⊤).2 hP''S
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h1
  · ext x
    rw [Subgroup.mem_inf]
    constructor
    · intro hx
      have hxL : x ∈ L := hBL hx
      refine ⟨hxL, (hnorm ⟨x, hxL⟩).2 ?_⟩
      have hr : ψ ⟨x, hxL⟩ ∈ ψ.range ⊓ Subgroup.normalizer (Ps : Set Y) :=
        (hB _).2 ⟨⟨x, hxL⟩, hx, rfl⟩
      have hn : ψ ⟨x, hxL⟩ ∈ Subgroup.normalizer (Ps : Set Y) := hr.2
      rw [Subgroup.mem_normalizer_iff] at hn ⊢
      intro y
      rw [hmemP'' y, hmemP'' _]
      have := hn (ψ y)
      rwa [← map_mul, ← map_inv, ← map_mul] at this
    · rintro ⟨hxL, hxn⟩
      have hn' : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (P'' : Set ↥L) := (hnorm ⟨x, hxL⟩).1 hxn
      have hn : ψ ⟨x, hxL⟩ ∈ Subgroup.normalizer (Ps : Set Y) := by
        rw [Subgroup.mem_normalizer_iff]
        intro r
        by_cases hr : r ∈ ψ.range
        · obtain ⟨y, rfl⟩ := hr
          have h1 := Subgroup.mem_normalizer_iff.mp hn' y
          rw [hmemP'' y, hmemP'' _, map_mul, map_mul, map_inv] at h1
          exact h1
        · constructor
          · intro hrP
            exact absurd (hPsR hrP) hr
          · intro hrP
            exfalso
            apply hr
            have h2 : ψ ⟨x, hxL⟩ * r * (ψ ⟨x, hxL⟩)⁻¹ ∈ ψ.range := hPsR hrP
            have h3 : (ψ ⟨x, hxL⟩)⁻¹ * (ψ ⟨x, hxL⟩ * r * (ψ ⟨x, hxL⟩)⁻¹) * ψ ⟨x, hxL⟩ ∈
                ψ.range :=
              ψ.range.mul_mem (ψ.range.mul_mem (ψ.range.inv_mem ⟨_, rfl⟩) h2) ⟨_, rfl⟩
            simpa [mul_assoc] using h3
      have hr : ψ ⟨x, hxL⟩ ∈ ψ.range ⊓ Subgroup.normalizer (Ps : Set Y) := ⟨⟨_, rfl⟩, hn⟩
      obtain ⟨b, hbB, hbx⟩ := (hB _).1 hr
      have h4 : ψ (⟨x, hxL⟩ * b⁻¹) = 1 := by rw [map_mul, map_inv, ← hbx, mul_inv_cancel]
      have h5 : x * (b : X)⁻¹ ∈ B := hkerB _ h4
      have : x = x * (b : X)⁻¹ * (b : X) := by group
      rw [this]
      exact B.mul_mem h5 hbB

end Lift

end SBc5

end CFSG.Quasithin
