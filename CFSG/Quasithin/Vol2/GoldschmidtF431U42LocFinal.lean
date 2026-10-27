module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocQG
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocX1

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

@[expose] noncomputable def pre2 (A : Subgroup G) : Subgroup Y := (A.comap C.φ2).map P2.subtype

theorem mem_pre2 {A : Subgroup G} {y : Y} : y ∈ C.pre2 A ↔ y ∈ P2 ∧ C.Φ2 y ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show C.Φ2 (x : Y) ∈ A
    rw [C.Φ2_of_mem x.2]
    exact hx
  · rintro ⟨hy, hA⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show C.φ2 ⟨y, hy⟩ ∈ A
    rw [← C.Φ2_of_mem hy]
    exact hA

theorem pre2_le {A : Subgroup G} : C.pre2 A ≤ P2 := fun _ hy => (C.mem_pre2.1 hy).1

theorem card_pre2 {A : Subgroup G} (hA : A ≤ C.φ2.range) : Nat.card (C.pre2 A) = Nat.card A := by
  rw [pre2, Subgroup.card_map_of_injective P2.subtype_injective]
  have := Subgroup.card_map_of_injective C.inj2 (K := A.comap C.φ2)
  rw [Subgroup.map_comap_eq_self hA] at this
  exact this.symm

theorem exists_Φ2_of_mem_range {g : G} (hg : g ∈ C.φ2.range) : ∃ y ∈ P2, C.Φ2 y = g := by
  obtain ⟨y, rfl⟩ := hg
  exact ⟨y, y.2, C.Φ2_of_mem y.2⟩

theorem conj_u15 {e : Y} (heP : e ∈ P2) (hc : e * tPrime = tPrime * e) :
    C.Φ2 e * C.Φ2 (sY 15) * (C.Φ2 e)⁻¹ = C.Φ2 (sY 15) ∨
      C.Φ2 e * C.Φ2 (sY 15) * (C.Φ2 e)⁻¹ = C.Φ2 (sY 15) * C.tG := by
  have h15 : sY 15 ∈ P2 := sY_mem_P2 mem_L0S_fifteen
  rw [← C.Φ2_conj heP h15]
  rcases conj_sY_fifteen heP hc with h | h
  · exact Or.inl (by rw [h])
  · refine Or.inr ?_
    rw [h, tG_def, ← C.Φ2_mul h15 (Vsub_le_P2 tPrime_mem_Vsub), sY15_mul_tPrime]

theorem Φ2_mem_normalizer {e : Y} (heP : e ∈ P2) :
    C.Φ2 e ∈ Subgroup.normalizer (C.V2 : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := C.mem_V2.1 hx
    rw [← C.Φ2_inv heP, ← C.Φ2_mul heP (Vsub_le_P2 hv),
      ← C.Φ2_mul (P2.mul_mem heP (Vsub_le_P2 hv)) (P2.inv_mem heP)]
    exact C.Φ2_mem_V2 (P2_conj_V heP hv)
  · intro hx
    obtain ⟨v, hv, hvx⟩ := C.mem_V2.1 hx
    have hx' : x = C.Φ2 (e⁻¹ * v * e) := by
      rw [C.Φ2_mul (P2.mul_mem (P2.inv_mem heP) (Vsub_le_P2 hv)) heP,
        C.Φ2_mul (P2.inv_mem heP) (Vsub_le_P2 hv), C.Φ2_inv heP, hvx]
      group
    rw [hx']
    have := P2_conj_V (P2.inv_mem heP) hv
    simpa using C.Φ2_mem_V2 this

end Ctx

end CFSG.Quasithin.H13.F431.U42
