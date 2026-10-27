module

public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F112W

section Valency

variable {G : Type*} [Group G]

theorem perm_eq_one_of_card_three {X : Type*} [Finite X] (hX : Nat.card X = 3) (σ : Equiv.Perm X)
    {a b : X} (hab : a ≠ b) (ha : σ a = a) (hb : σ b = b) : σ = 1 := by
  ext q
  by_contra hq
  have hq' : σ q ≠ q := hq
  have hqa : q ≠ a := fun h => hq' (h ▸ ha)
  have hqb : q ≠ b := fun h => hq' (h ▸ hb)
  have hsa : σ q ≠ a := fun h => hqa (σ.injective (h.trans ha.symm))
  have hsb : σ q ≠ b := fun h => hqb (σ.injective (h.trans hb.symm))
  have : Fintype X := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card] at hX
  classical
  have h3 : ({a, b, q} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => hqb h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, fun h => hqa h.symm⟩
  have hU : ({a, b, q} : Finset X) = Finset.univ :=
    Finset.eq_univ_of_card _ (h3.trans hX.symm)
  have hmem : σ q ∈ ({a, b, q} : Finset X) := hU ▸ Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact hsa h
  · exact hsb h
  · exact hq' h

theorem coreIn_eq_inf_conjSub_of_relIndex_three [Finite G] {P B : Subgroup G} (hBP : B ≤ P)
    (h3 : B.relIndex P = 3) {x : G} (hx : x ∈ P) (hxB : x ∉ B) :
    coreIn B P = B ⊓ conjSub x B := by
  apply le_antisymm
  · refine le_inf (coreIn_le_right B P) fun y hy => ?_
    rw [mem_conjSub]
    exact hy.2 x hx
  · rintro y ⟨hyB, hyx⟩
    have hyx' : x⁻¹ * y * x ∈ B := mem_conjSub.mp hyx
    have hyP : y ∈ P := hBP hyB
    refine ⟨hyP, fun h hh => ?_⟩
    set B' : Subgroup ↥P := B.subgroupOf P with hB'
    let φ : ↥P →* Equiv.Perm (↥P ⧸ B') := MulAction.toPermHom ↥P (↥P ⧸ B')
    have hcard : Nat.card (↥P ⧸ B') = 3 := h3
    have hmk : ∀ g : ↥P, φ ⟨y, hyP⟩ (g : ↥P ⧸ B') = ((⟨y, hyP⟩ * g : ↥P) : ↥P ⧸ B') := fun g => rfl
    have hp0 : φ ⟨y, hyP⟩ ((1 : ↥P) : ↥P ⧸ B') = ((1 : ↥P) : ↥P ⧸ B') := by
      rw [hmk]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using B.inv_mem hyB
    have hp1 : φ ⟨y, hyP⟩ ((⟨x, hx⟩ : ↥P) : ↥P ⧸ B') = ((⟨x, hx⟩ : ↥P) : ↥P ⧸ B') := by
      rw [hmk]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      have : ((⟨y, hyP⟩ * ⟨x, hx⟩ : ↥P)⁻¹ * ⟨x, hx⟩ : ↥P) = ⟨x⁻¹ * y⁻¹ * x, by
        exact P.mul_mem (P.mul_mem (P.inv_mem hx) (P.inv_mem hyP)) hx⟩ := by
        ext; simp [mul_assoc]
      rw [this]
      simpa [mul_assoc] using B.inv_mem hyx'
    have hne : ((1 : ↥P) : ↥P ⧸ B') ≠ ((⟨x, hx⟩ : ↥P) : ↥P ⧸ B') := by
      intro h
      have := QuotientGroup.eq.mp h
      rw [Subgroup.mem_subgroupOf] at this
      exact hxB (by simpa using this)
    have hone := perm_eq_one_of_card_three hcard (φ ⟨y, hyP⟩) hne hp0 hp1
    have hfix : φ ⟨y, hyP⟩ ((⟨h, hh⟩ : ↥P) : ↥P ⧸ B') = ((⟨h, hh⟩ : ↥P) : ↥P ⧸ B') := by
      rw [hone]
      rfl
    rw [hmk] at hfix
    have := QuotientGroup.eq.mp hfix
    rw [Subgroup.mem_subgroupOf] at this
    have h1 : h⁻¹ * y⁻¹ * h ∈ B := by simpa [mul_assoc] using this
    simpa [mul_assoc] using B.inv_mem h1

end Valency

end F112W

end CFSG.Quasithin
