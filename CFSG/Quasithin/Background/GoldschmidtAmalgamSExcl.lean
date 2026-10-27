module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSGlobB

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv CFSG.Open CFSG.QuasithinUnique

variable {E : Type*} [Group E] [Finite E]

structure VtxQ (A Q : Subgroup E) : Prop where
  Q_le : Q ≤ A
  Q_norm : ∀ g ∈ A, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q
  Q_card : Nat.card Q = 8
  cent : ∀ g ∈ A, (∀ q ∈ Q, g * q = q * g) → g ∈ Q

theorem vtxQ_of_vertex {A₁ A₂ : Subgroup E} (h : IsGoldschmidtTriple A₁ A₂) (c : CharTwo A₁)
    (hT : Nat.card ↥(A₁ ⊓ A₂) = 16) : VtxQ A₁ (pCoreOf 2 A₁) := by
  obtain ⟨x, π, hcard, -⟩ := vertex_data h c hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.Open.pCore 2 ↥A₁).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hcent := charTwo_cent c
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨q, hq, rfl⟩
    exact ⟨⟨g, hg⟩ * q * ⟨g, hg⟩⁻¹, hn.conj_mem q hq ⟨g, hg⟩, rfl⟩
  · show Nat.card ↥((CFSG.Open.pCore 2 ↥A₁).map A₁.subtype) = 8
    rw [Subgroup.card_map_of_injective A₁.subtype_injective]
    exact hcard
  · intro g hg hgc
    have := hcent ⟨g, hg⟩ fun q hq => Subtype.ext (hgc q ⟨q, hq, rfl⟩)
    exact ⟨⟨g, hg⟩, this, rfl⟩

omit [Finite E] in
theorem four_le_inf_card {T Q₁ Q₂ : Subgroup E} (h₁ : Q₁ ≤ T) (h₂ : Q₂ ≤ T)
    (hT : Nat.card T = 16) (c₁ : Nat.card Q₁ = 8) (c₂ : Nat.card Q₂ = 8) :
    4 ≤ Nat.card ↥(Q₁ ⊓ Q₂) := by
  have e1 := Subgroup.relIndex_mul_card Q₁ T
  rw [inf_eq_left.2 h₁, c₁, hT] at e1
  have e2 := Subgroup.relIndex_mul_card Q₂ T
  rw [inf_eq_left.2 h₂, c₂, hT] at e2
  have e3 := Subgroup.relIndex_inf_le (H := Q₁) (K := Q₂) (L := T)
  have e4 := Subgroup.relIndex_mul_card (Q₁ ⊓ Q₂) T
  rw [inf_eq_left.2 (inf_le_left.trans h₁), hT] at e4
  have r1 : Q₁.relIndex T = 2 := by omega
  have r2 : Q₂.relIndex T = 2 := by omega
  rw [r1, r2] at e3
  by_contra hlt
  push Not at hlt
  have : (Q₁ ⊓ Q₂).relIndex T * Nat.card ↥(Q₁ ⊓ Q₂) ≤ 4 * 3 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

omit [Finite E] in
theorem amalgam_symm {A₁ A₂ : Subgroup E} (h : IsGoldschmidtAmalgam A₁ A₂) :
    IsGoldschmidtAmalgam A₂ A₁ := ⟨h.toIsGoldschmidtTriple.symm, h.pCore_eq_bot⟩

theorem not_U {A₁ A₂ : Subgroup E} (h : IsGoldschmidtAmalgam A₁ A₂)
    (hT : Nat.card ↥(A₁ ⊓ A₂) = 16) (v₁ : VtxQ A₁ (pCoreOf 2 A₁)) (v₂ : VtxQ A₂ (pCoreOf 2 A₂))
    {z : E} (hzQ : z ∈ pCoreOf 2 A₁) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzc : ∀ g ∈ A₁, g * z = z * g)
    (hzu : ∀ q ∈ pCoreOf 2 A₁, q * q = 1 → q = 1 ∨ q = z)
    (d₂ : Dich A₂ (pCoreOf 2 A₂)) : False := by
  have hQ₁T : pCoreOf 2 A₁ ≤ A₁ ⊓ A₂ := by
    rintro x ⟨q, hq, rfl⟩
    exact ⟨q.2, pCore_le_inf h.toIsGoldschmidtTriple q hq⟩
  have hQ₂T : pCoreOf 2 A₂ ≤ A₁ ⊓ A₂ := by
    rintro x ⟨q, hq, rfl⟩
    exact ⟨pCore_le_inf h.toIsGoldschmidtTriple.symm q hq, q.2⟩
  have hzT : z ∈ A₁ ⊓ A₂ := hQ₁T hzQ
  have hzQ₂ : z ∈ pCoreOf 2 A₂ :=
    v₂.cent z hzT.2 fun q hq => (hzc q (hQ₂T hq).1).symm
  rcases d₂ with e | ⟨z₂, hz₂Q, hz₂1, hz₂z, hz₂c, hz₂u⟩
  ·
    have hsub : ((pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ : Subgroup E) : Set E) ⊆ ({1, z} : Set E) := by
      intro r hr
      rcases hzu r hr.1 (e r hr.2) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    have h4 := four_le_inf_card hQ₁T hQ₂T hT v₁.Q_card v₂.Q_card
    have h5 : ((pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ : Subgroup E) : Set E).ncard ≤
        ({1, z} : Set E).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h6 : ({1, z} : Set E).ncard ≤ 2 :=
      (Set.ncard_insert_le 1 {z}).trans (by rw [Set.ncard_singleton])
    have h7 : ((pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ : Subgroup E) : Set E).ncard =
        Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) := (Nat.card_coe_set_eq _).symm
    omega
  ·
    have hzz₂ : z = 1 ∨ z = z₂ := hz₂u z hzQ₂ hzz
    rcases hzz₂ with h1 | h1
    · exact hz1 h1
    · apply hz1
      refine central_trivial h hzT hzc fun g hg => ?_
      rw [h1]
      exact hz₂c g hg

theorem both_elementary {A₁ A₂ : Subgroup E} (h : IsGoldschmidtAmalgam A₁ A₂)
    (c₁ : CharTwo A₁) (c₂ : CharTwo A₂) (hT : Nat.card ↥(A₁ ⊓ A₂) = 16) :
    (∀ q ∈ pCoreOf 2 A₁, q * q = 1) ∧ (∀ q ∈ pCoreOf 2 A₂, q * q = 1) := by
  have hT' : Nat.card ↥(A₂ ⊓ A₁) = 16 := by rw [inf_comm]; exact hT
  have h' := amalgam_symm h
  have d₁ := dich_of_vertex h.toIsGoldschmidtTriple c₁ hT
  have d₂ := dich_of_vertex h'.toIsGoldschmidtTriple c₂ hT'
  have v₁ := vtxQ_of_vertex h.toIsGoldschmidtTriple c₁ hT
  have v₂ := vtxQ_of_vertex h'.toIsGoldschmidtTriple c₂ hT'
  refine ⟨?_, ?_⟩
  · rcases d₁ with e | ⟨z, hzQ, hz1, hzz, hzc, hzu⟩
    · exact e
    · exact (not_U h hT v₁ v₂ hzQ hz1 hzz hzc hzu d₂).elim
  · rcases d₂ with e | ⟨z, hzQ, hz1, hzz, hzc, hzu⟩
    · exact e
    · exact (not_U h' hT' v₂ v₁ hzQ hz1 hzz hzc hzu d₁).elim

end CFSG.Quasithin.F6.GoldAmS
