module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {Δ : Type*} [Group Δ]

@[expose] def InCell (B : Subgroup Δ) (n x : Δ) : Prop := ∃ b₁ ∈ B, ∃ b₂ ∈ B, x = b₁ * n * b₂

theorem InCell.lmul {B : Subgroup Δ} {n x b : Δ} (hb : b ∈ B) (h : InCell B n x) :
    InCell B n (b * x) := by
  obtain ⟨b₁, h₁, b₂, h₂, rfl⟩ := h
  exact ⟨b * b₁, B.mul_mem hb h₁, b₂, h₂, by group⟩

theorem InCell.congr {B : Subgroup Δ} {n n' x : Δ} (h : InCell B n x) (hn : n = n') :
    InCell B n' x := hn ▸ h

theorem inCell_one_iff {B : Subgroup Δ} {x : Δ} : InCell B 1 x ↔ x ∈ B := by
  constructor
  · rintro ⟨b₁, h₁, b₂, h₂, rfl⟩
    simpa using B.mul_mem h₁ h₂
  · intro hx
    exact ⟨x, hx, 1, B.one_mem, by group⟩

structure RankOne (B P : Subgroup Δ) (r : Δ) (U : List Δ) : Prop where
  le : B ≤ P
  mem : r ∈ P
  sq : r * r = 1
  nmem : r ∉ B
  U_mem : ∀ u ∈ U, u ∈ B
  cos : ∀ x ∈ P, x ∈ B ∨ ∃ v ∈ U, ∃ b ∈ B, v * x = r * b

namespace RankOne

variable {B P : Subgroup Δ} {r : Δ} {U : List Δ}

theorem inv_eq (h : RankOne B P r U) : r⁻¹ = r := inv_eq_of_mul_eq_one_right h.sq

theorem dec (h : RankOne B P r U) {b : Δ} (hb : b ∈ B) :
    ∃ u ∈ U, ∃ b₀ ∈ B, r * b₀ * r ∈ B ∧ b = b₀ * u := by
  have hbs : b⁻¹ * r ∈ P := P.mul_mem (P.inv_mem (h.le hb)) h.mem
  rcases h.cos _ hbs with h1 | ⟨v, hv, c, hc, hvc⟩
  · exact absurd (by simpa using B.mul_mem hb h1) h.nmem
  ·
    have hc' : r * (v * b⁻¹) * r = c := by
      calc r * (v * b⁻¹) * r = r * (v * (b⁻¹ * r)) := by group
        _ = r * (r * c) := by rw [hvc]
        _ = (r * r) * c := by group
        _ = c := by rw [h.sq, one_mul]
    refine ⟨v, hv, (v * b⁻¹)⁻¹, B.inv_mem (B.mul_mem (h.U_mem v hv) (B.inv_mem hb)), ?_, ?_⟩
    · have : r * (v * b⁻¹)⁻¹ * r = (r * (v * b⁻¹) * r)⁻¹ := by
        conv_lhs => rw [← inv_eq h]
        group
      rw [this, hc']
      exact B.inv_mem hc
    · group

theorem up (h : RankOne B P r U) {n x : Δ} (hn : ∀ u ∈ U, n⁻¹ * u * n ∈ B)
    (hx : InCell B n x) : InCell B (r * n) (r * x) := by
  obtain ⟨b₁, h₁, b₂, h₂, rfl⟩ := hx
  obtain ⟨u, hu, b₀, hb₀, hrb₀, hb⟩ := h.dec h₁
  refine ⟨r * b₀ * r, hrb₀, (n⁻¹ * u * n) * b₂, B.mul_mem (hn u hu) h₂, ?_⟩
  have key : r * (b₀ * u * n * b₂) = (r * b₀ * r⁻¹) * (r * n) * ((n⁻¹ * u * n) * b₂) := by group
  rw [hb, key, h.inv_eq]

theorem down (h : RankOne B P r U) {n' x : Δ} (hn' : ∀ u ∈ U, n'⁻¹ * u * n' ∈ B)
    (hx : InCell B (r * n') x) : InCell B n' (r * x) ∨ InCell B (r * n') (r * x) := by
  obtain ⟨b₁, h₁, b₂, h₂, rfl⟩ := hx
  have hP : r * b₁ * r ∈ P := P.mul_mem (P.mul_mem h.mem (h.le h₁)) h.mem
  have hx' : r * (b₁ * (r * n') * b₂) = (r * b₁ * r) * n' * b₂ := by group
  rcases h.cos _ hP with hB | ⟨v, hv, c, hc, hvc⟩
  · left
    rw [hx']
    exact ⟨r * b₁ * r, hB, b₂, h₂, rfl⟩
  · right
    have hrb : r * b₁ * r = v⁻¹ * r * c := by
      calc r * b₁ * r = v⁻¹ * (v * (r * b₁ * r)) := by group
        _ = v⁻¹ * (r * c) := by rw [hvc]
        _ = v⁻¹ * r * c := by group
    have hc' : InCell B n' (c * n' * b₂) := ⟨c, hc, b₂, h₂, rfl⟩
    have hup := h.up hn' hc'
    have e : v⁻¹ * r * c * n' * b₂ = v⁻¹ * (r * (c * n' * b₂)) := by group
    rw [hx', hrb, e]
    exact hup.lmul (B.inv_mem (h.U_mem v hv))

theorem cover (h : RankOne B P r U) {b b' : Δ} (hb : b ∈ B) (hb' : b' ∈ B) :
    ∃ u ∈ U, ∃ b'' ∈ B, b * r * b' = u⁻¹ * r * b'' := by
  obtain ⟨u, hu, b₀, hb₀, hrb₀, hbb⟩ := h.dec (B.inv_mem hb)
  have hb_eq : b = u⁻¹ * b₀⁻¹ := by
    calc b = (b⁻¹)⁻¹ := (inv_inv b).symm
      _ = (b₀ * u)⁻¹ := by rw [hbb]
      _ = u⁻¹ * b₀⁻¹ := by rw [mul_inv_rev]
  have hinv : r * b₀⁻¹ * r = (r * b₀ * r)⁻¹ := by
    conv_rhs => rw [← inv_eq h]
    group
  refine ⟨u, hu, (r * b₀⁻¹ * r) * b', B.mul_mem ?_ hb', ?_⟩
  · rw [hinv]
    exact B.inv_mem hrb₀
  · have : b * r * b' = u⁻¹ * r * ((r⁻¹ * b₀⁻¹ * r) * b') := by rw [hb_eq]; group
    rw [this, inv_eq h]

end RankOne

end CFSG.Quasithin.H13.F431.U42Aut
