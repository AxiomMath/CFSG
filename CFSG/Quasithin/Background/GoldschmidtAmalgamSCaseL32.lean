module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSL32

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv CFSG.Open CFSG.QuasithinUnique

theorem center_perm_four : ∀ g : Perm (Fin 4), (∀ h : Perm (Fin 4), h * g = g * h) → g = 1 := by
  decide

section F112

variable {D : Type*} [Group D]

theorem f112Convention_of_center_trivial {G₁ G₂ : Subgroup D}
    (h : ∀ x ∈ G₂, (∀ g ∈ G₂, g * x = x * g) → x = 1) : F112Convention G₁ G₂ := by
  intro hor x hx
  rcases hor with h1 | h2
  · exact h1 hx
  · have hx2 : x ∈ Subgroup.centralizer (G₂ : Set D) := h2 hx
    have hxT : x ∈ G₁ ⊓ G₂ := hx.1
    have := h x hxT.2 (fun g hg => Subgroup.mem_centralizer_iff.1 hx2 g hg)
    rw [this]
    exact Subgroup.one_mem _

end F112

theorem goldCaseL32_of_amalgam {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtAmalgam G₁ G₂) (c₁ : CharTwo G₁) (c₂ : CharTwo G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) = 8) : IsGoldCaseL32 G₁ G₂ := by
  have hA := typeA_of_amalgam h c₁ c₂ hT
  obtain ⟨W, gW, fW, K₁, K₂, hW, hK, hA'⟩ := exists_model_L32
  obtain ⟨Q₁, Q₂, V₁, V₂, -⟩ := id hA
  obtain ⟨ψ₁, -⟩ := V₁.exists_iso
  obtain ⟨ψ₂, -⟩ := V₂.exists_iso
  refine ⟨⟨W, gW, fW, K₁, K₂, hW, hK, TypeA.isAmalgamIso hA hA'⟩, ?_, ⟨ψ₁⟩, ⟨ψ₂⟩⟩
  refine f112Convention_of_center_trivial fun x hx hc => ?_
  have hy : ∀ k : Perm (Fin 4), k * ψ₂ ⟨x, hx⟩ = ψ₂ ⟨x, hx⟩ * k := by
    intro k
    obtain ⟨g, rfl⟩ := ψ₂.surjective k
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc g.1 g.2)
  have := center_perm_four _ hy
  have h1 : (⟨x, hx⟩ : ↥G₂) = 1 := ψ₂.injective (by rw [this, map_one])
  exact congrArg Subtype.val h1

theorem eight_le_card_of_charTwo {E : Type*} [Group E] [Finite E] {A₁ A₂ : Subgroup E}
    (h : IsGoldschmidtTriple A₁ A₂) (c : CharTwo A₁) : 8 ≤ Nat.card ↥(A₁ ⊓ A₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.Open.pCore 2 ↥A₁).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQ2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥A₁) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have h3 := card_vertex_left h
  have h6 := card_pCore_mul_six h
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hcent := charTwo_cent c
  by_contra hlt
  have hle : Nat.card (CFSG.Open.pCore 2 ↥A₁) ≤ 2 := by
    have h3' : Nat.card (CFSG.Open.pCore 2 ↥A₁) ≤ 3 := by omega
    rw [hk] at h3' ⊢
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    · have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
  have hall : ∀ g : ↥A₁, g ∈ CFSG.Open.pCore 2 ↥A₁ := by
    intro g
    refine hcent g fun q hq => ?_
    by_cases hq1 : q = 1
    · rw [hq1]; simp
    · have hconj : g * q * g⁻¹ ∈ CFSG.Open.pCore 2 ↥A₁ := hn.conj_mem q hq g
      have hc1 : g * q * g⁻¹ ≠ 1 := fun h1 => hq1 (by simpa using h1)
      have := @eq_of_card_le_two (↥(CFSG.Open.pCore 2 ↥A₁)) _ inferInstance hle
        ⟨_, hconj⟩ ⟨q, hq⟩ (fun h1 => hc1 (congrArg Subtype.val h1))
        (fun h1 => hq1 (congrArg Subtype.val h1))
      have h2 : g * q * g⁻¹ = q := congrArg Subtype.val this
      calc g * q = g * q * g⁻¹ * g := by group
        _ = q * g := by rw [h2]
  have htop : CFSG.Open.pCore 2 ↥A₁ = ⊤ := eq_top_iff.2 fun g _ => hall g
  have : Nat.card (CFSG.Open.pCore 2 ↥A₁) = Nat.card ↥A₁ := by
    rw [htop, Subgroup.card_top]
  have hpos : 0 < Nat.card (CFSG.Open.pCore 2 ↥A₁) := Nat.card_pos
  omega

end CFSG.Quasithin.F6.GoldAmS
