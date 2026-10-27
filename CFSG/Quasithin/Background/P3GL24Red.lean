module

public import CFSG.Quasithin.Background.P3GL24A5
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Equiv

theorem gl24_commute_of_commute_image {G : Type*} [Group G] (ρ : G →* Perm (Fin 5))
    (hZc : ∀ z ∈ ρ.ker, ∀ g : G, g * z = z * g) (hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1)
    (c₁ c₂ : G) (h1 : c₁ * c₁ = 1) (h2 : c₂ * c₂ = 1) (hc : ρ c₁ * ρ c₂ = ρ c₂ * ρ c₁) :
    c₁ * c₂ = c₂ * c₁ := by
  have hi1 : c₁⁻¹ = c₁ := inv_eq_of_mul_eq_one_right h1
  have hi2 : c₂⁻¹ = c₂ := inv_eq_of_mul_eq_one_right h2
  have hzk : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hz3 := hZ3 _ hzk
  have hcen := hZc _ hzk c₁
  have hz1 : c₁ * c₂ * c₁⁻¹ * c₂⁻¹ = 1 := by
    set z := c₁ * c₂ * c₁⁻¹ * c₂⁻¹ with hz
    have hzz : c₁ * z * c₁⁻¹ = z⁻¹ := by
      rw [hz, hi1, hi2]
      calc c₁ * (c₁ * c₂ * c₁ * c₂) * c₁ = (c₁ * c₁) * c₂ * c₁ * c₂ * c₁ := by group
        _ = c₂ * c₁ * c₂ * c₁ := by rw [h1, one_mul]
        _ = (c₁ * c₂ * c₁ * c₂)⁻¹ := by group; simp [hi1, hi2]
    have hz' : c₁ * z * c₁⁻¹ = z := by rw [hcen]; group
    have hsq : z * z = 1 := by
      have : z = z⁻¹ := hz'.symm.trans hzz
      calc z * z = z * z⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel z
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hsq]; simp
  calc c₁ * c₂ = (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * (c₂ * c₁) := by group
    _ = c₂ * c₁ := by rw [hz1, one_mul]

theorem gl24_reduction {G : Type*} [Group G] (ρ : G →* Perm (Fin 5))
    (hZc : ∀ z ∈ ρ.ker, ∀ g : G, g * z = z * g)
    (hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1)
    (hcube : ∀ g : G, g ^ 3 ∈ ρ.ker → g ^ 3 = 1)
    (heven : ∀ g, Perm.sign (ρ g) = 1)
    (s : Perm (Fin 5)) (hs2 : s * s = 1) (hsodd : Perm.sign s = -1)
    (C : Subgroup G) (hs : ∀ c ∈ C, ∃ c' ∈ C, ρ c' = s * ρ c * s⁻¹)
    (hO2 : ∀ N : Subgroup C, N.Normal → IsPGroup 2 N → N = ⊥)
    (hinv : ∃ y ∈ C, y ≠ 1 ∧ y * y = 1) :
    ((∀ c ∈ C, c ∈ ρ.ker → c = 1) ∧
        (Nonempty (C ≃* Perm (Fin 3)) ∨ Nonempty (C ≃* alternatingGroup (Fin 5)))) ∨
      (∃ ζ ∈ C, ζ ≠ 1 ∧ ζ ∈ ρ.ker ∧ ∃ c ∈ C, c * c * c = 1 ∧ c ∉ ρ.ker) := by
  obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, hnc⟩ : ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ * c₁ = 1 ∧ c₂ * c₂ = 1 ∧
      ρ c₁ * ρ c₂ ≠ ρ c₂ * ρ c₁ := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ a b : C, a * a = 1 → b * b = 1 → a * b = b * a := by
      intro a b ha hb
      apply Subtype.ext
      have ha' : (a : G) * a = 1 := congrArg Subtype.val ha
      have hb' : (b : G) * b = 1 := congrArg Subtype.val hb
      exact gl24_commute_of_commute_image ρ hZc hZ3 a b ha' hb' (hcon a a.2 b b.2 ha' hb')
    let N : Subgroup C :=
      { carrier := {c | c * c = 1}
        one_mem' := mul_one 1
        mul_mem' := fun {a b} ha hb => by
          have ha' : a * a = 1 := ha
          have hb' : b * b = 1 := hb
          show a * b * (a * b) = 1
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hcomm b a hb' ha']
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha', hb', one_mul]
        inv_mem' := fun {a} ha => by
          have ha' : a * a = 1 := ha
          show a⁻¹ * a⁻¹ = 1
          calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
            _ = 1 := by rw [ha', inv_one] }
    have hN : N.Normal := ⟨fun n hn g => by
      have hn' : n * n = 1 := hn
      show g * n * g⁻¹ * (g * n * g⁻¹) = 1
      calc g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
        _ = 1 := by rw [hn']; group⟩
    have hP2 : IsPGroup 2 N := fun x => ⟨1, by
      apply Subtype.ext
      have hx : (x : C) * x = 1 := x.2
      simpa [sq] using hx⟩
    obtain ⟨y, hyC, hy1, hy2⟩ := hinv
    have hyN : (⟨y, hyC⟩ : C) ∈ N := by
      show (⟨y, hyC⟩ : C) * ⟨y, hyC⟩ = 1
      exact Subtype.ext hy2
    rw [hO2 N hN hP2] at hyN
    exact hy1 (congrArg Subtype.val (Subgroup.mem_bot.1 hyN))
  let ρC : C →* Perm (Fin 5) := ρ.comp C.subtype
  have hPA : ρC.range ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨c, rfl⟩
    rw [Perm.mem_alternatingGroup]
    exact heven c
  have hsP : ∀ p ∈ ρC.range, s * p * s⁻¹ ∈ ρC.range := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨c', hc', hρ⟩ := hs c c.2
    exact ⟨⟨c', hc'⟩, hρ⟩
  have hmul : ∀ c : G, c * c = 1 → ρ c * ρ c = 1 := fun c hc => by rw [← map_mul, hc, map_one]
  obtain ⟨hcl, a, haP, ha3, ha1⟩ := gl24_claim_s ρC.range hPA s hs2 hsodd hsP (ρ c₁) (ρ c₂)
    ⟨⟨c₁, hc₁⟩, rfl⟩ ⟨⟨c₂, hc₂⟩, rfl⟩ (hmul c₁ h1) (hmul c₂ h2) hnc
  by_cases hZ : ∀ c ∈ C, c ∈ ρ.ker → c = 1
  · left
    refine ⟨hZ, ?_⟩
    have hinj : Function.Injective ρC := by
      rw [injective_iff_map_eq_one]
      intro c hc
      exact Subtype.ext (hZ c c.2 hc)
    let e : C ≃* ρC.range := MonoidHom.ofInjective hinj
    rcases hcl with hA | hS
    · exact Or.inr ⟨e.trans (MulEquiv.subgroupCongr hA)⟩
    · exact Or.inl ⟨e.trans hS.some⟩
  · right
    push Not at hZ
    obtain ⟨ζ, hζC, hζk, hζ1⟩ := hZ
    obtain ⟨c₀, hc₀⟩ := haP
    refine ⟨ζ, hζC, hζ1, hζk, c₀, c₀.2, ?_, ?_⟩
    · have hk : (c₀ : G) ^ 3 ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        have : ρ c₀ = a := hc₀
        rw [this, ha3]
      have := hcube c₀ hk
      calc (c₀ : G) * c₀ * c₀ = (c₀ : G) ^ 3 := (pow_three' _).symm
        _ = 1 := this
    · intro hk
      apply ha1
      rw [← hc₀]
      exact hk

end G118

end G11

end CFSG.Quasithin
