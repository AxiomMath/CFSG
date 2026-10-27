module

public import CFSG.Quasithin.Recognition.M12AscD8
public import CFSG.Quasithin.Recognition.M12AscD7

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem exists_lift
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G)
    {y : G} (h : OuterData c y) {a b : Perm (Fin 6)} (hab : (a, b) ∈ basisList) :
    ∃ g ∈ Subgroup.normalizer (c.D : Set G),
      g * m.ψ mX * g⁻¹ = c.ρ a ∧ g * c.x1 * g⁻¹ = c.ρ b := by
  classical
  let N : Subgroup G := Subgroup.normalizer (c.D : Set G)
  have hDN : c.D ≤ N := Subgroup.le_normalizer
  let D' : Subgroup ↥N := c.D.subgroupOf N
  let Ψ : G → G × G := fun g => (g * m.ψ mX * g⁻¹, g * c.x1 * g⁻¹)
  let 𝔅 : Finset (G × G) := (basisList.map fun p => (c.ρ p.1, c.ρ p.2)).toFinset
  have h𝔅card : 𝔅.card = 48 := by
    have hinj : Function.Injective (fun p : Perm (Fin 6) × Perm (Fin 6) => (c.ρ p.1, c.ρ p.2)) := by
      intro p q e
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      exact Prod.ext (c.ρ_inj e1) (c.ρ_inj e2)
    simp only [𝔅]
    rw [List.toFinset_card_of_nodup (basisList_nodup.map hinj), List.length_map, basisList_length]
  have hxne : m.ψ mX ≠ 1 := m.x_ne
  have hmem : ∀ g ∈ N, Ψ g ∈ 𝔅 := by
    intro g hg
    have hxD : g * m.ψ mX * g⁻¹ ∈ c.D := (Subgroup.mem_normalizer_iff.1 hg _).1 c.x_mem_D
    have hx1D : g * c.x1 * g⁻¹ ∈ c.D := (Subgroup.mem_normalizer_iff.1 hg _).1 c.x1_mem_D
    obtain ⟨a', ha', hae⟩ := (mem_D c).1 hxD
    obtain ⟨b', hb', hbe⟩ := (mem_D c).1 hx1D
    have hab' : (a', b') ∈ basisList := by
      rw [mem_basisList]
      refine ⟨ha', hb', ?_, ?_⟩
      · intro e
        rw [e, map_one] at hae
        apply hxne
        calc m.ψ mX = g⁻¹ * (g * m.ψ mX * g⁻¹) * g := by group
          _ = 1 := by rw [← hae]; group
      · intro hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        have hx1X := c.x1_X
        rcases hb with e | e | e
        · apply c.x1_ne
          rw [e, map_one] at hbe
          calc c.x1 = g⁻¹ * (g * c.x1 * g⁻¹) * g := by group
            _ = 1 := by rw [← hbe]; group
        · apply hx1X
          have : g * c.x1 * g⁻¹ = g * m.ψ mX * g⁻¹ := by rw [← hbe, ← hae, e]
          have : c.x1 = m.ψ mX := by
            have := mul_left_cancel (mul_right_cancel this)
            exact this
          rw [this]
          exact Subgroup.mem_zpowers _
        · apply hx1X
          have h1 : g * c.x1 * g⁻¹ = g * (m.ψ mX * m.ψ mX) * g⁻¹ := by
            calc g * c.x1 * g⁻¹ = c.ρ (a' * a') := by rw [← hbe, e]
              _ = (g * m.ψ mX * g⁻¹) * (g * m.ψ mX * g⁻¹) := by rw [map_mul, hae]
              _ = g * (m.ψ mX * m.ψ mX) * g⁻¹ := by group
          have : c.x1 = m.ψ mX * m.ψ mX := mul_left_cancel (mul_right_cancel h1)
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    simp only [𝔅, List.mem_toFinset, List.mem_map]
    exact ⟨(a', b'), hab', by simp only [Ψ, hae, hbe]⟩
  have hwd : ∀ g g' : ↥N, (QuotientGroup.leftRel D') g g' →
      (⟨Ψ g, hmem g g.2⟩ : ↥𝔅) = ⟨Ψ g', hmem g' g'.2⟩ := by
    intro g g' hgg
    rw [QuotientGroup.leftRel_apply] at hgg
    have hd : (g : G)⁻¹ * (g' : G) ∈ c.D := hgg
    have hg' : (g' : G) = (g : G) * ((g : G)⁻¹ * (g' : G)) := by group
    apply Subtype.ext
    simp only [Ψ]
    rw [hg']
    have hx := c.D_comm hd c.x_mem_D
    have hx1 := c.D_comm hd c.x1_mem_D
    refine Prod.ext ?_ ?_
    · show (g : G) * m.ψ mX * (g : G)⁻¹ = (g : G) * ((g : G)⁻¹ * (g' : G)) * m.ψ mX *
        ((g : G) * ((g : G)⁻¹ * (g' : G)))⁻¹
      rw [mul_assoc (g : G) _ (m.ψ mX), hx]
      group
    · show (g : G) * c.x1 * (g : G)⁻¹ = (g : G) * ((g : G)⁻¹ * (g' : G)) * c.x1 *
        ((g : G) * ((g : G)⁻¹ * (g' : G)))⁻¹
      rw [mul_assoc (g : G) _ c.x1, hx1]
      group
  let f : ↥N ⧸ D' → ↥𝔅 := Quotient.lift (fun g : ↥N => (⟨Ψ g, hmem g g.2⟩ : ↥𝔅)) hwd
  have hinj : Function.Injective f := by
    intro q1 q2
    induction q1 using Quotient.inductionOn with
    | h g =>
      induction q2 using Quotient.inductionOn with
      | h g' =>
        intro hf
        have hΨ : Ψ g = Ψ g' := congrArg Subtype.val hf
        have hx : (g : G) * m.ψ mX * (g : G)⁻¹ = (g' : G) * m.ψ mX * (g' : G)⁻¹ :=
          congrArg Prod.fst hΨ
        have hx1 : (g : G) * c.x1 * (g : G)⁻¹ = (g' : G) * c.x1 * (g' : G)⁻¹ :=
          congrArg Prod.snd hΨ
        have hc1 : ((g : G)⁻¹ * (g' : G)) * m.ψ mX = m.ψ mX * ((g : G)⁻¹ * (g' : G)) := by
          calc (g : G)⁻¹ * (g' : G) * m.ψ mX
              = (g : G)⁻¹ * ((g' : G) * m.ψ mX * (g' : G)⁻¹) * (g' : G) := by group
            _ = (g : G)⁻¹ * ((g : G) * m.ψ mX * (g : G)⁻¹) * (g' : G) := by rw [hx]
            _ = m.ψ mX * ((g : G)⁻¹ * (g' : G)) := by group
        have hc2 : ((g : G)⁻¹ * (g' : G)) * c.x1 = c.x1 * ((g : G)⁻¹ * (g' : G)) := by
          calc (g : G)⁻¹ * (g' : G) * c.x1
              = (g : G)⁻¹ * ((g' : G) * c.x1 * (g' : G)⁻¹) * (g' : G) := by group
            _ = (g : G)⁻¹ * ((g : G) * c.x1 * (g : G)⁻¹) * (g' : G) := by rw [hx1]
            _ = c.x1 * ((g : G)⁻¹ * (g' : G)) := by group
        have hmemD : (g : G)⁻¹ * (g' : G) ∈ c.D :=
          c.centralizer_D_le hyp h27 h ((mem_C c).2 ((c.centralizes_D_iff).2 ⟨hc1, hc2⟩))
        exact Quotient.sound (QuotientGroup.leftRel_apply.2 hmemD)
  have hcardB : Nat.card ↥𝔅 = 48 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, h𝔅card]
  have hcardD' : Nat.card D' = 9 := by
    have : Nat.card D' = Nat.card c.D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv
    rw [this, c.card_D]
  have hNcard := Subgroup.card_eq_card_quotient_mul_card_subgroup D'
  have hdvd : 432 ∣ Nat.card N := c.card_N_dvd h27 h
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hcard : Nat.card ↥𝔅 ≤ Nat.card (↥N ⧸ D') := by
    rw [hcardD'] at hNcard
    omega
  have hbij := hinj.bijective_of_nat_card_le hcard
  have hab𝔅 : (c.ρ a, c.ρ b) ∈ 𝔅 := by
    simp only [𝔅, List.mem_toFinset, List.mem_map]
    exact ⟨(a, b), hab, rfl⟩
  obtain ⟨q, hq⟩ := hbij.2 ⟨(c.ρ a, c.ρ b), hab𝔅⟩
  induction q using Quotient.inductionOn with
  | h g =>
    have hΨ : Ψ g = (c.ρ a, c.ρ b) := congrArg Subtype.val hq
    exact ⟨(g : G), g.2, congrArg Prod.fst hΨ, congrArg Prod.snd hΨ⟩

end AscCox

end CFSG.Quasithin
