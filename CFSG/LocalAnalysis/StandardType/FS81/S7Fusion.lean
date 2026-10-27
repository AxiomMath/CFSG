module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {t x : G}
    (ht : orderOf t = 2) : x ∈ Subgroup.zpowers t ↔ x = 1 ∨ x = t := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, ht, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem exists_mul_of_card_ggAutomizer_eq {G : Type} [Group G] [Finite G] {Y B : Subgroup G}
    (hcard : Nat.card (ggAutomizer Y B) = Nat.card (ggAutomizer ⊤ B)) {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) :
    ∃ y ∈ Y, y ∈ Subgroup.normalizer (B : Set G) ∧
      ∃ c ∈ Subgroup.centralizer (B : Set G), g = y * c := by
  have hle : ggAutomizer Y B ≤ ggAutomizer ⊤ B := ggAutomizer_mono B le_top
  have heq : ggAutomizer Y B = ggAutomizer ⊤ B := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hφ : ggConjAut B hg ∈ ggAutomizer Y B := by
    rw [heq]
    exact ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg
  obtain ⟨y, hyY, hyN, hyφ⟩ := mem_ggAutomizer_iff.mp hφ
  refine ⟨y, hyY, hyN, y⁻¹ * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : ((ggConjAut B hg (⟨b, hb⟩ : ↥B) : ↥B) : G) = y * b * y⁻¹ :=
      hyφ ⟨b, hb⟩
    have h2 : ((ggConjAut B hg (⟨b, hb⟩ : ↥B) : ↥B) : G) = g * b * g⁻¹ :=
      ggConjAut_apply B hg ⟨b, hb⟩
    have hconj : y * b * y⁻¹ = g * b * g⁻¹ := h1.symm.trans h2
    have hb_comm : b * y⁻¹ * g = y⁻¹ * g * b := by
      calc b * y⁻¹ * g = y⁻¹ * (y * b * y⁻¹) * g := by group
        _ = y⁻¹ * (g * b * g⁻¹) * g := by rw [hconj]
        _ = y⁻¹ * g * b := by group
    simpa only [mul_assoc] using hb_comm
  · group

theorem exists_conj_Y_of_mem {G : Type} [Group G] [Finite G] {Y B : Subgroup G} {b₀ : G}
    (hb₀ : b₀ ∈ B)
    (hfus : ∀ g : G, g * b₀ * g⁻¹ ∈ B →
      ∃ x ∈ Subgroup.normalizer (B : Set G), g * b₀ * g⁻¹ = x * b₀ * x⁻¹)
    (hcard : Nat.card (ggAutomizer Y B) = Nat.card (ggAutomizer ⊤ B))
    {g : G} (hg : g * b₀ * g⁻¹ ∈ B) : ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹ := by
  obtain ⟨x, hxN, hx⟩ := hfus g hg
  obtain ⟨y, hyY, -, c, hcC, hxc⟩ := exists_mul_of_card_ggAutomizer_eq hcard hxN
  refine ⟨y, hyY, ?_⟩
  have hcomm : b₀ * c = c * b₀ := (Subgroup.mem_centralizer_iff.mp hcC) b₀ hb₀
  have hc : c * b₀ * c⁻¹ = b₀ := by
    rw [← hcomm]
    group
  calc g * b₀ * g⁻¹ = x * b₀ * x⁻¹ := hx
    _ = (y * c) * b₀ * (y * c)⁻¹ := by rw [hxc]
    _ = y * b₀ * y⁻¹ := by
        rw [show (y * c) * b₀ * (y * c)⁻¹ = y * (c * b₀ * c⁻¹) * y⁻¹ by group, hc]

theorem exists_zpowers_conj_Y_of_isConjLine {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    {k : ℕ} (B : Basis3 G k) {b₀ : G} (hb₀ : b₀ ∈ B.span) (hF : Fus42 B b₀)
    (hcard : Nat.card (ggAutomizer Y B.span) = Nat.card (ggAutomizer ⊤ B.span))
    {e : Coords k} (he : IsConjLine b₀ (B.line e)) :
    ∃ y ∈ Y, Subgroup.zpowers (y * b₀ * y⁻¹) = B.line e := by
  obtain ⟨g, hg⟩ := he
  have hvec : B.vec e ∈ B.span := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  have hmem : g * b₀ * g⁻¹ ∈ B.span := by
    have hmem' : g * b₀ * g⁻¹ ∈ B.line e := hg ▸ Subgroup.mem_zpowers _
    exact Subgroup.zpowers_le.mpr hvec hmem'
  obtain ⟨y, hyY, hy⟩ := exists_conj_Y_of_mem hb₀ hF.2 hcard hmem
  exact ⟨y, hyY, by rw [← hy, hg]⟩

theorem exists_conj_Y_of_toral {G : Type} [Group G] [Finite G] {Y B W : Subgroup G} {b₀ : G}
    (hb₀ : b₀ ∈ B)
    (hfus : ∀ g : G, g * b₀ * g⁻¹ ∈ B →
      ∃ x ∈ Subgroup.normalizer (B : Set G), g * b₀ * g⁻¹ = x * b₀ * x⁻¹)
    (hcard : Nat.card (ggAutomizer Y B) = Nat.card (ggAutomizer ⊤ B))
    (htor : ∀ g : G, g * b₀ * g⁻¹ ∈ W → ∃ y ∈ Y, y * (g * b₀ * g⁻¹) * y⁻¹ ∈ B)
    {g : G} (hg : g * b₀ * g⁻¹ ∈ W) : ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹ := by
  obtain ⟨y₁, hy₁Y, hy₁⟩ := htor g hg
  have hmem : (y₁ * g) * b₀ * (y₁ * g)⁻¹ ∈ B := by
    rw [show (y₁ * g) * b₀ * (y₁ * g)⁻¹ = y₁ * (g * b₀ * g⁻¹) * y₁⁻¹ by group]
    exact hy₁
  obtain ⟨y₂, hy₂Y, hy₂⟩ := exists_conj_Y_of_mem hb₀ hfus hcard hmem
  refine ⟨y₁⁻¹ * y₂, Y.mul_mem (Y.inv_mem hy₁Y) hy₂Y, ?_⟩
  calc g * b₀ * g⁻¹ = y₁⁻¹ * (y₁ * g * b₀ * (y₁ * g)⁻¹) * y₁ := by group
    _ = y₁⁻¹ * (y₂ * b₀ * y₂⁻¹) * y₁ := by rw [hy₂]
    _ = (y₁⁻¹ * y₂) * b₀ * (y₁⁻¹ * y₂)⁻¹ := by group

theorem centralizer_inf_le_pCoreOf_of_isCharTwoType {G : Type} [Group G] (hG : IsCharTwoType G)
    {t : G} (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have hEq : Subgroup.normalizer (Subgroup.zpowers t : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    refine le_antisymm ?_ ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
        (Subgroup.mem_set_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
      rcases (mem_zpowers_of_orderOf_eq_two ht).mp h1 with h | h
      · exfalso
        apply ht1
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [h]; simp
      · calc g * t = (g * t * g⁻¹) * g := by group
          _ = t * g := by rw [h]
    · rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_le_normalizer _
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers t : Set G)) :=
    ⟨Subgroup.zpowers t, Subgroup.zpowers_ne_bot.mpr ht1,
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), rfl⟩
  have hH := hG _ hloc
  rwa [hEq] at hH

end CFSG.StandardType.FrameRoute.FS81
