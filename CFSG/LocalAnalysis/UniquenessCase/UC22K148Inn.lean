module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sec
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Quo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem sub_mem_of_inducesInner {L B : Subgroup G} (hcen : ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hB2 : ∀ b ∈ B, b * b = 1) {Y Z : Submodule (ZMod 2) V} (hZY : Z ≤ Y)
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) Z)
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → Z ≤ W → W ≤ Y → W = Z ∨ W = Y)
    {b l : G} (hb : b ∈ B) (hl : l ∈ L) (hbl : ∀ x ∈ L, b * x * b⁻¹ = l * x * l⁻¹) :
    ∀ y ∈ Y, ρ b y - ρ l y ∈ Z := by
  set c := l⁻¹ * b with hc
  have hcL : ∀ x ∈ L, c * x = x * c := by
    intro x hx
    have h1 := hbl x hx
    have h2 : b * x = l * x * l⁻¹ * b := by
      calc b * x = b * x * b⁻¹ * b := by group
        _ = l * x * l⁻¹ * b := by rw [h1]
    calc c * x = l⁻¹ * (b * x) := by rw [hc]; group
      _ = x * c := by rw [h2, hc]; group
  have hcB : ∀ b' ∈ B, b' * c = c * b' := by
    intro b' hb'
    set c' := b' * c * b'⁻¹ with hc'
    have hc'L : ∀ x ∈ L, c' * x = x * c' := by
      intro x hx
      have hx' : b'⁻¹ * x * b' ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb')) x).1 hx
        simpa using this
      have h1 := hcL _ hx'
      calc c' * x = b' * (c * (b'⁻¹ * x * b')) * b'⁻¹ := by rw [hc']; group
        _ = b' * ((b'⁻¹ * x * b') * c) * b'⁻¹ := by rw [h1]
        _ = x * c' := by rw [hc']; group
    have hmemL : c * c'⁻¹ ∈ L := by
      have h3 : b * b' * b⁻¹ = b' := by rw [hBc b hb b' hb']; group
      have h1 : c * c'⁻¹ = l⁻¹ * (b * b' * b⁻¹) * l * b'⁻¹ := by rw [hc', hc]; group
      have h4 : l⁻¹ * b' * l * b'⁻¹ = l⁻¹ * (b' * l * b'⁻¹) := by group
      rw [h1, h3, h4]
      exact mul_mem (inv_mem hl) ((Subgroup.mem_normalizer_iff.1 (hBN hb') l).1 hl)
    have hcen' : ∀ y ∈ L, (c * c'⁻¹) * y = y * (c * c'⁻¹) := by
      intro y hy
      have h1 : c'⁻¹ * y = y * c'⁻¹ := by
        have := hc'L y hy
        calc c'⁻¹ * y = c'⁻¹ * (y * c') * c'⁻¹ := by group
          _ = c'⁻¹ * (c' * y) * c'⁻¹ := by rw [this]
          _ = y * c'⁻¹ := by group
      calc c * c'⁻¹ * y = c * (c'⁻¹ * y) := by group
        _ = c * y * c'⁻¹ := by rw [h1]; group
        _ = y * c * c'⁻¹ := by rw [hcL y hy]
        _ = y * (c * c'⁻¹) := by group
    have h1 := hcen _ hmemL hcen'
    have h2 : c = c' := by
      calc c = c * c'⁻¹ * c' := by group
        _ = c' := by rw [h1, one_mul]
    calc b' * c = c' * b' := by rw [hc']; group
      _ = c * b' := by rw [← h2]
  have hc2 : c * c = 1 := by
    have hmem : c * c ∈ L := by
      have h1 : b * l⁻¹ * b⁻¹ = l * l⁻¹ * l⁻¹ := hbl _ (inv_mem hl)
      have h2 : c * c = l⁻¹ * (b * l⁻¹ * b⁻¹) * (b * b) := by rw [hc]; group
      rw [h2, h1, hB2 b hb, mul_one]
      exact mul_mem (inv_mem hl) (mul_mem (mul_mem hl (inv_mem hl)) (inv_mem hl))
    refine hcen _ hmem fun y hy => ?_
    calc c * c * y = c * (c * y) := by group
      _ = c * (y * c) := by rw [hcL y hy]
      _ = (c * y) * c := by group
      _ = y * c * c := by rw [hcL y hy]
      _ = y * (c * c) := by group
  have hcH : c ∈ L ⊔ B := mul_mem (Subgroup.mem_sup_left (inv_mem hl)) (Subgroup.mem_sup_right hb)
  have hZc : ∀ z ∈ Z, ρ c z ∈ Z := fun z hz => hZ c hcH z hz
  have hZc' : ∀ z ∈ Z, ρ c⁻¹ z ∈ Z := fun z hz => hZ _ (inv_mem hcH) z hz
  set W := Y ⊓ P22x.modFix ρ Z (Subgroup.zpowers c) with hW
  have hmemW : ∀ v, v ∈ W ↔ v ∈ Y ∧ ρ c v - v ∈ Z := fun v => by
    rw [hW, Submodule.mem_inf, mem_modFix_zpowers hZc hZc']
  have hWinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W := by
    have key : ∀ h ∈ L ⊔ B, h * c = c * h → ∀ v ∈ W, ρ h v ∈ W := by
      intro h hh hhc v hv
      obtain ⟨hvY, hvc⟩ := (hmemW v).1 hv
      refine (hmemW _).2 ⟨hY h hh v hvY, ?_⟩
      have : ρ c (ρ h v) - ρ h v = ρ h (ρ c v - v) := by
        rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hhc]
      rw [this]
      exact hZ h hh _ hvc
    exact isInvariant_sup (fun h hh => key h (Subgroup.mem_sup_left hh) (hcL h hh).symm)
      (fun h hh => key h (Subgroup.mem_sup_right hh) (hcB h hh))
  have hZW : Z ≤ W := fun z hz => (hmemW z).2 ⟨hZY hz, Z.sub_mem (hZc z hz) hz⟩
  have hcc : ∀ v, ρ c (ρ c v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, hc2, map_one, Module.End.one_apply]
  have hcY : ∀ y ∈ Y, ρ c y - y ∈ Z := by
    intro y hy
    rcases hirr W hWinv hZW inf_le_left with hWe | hWe
    · have hy' : ρ c y - y ∈ W := by
        refine (hmemW _).2 ⟨Y.sub_mem (hY c hcH y hy) hy, ?_⟩
        have h0 : ρ c (ρ c y - y) - (ρ c y - y) = (2 : ℕ) • y - (2 : ℕ) • ρ c y := by
          rw [map_sub, hcc, two_nsmul, two_nsmul]
          abel
        rw [h0, nsmul_two_eq_zero, nsmul_two_eq_zero, sub_zero]
        exact Z.zero_mem
      rwa [hWe] at hy'
    · have hyW : y ∈ W := by rw [hWe]; exact hy
      exact ((hmemW y).1 hyW).2
  intro y hy
  have hbc : b = l * c := by rw [hc]; group
  have h0 : ρ b y - ρ l y = ρ l (ρ c y - y) := by
    rw [hbc, map_mul, Module.End.mul_apply, map_sub]
  rw [h0]
  exact hZ l (Subgroup.mem_sup_left hl) _ (hcY y hy)

theorem mem_secKer_bot {W : Submodule (ZMod 2) V} {g : G} :
    g ∈ secKer ρ ⊥ W ↔ (∀ w ∈ W, ρ g w ∈ W) ∧ ∀ w ∈ W, ρ g⁻¹ w ∈ W := by
  rw [mem_secKer]
  refine ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨fun y hy => ?_, h.1, h.2⟩⟩
  rw [Submodule.mem_bot] at hy
  rw [hy, map_zero, sub_zero]
  exact W.zero_mem

theorem exists_minimal_invariant [Finite V] {H : Subgroup G} {Z W : Submodule (ZMod 2) V}
    (hW : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H W) (hZW : Z < W) :
    ∃ Y₁ : Submodule (ZMod 2) V, Z < Y₁ ∧ Y₁ ≤ W ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y₁ ∧
      ∀ X : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H X → Z ≤ X → X ≤ Y₁ → X = Z ∨ X = Y₁ := by
  haveI : IsArtinian (ZMod 2) V := isArtinian_of_finite
  let S : Set (Submodule (ZMod 2) V) := {X | CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H X ∧ Z < X ∧ X ≤ W}
  obtain ⟨Y₁, ⟨hY₁, hZY₁, hY₁W⟩, hmin⟩ := IsArtinian.set_has_minimal S ⟨W, hW, hZW, le_rfl⟩
  refine ⟨Y₁, hZY₁, hY₁W, hY₁, fun X hX hZX hXY₁ => ?_⟩
  by_cases hXZ : X = Z
  · exact Or.inl hXZ
  · right
    by_contra hne
    exact hmin X ⟨hX, lt_of_le_of_ne hZX (Ne.symm hXZ), hXY₁.trans hY₁W⟩ (lt_of_le_of_ne hXY₁ hne)

theorem sub_mem_of_finrank_eq_succ [Finite V] {H : Subgroup G} {Y Z : Submodule (ZMod 2) V} (hZY : Z ≤ Y)
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z)
    (h1 : finrank (ZMod 2) ↥Y = finrank (ZMod 2) ↥Z + 1) : ∀ h ∈ H, ∀ y ∈ Y, ρ h y - y ∈ Z := by
  intro h hh y hy
  by_cases hyZ : y ∈ Z
  · exact Z.sub_mem (hZ h hh y hyZ) hyZ
  have hq0 : (Submodule.Quotient.mk ⟨y, hy⟩ : SecQ Y Z) ≠ 0 := fun h0 =>
    hyZ ((Submodule.Quotient.mk_eq_zero (Z.comap Y.subtype) (x := ⟨y, hy⟩)).1 h0)
  have hfr : finrank (ZMod 2) (SecQ Y Z) = 1 := by rw [finrank_secQ hZY]; omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hq0).1 hfr
    (secHom hY hZ ⟨h, hh⟩ (Submodule.Quotient.mk ⟨y, hy⟩))
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h01 c with rfl | rfl
  · rw [zero_smul] at hc
    exact absurd ((LinearEquiv.map_eq_zero_iff _).1 hc.symm) hq0
  · rw [one_smul] at hc
    exact (secHom_mk_eq_mk_iff ⟨h, hh⟩ ⟨y, hy⟩).1 hc.symm

theorem card_eq_two_mul_of_mul_mem {B B₁ : Subgroup G} (hle : B₁ ≤ B) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hb₀' : b₀ ∉ B₁) (h : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ∉ B₁ → b₂ ∉ B₁ → b₁ * b₂ ∈ B₁) :
    Nat.card ↥B = 2 * Nat.card ↥B₁ := by
  have hidx : (B₁.subgroupOf B).index = 2 := by
    refine Subgroup.index_eq_two_iff_exists_notMem_and.2 ⟨⟨b₀, hb₀⟩, ?_, fun b => ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hb₀'
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      by_cases hb : (b : G) ∈ B₁
      · exact Or.inr hb
      · exact Or.inl (h _ b.2 _ hb₀ hb hb₀')
  have h1 := Subgroup.card_mul_index (B₁.subgroupOf B)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
