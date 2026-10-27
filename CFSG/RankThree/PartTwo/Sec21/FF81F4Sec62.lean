module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62Order
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62Outer
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

variable {G : Type} [Group G] [Finite G]

theorem ff81_6_2_core {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}
    (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (M : Subgroup G)
    (hM : StatedClassicalModel M .PSp 3 2 1)
    (hMC : Subgroup.zpowers (β' b₂ b₃) ⊔ M = Cen (β' b₂ b₃))
    (h58 : setMul (Op 2 (Cen t₀)) L = Cen t₀ ∧ ∃ T₀ T₁ : Subgroup G, IsElemAb 2 6 T₀ ∧
      IsExtraspecialPlus 4 T₁ ∧ T₀ ⊔ T₁ = Op 2 (Cen t₀) ∧ T₀ ⊓ T₁ = ⊥)
    (Y : Subgroup G) (hY : Nat.card Y = 3311126603366400)
    (hBY : B ≤ Y) (hCtY : Cen t₀ ≤ Y) (hYgen : Cen b ⊔ Cen (β' b₂ b₃) = Y)
    (K0 : ∀ z ∈ Y, (∀ y ∈ Y, z * y = y * z) → z = 1)
    (K1 : ∀ g ∈ Nor Y, (¬ ∃ y ∈ Y, ∀ x ∈ Y, g * x * g⁻¹ = y * x * y⁻¹) →
      ∃ y ∈ Y, ∀ x ∈ Y, (g * y) ^ 2 * x = x * (g * y) ^ 2)
    (K6 : ∀ g ∈ Nor Y, (¬ ∃ y ∈ Y, ∀ x ∈ Y, g * x * g⁻¹ = y * x * y⁻¹) →
      ∀ u ∈ Y, ∀ v ∈ Y, orderOf u = 2 → orderOf v = 2 →
        Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
        Nat.card ↥(Y ⊓ Cen v) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
        ∃ y ∈ Y, y * u * y⁻¹ = v ∨ y * (g * u * g⁻¹) * y⁻¹ = v)
    (K3 : ∀ x ∈ Y, orderOf x = 3 → 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) ∨
      Nat.card ↥(Y ⊓ Cen x) = 2 ^ 9 * 3 ^ 5 * 5 * 7)
    (K4 : ∀ U : Subgroup G, IsSylowOf 2 U Y → Nat.card ↥(Subgroup.center ↥U) = 4)
    (K5 : ∀ U : Subgroup G, IsSylowOf 2 U Y → U = Subgroup.closure {u | u ∈ U ∧ orderOf u = 2 ∧
      Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7})
    (K7 : ∀ E : Subgroup G, E ≤ Y → IsElemAb 3 4 E → Y ⊓ CenS E = E → ∀ x ∈ Y, orderOf x = 3 →
      ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) →
      {D : Subgroup G | D ≤ E ∧ ∃ y ∈ Y, conjBy y (Subgroup.zpowers x) = D}.ncard ≤ 12)
    (K8 : ∀ τ : G, orderOf τ = 2 → τ ∈ Nor Y →
      (¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹) →
      ∀ R : Subgroup G, R ≤ Y ⊓ Cen τ → IsPGroup 2 R → Y ⊓ Cen τ ≤ Nor R → R = ⊥)
    (KG : ∀ τ : G, orderOf τ = 2 → τ ∈ Nor Y →
      (¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹) →
      13 ∣ Nat.card ↥(Y ⊓ Cen τ) ∧
        (∀ V : Subgroup G, IsSylowOf 2 V (Y ⊓ Cen τ) → Nat.card V = 2 ^ 12 ∧
          Subgroup.closure {x | x ∈ V ∧ orderOf x = 2} ≠ V) ∧
        ∀ σ ∈ Y ⊔ Subgroup.zpowers τ, orderOf σ = 2 → σ ∉ Y →
          ∃ g ∈ Y ⊔ Subgroup.zpowers τ, g * σ * g⁻¹ = τ) :
    Nor B ≤ Y ∧ ¬ CaseIIb b B b₁ b₂ b₃ := by
  have hB := h5.basis
  have hbB := hB.mem.1
  have hbY : b ∈ Y := hBY hbB
  have hCbY : Cen b ≤ Y := hYgen ▸ le_sup_left
  have hCβY : Cen (β' b₂ b₃) ≤ Y := hYgen ▸ le_sup_right
  obtain ⟨hCbcard, hCbsup⟩ := cen_eq_sup_of_le hB hCbY K3
  have hCβcard := card_cen_β' hB hM hMC hCβY K3
  have hCBeq : CenS B = B := cenS_eq_of_cen_eq hB hCbsup
  have hCt := card_cen_t₀ hB h5.ht₀L h58 hCtY hY
  have hYCt : Nat.card ↥(Y ⊓ Cen t₀) = 2 ^ 24 * 3 ^ 4 * 5 * 7 := by
    rw [inf_of_le_right hCtY]
    exact hCt
  have hb3 := hB.hyp.ord
  have hβ3 := orderOf_β' hB
  have hcenB : ∀ n ∈ Nor B, Cen (n * b * n⁻¹) ≤ Y := by
    intro n hn
    have hxB : n * b * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hn b).mp hbB
    refine cen_le_of_card K3 (hBY hxB) ?_ ?_
    · rw [show n * b * n⁻¹ = MulAut.conj n b from rfl, MulEquiv.orderOf_eq]
      exact hb3
    · rw [card_cen_conj, hCbcard]
  have hcenβ : ∀ n ∈ Nor B, Cen (n * β' b₂ b₃ * n⁻¹) ≤ Y := by
    intro n hn
    have hxB : n * β' b₂ b₃ * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hn _).mp (β'_mem hB)
    refine cen_le_of_card K3 (hBY hxB) ?_ ?_
    · rw [show n * β' b₂ b₃ * n⁻¹ = MulAut.conj n (β' b₂ b₃) from rfl, MulEquiv.orderOf_eq]
      exact hβ3
    · rw [card_cen_conj, hCβcard]
  have hNBY : Nor B ≤ Nor Y := by
    intro n hn
    have e : conjBy n Y = Cen (n * b * n⁻¹) ⊔ Cen (n * β' b₂ b₃ * n⁻¹) := by
      rw [cen_conj, cen_conj, ← hYgen]
      exact Subgroup.map_sup _ _ _
    have hconj : conjBy n Y ≤ Y := e ▸ sup_le (hcenB n hn) (hcenβ n hn)
    exact Subgroup.mem_normalizer_fintype fun y hy => hconj ⟨y, hy, rfl⟩
  have hCGY : ∀ z : G, (∀ y ∈ Y, z * y = y * z) → z = 1 := fun z hz =>
    K0 z (hCbY (Subgroup.mem_centralizer_singleton_iff.mpr (hz b hbY))) hz
  have hNYY : Nor Y ≤ Y := by
    intro n hn
    by_contra hnY
    have hno : ¬ ∃ y ∈ Y, ∀ x ∈ Y, n * x * n⁻¹ = y * x * y⁻¹ := by
      rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * n = 1 := hCGY _ fun x hx => by
        have := hyx x hx
        calc y⁻¹ * n * x = y⁻¹ * (n * x * n⁻¹) * n := by group
          _ = y⁻¹ * (y * x * y⁻¹) * n := by rw [this]
          _ = x * (y⁻¹ * n) := by group
      exact hnY (inv_mul_eq_one.mp h1 ▸ hy)
    obtain ⟨y, hy, hsq⟩ := K1 n hn hno
    have hτsq : (n * y) ^ 2 = 1 := hCGY _ hsq
    have hτY : n * y ∉ Y := fun h => hnY (by
      have := Y.mul_mem h (Y.inv_mem hy)
      rwa [mul_inv_cancel_right] at this)
    have hτ : orderOf (n * y) = 2 :=
      orderOf_eq_prime hτsq fun h1 => hτY (h1 ▸ Y.one_mem)
    have hτN : n * y ∈ Nor Y := Subgroup.mul_mem _ hn (Subgroup.le_normalizer hy)
    have hτo : ¬ ∃ y' ∈ Y, ∀ x ∈ Y, (n * y) * x * (n * y)⁻¹ = y' * x * y'⁻¹ := by
      rintro ⟨y', hy', hy'x⟩
      apply hno
      refine ⟨y' * y⁻¹, Y.mul_mem hy' (Y.inv_mem hy), fun x hx => ?_⟩
      have h1 := hy'x (y⁻¹ * x * y) (Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hx) hy)
      calc n * x * n⁻¹ = (n * y) * (y⁻¹ * x * y) * (n * y)⁻¹ := by group
        _ = y' * (y⁻¹ * x * y) * y'⁻¹ := h1
        _ = (y' * y⁻¹) * x * (y' * y⁻¹)⁻¹ := by group
    obtain ⟨G13, G2, G3⟩ := KG _ hτ hτN hτo
    exact no_outer_involution hB.hyp.char2 hY h5.ht₀ hCtY hCt K4 K5 hτ hτN hτY
      (fun u hu hu2 huc => K6 _ hτN hτo u hu t₀ (hCtY (Subgroup.mem_centralizer_singleton_iff.mpr
        rfl)) hu2 h5.ht₀ huc hYCt) (K8 _ hτ hτN hτo) G13 G2 G3
  have hNB : Nor B ≤ Y := hNBY.trans hNYY
  refine ⟨hNB, ?_⟩
  rintro ⟨-, -, hcard, -⟩
  have hYCB : Y ⊓ CenS B = B := by rw [hCBeq]; exact inf_of_le_right hBY
  have hnd : ¬ 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen b) := by
    rw [inf_of_le_right hCbY]
    exact not_dvd_card_cen hB
  have h12 := K7 B hBY hB.mono.1 hYCB b hbY hb3 hnd
  have hsub : ConjLines B b ⊆ {D : Subgroup G | D ≤ B ∧ ∃ y ∈ Y,
      conjBy y (Subgroup.zpowers b) = D} := fun D hD => by
    obtain ⟨n, hn, hnD⟩ := hB.fus D hD
    exact ⟨hD.1, n, hNB hn, hnD⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem card_of_model_f4_s6 {H : Type} [Group H]
    (h : ChevalleyExceptionalModel H .F4 2 1) : Nat.card H = 3311126603366400 := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 h.2]
  decide

end CFSG.RankThree.PartTwo.Sec21.FF81.S6
