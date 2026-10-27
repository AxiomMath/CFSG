module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockSup

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem IsCarrier.sup_mod {B B' P P' L L' Y : Subgroup G} (h₁ : IsCarrier B P)
    (h₂ : IsCarrier B' P') (hBL : B ≤ L) (hB'L : B' ≤ L')
    (hLN : L ≤ Subgroup.normalizer (L' : Set G)) (hL'N : L' ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b * a⁻¹ * b⁻¹ ∈ Y) (hYL : Y ⊓ L ≤ P) (hYL' : Y ⊓ L' ≤ P')
    (hint : L ⊓ L' ≤ Y)
    (hc : ∀ x ∈ B, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ Y) → x ∈ P)
    (hc' : ∀ x ∈ B', (∀ p ∈ P', x * p * x⁻¹ * p⁻¹ ∈ Y) → x ∈ P') :
    IsCarrier (B ⊔ B') (P ⊔ P') := by
  have hcomm' : ∀ x ∈ L', ∀ b ∈ L, x * b * x⁻¹ * b⁻¹ ∈ Y := fun x hx b hb => by
    have := Y.inv_mem (hcomm b hb x hx)
    have e : (b * x * b⁻¹ * x⁻¹)⁻¹ = x * b * x⁻¹ * b⁻¹ := by group
    rwa [e] at this
  have hPL : P ≤ L := h₁.le.trans hBL
  have hP'L' : P' ≤ L' := h₂.le.trans hB'L
  have kB := conj_mem_of_comm hL'N hBL h₁.le hcomm' hYL
  have kB' := conj_mem_of_comm hLN hB'L h₂.le hcomm hYL'
  have kP := conj_mem_of_comm hL'N hPL le_rfl hcomm' hYL
  have kP' := conj_mem_of_comm hLN hP'L' le_rfl hcomm hYL'
  have hB'B : B' ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_conj_mem fun x hx b hb => kB x (hB'L hx) b hb
  have hP'P : P' ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_conj_mem fun x hx p hp => kP x (hP'L' hx) p hp
  have hB'P : B' ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_conj_mem fun x hx p hp => kP x (hB'L hx) p hp
  have hBP' : B ≤ Subgroup.normalizer (P' : Set G) :=
    le_normalizer_of_conj_mem fun x hx p hp => kP' x (hBL hx) p hp
  have hinf : B ⊓ B' = P ⊓ P' := by
    refine le_antisymm (fun x hx => ?_) (inf_le_inf h₁.le h₂.le)
    have hxY : x ∈ Y := hint ⟨hBL hx.1, hB'L hx.2⟩
    exact ⟨hYL ⟨hxY, hBL hx.1⟩, hYL' ⟨hxY, hB'L hx.2⟩⟩
  have hsyl := isSylow_sup_of_inf_eq h₁.isSylow h₂.isSylow hB'B hP'P hinf
  have hnorm : B ⊔ B' ≤ Subgroup.normalizer ((P ⊔ P' : Subgroup G) : Set G) :=
    sup_le (fun x hx => mem_normalizer_sup (h₁.norm hx) (hBP' hx))
      (fun x hx => mem_normalizer_sup (hB'P hx) (h₂.norm hx))
  refine ⟨sup_le_sup h₁.le h₂.le, hsyl.2.1, hnorm, fun x hx k hk =>
    mem_of_isSylow_of_normal hsyl hnorm hx hk, fun x hx hcx => ?_⟩
  have hx' : x ∈ ((B ⊔ B' : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hB'B] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hcx' : ∀ p ∈ P ⊔ P', a * b * p = p * (a * b) := fun p hp => hcx p hp
  refine Subgroup.mul_mem_sup (hc a ha fun q hq => ?_) (hc' b hb fun p' hp' => ?_)
  · set p : G := b⁻¹ * q * b with hpdef
    have hpP : p ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hB'P (B'.inv_mem hb)) q).mp hq
      simpa [hpdef] using this
    have e1 : a * (b * p * b⁻¹) * a⁻¹ = p := by
      calc a * (b * p * b⁻¹) * a⁻¹ = (a * b * p) * (a * b)⁻¹ := by group
        _ = (p * (a * b)) * (a * b)⁻¹ := by rw [hcx' p (Subgroup.mem_sup_left hpP)]
        _ = p := by group
    have eq : b * p * b⁻¹ = q := by simp [hpdef, mul_assoc]
    rw [eq] at e1
    have e2 : a * q * a⁻¹ * q⁻¹ = p * b * p⁻¹ * b⁻¹ := by
      rw [e1]
      rw [← eq]
      group
    rw [e2]
    exact hcomm p (hPL hpP) b (hB'L hb)
  · set r : G := b * p' * b⁻¹ with hrdef
    have hrP' : r ∈ P' := (Subgroup.mem_normalizer_iff.mp (h₂.norm hb) p').mp hp'
    have e1 : a * r * a⁻¹ = p' := by
      calc a * r * a⁻¹ = (a * b * p') * (a * b)⁻¹ := by simp only [hrdef]; group
        _ = (p' * (a * b)) * (a * b)⁻¹ := by rw [hcx' p' (Subgroup.mem_sup_right hp')]
        _ = p' := by group
    have e2 : b * p' * b⁻¹ * p'⁻¹ = (a * r * a⁻¹ * r⁻¹)⁻¹ := by
      conv_lhs => rw [show b * p' * b⁻¹ = r from rfl, ← e1]
      group
    rw [e2]
    exact Y.inv_mem (hcomm a (hBL ha) r (hP'L' hrP'))

end CFSG.Quasithin.GoldMLA
