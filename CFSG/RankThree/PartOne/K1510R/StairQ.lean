module

public import CFSG.RankThree.PartOne.S12.Sec1510Fit
public import CFSG.RankThree.PartOne.S12.Sec15Frattini

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG

variable {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem exists_Q {V P : Subgroup H} [V.Normal]
    (hlayer : layer (H ⧸ V) = ⊥)
    (hA : ∀ M : Subgroup (H ⧸ V), M.Normal → Group.IsNilpotent ↥M → ¬ p ∣ Nat.card ↥M → M = ⊥)
    (hPsyl : IsSylowOf p P ⊤) :
    ∃ Q : Subgroup H, Q ≤ P ∧ (∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧
      (∀ y : H, ∃ k ∈ V ⊔ Q, k⁻¹ * y ∈ Subgroup.normalizer (Q : Set H)) ∧
      (∀ x ∈ P, (∀ q ∈ Q, x * q = q * x) → x ∈ Q) := by
  classical
  have hπ : Function.Surjective (QuotientGroup.mk' V) := QuotientGroup.mk'_surjective V
  obtain ⟨Qb, hQbY, hQbN, hQbp, hQbC, hQbZ⟩ := Sec1510.fitting_layer_centralizer p hA
  set π := QuotientGroup.mk' V with hπdef
  have hYb : ∀ y : H ⧸ V, y ∈ Subgroup.centralizer (layer (H ⧸ V) : Set (H ⧸ V)) := by
    intro y
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hlayer] at hh
    have : h = 1 := Subgroup.mem_bot.1 hh
    rw [this, one_mul, mul_one]
  have hQbN' : ∀ (y q : H ⧸ V), q ∈ Qb → y * q * y⁻¹ ∈ Qb := fun y q hq => hQbN y (hYb y) q hq
  have hπV : ∀ v ∈ V, π v = 1 := fun v hv => (QuotientGroup.eq_one_iff v).2 hv
  set Qt := Qb.comap π with hQt
  have hQtN : ∀ g : H, g ∈ Subgroup.normalizer (Qt : Set H) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      show π (g * h * g⁻¹) ∈ Qb
      rw [map_mul, map_mul, map_inv]
      exact hQbN' (π g) (π h) hh
    · intro hh
      have h1 : π (g * h * g⁻¹) ∈ Qb := hh
      have h2 := hQbN' (π g)⁻¹ _ h1
      have e1 : (π g)⁻¹ * π (g * h * g⁻¹) * ((π g)⁻¹)⁻¹ = π h := by
        rw [map_mul, map_mul, map_inv]; group
      rw [e1] at h2
      exact h2
  have hPsyl' : CFSG.ABGLocalTools.IsSylowOf p P ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 hPsyl
  have hnorm : (⊤ : Subgroup H) ≤ Subgroup.normalizer (Qt : Set H) := fun g _ => hQtN g
  have hQsyl0 : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ Qt) Qt :=
    hPsyl'.inf_of_le_normalizer le_top hnorm
  set Q := P ⊓ Qt with hQ
  have hQeq : Qt = V ⊔ Q := by
    have := Sec15Frattini.comap_eq_sup_of_sylow π hπ hQbp hQsyl0
    rwa [QuotientGroup.ker_mk'] at this
  refine ⟨Q, inf_le_left, ?_, ?_, ?_⟩
  · intro g hg q hq
    refine ⟨P.mul_mem (P.mul_mem hg hq.1) (P.inv_mem hg), ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hQtN g) q).1 hq.2
    exact this
  · intro y
    obtain ⟨k, hk, hkn⟩ := Sec15Frattini.exists_mem_normalizer_of_isSylowOf hQsyl0 (hQtN y)
    exact ⟨k, hQeq ▸ hk, hkn⟩
  · intro x hxP hxc
    have hmem : π x ∈ Qb := by
      refine hQbC (π x) (hYb _) ?_
      intro q hq
      obtain ⟨h, rfl⟩ := hπ q
      have hh : h ∈ Qt := hq
      rw [hQeq] at hh
      obtain ⟨v, hv, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hh
      have hcomm := hxc w hw
      simp only [map_mul, hπV v hv, one_mul]
      rw [← map_mul, ← map_mul, hcomm]
    exact ⟨hxP, hmem⟩

end CFSG.RankThree.PartOne.K1510R
