module

public import CFSG.Timmesfeld.Transvection.ModelSULowBlock
import CFSG.Timmesfeld.Transvection.ModelSULowRadGen
import CFSG.LieType.Universal.Unitary.HermitianQuadratic

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LinearAlgebra

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

private theorem lowPart_mul_self_eq_one [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {g : SU σ m} (hg : g ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (hgg : g * g = 1) : lowPart σ m g * lowPart σ m g = 1 := by
  have h := lowPart_mul (σ := σ) (m := m) g
    (fun x hx => suMat_mulVec_mem_lowSpan_of_mem_normalizer hσ hg hx)
  rw [hgg, lowPart_one] at h
  exact h.symm

private theorem conj_eq_self_of_lowPart_eq_one {g : SU σ m}
    (hg : g ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (h1 : lowPart σ m g = 1) {w : SU σ m} (hw : w ∈ lowRad σ m) :
    g * w * g⁻¹ = w := by
  have heq : lowPart σ m g = lowPart σ m (1 : SU σ m) := by
    rw [lowPart_one]
    exact h1
  have h := conj_eq_conj_of_lowPart_eq hg
    (Subgroup.normalizer (lowRad σ m : Set (SU σ m))).one_mem heq hw
  simpa using h

private theorem lowPart_ne_one {g : SU σ m}
    (hg : g ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (hne : ∃ w ∈ lowRad σ m, g * w * g⁻¹ ≠ w) : lowPart σ m g ≠ 1 := by
  rintro h1
  obtain ⟨w, hw, hwne⟩ := hne
  exact hwne (conj_eq_self_of_lowPart_eq_one hg h1 hw)

private theorem lowBlock_mul_inv {a b : SU σ m} (ha : a ∈ lowRad σ m) (hb : b ∈ lowRad σ m) :
    lowBlock σ m (a * b⁻¹) = lowBlock σ m a - lowBlock σ m b := by
  rw [lowBlock_mul ha (inv_mem hb), lowBlock_inv hb]
  abel

theorem card_inf_centralizer_mul_card_le [Finite F] [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) (hm : 3 ≤ m / 2) {g : SU σ m}
    (hgN : g ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (hgg : g * g = 1)
    (hne : ∃ w ∈ lowRad σ m, g * w * g⁻¹ ≠ w) :
    Nat.card ↥(lowRad σ m ⊓ Subgroup.centralizer {g}) * Nat.card F ≤
      Nat.card ↥(lowRad σ m) := by
  classical
  haveI : Finite (SU σ m) :=
    Finite.of_injective (mat σ m) (mat_injective (σ := σ) (n := m))
  have hP : lowPart σ m g * lowPart σ m g = 1 := lowPart_mul_self_eq_one hσ hgN hgg
  have hP1 : lowPart σ m g ≠ 1 := lowPart_ne_one hgN hne
  obtain ⟨μ, hμherm, hμzero⟩ :=
    exists_addMonoidHom_eq_zero_of_conj_eq (σ := σ) hσ hm hP hP1
  choose wl hwlQ hwlB using fun l : F =>
    exists_mem_lowRad_lowBlock_eq (σ := σ) (m := m) hσ (hμherm l)
  let f : F × ↥(lowRad σ m ⊓ Subgroup.centralizer ({g} : Set (SU σ m))) →
      ↥(lowRad σ m) :=
    fun p => ⟨wl p.1 * (p.2 : SU σ m),
      (lowRad σ m).mul_mem (hwlQ p.1) p.2.2.1⟩
  have hinj : Function.Injective f := by
    rintro ⟨l, c⟩ ⟨l', c'⟩ heq
    have heq' : wl l * (c : SU σ m) = wl l' * (c' : SU σ m) := congrArg Subtype.val heq
    have hcQ : (c : SU σ m) ∈ lowRad σ m := c.2.1
    have hc'Q : (c' : SU σ m) ∈ lowRad σ m := c'.2.1
    have hB : μ l + lowBlock σ m (c : SU σ m) = μ l' + lowBlock σ m (c' : SU σ m) := by
      have h := congrArg (lowBlock σ m) heq'
      rwa [lowBlock_mul (hwlQ l) hcQ, lowBlock_mul (hwlQ l') hc'Q, hwlB l, hwlB l'] at h
    have hsub : μ (l - l') = lowBlock σ m ((c' : SU σ m) * (c : SU σ m)⁻¹) := by
      have h1 : μ l - μ l' =
          lowBlock σ m (c' : SU σ m) - lowBlock σ m (c : SU σ m) := by
        calc μ l - μ l' = (μ l + lowBlock σ m (c : SU σ m)) -
              (μ l' + lowBlock σ m (c : SU σ m)) := by abel
          _ = (μ l' + lowBlock σ m (c' : SU σ m)) -
              (μ l' + lowBlock σ m (c : SU σ m)) := by rw [hB]
          _ = lowBlock σ m (c' : SU σ m) - lowBlock σ m (c : SU σ m) := by abel
      rw [map_sub, h1, lowBlock_mul_inv hc'Q hcQ]
    have hcomm_c' : Commute (c' : SU σ m) g :=
      Subgroup.mem_centralizer_singleton_iff.mp c'.2.2
    have hcomm_c : Commute (c : SU σ m) g :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    have hcent : Commute ((c' : SU σ m) * (c : SU σ m)⁻¹) g :=
      hcomm_c'.mul_left hcomm_c.inv_left
    have hc'cQ : (c' : SU σ m) * (c : SU σ m)⁻¹ ∈ lowRad σ m :=
      (lowRad σ m).mul_mem hc'Q (inv_mem hcQ)
    have hconj : g * ((c' : SU σ m) * (c : SU σ m)⁻¹) * g⁻¹ =
        (c' : SU σ m) * (c : SU σ m)⁻¹ := by
      calc g * ((c' : SU σ m) * (c : SU σ m)⁻¹) * g⁻¹ =
          ((c' : SU σ m) * (c : SU σ m)⁻¹) * g * g⁻¹ := by rw [← hcent.eq]
        _ = (c' : SU σ m) * (c : SU σ m)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel, mul_one]
    have hfix : lowPart σ m g * lowBlock σ m ((c' : SU σ m) * (c : SU σ m)⁻¹) *
        conjTr σ (lowPart σ m g) = lowBlock σ m ((c' : SU σ m) * (c : SU σ m)⁻¹) := by
      rw [← lowBlock_conj g hc'cQ, hconj]
    have hfix' : lowPart σ m g * μ (l - l') * conjTr σ (lowPart σ m g) = μ (l - l') := by
      rw [hsub]
      exact hfix
    have hl : l = l' := sub_eq_zero.mp (hμzero (l - l') hfix')
    subst hl
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq'))
  have hle := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.mul_comm] at hle
  exact hle

theorem exists_lowPart_sub_one_eq_smul [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {g₀ g : SU σ m}
    (hg₀ : g₀ ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (hg : g ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (hg₀₀ : g₀ * g₀ = 1) (hgg : g * g = 1) (hcomm : g * g₀ = g₀ * g)
    (hne : ∃ w ∈ lowRad σ m, g₀ * w * g₀⁻¹ ≠ w)
    (hq : ∀ w ∈ lowRad σ m,
      g * (g₀ * w * g₀⁻¹ * w⁻¹) * g⁻¹ = g₀ * w * g₀⁻¹ * w⁻¹) :
    ∃ c : F, c + σ c = 0 ∧ lowPart σ m g - 1 = c • (lowPart σ m g₀ - 1) := by
  classical
  have hfix₀ : ∀ x ∈ lowSpan F m, suMat σ m g₀ *ᵥ x ∈ lowSpan F m :=
    fun x hx => suMat_mulVec_mem_lowSpan_of_mem_normalizer hσ hg₀ hx
  have hfix : ∀ x ∈ lowSpan F m, suMat σ m g *ᵥ x ∈ lowSpan F m :=
    fun x hx => suMat_mulVec_mem_lowSpan_of_mem_normalizer hσ hg hx
  have hP : lowPart σ m g₀ * lowPart σ m g₀ = 1 := lowPart_mul_self_eq_one hσ hg₀ hg₀₀
  have hP' : lowPart σ m g * lowPart σ m g = 1 := lowPart_mul_self_eq_one hσ hg hgg
  have hPP' : lowPart σ m g₀ * lowPart σ m g = lowPart σ m g * lowPart σ m g₀ := by
    have h1 := lowPart_mul (σ := σ) (m := m) g₀ hfix
    have h2 := lowPart_mul (σ := σ) (m := m) g hfix₀
    rw [← h1, ← h2, hcomm]
  have hP1 : lowPart σ m g₀ ≠ 1 := lowPart_ne_one hg₀ hne
  refine exists_sub_one_eq_smul_sub_one (σ := σ) hσ htr hP hP' hPP' hP1 ?_
  intro M hM
  obtain ⟨w, hw, hBw⟩ := exists_mem_lowRad_lowBlock_eq (σ := σ) (m := m) hσ hM
  have haQ : g₀ * w * g₀⁻¹ ∈ lowRad σ m :=
    (Subgroup.mem_normalizer_iff.mp hg₀ w).1 hw
  have hbQ : w⁻¹ ∈ lowRad σ m := inv_mem hw
  have habQ : g₀ * w * g₀⁻¹ * w⁻¹ ∈ lowRad σ m := (lowRad σ m).mul_mem haQ hbQ
  have hBexp : lowBlock σ m (g₀ * w * g₀⁻¹ * w⁻¹) =
      lowPart σ m g₀ * M * conjTr σ (lowPart σ m g₀) - M := by
    rw [lowBlock_mul haQ hbQ, lowBlock_inv hw, lowBlock_conj g₀ hw, hBw]
    abel
  have hBexp' : lowBlock σ m (g * (g₀ * w * g₀⁻¹ * w⁻¹) * g⁻¹) =
      lowPart σ m g * (lowPart σ m g₀ * M * conjTr σ (lowPart σ m g₀) - M) *
        conjTr σ (lowPart σ m g) := by
    rw [lowBlock_conj g habQ, hBexp]
  rw [hq w hw, hBexp] at hBexp'
  exact hBexp'.symm

end ModelRank

end CFSG.Timmesfeld.Transvection
