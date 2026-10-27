module

public import CFSG.RankThree.PartOne.TAIL.LSideOutAut
public import CFSG.RankThree.PartOne.TAIL.LSideSym
public import CFSG.RankThree.PartOne.TAIL.LSideConj

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix Subgroup
open CFSG.RankThree.PartOne.MB3 (slRe slReEquiv coe_slRe)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

theorem not_dvd_card_sl_six (k : ℕ) (hk : k ≤ 1) :
    ¬ 7 ^ 3 ∣ Nat.card (SpecialLinearGroup (Fin (6 + k)) (ZMod 2)) := by
  interval_cases k
  · show ¬ 7 ^ 3 ∣ Nat.card (SpecialLinearGroup (Fin 6) (ZMod 2))
    rw [Matrix.card_SL_field 6, ZMod.card]
    decide +kernel
  · show ¬ 7 ^ 3 ∣ Nat.card (SpecialLinearGroup (Fin 7) (ZMod 2))
    rw [Matrix.card_SL_field 7, ZMod.card]
    decide +kernel

@[expose] def e0 (k : ℕ) : (Fin 3 ⊕ Fin 3) ⊕ Fin k ≃ Fin (6 + k) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin k))).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[expose] def modelB (k : ℕ) : Subgroup (SpecialLinearGroup (Fin (6 + k)) (ZMod 2)) :=
  (B0 (Fin k)).map (slReEquiv (e0 k)).toMonoidHom

theorem mem_modelB {k : ℕ} {y : SpecialLinearGroup (Fin (6 + k)) (ZMod 2)} :
    y ∈ modelB k ↔ ∃ i j : ℤ, y = slRe (e0 k) (eB (Fin k) i j) := by
  constructor
  · rintro ⟨z, ⟨i, j, rfl⟩, rfl⟩
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨eB (Fin k) i j, eB_mem_B0 i j, rfl⟩

theorem card_modelB (k : ℕ) : Nat.card (modelB k) = 49 := by
  rw [modelB, Subgroup.card_map_of_injective (f := (slReEquiv (e0 k)).toMonoidHom)
    (slReEquiv (e0 k)).injective, card_B0]

theorem graph_modelB (k : ℕ) : ∀ b ∈ modelB k, slGraphAut (6 + k) (ZMod 2) b = b⁻¹ := by
  intro b hb
  obtain ⟨i, j, rfl⟩ := mem_modelB.1 hb
  exact graph_slRe_eB (e0 k) i j

theorem irr_modelB (k : ℕ) : ∀ d ∈ modelB k, d ≠ 1 →
    ∃ g ∈ Subgroup.normalizer (modelB k : Set (SpecialLinearGroup (Fin (6 + k)) (ZMod 2))),
      g * d * g⁻¹ ∉ Subgroup.zpowers d := by
  intro d hd hd1
  obtain ⟨i, j, rfl⟩ := mem_modelB.1 hd
  have hd0 : eB (Fin k) i j ≠ 1 := fun h => hd1 (by rw [h, map_one])
  obtain ⟨g₀, hg₀, hng⟩ := irreducible_B0 _ (eB_mem_B0 i j) hd0
  refine ⟨slRe (e0 k) g₀, ?_, ?_⟩
  · refine mem_normalizer_of_conj_mem' fun y hy => ?_
    obtain ⟨i', j', rfl⟩ := mem_modelB.1 hy
    have hc : g₀ * eB (Fin k) i' j' * g₀⁻¹ ∈ B0 (Fin k) :=
      (Subgroup.mem_normalizer_iff.1 hg₀ _).1 (eB_mem_B0 i' j')
    obtain ⟨i'', j'', hij⟩ := hc
    refine mem_modelB.2 ⟨i'', j'', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hij]
  · intro hmem
    apply hng
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, (slReEquiv (e0 k)).injective ?_⟩
    show slRe (e0 k) _ = slRe (e0 k) _
    rw [map_zpow, map_mul, map_mul, map_inv]
    exact hm

theorem model_facts (k : ℕ) (hk : k ≤ 1)
    {B : Subgroup (SpecialLinearGroup (Fin (6 + k)) (ZMod 2))} (hB : Nat.card B = 49) :
    (∀ d ∈ B, d ≠ 1 → ∃ g ∈ Subgroup.normalizer (B : Set _), g * d * g⁻¹ ∉ Subgroup.zpowers d) ∧
    (∀ α : MulAut (SpecialLinearGroup (Fin (6 + k)) (ZMod 2)), (∀ x, x ∈ B ↔ α x ∈ B) →
      ∃ l ∈ Subgroup.normalizer (B : Set _),
        (∀ x ∈ B, l * α x * l⁻¹ = x) ∨ (∀ x ∈ B, l * α x * l⁻¹ = x⁻¹)) := by
  obtain ⟨u, hu⟩ := exists_conj_of_card_forty_nine (not_dvd_card_sl_six k hk) (card_modelB k) hB
  exact ⟨irr_of_conj hu (irr_modelB k), fun α hα =>
    aut_pm_of_conj hu (graph_modelB k) (aut_sl_zmod_two (by omega)) α hα⟩

end CFSG.RankThree.PartOne.TAIL
