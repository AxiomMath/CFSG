module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem o4dich_le_normalizer {Z A B : Subgroup G}
    (hc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hA : A ≤ Z) (hB : B ≤ Z) :
    A ≤ normalizer (B : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : a * h * a⁻¹ = h := by rw [hc a (hA ha) h (hB hh), mul_inv_cancel_right]
    rwa [h1]
  · intro hh
    have h1 : a * (a * h * a⁻¹) = (a * h * a⁻¹) * a := hc a (hA ha) _ (hB hh)
    have h2 : (a * h * a⁻¹) * a = a * h := by group
    rw [h2] at h1
    rwa [mul_left_cancel h1] at hh

private theorem o4dich_main {Q A B Z E Z0 D : Subgroup G} {f : ℕ}
    (hQA : Q = A ⊓ B) (hZE : Z ≤ E) (hAZ : A ⊔ B ≤ Z)
    (hc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hZ0 : Z0 ≤ Z)
    (hidx : A.relIndex Z = 2 ^ f) (hcard : Nat.card B = Nat.card A)
    (hDB : D ≤ normalizer (B : Set G))
    (hfpf : ∀ k ∈ D, k ≠ 1 → ∀ e ∈ E, ⁅e, k⁆ ∈ A → e ∈ A)
    (htr : ∀ x ∈ Z, x ∉ A → ∀ y ∈ Z, y ∉ A → ∃ k ∈ D, k * x * k⁻¹ * y⁻¹ ∈ A) :
    A = Q ∨ (Z0 ≤ A ⊔ B ∧ Q.relIndex A = 2 ^ f ∧
      (∀ k ∈ D, k ≠ 1 → ∀ x ∈ B, k * x * k⁻¹ * x⁻¹ ∈ Q → x ∈ Q) ∧
      (∀ x ∈ B, x ∉ Q → ∀ y ∈ B, y ∉ Q → ∃ k ∈ D, k * x * k⁻¹ * y⁻¹ ∈ Q)) := by
  have hAZ' : A ≤ Z := le_sup_left.trans hAZ
  have hBZ : B ≤ Z := le_sup_right.trans hAZ
  have hQ : ∀ {x : G}, x ∈ Q ↔ x ∈ A ∧ x ∈ B := by
    intro x
    rw [hQA, mem_inf]
  by_cases hBA : B ≤ A
  · left
    rw [hQA, Subgroup.eq_of_le_of_card_ge hBA hcard.ge, inf_idem]
  right
  obtain ⟨x, hxB, hxA⟩ := SetLike.not_le_iff_exists.mp hBA
  have hZle : Z ≤ A ⊔ B := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact mem_sup_left hyA
    obtain ⟨k, hk, hkA⟩ := htr x (hBZ hxB) hxA y hy hyA
    have hkx : k * x * k⁻¹ ∈ B := (mem_normalizer_iff.mp (hDB hk) x).mp hxB
    have hy' : y = (k * x * k⁻¹ * y⁻¹)⁻¹ * (k * x * k⁻¹) := by group
    rw [hy']
    exact mul_mem (mem_sup_left (inv_mem hkA)) (mem_sup_right hkx)
  have hZeq : A ⊔ B = Z := le_antisymm hAZ hZle
  refine ⟨hZ0.trans hZle, ?_, ?_, ?_⟩
  ·
    have h1 : B.relIndex Z = B.relIndex A := by
      rw [← hZeq]
      exact C5.relIndex_sup_eq_of_le_normalizer (o4dich_le_normalizer hc hAZ' hBZ)
    have h2 := C5.card_eq_card_mul_relIndex hBZ
    have h3 := C5.card_eq_card_mul_relIndex hAZ'
    rw [hcard] at h2
    have h4 : B.relIndex Z = A.relIndex Z :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.symm.trans h3)
    rw [hQA, inf_comm, inf_relIndex_right, ← h1, h4, hidx]
  · intro k hk hk1 y hyB hky
    have hyA : ⁅y, k⁆ ∈ A := by
      have h1 : ⁅y, k⁆ = (k * y * k⁻¹ * y⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact (hQ.mp (inv_mem hky)).1
    exact hQ.mpr ⟨hfpf k hk hk1 y (hZE (hBZ hyB)) hyA, hyB⟩
  · intro y hyB hyQ z hzB hzQ
    obtain ⟨k, hk, hkA⟩ := htr y (hBZ hyB) (fun h => hyQ (hQ.mpr ⟨h, hyB⟩)) z (hBZ hzB)
      (fun h => hzQ (hQ.mpr ⟨h, hzB⟩))
    have hky : k * y * k⁻¹ ∈ B := (mem_normalizer_iff.mp (hDB hk) y).mp hyB
    exact ⟨k, hk, hQ.mpr ⟨hkA, mul_mem hky (inv_mem hzB)⟩⟩

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem centerOf_LX_eq_QT_or_caseII {f : ℕ}
    (hQA : t.QT = centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)))
    (hEE : t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT))
    (hAZ : centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ≤ centerOf (t.PX t.QT))
    (hZ0 : t.Zv 0 ≤ centerOf (t.PX t.QT))
    (hidx : (centerOf (t.LX t.QT 1)).relIndex (centerOf (t.PX t.QT)) = 2 ^ f)
    (hcard : Nat.card (centerOf (t.LX t.QT (-1))) = Nat.card (centerOf (t.LX t.QT 1)))
    (hDA : t.D2 ≤ normalizer (centerOf (t.LX t.QT (-1)) : Set G))
    (hfpf : ∀ k ∈ t.D2, k ≠ 1 → ∀ e ∈ t.EX t.QT 1,
      ⁅e, k⁆ ∈ centerOf (t.LX t.QT 1) → e ∈ centerOf (t.LX t.QT 1))
    (htr : ∀ x ∈ centerOf (t.PX t.QT), x ∉ centerOf (t.LX t.QT 1) →
      ∀ y ∈ centerOf (t.PX t.QT), y ∉ centerOf (t.LX t.QT 1) →
        ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ centerOf (t.LX t.QT 1)) :
    centerOf (t.LX t.QT 1) = t.QT ∨
      (t.Zv 0 ≤ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ∧
        t.QT.relIndex (centerOf (t.LX t.QT 1)) = 2 ^ f ∧
        (∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ centerOf (t.LX t.QT (-1)),
          k * x * k⁻¹ * x⁻¹ ∈ t.QT → x ∈ t.QT) ∧
        (∀ x ∈ centerOf (t.LX t.QT (-1)), x ∉ t.QT →
          ∀ y ∈ centerOf (t.LX t.QT (-1)), y ∉ t.QT → ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ t.QT)) :=
  o4dich_main hQA (hEE.symm.le.trans inf_le_left) hAZ
    (fun x hx y hy => ((mem_centralizer_iff.mp hx.2) y hy.1).symm) hZ0 hidx hcard hDA hfpf htr

end Track

end CFSG.Quasithin.Stroth.Rq

end
