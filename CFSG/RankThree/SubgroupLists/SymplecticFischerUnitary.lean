module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerExcl
public import CFSG.Fischer.Classification.Unitary.Model
import all CFSG.Fischer.F4

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Open CFSG.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

namespace UnitaryFischer

@[expose] def IsNormedIsoPt (p : F4 × F4 × F4 × F4) : Prop :=
  p ≠ 0 ∧ p.1 ^ 2 * p.1 + p.2.1 ^ 2 * p.2.1 + p.2.2.1 ^ 2 * p.2.2.1 + p.2.2.2 ^ 2 * p.2.2.2 = 0 ∧
    (p.1 ≠ 0 → p.1 = 1) ∧ (p.1 = 0 → p.2.1 ≠ 0 → p.2.1 = 1) ∧
    (p.1 = 0 → p.2.1 = 0 → p.2.2.1 ≠ 0 → p.2.2.1 = 1) ∧
    (p.1 = 0 → p.2.1 = 0 → p.2.2.1 = 0 → p.2.2.2 ≠ 0 → p.2.2.2 = 1)

instance : DecidablePred IsNormedIsoPt := fun p => by
  unfold IsNormedIsoPt
  infer_instance

theorem card_normedIsoPts : (Finset.univ.filter IsNormedIsoPt).card = 45 := by
  decide

theorem eq_one_of_isNormedIsoPt : ∀ a b c d k : F4, IsNormedIsoPt (a, b, c, d) →
    IsNormedIsoPt (k * a, k * b, k * c, k * d) → k = 1 := by
  decide

@[expose] noncomputable def pad (k : ℕ) (p : F4 × F4 × F4 × F4) : Fin (4 + k) → K :=
  Fin.append ![eF4 p.1, eF4 p.2.1, eF4 p.2.2.1, eF4 p.2.2.2] 0

variable {k : ℕ}

theorem pad_castAdd (p : F4 × F4 × F4 × F4) :
    pad k p (Fin.castAdd k 0) = eF4 p.1 ∧ pad k p (Fin.castAdd k 1) = eF4 p.2.1 ∧
      pad k p (Fin.castAdd k 2) = eF4 p.2.2.1 ∧ pad k p (Fin.castAdd k 3) = eF4 p.2.2.2 := by
  simp [pad]

theorem herm_pad (p : F4 × F4 × F4 × F4) :
    herm frob (pad k p) (pad k p) = eF4 (p.1 ^ 2 * p.1 + p.2.1 ^ 2 * p.2.1 +
      p.2.2.1 ^ 2 * p.2.2.1 + p.2.2.2 ^ 2 * p.2.2.2) := by
  rw [herm_def, Fin.sum_univ_add]
  simp only [frob_apply]
  simp [pad, Fin.sum_univ_four]

theorem pad_ne_zero {p : F4 × F4 × F4 × F4} (hp : p ≠ 0) : pad k p ≠ 0 := by
  intro h
  apply hp
  obtain ⟨e0, e1, e2, e3⟩ := pad_castAdd (k := k) p
  have h0 := congrFun h (Fin.castAdd k 0)
  have h1 := congrFun h (Fin.castAdd k 1)
  have h2 := congrFun h (Fin.castAdd k 2)
  have h3 := congrFun h (Fin.castAdd k 3)
  rw [Pi.zero_apply] at h0 h1 h2 h3
  rw [e0, map_eq_zero_iff _ eF4.injective] at h0
  rw [e1, map_eq_zero_iff _ eF4.injective] at h1
  rw [e2, map_eq_zero_iff _ eF4.injective] at h2
  rw [e3, map_eq_zero_iff _ eF4.injective] at h3
  ext <;> simp [h0, h1, h2, h3]

theorem eq_of_tqU_pad_eq {p p' : F4 × F4 × F4 × F4} (hp : IsNormedIsoPt p)
    (hp' : IsNormedIsoPt p') (h : tqU (pad k p) = tqU (pad k p')) : p = p' := by
  have hiso : ∀ {p : F4 × F4 × F4 × F4}, IsNormedIsoPt p → herm frob (pad k p) (pad k p) = 0 :=
    fun hp => by rw [herm_pad, hp.2.1, map_zero]
  obtain ⟨c, hc⟩ := (tqU_eq_tqU_iff (by omega) (pad_ne_zero hp.1) (hiso hp) (pad_ne_zero hp'.1)
    (hiso hp')).1 h
  obtain ⟨c', rfl⟩ := eF4.surjective c
  have hcoord : ∀ i, pad k p' i = eF4 c' * pad k p i := fun i => by
    rw [hc, Pi.smul_apply, smul_eq_mul]
  obtain ⟨e0, e1, e2, e3⟩ := pad_castAdd (k := k) p
  obtain ⟨e0', e1', e2', e3'⟩ := pad_castAdd (k := k) p'
  have h0 := hcoord (Fin.castAdd k 0)
  have h1 := hcoord (Fin.castAdd k 1)
  have h2 := hcoord (Fin.castAdd k 2)
  have h3 := hcoord (Fin.castAdd k 3)
  rw [e0, e0', ← map_mul, eF4_inj] at h0
  rw [e1, e1', ← map_mul, eF4_inj] at h1
  rw [e2, e2', ← map_mul, eF4_inj] at h2
  rw [e3, e3', ← map_mul, eF4_inj] at h3
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨a', b', c'', d'⟩ := p'
  simp only at h0 h1 h2 h3
  subst h0 h1 h2 h3
  rw [eq_one_of_isNormedIsoPt a b c d c' hp hp']
  simp

end UnitaryFischer

open UnitaryFischer

theorem fischerUnitaryCard : FischerUnitaryCard := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  have hiso : ∀ {p : F4 × F4 × F4 × F4}, IsNormedIsoPt p → herm frob (pad k p) (pad k p) = 0 :=
    fun hp => by rw [herm_pad, hp.2.1, map_zero]
  let S := Finset.univ.filter IsNormedIsoPt
  have hS : ∀ p : S, IsNormedIsoPt p.1 := fun p => (Finset.mem_filter.1 p.2).2
  let F : S → {q : U2 (4 + k) // ∃ h : SUm (4 + k), (h : GL (Fin (4 + k)) K) ∈ TU (4 + k) ∧
      q = (QuotientGroup.mk h : U2 (4 + k))} := fun p =>
    ⟨tqU (pad k p.1), by
      obtain ⟨h, hT, he⟩ := tqU_mem_DU (pad_ne_zero (hS p).1) (hiso (hS p))
      exact ⟨h, hT, he.symm⟩⟩
  have hF : Function.Injective F := fun p p' h =>
    Subtype.ext (eq_of_tqU_pad_eq (hS p) (hS p') (congrArg Subtype.val h))
  have hle := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_normedIsoPts] at hle
  exact hle
