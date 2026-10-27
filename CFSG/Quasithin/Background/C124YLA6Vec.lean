module

public import CFSG.Quasithin.Background.C124YLA6Perm
public import CFSG.Quasithin.Background.B4Models

set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv CFSG.Quasithin CFSG.Quasithin.G6

abbrev V6 : Type := Fin 6 → ZMod 2

@[expose] def evenV (m : V6) : Bool := m 0 + m 1 + m 2 + m 3 + m 4 + m 5 == 0

@[expose] def actV (g : P6) (m : V6) : V6 := fun i => m (g⁻¹ i)

@[expose] def kerB (m : V6) : Bool :=
  m 0 == m 1 && m 1 == m 2 && m 2 == m 3 && m 3 == m 4 && m 4 == m 5

@[expose] def fixB (g : P6) (m : V6) : Bool := kerB (fun i => actV g m i - m i)

@[expose] def cntL (l : List P6) : ℕ :=
  (Finset.univ.filter fun m : V6 => evenV m = true ∧ ∀ g ∈ l, fixB g m = true).card

@[expose] def e01 : V6 := ![1, 1, 0, 0, 0, 0]

@[expose] def e25 : V6 := ![0, 0, 1, 0, 0, 1]

@[expose] def e34 : V6 := ![0, 0, 0, 1, 1, 0]

theorem cntL_klist : cntL klist = 8 := by decide +kernel

theorem cntL_congr {l l' : List P6} (h : ∀ g, g ∈ l ↔ g ∈ l') : cntL l = cntL l' := by
  unfold cntL
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun _ => ⟨fun H g hg => H g ((h g).2 hg), fun H g hg => H g ((h g).1 hg)⟩

theorem fixed_vectors : ∀ k ∈ klist, fixB k e01 = true ∧ fixB k e25 = true ∧ fixB k e34 = true := by
  decide +kernel

theorem even_vectors : evenV e01 = true ∧ evenV e25 = true ∧ evenV e34 = true := by
  decide +kernel

theorem cent_dec : ∀ g : P6, Perm.sign g = 1 → fixB g e01 = true → fixB g e25 = true →
    fixB g e34 = true → memP g klist = true := by decide +kernel

theorem moves_dec : fixB (swap 0 2 * swap 4 5) e01 = false := by decide +kernel

theorem witY_moves : (swap 0 2 * swap 4 5 : P6) ∈ Yg := by
  rw [mem_Yg]
  exact (by decide +kernel : inY (swap 0 2 * swap 4 5) = true)

theorem evenV_iff (m : PermMod 6) : m ∈ coreMod 6 ↔ evenV (Multiplicative.toAdd m) = true := by
  rw [mem_coreMod, Fin.sum_univ_six]
  simp [evenV]

theorem kerB_iff (y : V6) : kerB y = true ↔ y = 0 ∨ y = fun _ => 1 := by
  revert y
  decide +kernel

theorem allOnes_mem_core : allOnes 6 ∈ coreMod 6 := by
  rw [mem_coreMod, Fin.sum_univ_six]
  simp only [allOnes, toAdd_ofAdd]
  decide

theorem mem_ker_iff (m : PermMod 6) :
    m ∈ (FFModel.altDn 6).ker ↔ kerB (Multiplicative.toAdd m) = true := by
  rw [kerB_iff]
  show m ∈ Subgroup.zpowers (allOnes 6) ⊓ coreMod 6 ↔ _
  constructor
  · rintro ⟨hz, -⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hk : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hk (k : ZMod 2) with h | h
    · left
      ext i
      simp [allOnes, h]
    · right
      ext i
      simp [allOnes, h]
  · rintro (h | h)
    · have : m = 1 := Multiplicative.toAdd.injective (by simpa using h)
      rw [this]
      exact ⟨one_mem _, one_mem _⟩
    · have : m = allOnes 6 := Multiplicative.toAdd.injective (by simpa [allOnes] using h)
      rw [this]
      exact ⟨Subgroup.mem_zpowers _, allOnes_mem_core⟩

theorem fix_iff (g : P6) (m : PermMod 6) :
    permAct 6 g m * m⁻¹ ∈ (FFModel.altDn 6).ker ↔ fixB g (Multiplicative.toAdd m) = true := by
  rw [mem_ker_iff]
  have : Multiplicative.toAdd (permAct 6 g m * m⁻¹) =
      fun i => actV g (Multiplicative.toAdd m) i - Multiplicative.toAdd m i := by
    ext i
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, permAct_apply, actV]
    exact (sub_eq_add_neg _ _).symm
  rw [this]
  rfl

theorem card_fix_eq (l : List P6) (hl : ∀ g ∈ l, g ∈ alternatingGroup (Fin 6))
    (B : Subgroup ↥(alternatingGroup (Fin 6)))
    (hB : ∀ γ : ↥(alternatingGroup (Fin 6)), γ ∈ B ↔ (γ : P6) ∈ l) :
    Nat.card {m : PermMod 6 // m ∈ coreMod 6 ∧
      ∀ γ ∈ B, permAct 6 (γ : P6) m * m⁻¹ ∈ (FFModel.altDn 6).ker} = cntL l := by
  have e : {m : PermMod 6 // m ∈ coreMod 6 ∧
      ∀ γ ∈ B, permAct 6 (γ : P6) m * m⁻¹ ∈ (FFModel.altDn 6).ker} ≃
      {x : V6 // evenV x = true ∧ ∀ g ∈ l, fixB g x = true} :=
    Equiv.subtypeEquiv Multiplicative.toAdd fun m => by
      rw [evenV_iff]
      refine and_congr_right fun _ => ⟨fun H g hg => ?_, fun H γ hγ => ?_⟩
      · exact (fix_iff g m).1 (H ⟨g, hl g hg⟩ ((hB _).2 hg))
      · exact (fix_iff _ m).2 (H _ ((hB γ).1 hγ))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem card_core : Nat.card ↥(coreMod 6) = 32 := by
  have e : ↥(coreMod 6) ≃ {x : V6 // evenV x = true} :=
    Equiv.subtypeEquiv Multiplicative.toAdd fun m => evenV_iff m
  have h : (Finset.univ.filter fun x : V6 => evenV x = true).card = 32 := by decide +kernel
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, h]

theorem card_ker : Nat.card ↥(FFModel.altDn 6).ker = 2 := by
  have e : ↥(FFModel.altDn 6).ker ≃ {x : V6 // kerB x = true} :=
    Equiv.subtypeEquiv Multiplicative.toAdd fun m => mem_ker_iff m
  have h : (Finset.univ.filter fun x : V6 => kerB x = true).card = 2 := by decide +kernel
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, h]

end CFSG.Quasithin.C124.YL.A6
