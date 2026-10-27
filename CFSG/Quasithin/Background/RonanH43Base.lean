module

public import CFSG.Quasithin.Background.HSL3One

public section

namespace CFSG.Quasithin.RonanH43

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3One CFSG.Open
  CFSG.Assembly.LowTwoRank Matrix

abbrev PV : Type := PairMod (ZMod 2)

abbrev mk (v w : Fin 3 → ZMod 2) : PV := (Multiplicative.ofAdd v, Multiplicative.ofAdd w)

@[expose] def xi (A : Subgroup (MulAut PV)) : Subgroup PV :=
  ⨆ (a : MulAut PV) (_ : a ∈ A) (_ : a ≠ 1), fixV (Subgroup.zpowers a)

@[expose] def commOnR (W : Subgroup PV) (A : Subgroup (MulAut PV)) : Subgroup PV :=
  Subgroup.closure {u | ∃ a ∈ A, ∃ w ∈ W, u = a w * w⁻¹}

@[expose] def conjR (g : MulAut PV) (A : Subgroup (MulAut PV)) : Subgroup (MulAut PV) :=
  A.map (MulAut.conj g).toMonoidHom

theorem fixV_le_xi {A : Subgroup (MulAut PV)} {a : MulAut PV} (ha : a ∈ A) (h1 : a ≠ 1) :
    fixV (Subgroup.zpowers a) ≤ xi A :=
  le_iSup₂_of_le a ha (le_iSup_of_le h1 le_rfl)

theorem xi_le {A : Subgroup (MulAut PV)} {S : Subgroup PV}
    (h : ∀ a ∈ A, a ≠ 1 → fixV (Subgroup.zpowers a) ≤ S) : xi A ≤ S :=
  iSup_le fun a => iSup_le fun ha => iSup_le fun h1 => h a ha h1

theorem mem_conjR {g : MulAut PV} {A : Subgroup (MulAut PV)} {y : MulAut PV} :
    y ∈ conjR g A ↔ ∃ x ∈ A, y = g * x * g⁻¹ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem card_zmod_two : Nat.card (ZMod 2) = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem mem_statedSL_two (g : GL (Fin 3) (ZMod 2)) : g ∈ StatedSL 3 (ZMod 2) := by
  rw [mem_statedSL_iff]
  have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det
    with h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · exact h

theorem pairHom_mem_pairSL (g : GL (Fin 3) (ZMod 2)) : pairHom g ∈ pairSL (ZMod 2) :=
  ⟨g, mem_statedSL_two g, rfl⟩

theorem le_pairNorm_of_perfectCore {M : Subgroup (MulAut PV)}
    (h : perfectCore M = pairSL (ZMod 2)) : M ≤ pairNorm (ZMod 2) := by
  intro x hx
  have h1 : x ∈ Subgroup.normalizer (M : Set (MulAut PV)) := Subgroup.le_normalizer hx
  have h2 := normalizer_le_normalizer_perfectCore M h1
  rwa [h] at h2

theorem norm_cases {x : MulAut PV} (hx : x ∈ pairNorm (ZMod 2)) :
    x ∈ pairSL (ZMod 2) ∨ ∃ h : GL (Fin 3) (ZMod 2), x = swapAut (ZMod 2) * pairHom h := by
  rcases mem_pairSub_or hx with h | h
  · exact Or.inl (mem_pairSL_of_mem_pairSub card_zmod_two hx h)
  · right
    have hy : swapAut (ZMod 2) * x ∈ pairNorm (ZMod 2) :=
      Subgroup.mul_mem _ swapAut_mem_pairNorm hx
    obtain ⟨γ, -, hγ⟩ := mem_pairSL_of_mem_pairSub card_zmod_two hy h
    refine ⟨γ, ?_⟩
    rw [hγ, ← mul_assoc, swapAut_mul_self, one_mul]

theorem swap_pairHom_apply_mk (h : GL (Fin 3) (ZMod 2)) (v w : Fin 3 → ZMod 2) :
    (swapAut (ZMod 2) * pairHom h) (mk v w) = mk ((dualGL h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w)
      ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := rfl

theorem eq_mk (x : PV) : x = mk (Multiplicative.toAdd x.1) (Multiplicative.toAdd x.2) := rfl

end CFSG.Quasithin.RonanH43
