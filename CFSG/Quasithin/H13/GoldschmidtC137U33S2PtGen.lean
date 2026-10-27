module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Gens
public import CFSG.Quasithin.Background.B15P4Comp

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Orbit CFSG.Quasithin.H13.G2Dat CFSG.Quasithin.H13.U3.GC137.S2

variable {W : Type} [CommGroup W]

theorem conj_map_eq (ρ : Gam →* MulAut W) (c : Gam) (K : Subgroup Gam) :
    B1.conjAut (ρ c) (K.map ρ) = (K.map (MulAut.conj c).toMonoidHom).map ρ := by
  rw [B15P4.conjAut_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply]

theorem g2Point_of (ρ : Gam →* MulAut W) (hρ : Function.Injective ρ)
    (hrk : rkIdx (fixV (Asub.map ρ)) = 3)
    (hff : ∀ B : Subgroup (MulAut W), B ≤ Asub.map ρ →
      Nat.card ↥B * Nat.card ↥(fixV B) ≤ Nat.card ↥(Asub.map ρ) * Nat.card ↥(fixV (Asub.map ρ)))
    (hcls : ∀ B : Subgroup Gam, B ≤ Rsub → B ≠ ⊥ → IsElemAbelian2 (B.map ρ) →
      Nat.card W ≤ Nat.card ↥(B.map ρ) * Nat.card ↥(fixV (B.map ρ)) → B = Asub)
    (hCR : ∀ r ∈ Rsub, (∀ w ∈ fixV (Asub.map ρ), ρ r w = w) → r ∈ Asub) :
    G2Point ρ.range ((g2Derived (ZMod 2)).map ρ) (Ppt.map ρ) := by
  have hpc : pCoreOf 2 (Ppt.map ρ) = Rsub.map ρ := by
    rw [pCoreOf_map_injective ρ hρ, pCoreOf_Ppt]
  have hcardA : Nat.card ↥(Asub.map ρ) = 8 := by
    rw [Subgroup.card_map_of_injective hρ, card_Asub]
  refine ⟨Asub.map ρ, ?_, ⟨Subgroup.map_le_range _ _, ?_, ?_, hff⟩, ?_, ?_, hcardA, hrk, ?_⟩
  · rw [hpc]
    exact Subgroup.map_mono Asub_le_Rsub
  · intro h0
    rw [h0] at hcardA
    simp at hcardA
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨j, hj, rfl⟩ := hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact eq_of_code (by
        simp only [matCode_mulG, matCode_sEltG (A_lt i hi), matCode_sEltG (A_lt j hj)]
        exact A_comm i hi j hj)
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨i, hi, rfl⟩ := ha
      rw [← map_pow]
      have : sEltG i ^ 2 = 1 := by
        rw [pow_two]
        exact eq_of_code (by
          simp only [matCode_mulG, matCode_sEltG (A_lt i hi)]
          exact (A_sq i hi).trans matCode_one.symm)
      rw [this, map_one]
  · intro B hB hBo
    rw [hpc] at hB
    set B' : Subgroup Gam := B.comap ρ with hB'
    have hBB : B'.map ρ = B := Subgroup.map_comap_eq_self (hB.trans (Subgroup.map_le_range _ _))
    have hB'R : B' ≤ Rsub := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hB hx
      have : y = x := hρ hyx
      rwa [← this]
    have hne : B' ≠ ⊥ := by
      intro h0
      apply hBo.2.1
      rw [← hBB, h0, Subgroup.map_bot]
    have hff' := hBo.2.2.2 ⊥ bot_le
    rw [B1.fixV_bot, Subgroup.card_bot, Subgroup.card_top, one_mul] at hff'
    rw [← hBB] at hff'
    have := hcls B' hB'R hne (by rw [hBB]; exact hBo.2.2.1) hff'
    rw [← hBB, this]
  · rintro x ⟨hx1, hx2⟩
    rw [hpc] at hx1
    obtain ⟨r, hr, rfl⟩ := hx1
    exact ⟨r, hCR r hr fun w hw => hx2 w hw, rfl⟩
  · refine ⟨ρ cG, ⟨cG, cG_mem, rfl⟩, ?_⟩
    rw [conj_map_eq, ← Subgroup.map_sup, A_sup_conj_eq_top, ← MonoidHom.range_eq_map]
    exact Subgroup.map_le_range _ _

end CFSG.Quasithin.H13.U3.GC137
