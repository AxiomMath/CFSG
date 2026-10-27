module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddCount

public section

namespace CFSG.StandardType

namespace OrthRestOdd

open Module CFSG.RankThree.PartOne.LIT

universe u v

variable {K : Type u} [Field K]

theorem exists_commSpace_two_fix {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {X : Type v} [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] (hn : 6 ≤ finrank K X) {B : X →ₗ[K] X →ₗ[K] K}
    {E : Subgroup (X ≃ₗ[K] X)} [Finite E] (hE : IsoGroup B p E) {Y : Submodule K X}
    (hY : Y ≠ ⊥) (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) (hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, B y y' = 0)
    (hcard : p ^ (finrank K X / 2 - 1) ≤ Nat.card E) :
    ∃ t ∈ E, t ≠ 1 ∧ finrank K (commSpace t) = 2 ∧
      ∃ Y' : Submodule K X, Y' ≠ ⊥ ∧ Y' ≤ Y ∧ (∀ g ∈ E, ∀ y ∈ Y', g y ∈ Y') ∧
        ∀ y ∈ Y', t y = y := by
  obtain ⟨k, hk⟩ := hE.even_finrank
  rcases card_le_or_exists_fix hE hp hpK hY hYinv with hle | ⟨g, hgE, hg1, Y', hY'0, hY'Y,
    hY'inv, hgY'⟩
  · exfalso
    have : p ^ 2 ≤ p ^ (finrank K X / 2 - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have := hp.one_lt
    have : p < p ^ 2 := by nlinarith
    omega
  · have hc := hE.isCompl hpK hgE
    have hEU := hE.resFix hpK hgE
    have hEW := hE.resComm hpK hgE
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    obtain ⟨a, ha⟩ := hEU.even_finrank
    obtain ⟨b, hb⟩ := hEW.even_finrank
    have hW0 : finrank K (commSpace g) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      exact commSpace_ne_bot hg1
    have hY'U : Y' ≤ fixedSpace g := fun y hy => mem_fixedSpace.mpr (hgY' y hy)
    set Y'' : Submodule K (fixedSpace g) := Y'.comap (fixedSpace g).subtype with hY''
    have hY''0 : Y'' ≠ ⊥ := by
      intro h
      obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'0
      have hmem : (⟨y, hY'U hyY⟩ : fixedSpace g) ∈ Y'' := hyY
      rw [h, Submodule.mem_bot] at hmem
      exact hy0 (congrArg Subtype.val hmem)
    have hU0 : finrank K (fixedSpace g) ≠ 0 := by
      intro h
      apply hY''0
      have : Subsingleton (fixedSpace g) := Module.finrank_zero_iff.mp h
      exact Subsingleton.elim _ _
    have h1 := card_le_of_isotropic hp hpK hK1 (finrank K (fixedSpace g)) (fixedSpace g) rfl _ _
      hEU Y'' hY''0
      (by
        rintro _ ⟨h, rfl⟩ z hz
        exact hY'inv h h.2 z hz)
      (fun y hy y' hy' => hYiso y (hY'Y hy) y' (hY'Y hy'))
    have h2 := hEW.card_le hp hpK
    have h3 := card_le_mul_res hc (hE.fix_inv hgE) (hE.comm_inv hgE)
    have hpa : 0 < p ^ (finrank K (fixedSpace g) / 2 - 1) := pow_pos hp.pos _
    have hsplit : p ^ (finrank K X / 2 - 1) = p ^ (finrank K (fixedSpace g) / 2 - 1) *
        p ^ (finrank K (commSpace g) / 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hW : p ^ (finrank K (commSpace g) / 2) ≤
        Nat.card (resHom E _ (hE.comm_inv hgE)).range := by
      refine Nat.le_of_mul_le_mul_left ?_ hpa
      calc _ = p ^ (finrank K X / 2 - 1) := hsplit.symm
        _ ≤ Nat.card E := hcard
        _ ≤ _ := h3
        _ ≤ _ := Nat.mul_le_mul_right _ h1
    have hmul : Nat.card (resHom E _ (hE.fix_inv hgE)).range *
        Nat.card (resHom E _ (hE.comm_inv hgE)).range ≤ Nat.card E := by
      calc _ ≤ p ^ (finrank K (fixedSpace g) / 2 - 1) * p ^ (finrank K (commSpace g) / 2) :=
            Nat.mul_le_mul h1 h2
        _ = _ := hsplit.symm
        _ ≤ Nat.card E := hcard
    obtain ⟨tW, htW, htW1, htW2⟩ := exists_commSpace_two_of_full hp hpK
      (finrank K (commSpace g)) (commSpace g) rfl (by omega) _ _ hEW hW
    obtain ⟨t, htU, htW'⟩ := exists_lift hc _ _ hmul (one_mem _) htW
    refine ⟨t, t.2, fun h => htW1 ?_, ?_, Y', hY'0, hY'Y, hY'inv, fun y hy => ?_⟩
    · rw [← htW', show t = 1 from Subtype.ext h, map_one]
    · rw [finrank_commSpace_of_res_eq_one hc _ (hE.comm_inv hgE) htU, htW', htW2]
    · exact congrArg Subtype.val (LinearEquiv.congr_fun htU ⟨y, hY'U hy⟩)

end OrthRestOdd

end CFSG.StandardType
