module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private theorem ggQ2s08ab_card_bs (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) : Nat.card ↥Bs = 3 ^ n := by
  have hV : Nat.card M.V = 3 ^ n := by
    rw [Nat.card_congr κ.toEquiv]
    simp [Vn, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
    _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
    _ = 3 ^ n := hV

private theorem ggQ2s08ab_card_comap (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) (R : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n))
    (hR : R ≤ (ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)) :
    Nat.card ↥(R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs) = Nat.card ↥R := by
  have hinj : Function.Injective (ggQ2CellLin M κ) := ggQ2CellLin_injective M κ
  have hmap : (R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ) = R := by
    apply le_antisymm
    · intro r hr
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hr
      exact hφ.1
    · intro r hr
      obtain ⟨φ, hφA, hφr⟩ := Subgroup.mem_map.mp (hR hr)
      refine Subgroup.mem_map.mpr ⟨φ, ⟨?_, hφA⟩, hφr⟩
      exact Subgroup.mem_comap.mpr (hφr ▸ hr)
  have hcard : Nat.card ↥((R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs).map
      (ggQ2CellLin M κ)) = Nat.card ↥(R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs) :=
    Subgroup.card_map_of_injective (f := ggQ2CellLin M κ) hinj
  rw [hmap] at hcard
  exact hcard.symm

private lemma ggQ2s08ab_lin_aux : ∀ k : ℕ, 6 * (k + 10) ≤ 3 ^ (k + 9) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : (k + 1) + 10 = (k + 10) + 1 := by omega
    have h2 : (k + 1) + 9 = (k + 9) + 1 := by omega
    rw [h1, h2, pow_succ]
    nlinarith [ih]

private lemma ggQ2s08ab_lin (m : ℕ) (hm : 9 ≤ m) : 6 * (m + 1) ≤ 3 ^ m := by
  have h := ggQ2s08ab_lin_aux (m - 9)
  have h1 : m - 9 + 10 = m + 1 := by omega
  have h2 : m - 9 + 9 = m := by omega
  rwa [h1, h2] at h

private lemma ggQ2s08ab_tri (m : ℕ) : m + m * (m - 1) / 2 = (m + 1) * m / 2 := by
  have h1 : m * (m - 1) / 2 = m.choose 2 := (Nat.choose_two_right m).symm
  have h2 : (m + 1) * m / 2 = (m + 1).choose 2 := by
    rw [Nat.choose_two_right (m + 1)]
    simp
  rw [h1, h2, Nat.choose_succ_succ m 1, Nat.choose_one_right m]

private theorem ggQ2s08ab_count {r : ℕ} (hr : 11 ≤ r) :
    8 * (3 ^ (r + 1) * (4 * (2 ^ r * r.factorial))) < 3 ^ (r * (r - 1) / 2) := by
  refine Nat.le_induction (m := 11)
    (P := fun r _ => 8 * (3 ^ (r + 1) * (4 * (2 ^ r * r.factorial))) <
      3 ^ (r * (r - 1) / 2)) ?base ?step r hr
  · norm_num [Nat.factorial]
  · intro m hm ih
    rw [show (m + 1) - 1 = m by omega]
    have hident : 8 * (3 ^ (m + 1 + 1) * (4 * (2 ^ (m + 1) * (m + 1).factorial)))
        = 6 * (m + 1) * (8 * (3 ^ (m + 1) * (4 * (2 ^ m * m.factorial)))) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    have hbound : 6 * (m + 1) ≤ 3 ^ m := ggQ2s08ab_lin m (by omega)
    calc
      8 * (3 ^ (m + 1 + 1) * (4 * (2 ^ (m + 1) * (m + 1).factorial)))
          = 6 * (m + 1) * (8 * (3 ^ (m + 1) * (4 * (2 ^ m * m.factorial)))) := hident
      _ ≤ 3 ^ m * (8 * (3 ^ (m + 1) * (4 * (2 ^ m * m.factorial)))) :=
            Nat.mul_le_mul_right _ hbound
      _ < 3 ^ m * 3 ^ (m * (m - 1) / 2) :=
            mul_lt_mul_of_pos_left ih (pow_pos (by norm_num) m)
      _ = 3 ^ (m + m * (m - 1) / 2) := by rw [← pow_add]
      _ = 3 ^ ((m + 1) * m / 2) := by rw [ggQ2s08ab_tri m]

theorem ggQ2s08_bigA_bound [Finite G]
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (M : GGQ2LDatum 3 Bs L x) (hA : M.ShapeA) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab)
    (hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab))
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (h12 : 12 ≤ lab.rank + 1)
    (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :
    ∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
      R ≤ (ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ) →
      8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2) := by
  classical
  intro R hR
  have hBs : Nat.card ↥Bs = 3 ^ (lab.rank + 1) := ggQ2s08ab_card_bs M κ
  have hN : 11 ≤ lab.rank := by omega
  have h1 := ggQ2s08_stab_card_le_all hTBW hS hnc M.hx M
    (Or.inr (Or.inl hA)) hlab hmark hInn hCen hOut hMW
  have hDiag := ggQ2s08_diagPerm_card_le (M := M.coxeter) hlab hMW M.isCartan
  have hCardAut := ggQ2s08_card_automizer_le M hlab hMW
  have hstab : Nat.card ↥(ggAutomizer ⊤ Bs ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨x, M.hx⟩ : ↥Bs)) ≤
      4 * (2 ^ lab.rank * lab.rank.factorial) := by
    calc _ ≤ 2 * Nat.card {π : M.Λ ≃ M.Λ // GGQ2S08DiagPerm 3 M.cartan π} *
        Nat.card ↥(ggAutomizer L Bs) := h1
      _ ≤ 2 * 2 * (2 ^ lab.rank * lab.rank.factorial) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hDiag) hCardAut
      _ = 4 * (2 ^ lab.rank * lab.rank.factorial) := by ring
  let A' : Subgroup (MulAut ↥Bs) :=
    R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs
  have hcard : Nat.card ↥A' = Nat.card ↥R := ggQ2s08ab_card_comap M κ R hR
  have horbit : Nat.card ↥A' ≤
      Nat.card ↥Bs * (4 * (2 ^ lab.rank * lab.rank.factorial)) :=
    ggQ2s08_card_le_of_stab M.hx hstab (A := A') inf_le_right
  rw [hcard, hBs] at horbit
  calc 8 * Nat.card R
        ≤ 8 * (3 ^ (lab.rank + 1) * (4 * (2 ^ lab.rank * lab.rank.factorial))) :=
          Nat.mul_le_mul_left 8 horbit
    _ < 3 ^ (lab.rank * (lab.rank - 1) / 2) := ggQ2s08ab_count hN

end CFSG.StandardType

end
