module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513bAux
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Seven
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Arc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513Rev
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan513b_fwd (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) (ℓ : Line Γ) (hs : ¬ LineSingLe Γ G ℓ 4) (a : ℤ) (d : ℕ)
    (hd4 : d ≤ 4) {x z : G} (hxδ : x • ℓ.vert (a + d) = ℓ.vert (a + d))
    (hxα : x • ℓ.vert a ≠ ℓ.vert a) (hz : z ∈ Cinv G (ℓ.vert a)) (hxz : x * z = z * x) :
    False := by
  classical
  have hadj := F.adj_smul
  obtain ⟨hz1, -, hzs, hzc⟩ := hz
  have hzα : z • ℓ.vert a = ℓ.vert a := MulAction.mem_stabilizer_iff.1 hzs
  have hex : ∃ j : ℕ, x • ℓ.vert (a + j) = ℓ.vert (a + j) := ⟨d, hxδ⟩
  set m := Nat.find hex with hmdef
  have hmfix : x • ℓ.vert (a + m) = ℓ.vert (a + m) := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      apply hxα
      have := hmfix
      rw [h] at this
      simpa using this
    · exact h
  have hmd : m ≤ d := Nat.find_min' hex hxδ
  have hmove : x • ℓ.vert (a + m - 1) ≠ ℓ.vert (a + m - 1) := by
    have := Nat.find_min hex (show m - 1 < m by omega)
    rwa [show a + ((m - 1 : ℕ) : ℤ) = a + m - 1 by omega] at this
  have hv0 : (foldArc hadj ℓ a m x hmfix hmove).vert 0 = ℓ.vert a := by
    show foldVert ℓ a m x 0 = ℓ.vert a
    rw [foldVert_le ℓ a m x (Nat.zero_le _)]
    simp
  have hv2 : (foldArc hadj ℓ a m x hmfix hmove).vert (2 * m) = x • ℓ.vert a := by
    have := foldVert_ge ℓ a m x hmfix (k := 2 * m) (by omega)
    rwa [show a + 2 * (m : ℤ) - ((2 * m : ℕ) : ℤ) = a by push_cast; ring] at this
  have hvm : (foldArc hadj ℓ a m x hmfix hmove).vert m = ℓ.vert (a + m) :=
    foldVert_le ℓ a m x le_rfl
  have hvm1 : (foldArc hadj ℓ a m x hmfix hmove).vert (m + 1) = x • ℓ.vert (a + m - 1) := by
    have := foldVert_ge ℓ a m x hmfix (k := m + 1) (by omega)
    rwa [show a + 2 * (m : ℤ) - ((m + 1 : ℕ) : ℤ) = a + m - 1 by push_cast; ring] at this
  have hzxα : z • x • ℓ.vert a = x • ℓ.vert a := by
    rw [smul_smul, ← hxz, mul_smul, hzα]
  have hall := fun k (hk : k ≤ 2 * m) =>
    Arc.fixes_of_ends F.isTree hadj (foldArc hadj ℓ a m x hmfix hmove) (by rwa [hv0])
      (by rwa [hv2]) k hk
  have hzu : z • ℓ.vert (a + m) = ℓ.vert (a + m) := by
    simpa [hvm] using hall m (by omega)
  have hzq : z • x • ℓ.vert (a + m - 1) = x • ℓ.vert (a + m - 1) := by
    simpa [hvm1] using hall (m + 1) (by omega)
  have hadjq : Γ.Adj (ℓ.vert (a + m)) (x • ℓ.vert (a + m - 1)) := by
    have := (hadj x _ _).2 (ℓ.adj_pred (a + m))
    rwa [hmfix] at this
  obtain ⟨X, hXfix, hXq⟩ := Line.exists_move_end hs a hm1 (by omega) hadjq hmove
  have hXz : X * z = z * X :=
    hzc X (MulAction.mem_stabilizer_iff.2 (by simpa using hXfix 0 (Nat.zero_le _)))
  obtain ⟨X', hX'fix, hX'u⟩ := Line.exists_fix_move_next F hs a hm1 (by omega : m ≤ 4 + 1)
  have hX'z : Commute X' z :=
    hzc X' (MulAction.mem_stabilizer_iff.2 (by simpa using hX'fix 0 (by omega)))
  have hYz : (x * X' * x⁻¹) * z = z * (x * X' * x⁻¹) :=
    (((Commute.mul_left (show Commute x z from hxz) hX'z).mul_left
      (show Commute x z from hxz).inv_left)).eq
  have hYq : (x * X' * x⁻¹) • (x • ℓ.vert (a + m - 1)) = x • ℓ.vert (a + m - 1) := by
    have h := hX'fix (m - 1) (by omega)
    rw [show a + ((m - 1 : ℕ) : ℤ) = a + m - 1 by omega] at h
    rw [mul_smul, mul_smul, inv_smul_smul, h]
  have hYu : (x * X' * x⁻¹) • ℓ.vert (a + m) ≠ ℓ.vert (a + m) := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff.2 hmfix.symm]
    intro h
    apply hX'u
    have h2 := congrArg (fun v => x⁻¹ • v) h
    simpa [inv_smul_eq_iff.2 hmfix.symm] using h2
  have hcross : CrossPair (ℓ.vert (a + m)) (x • ℓ.vert (a + m - 1)) X (x * X' * x⁻¹) :=
    ⟨hXfix m le_rfl, hXq, hYq, hYu⟩
  exact no_fixed_cross F h40 h28 hΞ hadjq hcross hz1 hzu hzq hXz hYz

theorem fan513b (F : FanTree Γ G) (h28 : Fan28) (h36 : Fan36 F) : Fan513b F := by
  intro h40 hΞ T hT a d hd x hxδ hxα z hz hxz
  have hs : ¬ LineSingLe Γ G T.line 4 :=
    Sec3Seven.not_lineSingLe_four F h40 h36 T (hasLenTwoReflection_of_inXi hT)
  have hxδ' : x • T.line.vert (a + d) = T.line.vert (a + d) := MulAction.mem_stabilizer_iff.1 hxδ
  have hxα' : x • T.line.vert a ≠ T.line.vert a := fun h =>
    hxα (MulAction.mem_stabilizer_iff.2 h)
  rcases lt_trichotomy d 0 with hneg | hzero | hpos
  · have hs' : ¬ LineSingLe Γ G T.line.rev 4 := fun h => hs (lineSingLe_of_rev h)
    refine fan513b_fwd F h40 h28 hΞ T.line.rev hs' (-a) (-d).toNat (by omega) (x := x) (z := z)
      ?_ ?_ ?_ hxz
    · rw [Line.rev_vert]
      rw [show -(-a + (((-d).toNat : ℕ) : ℤ)) = a + d by omega]
      exact hxδ'
    · rw [Line.rev_vert, neg_neg]
      exact hxα'
    · rw [Line.rev_vert, neg_neg]
      exact hz
  · exact absurd (by simpa [hzero] using hxδ') hxα'
  · refine fan513b_fwd F h40 h28 hΞ T.line hs a d.toNat (by omega) (x := x) (z := z) ?_ hxα' hz hxz
    rw [show a + ((d.toNat : ℕ) : ℤ) = a + d by omega]
    exact hxδ'

end CFSG.Quasithin.Fan86
