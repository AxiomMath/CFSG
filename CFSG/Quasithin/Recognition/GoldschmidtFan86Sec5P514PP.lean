module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem edgeCirc_pred_of_five (F : FanTree Γ G) (ℓ : Line Γ) {i : ℤ}
    (h : valence Γ (ℓ.vert i) = 5) :
    ℓ.edgeCirc (G := G) (i - 1) = Gcirc Γ G (ℓ.vert i) (ℓ.vert (i - 1)) := by
  have hne : valence Γ (ℓ.vert (i - 1)) ≠ 5 := fun h' =>
    F.alternating _ _ (ℓ.adj_pred i) (h.trans h'.symm)
  have := ℓ.edgeCirc_of_ne_five (G := G) hne
  rwa [sub_add_cancel] at this

theorem mul_cj_inv {z z' : G} (hz2 : z * z = 1) (hz2' : z' * z' = 1) :
    (z * cj z z') * (z' * cj z' z) = 1 := by
  calc (z * cj z z') * (z' * cj z' z) = z * z' * z * (z' * z') * z * z' * z := by
        simp only [cj, mul_assoc]
    _ = z * z' * (z * z) * z' * z := by rw [hz2', mul_one]; simp only [mul_assoc]
    _ = z * (z' * z') * z := by rw [hz2, mul_one]; simp only [mul_assoc]
    _ = 1 := by rw [hz2', mul_one, hz2]

theorem cj_comm_eq {z z' : G} (hz2 : z * z = 1) (hz2' : z' * z' = 1) (hw : (z * cj z z') *
    (z * cj z z') = 1) : z' * cj z' z = z * cj z z' :=
  (eq_inv_of_mul_eq_one_right (mul_cj_inv hz2 hz2')).trans (inv_eq_of_mul_eq_one_right hw)

theorem pp_perfect (F : FanTree Γ G) (h40 : Fan40 F) (h53c : Fan53c F) (h54 : Fan54 F)
    (h55b : Fan55b F) (T : Track Γ G) (hT : T.fixer = ⊥) {z z' : G}
    {a b tL tR a' b' tL' tR' : ℤ} (hz : z ∈ T.line.Zc) (hz' : z' ∈ T.line.Zc)
    (hpp : T.line.InPerfectPos z z' a b tL tR a' b' tL' tR')
    (hv5 : valence Γ (T.line.vert b) = 5) (hv5' : valence Γ (T.line.vert a') = 5) :
    tR - b ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨hzl, hzr, hpl, hpr⟩ := hpp
  have hz2 : z * z = 1 := hz.1
  have hz2' : z' * z' = 1 := hz'.1
  obtain ⟨hab, hzfix, hzcen, -⟩ := hzl.core
  obtain ⟨hab', hzfix', hzcen', -⟩ := hzr.core
  have fz : ∀ i, tL ≤ i → i ≤ tR → z • T.line.vert i = T.line.vert i := fun i h1 h2 =>
    (hzl.fix i).2 ⟨h1, h2⟩
  have fz' : ∀ i, tL' ≤ i → i ≤ tR' → z' • T.line.vert i = T.line.vert i := fun i h1 h2 =>
    (hzr.fix i).2 ⟨h1, h2⟩
  have tLa : tL ≤ a := ((hzl.fix a).1 (hzfix a le_rfl hab.le)).1
  have bR : b ≤ tR := ((hzl.fix b).1 (hzfix b hab.le le_rfl)).2
  have tL'a' : tL' ≤ a' := ((hzr.fix a').1 (hzfix' a' le_rfl hab'.le)).1
  have b'R : b' ≤ tR' := ((hzr.fix b').1 (hzfix' b' hab'.le le_rfl)).2
  have hzb1 : ∀ i, z' • T.line.vert i ≠ T.line.vert i → i < tL' ∨ tR' < i := fun i h => by
    by_contra hc
    push Not at hc
    exact h (fz' i hc.1 hc.2)
  have hz'p : z' • T.line.vert (b - 1) ≠ T.line.vert (b - 1) := fun h => by
    have := ((hzr.fix (b - 1)).1 h).1
    omega
  have hzp' : z • T.line.vert (a' + 1) ≠ T.line.vert (a' + 1) := fun h => by
    have := ((hzl.fix (a' + 1)).1 h).2
    omega
  have hAL1 := perm_cen F (v := T.line.vert b) (p := T.line.vert (b - 1))
    (q := T.line.vert (b + 1)) (T.line.adj_pred b) (T.line.adj b) (T.line.vert_pred_ne_succ b)
    hz2 hz2' (fz b (by omega) (by omega)) (fz (b - 1) (by omega) (by omega))
    (fz (b + 1) (by omega) (by omega))
    (by rw [← edgeCirc_pred_of_five F T.line hv5]; exact hzcen (b - 1) (by omega) (by omega))
    (fz' b (by omega) (by omega)) (fz' (b + 1) (by omega) (by omega)) hz'p
  have hAL2 := perm_cen F (v := T.line.vert a') (p := T.line.vert (a' + 1))
    (q := T.line.vert (a' - 1)) (T.line.adj a') (T.line.adj_pred a')
    (T.line.vert_pred_ne_succ a').symm hz2' hz2 (fz' a' (by omega) (by omega))
    (fz' (a' + 1) (by omega) (by omega)) (fz' (a' - 1) (by omega) (by omega))
    (by rw [← T.line.edgeCirc_of_five hv5']; exact hzcen' a' le_rfl hab')
    (fz a' (by omega) (by omega)) (fz (a' - 1) (by omega) (by omega)) hzp'
  have huu := cj_comm_eq hz2 hz2' hAL1.1
  have hcenR : z * cj z z' ∈ Cen (T.line.edgeCirc (G := G) b) := by
    rw [T.line.edgeCirc_of_five hv5]; exact hAL1.2
  have hcenL : z * cj z z' ∈ Cen (T.line.edgeCirc (G := G) (a' - 1)) := by
    rw [← huu, edgeCirc_pred_of_five F T.line hv5']; exact hAL2.2
  have hne : z' * z ≠ z * z' := h54 h40 T.line z a b hz hzl.core b (b - 1) (Or.inl ⟨rfl, rfl⟩)
    z' (MulAction.mem_stabilizer_iff.2 (fz' b (by omega) (by omega)))
    (fun h => hz'p (MulAction.mem_stabilizer_iff.1 h))
  have hu1 : z * cj z z' ≠ 1 := perm_ne_one hz2 hz2' hne
  have hufix : ∀ i, b ≤ i → i ≤ a' → (z * cj z z') • T.line.vert i = T.line.vert i := by
    intro i h1 h2
    simp only [cj, mul_smul]
    rw [fz' i (by omega) (by omega), fz i (by omega) (by omega), fz' i (by omega) (by omega),
      fz i (by omega) (by omega)]
  obtain ⟨tLu, tRu, hfixu⟩ := exists_fixIdx_interval F T hT hu1
    (i₀ := b) (hufix b le_rfl (by omega))
  have huZ : z * cj z z' ∈ T.line.Zc := ⟨hAL1.1, b, hcenR⟩
  have hP : ∀ k, z * cj z z' ∈ Cen (T.line.edgeCirc (G := G) k) →
      k ∈ T.line.fixIdx (z * cj z z') ∧ k + 1 ∈ T.line.fixIdx (z * cj z z') := fun k hk => by
    have := T.line.edgeCirc_fix hk.1
    exact ⟨this.1, this.2⟩
  obtain ⟨a₁, b₁, ha₁, hb₁, hc1⟩ := exists_isCoreWith T.line
    (P := fun k => z * cj z z' ∈ Cen (T.line.edgeCirc (G := G) k)) hfixu hP hcenR
  obtain ⟨a₂, b₂, ha₂, hb₂, hc2⟩ := exists_isCoreWith T.line
    (P := fun k => z * cj z z' ∈ Cen (T.line.edgeCirc (G := G) k)) hfixu hP hcenL
  have hid := h55b h40 T _ a₁ b₁ tLu tRu a₂ b₂ huZ ⟨hfixu, hc1⟩ hc2
  have hle := h53c h40 T.line _ a₁ b₁ huZ hc1
  omega

end P514

end CFSG.Quasithin.Fan86
