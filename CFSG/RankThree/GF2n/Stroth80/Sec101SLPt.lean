module

public import CFSG.RankThree.GF2n.Stroth80.Sec123Order
public import CFSG.RankThree.GF2n.Stroth80.Sec101Orbit
public import CFSG.RankThree.GF2n.Stroth80.Sec101SLVec

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_mem_inf_QB_of_mem_normalizer (hc : Ctx M Q Z B) {y σ : G} (hy : y ∈ Q)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) (hσ : σ ∈ LB M Q B) :
    ⁅y, σ⁆ ∈ Q ⊓ QB B := by
  obtain ⟨s, hs, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB hσ
  have hsM : s ∈ M := (Subgroup.mem_inf.mp hs).2
  have hsQB : s ∈ QB B := (Subgroup.mem_inf.mp hs).1
  have hZD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q (Ctx.Z_le_QB hc).1
  have hys : ⁅y, s⁆ ∈ Q ⊓ QB B := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hsQ : s * y⁻¹ * s⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) y⁻¹).mp (Q.inv_mem hy)
      rw [show ⁅y, s⁆ = y * (s * y⁻¹ * s⁻¹) by
        simp only [commutatorElement_def]; group]
      exact Q.mul_mem hy hsQ
    · have hyQB : y * s * y⁻¹ ∈ QB B := hc.conj_QB_of_mem_normalizer hyB hsQB
      rw [show ⁅y, s⁆ = (y * s * y⁻¹) * s⁻¹ by
        simp only [commutatorElement_def]]
      exact (QB B).mul_mem hyQB ((QB B).inv_mem hsQB)
  have hqZ : ⁅y, q⁆ ∈ Z := Smith81.comm_mem_Z hc.hyp hy hq
  have hsq : s * ⁅y, q⁆ * s⁻¹ ∈ Q ⊓ QB B :=
    hZD ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hsM) _).mp hqZ)
  rw [commutatorElement_mul_right_eq_mul_conj]
  simpa only [mul_assoc] using (Q ⊓ QB B).mul_mem hys hsq

theorem IsSaturated101.Vt_le (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    {σ : G} (hσ : σ ∈ LB M Q C) (hσQ : σ ∉ Q) (hR : Rt M (LB M Q C) σ ≠ LB M Q C) :
    Vt M (LB M Q C) C Z σ ≤ X := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  have hsl : SLlike hcC σ := (HC.alt σ hσ hσQ).resolve_left hR
  obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
  have hslC : SLNat hcC σ := hslm.toSLNat hm2
  have h35 := (stroth_3_5 h34 hcC HC.width HC.n_gt HC.noA2 HC.gen).2.1
  have hVinf : Vt M (LB M Q C) C Z σ ≤ Q ⊓ QB C :=
    hcC.Vt_le_inf_QB_of_SLNat (HC.toSec5 hσ hσQ) h35 hslC
  refine sec39_Vt_le hX.Z_le fun k hkM hT => ?_
  have hD : IsRootB M B (conjSubgroup k C) := hC.conj hkM
  exact hsat C hC hCX (conjSubgroup k C) hD ((sec39_conjB_le_Vt hkM hT).trans hVinf)

private theorem comm_mem_sup_Z_of_root (hc : Ctx M Q Z B) {X : Subgroup G}
    (hX : IsClique101 M Q Z B X) {E : Subgroup G} (hE : IsRootB M B E) (hEX : E ≤ X)
    {σ x : G} (hσ : σ ∈ LB M Q E) (hx : x ∈ X) : ⁅x, σ⁆ ∈ E ⊔ Z := by
  have hcE : Ctx M Q Z E := hE.ctx hc
  obtain ⟨s, hs, q, hq, rfl⟩ := hcE.exists_mul_of_mem_LB hσ
  have hsM : s ∈ M := (Subgroup.mem_inf.mp hs).2
  have hsQB : s ∈ QB E := (Subgroup.mem_inf.mp hs).1
  have hxQ : x ∈ Q := hX.le_Q hx
  have hxQB : x ∈ QB E := hX.le_QB E hE hEX hx
  have hxs : ⁅x, s⁆ ∈ E := hcE.QB_comm_mem hxQB hsQB
  have hxq : ⁅x, q⁆ ∈ Z := Smith81.comm_mem_Z hc.hyp hxQ hq
  have hsq : s * ⁅x, q⁆ * s⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hsM) _).mp hxq
  rw [commutatorElement_mul_right_eq_mul_conj]
  simpa only [mul_assoc] using
    (E ⊔ Z).mul_mem (Subgroup.mem_sup_left hxs) (Subgroup.mem_sup_right hsq)

theorem IsRootB.inf_sup_Z_eq_Z_of_not_le {hc : Ctx M Q Z B} {E E' : Subgroup G}
    (hE : IsRootB M B E) (hE' : IsRootB M B E') (h : ¬ E' ≤ E ⊔ Z) :
    (E ⊔ Z) ⊓ (E' ⊔ Z) = Z := by
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  intro w hw
  by_contra hwZ
  have hw1 : w ≠ 1 := fun h1 => hwZ (h1 ▸ Z.one_mem)
  obtain ⟨p, hpQ, hwp⟩ := (hE.ctx hc).exists_mem_conj_of_mem_sup hw.1 hwZ
  obtain ⟨p', hp'Q, hwp'⟩ := (hE'.ctx hc).exists_mem_conj_of_mem_sup hw.2 hwZ
  have hEp : IsRootB M B (conjSubgroup p E) := hE.conj (hc.hyp.Q_normal.1 hpQ)
  have hE'p : IsRootB M B (conjSubgroup p' E') := hE'.conj (hc.hyp.Q_normal.1 hp'Q)
  have heq : conjSubgroup p E = conjSubgroup p' E' :=
    Smith81.IsZConjugate.eq_of_mem hc.hyp (hEp.isZConjugate hc) (hE'p.isZConjugate hc)
      hw1 hwp hwp'
  have hE'eq : E' = conjSubgroup (p'⁻¹ * p) E := by
    have h1 := congrArg (conjSubgroup p'⁻¹) heq
    simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
    exact h1.symm
  have hQ : p'⁻¹ * p ∈ Q := Q.mul_mem (Q.inv_mem hp'Q) hpQ
  have hle : E' ≤ E ⊔ Z := by
    rw [hE'eq]
    calc conjSubgroup (p'⁻¹ * p) E ≤ conjSubgroup (p'⁻¹ * p) (E ⊔ Z) :=
          Subgroup.map_mono le_sup_left
      _ = E ⊔ Z := (hE.ctx hc).conj_sup_Z_of_mem_Q hQ
  exact h hle

theorem IsSaturated101.comm_mem_Z (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    (hsat : IsSaturated101 M Q Z B X) {C : Subgroup G} (hC : IsRootB M B C) (hCX : C ≤ X)
    {σ : G} (hσ : σ ∈ LB M Q C) (hσQ : σ ∉ Q) (hR : Rt M (LB M Q C) σ ≠ LB M Q C) :
    ∀ x ∈ X, ⁅x, σ⁆ ∈ Z := by
  have hcC : Ctx M Q Z C := hC.ctx hc
  have HC : Sec10Hyp hcC n := hC.sec10 H
  have hsl : SLlike hcC σ := (HC.alt σ hσ hσQ).resolve_left hR
  obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
  have hVcard : Nat.card ↥(Vt M (LB M Q C) C Z σ) = Nat.card Z ^ (m + 1) :=
    SLMNat.card_Vt hslm
  have hCcard : Nat.card C = Nat.card Z := (hC.isZConjugate hc).card_eq
  have hCZcard : Nat.card ↥(C ⊔ Z) = Nat.card Z ^ 2 := by
    rw [hcC.card_sup_Z, hCcard]
    ring
  have hVgt : Nat.card ↥(C ⊔ Z) < Nat.card ↥(Vt M (LB M Q C) C Z σ) := by
    rw [hCZcard, hVcard]
    have hq1 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
    calc Nat.card Z ^ 2 < Nat.card Z ^ 3 := Nat.pow_lt_pow_right hq1 (by omega)
      _ ≤ Nat.card Z ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hVnotle : ¬ Vt M (LB M Q C) C Z σ ≤ C ⊔ Z := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  have hex : ∃ k : G, k ∈ M ∧ σ ∈ conjSubgroup k (LB M Q C) ∧
      ¬ conjSubgroup k C ≤ C ⊔ Z := by
    by_contra hex
    have hle : Vt M (LB M Q C) C Z σ ≤ C ⊔ Z :=
      sec39_Vt_le le_sup_right fun k hkM hT => by
        by_contra hkZ
        exact hex ⟨k, hkM, hT, hkZ⟩
    exact hVnotle hle
  obtain ⟨k, hkM, hT, hnot⟩ := hex
  have hD : IsRootB M B (conjSubgroup k C) := hC.conj hkM
  have hDX : conjSubgroup k C ≤ X :=
    (sec39_conjB_le_Vt hkM hT).trans
      (IsSaturated101.Vt_le h34 H hX hsat hC hCX hσ hσQ hR)
  have hσD : σ ∈ LB M Q (conjSubgroup k C) := by
    rw [hcC.LB_conj hkM]
    exact hT
  intro x hx
  have h1 := comm_mem_sup_Z_of_root hc hX hC hCX hσ hx
  have h2 := comm_mem_sup_Z_of_root hc hX hD hDX hσD hx
  have h3 := IsRootB.inf_sup_Z_eq_Z_of_not_le (hc := hc) hC hD hnot
  exact h3 ▸ Subgroup.mem_inf.mpr ⟨h1, h2⟩

theorem IsSaturated101.inf_QB_le_Z (hc : Ctx M Q Z B) {X X' : Subgroup G}
    (hsat : IsSaturated101 M Q Z B X) (hX' : IsClique101 M Q Z B X') (hXX' : X ⊓ X' = Z)
    {Y : Subgroup G} (hY : IsRootB M B Y) (hYX : Y ≤ X) : X' ⊓ QB Y ≤ Z := by
  intro w hw
  by_contra hwZ
  have hw1 : w ≠ 1 := fun h1 => hwZ (h1 ▸ Z.one_mem)
  obtain ⟨W, hW, hwW, hWX'⟩ := hX'.cover w hw.1 hwZ
  by_cases hWY : W = Y
  · have hYZ : Y ≤ Z := by
      rw [← hXX']
      exact le_inf hYX (by rwa [hWY] at hWX')
    exact hwZ (hYZ (hWY ▸ hwW))
  · have hYle : Y ≤ QB W :=
      hc.hyp.le_QB_of_mem_QB (hY.isZConjugate hc) (hW.isZConjugate hc) hwW hw1 hw.2
    have hWle : W ≤ QB Y :=
      (hc.hyp.le_QB_iff_le_QB (hW.isZConjugate hc) (hY.isZConjugate hc) hWY).mpr hYle
    have hWsat : W ≤ X := hsat Y hY hYX W hW (le_inf (hW.ctx hc).le hWle)
    have hWZ : W ≤ Z := by
      rw [← hXX']
      exact le_inf hWsat hWX'
    exact hwZ (hWZ hwW)

end CFSG.RankThree.GF2n.Stroth80
