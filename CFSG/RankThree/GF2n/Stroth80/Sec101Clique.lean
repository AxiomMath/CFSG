module

public import CFSG.RankThree.GF2n.Stroth80.Sec101SLVec

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem IsClique101.le_of_roots {X Y : Subgroup G} (hX : IsClique101 M Q Z B X) (hZY : Z ≤ Y)
    (h : ∀ E, IsRootB M B E → E ≤ X → E ≤ Y) : X ≤ Y := by
  intro x hx
  by_cases hxZ : x ∈ Z
  · exact hZY hxZ
  · obtain ⟨E, hE, hxE, hEX⟩ := hX.cover x hx hxZ
    exact h E hE hEX hxE

theorem IsClique101.conj (hc : Ctx M Q Z B) {X : Subgroup G} (hX : IsClique101 M Q Z B X)
    {g : G} (hg : g ∈ M) : IsClique101 M Q Z B (conjSubgroup g X) where
  Z_le := by
    rw [← hc.conj_Z_eq hg]
    exact Subgroup.map_mono hX.Z_le
  le_Q := by
    calc conjSubgroup g X ≤ conjSubgroup g Q := Subgroup.map_mono hX.le_Q
      _ = Q := hc.conj_Q_eq hg
  cover := by
    intro y hy hyZ
    have hxX : g⁻¹ * y * g ∈ X := mem_conjSubgroup.mp hy
    have hxZ : g⁻¹ * y * g ∉ Z := by
      intro hxZ
      apply hyZ
      have h1 : y ∈ conjSubgroup g Z := mem_conjSubgroup.mpr hxZ
      rwa [hc.conj_Z_eq hg] at h1
    obtain ⟨E, hE, hxE, hEX⟩ := hX.cover _ hxX hxZ
    exact ⟨conjSubgroup g E, hE.conj hg, mem_conjSubgroup.mpr hxE, Subgroup.map_mono hEX⟩
  le_QB := by
    intro E' hE' hE'X
    have hE : IsRootB M B (conjSubgroup g⁻¹ E') := hE'.conj (M.inv_mem hg)
    have hEX : conjSubgroup g⁻¹ E' ≤ X := by
      intro e he
      have he' : g * e * g⁻¹ ∈ E' := by simpa using mem_conjSubgroup.mp he
      have h1 := hE'X he'
      rw [mem_conjSubgroup] at h1
      rwa [show g⁻¹ * (g * e * g⁻¹) * g = e by group] at h1
    have h1 : X ≤ QB (conjSubgroup g⁻¹ E') := hX.le_QB _ hE hEX
    have h2 : conjSubgroup g X ≤ conjSubgroup g (QB (conjSubgroup g⁻¹ E')) :=
      Subgroup.map_mono h1
    have h3 : conjSubgroup g (QB (conjSubgroup g⁻¹ E')) = QB E' := by
      rw [← QB_conj g (conjSubgroup g⁻¹ E')]
      congr 1
      rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    rwa [h3] at h2

theorem IsMaxClique101.conj (hc : Ctx M Q Z B) {X : Subgroup G} (hX : IsMaxClique101 M Q Z B X)
    {g : G} (hg : g ∈ M) : IsMaxClique101 M Q Z B (conjSubgroup g X) := by
  refine ⟨hX.1.conj hc hg, fun Y hY => ?_⟩
  have hY' : Nat.card (conjSubgroup g⁻¹ Y) ≤ Nat.card X :=
    hX.2 _ (hY.conj hc (M.inv_mem hg))
  rw [card_conjSubgroup g X]
  calc Nat.card Y = Nat.card (conjSubgroup g⁻¹ Y) := (card_conjSubgroup g⁻¹ Y).symm
    _ ≤ Nat.card X := hY'

theorem Ctx.isClique101_sup (hc : Ctx M Q Z B) : IsClique101 M Q Z B (B ⊔ Z) where
  Z_le := le_sup_right
  le_Q := sup_le hc.le hc.Z_le_Q
  cover := by
    intro x hx hxZ
    obtain ⟨p, hp, hxp⟩ := hc.exists_mem_conj_of_mem_sup hx hxZ
    refine ⟨conjSubgroup p B, ⟨p, hc.hyp.Q_normal.1 hp, rfl⟩, hxp, ?_⟩
    calc conjSubgroup p B ≤ conjSubgroup p (B ⊔ Z) := Subgroup.map_mono le_sup_left
      _ = B ⊔ Z := hc.conj_sup_Z_of_mem_Q hp
  le_QB := by
    intro E hE hEX
    obtain ⟨p, hp, hpE⟩ := hc.exists_conj_of_le_ZB (hE.ctx hc) (by
      rwa [sup_comm] at hEX)
    calc B ⊔ Z = conjSubgroup p (B ⊔ Z) := (hc.conj_sup_Z_of_mem_Q hp).symm
      _ ≤ conjSubgroup p (QB B) :=
        Subgroup.map_mono (sup_le (Ctx.B_le_QB hc) (Ctx.Z_le_QB hc).1)
      _ = QB (conjSubgroup p B) := (QB_conj p B).symm
      _ = QB E := by rw [hpE]

theorem Sec10Hyp.isClique101_Vt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q) (hsl : SLlike hc t) :
    IsClique101 M Q Z B (Vt M (LB M Q B) B Z t) where
  Z_le := sec39_Z_le_Vt
  le_Q := hc.Vt_le_Q t
  cover := by
    intro v hv hvZ
    obtain ⟨r, hrR, hrv⟩ := hsl.exists_mem_conj_sup ht hv hvZ
    obtain ⟨p, hpQ, hpv⟩ :=
      (hc.conj_of_mem (hc.Rt_le_M t hrR)).exists_mem_conj_of_mem_sup hrv hvZ
    have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
    have hrM : r ∈ M := hc.Rt_le_M t hrR
    have hprR : p * r ∈ Rt M (LB M Q B) t :=
      (Rt M (LB M Q B) t).mul_mem (hc.Q_le_Rt ht hpQ) hrR
    refine ⟨conjSubgroup (p * r) B, ⟨p * r, M.mul_mem hpM hrM, rfl⟩, ?_,
      (le_sup_left.trans (hc.conj_Rt_le_Vt ht hprR))⟩
    rwa [conjSubgroup_mul]
  le_QB := by
    intro E hE hEV
    obtain ⟨r, hrR, hrE⟩ := hsl.exists_eq_conj_of_le_Vt ht hE hEV
    have hSL : SLNat hc t := by
      obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
      exact hslm.toSLNat hm2
    have hVinf : Vt M (LB M Q B) B Z t ≤ Q ⊓ QB B :=
      hc.Vt_le_inf_QB_of_SLNat (H.toSec5 ht htQ)
        (stroth_3_5 h34 hc H.width H.n_gt H.noA2 H.gen).2.1 hSL
    have hVr : Vt M (LB M Q B) B Z t ≤ conjSubgroup r (QB B) :=
      calc Vt M (LB M Q B) B Z t = conjSubgroup r (Vt M (LB M Q B) B Z t) :=
            (conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hrR)).symm
        _ ≤ conjSubgroup r (QB B) := Subgroup.map_mono (hVinf.trans inf_le_right)
    rw [hrE, QB_conj]
    exact hVr

private theorem IsMaxClique101.exists_not_le_Z (hc : Ctx M Q Z B) {X : Subgroup G}
    (hX : IsMaxClique101 M Q Z B X) : ∃ x, x ∈ X ∧ x ∉ Z := by
  have hBZle : Nat.card ↥(B ⊔ Z : Subgroup G) ≤ Nat.card X := hX.2 _ hc.isClique101_sup
  have hBcard : Nat.card B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hZgt : Nat.card Z < Nat.card ↥(B ⊔ Z : Subgroup G) := by
    rw [hc.card_sup_Z, hBcard]
    exact lt_mul_of_one_lt_left (by have := hc.hyp.q4; omega)
      (by have := hc.hyp.q4; omega)
  have hXnotZ : ¬ X ≤ Z := by
    intro hXZ
    have hleZ : Nat.card X ≤ Nat.card Z :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hXZ) (Subgroup.inclusion_injective hXZ)
    omega
  by_contra h
  apply hXnotZ
  intro x hx
  by_contra hxZ
  exact h ⟨x, hx, hxZ⟩

theorem Ctx.exists_maxClique (hc : Ctx M Q Z B) :
    ∃ X, IsMaxClique101 M Q Z B X ∧ B ≤ X := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {X | IsClique101 M Q Z B X}
  have hSne : S.Nonempty := ⟨B ⊔ Z, hc.isClique101_sup⟩
  have hSfin : S.Finite := Set.finite_univ.subset (Set.subset_univ S)
  obtain ⟨X, hXS, hXmax⟩ :=
    Set.Finite.exists_maximalFor (fun X : Subgroup G => Nat.card X) S hSfin hSne
  have hXcl : IsClique101 M Q Z B X := hXS
  have hXc : IsMaxClique101 M Q Z B X := ⟨hXcl, fun Y hY => by
    rcases le_total (Nat.card Y) (Nat.card X) with h | h
    · exact h
    · exact hXmax hY h⟩
  obtain ⟨x, hxX, hxZ⟩ := hXc.exists_not_le_Z hc
  obtain ⟨E, hE, hxE, hEX⟩ := hXcl.cover x hxX hxZ
  obtain ⟨m, hm, hEm⟩ := hE
  refine ⟨conjSubgroup m⁻¹ X, hXc.conj hc (M.inv_mem hm), ?_⟩
  calc B = conjSubgroup m⁻¹ (conjSubgroup m B) := by
        rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    _ = conjSubgroup m⁻¹ E := by rw [hEm]
    _ ≤ conjSubgroup m⁻¹ X := Subgroup.map_mono hEX

theorem IsMaxClique101.card_ge (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {X : Subgroup G} (hX : IsMaxClique101 M Q Z B X) :
    Nat.card Z ^ 3 ≤ Nat.card X := by
  obtain ⟨t, ht, htQ, hsl⟩ := H.ex
  obtain ⟨m, hm2, hslm⟩ := hsl.exists_SLMNat
  have hV : IsClique101 M Q Z B (Vt M (LB M Q B) B Z t) :=
    H.isClique101_Vt h34 ht htQ hsl
  have hle : Nat.card (Vt M (LB M Q B) B Z t) ≤ Nat.card X := hX.2 _ hV
  rw [SLMNat.card_Vt hslm] at hle
  calc Nat.card Z ^ 3 ≤ Nat.card Z ^ (m + 1) :=
        Nat.pow_le_pow_right (by have := hc.hyp.q4; omega) (by omega)
    _ ≤ Nat.card X := hle

end CFSG.RankThree.GF2n.Stroth80
