module

import CFSG.RankThree.GF2n.Stroth80.Sec103Mul
public import CFSG.RankThree.GF2n.Stroth80.Sec10Swap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good101.mul_mem_Q (hc : Ctx M Q Z B) {t y : G} (ht : Good101 M Q Z B t) (hyQ : y ∈ Q)
    (hyB : y ∈ QB B) (hroot : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = t * y) :
    Good101 M Q Z B (t * y) := by
  refine ⟨hroot, M.mul_mem ht.2.1 (hc.hyp.Q_normal.1 hyQ), ?_,
    (QB B).mul_mem ht.2.2.2.1 hyB, ?_⟩
  · intro h
    apply ht.2.2.1
    have h1 : t = (t * y) * y⁻¹ := by group
    rw [h1]
    exact Q.mul_mem h (Q.inv_mem hyQ)
  · rw [Rt_mul_of_mem_Q hc hyQ]
    exact ht.2.2.2.2

theorem Good101.conjG (hc : Ctx M Q Z B) {t : G} (ht : Good101 M Q Z B t) (g : G) :
    Good101 (conjSubgroup g M) (conjSubgroup g Q) (conjSubgroup g Z) (conjSubgroup g B)
      (g * t * g⁻¹) := by
  obtain ⟨g₁, z, hz, hz1, hgt⟩ := ht.1
  refine ⟨⟨g * g₁ * g⁻¹, g * z * g⁻¹, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact mem_conjSubgroup.mpr (by
      rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
      exact hz)
  · intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group
  · rw [show g * g₁ * g⁻¹ * (g * z * g⁻¹) * (g * g₁ * g⁻¹)⁻¹ =
      g * (g₁ * z * g₁⁻¹) * g⁻¹ by group, hgt]
  · exact Subgroup.mem_map_of_mem _ ht.2.1
  · intro h
    apply ht.2.2.1
    have h' := mem_conjSubgroup.mp h
    rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h'
  · rw [QB_conj]
    exact Subgroup.mem_map_of_mem _ ht.2.2.2.1
  · rw [Smith81.LB_conj, Smith81.Rt_conj]
    intro h
    apply ht.2.2.2.2
    have h' := congrArg (conjSubgroup g⁻¹) h
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
      conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h'
    exact h'

theorem noSL2_conjG {hc : Ctx M Q Z B} (h : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2)
    (g : G) :
    ∀ s : G, Good101 (conjSubgroup g M) (conjSubgroup g Q) (conjSubgroup g Z) (conjSubgroup g B) s →
      ¬ SLMNat (hc.conjBy g) s 2 := by
  have hconj : ∀ X : Subgroup G, conjSubgroup g⁻¹ (conjSubgroup g X) = X := by
    intro X
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  intro s hs hs2
  apply h (g⁻¹ * s * g)
  · have h' := Good101.conjG (hc := hc.conjBy g) hs g⁻¹
    simpa only [hconj M, hconj Q, hconj Z, hconj B, inv_inv] using h'
  · have h' := SLMNat.conjG hs2 g⁻¹
    exact SLMNat.of_eq (by simpa only [inv_inv] using h') hc
      (hconj M) (hconj Q) (hconj Z) (hconj B)

theorem Good103.inf_QB_eq_of_mul (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t w : G} (hw : w ∈ Z)
    (ht : Good103 M Q Z B t) (htw : Good103 M Q Z B (t * w)) {Y Y' : Subgroup G}
    (hs : Sit M Q Z Y t) (hs' : Sit M Q Z Y' (t * w)) : Q ⊓ QB Y' = Q ⊓ QB Y := by
  have hle : Q ⊓ QB Y' ≤ Q ⊓ QB Y := by
    rw [← Good103.iSup_root_eq h34 hspread H htw hs']
    refine iSup_le fun C => iSup_le fun hC => iSup_le fun hCY => ?_
    have hCY' : C ≠ Y' := by
      intro h
      rw [h] at hC
      have hmem : t * w ∈ Y' ⊓ Q := ⟨hs'.mem, hC.le hs'.mem⟩
      rw [hs'.X_inf_Q, Subgroup.mem_bot] at hmem
      exact hs'.ne_one hmem
    have hY'QB : Y' ≤ QB C :=
      hc.hyp.le_QB_of_le_QB hC.conj hs'.conj hCY' hCY
    have hZQB : Z ≤ QB C :=
      hc.hyp.le_QB_of_le_QB hC.conj ⟨1, (conjSubgroup_one Z).symm⟩ hC.ne
        (by rw [hc.hyp.QB_Z]; exact hC.le)
    have htQB : t ∈ QB C := by
      have h1 : t * w ∈ QB C := hY'QB hs'.mem
      have h2 := (QB C).mul_mem h1 ((QB C).inv_mem (hZQB hw))
      rwa [mul_inv_cancel_right] at h2
    exact le_inf hC.le (hc.hyp.le_QB_of_mem_QB hC.conj hs.conj hs.mem hs.ne_one htQB)
  obtain ⟨m, -, hm⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  have hm' : SLMNat hc (t * w) m := (SLMNat.mul_of_mem_Q (hc := hc) (hc.Z_le_Q hw)).mpr hm
  have hcard : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ m :=
    Good103.card_inf_QB_eq_pow hc ht hs (SLMNat.card_Vt hm)
  have hcard' : Nat.card ↥(Q ⊓ QB Y') = Nat.card Z ^ m :=
    Good103.card_inf_QB_eq_pow hc htw hs' (SLMNat.card_Vt hm')
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcard.trans hcard'.symm))

private theorem good103_partner_frame (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t z₀ : G} (ht : Good103 M Q Z B t) (hz₀ : z₀ ∈ Z)
    (hfuse : ∃ g : G, g * t * g⁻¹ = t * z₀) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ∃ Y' : Subgroup G, Sit M Q Z Y' (t * z₀) ∧ Good103 M Q Z B (t * z₀) ∧
      Q ⊓ QB Y' = Q ⊓ QB Y := by
  have hroot : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = t * z₀ := by
    obtain ⟨c, hc'⟩ := hfuse
    obtain ⟨g₁, z, hz, hz1, hgz⟩ := ht.1.1
    exact ⟨c * g₁, z, hz, hz1, by
      rw [show c * g₁ * z * (c * g₁)⁻¹ = c * (g₁ * z * g₁⁻¹) * c⁻¹ from by group, hgz, hc']⟩
  have h101 : Good101 M Q Z B (t * z₀) :=
    Good101.mul_mem_Q hc ht.1 (hc.Z_le_Q hz₀) ((Ctx.Z_le_QB hc).1 hz₀) hroot
  have h103 : Good103 M Q Z B (t * z₀) :=
    Good103.mul_of_mem_Z h34 h311a hspread H ht hz₀ h101
  obtain ⟨Y', hs'⟩ := Good101.exists_sit hc h101
  exact ⟨Y', hs', h103, Good103.inf_QB_eq_of_mul h34 hspread H hz₀ ht h103 hs hs'⟩

private theorem good101_mul_zpow_swap (hc : Ctx M Q Z B) {g t z₀ : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B)
    (hz103 : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z₀)
    (ht : Good101 M Q Z B t) (hz₀ : z₀ ∈ Z)
    (hfuse : ∃ c : G, c * t * c⁻¹ = t * z₀) :
    Good101 (conjSubgroup g M) (conjSubgroup g Q) Y B (z₀ * t) := by
  have h12 := smith_1_12 hs
  have htz : t * z₀ = z₀ * t :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h12.1 hs.mem)).2 z₀ hz₀).symm
  have hroot : ∃ c : G, ∃ z ∈ Y, z ≠ 1 ∧ c * z * c⁻¹ = z₀ * t := by
    obtain ⟨c, hc'⟩ := hfuse
    exact ⟨c, t, hs.mem, hs.ne_one, by rw [hc', htz]⟩
  have htZ : t ∈ conjSubgroup g Z := by
    rw [hgZ]
    exact hs.mem
  exact Good101.mul_mem_Q hcY hz103.1 (Subgroup.map_mono hc.Z_le_Q htZ)
    ht.2.2.2.1 hroot

theorem Good103.swap_partner (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) (hc : Ctx M Q Z B) {g t z₀ : G} {Y : Subgroup G}
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B)
    {n : ℕ} (H' : Sec10Hyp hcY n)
    (ht : Good101 M Q Z B t) (hs : Sit M Q Z Y t) (hz₀ : z₀ ∈ Z)
    (hfuse : ∃ c : G, c * t * c⁻¹ = t * z₀) (hgZ : conjSubgroup g Z = Y)
    (hz103 : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z₀) :
    Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B (z₀ * t) := by
  have h101 := good101_mul_zpow_swap hc hs hgZ hcY hz103 ht hz₀ hfuse
  exact Good103.mul_of_mem_Z h34 h311a hspread H' hz103 hs.mem h101

theorem Sit.swap_partner {hc : Ctx M Q Z B} {t z₀ : G} {Y Y' : Subgroup G} {g : G}
    (hs : Sit M Q Z Y t) (hs' : Sit M Q Z Y' (t * z₀)) (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    Sit (conjSubgroup g M) (conjSubgroup g Q) Y Y' (z₀ * t) := by
  have h12 := smith_1_12 hs
  have htz : t * z₀ = z₀ * t :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h12.1 hs.mem)).2 z₀ hz₀).symm
  refine ⟨hcY.hyp, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h', hY'⟩ := hs'.conj
    refine ⟨h' * g⁻¹, ?_⟩
    rw [conjSubgroup_mul, show conjSubgroup g⁻¹ Y = Z by
      rw [← hgZ, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one], ← hY']
  · rw [← htz]
    exact hs'.mem
  · intro h
    have hzY : z₀ ∈ Y := by
      have h1 : z₀ = (z₀ * t) * t⁻¹ := by group
      rw [h1, h]
      simpa using Y.inv_mem hs.mem
    have hmem : z₀ ∈ Z ⊓ Y := ⟨hz₀, hzY⟩
    rw [hs.Z_inf_X, Subgroup.mem_bot] at hmem
    exact hz₀1 hmem
  · rw [← Smith81.normalizer_conj_eq hs.hyp g, hgZ]
    refine (Subgroup.normalizer (Y : Set G)).mul_mem ?_ (Subgroup.le_normalizer hs.mem)
    exact Subgroup.centralizer_le_normalizer (Y : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h12.1 hy)).2 z₀ hz₀).symm)
  · have hQY : conjSubgroup g Q = QB Y := by rw [← QB_conj_eq hs.hyp g, hgZ]
    rw [hQY]
    intro h
    have hYQBY : Y ≤ QB Y := by
      obtain ⟨k, hk, hQB, -⟩ := hs.QB_eq
      rw [hQB, hk]
      exact Subgroup.map_mono hc.Z_le_Q
    have hzQBY : z₀ ∈ QB Y := by
      have h1 : z₀ = (z₀ * t) * t⁻¹ := by group
      rw [h1]
      exact (QB Y).mul_mem h ((QB Y).inv_mem (hYQBY hs.mem))
    have hmem : z₀ ∈ Z ⊓ QB Y := ⟨hz₀, hzQBY⟩
    rw [Smith81.Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at hmem
    exact hz₀1 hmem

private theorem inf_QB_partner_swap (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {g t z₀ : G} {Y Y' : Subgroup G}
    {n : ℕ} {hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B} (H' : Sec10Hyp hcY n)
    (hgZ : conjSubgroup g Z = Y)
    (hz103 : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z₀)
    (h103 : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B (z₀ * t))
    (hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z₀)
    (hsit : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Y' (z₀ * t))
    (hs : Sit M Q Z Y t) :
    QB Y ⊓ QB Y' = QB Y ⊓ Q := by
  have hQY : conjSubgroup g Q = QB Y := by rw [← QB_conj_eq hs.hyp g, hgZ]
  have h := Good103.inf_QB_eq_of_mul h34 hspread H' hs.mem hz103 h103 hsz hsit
  rwa [hQY, hc.hyp.QB_Z] at h

theorem Good103.partner (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t z₀ : G} (ht : Good103 M Q Z B t) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hfuse : ∃ g : G, g * t * g⁻¹ = t * z₀) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    ∃ Y' : Subgroup G, Sit M Q Z Y' (t * z₀) ∧ Good103 M Q Z B (t * z₀) ∧
      Q ⊓ QB Y' = Q ⊓ QB Y ∧ QB Y ⊓ QB Y' = QB Y ⊓ Q := by
  obtain ⟨Y', hs', h103, ha⟩ :=
    good103_partner_frame h34 h311a hspread H ht hz₀ hfuse hs
  obtain ⟨m, -, hm⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨hsz, hz103, -, -⟩ := hswap z₀ hz₀ hz₀1
  have h103'' : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B (z₀ * t) :=
    Good103.swap_partner h34 h311a hspread hc hcY H' ht.1 hs hz₀ hfuse hgZ hz103
  have hsit : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Y' (z₀ * t) :=
    Sit.swap_partner (hc := hc) hs hs' hgZ hcY hz₀ hz₀1
  exact ⟨Y', hs', h103, ha,
    inf_QB_partner_swap (hc := hc) h34 hspread H' hgZ hz103 h103'' hsz hsit hs⟩

end CFSG.RankThree.GF2n.Stroth80
