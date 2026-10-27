module

public import CFSG.RankThree.GF2n.Stroth80.Sec53cVone

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec53b_prod_of_vone_eq (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t r : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hE : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) :
    ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ a ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t),
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t), x = a * b := by
  have hq : 0 < Nat.card Z := Nat.card_pos
  obtain ⟨hAc, hCc⟩ := Ctx.card_QB_inf_Wt_pair h34 hRoot hc hs hm hV hr
  have hV3 := card_Vt_inf_QB_inf_QB_sp h34 hRoot hc hs hm hV hr hplane
  have hY : Nat.card ↥((Vt M (LB M Q B) B Z t ⊓ QB B) ⊓
      (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B))) = Nat.card Z ^ (2 * m - 1) := by
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * m + 1)) ?_
    rw [hV3, ← pow_add, ← pow_add]
    congr 1
    omega
  have hle : (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ≤
      (Vt M (LB M Q B) B Z t ⊓ QB B) ⊓
        (Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B)) := by
    intro y hy
    have hyV : y ∈ Vt M (LB M Q B) B Z t := by
      rw [← hE]
      exact inf_QB_inf_QB_le_vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)
        ⟨⟨hy.1.1, hy.2.1⟩, (inf_le_left : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q) hy.1.2⟩
    exact ⟨⟨hyV, hy.1.1⟩, ⟨hyV, hy.2.1⟩⟩
  have hI : Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊓
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))) ≤ Nat.card Z ^ (2 * m - 1) :=
    hY ▸ Subgroup.card_le_of_le hle
  have hQ : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have hDc : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ (2 * m - 1) =
      Nat.card Z ^ (2 * n) := by
    have h := hc.card_Wt_mul_card_Vt t
    rw [SpMNat.card_V hV, hQ] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hq 2) ?_
    calc Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ (2 * m - 1) * Nat.card Z ^ 2
        = Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ (2 * m + 1) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
      _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z := h
      _ = Nat.card Z ^ (2 * n) * Nat.card Z ^ 2 := by ring
  exact exists_mul_of_card_eq_pow inf_le_right inf_le_right hAc hCc hI hDc


theorem vone_ne_of_odd (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement)
    (hOdd : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t → Odd n)
    (hfixB : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
    (hfixC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t →
        ∀ x ∈ Sec8W1 M Q Z B t r,
          (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
            x ∈ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane hE
  have hrM : r ∈ M := hc.Rt_le_M t hr
  obtain ⟨K, fK, finK, hK, m, hm, φ, u, u', hφ, hker, hact, huu', hL, hL'⟩ :=
    sec5NatPointsSp_of h34 hRoot G M Q Z B hc n t hs hsp r hr hplane
  letI := fK
  letI := finK
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hV : SpMNat hc t m := ⟨K, fK, finK, hK, φ, hφ, hker, hact⟩
  have hsp' : SpNat hc t := ⟨K, fK, finK, hK, m, hm, φ, hφ, hker, hact⟩
  have hV1 : Sec8V1 M Q Z B t r = Vt M (LB M Q B) B Z t := hE
  have hW1 : Sec8W1 M Q Z B t r = Wt Q (Vt M (LB M Q B) B Z t) := by
    unfold Sec8W1
    rw [hV1]
  have hprod : ∀ x ∈ Sec8W1 M Q Z B t r,
      ∃ a ∈ QB B ⊓ Sec8W1 M Q Z B t r,
      ∃ b ∈ QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r, x = a * b := by
    rw [hW1]
    exact sec53b_prod_of_vone_eq h34 hRoot hc hs hm hV hr hplane hE
  have hcomm : ⁅Sec8W1 M Q Z B t r, hc.CN t⁆ ≤ Sec8V1 M Q Z B t r :=
    sec53b_comm_of_51 h51 hc hs hsp' hr hplane hprod (sec53b_hboxB hc hs hr)
      (sec53b_hboxC hc hs hr)
  have hsupW : Sec8W1 M Q Z B t r ≤
      ((QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) ⊔
        ((QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) := by
    refine hc.hsupW_of_prod ?_
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    exact Subgroup.mul_mem_sup ha hb
  have hd := hc.isOppDecomp_of_components hs hr
    (stroth53VW_holds h34 hRoot h51 G M Q Z B hc n t hs hsp' r hr hplane) hsupW
    (stroth53Inf_holds G M Q Z B hc n t hs hsp' r hr hplane)
    (hfixB G M Q Z B hc n t hs hsp' r hr hplane hE)
    (hfixC G M Q Z B hc n t hs hsp' r hr hplane hE)
  have hLeR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'eR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hr
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hL'
  have hWinv : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8W1 M Q Z B t r,
      ρ * x * ρ⁻¹ ∈ Sec8W1 M Q Z B t r := by
    intro ρ hρ x hx
    rw [hW1] at hx ⊢
    exact conj_mem_Wt (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ))
      (hc.Rt_normalizes_Vt hs.mem hρ) hx
  have hVinv : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8V1 M Q Z B t r,
      ρ * x * ρ⁻¹ ∈ Sec8V1 M Q Z B t r := by
    intro ρ hρ x hx
    rw [hV1] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt hs.mem hρ) x).mp hx
  have hN : ∀ s ∈ hc.CN t, ∀ y ∈ Sec8W1 M Q Z B t r, ⁅s, y⁆ ∈ Sec8V1 M Q Z B t r := by
    intro s hsN y hy
    rw [← commutatorElement_inv]
    exact (Sec8V1 M Q Z B t r).inv_mem ((Subgroup.commutator_le.mp hcomm) y hy s hsN)
  obtain ⟨a, ha⟩ := stroth_2_1_ii_secSp (m := m) (by omega) φ hφ hker hWinv hVinv hN hd hLeR
    hL'eR huu' hL hL2
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hQ : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  have hVc : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) :=
    SpMNat.card_V hV
  have hWV := hc.card_Wt_mul_card_Vt t
  rw [hW1, hV1, hK] at ha
  rw [hVc, hQ] at hWV
  rw [hVc] at ha
  have hexp : Nat.card Z ^ (4 * m + 2 + 2 ^ m * a) = Nat.card Z ^ (2 * n + 2) := by
    calc Nat.card Z ^ (4 * m + 2 + 2 ^ m * a)
        = (Nat.card Z ^ (2 * m + 1) * Nat.card Z ^ (2 ^ m * a)) * Nat.card Z ^ (2 * m + 1) := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
      _ = Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ (2 * m + 1) := by rw [← ha]
      _ = Nat.card Z ^ (2 * n + 1) * Nat.card Z := hWV
      _ = Nat.card Z ^ (2 * n + 2) := by rw [← pow_succ]
  have h2 := Nat.pow_right_injective hq2 hexp
  have h4 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  obtain ⟨j, hj⟩ := hOdd G M Q Z B hc n t hs hsp' r hr hplane
  rw [h4] at h2
  have h5 : 4 * 2 ^ (m - 2) * a = 4 * (2 ^ (m - 2) * a) := by ring
  rw [h5] at h2
  omega

end CFSG.RankThree.GF2n.Stroth80
