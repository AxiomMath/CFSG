module

public import CFSG.RankThree.GF2n.Stroth80.Sec10NoFuse
public import CFSG.RankThree.GF2n.Stroth80.Sec10WidthFour
public import CFSG.RankThree.GF2n.Stroth80.Sec10Seven
public import CFSG.RankThree.GF2n.Stroth80.Sec10N35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem width_le_five_of_rootPair (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hII : ∃ y ∈ Y, y ≠ 1 ∧ ∃ z₀ ∈ Z, z₀ ≠ 1 ∧
      ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = y * z₀) : n ≤ 5 := by
  obtain ⟨y, hyY, hy1, z₀, hz₀, hz₀1, g, z, hz, hz1, hgz⟩ := hII
  have hy103 : Good103 M Q Z B y := (Good103.iff_of_mem_root h34 hspread H ht.1 hs hyY hy1).mpr ht
  have hym : SLMNat hc y 2 := (SLMNat.iff_of_mem_root h34 hspread H ht.1 hs hyY hy1).mpr hm
  obtain ⟨g₁, z₁, hz₁, hz₁1, hg₁⟩ := hy103.1.1
  obtain ⟨m, -, hmz⟩ := Smith81.Z_isConj hc.hyp hz₁ hz₁1 hz hz1
  have hfuse : ∃ c : G, c * y * c⁻¹ = y * z₀ :=
    ⟨g * m * g₁⁻¹, by rw [← hgz, ← hmz, ← hg₁]; group⟩
  have := (Good103.card_centralizer_le_of_fuse h34 h311a hspread H hy103 hz₀ hz₀1 hfuse
    hym).2.2.2
  omega

private theorem noFuse_of_not_rootPair {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G}
    (hs : Sit M Q Z Y t)
    (hI : ¬ ∃ y ∈ Y, y ≠ 1 ∧ ∃ z₀ ∈ Z, z₀ ≠ 1 ∧
      ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = y * z₀) :
    ∀ x ∈ Q, ∀ z ∈ Z, x * t * x⁻¹ = t * z → z = 1 := by
  intro x _ z hz hxz
  by_contra hz1
  obtain ⟨g₁, z₁, hz₁, hz₁1, hg₁⟩ := ht.1
  exact hI ⟨t, hs.mem, hs.ne_one, z, hz, hz1, x * g₁, z₁, hz₁, hz₁1,
    by rw [← hxz, ← hg₁]; group⟩

private theorem noFuse_swap_of_not_rootPair {t : G} {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) (Q' : Subgroup G)
    (hI : ¬ ∃ y ∈ Y, y ≠ 1 ∧ ∃ z₀ ∈ Z, z₀ ≠ 1 ∧
      ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = y * z₀) :
    ∀ x ∈ Q', ∀ y ∈ Y, x * z₀ * x⁻¹ = z₀ * y → y = 1 := by
  intro x _ y hy hxy
  by_contra hy1
  have hyz : z₀ * y = y * z₀ :=
    Subgroup.mem_centralizer_iff.mp ((smith_1_12 hs).1 hy).2 z₀ hz₀
  exact hI ⟨y, hy, hy1, z₀, hz₀, hz₀1, x, z₀, hz₀, hz₀1, by rw [hxy, hyz]⟩

private theorem Q1_swap_le_of_noFuse (hc : Ctx M Q Z B) {g : G} {Y : Subgroup G}
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (hQB : QB Y = conjSubgroup g Q)
    {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hz₀L : z₀ ∈ LB (conjSubgroup g M) (conjSubgroup g Q) B)
    (hNF' : ∀ x ∈ conjSubgroup g Q, ∀ y ∈ Y, x * z₀ * x⁻¹ = z₀ * y → y = 1) :
    Q1 hcY z₀ ≤ QB Y ⊓ M := by
  intro x hx
  obtain ⟨hxQ, hxY⟩ := (hcY.mem_Q1_iff (hcY.LB_le_M hz₀L)).mp hx
  have hcomm := hcY.mul_comm_of_noFuse hz₀L hNF' hxQ hxY
  have hxN := Tim77.mem_normalizer_of_commute_of_isTI hc.hyp.ti hz₀ hz₀1 hcomm
  refine ⟨by rw [hQB]; exact hxQ, ?_⟩
  rwa [hc.hyp.normalizer_Z.1] at hxN

private theorem width_le_five_of_noRootPair (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hI : ¬ ∃ y ∈ Y, y ≠ 1 ∧ ∃ z₀ ∈ Z, z₀ ≠ 1 ∧
      ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = y * z₀)
    (hC : Nat.card ↥(QB Y ⊓ M) ≤ Nat.card Z ^ (n + 2)) : n ≤ 5 := by
  obtain ⟨z₀, hz₀, hz₀1⟩ := Smith81.exists_ne_one_mem_Z hc.hyp
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨-, hz103, -, hz2⟩ := hswap z₀ hz₀ hz₀1
  have hQB : QB Y = conjSubgroup g Q := by rw [← hgZ]; exact QB_conj_eq hs.hyp g
  have hYZ : Nat.card Y = Nat.card Z := by rw [← hgZ]; exact card_conjSubgroup g Z
  have hz₀L := hz103.1.mem_LB
  have hle := Q1_swap_le_of_noFuse hc hcY hQB hz₀ hz₀1 hz₀L
    (noFuse_swap_of_not_rootPair hs hz₀ hz₀1 (conjSubgroup g Q) hI)
  haveI : (Y.subgroupOf (Ut (conjSubgroup g Q) Y z₀)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hcY.hyp.Z_normal.2 (hcY.hyp.Q_normal.1 (hcY.Ut_le_Q (hcY.LB_le_M hz₀L) hv)))
  have hχ := card_mul_card_of_isChiIso (hcY.isChiIso_Q1_Ut hz₀L) (fun x hx => hx.1)
    (le_sup_right : Y ≤ Ut (conjSubgroup g Q) Y z₀)
  have hU' := Good103.card_Ut_eq h34 h311a hspread H' hz103 hz2
  have hW : Nat.card ↥(conjSubgroup g Q) = Nat.card Y ^ (2 * n + 1) := H'.width
  have hQ1 : Nat.card ↥(Q1 hcY z₀) ≤ Nat.card Z ^ (n + 2) :=
    (Subgroup.card_le_of_le hle).trans hC
  rw [hU', hW, hYZ] at hχ
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have hpow : Nat.card Z ^ (2 * n + 2) ≤ Nat.card Z ^ (n + 7) := by
    calc Nat.card Z ^ (2 * n + 2) = Nat.card Z ^ (2 * n + 1) * Nat.card Z := by ring
      _ = Nat.card ↥(Q1 hcY z₀) * Nat.card Z ^ (2 * 2 + 1) := hχ
      _ ≤ Nat.card Z ^ (n + 2) * Nat.card Z ^ (2 * 2 + 1) := Nat.mul_le_mul_right _ hQ1
      _ = Nat.card Z ^ (n + 7) := by ring
  have := (Nat.pow_le_pow_iff_right hq).mp hpow
  omega

theorem Good103.width_eq_five_of_SL2 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2) : n = 5 := by
  obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht.1
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have hge : 4 ≤ n := by
    have h1 := hc.card_Ut_le H.width ht.1.mem_LB
    rw [Good103.card_Ut_eq h34 h311a hspread H ht hm] at h1
    have := (Nat.pow_le_pow_iff_right hq).mp h1
    omega
  have hne : n ≠ 4 := by
    rintro rfl
    exact Good103.not_SLMNat_two_of_width_four h34 h311a hspread H ht hm
  have hle : n ≤ 5 := by
    by_cases hII : ∃ y ∈ Y, y ≠ 1 ∧ ∃ z₀ ∈ Z, z₀ ≠ 1 ∧
        ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = y * z₀
    · exact width_le_five_of_rootPair h34 h311a hspread H ht hm hs hII
    · exact width_le_five_of_noRootPair h34 h311a hspread H ht hm hs hII
        (Good103.card_QB_inf_M_le_of_noFuse h34 h311a hspread H ht hm hs
          (noFuse_of_not_rootPair ht.1 hs hII))
  omega

theorem stroth107M2Statement_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) : Stroth107M2Statement := by
  intro G _ _ M Q Z B hc n t H ht hm
  have h5 : n = 5 := Good103.width_eq_five_of_SL2 h34 h311a hspread H ht hm
  subst h5
  exact Sec10Hyp.false_of_five h34 H

end CFSG.RankThree.GF2n.Stroth80
