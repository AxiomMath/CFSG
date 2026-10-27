module

public import CFSG.RankThree.GF2n.Smith81.ETables
public import CFSG.RankThree.GF2n.Stroth80.Sec10Commute
public import CFSG.RankThree.GF2n.Stroth80.Sec10LBInf
public import CFSG.RankThree.GF2n.Stroth80.Sec10Second
public import CFSG.RankThree.GF2n.Stroth80.Sec10Transv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Good103.le_QB_of_le_Vt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) {A : Subgroup G}
    (hA : ∃ g : G, A = conjSubgroup g Z) (hAB : A ≠ B)
    (hAV : A ≤ Vt M (LB M Q B) B Z t) : B ≤ QB A := by
  obtain ⟨m, hm2, hm⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  have h5 : Sec5Hyp hc n t := H.toSec5 ht.1.mem_LB ht.1.2.2.1
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    (stroth310SL_of_34 h34) G M Q Z B hc n t h5 (SLMNat.toSLNat hm hm2)
  exact hc.hyp.le_QB_of_le_QB hA hc.conj hAB (hAV.trans hVQB)

private theorem eq_six_eq_three {q n m : ℕ} (hq : 1 < q) (hm3 : 3 ≤ m) (h2m : 2 * m ≤ n)
    (h : q ^ (n - 1) ≤ q ^ (m + 2)) : n = 6 ∧ m = 3 := by
  have h' : n - 1 ≤ m + 2 := (Nat.pow_le_pow_iff_right hq).mp h
  omega

theorem Good103.card_LB_inf_LB_le_of_second_root (h34 : Stroth34Statement)
    {hc : Ctx M Q Z B} {A : Subgroup G} (hcA : Ctx M Q Z A) {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) (htA : t ∈ QB A)
    (hCQt : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1))
    (hAex : ∃ h : G, A = conjSubgroup h Z) (hAV : A ≤ Vt M (LB M Q B) B Z t)
    (hne : A ≠ B) (hAB : (A ⊔ Z) ⊓ (B ⊔ Z) = Z)
    (hQB : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    (hQBA : Nat.card ↥(Q ⊓ QB A) = Nat.card Z ^ (n + 1)) :
    Nat.card ↥(LB M Q A ⊓ LB M Q B) ≤ Nat.card Z ^ 2 * Nat.card Q := by
  have hXcard := Ctx.card_inf_QB_inf_QB_centralizer hc hcA ht.1.2.2.2.1 htA
    (le_of_eq hQB.symm) (le_of_eq hQBA.symm) hCQt
  let X : Subgroup G := Q ⊓ QB A ⊓ QB B
  have hYX : Nat.card ↥(Q ⊓ QB A ⊓ QB B ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card ↥X :=
    Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hX : Nat.card Z ^ (n + 1) ≤ Nat.card Z ^ 2 * Nat.card ↥X :=
    hXcard.trans (Nat.mul_le_mul_left _ hYX)
  have hBQA : B ≤ QB A := Good103.le_QB_of_le_Vt h34 H ht hAex hne hAV
  exact Ctx.card_LB_inf_LB_le hc hcA H.width (le_inf (le_inf hc.le hBQA) hc.B_le_QB)
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right hX hAB
    (le_of_eq hQB.symm)

private theorem card_LB_inf_CN_le (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t z₀ : G}
    (ht : Good103 M Q Z B t) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    (hfuse : ∃ g : G, g * t * g⁻¹ = t * z₀) {m : ℕ} (hm : SLMNat hc t m) (hm3 : 3 ≤ m)
    (hCQt : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card Z ^ (n + 1)) :
    Nat.card ↥(LB M Q B ⊓ hc.CN t) ≤ Nat.card Z ^ 3 * Nat.card Q := by
  obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht.1
  have hV : Nat.card Z ^ 2 < Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    rw [SLMNat.card_Vt hm]
    exact Nat.pow_lt_pow_right (by have := hc.hyp.q4; omega) (by omega)
  obtain ⟨g, hgM, hAle, hne, -, htA, hAZBZ⟩ :=
    Good103.exists_conj_le_inf (hc := hc) ht hs hV
  set A : Subgroup G := conjSubgroup g B with hAdef
  have hcA : Ctx M Q Z A := hc.conj_of_mem hgM
  have HA : Sec10Hyp hcA n := H.conj_of_mem hgM
  have htAg : Good103 M Q Z A t := Good103.conj_of_mem hc ht hgM htA
  have hCNle := Good103.card_CN_le_of_fuse h34 h311a hspread HA htAg hz₀ hz₀1 hfuse
  have hCNeq : hcA.CN t = hc.CN t := Ctx.CN_conj_eq hc hgM t
  rw [hCNeq] at hCNle
  have h1 := card_inf_le_mul_card_inf_inf (L₁ := LB M Q B) (L₂ := LB M Q A)
    (N := hc.CN t) (c := Nat.card Z) hCNle
  have hLBinfN : Nat.card ↥(LB M Q B ⊓ hc.CN t) ≤
      Nat.card Z * Nat.card ↥(LB M Q A ⊓ LB M Q B) := by
    refine h1.trans (Nat.mul_le_mul_left _ ?_)
    rw [inf_comm (LB M Q A) (LB M Q B)]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hQB := (card_LB_of_ctx h34 hc H.width H.n_gt H.noA2 H.gen).2
  have hQBA := (card_LB_of_ctx h34 hcA HA.width HA.n_gt HA.noA2 HA.gen).2
  obtain ⟨gB, hgB⟩ := hc.conj
  have hAex : ∃ h : G, A = conjSubgroup h Z :=
    ⟨g * gB, by rw [hAdef, hgB, conjSubgroup_mul]⟩
  have hAV : A ≤ Vt M (LB M Q B) B Z t := by
    rw [Good103.Vt_eq ht hs]
    simpa only [hAdef] using hAle.trans le_sup_left
  have h3 := Good103.card_LB_inf_LB_le_of_second_root h34 hcA H ht htA hCQt hAex hAV
    (by simpa only [hAdef] using hne) (by simpa only [hAdef] using hAZBZ) hQB hQBA
  calc Nat.card ↥(LB M Q B ⊓ hc.CN t)
      ≤ Nat.card Z * Nat.card ↥(LB M Q A ⊓ LB M Q B) := hLBinfN
    _ ≤ Nat.card Z * (Nat.card Z ^ 2 * Nat.card Q) := Nat.mul_le_mul_left _ h3
    _ = Nat.card Z ^ 3 * Nat.card Q := by ring

theorem stroth_10_6b (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec10Hyp hc n → (∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2) → Good103 M Q Z B t →
        (∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * t * g⁻¹ = t * z) → n = 6 ∧ SLMNat hc t 3 := by
  intro G _ _ M Q Z B hc n t H hge3 ht hfuse
  obtain ⟨g₀, z₀, hz₀, hz₀1, hfuse⟩ := hfuse
  obtain ⟨m, hm2, hm⟩ := SLlike.exists_SLMNat (H.slLike ht.1)
  have hm3 : 3 ≤ m := by
    by_contra h
    have hm_eq : m = 2 := by omega
    exact hge3 t ht.1 (hm_eq ▸ hm)
  obtain ⟨hCQt, -, h2m, -⟩ :=
    Good103.card_centralizer_le_of_fuse h34 h311a hspread H ht hz₀ hz₀1
      ⟨g₀, hfuse⟩ hm
  have hbound := card_LB_inf_CN_le h34 h311a hspread H ht hz₀ hz₀1
    ⟨g₀, hfuse⟩ hm hm3 hCQt
  have hLBcard := (card_LB_of_ctx h34 hc H.width H.n_gt H.noA2 H.gen).1
  have hLBle := Sec10Hyp.card_LB_le_mul_card_LB_inf_CN h34 H ht.1 hm
  have hmain : Nat.card Q * Nat.card Z ^ (n - 1) ≤
      Nat.card Z ^ (m + 2) * Nat.card Q := by
    rw [← hLBcard]
    calc Nat.card ↥(LB M Q B)
        ≤ Nat.card Z ^ (m - 1) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := hLBle
      _ ≤ Nat.card Z ^ (m - 1) * (Nat.card Z ^ 3 * Nat.card Q) :=
          Nat.mul_le_mul_left _ hbound
      _ = Nat.card Z ^ (m + 2) * Nat.card Q := by
          rw [show Nat.card Z ^ (m - 1) * (Nat.card Z ^ 3 * Nat.card Q) =
              (Nat.card Z ^ (m - 1) * Nat.card Z ^ 3) * Nat.card Q by ring,
            ← pow_add, show m - 1 + 3 = m + 2 by omega]
  have hineq : Nat.card Z ^ (n - 1) ≤ Nat.card Z ^ (m + 2) := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := ↥Q))
    calc Nat.card Z ^ (n - 1) * Nat.card Q =
        Nat.card Q * Nat.card Z ^ (n - 1) := by ring
      _ ≤ Nat.card Z ^ (m + 2) * Nat.card Q := hmain
  obtain ⟨hn, hm_eq⟩ := eq_six_eq_three (by have := hc.hyp.q4; omega) hm3 h2m hineq
  exact ⟨hn, hm_eq ▸ hm⟩

theorem Good103.no_fuse_of_noSL2 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) (hge3 : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2)
    {t : G} (ht : Good103 M Q Z B t) : ∀ y ∈ Q, ∀ z ∈ Z, y * t * y⁻¹ = t * z → z = 1 := by
  intro y hyQ z hz hconj
  by_cases hz1 : z = 1
  · exact hz1
  · obtain ⟨hn, hm3⟩ := (stroth_10_6b h34 h311a hspread) G M Q Z B hc n t H hge3 ht
      ⟨y, z, hz, hz1, hconj⟩
    have hU : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (n + 1) := by
      rw [Good103.card_Ut_eq h34 h311a hspread H ht hm3, hn]
    obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht.1
    have ht2 : t ^ 2 = 1 := by
      rw [sq]
      exact hs.x_sq
    have hUC : Ut Q Z t ≤ Subgroup.centralizer ({t} : Set G) :=
      Ctx.Ut_le_centralizer h34 hc (H.toSec5 ht.1.mem_LB ht.1.2.2.1)
        (SLMNat.toSLNat hm3 (by norm_num)) ht2
    exact Ctx.no_fuse_of_card_Ut hc H.width ht.1.mem_LB hU hUC y hyQ z hz hconj

end CFSG.RankThree.GF2n.Stroth80
