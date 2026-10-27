module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CritB2

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_five_stab (F : Frame L1 L2 S D X) {p : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hp : vtype p = false) : ∃ e ∈ stab p, e ∉ Qv p ∧ e ^ 5 = 1 := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_stab_false (L1 := L1) (L2 := L2) (S := S) hp
  obtain ⟨x0, hx0, hx05, hx01, -⟩ := F.exists_gen
  have hxP : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  refine ⟨g⁻¹ * x0 * g, ?_, ?_, ?_⟩
  · have : x0 ∈ conjSub g (stab p) := by rw [hg1]; exact hxP
    exact mem_conjSub.mp this
  · intro h
    have hQ : x0 ∈ conjSub g (Qv p) := mem_conjSub.mpr h
    rw [hg2] at hQ
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (P1 L1 L2 S)) ⟨x0, hQ⟩
    have hk' : x0 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hgcd : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk', hx05⟩
    rw [hgcd, pow_one] at this
    exact hx01 this
  · have := conj_pow (a := g⁻¹) (b := x0) (i := 5)
    rw [inv_inv] at this
    rw [this, hx05]
    group

theorem Zv_ne_of_mem_nbrs_false (F : Frame L1 L2 S D X) {p y y' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hp : vtype p = false) (hy : y ∈ nbrs p) (hy' : y' ∈ nbrs p) (hne : y ≠ y') :
    Zv y ≠ Zv y' := by
  intro heq
  have hA := Amal.of_frame F
  obtain ⟨e, he, heQ, he5⟩ := exists_five_stab F hp
  have he5' : e ^ 5 ∈ Qv p := by rw [he5]; exact one_mem _
  obtain ⟨g, hg, hgy⟩ := exists_zpow_smul_nbr F hp he heQ he5' hy hy'
  have hgst : (g : G) ∈ stab p := (Subgroup.zpowers_le.mpr he) hg
  have hgN : conjSub (g : G) (Zv y) = Zv y := by rw [← Zv_smul, hgy, ← heq]
  have hgQ : (g : G) ∉ Qv p := by
    intro h
    have hfix : g • y = y := smul_eq_of_mem_stab (g := g)
      (hA.Qv_le_stab_of_mem_nbrs hy h)
    exact hne (by rw [← hgy, hfix])
  have hg5 : (g : G) ^ 5 ∈ Qv p := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he5, one_zpow]
    exact one_mem _
  have hall : ∀ u ∈ nbrs p, Zv u = Zv y := by
    intro u hu
    obtain ⟨h, hh, hhu⟩ := exists_zpow_smul_nbr F hp hgst hgQ hg5 hy hu
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hconj : ∀ n : ℤ, conjSub ((g : G) ^ n) (Zv y) = Zv y := by
      intro n
      have hmem : (g : G) ∈ Subgroup.normalizer (Zv y : Set G) := mem_normalizer_of_conjSub_eq hgN
      exact F7.conjSub_eq_of_mem_normalizer (Subgroup.zpow_mem _ hmem n)
    rw [← hhu, Zv_smul, ← hi]
    exact hconj i
  have hnp : stab p ≤ Subgroup.normalizer (Zv y : Set G) := by
    intro k hk
    obtain ⟨hG0, hfix⟩ := mem_stab.mp hk
    have hku : (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • y ∈ nbrs p := by
      have := (smul_adj (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S))).mpr
        (show (graph _ _ _).Adj p y from hy)
      rwa [hfix] at this
    have e := Zv_smul (⟨k, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) y
    rw [hall _ hku] at e
    exact mem_normalizer_of_conjSub_eq e.symm
  have hyp : p ∈ nbrs y := (show (graph _ _ _).Adj p y from hy).symm
  have hU : Zv y ≤ stab p ⊓ stab y :=
    le_inf ((Zv_le_Qv_of_mem_nbrs F hyp).trans (pCoreOf_le 2 _))
      ((hA.Zv_le_Qv y).trans (pCoreOf_le 2 _))
  exact hA.Zv_ne_bot y (hA.eq_bot_of_normalizes_both (show (graph _ _ _).Adj p y from hy) hU
    hnp (hA.stab_le_normalizer_Zv y))

end CFSG.Quasithin.Kleidman.F204
