module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Quasithin.H13

section L828G

theorem pow_three_smul_eq_828 {W : Type*} [Group W] {g : MulAut W} (hg : g ^ 9 = 1) {k : ℤ}
    (hk : g ^ k ≠ 1) {w : W} (hw : (g ^ k) w = w) : (g ^ 3) w = w := by
  have hst : g ^ k ∈ MulAction.stabilizer (MulAut W) w := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact hw
  have hfix : ∀ n : ℤ, (g ^ (k * n)) w = w := fun n => by
    have h := Subgroup.zpow_mem _ hst n
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← zpow_mul] at h
    exact h
  have hg9 : g ^ (9 : ℤ) = 1 := by exact_mod_cast hg
  have hgd : (g ^ ((Int.gcd k 9 : ℕ) : ℤ)) w = w := by
    rw [Int.gcd_eq_gcd_ab k 9, zpow_add, zpow_mul g 9, hg9, one_zpow, mul_one]
    exact hfix _
  have hd9 : Int.gcd k 9 ∣ 9 := by
    have := Int.gcd_dvd_right k 9
    exact_mod_cast this
  have hdk : ((Int.gcd k 9 : ℕ) : ℤ) ∣ k := Int.gcd_dvd_left k 9
  have hdle : Int.gcd k 9 ≤ 9 := Nat.le_of_dvd (by norm_num) hd9
  generalize Int.gcd k 9 = d at hgd hd9 hdk hdle
  interval_cases d <;> norm_num at hd9
  ·
    have h1 : g w = w := by simpa using hgd
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, h1, h1, h1]
  ·
    simpa using hgd
  ·
    exfalso
    obtain ⟨j, rfl⟩ := hdk
    apply hk
    rw [zpow_mul, show ((9 : ℕ) : ℤ) = 9 from rfl, hg9, one_zpow]

theorem pow_three_eq_one_of_card_828 {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 16)
    {g : MulAut W} (hg : g ^ 9 = 1) : g ^ 3 = 1 := by
  classical
  by_contra hx
  have : Fintype W := Fintype.ofFinite W
  have hord : orderOf g = 9 := by
    have h1 : orderOf g ∣ 9 := orderOf_dvd_of_pow_eq_one hg
    have h2 : ¬ orderOf g ∣ 3 := fun h => hx (orderOf_dvd_iff_pow_eq_one.mp h)
    have hle : orderOf g ≤ 9 := Nat.le_of_dvd (by norm_num) h1
    generalize orderOf g = o at h1 h2 hle
    interval_cases o <;> revert h1 h2 <;> decide
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) fun f f' h => MulEquiv.ext (congrFun h)
  set H := Subgroup.zpowers g with hHdef
  have : Fintype ↥H := Fintype.ofFinite _
  have hcomm : ∀ h ∈ H, ∀ w : W, (g ^ 3) (h w) = h ((g ^ 3) w) := by
    intro h hh w
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← zpow_natCast, ← zpow_add, ← zpow_add,
      add_comm]
  let X : SubMulAction ↥H W :=
    { carrier := {w | (g ^ 3) w ≠ w}
      smul_mem' := by
        intro h w hw hfx
        apply hw
        rw [Subgroup.smul_def, MulAut.smul_def, hcomm h h.2 w] at hfx
        exact (h : MulAut W).injective hfx }
  have hfree : ∀ h : ↥H, h ≠ 1 → Fintype.card (MulAction.fixedBy ↥X h) = 0 := by
    intro h hh
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
    have hgn : g ^ n ≠ 1 := fun h1 => hh (Subtype.ext (hn.symm.trans h1))
    have hx' : (g ^ n) (x : W) = x := by
      have h2 := congrArg Subtype.val (MulAction.mem_fixedBy.mp hx)
      rw [SubMulAction.val_smul, Subgroup.smul_def, MulAut.smul_def, ← hn] at h2
      exact h2
    exact x.2 (pow_three_smul_eq_828 hg hgn hx')
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥H ↥X
  rw [Finset.sum_eq_single 1 (fun h _ hh => hfree h hh) (by simp)] at hB
  have h1 : Fintype.card (MulAction.fixedBy ↥X (1 : ↥H)) = Fintype.card ↥X := by
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => MulAction.mem_fixedBy.mpr
      (one_smul _ x)))]
  have hH : Fintype.card ↥H = 9 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hord]
  rw [h1, hH] at hB
  let F : Subgroup W := MonoidHom.eqLocus (g ^ 3).toMonoidHom (MonoidHom.id W)
  have hX : Nat.card ↥X + Nat.card F = 16 := by
    have h2 : Nat.card ↥X = Nat.card {w : W // ¬ (g ^ 3) w = w} := rfl
    have h3 : Nat.card F = Nat.card {w : W // (g ^ 3) w = w} := rfl
    rw [h2, h3, ← hW]
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le (fun w : W => (g ^ 3) w = w)
    omega
  rw [← Nat.card_eq_fintype_card] at hB
  have hF : Nat.card F ∣ 16 := hW ▸ Subgroup.card_subgroup_dvd_card F
  have hF16 : Nat.card F ≠ 16 := by
    intro h16
    apply hx
    have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (h16.trans hW.symm)
    ext w
    have hw : w ∈ F := htop ▸ Subgroup.mem_top w
    exact hw
  have hle : Nat.card F ≤ 16 := Nat.le_of_dvd (by norm_num) hF
  generalize Nat.card F = c at hF hF16 hle hX
  interval_cases c
  all_goals omega

end L828G

end CFSG.Quasithin.H13
