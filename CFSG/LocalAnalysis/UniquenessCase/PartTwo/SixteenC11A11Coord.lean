module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2AltBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

@[expose] def s16c11AltVec (n : ℕ) (x : Fin n → ZMod 2) (hx : ∑ i, x i = 0) :
    (FFModel.altDn n).Mod :=
  QuotientGroup.mk (⟨Multiplicative.ofAdd x, hx⟩ : ↥(G6.coreMod n))

theorem s16c11AltVec_surjective (n : ℕ) (q : (FFModel.altDn n).Mod) :
    ∃ (x : Fin n → ZMod 2) (hx : ∑ i, x i = 0), q = s16c11AltVec n x hx := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective q
  unfold FFModel.altDn at m hm
  refine ⟨Multiplicative.toAdd (m : G6.PermMod n), G6.mem_coreMod.1 m.2, ?_⟩
  rw [← hm, s16c11AltVec]
  congr 1

theorem s16c11AltVec_eq_iff {n : ℕ} (hn : ¬ 2 ∣ n) {x y : Fin n → ZMod 2}
    {hx : ∑ i, x i = 0} {hy : ∑ i, y i = 0} :
    s16c11AltVec n x hx = s16c11AltVec n y hy ↔ x = y := by
  constructor
  · intro h
    have hmem : ((⟨Multiplicative.ofAdd x, hx⟩ : ↥(G6.coreMod n))⁻¹ *
        ⟨Multiplicative.ofAdd y, hy⟩) ∈
        (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n) :=
      QuotientGroup.eq.mp h
    obtain ⟨hzp, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
    have hA : ∀ i, Multiplicative.toAdd (G6.allOnes n ^ k) i = k • (1 : ZMod 2) := by
      intro i
      rw [toAdd_zpow, Pi.smul_apply, G6.allOnes, toAdd_ofAdd]
    have hB : ∀ i, Multiplicative.toAdd
        ((Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y) i = - x i + y i := by
      intro i
      rw [toAdd_mul, Pi.add_apply, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, Pi.neg_apply]
    have hk' : ∀ i, k • (1 : ZMod 2) = - x i + y i := by
      intro i
      rw [← hA i, ← hB i]
      exact congrFun (congrArg Multiplicative.toAdd hk) i
    have hn1 : (n : ZMod 2) = 1 := by
      have h0 : (n : ZMod 2) ≠ 0 := fun h0 => hn ((ZMod.natCast_eq_zero_iff n 2).1 h0)
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (n : ZMod 2) with h1 | h1
      · exact absurd h1 h0
      · exact h1
    have hL : ∑ i : Fin n, k • (1 : ZMod 2) = (k : ZMod 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [nsmul_eq_mul, zsmul_eq_mul, mul_one, hn1, one_mul]
    have hR : ∑ i : Fin n, (- x i + y i) = 0 := by
      have hc : ∀ i : Fin n, - x i + y i = x i + y i := fun i =>
        congrArg (fun z => z + y i) (CharTwo.neg_eq (x i))
      rw [Finset.sum_congr rfl fun i _ => hc i, Finset.sum_add_distrib, hx, hy, add_zero]
    have hkz : (k : ZMod 2) = 0 := by
      have hsum : ∑ i : Fin n, k • (1 : ZMod 2) = ∑ i : Fin n, (- x i + y i) :=
        Finset.sum_congr rfl fun i _ => hk' i
      rw [hL, hR] at hsum
      exact hsum
    have hk0 : k • (1 : ZMod 2) = 0 := by
      rw [zsmul_eq_mul, hkz, zero_mul]
    funext i
    have hi : k • (1 : ZMod 2) = - x i + y i := hk' i
    rw [hk0] at hi
    have h2 : - x i + y i = 0 := hi.symm
    rw [add_eq_zero_iff_eq_neg] at h2
    exact neg_inj.mp h2
  · rintro rfl
    rfl

theorem s16c11AltVec_eq_one_iff {n : ℕ} (hn : ¬ 2 ∣ n) {x : Fin n → ZMod 2}
    {hx : ∑ i, x i = 0} : s16c11AltVec n x hx = 1 ↔ x = 0 := by
  have h1 : (1 : (FFModel.altDn n).Mod) = s16c11AltVec n 0 (by simp) := by
    rw [s16c11AltVec]
    rfl
  rw [h1]
  exact s16c11AltVec_eq_iff hn

theorem s16c11AltAct_vec (n : ℕ) (g : ↥(alternatingGroup (Fin n))) {x : Fin n → ZMod 2}
    {hx : ∑ i, x i = 0} {hx' : ∑ i, x ((g : Equiv.Perm (Fin n))⁻¹ i) = 0} :
    S16C11AltAct n g (s16c11AltVec n x hx) =
      s16c11AltVec n (fun i => x ((g : Equiv.Perm (Fin n))⁻¹ i)) hx' := by
  simp only [S16C11AltAct, s16c11AltVec, FFModel.IsActionModel.modAct_apply,
    FFModel.IsActionModel.modEnd_mk]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
