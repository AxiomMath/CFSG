module

public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

@[expose] def s16c11BigCls (n : ℕ) (x : Fin n → ZMod 2) (hx : ∑ i, x i = 0) :
    (FFModel.symDn n).Mod :=
  QuotientGroup.mk (⟨Multiplicative.ofAdd x, hx⟩ : ↥(G6.coreMod n))

theorem s16c11BigCls_surjective (n : ℕ) (q : (FFModel.symDn n).Mod) :
    ∃ (x : Fin n → ZMod 2) (hx : ∑ i, x i = 0), q = s16c11BigCls n x hx := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective q
  unfold FFModel.symDn at m hm
  refine ⟨Multiplicative.toAdd (m : G6.PermMod n), G6.mem_coreMod.1 m.2, ?_⟩
  rw [← hm, s16c11BigCls]
  congr 1

private lemma s16c11_big_cls_toAdd_allOnes_zpow (n : ℕ) (k : ℤ) (i : Fin n) :
    Multiplicative.toAdd (G6.allOnes n ^ k) i = k • (1 : ZMod 2) := by
  rw [toAdd_zpow, Pi.smul_apply, G6.allOnes, toAdd_ofAdd]

private lemma s16c11_big_cls_toAdd_mul_inv (n : ℕ) (x y : Fin n → ZMod 2) (i : Fin n) :
    Multiplicative.toAdd ((Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y) i =
      - x i + y i := by
  rw [toAdd_mul, Pi.add_apply, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, Pi.neg_apply]

theorem s16c11BigCls_eq_iff {n : ℕ} {x y : Fin n → ZMod 2} {hx : ∑ i, x i = 0}
    {hy : ∑ i, y i = 0} :
    s16c11BigCls n x hx = s16c11BigCls n y hy ↔ (y = x ∨ y = fun i => x i + 1) := by
  constructor
  · intro h
    have hmem : ((⟨Multiplicative.ofAdd x, hx⟩ : ↥(G6.coreMod n))⁻¹ *
        ⟨Multiplicative.ofAdd y, hy⟩) ∈
        (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n) :=
      QuotientGroup.eq.mp h
    obtain ⟨hzp, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzp
    have hk' : ∀ i : Fin n, k • (1 : ZMod 2) = - x i + y i := by
      intro i
      rw [← s16c11_big_cls_toAdd_allOnes_zpow n k i,
        ← s16c11_big_cls_toAdd_mul_inv n x y i]
      exact congrFun (congrArg Multiplicative.toAdd hk) i
    have hyx : ∀ i : Fin n, y i = x i + k • (1 : ZMod 2) := by
      intro i
      rw [hk' i]
      abel
    have hk_eq : k • (1 : ZMod 2) = (k : ZMod 2) := by
      rw [zsmul_eq_mul, mul_one]
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (k : ZMod 2) with h0 | h1
    · left
      funext i
      rw [hyx i, hk_eq, h0, add_zero]
    · right
      funext i
      rw [hyx i, hk_eq, h1]
  · rintro (rfl | h)
    · unfold s16c11BigCls
      congr 1
    · have hxA : Multiplicative.ofAdd x ∈ G6.coreMod n := hx
      have hyA : Multiplicative.ofAdd y ∈ G6.coreMod n := hy
      have hmem : ((⟨Multiplicative.ofAdd x, hxA⟩ : ↥(G6.coreMod n))⁻¹ *
          ⟨Multiplicative.ofAdd y, hyA⟩) ∈
          (Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n).subgroupOf (G6.coreMod n) := by
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · refine Subgroup.mem_zpowers_iff.mpr ⟨1, ?_⟩
          apply Multiplicative.toAdd.injective
          funext i
          rw [show (↑((⟨Multiplicative.ofAdd x, hxA⟩ : ↥(G6.coreMod n))⁻¹ *
              ⟨Multiplicative.ofAdd y, hyA⟩) : G6.PermMod n) =
              (Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y from rfl]
          rw [s16c11_big_cls_toAdd_allOnes_zpow n 1 i,
            s16c11_big_cls_toAdd_mul_inv n x y i, h]
          simp only [one_zsmul, neg_one_zsmul, add_zero]
          abel
        · exact ((⟨Multiplicative.ofAdd x, hxA⟩ : ↥(G6.coreMod n))⁻¹ *
            ⟨Multiplicative.ofAdd y, hyA⟩).2
      exact (QuotientGroup.eq).mpr hmem

theorem s16c11BigCls_modAct (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : Fin n → ZMod 2}
    {hx : ∑ i, x i = 0} {hx' : ∑ i, x (σ⁻¹ i) = 0} :
    (FFModel.symDn_isActionModel n).modAct σ (s16c11BigCls n x hx) =
      s16c11BigCls n (fun i => x (σ⁻¹ i)) hx' := by
  simp only [s16c11BigCls, FFModel.IsActionModel.modAct_apply,
    FFModel.IsActionModel.modEnd_mk]
  rfl

theorem s16c11BigCls_card (n : ℕ) (hn : n = 9 ∨ n = 10) :
    Nat.card (FFModel.symDn n).Mod = 2 ^ 8 := by
  have hcard : Nat.card (FFModel.symDn n).Mod =
      Nat.card (CFSG.Quasithin.Explicit.dnModel n .symmetric).Sec := rfl
  rcases hn with rfl | rfl
  · rw [hcard, CFSG.Quasithin.Explicit.card_dn_sec (by omega) .symmetric,
      if_neg (by decide : ¬ Even 9)]
  · rw [hcard, CFSG.Quasithin.Explicit.card_dn_sec (by omega) .symmetric,
      if_pos (by decide : Even 10)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
