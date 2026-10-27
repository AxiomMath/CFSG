module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R53a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c4_r56_comm_mem (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {g a v : G} (ha : a ∈ conjSubgroup V g)
    (hv : v ∈ conjSubgroup D.M g) : a * v * a⁻¹ * v⁻¹ ∈ conjSubgroup V g := by
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have ha' : g * a * g⁻¹ ∈ V := (mem_conjSubgroup_iff).1 ha
  have hv' : g * v * g⁻¹ ∈ D.M := (mem_conjSubgroup_iff).1 hv
  have hnv : g * v * g⁻¹ ∈ normalizer (V : Set G) := hP.le_normalizer hv'
  have hconj : (g * v * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹ ∈ V :=
    ((Subgroup.mem_normalizer_iff.1 hnv) (g * a * g⁻¹)⁻¹).1 (V.inv_mem ha')
  refine (mem_conjSubgroup_iff).2 ?_
  rw [show g * (a * v * a⁻¹ * v⁻¹) * g⁻¹ =
      (g * a * g⁻¹) * ((g * v * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹) by group]
  exact V.mul_mem ha' hconj

theorem s16c4_r56_fixV_of_mem {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {B : Subgroup G}
    {g : G} (hBg : B ≤ conjSubgroup V g) (hBst : B ≤ stabTil V₀ V) {u : IntMod V hV}
    (hu : u.val ∈ conjSubgroup V g) : mkTil V₀ V hV u ∈ fixV (barSub V₀ V hV B) := by
  rw [mem_fixV]
  intro z hz
  obtain ⟨b, hbB, rfl⟩ := (mem_barSub V₀ V hV B z).1 hz
  rw [actTil_mk]
  have hb : (b : G) ∈ conjSubgroup V g := hBg hbB
  have hcomm : (b : G) * u.val = u.val * (b : G) :=
    B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup hV g) hb hu
  have hstab : actStab V₀ V hV b u = u := by
    refine IntMod.val_injective ?_
    rw [actStab_apply_val, hcomm]
    group
  rw [hstab]

theorem s16c4_r56_hcom (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {B : Subgroup G}
    (hB : B ∈ E3.gammaSet V 1 D.M) {g : G} (hBg : B ≤ conjSubgroup V g)
    (hcard : Nat.card (barSub V₀ V hV B) = 2 ^ 4)
    (hr : ((mSub V₀ + 5 : ℕ) : ℕ∞) ≤ rMV D.M V) :
    ∀ x ∈ barSub V₀ V hV B, x ≠ 1 → ∀ w : Vtil V₀ V hV, x w = w →
      ∀ y ∈ barSub V₀ V hV B, y w * w⁻¹ ∈ fixV (barSub V₀ V hV B) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hBst : B ≤ stabTil V₀ V := hB.1.trans hMst
  have hVg2 : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hBel : IsElemAbelian 2 B := B2F.isElemAbelian_mono hBg hVg2
  have hE2 : IsElemAbelian2 (barSub V₀ V hV B) := isElemAbelian2_barSub hV hBel
  have hE2' : IsPGroup 2 (barSub V₀ V hV B) := E3.isPGroup_of_isElemAbelian2 hE2
  intro x hx hxne w hw y hy
  have hQ : Subgroup.zpowers x ≤ barSub V₀ V hV B := Subgroup.zpowers_le.2 hx
  have hQcard : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE2.2 x hx) hxne
  have hmq3 : E3.mQuot (barSub V₀ V hV B) (Subgroup.zpowers x) = 3 := by
    have hmul := E3.card_eq_two_pow_mul hE2' hQ
    rw [hcard, hQcard] at hmul
    have h' : 2 ^ 4 = 2 ^ (E3.mQuot (barSub V₀ V hV B) (Subgroup.zpowers x) + 1) := by
      rw [pow_succ]
      exact hmul
    have := Nat.pow_right_injective (le_refl 2) h'
    omega
  have hi : ((1 + E3.mQuot (barSub V₀ V hV B) (Subgroup.zpowers x) + mSub V₀ : ℕ) : ℕ∞) <
      rMV D.M V := by
    rw [hmq3]
    refine lt_of_lt_of_le ?_ hr
    exact_mod_cast (by omega : 1 + 3 + mSub V₀ < mSub V₀ + 5)
  have hpre : preTil V₀ V hV (fixV (Subgroup.zpowers x)) ≤ conjSubgroup D.M g :=
    s16c4_preTil_fixV_le D h22 hS (i := 1) hB (g := g) hBg hQ hi
  have hwQ : w ∈ fixV (Subgroup.zpowers x) :=
    (mem_fixV_zpowers_iff_apply (g := x) (v := w)).2 hw
  obtain ⟨v, hv⟩ := mkTil_surjective V₀ V hV w
  have hvQ : mkTil V₀ V hV v ∈ fixV (Subgroup.zpowers x) := by rw [hv]; exact hwQ
  have hvmem : v.val ∈ conjSubgroup D.M g :=
    hpre ((mem_preTil V₀ V hV (fixV (Subgroup.zpowers x))).2 ⟨v, rfl, hvQ⟩)
  obtain ⟨a, haB, haeq⟩ := (mem_barSub V₀ V hV B y).1 hy
  have hyw : y w = mkTil V₀ V hV (actStab V₀ V hV a v) := by
    rw [← haeq, ← hv, actTil_mk]
  have huy : mkTil V₀ V hV (actStab V₀ V hV a v * v⁻¹) = y w * w⁻¹ := by
    rw [hyw, ← hv, map_mul, map_inv]
  have huval : (actStab V₀ V hV a v * v⁻¹).val ∈ conjSubgroup V g := by
    have hcomm := s16c4_r56_comm_mem D hS (hBg haB) hvmem
    convert hcomm using 1
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
  have hfix := s16c4_r56_fixV_of_mem (V₀ := V₀) (V := V) (hV := hV) (B := B) (g := g)
    (u := actStab V₀ V hV a v * v⁻¹) hBg hBst huval
  rwa [huy] at hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
