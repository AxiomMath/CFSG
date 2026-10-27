module

public import CFSG.RankThree.GF2n.Tim81RootLocal
public import CFSG.RankThree.GF2n.Tim78S4RootDefs
public import CFSG.RankThree.GF2n.Tim77Prop24Core
import CFSG.RankThree.GF2n.Tim77Prop24Roots

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

namespace Tim78

variable {G : Type*} [Group G]

theorem exists_pow_mul_eq_mul {X N : Subgroup G} (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    {h e : G} (hh : h ∈ X) (he : e ∈ N) (k : ℕ) : ∃ e' ∈ N, (h * e) ^ k = h ^ k * e' := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨e', he', hk⟩ := ih
    have h1 : h⁻¹ * e' * h⁻¹⁻¹ ∈ N := hnorm h⁻¹ (X.inv_mem hh) e' he'
    rw [inv_inv] at h1
    refine ⟨(h⁻¹ * e' * h) * e, N.mul_mem h1 he, ?_⟩
    rw [pow_succ, hk, pow_succ]
    group

theorem exists_bisector_of_odd {X N : Subgroup G} (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    {u u' : G} (hu : u ∈ X) (hu' : u' ∈ X) (huu : u * u = 1) (hu'u' : u' * u' = 1)
    (hodd : Odd (orderOf (u * u')))
    (φ : G →* G) (hφu : φ u = u') (hφu' : u⁻¹ * φ u' ∈ N) :
    ∃ σ ∈ X, (σ * u * σ⁻¹) * (σ * u * σ⁻¹) = 1 ∧
      (σ * u * σ⁻¹) * u * (σ * u * σ⁻¹)⁻¹ = u' ∧
      (σ * u * σ⁻¹)⁻¹ * φ (σ * u * σ⁻¹) ∈ N := by
  obtain ⟨k, hk⟩ := hodd
  set ρ := u * u' with hρ
  have hρm : ρ ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one ρ
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hu'i : u'⁻¹ = u' := inv_eq_of_mul_eq_one_right hu'u'
  have hρi : ρ⁻¹ = u' * u := by rw [hρ, mul_inv_rev, hui, hu'i]
  have hρX : ρ ∈ X := X.mul_mem hu hu'
  have huρ1 : u * ρ * u⁻¹ = ρ⁻¹ := by
    rw [hρi, hρ, hui]
    calc u * (u * u') * u = (u * u) * u' * u := by group
      _ = u' * u := by rw [huu, one_mul]
  have huρ : ∀ i : ℕ, u * ρ ^ i * u⁻¹ = (ρ⁻¹) ^ i := by
    intro i
    have := map_pow (MulAut.conj u) ρ i
    simpa [MulAut.conj_apply, huρ1] using this
  have hρ2k : ρ ^ (2 * k) = ρ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact hρm
  have hρ2k' : (ρ⁻¹) ^ (2 * k) = ρ := by
    rw [inv_pow, hρ2k, inv_inv]
  set s := k * (k + 1) with hs
  set σ := ρ ^ s with hσ
  have hσX : σ ∈ X := X.pow_mem hρX s
  have hσσ : σ * σ = ρ ^ k := by
    rw [hσ, ← pow_add, ← two_mul]
    have : 2 * s = (2 * k + 1) * k + k := by rw [hs]; ring
    rw [this, pow_add, pow_mul, hρm, one_pow, one_mul]
  have huσ : u * σ⁻¹ = σ * u := by
    have h1 := huρ s
    have h2 : u * σ⁻¹ * u⁻¹ = σ := by
      calc u * σ⁻¹ * u⁻¹ = (u * σ * u⁻¹)⁻¹ := by group
        _ = ((ρ⁻¹) ^ s)⁻¹ := by rw [hσ, h1]
        _ = σ := by rw [inv_pow, inv_inv]
    calc u * σ⁻¹ = (u * σ⁻¹ * u⁻¹) * u := by group
      _ = σ * u := by rw [h2]
  have hr : σ * u * σ⁻¹ = ρ ^ k * u := by
    rw [mul_assoc, huσ, ← mul_assoc, hσσ]
  refine ⟨σ, hσX, ?_⟩
  rw [hr]
  have hrr : (ρ ^ k * u) * (ρ ^ k * u) = 1 := by
    calc (ρ ^ k * u) * (ρ ^ k * u) = ρ ^ k * (u * ρ ^ k * u⁻¹) * (u * u) := by
          group
      _ = 1 := by rw [huρ k, inv_pow, huu]; group
  have hrinv : (ρ ^ k * u)⁻¹ = ρ ^ k * u := inv_eq_of_mul_eq_one_right hrr
  refine ⟨hrr, ?_, ?_⟩
  · rw [hrinv]
    calc ρ ^ k * u * u * (ρ ^ k * u) = ρ ^ k * (u * u) * ρ ^ k * u := by group
      _ = ρ ^ (2 * k) * u := by rw [huu, mul_one, ← pow_add, two_mul]
      _ = u' := by rw [hρ2k, hρi, mul_assoc, huu, mul_one]
  · rw [hrinv]
    have hφρ : φ ρ = ρ⁻¹ * (u⁻¹ * φ u') := by
      rw [hρ, map_mul, hφu, hρi]
      group
    obtain ⟨n₁, hn₁, hpow⟩ := exists_pow_mul_eq_mul hnorm (X.inv_mem hρX) hφu' k
    have hφr : φ (ρ ^ k * u) = (ρ⁻¹) ^ k * n₁ * u' := by
      rw [map_mul, map_pow, hφρ, hpow, hφu]
    rw [hφr]
    have huρ' : u * (ρ⁻¹) ^ k * u⁻¹ = ρ ^ k := by
      calc u * (ρ⁻¹) ^ k * u⁻¹ = (u * ρ ^ k * u⁻¹)⁻¹ := by rw [inv_pow]; group
        _ = ρ ^ k := by rw [huρ k, inv_pow, inv_inv]
    have hfin : ρ ^ k * u * ((ρ⁻¹) ^ k * n₁ * u') = u' * n₁ * u'⁻¹ := by
      calc ρ ^ k * u * ((ρ⁻¹) ^ k * n₁ * u')
          = ρ ^ k * (u * (ρ⁻¹) ^ k * u⁻¹) * u * n₁ * u' := by group
        _ = ρ ^ (2 * k) * u * n₁ * u' := by rw [huρ', ← pow_add, two_mul]
        _ = u' * (u * u) * n₁ * u' := by rw [hρ2k, hρi]; group
        _ = u' * n₁ * u'⁻¹ := by rw [huu, hu'i]; group
    rw [hfin]
    exact hnorm u' hu' n₁ hn₁

end Tim78

namespace Tim77

variable {G : Type*} [Group G] [Finite G]

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

theorem conj_not_mem_M {k u : G} (hk : k ∈ A ⊔ Ab) (hu : u ∈ A) (huL : u ∉ L) :
    k * u * k⁻¹ ∉ M := by
  intro h
  apply huL
  have hkN : k⁻¹ ∈ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer_M ((A ⊔ Ab).inv_mem hk)
  have := (Subgroup.mem_normalizer_iff.mp hkN _).mp h
  rw [show k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ = u by group] at this
  rw [← S.inf_M]
  exact Subgroup.mem_inf.mpr ⟨hu, this⟩

theorem mul_mem_conj_of_sq {k t n : G} (hk : k ∈ A ⊔ Ab) (ht : t ∈ conjSubgroup k A)
    (htM : t ∉ M) (hn : n ∈ M) (h2 : t * n * (t * n) = 1) : t * n ∈ conjSubgroup k A := by
  have hkN : k ∈ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer_M hk
  have hkN' : k⁻¹ ∈ Subgroup.normalizer (M : Set G) := S.sup_le_normalizer_M ((A ⊔ Ab).inv_mem hk)
  have ht₀ : k⁻¹ * t * k ∈ A := mem_conjSubgroup.mp ht
  have ht₀L : k⁻¹ * t * k ∉ L := fun h => htM (by
    have := (Subgroup.mem_normalizer_iff.mp hkN _).mp (S.L_le_M h)
    rwa [show k * (k⁻¹ * t * k) * k⁻¹ = t by group] at this)
  have hn₀ : k⁻¹ * n * k ∈ M := by
    have := (Subgroup.mem_normalizer_iff.mp hkN' n).mp hn
    rwa [inv_inv] at this
  have h₀ : (k⁻¹ * t * k) * (k⁻¹ * n * k) * ((k⁻¹ * t * k) * (k⁻¹ * n * k)) = 1 := by
    calc (k⁻¹ * t * k) * (k⁻¹ * n * k) * ((k⁻¹ * t * k) * (k⁻¹ * n * k))
        = k⁻¹ * (t * n * (t * n)) * k := by group
      _ = 1 := by rw [h2]; group
  have h₁ := S.mul_mem_A_of_sq ht₀ ht₀L hn₀ h₀
  rw [mem_conjSubgroup]
  convert h₁ using 1
  group

end Prop24Setup

end Tim77

end CFSG.RankThree.GF2n

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace RootCore

variable [Finite G] {M B Q : Subgroup G} (H : RootCore M B Q)
include H

theorem case2_aa {g a y : G} (C : Case2 M B Q g a y) : a * a = 1 := by
  rw [← sq]
  exact (isElemAbelian_conjSubgroup H.elemAb g).2 a (Subgroup.mem_inf.mp C.ha).1

theorem case2_conj_a {g a y : G} (C : Case2 M B Q g a y) : y * a * y⁻¹ = a * ⁅a, y⁆ := by
  have haa := H.case2_aa C
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  rw [commutatorElement_def, hainv]
  calc y * a * y⁻¹ = (a * a) * y * a * y⁻¹ := by rw [haa, one_mul]
    _ = a * (a * y * a * y⁻¹) := by group

theorem case2_comm_ab {g a y : G} (C : Case2 M B Q g a y) : a * ⁅a, y⁆ = ⁅a, y⁆ * a := by
  have haa := H.case2_aa C
  have hbb : ⁅a, y⁆ * ⁅a, y⁆ = 1 := by rw [← sq]; exact H.sq_eq_one _ C.hb
  have h1 := H.case2_conj_a C
  have h2 : (a * ⁅a, y⁆) * (a * ⁅a, y⁆) = 1 := by
    rw [← h1]
    calc y * a * y⁻¹ * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [haa]; group
  have h3 : a * ⁅a, y⁆ * a = ⁅a, y⁆ := by
    have : a * ⁅a, y⁆ * a * ⁅a, y⁆ = 1 := by rw [← h2]; group
    have h4 := eq_inv_of_mul_eq_one_left this
    rwa [inv_eq_of_mul_eq_one_right hbb] at h4
  calc a * ⁅a, y⁆ = a * ⁅a, y⁆ * (a * a) := by rw [haa, mul_one]
    _ = (a * ⁅a, y⁆ * a) * a := by group
    _ = ⁅a, y⁆ * a := by rw [h3]

theorem case2_b_mem_normalizer {g a y : G} (C : Case2 M B Q g a y) :
    ⁅a, y⁆ ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
  rw [H.normalizer_conj_eq]
  exact H.centralizer_le_conj (Subgroup.mem_inf.mp C.ha).1 C.ha1
    (Subgroup.mem_centralizer_singleton_iff.mpr (H.case2_comm_ab C).symm)

theorem case2_sq_mem_normalizer {g a y : G} (C : Case2 M B Q g a y) :
    y ^ 2 ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
  rw [H.normalizer_conj_eq]
  refine H.centralizer_le_conj (Subgroup.mem_inf.mp C.ha).1 C.ha1
    (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  have hbb : ⁅a, y⁆ * ⁅a, y⁆ = 1 := by rw [← sq]; exact H.sq_eq_one _ C.hb
  have hyb : ⁅a, y⁆ * y = y * ⁅a, y⁆ := H.center_Q C.hb C.hy
  have h1 := H.case2_conj_a C
  have h2 : y * (y * a * y⁻¹) * y⁻¹ = a := by
    rw [h1]
    calc y * (a * ⁅a, y⁆) * y⁻¹ = (y * a * y⁻¹) * (y * ⁅a, y⁆ * y⁻¹) := by group
      _ = (a * ⁅a, y⁆) * ⁅a, y⁆ := by rw [h1, ← hyb]; group
      _ = a := by rw [mul_assoc, hbb, mul_one]
  have h3 : a * (y * y) = y * y * a := by
    calc a * (y * y) = (y * (y * a * y⁻¹) * y⁻¹) * (y * y) := by rw [h2]
      _ = y * y * a := by group
  rw [sq]
  exact h3.symm

theorem prop24_AB {g : G} (hgM : ¬ conjSubgroup g B ≤ M) (hA0 : conjSubgroup g B ⊓ M ≠ ⊥) :
    Tim77.Prop24Setup (conjSubgroup g B) B
      (conjSubgroup g B ⊓ Subgroup.normalizer (B : Set G))
      (B ⊓ Subgroup.normalizer (conjSubgroup g B : Set G))
      ((conjSubgroup g B ⊓ Subgroup.normalizer (B : Set G)) ⊔
        (B ⊓ Subgroup.normalizer (conjSubgroup g B : Set G))) := by
  have hLAB : conjSubgroup g B ⊓ Subgroup.normalizer (B : Set G) = conjSubgroup g B ⊓ M := by
    rw [H.normalizer_B]
  have hgB : B = conjSubgroup g⁻¹ (conjSubgroup g B) := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  exact ⟨isElemAbelian_conjSubgroup H.elemAb g, isTI_conjSubgroup H.ti g, ⟨g⁻¹, hgB⟩, rfl, rfl,
    rfl, hLAB ▸ hA0, fun h => hgM (by rw [← h, hLAB]; exact inf_le_right)⟩

theorem case2_mem_normalizer_conj {g a y x : G} (C : Case2 M B Q g a y)
    (hx : x ∈ conjSubgroup g B ⊓ M) :
    x ∈ Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G) := by
  have SB := H.prop24_AB C.hgM (by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨a, C.ha⟩, fun h => C.ha1 (congrArg Subtype.val h)⟩)
  have haA := (Subgroup.mem_inf.mp C.ha).1
  have hxA := (Subgroup.mem_inf.mp hx).1
  have hxa : x * a = a * x := SB.comm_A hxA haA
  have hxb : x * ⁅a, y⁆ = ⁅a, y⁆ * x := by
    refine SB.comm_L_Lb (Subgroup.mem_inf.mpr ⟨hxA, ?_⟩)
      (Subgroup.mem_inf.mpr ⟨C.hb, H.case2_b_mem_normalizer C⟩)
    rw [H.normalizer_B]
    exact (Subgroup.mem_inf.mp hx).2
  have hab : a * ⁅a, y⁆ ∈ conjSubgroup y (conjSubgroup g B) := by
    rw [← H.case2_conj_a C, mem_conjSubgroup, show y⁻¹ * (y * a * y⁻¹) * y = a by group]
    exact haA
  have hab1 : a * ⁅a, y⁆ ≠ 1 := by
    rw [← H.case2_conj_a C]
    intro h
    apply C.ha1
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  refine Tim77.mem_normalizer_of_commute_of_isTI
    (isTI_conjSubgroup (isTI_conjSubgroup H.ti g) y) hab hab1 ?_
  calc x * (a * ⁅a, y⁆) = (x * a) * ⁅a, y⁆ := by group
    _ = a * (x * ⁅a, y⁆) := by rw [hxa]; group
    _ = a * (⁅a, y⁆ * x) := by rw [hxb]
    _ = (a * ⁅a, y⁆) * x := by group

theorem case2_not_le_normalizer {g a y : G} (C : Case2 M B Q g a y) :
    ¬ conjSubgroup g B ≤ Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G) := by
  intro hAN
  have hA'E := isElemAbelian_conjSubgroup (isElemAbelian_conjSubgroup H.elemAb g) y
  have hA'TI := isTI_conjSubgroup (isTI_conjSubgroup H.ti g) y
  have hconj : conjSubgroup y⁻¹ (conjSubgroup y (conjSubgroup g B)) = conjSubgroup g B := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hel := Tim77.tim77_2_3 hA'E hA'TI (g := y⁻¹) (by rw [hconj]; exact hAN)
  rw [hconj] at hel
  have haA := (Subgroup.mem_inf.mp C.ha).1
  have haa := H.case2_aa C
  have hab' : y * a * y⁻¹ ∈ conjSubgroup y (conjSubgroup g B) := by
    rw [mem_conjSubgroup, show y⁻¹ * (y * a * y⁻¹) * y = a by group]
    exact haA
  have hb : ⁅a, y⁆ = a * (y * a * y⁻¹) := by
    rw [H.case2_conj_a C, ← mul_assoc, haa, one_mul]
  refine C.hgM fun u hu => ?_
  refine H.normalizer_eq_and_centralizer_le.2 ⁅a, y⁆ C.hb C.hb1
    (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  have h1 : u * a = a * u := comm_of_isElemAbelian (isElemAbelian_conjSubgroup H.elemAb g) hu haA
  have h2 : u * (y * a * y⁻¹) = (y * a * y⁻¹) * u :=
    comm_of_isElemAbelian hel (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left hab')
  rw [hb]
  calc u * (a * (y * a * y⁻¹)) = (u * a) * (y * a * y⁻¹) := by group
    _ = a * (u * (y * a * y⁻¹)) := by rw [h1]; group
    _ = a * ((y * a * y⁻¹) * u) := by rw [h2]
    _ = (a * (y * a * y⁻¹)) * u := by group

theorem prop24_AA' {g a y : G} (C : Case2 M B Q g a y) :
    Tim77.Prop24Setup (conjSubgroup g B) (conjSubgroup y (conjSubgroup g B))
      (conjSubgroup g B ⊓ Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G))
      (conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G))
      ((conjSubgroup g B ⊓ Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) ⊔
        (conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G))) := by
  have hLbot : conjSubgroup g B ⊓
      Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G) ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨a, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp C.ha).1,
      H.case2_mem_normalizer_conj C C.ha⟩⟩, fun h => C.ha1 (congrArg Subtype.val h)⟩
  have hLne : conjSubgroup g B ⊓
      Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G) ≠ conjSubgroup g B := by
    intro hL
    refine H.case2_not_le_normalizer C ?_
    calc conjSubgroup g B = conjSubgroup g B ⊓
          Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G) := hL.symm
      _ ≤ Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G) := inf_le_right
  exact ⟨isElemAbelian_conjSubgroup H.elemAb g, isTI_conjSubgroup H.ti g, ⟨y, rfl⟩, rfl, rfl, rfl,
    hLbot, hLne⟩

theorem case2_Lb_eq {g a y : G} (C : Case2 M B Q g a y) :
    conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G) =
      conjSubgroup y (conjSubgroup g B ⊓
        Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) := by
  have hAA : conjSubgroup y (conjSubgroup y (conjSubgroup g B)) = conjSubgroup g B := by
    rw [← conjSubgroup_mul, ← sq]
    exact conjSubgroup_eq_self_iff.mpr (H.case2_sq_mem_normalizer C)
  rw [conjSubgroup_inf, ← normalizer_conjSubgroup, hAA]

theorem rootStep1Case2_of_not_le_M {g : G} (hgM : ¬ conjSubgroup g B ≤ M) :
    RootStep1Case2 M B Q g := by
  classical
  intro a ha ha1 y hy hb hb1
  have C : Case2 M B Q g a y := ⟨hgM, ha, ha1, hy, hb, hb1⟩
  by_contra hz1
  have haA := (Subgroup.mem_inf.mp ha).1
  have hE := isElemAbelian_conjSubgroup H.elemAb g
  have S := H.prop24_AA' C
  have SB := H.prop24_AB hgM (by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨a, ha⟩, fun h => ha1 (congrArg Subtype.val h)⟩)
  obtain ⟨t, htA, htN⟩ := Set.not_subset.mp (H.case2_not_le_normalizer C)
  have htL : t ∉ conjSubgroup g B ⊓
      Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G) :=
    fun h => htN (Subgroup.mem_inf.mp h).2
  have ht'A' : y * t * y⁻¹ ∈ conjSubgroup y (conjSubgroup g B) := by
    rw [mem_conjSubgroup, show y⁻¹ * (y * t * y⁻¹) * y = t by group]
    exact htA
  have ht'Lb : y * t * y⁻¹ ∉ conjSubgroup y (conjSubgroup g B) ⊓
      Subgroup.normalizer (conjSubgroup g B : Set G) := by
    rw [H.case2_Lb_eq C]
    intro h
    apply htL
    have := mem_conjSubgroup.mp h
    rwa [show y⁻¹ * (y * t * y⁻¹) * y = t by group] at this
  have hodd := S.odd_orderOf_mul htA htL ht'A' ht'Lb
  have htt : t * t = 1 := by rw [← sq]; exact hE.2 t htA
  have ht't' : y * t * y⁻¹ * (y * t * y⁻¹) = 1 := by
    calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hnorm : ∀ x ∈ conjSubgroup g B ⊔ conjSubgroup y (conjSubgroup g B),
      ∀ n ∈ (conjSubgroup g B ⊓
          Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) ⊔
        (conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G)),
      x * n * x⁻¹ ∈ (conjSubgroup g B ⊓
          Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) ⊔
        (conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G)) :=
    fun x hx n hn => (Subgroup.mem_normalizer_iff.mp (S.sup_le_normalizer_M hx) n).mp hn
  have hA₀L : ∀ x ∈ conjSubgroup g B ⊓ M, x ∈ (conjSubgroup g B ⊓
      Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, H.case2_mem_normalizer_conj C hx⟩
  have hzN := H.case2_sq_mem_normalizer C
  have hzB : y ^ 2 ∈ B := H.sq_mem hy
  have hc : t * y ^ 2 * t⁻¹ * (y ^ 2)⁻¹ ∈ conjSubgroup g B ⊓ M := by
    have := SB.commutator_mem_L htA (Subgroup.mem_inf.mpr ⟨hzB, hzN⟩)
    rwa [H.normalizer_B] at this
  have hc' : t * (y * y) * t⁻¹ * (y * y)⁻¹ ∈ conjSubgroup g B ⊓ M := by
    rw [← sq]; exact hc
  have hφ : t⁻¹ * (y * (y * t * y⁻¹) * y⁻¹) ∈ (conjSubgroup g B ⊓
          Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) ⊔
        (conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G)) := by
    have hcN := Subgroup.mem_sup_left (S := (conjSubgroup g B ⊓
          Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)))
        (T := (conjSubgroup y (conjSubgroup g B) ⊓
          Subgroup.normalizer (conjSubgroup g B : Set G))) (hA₀L _ hc')
    have h1 := hnorm t⁻¹ (Subgroup.mem_sup_left (inv_mem htA)) _ (inv_mem hcN)
    convert h1 using 1
    have e1 : y * (y * t * y⁻¹) * y⁻¹ = (y * y) * t * (y * y)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [e1]
    generalize y * y = z
    group
  obtain ⟨σ, hσX, hr2, hrt, hrφ⟩ := exists_bisector_of_odd hnorm (Subgroup.mem_sup_left htA)
    (Subgroup.mem_sup_right ht'A') htt ht't' hodd (MulAut.conj y).toMonoidHom
    (by simp [MulAut.conj_apply]) (by simpa [MulAut.conj_apply] using hφ)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hrφ
  have hrD : σ * t * σ⁻¹ ∈ conjSubgroup σ (conjSubgroup g B) := by
    rw [mem_conjSubgroup, show σ⁻¹ * (σ * t * σ⁻¹) * σ = t by group]
    exact htA
  have hrM := S.conj_not_mem_M hσX htA htL
  have hyrD : y * (σ * t * σ⁻¹) * y⁻¹ ∈ conjSubgroup σ (conjSubgroup g B) := by
    have e : y * (σ * t * σ⁻¹) * y⁻¹ = σ * t * σ⁻¹ *
        ((σ * t * σ⁻¹)⁻¹ * (y * (σ * t * σ⁻¹) * y⁻¹)) := by group
    rw [e]
    refine S.mul_mem_conj_of_sq hσX hrD hrM hrφ ?_
    rw [← e]
    calc y * (σ * t * σ⁻¹) * y⁻¹ * (y * (σ * t * σ⁻¹) * y⁻¹)
        = y * ((σ * t * σ⁻¹) * (σ * t * σ⁻¹)) * y⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hr1 : σ * t * σ⁻¹ ≠ 1 := by
    intro h
    apply htL
    have : t = 1 := by
      calc t = σ⁻¹ * (σ * t * σ⁻¹) * σ := by group
        _ = 1 := by rw [h]; group
    rw [this]
    exact one_mem _
  have hDg : conjSubgroup σ (conjSubgroup g B) = conjSubgroup (σ * g) B := by
    rw [conjSubgroup_mul]
  have hyD : y ∈ Subgroup.normalizer (conjSubgroup (σ * g) B : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    refine conjSubgroup_eq_of_isTI (isTI_conjSubgroup H.ti (σ * g)) ?_
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨y * (σ * t * σ⁻¹) * y⁻¹, Subgroup.mem_inf.mpr ⟨hDg ▸ hyrD, ?_⟩⟩, ?_⟩
    · rw [mem_conjSubgroup, show y⁻¹ * (y * (σ * t * σ⁻¹) * y⁻¹) * y = σ * t * σ⁻¹ by group]
      exact hDg ▸ hrD
    · intro h
      apply hr1
      have h' : y * (σ * t * σ⁻¹) * y⁻¹ = 1 := congrArg Subtype.val h
      calc σ * t * σ⁻¹ = y⁻¹ * (y * (σ * t * σ⁻¹) * y⁻¹) * y := by group
        _ = 1 := by rw [h']; group
  have hDM : conjSubgroup (σ * g) B ≤ M := by
    by_contra hDM
    exact hz1 (H.sq_eq_one_of_mem_normalizer_of_not_le_M hDM hy hyD)
  have hbN : ⁅a, y⁆ ∈ (conjSubgroup g B ⊓
          Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) ⊔
        (conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G)) := by
    have haL := hA₀L a ha
    have hya : y * a * y⁻¹ ∈ conjSubgroup y (conjSubgroup g B) ⊓
        Subgroup.normalizer (conjSubgroup g B : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_conjSubgroup, show y⁻¹ * (y * a * y⁻¹) * y = a by group]
        exact haA
      · rw [H.case2_conj_a C, H.normalizer_conj_eq]
        refine H.centralizer_le_conj haA ha1 (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
        rw [mul_assoc, ← H.case2_comm_ab C, ← mul_assoc]
    have e : ⁅a, y⁆ = a⁻¹ * (y * a * y⁻¹) := by
      rw [H.case2_conj_a C]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem haL)) (Subgroup.mem_sup_right hya)
  have hbD : ⁅a, y⁆ ∈ conjSubgroup (σ * g) B := by
    rw [← hDg, mem_conjSubgroup]
    refine S.L_le ?_
    have hm : σ⁻¹ * ⁅a, y⁆ * σ⁻¹⁻¹ ∈ (conjSubgroup g B ⊓
          Subgroup.normalizer (conjSubgroup y (conjSubgroup g B) : Set G)) ⊔
        (conjSubgroup y (conjSubgroup g B) ⊓ Subgroup.normalizer (conjSubgroup g B : Set G)) :=
      hnorm σ⁻¹ (inv_mem hσX) _ hbN
    rw [inv_inv] at hm
    refine S.mem_L_of_commute_M htA htL hm ?_
    have hcomm := H.commute_of_conj_le_M hDM ⁅a, y⁆ hb (σ * t * σ⁻¹) (hDg ▸ hrD)
    calc t * (σ⁻¹ * ⁅a, y⁆ * σ) = σ⁻¹ * ((σ * t * σ⁻¹) * ⁅a, y⁆) * σ := by group
      _ = σ⁻¹ * (⁅a, y⁆ * (σ * t * σ⁻¹)) * σ := by rw [hcomm]
      _ = σ⁻¹ * ⁅a, y⁆ * σ * t := by group
  have hDB : conjSubgroup (σ * g) B = B := by
    refine conjSubgroup_eq_of_isTI H.ti ?_
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨⁅a, y⁆, Subgroup.mem_inf.mpr ⟨hb, hbD⟩⟩, fun h => hb1 (congrArg Subtype.val h)⟩
  have hrB : σ * t * σ⁻¹ ∈ B := hDB ▸ hDg ▸ hrD
  have hNA : y⁻¹ * (σ * t * σ⁻¹) ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    refine conjSubgroup_eq_of_isTI (isTI_conjSubgroup H.ti g) ?_
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    have htt' : t = (σ * t * σ⁻¹)⁻¹ * (y * t * y⁻¹) * (σ * t * σ⁻¹) := by
      rw [← hrt]; group
    refine ⟨⟨t, Subgroup.mem_inf.mpr ⟨htA, ?_⟩⟩, ?_⟩
    · rw [mem_conjSubgroup]
      have : (y⁻¹ * (σ * t * σ⁻¹))⁻¹ * t * (y⁻¹ * (σ * t * σ⁻¹)) =
          (σ * t * σ⁻¹)⁻¹ * (y * t * y⁻¹) * (σ * t * σ⁻¹) := by group
      rw [this, ← htt']
      exact htA
    · intro h
      apply htL
      have : t = 1 := congrArg Subtype.val h
      rw [this]
      exact one_mem _
  have hsq := H.sq_eq_one_of_mem_normalizer_of_not_le_M hgM
    (mul_mem (inv_mem hy) (H.B_le_Q hrB)) hNA
  apply hz1
  have hry : σ * t * σ⁻¹ * y⁻¹ = y⁻¹ * (σ * t * σ⁻¹) := H.center_Q hrB (inv_mem hy)
  have hrr : σ * t * σ⁻¹ * (σ * t * σ⁻¹) = 1 := hr2
  have e : (y⁻¹ * (σ * t * σ⁻¹)) ^ 2 = (y ^ 2)⁻¹ := by
    calc (y⁻¹ * (σ * t * σ⁻¹)) ^ 2 = y⁻¹ * (σ * t * σ⁻¹ * y⁻¹) * (σ * t * σ⁻¹) := by
          rw [sq]; group
      _ = y⁻¹ * y⁻¹ * (σ * t * σ⁻¹ * (σ * t * σ⁻¹)) := by rw [hry]; group
      _ = (y ^ 2)⁻¹ := by rw [hrr, sq]; group
  rw [e] at hsq
  exact inv_eq_one.mp hsq

theorem rootStep1_of_case2 {g : G}
    (hgM : ¬ conjSubgroup g B ≤ M) (h2 : RootStep1Case2 M B Q g) : RootStep1 M B Q g := by
  intro a ha ha1 y hy hB
  by_cases hc : ⁅a, y⁆ = 1
  · have hya : y * a = a * y := (commutatorElement_eq_one_iff_mul_comm.mp hc).symm
    have hyC : y ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hya⟩
    obtain ⟨e1, e2⟩ := H.centralizer_Q_eq_of_not_le_M hgM ha ha1
    rw [e1, e2] at hyC
    exact H.sq_eq_one_of_mem_normalizer_of_not_le_M hgM hy (Subgroup.mem_inf.mp hyC).2
  · exact h2 a ha ha1 y hy hB hc

end RootCore

end CFSG.RankThree.GF2n.Tim78
