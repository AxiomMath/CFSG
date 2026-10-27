module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveEleven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.inf_kerMOf_le_centralizer_eSub (hX : Hyp167 M V₀ V U S H g X T) :
    T ⊓ kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) := by
  have hTK : T ⊓ kerMOf M X = pCoreOf 2 (kerMOf M X) :=
    Hyp167.inf_kerMOf_eq_pCoreOf hX
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  have hnormK : X ≤ Subgroup.normalizer ((kerMOf M X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 (normal_subgroupOf_kerMOf M X)
  have hnormP : X ≤ Subgroup.normalizer (pCoreOf 2 (kerMOf M X) : Set G) :=
    hnormK.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (kerMOf M X))
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hqP : q ∈ pCoreOf 2 (kerMOf M X) := by
    rw [← hTK]
    exact hq
  have hEsub : eSub V₀ X T ≤ Subgroup.centralizer ({q} : Set G) := by
    change conjClosure (V₀ ⊓ Subgroup.centralizer (T : Set G)) X ≤
      Subgroup.centralizer ({q} : Set G)
    refine conjClosure_le fun h hh z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hq' : h⁻¹ * q * h ∈ T ⊓ kerMOf M X := by
      rw [hTK]
      simpa using (Subgroup.mem_normalizer_iff.1 (hnormP (X.inv_mem hh)) q).1 hqP
    have hzq : (h⁻¹ * q * h) * z = z * (h⁻¹ * q * h) :=
      Subgroup.mem_centralizer_iff.1 hz.2 (h⁻¹ * q * h) hq'.1
    calc q * (h * z * h⁻¹)
        = h * ((h⁻¹ * q * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * q * h)) * h⁻¹ := by rw [hzq]
      _ = (h * z * h⁻¹) * q := by group
  exact (Subgroup.mem_centralizer_iff.1 (hEsub he) q (Set.mem_singleton q)).symm

theorem Hyp167.odd_relIndex_inf_centralizer_eSub (hX : Hyp167 M V₀ V U S H g X T) :
    Odd ((X ⊓ centralizer (eSub V₀ X T : Set G)).relIndex (kerMOf M X)) := by
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  have hKM : kerMOf M X ≤ M := kerMOf_le_left M X
  have hKXM : kerMOf M X ≤ X ⊓ M := le_inf hKX hKM
  have hnormK : X ≤ Subgroup.normalizer ((kerMOf M X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 (normal_subgroupOf_kerMOf M X)
  have hKn : ((kerMOf M X).subgroupOf (X ⊓ M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKXM).2 (inf_le_left.trans hnormK)
  have hSyl : IsSylowIn 2 (T ⊓ kerMOf M X) (kerMOf M X) :=
    hX.sylow.inf_normal hKXM hKn
  have hoddTK : Odd ((T ⊓ kerMOf M X).relIndex (kerMOf M X)) := by
    have := hSyl.not_dvd_relIndex
    exact Nat.odd_iff.2 (by omega)
  have hle : T ⊓ kerMOf M X ≤ X ⊓ centralizer (eSub V₀ X T : Set G) :=
    le_inf (inf_le_right.trans hKX) (Hyp167.inf_kerMOf_le_centralizer_eSub hX)
  have hdvd : (X ⊓ centralizer (eSub V₀ X T : Set G)).relIndex (kerMOf M X) ∣
      (T ⊓ kerMOf M X).relIndex (kerMOf M X) :=
    Subgroup.relIndex_dvd_of_le_left (kerMOf M X) hle
  exact Odd.of_dvd_nat hoddTK hdvd

theorem Hyp167.two_lt_relIndex_of_inf_eq_bot (h1 : W16One G) (hS : Std15 G) (h152 : Thm152 G)
    (hV₀ : V₀ ≤ pCoreOf 2 H) (hX : Hyp167 M V₀ V U S H g X T)
    (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥) :
    2 < (conjSubgroup V g ⊓ kerMOf M X).relIndex (conjSubgroup V g) := by
  by_contra hc
  have hle : (conjSubgroup V g ⊓ kerMOf M X).relIndex (conjSubgroup V g) ≤ 2 :=
    not_lt.1 hc
  have hV : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hquot : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) ≤ 1 := by
    rw [E3.relIndex_eq_two_pow hV.isPGroup (conjSubgroup V g ⊓ kerMOf M X)] at hle
    by_contra hm
    have hm' : 2 ≤ E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) := by
      omega
    have h4 : 2 ^ 2 ≤ (2 : ℕ) ^
        E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) :=
      Nat.pow_le_pow_right (by norm_num) hm'
    omega
  have h1n : 1 ≤ E3.mQuot V (U ⊔ V₀) := Cex16.one_le_n h152 hX.cex
  have h1m : 1 ≤ mSub V₀ := by
    change 1 ≤ rk V₀
    by_contra h0
    have hz : rk V₀ = 0 := by omega
    exact hX.cex.hyp.ne_bot
      ((CFSG.Quasithin.rk_eq_zero_iff_of_isPGroup hX.cex.hyp.elemAbelian₀.isPGroup).1 hz)
  have h2bar : 2 ≤ mBar M V₀ V hX.cex.hyp.h6.elemAbelian := by
    have := hX.cex.mbar
    omega
  have hmin : 2 ≤ Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
      (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) :=
    le_min (by omega) h2bar
  have hm : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) <
      Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
        (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) :=
    lt_of_le_of_lt hquot (lt_of_lt_of_le (by norm_num) hmin)
  have hcent := Hyp167.inf_centralizer_le_of_inf_eq_bot h1 hS hV₀ hX hBE
    (D := conjSubgroup V g ⊓ kerMOf M X) inf_le_left hm
  have hDcent : conjSubgroup V g ⊓ kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) := by
    intro x hx
    exact Hyp167.inf_kerMOf_le_centralizer_eSub hX ⟨hX.A_le_T hx.1, hx.2⟩
  have hEinf : eSub V₀ X T ⊓
      centralizer ((conjSubgroup V g ⊓ kerMOf M X : Subgroup G) : Set G) = eSub V₀ X T := by
    rw [inf_eq_left]
    exact (Subgroup.le_centralizer_iff (H := eSub V₀ X T)
      (K := conjSubgroup V g ⊓ kerMOf M X)).2 hDcent
  have hEA : eSub V₀ X T ≤ centralizer (conjSubgroup V g : Set G) := hEinf ▸ hcent
  have hAE : conjSubgroup V g ≤ centralizer (eSub V₀ X T : Set G) :=
    (Subgroup.le_centralizer_iff (H := eSub V₀ X T)
      (K := conjSubgroup V g)).1 hEA
  exact hX.mem.2.2.not_le_ker ((le_inf hX.mem.2.2.A_le hAE).trans
    (Hyp167.inf_centralizer_eSub_le_kerMOf hX))

end CFSG.LocalAnalysis.WeakClosure81

end
