module

public import CFSG.RankThree.GF2n.Tim79aSec2O2
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sq_centralizes_of_commute_commutator {U : Subgroup G} (hU : Assembly.IsElemAbelian 2 U)
    {y : G} (hy : y ∈ Subgroup.normalizer (U : Set G))
    (h : ∀ u ∈ U, y * ⁅u, y⁆ = ⁅u, y⁆ * y) : ∀ u ∈ U, y ^ 2 * u = u * y ^ 2 := by
  intro u hu
  have hσ : ∀ x ∈ U, y * x * y⁻¹ ∈ U := fun x hx => (Subgroup.mem_normalizer_iff.mp hy x).mp hx
  have hinv : ∀ x ∈ U, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hU.2 x hx)
  have hcomm : ∀ x ∈ U, ∀ z ∈ U, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hU.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  obtain ⟨σu, hσu⟩ : ∃ s : G, s = y * u * y⁻¹ := ⟨_, rfl⟩
  have hσuU : σu ∈ U := hσu ▸ hσ u hu
  have hσσ : y * σu * y⁻¹ ∈ U := hσ σu hσuU
  have hc : ⁅u, y⁆ = u * σu := by
    rw [commutatorElement_def, hσu, hinv u hu]
    group
  have h1 := h u hu
  have h2 : y * ⁅u, y⁆ * y⁻¹ = ⁅u, y⁆ := by
    rw [mul_inv_eq_iff_eq_mul]; exact h1
  rw [hc] at h2
  have h3 : σu * (y * σu * y⁻¹) = u * σu := by
    have : y * (u * σu) * y⁻¹ = σu * (y * σu * y⁻¹) := by rw [hσu]; group
    rw [← this]; exact h2
  have h4 : y * σu * y⁻¹ = u := by
    have h5 : σu * (y * σu * y⁻¹) = σu * u := by rw [h3, hcomm u hu σu hσuU]
    exact mul_left_cancel h5
  have h6 : y ^ 2 * u * y⁻¹ ^ 2 = u := by
    calc y ^ 2 * u * y⁻¹ ^ 2 = y * (y * u * y⁻¹) * y⁻¹ := by rw [pow_two, pow_two]; group
      _ = y * σu * y⁻¹ := by rw [hσu]
      _ = u := h4
  calc y ^ 2 * u = (y ^ 2 * u * y⁻¹ ^ 2) * y ^ 2 := by group
    _ = u * y ^ 2 := by rw [h6]

theorem centralizes_of_sq_centralizes {U : Subgroup G} {y : G} (hodd : Odd (orderOf y))
    (h : ∀ u ∈ U, y ^ 2 * u = u * y ^ 2) : ∀ u ∈ U, y * u = u * y := by
  intro u hu
  obtain ⟨k, hk⟩ := hodd
  have hy : y = (y ^ 2) ^ (k + 1) := by
    have h1 : y ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one y
    calc y = y ^ (2 * k + 1) * y := by rw [h1, one_mul]
      _ = y ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (y ^ 2) ^ (k + 1) := pow_mul y 2 (k + 1)
  have hc : Commute (y ^ 2) u := (h u hu : y ^ 2 * u = u * y ^ 2)
  rw [hy]
  exact (hc.pow_left (k + 1)).eq

variable {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem H_le_normalizer_pCore_xOf :
    H ≤ Subgroup.normalizer (inSubgroup (pCore 2) (xOf V H) : Set G) :=
  (H_le_normalizer_xOf V H).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (xOf V H))

theorem wOf_le_pCore_xOf : wOf V H ≤ inSubgroup (pCore 2) (xOf V H) := by
  refine Tim78.le_inSubgroup_pCore (wOf_le_xOf V H) ?_ ?_
  · intro x hx
    exact H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hx)
  · exact CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian

theorem centralizer_pCore_le_normalizer_conj {h : G} (hh : h ∈ H) {c : G}
    (hc' : c ∈ Subgroup.centralizer (inSubgroup (pCore 2) (xOf V H) : Set G)) :
    c ∈ Subgroup.normalizer (conjSubgroup h V : Set G) := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hc.conj_inf_wOf_ne_bot hh)
  obtain ⟨hwU, hwW⟩ := Subgroup.mem_inf.mp hw
  have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
  have hcomm : c * w = w * c :=
    (Subgroup.mem_centralizer_iff.mp hc' w (hc.wOf_le_pCore_xOf hwW)).symm
  exact Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti h) hwU hw1' hcomm

theorem odd_centralizes_conj {h : G} (hh : h ∈ H) {y : G}
    (hyX : y ∈ xOf V H)
    (hy : y ∈ Subgroup.centralizer (inSubgroup (pCore 2) (xOf V H) : Set G))
    (hodd : Odd (orderOf y)) : ∀ u ∈ conjSubgroup h V, y * u = u * y := by
  set X := xOf V H with hX
  set K := inSubgroup (pCore 2) X with hK
  obtain ⟨hK2, hKX, hXK⟩ := inSubgroup_pCore_two X
  let R : Subgroup G := Subgroup.closure {z | ∃ x ∈ X, z = x * y * x⁻¹}
  have hCx : ∀ x ∈ X, ∀ c ∈ Subgroup.centralizer (K : Set G),
      x * c * x⁻¹ ∈ Subgroup.centralizer (K : Set G) := fun x hx c hc' =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer (hXK hx)) c).mp hc'
  have hyR : y ∈ R := Subgroup.subset_closure ⟨1, X.one_mem, by group⟩
  have hRX : R ≤ X := (Subgroup.closure_le _).2 (by
    rintro z ⟨x, hx, rfl⟩
    exact X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx))
  have hRC : R ≤ Subgroup.centralizer (K : Set G) := (Subgroup.closure_le _).2 (by
    rintro z ⟨x, hx, rfl⟩
    exact hCx x hx y hy)
  have hRconj : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    intro x hx r hr
    induction hr using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨x', hx', rfl⟩ := hz
      exact Subgroup.subset_closure ⟨x * x', X.mul_mem hx hx', by group⟩
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show x * (a * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹) by group]
      exact R.mul_mem ha hb
    | inv a _ ha =>
      rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
      exact R.inv_mem ha
  have hRnorm : X ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨hRconj x hx r, fun hr => ?_⟩
    have := hRconj x⁻¹ (X.inv_mem hx) _ hr
    simpa [mul_assoc] using this
  have hRU : ∀ r ∈ R, ∀ k ∈ H, r ∈ Subgroup.normalizer (conjSubgroup k V : Set G) :=
    fun r hr k hk => hc.centralizer_pCore_le_normalizer_conj hk (hRC hr)
  set U := conjSubgroup h V with hUdef
  have hUel : Assembly.IsElemAbelian 2 U := isElemAbelian_conjSubgroup hc.elemAb h
  have hS2 : IsPGroup 2 ↥(U ⊓ R) :=
    (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hUel).to_le inf_le_left
  have hSnorm : R ≤ Subgroup.normalizer ((U ⊓ R : Subgroup G) : Set G) := fun r hr =>
    mem_normalizer_inf (hRU r hr h hh) (Subgroup.le_normalizer hr)
  have hSO : U ⊓ R ≤ inSubgroup (pCore 2) R :=
    Tim78.le_inSubgroup_pCore inf_le_right hSnorm hS2
  have hOK : inSubgroup (pCore 2) R ≤ K :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 R X hRX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRX).2 hRnorm)
  have hyN : y ∈ Subgroup.normalizer (U : Set G) :=
    hc.centralizer_pCore_le_normalizer_conj hh hy
  have hcomm : ∀ u ∈ U, y * ⁅u, y⁆ = ⁅u, y⁆ * y := by
    intro u hu
    have huX : u ∈ X := le_xOf (conjSubgroup_mem_omegaOf hh) hu
    have hc1 : ⁅u, y⁆ ∈ U := by
      have : y * u⁻¹ * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hyN u⁻¹).mp (U.inv_mem hu)
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact U.mul_mem hu (by simpa [mul_assoc] using this)
    have hc2 : ⁅u, y⁆ ∈ R := by
      have h1 : u * y * u⁻¹ ∈ R := Subgroup.subset_closure ⟨u, huX, rfl⟩
      rw [commutatorElement_def]
      exact R.mul_mem h1 (R.inv_mem hyR)
    exact (Subgroup.mem_centralizer_iff.mp hy _ (hOK (hSO ⟨hc1, hc2⟩))).symm
  exact centralizes_of_sq_centralizes hodd
    (sq_centralizes_of_commute_commutator hUel hyN hcomm)

theorem odd_centralizes_xOf {y : G} (hyX : y ∈ xOf V H)
    (hy : y ∈ Subgroup.centralizer (inSubgroup (pCore 2) (xOf V H) : Set G))
    (hodd : Odd (orderOf y)) : ∀ x ∈ xOf V H, y * x = x * y := by
  have : xOf V H ≤ Subgroup.centralizer ({y} : Set G) := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨h, hh, rfl⟩ := hU
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hc.odd_centralizes_conj hh hyX hy hodd u hu).symm
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (this hx)).symm

theorem odd_eq_one {y : G} (hyX : y ∈ xOf V H)
    (hy : y ∈ Subgroup.centralizer (inSubgroup (pCore 2) (xOf V H) : Set G))
    (hodd : Odd (orderOf y)) : y = 1 := by
  set X := xOf V H with hX
  set K := inSubgroup (pCore 2) X with hK
  have hyc := hc.odd_centralizes_xOf hyX hy hodd
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.V_ne_bot
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvX : v ∈ X := le_xOf (conjSubgroup_mem_omegaOf (one_mem H)) (by
    rw [conjSubgroup_one]; exact hv)
  have hyM : y ∈ M := hc.mem_M_of_commute hv hv1' (hyc v hvX)
  have hyP : y ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpH : p ∈ H := hc.PleH hp
    have hy'X : p * y * p⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H hpH) y).mp hyX
    have hy'C : p * y * p⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_centralizer (hc.H_le_normalizer_pCore_xOf hpH)) y).mp hy
    have hy'odd : Odd (orderOf (p * y * p⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hodd
    have hy'c := hc.odd_centralizes_xOf hy'X hy'C hy'odd
    have hcomm : Commute y (p * y * p⁻¹)⁻¹ :=
      (show Commute (p * y * p⁻¹) y from hy'c y hyX).symm.inv_right
    have hcodd : Odd (orderOf (y * (p * y * p⁻¹)⁻¹)) := by
      have hd := hcomm.orderOf_mul_dvd_lcm
      have ho1 : Odd (orderOf (p * y * p⁻¹)⁻¹) := by rw [orderOf_inv]; exact hy'odd
      exact Odd.of_dvd_nat (Odd.mul hodd ho1) (hd.trans (Nat.lcm_dvd_mul _ _))
    have hcP : y * (p * y * p⁻¹)⁻¹ ∈ P := by
      have e : y * (p * y * p⁻¹)⁻¹ = (y * p * y⁻¹) * p⁻¹ := by group
      rw [e]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hyM) p).mp hp)
        (P.inv_mem hp)
    have h1 := Tim78.eq_one_of_odd_of_isPGroup hc.isPGroup_P hcP hcodd
    have h2 : y = p * y * p⁻¹ := mul_inv_eq_one.mp h1
    calc p * y = (p * y * p⁻¹) * p := by group
      _ = y * p := by rw [← h2]
  have hyV : y ∈ V := hc.centralizer_P_eq ▸ hyP
  exact Tim78.eq_one_of_odd_of_isPGroup hc.isPGroup_V hyV hodd

theorem centralizer_pCore_xOf_le : (xOf V H) ⊓ Subgroup.centralizer
    (inSubgroup (pCore 2) (xOf V H) : Set G) ≤ inSubgroup (pCore 2) (xOf V H) := by
  set X := xOf V H with hX
  set K := inSubgroup (pCore 2) X with hK
  obtain ⟨hK2, hKX, hXK⟩ := inSubgroup_pCore_two X
  set C := X ⊓ Subgroup.centralizer (K : Set G) with hC
  have hCnorm : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (mem_normalizer_centralizer (hXK hx))
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨a, ha, -⟩ := Tim78.exists_odd_orderOf_pow (c : G)
    refine ⟨a, Subtype.ext ?_⟩
    have hmem : (c : G) ^ 2 ^ a ∈ C := C.pow_mem c.2 _
    simpa using hc.odd_eq_one hmem.1 hmem.2 ha
  exact Tim78.le_inSubgroup_pCore inf_le_left hCnorm hC2

theorem fitting_xOf : generalizedFitting ↥(xOf V H) = pCore 2 ↥(xOf V H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← isCharacteristicP_iff_generalizedFitting_eq_pCore]
  intro z hz
  have hzC : (z : G) ∈ (xOf V H) ⊓ Subgroup.centralizer
      (inSubgroup (pCore 2) (xOf V H) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hz w hw
    exact congrArg Subtype.val this
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp (hc.centralizer_pCore_xOf_le hzC)
  have : w = z := Subtype.ext hwz
  exact this ▸ hw

end MinCex

end CFSG.RankThree.GF2n.Tim79a
