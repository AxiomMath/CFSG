module

public import Mathlib.GroupTheory.Focal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Algebra.Group.Equiv.Finite
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace ZStar.TransferReduction

open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Fintype G]

@[expose] def Isolated (t : G) : Prop :=
  ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t

private def WeaklyClosedIn (t : G) (P : Subgroup G) : Prop :=
  ∀ g : G, g * t * g⁻¹ ∈ P → g * t * g⁻¹ = t

theorem mem_center_sylow_two {t : G} (ht : Isolated t) (P : Sylow 2 G)
    (htP : t ∈ P) : (⟨t, htP⟩ : P) ∈ Subgroup.center P := by
  let tp : P := ⟨t, htP⟩
  let C : Subgroup P := Subgroup.centralizer ({tp} : Set P)
  have hCself : Subgroup.normalizer (C : Set P) ≤ C := by
    intro s hs
    have htpC : tp ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
    have hconjC : s * tp * s⁻¹ ∈ C :=
      ((Subgroup.mem_normalizer_iff.mp hs tp).mp htpC)
    have hcomm : (s * tp * s⁻¹) * tp = tp * (s * tp * s⁻¹) := by
      have := (Subgroup.mem_centralizer_iff.mp hconjC tp (Set.mem_singleton tp))
      exact this.symm
    have heq : s * tp * s⁻¹ = tp := by
      apply Subtype.ext
      exact ht (s : G) (congrArg Subtype.val hcomm)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    simpa [mul_assoc] using
      (congrArg (fun x : P => x * s) heq).symm
  have hCtop : C = ⊤ := by
    let _ : Group.IsNilpotent P := P.2.isNilpotent
    apply (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent C)
    exact le_antisymm hCself Subgroup.le_normalizer
  apply Subgroup.mem_center_iff.mpr
  intro s
  have hs : s ∈ C := by rw [hCtop]; trivial
  have := Subgroup.mem_centralizer_iff.mp hs tp (Set.mem_singleton tp)
  exact this.symm

private theorem weaklyClosedIn_sylow_two {t : G} (ht : Isolated t) (P : Sylow 2 G)
    (htP : t ∈ P) : WeaklyClosedIn t P := by
  intro g hconjP
  apply ht g
  have hz := Subgroup.mem_center_iff.mp (mem_center_sylow_two ht P htP)
  exact congrArg Subtype.val (hz ⟨g * t * g⁻¹, hconjP⟩)

theorem odd_orderOf_conjugate_mul {t : G} (ht : Isolated t)
    (ht2 : t * t = 1) (g : G) :
    Odd (orderOf ((g * t * g⁻¹) * t)) := by
  let a : G := g * t * g⁻¹
  let r : G := a * t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ha2 : a * a = 1 := by
    dsimp [a]
    calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; simp
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hsemi : SemiconjBy t r r⁻¹ := by
    show t * r = r⁻¹ * t
    simp only [r, mul_inv_rev, htinv, hainv, mul_assoc]
  have hmove (k : ℕ) : t * r ^ k = (r ^ k)⁻¹ * t := by
    simpa only [inv_pow] using (hsemi.pow_right k).eq
  have hmoveInv (k : ℕ) : t * (r ^ k)⁻¹ = r ^ k * t := by
    simpa only [inv_pow, inv_inv] using (hsemi.inv_right.pow_right k).eq
  change Odd (orderOf r)
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨m, hm⟩ := even_iff_two_dvd.mp heven
  have horderPos : 0 < orderOf r := (isOfFinOrder_of_finite r).orderOf_pos
  have hmPos : 0 < m := by omega
  have hmLt : m < orderOf r := by omega
  have hrmNe : r ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hmPos.ne' hmLt
  have hrmSq : r ^ m * r ^ m = 1 := by
    have hpow := pow_orderOf_eq_one r
    rw [hm, two_mul, pow_add] at hpow
    exact hpow
  have hrmInv : (r ^ m)⁻¹ = r ^ m :=
    inv_eq_of_mul_eq_one_right hrmSq
  let u : G := r ^ m * t
  have huComm : u * t = t * u := by
    dsimp [u]
    calc
      (r ^ m * t) * t = r ^ m := by rw [mul_assoc, ht2, mul_one]
      _ = (r ^ m)⁻¹ := hrmInv.symm
      _ = t * (r ^ m * t) := by
        rw [← mul_assoc, hmove, mul_assoc, ht2, mul_one]
  have huNe : u ≠ t := by
    intro hu
    apply hrmNe
    apply mul_right_cancel (b := t)
    simpa [u] using hu
  obtain ⟨k, hmk | hmk⟩ := Nat.even_or_odd' m
  · have hconj : r ^ k * t * (r ^ k)⁻¹ = u := by
      dsimp [u]
      calc
        r ^ k * t * (r ^ k)⁻¹ = r ^ k * (t * (r ^ k)⁻¹) := by
          rw [mul_assoc]
        _ = r ^ k * (r ^ k * t) := by rw [hmoveInv]
        _ = (r ^ k * r ^ k) * t := by rw [mul_assoc]
        _ = r ^ (k + k) * t := by rw [pow_add]
        _ = r ^ m * t := by rw [hmk, two_mul]
    apply huNe
    rw [← hconj]
    apply ht (r ^ k)
    rw [hconj]
    exact huComm
  · have ha : a = r * t := by
      dsimp [r]
      rw [mul_assoc, ht2, mul_one]
    have hconjA : r ^ k * a * (r ^ k)⁻¹ = u := by
      dsimp [u]
      calc
        r ^ k * a * (r ^ k)⁻¹ =
            (r ^ k * r) * (t * (r ^ k)⁻¹) := by rw [ha]; simp only [mul_assoc]
        _ = (r ^ k * r) * (r ^ k * t) := by rw [hmoveInv]
        _ = (r ^ k * r * r ^ k) * t := by simp only [mul_assoc]
        _ = r ^ (k + 1 + k) * t := by rw [← pow_succ, ← pow_add]
        _ = r ^ m * t := by rw [hmk]; congr 2 <;> omega
    have hconj : (r ^ k * g) * t * (r ^ k * g)⁻¹ = u := by
      calc
        (r ^ k * g) * t * (r ^ k * g)⁻¹ =
            r ^ k * (g * t * g⁻¹) * (r ^ k)⁻¹ := by group
        _ = r ^ k * a * (r ^ k)⁻¹ := by rfl
        _ = u := hconjA
    apply huNe
    rw [← hconj]
    apply ht (r ^ k * g)
    rw [hconj]
    exact huComm

theorem normalizer_le_centralizer_singleton {t : G} (ht : Isolated t)
    (P : Sylow 2 G) (htP : t ∈ P) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]
  have hconjP : g * t * g⁻¹ ∈ P :=
    ((Subgroup.mem_normalizer_iff.mp hg t).mp htP)
  have heq := weaklyClosedIn_sylow_two ht P htP g hconjP
  simpa [mul_assoc] using
    (congrArg (fun x : G => x * g) heq).symm

theorem zStar_of_isCyclic_sylow_two {t : G} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) (P : Sylow 2 G) [IsCyclic P] :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  have htOrder : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      simpa [pow_two] using ht2
    have hpos : 0 < orderOf t := (isOfFinOrder_of_finite t).orderOf_pos
    have hneOne : orderOf t ≠ 1 := by
      intro hone
      exact ht1 (orderOf_eq_one_iff.mp hone)
    have hle : orderOf t ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  have htwoCard : 2 ∣ Nat.card G := by
    simpa [htOrder] using orderOf_dvd_natCard t
  have hminFac : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr htwoCard
  let hnorm : Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) :=
    IsCyclic.normalizer_le_centralizer hminFac
      (inferInstance : IsCyclic P)
  let f : G →* P := MonoidHom.transferSylow P hnorm
  let N : Subgroup G := f.ker
  have hcomplement : N.IsComplement' (P : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hnotEven : ¬Even (Nat.card N) := by
    rw [even_iff_two_dvd]
    have hnot := Sylow.not_dvd_index P
    rw [hcomplement.index_eq_card] at hnot
    exact hnot
  have hodd : Odd (Nat.card N) := Nat.not_even_iff_odd.mp hnotEven
  refine ⟨N, inferInstance, hodd, ?_⟩
  intro g
  change f (g * t * g⁻¹ * t⁻¹) = 1
  simp only [map_mul, map_inv]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' (f g) (f t))

section Focal

variable (P : Sylow 2 G)

def FocalTerminal (t : G) : Prop :=
  Subgroup.zpowers (P.transferFocal t) = ⊤

private theorem exists_proper_normal_overgroup_of_not_focalTerminal (t : G)
    (hterminal : ¬ FocalTerminal P t) :
    ∃ H : Subgroup G, H.Normal ∧ H < ⊤ ∧ t ∈ H := by
  let V := P.transferFocal
  let A : Subgroup (P ⧸ P.focalSubgroupOf) := Subgroup.zpowers (V t)
  let H : Subgroup G := A.comap V
  let _ : A.Normal := Subgroup.normal_of_isMulCommutative A
  refine ⟨H, Subgroup.normal_comap V, ?_, ?_⟩
  · apply lt_top_iff_ne_top.mpr
    intro hH
    apply hterminal
    apply le_antisymm le_top
    intro q hq
    obtain ⟨g, rfl⟩ := Subgroup.transferFocal_surjective P q
    have hgH : g ∈ H := by rw [hH]; exact Subgroup.mem_top g
    exact hgH
  · exact Subgroup.mem_zpowers (V t)

theorem focalTerminal_of_no_proper_normal_overgroup (t : G)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤) :
    FocalTerminal P t := by
  by_contra hterminal
  obtain ⟨H, hHnormal, hHproper, htH⟩ :=
    exists_proper_normal_overgroup_of_not_focalTerminal P t hterminal
  exact hHproper.ne (hmin H hHnormal htH)

private theorem card_focalQuotient_le_two_of_terminal {t : G} (ht2 : t * t = 1)
    (hterminal : FocalTerminal P t) :
    Nat.card (P ⧸ P.focalSubgroupOf) ≤ 2 := by
  have hsq : (P.transferFocal t) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, ht2, map_one]
  have hdvd : orderOf (P.transferFocal t) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  calc
    Nat.card (P ⧸ P.focalSubgroupOf) =
        Nat.card (⊤ : Subgroup (P ⧸ P.focalSubgroupOf)) := by simp
    _ = Nat.card (Subgroup.zpowers (P.transferFocal t)) :=
      congrArg (fun S : Subgroup (P ⧸ P.focalSubgroupOf) => Nat.card S) hterminal.symm
    _ = orderOf (P.transferFocal t) := Nat.card_zpowers _
    _ ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdvd

theorem card_focalQuotient_eq_one_or_two_of_terminal {t : G} (ht2 : t * t = 1)
    (hterminal : FocalTerminal P t) :
    Nat.card (P ⧸ P.focalSubgroupOf) = 1 ∨
      Nat.card (P ⧸ P.focalSubgroupOf) = 2 := by
  have hpos : 0 < Nat.card (P ⧸ P.focalSubgroupOf) := Nat.card_pos
  have hle := card_focalQuotient_le_two_of_terminal P ht2 hterminal
  omega

end Focal

theorem commutator_eq_top_or_index_eq_two_of_no_proper_normal_overgroup
    {t : G} (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤) :
    commutator G = ⊤ ∨ (commutator G).index = 2 := by
  let H : Subgroup G := commutator G ⊔ Subgroup.zpowers t
  have hHnormal : H.Normal :=
    Subgroup.Normal.of_commutator_le G (show commutator G ≤ H from le_sup_left)
  have htH : t ∈ H := by
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hHtop : H = ⊤ := hmin H hHnormal htH
  have ht2z : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact ht2
  have hindex_dvd : (commutator G).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨t, fun b => ?_⟩
    have hbH : b ∈ H := by
      rw [hHtop]
      exact Subgroup.mem_top b
    change b ∈ commutator G ⊔ Subgroup.zpowers t at hbH
    rw [Subgroup.mem_sup_of_normal_left] at hbH
    obtain ⟨d, hd, z, hz, hdz⟩ := hbH
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
    · right
      have hpow : t ^ n = 1 := by
        rw [hk, zpow_mul, ht2z, one_zpow]
      rw [hpow, mul_one] at hdz
      rw [← hdz]
      exact hd
    · left
      have hpow : t ^ n = t := by
        rw [hk, zpow_add, zpow_mul, ht2z, one_zpow, one_mul, zpow_one]
      rw [hpow] at hdz
      have hbt : b * t = d := by
        rw [← hdz, mul_assoc, ht2, mul_one]
      rw [hbt]
      exact hd
  have hindex_ne : (commutator G).index ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero
  have hindex_le : (commutator G).index ≤ 2 :=
    Nat.le_of_dvd (by decide : 0 < 2) hindex_dvd
  rcases (show (commutator G).index = 1 ∨ (commutator G).index = 2 by omega) with
    hindex_one | hindex_two
  · left
    exact Subgroup.index_eq_one.mp hindex_one
  · exact Or.inr hindex_two

theorem commutator_eq_top_of_card_focalQuotient_eq_one
    (P : Sylow 2 G) {t : G} (htP : t ∈ P)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤)
    (hcard : Nat.card (P ⧸ P.focalSubgroupOf) = 1) :
    commutator G = ⊤ := by
  have hfocalIndex : P.focalSubgroupOf.index = 1 := by
    rw [Subgroup.index_eq_card]
    exact hcard
  have hfocalTop : P.focalSubgroupOf = ⊤ :=
    Subgroup.index_eq_one.mp hfocalIndex
  have htFocalOf : (⟨t, htP⟩ : P) ∈ P.focalSubgroupOf := by
    rw [hfocalTop]
    trivial
  have htFocal : t ∈ (P : Subgroup G).focalSubgroup := by
    rw [Subgroup.focalSubgroupOf_def] at htFocalOf
    exact htFocalOf
  have htComm : t ∈ commutator G := by
    have htInf : t ∈ commutator G ⊓ (P : Subgroup G) := by
      rw [Subgroup.commutator_inf_eq_focalSubgroup P]
      exact htFocal
    exact htInf.1
  exact hmin (commutator G) inferInstance htComm

theorem commutator_index_eq_two_of_card_focalQuotient_eq_two
    (P : Sylow 2 G) {t : G} (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤)
    (hcard : Nat.card (P ⧸ P.focalSubgroupOf) = 2) :
    (commutator G).index = 2 := by
  rcases commutator_eq_top_or_index_eq_two_of_no_proper_normal_overgroup ht2 hmin with
    hperfect | hindex
  · have hfocal : (P : Subgroup G).focalSubgroup = (P : Subgroup G) := by
      rw [← Subgroup.commutator_inf_eq_focalSubgroup P, hperfect, top_inf_eq]
    have hfocalOf : P.focalSubgroupOf = ⊤ := by
      rw [Subgroup.focalSubgroupOf_def, hfocal]
      ext x
      simp
    have hone : Nat.card (P ⧸ P.focalSubgroupOf) = 1 := by
      rw [hfocalOf]
      simp
    omega
  · exact hindex

section AbelianSylow

universe v

private noncomputable def actionNorm (A : Type u) (M : Type v)
    [Group A] [Fintype A] [CommGroup M] [MulDistribMulAction A M] : M →* M :=
  MonoidHom.toAdditive.symm
    (Representation.ofMulDistribMulAction A M).norm.toAddMonoidHom

private theorem actionNorm_apply (A : Type u) (M : Type v)
    [Group A] [Fintype A] [CommGroup M] [MulDistribMulAction A M] (x : M) :
    actionNorm A M x = ∏ a : A, a • x := by
  simp [actionNorm, Representation.norm]

private theorem actionNorm_smul (A : Type u) (M : Type v)
    [Group A] [Fintype A] [CommGroup M] [MulDistribMulAction A M]
    (a : A) (x : M) : actionNorm A M (a • x) = actionNorm A M x := by
  change Additive.toMul
      ((Representation.ofMulDistribMulAction A M).norm
        (Additive.ofMul (a • x))) =
    Additive.toMul
      ((Representation.ofMulDistribMulAction A M).norm (Additive.ofMul x))
  exact congrArg Additive.toMul
    (Representation.norm_self_apply
      (Representation.ofMulDistribMulAction A M) a (Additive.ofMul x))

private theorem actionNorm_inv_mul_smul (A : Type u) (M : Type v)
    [Group A] [Fintype A] [CommGroup M] [MulDistribMulAction A M]
    (a : A) (x : M) : actionNorm A M (x⁻¹ * a • x) = 1 := by
  rw [map_mul, map_inv, actionNorm_smul, inv_mul_cancel]

private theorem actionNorm_of_fixed (A : Type u) (M : Type v)
    [Group A] [Fintype A] [CommGroup M] [MulDistribMulAction A M]
    (x : M) (hx : ∀ a : A, a • x = x) :
    actionNorm A M x = x ^ Nat.card A := by
  rw [actionNorm_apply]
  simp_rw [hx]
  simp

private theorem not_mem_focalSubgroupOf_of_isMulCommutative_sylow_two
    {t : G} (ht : Isolated t) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ P) [IsMulCommutative P] :
    (⟨t, htP⟩ : P) ∉ P.focalSubgroupOf := by
  classical
  let : CommGroup P := IsMulCommutative.instCommGroup
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  let PN : Subgroup N := (P : Subgroup G).subgroupOf N
  let f : N →* MulAut P := (P : Subgroup G).normalizerMonoidHom
  have hPNnormal : PN.Normal := by
    constructor
    intro p hp n
    change (n : G) * (p : G) * (n : G)⁻¹ ∈ P
    exact ((Subgroup.mem_normalizer_iff.mp n.property (p : G)).mp hp)
  let _ : PN.Normal := hPNnormal
  have hPNker : PN ≤ f.ker := by
    rw [Subgroup.normalizerMonoidHom_ker]
    intro p hp
    change (p : G) ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (congrArg Subtype.val
      (mul_comm (⟨p, hp⟩ : P) (⟨x, hx⟩ : P))).symm
  let qf : (N ⧸ PN) →* MulAut P := QuotientGroup.lift PN f hPNker
  let A : Subgroup (MulAut P) := qf.range
  have hAodd : Odd (Nat.card A) := by
    rw [← Nat.not_even_iff_odd]
    rw [even_iff_two_dvd]
    intro htwo
    apply P.not_dvd_index
    apply htwo.trans
    apply (Subgroup.card_range_dvd qf).trans
    change Nat.card (N ⧸ PN) ∣ (P : Subgroup G).index
    change (P : Subgroup G).relIndex N ∣ (P : Subgroup G).index
    exact Subgroup.relIndex_dvd_index_of_le hPN
  let tp : P := ⟨t, htP⟩
  have hfixf (n : N) : f n tp = tp := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact weaklyClosedIn_sylow_two ht P htP (n : G)
      ((Subgroup.mem_normalizer_iff.mp n.property t).mp htP)
  have hfixA (a : A) : (a : MulAut P) tp = tp := by
    obtain ⟨q, hq⟩ := a.property
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective PN q
    rw [← hq]
    exact hfixf n
  let nu : P →* P := actionNorm A P
  have hnut : nu tp = tp := by
    rw [actionNorm_of_fixed A P tp (fun a => by exact hfixA a)]
    obtain ⟨k, hk⟩ := hAodd
    rw [hk, pow_add, pow_mul]
    change (tp ^ 2) ^ k * tp ^ 1 = tp
    have htp2 : tp ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using ht2
    rw [htp2, one_pow, one_mul, pow_one]
  have hfocalKer : P.focalSubgroupOf ≤ nu.ker := by
    rw [Subgroup.focalSubgroupOf_eq_closure, Subgroup.closure_le]
    intro y hy
    obtain ⟨x, hxP, w, hy⟩ := hy
    have hconjP : w * x⁻¹ * w⁻¹ ∈ P := by
      have hshape : w * x⁻¹ * w⁻¹ = x⁻¹ * (y : G) := by
        rw [hy]
        group
      rw [hshape]
      exact P.mul_mem (P.inv_mem hxP) y.property
    have hconjP' : (w⁻¹)⁻¹ * x⁻¹ * w⁻¹ ∈ P := by
      simpa using hconjP
    obtain ⟨n, hnN, hn⟩ :=
      Sylow.conj_eq_normalizer_conj_of_mem P x⁻¹ w⁻¹
        (P.inv_mem hxP) hconjP'
    let nn : N := ⟨n, hnN⟩
    let qa : N ⧸ PN := QuotientGroup.mk' PN nn⁻¹
    let a : A := ⟨qf qa, ⟨qa, rfl⟩⟩
    have haction : a • (⟨x⁻¹, P.inv_mem hxP⟩ : P) =
        ⟨n⁻¹ * x⁻¹ * n, by
          change n⁻¹ * x⁻¹ * n ∈ (P : Subgroup G)
          simpa only [inv_inv] using
            ((Subgroup.mem_normalizer_iff.mp (N.inv_mem hnN) x⁻¹).mp
              (P.inv_mem hxP))⟩ := by
      rw [Subgroup.smul_def, MulAut.smul_def]
      dsimp only [a]
      apply Subtype.ext
      rw [show qf qa = f nn⁻¹ by rfl]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp [nn]
    change nu y = 1
    have hyshape : y = (⟨x⁻¹, P.inv_mem hxP⟩ : P)⁻¹ *
        a • (⟨x⁻¹, P.inv_mem hxP⟩ : P) := by
      apply Subtype.ext
      rw [haction]
      change (y : G) = x⁻¹⁻¹ * (n⁻¹ * x⁻¹ * n)
      rw [hy]
      rw [← hn]
      group
    rw [hyshape]
    exact actionNorm_inv_mul_smul A P a ⟨x⁻¹, P.inv_mem hxP⟩
  intro htF
  have htker : tp ∈ nu.ker := hfocalKer htF
  have hnuone : nu tp = 1 := MonoidHom.mem_ker.mp htker
  apply ht1
  rw [hnut] at hnuone
  exact congrArg Subtype.val hnuone

private theorem commutator_ne_top_of_isMulCommutative_sylow_two
    {t : G} (ht : Isolated t) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ P) [IsMulCommutative P] :
    commutator G ≠ ⊤ := by
  intro hperfect
  have hnot :=
    not_mem_focalSubgroupOf_of_isMulCommutative_sylow_two
      ht ht1 ht2 P htP
  apply hnot
  rw [Subgroup.focalSubgroupOf_def]
  change t ∈ (P : Subgroup G).focalSubgroup
  rw [← Subgroup.commutator_inf_eq_focalSubgroup P, hperfect, top_inf_eq]
  exact htP

theorem commutator_index_eq_two_of_terminal_of_isMulCommutative_sylow_two
    {t : G} (ht : Isolated t) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (P : Sylow 2 G) (htP : t ∈ P) [IsMulCommutative P]
    (hmin : ∀ H : Subgroup G, H.Normal → t ∈ H → H = ⊤) :
    (commutator G).index = 2 := by
  rcases commutator_eq_top_or_index_eq_two_of_no_proper_normal_overgroup
      ht2 hmin with hperfect | hindex
  · exact (commutator_ne_top_of_isMulCommutative_sylow_two
      ht ht1 ht2 P htP hperfect).elim
  · exact hindex

end AbelianSylow

section NormalOvergroup

theorem odd_card_sup_of_le_normalizer {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B)) :
    Odd (Nat.card ↥(A ⊔ B)) := by
  rw [sup_comm]
  let U : Subgroup G := B ⊔ A
  let A' : Subgroup U := A.subgroupOf U
  let _ : A'.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBA
  let inclB : B →* U := Subgroup.inclusion le_sup_left
  let f : B →* U ⧸ A' := (QuotientGroup.mk' A').comp inclB
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective A' q
    have hu : (u : G) ∈ (B : Set G) * (A : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B A hBA]
      exact u.property
    obtain ⟨b, hb, a, ha, hab⟩ := hu
    refine ⟨⟨b, hb⟩, ?_⟩
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((b : G) / (u : G) : G) ∈ A
    have hconj := Subgroup.le_normalizer_iff.mp hBA b hb a⁻¹ (A.inv_mem ha)
    rw [← hab]
    simpa [div_eq_mul_inv, mul_assoc] using hconj
  have hquot : Odd (Nat.card (U ⧸ A')) :=
    hB.of_dvd_nat (Subgroup.card_dvd_of_surjective hf)
  have hA' : Nat.card A' = Nat.card A := by
    simpa [A', U] using
      Nat.card_congr (A.subgroupOfEquivOfLe (show A ≤ B ⊔ A from le_sup_right))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup A', hA']
  exact hquot.mul hA

private theorem odd_card_finset_sup {ι : Type*} (s : Finset ι) (A : ι → Subgroup G)
    (hnormal : ∀ i ∈ s, (A i).Normal)
    (hodd : ∀ i ∈ s, Odd (Nat.card (A i))) :
    Odd (Nat.card ↥(s.sup A)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sup_insert]
      have : (A a).Normal := hnormal a (by simp)
      apply odd_card_sup_of_le_normalizer
      · exact Subgroup.le_normalizer_of_normal
      · exact hodd a (by simp)
      · apply ih
        · intro i hi
          exact hnormal i (by simp [hi])
        · intro i hi
          exact hodd i (by simp [hi])

private theorem odd_card_iSup {ι : Type*} [Fintype ι] (A : ι → Subgroup G)
    (hnormal : ∀ i, (A i).Normal)
    (hodd : ∀ i, Odd (Nat.card (A i))) :
    Odd (Nat.card ↥(⨆ i, A i)) := by
  classical
  rw [← Finset.sup_univ_eq_iSup A]
  exact odd_card_finset_sup Finset.univ A
    (by simpa using hnormal) (by simpa using hodd)

theorem odd_card_normalClosure_of_normal_subgroupOf
    (H K : Subgroup G) [H.Normal] (hKH : K ≤ H)
    (hKnormal : (K.subgroupOf H).Normal)
    (hKodd : Odd (Nat.card K)) :
    Odd (Nat.card (Subgroup.normalClosure (K : Set G))) := by
  classical
  let K_H : Subgroup H := K.subgroupOf H
  let D : G → Subgroup H := fun g =>
    Subgroup.map (MulAut.conjNormal (H := H) g) K_H
  let C : G → Subgroup G := fun g =>
    Subgroup.map (MulAut.conj g) K
  have hmap (g : G) : Subgroup.map H.subtype (D g) = C g := by
    have hcomp : H.subtype.comp (MulAut.conjNormal (H := H) g) =
        (MulAut.conj g).toMonoidHom.comp H.subtype := by
      ext x
      rfl
    calc
      Subgroup.map H.subtype (D g) =
          Subgroup.map (H.subtype.comp (MulAut.conjNormal (H := H) g)) K_H := by
            exact Subgroup.map_map K_H H.subtype
              (MulAut.conjNormal (H := H) g).toMonoidHom
      _ = Subgroup.map ((MulAut.conj g).toMonoidHom.comp H.subtype) K_H := by
            rw [hcomp]
      _ = Subgroup.map (MulAut.conj g) (Subgroup.map H.subtype K_H) := by
            exact (Subgroup.map_map K_H (MulAut.conj g).toMonoidHom H.subtype).symm
      _ = C g := by
            rw [Subgroup.map_subgroupOf_eq_of_le hKH]
  have hDnormal (g : G) : (D g).Normal := by
    exact MulEquiv.normal_map_iff.mpr hKnormal
  have hK_H_card : Nat.card K_H = Nat.card K := by
    exact Nat.card_congr (K.subgroupOfEquivOfLe hKH)
  have hDodd (g : G) : Odd (Nat.card (D g)) := by
    rw [show Nat.card (D g) = Nat.card K_H by
      exact Subgroup.card_map_of_injective
        (MulAut.conjNormal (H := H) g).injective]
    rw [hK_H_card]
    exact hKodd
  have hoddSup : Odd (Nat.card ↥(⨆ g, D g)) :=
    odd_card_iSup D hDnormal hDodd
  have hconjsets : Group.conjugatesOfSet (K : Set G) =
      ⋃ g : G, (C g : Set G) := by
    ext x
    constructor
    · intro hx
      rw [Group.mem_conjugatesOfSet_iff] at hx
      obtain ⟨a, ha, hax⟩ := hx
      rw [isConj_iff] at hax
      obtain ⟨g, hg⟩ := hax
      rw [Set.mem_iUnion]
      refine ⟨g, ?_⟩
      change x ∈ Subgroup.map (MulAut.conj g) K
      exact ⟨a, ha, by simpa [MulAut.conj_apply] using hg⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨g, hx⟩ := hx
      change x ∈ Subgroup.map (MulAut.conj g) K at hx
      obtain ⟨a, ha, hax⟩ := hx
      rw [Group.mem_conjugatesOfSet_iff]
      refine ⟨a, ha, ?_⟩
      rw [isConj_iff]
      exact ⟨g, by simpa [MulAut.conj_apply] using hax⟩
  have hnormalClosure : Subgroup.normalClosure (K : Set G) = ⨆ g, C g := by
    rw [Subgroup.normalClosure, hconjsets, ← Subgroup.iSup_eq_closure C]
  have hmapSup : Subgroup.map H.subtype (⨆ g, D g) = ⨆ g, C g := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hmap
  rw [hnormalClosure, ← hmapSup, Subgroup.card_subtype]
  exact hoddSup

theorem exists_normal_smul_sylow_eq_of_quotient_isPGroup
    {p : ℕ} [Fact (Nat.Prime p)] (O : Subgroup G) [O.Normal]
    (hquot : IsPGroup p (G ⧸ O)) (S T : Sylow p G) :
    ∃ o : O, (o : G) • S = T := by
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective O
  let SQ : Sylow p (G ⧸ O) := Sylow.mapSurjective hqsurj S
  have hSQtop : (SQ : Subgroup (G ⧸ O)) = ⊤ := by
    exact (SQ.is_maximal' (hquot.to_subgroup ⊤) le_top).symm
  have hmaptop : Subgroup.map q (S : Subgroup G) = ⊤ := by
    rw [← Sylow.coe_mapSurjective hqsurj S]
    exact hSQtop
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq G S T
  have hql_mem : q l ∈ Subgroup.map q (S : Subgroup G) := by
    rw [hmaptop]
    trivial
  obtain ⟨s, hs, hqs⟩ := hql_mem
  have ho : l * s⁻¹ ∈ O := by
    have : l / s ∈ O := QuotientGroup.eq_iff_div_mem.mp hqs.symm
    simpa [div_eq_mul_inv] using this
  let o : O := ⟨l * s⁻¹, ho⟩
  refine ⟨o, ?_⟩
  have hsfix : s • S = S := by
    apply Sylow.smul_eq_iff_mem_normalizer.mpr
    exact Subgroup.le_normalizer hs
  have hact := congrArg (fun P : Sylow p G => (o : G) • P) hsfix
  have hol : l • S = (o : G) • S := by
    simpa [← mul_smul, o, mul_assoc] using hact
  exact hol.symm.trans hl

theorem isPGroup_zpowers_two_of_sq_eq_one {X : Type*} [Group X]
    (x : X) (hx : x * x = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  rw [Nat.card_zpowers, pow_one]
  apply orderOf_dvd_of_pow_eq_one
  simpa [pow_two] using hx

private theorem zpowers_le_normalizer_zpowers_of_commute {X : Type*} [Group X]
    {x y : X} (hxy : Commute y x) :
    Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha b hb
  rw [Subgroup.mem_zpowers_iff] at ha hb
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have hpow : Commute (y ^ m) (x ^ n) := hxy.zpow_zpow m n
  have heq : y ^ m * x ^ n * (y ^ m)⁻¹ = x ^ n := by
    rw [hpow.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [heq]
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨n, rfl⟩

private theorem exists_ker_smul_sylow_eq_of_isPGroup
    {p : ℕ} [Fact (Nat.Prime p)] {Q : Type*} [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) (hQ : IsPGroup p Q)
    (S T : Sylow p G) : ∃ k : f.ker, (k : G) • S = T := by
  let SQ : Sylow p Q := Sylow.mapSurjective hf S
  have hSQtop : (SQ : Subgroup Q) = ⊤ := by
    exact (SQ.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have hmaptop : Subgroup.map f (S : Subgroup G) = ⊤ := by
    rw [← Sylow.coe_mapSurjective hf S]
    exact hSQtop
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq G S T
  have hfl_mem : f l ∈ Subgroup.map f (S : Subgroup G) := by
    rw [hmaptop]
    trivial
  obtain ⟨s, hs, hfs⟩ := hfl_mem
  have hk : l * s⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfs.symm]
    exact mul_inv_cancel (f s)
  let k : f.ker := ⟨l * s⁻¹, hk⟩
  refine ⟨k, ?_⟩
  have hsfix : s • S = S := by
    apply Sylow.smul_eq_iff_mem_normalizer.mpr
    exact Subgroup.le_normalizer hs
  have hact := congrArg (fun P : Sylow p G => (k : G) • P) hsfix
  have hkl : l • S = (k : G) • S := by
    simpa [← mul_smul, k, mul_assoc] using hact
  exact hkl.symm.trans hl

theorem normal_overgroup_lifting {t : G}
    (ht : Isolated t) (ht2 : t * t = 1)
    (H K : Subgroup G) [H.Normal] (htH : t ∈ H) (hKH : K ≤ H)
    (hKnormal : (K.subgroupOf H).Normal) (hKodd : Odd (Nat.card K))
    (hcentral : ∀ h : H, (h : G) * t * (h : G)⁻¹ * t⁻¹ ∈ K) :
    ∃ O : Subgroup G, O.Normal ∧ Odd (Nat.card O) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ O := by
  classical
  let O : Subgroup G := Subgroup.normalClosure (K : Set G)
  let _ : O.Normal := Subgroup.normalClosure_normal
  have hKO : K ≤ O := Subgroup.le_normalClosure
  have hOodd : Odd (Nat.card O) :=
    odd_card_normalClosure_of_normal_subgroupOf H K hKH hKnormal hKodd
  refine ⟨O, inferInstance, hOodd, ?_⟩
  intro g
  let s : G := g * t * g⁻¹
  have hsH : s ∈ H := by
    exact (inferInstance : H.Normal).conj_mem t htH g
  have hs2 : s * s = 1 := by
    dsimp [s]
    calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; simp
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  have hqt2 : q t * q t = 1 := by
    rw [← map_mul, ht2, map_one]
  have hqs2 : q s * q s = 1 := by
    rw [← map_mul, hs2, map_one]
  have hstO : s * t * s⁻¹ * t⁻¹ ∈ O :=
    hKO (hcentral ⟨s, hsH⟩)
  have hqst : q (s * t) = q (t * s) := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa [div_eq_mul_inv, mul_assoc] using hstO
  have hcomm : Commute (q s) (q t) := by
    show q s * q t = q t * q s
    simpa only [map_mul] using hqst
  let A : Subgroup (G ⧸ O) := Subgroup.zpowers (q t)
  let B : Subgroup (G ⧸ O) := Subgroup.zpowers (q s)
  let R : Subgroup (G ⧸ O) := A ⊔ B
  have hA : IsPGroup 2 A := isPGroup_zpowers_two_of_sq_eq_one (q t) hqt2
  have hB : IsPGroup 2 B := isPGroup_zpowers_two_of_sq_eq_one (q s) hqs2
  have hBA : B ≤ Subgroup.normalizer (A : Set (G ⧸ O)) :=
    zpowers_le_normalizer_zpowers_of_commute hcomm
  have hR : IsPGroup 2 R := IsPGroup.to_sup_of_normal_left' hA hB hBA
  let L : Subgroup G := Subgroup.comap q R
  have htL : t ∈ L := by
    change q t ∈ R
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers (q t))
  have hsL : s ∈ L := by
    change q s ∈ R
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (q s))
  let f : L →* R := (q.comp L.subtype).codRestrict R (fun x => x.property)
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (r : G ⧸ O)
    have hxL : x ∈ L := by
      change q x ∈ R
      rw [hx]
      exact r.property
    refine ⟨⟨x, hxL⟩, ?_⟩
    apply Subtype.ext
    exact hx
  let tl : L := ⟨t, htL⟩
  let sl : L := ⟨s, hsL⟩
  have htl2 : tl * tl = 1 := by
    apply Subtype.ext
    exact ht2
  have hsl2 : sl * sl = 1 := by
    apply Subtype.ext
    exact hs2
  have htc : IsPGroup 2 (Subgroup.zpowers tl) :=
    isPGroup_zpowers_two_of_sq_eq_one tl htl2
  have hsc : IsPGroup 2 (Subgroup.zpowers sl) :=
    isPGroup_zpowers_two_of_sq_eq_one sl hsl2
  obtain ⟨ST, hST⟩ := htc.exists_le_sylow
  obtain ⟨SS, hSS⟩ := hsc.exists_le_sylow
  obtain ⟨k, hk⟩ := exists_ker_smul_sylow_eq_of_isPGroup f hf hR SS ST
  have hslSS : sl ∈ (SS : Subgroup L) :=
    hSS (Subgroup.mem_zpowers sl)
  have hconjST : (k : L) * sl * (k : L)⁻¹ ∈ (ST : Subgroup L) := by
    have hmapped : (k : L) * sl * (k : L)⁻¹ ∈
        ((k : L) • SS : Sylow 2 L) := by
      exact (Sylow.equivSMul SS (k : L) ⟨sl, hslSS⟩).property
    rw [hk] at hmapped
    exact hmapped
  let M : Subgroup G := Subgroup.map L.subtype (ST : Subgroup L)
  have hM : IsPGroup 2 M := ST.isPGroup'.map L.subtype
  obtain ⟨P, hMP⟩ := hM.exists_le_sylow
  have htlST : tl ∈ (ST : Subgroup L) :=
    hST (Subgroup.mem_zpowers tl)
  have htP : t ∈ P := by
    apply hMP
    exact ⟨tl, htlST, rfl⟩
  let kg : G := ((k : L) : G)
  have hconjP : kg * s * kg⁻¹ ∈ P := by
    apply hMP
    refine ⟨(k : L) * sl * (k : L)⁻¹, hconjST, ?_⟩
    rfl
  have hshape : (kg * g) * t * (kg * g)⁻¹ = kg * s * kg⁻¹ := by
    dsimp [s]
    group
  have hconjeq : kg * s * kg⁻¹ = t := by
    have hmem : (kg * g) * t * (kg * g)⁻¹ ∈ (P : Subgroup G) := by
      rw [hshape]
      exact hconjP
    have hweak := weaklyClosedIn_sylow_two ht P htP (kg * g) hmem
    simpa only [hshape] using hweak
  have hqkg : q kg = 1 := by
    have hk1 : f (k : L) = 1 := MonoidHom.mem_ker.mp k.property
    have hk1' := congrArg Subtype.val hk1
    change q (((k : L) : G)) = 1 at hk1'
    simpa [kg] using hk1'
  have hqeq : q s = q t := by
    have heq := congrArg q hconjeq
    simpa [map_mul, map_inv, hqkg] using heq
  have hdiv : s / t ∈ O := QuotientGroup.eq_iff_div_mem.mp hqeq
  simpa [s, div_eq_mul_inv] using hdiv

theorem zStar_of_commutator_terminal
    (hterminal :
      ∀ {X : Type u} [Group X] [Fintype X] {x : X},
        Isolated x → x * x = 1 →
        (∀ H : Subgroup X, H.Normal → x ∈ H → H = ⊤) →
        (commutator X = ⊤ ∨ (commutator X).index = 2) →
        ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧
          ∀ g : X, g * x * g⁻¹ * x⁻¹ ∈ N)
    {t : G} (ht : Isolated t) (ht2 : t * t = 1) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N := by
  let rec go (X : Type u) [Group X] [Fintype X] (x : X)
      (hx : Isolated x) (hx2 : x * x = 1) :
      ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧
        ∀ g : X, g * x * g⁻¹ * x⁻¹ ∈ N := by
    classical
    by_cases hmin : ∀ H : Subgroup X, H.Normal → x ∈ H → H = ⊤
    · exact hterminal hx hx2 hmin
        (commutator_eq_top_or_index_eq_two_of_no_proper_normal_overgroup hx2 hmin)
    · push Not at hmin
      obtain ⟨H, hHnormal, hxH, hHne⟩ := hmin
      let _ : H.Normal := hHnormal
      let xH : H := ⟨x, hxH⟩
      have hxH2 : xH * xH = 1 := by
        apply Subtype.ext
        exact hx2
      have hisolatedH : Isolated xH := by
        intro h hh
        apply Subtype.ext
        exact hx (h : X) (congrArg Subtype.val hh)
      have hcard : Nat.card H < Nat.card X := by
        have hle : Nat.card H ≤ Nat.card X := Subgroup.card_le_card_group H
        apply lt_of_le_of_ne hle
        intro heq
        exact hHne ((Subgroup.card_eq_iff_eq_top H).mp heq)
      obtain ⟨K, hKnormal, hKodd, hKcomm⟩ :=
        go H xH hisolatedH hxH2
      let KX : Subgroup X := Subgroup.map H.subtype K
      have hKXH : KX ≤ H := Subgroup.map_subtype_le K
      have hrestrict : KX.subgroupOf H = K := by
        apply Subgroup.map_subtype_inj.mp
        rw [Subgroup.map_subgroupOf_eq_of_le hKXH]
      have hKXnormal : (KX.subgroupOf H).Normal := by
        rw [hrestrict]
        exact hKnormal
      have hKXodd : Odd (Nat.card KX) := by
        rw [show Nat.card KX = Nat.card K by
          exact Subgroup.card_subtype H K]
        exact hKodd
      have hKXcomm :
          ∀ h : H, (h : X) * x * (h : X)⁻¹ * x⁻¹ ∈ KX := by
        intro h
        refine ⟨h * xH * h⁻¹ * xH⁻¹, hKcomm h, ?_⟩
        rfl
      exact normal_overgroup_lifting hx hx2 H KX hxH hKXH hKXnormal hKXodd hKXcomm
  termination_by Nat.card X
  decreasing_by
    simpa only [Nat.card_eq_fintype_card] using hcard
  exact go G t ht ht2

end NormalOvergroup

end ZStar.TransferReduction

end CFSG
