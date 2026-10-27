module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCenterOfOddQuotientKernel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowReflectedToriCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2LowOddCyclicCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise
open scoped commutatorElement
open scoped IsMulCommutative

namespace CFSG.GorensteinWalter

universe u



/-! ## Model facts for the reflected-torus containment -/

/-- In the odd `PGL₂` model, the reflected torus `R = U ∩ PGL₂'` has
half the order of the torus `U`. -/
public theorem pgl2_reflected_torus_R_card_eq_half
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    Nat.card T.R = Nat.card T.U / 2 := by
  classical
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  have hUJ : T.R = T.U ⊓ J := by
    simpa [J] using T.R_eq
  let RU : Subgroup T.U := J.subgroupOf T.U
  have hRUindex : RU.index = 2 := by
    have hdvd : RU.index ∣ 2 := by
      change J.relIndex T.U ∣ 2
      simpa [hJindex] using
        (Subgroup.relIndex_dvd_index_of_normal (H := J) (K := T.U))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exfalso
      have htop : RU = ⊤ := Subgroup.index_eq_one.mp hone
      apply T.s_not_mem_commutator
      have hsU : T.s ∈ T.U := T.s_mem_U
      have hsRU : (⟨T.s, hsU⟩ : T.U) ∈ RU := by
        rw [htop]
        trivial
      exact hsRU
    · exact htwo
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    rw [hKcard]
    exact hpOdd.pow
  have hUeven : Even (Nat.card T.U) := by
    rcases T.U_card with hU | hU
    · rw [hU]
      rcases hqOdd with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      omega
    · rw [hU]
      rcases hqOdd with ⟨a, ha⟩
      refine ⟨a + 1, ?_⟩
      omega
  rcases hUeven with ⟨a, haU⟩
  have hUtwo : Nat.card T.U = 2 * (Nat.card T.U / 2) := by
    rw [haU]
    omega
  have hRUcard : Nat.card RU = Nat.card T.U / 2 := by
    have hmul := RU.card_mul_index
    rw [hRUindex, hUtwo] at hmul
    omega
  have hcardUJ : Nat.card ((T.U ⊓ J : Subgroup (PGL2 K))) = Nat.card RU := by
    refine (Nat.card_congr ?_).symm
    refine {
      toFun := fun x => ⟨(x.1 : PGL2 K), ⟨x.1.2, x.2⟩⟩
      invFun := fun y => ⟨⟨(y : PGL2 K), y.2.1⟩, y.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro x
      rfl
    · intro y
      rfl
  calc
    Nat.card T.R = Nat.card ((T.U ⊓ J : Subgroup (PGL2 K))) := by
      rw [hUJ]
    _ = Nat.card RU := hcardUJ
    _ = Nat.card T.U / 2 := hRUcard

/-- Powers of an involution are trivial or the involution itself. -/
private lemma zpow_eq_one_or_self_of_sq_eq_one {G : Type u} [Group G] {t : G}
    (ht : t * t = 1) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  by_cases ht1 : t = 1
  · left
    simp [ht1]
  · have hord : orderOf t = 2 :=
      (orderOf_eq_prime_iff (x := t)).2 ⟨by simpa [pow_two] using ht, ht1⟩
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change k % (2 : ℤ) = 0 at hk
      simp [hk]
    · right
      change k % (2 : ℤ) = 1 at hk
      simp [hk]

/-- Lift a centralizer element from `E/Z(E)` to an element of `E` fixed by
the normalizing involution `s`: if `[s,x] ∈ Z(E)`, then `s` fixes some
`z*x` with `z ∈ Z(E)`. -/
private lemma centralizer_lift_of_odd_center
    {G : Type u} [Group G] [Finite G]
    (E : Subgroup G) (s : G)
    (hsE : Subgroup.zpowers s ≤ Subgroup.normalizer (E : Set G))
    (hs2 : s * s = 1)
    (hZodd : Odd (Nat.card ((Subgroup.center E).map E.subtype)))
    {x : E}
    (hxfix : s * (x : G) * s⁻¹ * (x : G)⁻¹ ∈
      (Subgroup.center E).map E.subtype) :
    ∃ z : (Subgroup.center E).map E.subtype,
      s * ((z : G) * (x : G)) * s⁻¹ = (z : G) * (x : G) := by
  classical
  by_cases hs1 : s = 1
  · refine ⟨1, ?_⟩
    simp [hs1]
  let A : Subgroup G := Subgroup.zpowers s
  let Z : Subgroup G := (Subgroup.center E).map E.subtype
  have hmap (a : G) (ha : a ∈ A) : ∀ y : G, y ∈ Z → a * y * a⁻¹ ∈ Z := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨c, hc, rfl⟩
    have haE : a ∈ Subgroup.normalizer (E : Set G) := hsE ha
    have hconj_mem : a * (c : G) * a⁻¹ ∈ E :=
      ((Subgroup.mem_normalizer_iff.mp haE) (c : G)).mp (c : E).2
    have hconj_center : (⟨a * (c : G) * a⁻¹, hconj_mem⟩ : E) ∈
        Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro e
      have hainv : a⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
        (Subgroup.normalizer (E : Set G)).inv_mem haE
      have hback : a⁻¹ * (e : G) * a ∈ E :=
        by
          have h := ((Subgroup.mem_normalizer_iff.mp hainv) (e : G)).mp e.property
          simpa using h
      have hc_comm : (c : G) * (a⁻¹ * (e : G) * a) =
          (a⁻¹ * (e : G) * a) * (c : G) := by
        have h := Subgroup.mem_center_iff.mp hc
          (⟨a⁻¹ * (e : G) * a, hback⟩ : E)
        exact (congrArg Subtype.val h).symm
      apply Subtype.ext
      change (e : G) * (a * (c : G) * a⁻¹) =
        (a * (c : G) * a⁻¹) * (e : G)
      calc
        (e : G) * (a * (c : G) * a⁻¹) =
            a * ((a⁻¹ * (e : G) * a) * (c : G)) * a⁻¹ := by group
        _ = a * ((c : G) * (a⁻¹ * (e : G) * a)) * a⁻¹ := by
          rw [← hc_comm]
        _ = (a * (c : G) * a⁻¹) * (e : G) := by group
    exact Subgroup.mem_map.mpr
      ⟨⟨a * (c : G) * a⁻¹, hconj_mem⟩, hconj_center, rfl⟩
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hmap a ha y hy
    · intro hy
      have hainvA : a⁻¹ ∈ A := A.inv_mem ha
      have hback := hmap a⁻¹ hainvA (a * y * a⁻¹) hy
      change a⁻¹ * (a * y * a⁻¹) * (a⁻¹)⁻¹ ∈ Z at hback
      simpa [mul_assoc] using hback
  let : MulDistribMulAction A Z :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
  let : MulDistribMulAction (↥A) (↥Z) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
  let : CommGroup Z := by
    dsimp [Z]
    infer_instance
  have hAcard : Nat.card A = 2 := by
    dsimp [A]
    have hord : orderOf s = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hs2) hs1
    rw [Nat.card_zpowers, hord]
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Z) := by
    rw [hAcard]
    exact hZodd.coprime_two_right.symm
  have hdefect (a : A) : (x : G)⁻¹ * (a : G) * (x : G) * (a : G)⁻¹ ∈ Z := by
    rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨k, hk⟩
    rcases zpow_eq_one_or_self_of_sq_eq_one hs2 k with h1 | hs
    · have ha : (a : G) = 1 := by
        simpa [hk] using h1
      rw [ha]
      simp
    · have ha : (a : G) = s := by
        simpa [hk] using hs
      rw [ha]
      have hrewrite : (x : G)⁻¹ * s * (x : G) * s⁻¹ =
          (x : G)⁻¹ * (s * (x : G) * s⁻¹ * (x : G)⁻¹) * (x : G) := by group
      rw [hrewrite]
      obtain ⟨d0, hd0, hd0val⟩ := hxfix
      have hd0center : (d0 : E) ∈ Subgroup.center E := hd0
      have hfix : (x : G)⁻¹ * (d0 : G) * x = (d0 : G) := by
        have h := Subgroup.mem_center_iff.mp hd0center x
        have hd : (d0 : G) * (x : G) = (x : G) * (d0 : G) :=
          by simpa using (congrArg Subtype.val h).symm
        calc
          (x : G)⁻¹ * (d0 : G) * x = (x : G)⁻¹ * ((d0 : G) * (x : G)) := by group
          _ = (x : G)⁻¹ * ((x : G) * (d0 : G)) := by rw [hd]
          _ = d0 := by group
      rw [← hd0val]
      rw [Subgroup.mem_map]
      refine ⟨d0, hd0, ?_⟩
      simpa [hfix]
  let c : A → Z := fun a =>
    ⟨(x : G)⁻¹ * (a : G) * (x : G) * (a : G)⁻¹, hdefect a⟩
  have hcocycle : @IsCocycle₁ (↥A) (↥Z) _ _
      (Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ) c := by
    intro a b
    apply Subtype.ext
    let : MulDistribMulAction (↥A) (↥Z) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
    change (x : G)⁻¹ * (a * b : G) * (x : G) * (a * b : G)⁻¹ =
      ((x : G)⁻¹ * (a : G) * (x : G) * (a : G)⁻¹) *
        (a * ((x : G)⁻¹ * (b : G) * (x : G) * (b : G)⁻¹) * a⁻¹)
    simp only [Subgroup.coe_inv]
    group
  obtain ⟨z, hz⟩ :=
    @exists_coboundary_of_cocycle_of_coprime_card (↥A) (↥Z) _ _ _ _
      (Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ) c hcocycle hcop
  let sA : A := ⟨s, Subgroup.mem_zpowers s⟩
  let a : G := (x : G)⁻¹ * s * (x : G) * s⁻¹
  have hcs : a = ((sA • z : Z) : G)⁻¹ * (z : G) := by
    let : MulDistribMulAction (↥A) (↥Z) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
    have h := congrArg Subtype.val (hz sA)
    change (x : G)⁻¹ * s * (x : G) * s⁻¹ = ((sA • z : Z) : G)⁻¹ * (z : G) at h
    simpa [a, c, sA] using h
  have hzsmul : ((sA • z : Z) : G) = s * (z : G) * s⁻¹ := by
    let : MulDistribMulAction (↥A) (↥Z) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
    change s * (z : G) * s⁻¹ = s * (z : G) * s⁻¹
    rfl
  obtain ⟨d0, hd0, hd0val⟩ := hxfix
  have hd0center : (d0 : E) ∈ Subgroup.center E := hd0
  have hfix : (x : G)⁻¹ * (d0 : G) * x = (d0 : G) := by
    have h := Subgroup.mem_center_iff.mp hd0center x
    have hd : (d0 : G) * (x : G) = (x : G) * (d0 : G) :=
      by simpa using (congrArg Subtype.val h).symm
    calc
      (x : G)⁻¹ * (d0 : G) * x = (x : G)⁻¹ * ((d0 : G) * (x : G)) := by group
      _ = (x : G)⁻¹ * ((x : G) * (d0 : G)) := by rw [hd]
      _ = d0 := by group
  have ha_eq : a = (d0 : G) := by
    dsimp [a]
    calc
      (x : G)⁻¹ * s * (x : G) * s⁻¹ =
          (x : G)⁻¹ * (s * (x : G) * s⁻¹) := by group
      _ = (x : G)⁻¹ * ((d0 : G) * (x : G)) := by
        congr 1
        calc
          s * (x : G) * s⁻¹ = s * (x : G) * s⁻¹ * (x : G)⁻¹ * (x : G) := by group
          _ = (d0 : G) * (x : G) := by
            exact congrArg (fun y : G => y * (x : G)) hd0val.symm
      _ = (d0 : G) := by
        calc
          (x : G)⁻¹ * ((d0 : G) * (x : G)) =
              (x : G)⁻¹ * (d0 : G) * (x : G) := by group
          _ = (d0 : G) := hfix
  have hzs : s * (z : G) * s⁻¹ = (z : G) * a⁻¹ := by
    have h1 : (s * (z : G) * s⁻¹) * a = (z : G) := by
      rw [hcs, hzsmul]
      group
    calc
      s * (z : G) * s⁻¹ = (s * (z : G) * s⁻¹) * 1 := by simp
      _ = (s * (z : G) * s⁻¹) * (a * a⁻¹) := by group
      _ = ((s * (z : G) * s⁻¹) * a) * a⁻¹ := by group
      _ = (z : G) * a⁻¹ := by rw [h1]
  have hxs : s * (x : G) * s⁻¹ = a * (x : G) := by
    calc
      s * (x : G) * s⁻¹ = s * (x : G) * s⁻¹ * (x : G)⁻¹ * (x : G) := by group
      _ = (d0 : G) * (x : G) := by
        exact congrArg (fun y : G => y * (x : G)) hd0val.symm
      _ = a * (x : G) := by
        exact congrArg (fun y : G => y * (x : G)) ha_eq.symm
  refine ⟨z, ?_⟩
  calc
    s * ((z : G) * (x : G)) * s⁻¹ =
        (s * (z : G) * s⁻¹) * (s * (x : G) * s⁻¹) := by group
    _ = ((z : G) * a⁻¹) * (a * (x : G)) := by rw [hzs, hxs]
    _ = (z : G) * (x : G) := by group

/-- In a join with the subgroup generated by an involution that inverts the
first subgroup, every element is either in the subgroup or the subgroup
times the involution. -/
private lemma mem_sup_zpowers_of_involution_inverts
    {G : Type u} [Group G] {U : Subgroup G} {w : G}
    (_hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) {x : G} :
    x ∈ U ⊔ Subgroup.zpowers w ↔ ∃ u : G, u ∈ U ∧ (x = u ∨ x = u * w) := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ u : G, u ∈ U ∧ (x = u ∨ x = u * w)}
        one_mem' := ⟨1, U.one_mem, Or.inl rfl⟩
        mul_mem' := by
          intro a b ha hb
          rcases ha with ⟨u, hu, hu_or⟩
          rcases hb with ⟨v, hv, hv_or⟩
          rcases hu_or with heq | heq
          · rw [heq]
            rcases hv_or with heqv | heqv
            · rw [heqv]
              exact ⟨u * v, U.mul_mem hu hv, Or.inl rfl⟩
            · rw [heqv]
              exact ⟨u * v, U.mul_mem hu hv, Or.inr (by group)⟩
          · rw [heq]
            rcases hv_or with heqv | heqv
            · rw [heqv]
              have hwv : w * v * w⁻¹ = v⁻¹ := hwinv v hv
              have hstep : (u * w) * v = (u * v⁻¹) * w := by
                calc
                  (u * w) * v = u * (w * v) := by group
                  _ = u * ((w * v * w⁻¹) * w) := by group
                  _ = u * (v⁻¹ * w) := by rw [hwv]
                  _ = (u * v⁻¹) * w := by group
              exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inr (by rw [hstep])⟩
            · rw [heqv]
              have hwv : w * v * w⁻¹ = v⁻¹ := hwinv v hv
              have hstep : (u * w) * (v * w) = u * v⁻¹ := by
                calc
                  (u * w) * (v * w) = u * (w * v) * w := by group
                  _ = u * ((w * v * w⁻¹) * w) * w := by group
                  _ = u * (v⁻¹ * w) * w := by rw [hwv]
                  _ = u * v⁻¹ := by
                    calc
                      u * (v⁻¹ * w) * w = u * v⁻¹ * (w * w) := by group
                      _ = u * v⁻¹ := by simp [hwsq]
              exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inl (by rw [hstep])⟩
        inv_mem' := by
          intro a ha
          rcases ha with ⟨u, hu, hu_or⟩
          rcases hu_or with heq | heq
          · rw [heq]
            exact ⟨u⁻¹, U.inv_mem hu, Or.inl (by simp)⟩
          · rw [heq]
            have hwinvu : w * u⁻¹ * w⁻¹ = u := by
              simpa using hwinv (u⁻¹) (U.inv_mem hu)
            have hstep : (u * w)⁻¹ = u * w := by
              calc
                (u * w)⁻¹ = w⁻¹ * u⁻¹ := by simp
                _ = w * u⁻¹ := by rw [inv_eq_of_mul_eq_one_right hwsq]
                _ = (w * u⁻¹ * w⁻¹) * w := by group
                _ = u * w := by rw [hwinvu]
            exact ⟨u, hu, Or.inr (by rw [hstep])⟩ }
    have hUS : U ≤ S := by
      intro x hx
      exact ⟨x, hx, Or.inl rfl⟩
    have hwS : Subgroup.zpowers w ≤ S := by
      rw [Subgroup.zpowers_le]
      exact ⟨1, U.one_mem, Or.inr (by simp)⟩
    exact (sup_le hUS hwS) hx
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact Subgroup.mem_sup_left hu
    · exact Subgroup.mul_mem_sup hu (Subgroup.mem_zpowers w)

/-- In the `PGL₂` model, the intersection of the derived subgroup with the
centralizer of the outer torus involution is the reflected torus extended by
the inner reflector. -/
private lemma reflected_centralizer_intersection_eq_sup
    {K : Type u} [Field K] [Finite K]
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    let J : Subgroup (PGL2 K) := commutator (PGL2 K)
    J ⊓ Subgroup.centralizer ({T.s} : Set (PGL2 K)) =
      T.R ⊔ Subgroup.zpowers T.t := by
  classical
  intro J
  have hR : T.R = T.U ⊓ J := by simpa [J] using T.R_eq
  have hC : Subgroup.centralizer ({T.s} : Set (PGL2 K)) =
      T.U ⊔ Subgroup.zpowers T.w := T.centralizer_eq
  have htC : T.t ∈ Subgroup.centralizer ({T.s} : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact T.t_commutes_s.eq
  have htJ : T.t ∈ J := by simpa [J] using T.t_mem_commutator
  apply le_antisymm
  · intro x hx
    have hxJ : x ∈ J := hx.1
    have hxC : x ∈ Subgroup.centralizer ({T.s} : Set (PGL2 K)) := hx.2
    rw [hC] at hxC
    rcases (mem_sup_zpowers_of_involution_inverts T.w_not_mem_U T.w_involution
        T.w_inverts_U).mp hxC with ⟨u, huU, hu | huw⟩
    · have huJ : u ∈ J := by simpa [hu] using hxJ
      have huR : u ∈ T.R := by
        rw [hR]
        exact ⟨huU, huJ⟩
      simpa [hu] using (Subgroup.mem_sup_left huR : u ∈ T.R ⊔ Subgroup.zpowers T.t)
    · by_cases hwJ : T.w ∈ J
      · have ht_eq : T.t = T.w := by
          rcases T.t_eq_w_or_ws with ht | hts
          · exact ht
          · exfalso
            have hsJ : T.s ∈ J := by
              have hwts : T.w⁻¹ * T.t = T.s := by
                calc
                  T.w⁻¹ * T.t = T.w⁻¹ * (T.w * T.s) := by rw [hts]
                  _ = T.s := by group
              have hwtJ : T.w⁻¹ * T.t ∈ J := J.mul_mem (J.inv_mem hwJ) htJ
              simpa [hwts] using hwtJ
            exact T.s_not_mem_commutator (by simpa [J] using hsJ)
        have huJ : u ∈ J := by
          have hxw : x * T.w⁻¹ ∈ J := J.mul_mem hxJ (J.inv_mem hwJ)
          have hu_eq : u = x * T.w⁻¹ := by
            calc
              u = (u * T.w) * T.w⁻¹ := by group
              _ = x * T.w⁻¹ := by rw [huw]
          simpa [hu_eq] using hxw
        have huR : u ∈ T.R := by
          rw [hR]
          exact ⟨huU, huJ⟩
        have hxeq : x = u * T.t := by rw [huw, ← ht_eq]
        simpa [hxeq] using (Subgroup.mul_mem_sup huR (Subgroup.mem_zpowers T.t))
      · have ht_eq : T.t = T.w * T.s := by
          rcases T.t_eq_w_or_ws with ht | hts
          · exfalso
            exact hwJ (by simpa [ht] using htJ)
          · exact hts
        have hws : T.w * T.s = T.s * T.w := by
          have h := T.w_inverts_U T.s T.s_mem_U
          have hsinv : T.s⁻¹ = T.s := by
            simpa [pow_two] using
              (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using T.s_involution.right))
          rw [hsinv] at h
          calc
            T.w * T.s = (T.w * T.s * T.w⁻¹) * T.w := by group
            _ = T.s * T.w := by rw [h]
        have hxt : x * T.t⁻¹ ∈ J := J.mul_mem hxJ (J.inv_mem htJ)
        have htinv : T.t⁻¹ = T.w * T.s := by
          calc
            T.t⁻¹ = T.t := by
              simpa [pow_two] using
                (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using T.t_involution.right))
            _ = T.w * T.s := ht_eq
        have hstep : x * T.t⁻¹ = u * T.s := by
          rw [huw, htinv]
          calc
            u * T.w * (T.w * T.s) = u * (T.w * T.w) * T.s := by group
            _ = u * T.s := by simp [T.w_involution]
        have husJ : u * T.s ∈ J := by
          simpa [hstep] using hxt
        have husU : u * T.s ∈ T.U := T.U.mul_mem huU T.s_mem_U
        have husR : u * T.s ∈ T.R := by
          rw [hR]
          exact ⟨husU, husJ⟩
        have hxeq : x = (u * T.s) * T.t := by
          rw [huw, ht_eq]
          calc
            u * T.w = u * T.w * (T.s * T.s) := by
              rw [← pow_two, T.s_involution.right]
              group
            _ = u * (T.w * T.s) * T.s := by group
            _ = u * (T.s * T.w) * T.s := by rw [hws]
            _ = (u * T.s) * (T.w * T.s) := by group
        simpa [hxeq] using (Subgroup.mul_mem_sup husR (Subgroup.mem_zpowers T.t))
  · apply sup_le
    · intro x hxR
      have hxJ : x ∈ J := by
        rw [hR] at hxR
        exact hxR.2
      exact ⟨hxJ, T.R_le_centralizer_s hxR⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨htJ, htC⟩

/-- The commutator of the inner reflector with the reflected torus extended
by the reflector is the reflected torus itself. -/
private lemma commutator_zpowers_sup_eq_R
    {K : Type u} [Field K] [Finite K]
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    ⁅Subgroup.zpowers T.t, T.R ⊔ Subgroup.zpowers T.t⁆ = T.R := by
  classical
  have hRleU : T.R ≤ T.U := by
    rw [T.R_eq]
    exact inf_le_left
  have htnotR : T.t ∉ T.R := by
    intro htR
    exact T.t_not_mem_U (hRleU htR)
  have htinvs : ∀ x : PGL2 K, x ∈ T.R → T.t * x * T.t⁻¹ = x⁻¹ :=
    fun x hx => T.t_inverts_U x (hRleU hx)
  have htt : T.t * T.t = 1 := by simpa [pow_two] using T.t_involution.right
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases (Subgroup.mem_zpowers_iff.mp ha) with ⟨k, rfl⟩
    rcases (zpow_eq_one_or_self_of_sq_eq_one htt k) with hk | hk
    · rw [hk]
      simp
    · rw [hk]
      rcases (mem_sup_zpowers_of_involution_inverts htnotR htt
          htinvs).mp hb with ⟨r, hrR, hr_or⟩
      rcases hr_or with heq | heq
      · rw [heq]
        have htr : T.t * r * T.t⁻¹ = r⁻¹ := by
          simpa [inv_eq_of_mul_eq_one_right htt] using htinvs r hrR
        have hmem : ⁅T.t, r⁆ ∈ T.R := by
          rw [commutatorElement_def, htr]
          exact T.R.mul_mem (T.R.inv_mem hrR) (T.R.inv_mem hrR)
        exact hmem
      · rw [heq]
        have hcomm : ⁅T.t, r * T.t⁆ = ⁅T.t, r⁆ := by
          rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_self]
          group
        have htr : T.t * r * T.t⁻¹ = r⁻¹ := by
          simpa [inv_eq_of_mul_eq_one_right htt] using htinvs r hrR
        have hmem : ⁅T.t, r * T.t⁆ ∈ T.R := by
          rw [hcomm, commutatorElement_def, htr]
          exact T.R.mul_mem (T.R.inv_mem hrR) (T.R.inv_mem hrR)
        exact hmem
  · -- R ≤ [⟨t⟩, R ⊔ ⟨t⟩] by odd squaring
    intro r hrR
    let k : ℕ := (Nat.card T.R + 1) / 2
    have hRodd : Odd (Nat.card T.R) := T.R_card_odd
    have hk2 : 2 * k = Nat.card T.R + 1 := by
      dsimp [k]
      rcases hRodd with ⟨a, ha⟩
      rw [ha]
      omega
    let x : PGL2 K := (r⁻¹) ^ k
    have hxR : x ∈ T.R := T.R.pow_mem (T.R.inv_mem hrR) k
    have hx2 : x⁻¹ = r ^ k := by
      dsimp [x]
      rw [inv_pow]
      simp
    have hcomm : ⁅T.t, x⁆ = r := by
      calc
        ⁅T.t, x⁆ = T.t * x * T.t⁻¹ * x⁻¹ := rfl
        _ = x⁻¹ * x⁻¹ := by
          rw [T.t_inverts_U x (hRleU hxR)]
        _ = r ^ (k + k) := by rw [hx2, pow_add]
        _ = r ^ (2 * k) := by congr 1; omega
        _ = r := by
          rw [hk2, pow_add, pow_one]
          have hrpow : r ^ Nat.card T.R = 1 := by
            exact congrArg Subtype.val
              (pow_card_eq_one' (G := T.R) (x := ⟨r, hrR⟩))
          rw [hrpow]
          simp
    have hxmem : x ∈ T.R ⊔ Subgroup.zpowers T.t := Subgroup.mem_sup_left hxR
    have hcmem : ⁅T.t, x⁆ ∈ ⁅Subgroup.zpowers T.t, T.R ⊔ Subgroup.zpowers T.t⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers T.t) hxmem
    simpa [hcomm] using hcmem

/-- The standard reflected commutator in the odd `PGL₂` model is cyclic of
order the odd half of `q±1`. -/
private lemma pgl2_reflected_outer_commutator_card_std
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    let C1 : Subgroup (PGL2 K) := ⁅Subgroup.zpowers T.t,
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({T.s} : Set (PGL2 K))⁆
    IsCyclic C1 ∧ Nat.card C1 = Nat.card T.U / 2 := by
  classical
  intro C1
  have hCeq : commutator (PGL2 K) ⊓
      Subgroup.centralizer ({T.s} : Set (PGL2 K)) =
      T.R ⊔ Subgroup.zpowers T.t := by
    simpa using (reflected_centralizer_intersection_eq_sup P eP T)
  have hC1eq : C1 = ⁅Subgroup.zpowers T.t, T.R ⊔ Subgroup.zpowers T.t⁆ := by
    dsimp [C1]
    rw [hCeq]
  have hcomm : ⁅Subgroup.zpowers T.t, T.R ⊔ Subgroup.zpowers T.t⁆ = T.R :=
    commutator_zpowers_sup_eq_R P eP T
  have hRcyclic : IsCyclic T.R := by
    have : IsCyclic T.U := T.U_cyclic
    have hRU : T.R ≤ T.U := by
      rw [T.R_eq]
      exact inf_le_left
    exact Subgroup.isCyclic_of_le (H := T.R) (H' := T.U) hRU
  have hRcard : Nat.card T.R = Nat.card T.U / 2 :=
    pgl2_reflected_torus_R_card_eq_half hK hcard P eP T
  rw [hC1eq, hcomm]
  exact ⟨hRcyclic, hRcard⟩

/-- In the odd `PGL₂` model, the commutator of an inner reflector with the
centralizer of the conjugated outer torus involution is cyclic of order the
odd half of `q±1`. -/
public theorem pgl2_reflected_outer_commutator_card
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP)
    {s0 t0 : PGL2 K}
    (hst0 : ∃ a : PGL2 K, s0 = a * T.s * a⁻¹ ∧ t0 = a * T.t * a⁻¹) :
    let C1 : Subgroup (PGL2 K) := ⁅Subgroup.zpowers t0,
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({s0} : Set (PGL2 K))⁆
    IsCyclic C1 ∧ Nat.card C1 = Nat.card T.U / 2 := by
  classical
  intro C1
  rcases hst0 with ⟨a, hs0, ht0⟩
  let e : PGL2 K ≃* PGL2 K := MulAut.conj a
  have he : e T.s = s0 := by
    simpa [e, MulAut.conj_apply] using hs0.symm
  have he_t : e T.t = t0 := by
    simpa [e, MulAut.conj_apply] using ht0.symm
  have hmap_z : (Subgroup.zpowers T.t).map e.toMonoidHom = Subgroup.zpowers t0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨k, rfl⟩
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      change t0 ^ k = e (T.t ^ k)
      rw [map_zpow, he_t]
    · rintro ⟨k, rfl⟩
      rw [Subgroup.mem_map]
      refine ⟨T.t ^ k, ?_, ?_⟩
      · rw [Subgroup.mem_zpowers_iff]
        exact ⟨k, rfl⟩
      · change e (T.t ^ k) = t0 ^ k
        rw [map_zpow, he_t]
  have hmap_J : (commutator (PGL2 K)).map e.toMonoidHom =
      commutator (PGL2 K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := K)).range := by
        simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using hy
      change a * y * a⁻¹ ∈ commutator (PGL2 K)
      simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using
        (Subgroup.normal_of_index_eq_two
          (pgl2_psl2Range_index_eq_two K hK)).conj_mem y hy' a
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨e.symm x, ?_, by simp⟩
      have : e.symm x = a⁻¹ * x * a := by
        change (MulAut.conj a).symm x = a⁻¹ * x * a
        simp
      have hxJ : e.symm x ∈ commutator (PGL2 K) := by
        rw [this]
        have hx' : x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
            (n := Fin 2) (R := K)).range := by
          simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using hx
        simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using
          (Subgroup.normal_of_index_eq_two
            (pgl2_psl2Range_index_eq_two K hK)).conj_mem x hx' a⁻¹
      simpa [this] using hxJ
  have hmap_c : (Subgroup.centralizer ({T.s} : Set (PGL2 K))).map e.toMonoidHom =
      Subgroup.centralizer ({s0} : Set (PGL2 K)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyc : y * T.s = T.s * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      have h := congrArg e hyc
      simpa [he] using h
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨e.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx' : x * s0 = s0 * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have h := congrArg e.symm hx'
      simpa [← he] using h
  have hmap_inf : (commutator (PGL2 K) ⊓
      Subgroup.centralizer ({T.s} : Set (PGL2 K))).map e.toMonoidHom =
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({s0} : Set (PGL2 K)) := by
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, hmap_J, hmap_c]
  have hC1eq : C1 = (⁅Subgroup.zpowers T.t,
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({T.s} : Set (PGL2 K))⁆).map
        e.toMonoidHom := by
    dsimp [C1]
    rw [← hmap_z, ← hmap_inf, ← Subgroup.map_commutator]
    rfl
  have hstd := pgl2_reflected_outer_commutator_card_std hK hcard P eP T
  dsimp at hstd
  rcases hstd with ⟨hcyc, hcard'⟩
  have hcyc' : IsCyclic C1 := by
    rw [hC1eq]
    exact (Subgroup.equivMapOfInjective
      (⁅Subgroup.zpowers T.t,
        commutator (PGL2 K) ⊓ Subgroup.centralizer ({T.s} : Set (PGL2 K))⁆)
      e.toMonoidHom e.injective).isCyclic.mp hcyc
  have hcard'' : Nat.card C1 = Nat.card T.U / 2 := by
    rw [hC1eq]
    rw [Subgroup.card_map_of_injective e.injective]
    exact hcard'
  exact ⟨hcyc', hcard''⟩

/-- In the odd `PGL₂` model, the conjugated reflected commutator is exactly
the conjugate of the reflected torus `R`. -/
public theorem pgl2_reflected_outer_commutator_eq_conj_R
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP)
    {a s0 t0 : PGL2 K}
    (hs0 : s0 = a * T.s * a⁻¹) (ht0 : t0 = a * T.t * a⁻¹) :
    let C1 : Subgroup (PGL2 K) :=
      ⁅Subgroup.zpowers t0,
        commutator (PGL2 K) ⊓ Subgroup.centralizer ({s0} : Set (PGL2 K))⁆
    C1 = T.R.map (MulAut.conj a).toMonoidHom := by
  classical
  intro C1
  let e : PGL2 K ≃* PGL2 K := MulAut.conj a
  have he : e T.s = s0 := by
    simpa [e, MulAut.conj_apply] using hs0.symm
  have he_t : e T.t = t0 := by
    simpa [e, MulAut.conj_apply] using ht0.symm
  have hmap_z : (Subgroup.zpowers T.t).map e.toMonoidHom = Subgroup.zpowers t0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨k, rfl⟩
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      change t0 ^ k = e (T.t ^ k)
      rw [map_zpow, he_t]
    · rintro ⟨k, rfl⟩
      rw [Subgroup.mem_map]
      refine ⟨T.t ^ k, ?_, ?_⟩
      · rw [Subgroup.mem_zpowers_iff]
        exact ⟨k, rfl⟩
      · change e (T.t ^ k) = t0 ^ k
        rw [map_zpow, he_t]
  have hmap_J : (commutator (PGL2 K)).map e.toMonoidHom =
      commutator (PGL2 K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := K)).range := by
        simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using hy
      change a * y * a⁻¹ ∈ commutator (PGL2 K)
      simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using
        (Subgroup.normal_of_index_eq_two
          (pgl2_psl2Range_index_eq_two K hK)).conj_mem y hy' a
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨e.symm x, ?_, by simp⟩
      have : e.symm x = a⁻¹ * x * a := by
        change (MulAut.conj a).symm x = a⁻¹ * x * a
        simp
      have hxJ : e.symm x ∈ commutator (PGL2 K) := by
        rw [this]
        have hx' : x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
            (n := Fin 2) (R := K)).range := by
          simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using hx
        simpa [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using
          (Subgroup.normal_of_index_eq_two
            (pgl2_psl2Range_index_eq_two K hK)).conj_mem x hx' a⁻¹
      simpa [this] using hxJ
  have hmap_c : (Subgroup.centralizer ({T.s} : Set (PGL2 K))).map e.toMonoidHom =
      Subgroup.centralizer ({s0} : Set (PGL2 K)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyc : y * T.s = T.s * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      have h := congrArg e hyc
      simpa [he] using h
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨e.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx' : x * s0 = s0 * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have h := congrArg e.symm hx'
      simpa [← he] using h
  have hmap_inf : (commutator (PGL2 K) ⊓
      Subgroup.centralizer ({T.s} : Set (PGL2 K))).map e.toMonoidHom =
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({s0} : Set (PGL2 K)) := by
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, hmap_J, hmap_c]
  have hC1eq : C1 = (⁅Subgroup.zpowers T.t,
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({T.s} : Set (PGL2 K))⁆).map
        e.toMonoidHom := by
    dsimp [C1]
    rw [← hmap_z, ← hmap_inf, ← Subgroup.map_commutator]
    rfl
  have hstd_eq : ⁅Subgroup.zpowers T.t,
      commutator (PGL2 K) ⊓ Subgroup.centralizer ({T.s} : Set (PGL2 K))⁆ =
      T.R := by
    have hCeq : commutator (PGL2 K) ⊓
        Subgroup.centralizer ({T.s} : Set (PGL2 K)) =
        T.R ⊔ Subgroup.zpowers T.t :=
      reflected_centralizer_intersection_eq_sup P eP T
    rw [hCeq]
    exact commutator_zpowers_sup_eq_R P eP T
  rw [hC1eq, hstd_eq]

/-- In the odd `PGL₂` model, the centralizer of an inner reflector inside
the derived subgroup has twice the other half of `q±1`. -/
private lemma unique_involution_cyclic
    {U : Type u} [Group U] [Finite U] [IsCyclic U] {s : U}
    (hs : s ^ 2 = 1) (hsne : s ≠ 1) :
    ∀ x : U, x ^ 2 = 1 → x ≠ 1 → x = s := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let A : Finset U := Finset.univ.filter (fun a => a ^ 2 = 1)
  have hle : A.card ≤ 2 := by
    simpa [A] using (IsCyclic.card_pow_eq_one_le (α := U) (n := 2) (by norm_num))
  have hmem1 : (1 : U) ∈ A := by simp [A]
  have hmemS : s ∈ A := by simp [A, hs]
  have hge : 2 ≤ A.card := by
    let B : Finset U := {1, s}
    have hBsub : B ⊆ A := by
      intro a ha
      dsimp [B] at ha
      simp at ha
      rcases ha with rfl | rfl
      · simp [A]
      · simp [A, hs]
    have hBcard : B.card = 2 := by
      dsimp [B]
      rw [Finset.card_eq_two]
      exact ⟨1, s, Ne.symm hsne, rfl⟩
    rw [← hBcard]
    exact Finset.card_le_card hBsub
  have hcard : A.card = 2 := le_antisymm hle hge
  intro x hx hxne
  by_contra hxs
  have hdistinct : ({1, s, x} : Finset U).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, s, x, Ne.symm hsne, hxne.symm, Ne.symm hxs, rfl⟩
  have hsub : ({1, s, x} : Finset U) ⊆ A := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp [A]
    · simp [A, hs]
    · simp [A, hx]
  have hle3 : 3 ≤ A.card := by
    rw [← hdistinct]
    exact Finset.card_le_card hsub
  omega

private lemma unique_involution_of_cyclic_subgroup
    {G : Type u} [Group G] [Finite G] (U : Subgroup G) (hUcyc : IsCyclic U)
    {s : G} (hsU : s ∈ U) (hssq : s * s = 1) (hsne : s ≠ 1)
    {x : G} (hxU : x ∈ U) (hxsq : x * x = 1) (hxne : x ≠ 1) : x = s := by
  let sU : U := ⟨s, hsU⟩
  let xU : U := ⟨x, hxU⟩
  have hsU2 : sU ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hssq
  have hsUne : sU ≠ 1 := by
    intro h
    exact hsne (congrArg Subtype.val h)
  have hxU2 : xU ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hxsq
  have hxUne : xU ≠ 1 := by
    intro h
    exact hxne (congrArg Subtype.val h)
  have hEq : xU = sU := by
    exact unique_involution_cyclic (U := U) hsU2 hsUne xU hxU2 hxUne
  exact congrArg Subtype.val hEq

private lemma torus_involution_mem_commutator
    {K : Type u} [Field K] [Finite K]
    (hJindex : (commutator (PGL2 K)).index = 2)
    (U : Subgroup (PGL2 K)) (hUcyc : IsCyclic U)
    {s : PGL2 K} (hsU : s ∈ U) (hssq : s * s = 1) (hsne : s ≠ 1)
    {m : ℕ} (hUcard : Nat.card U = 2 * m) (hmeven : Even m)
    (hUJ : ¬ U ≤ commutator (PGL2 K)) :
    s ∈ commutator (PGL2 K) := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : IsCyclic U := hUcyc
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let UJ : Subgroup (PGL2 K) := U ⊓ J
  let UJU : Subgroup U := UJ.subgroupOf U
  have hUJleU : UJ ≤ U := inf_le_left
  have hUJ' : ∃ a : PGL2 K, a ∈ U ∧ a ∉ J := by
    by_contra h
    apply hUJ
    intro x hx
    by_contra hxJ
    exact h ⟨x, hx, hxJ⟩
  rcases hUJ' with ⟨a, haU, haJ⟩
  have hUJUindex : UJU.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨a, haU⟩, ?_, ?_⟩
    · intro h
      exact haJ (Subgroup.mem_subgroupOf.mp h).2
    · intro b
      by_cases hb : (b : PGL2 K) ∈ J
      · right
        exact Subgroup.mem_subgroupOf.mpr ⟨b.2, hb⟩
      · left
        apply Subgroup.mem_subgroupOf.mpr
        have hiff := (Subgroup.mul_mem_iff_of_index_two hJindex
          (a := (b : PGL2 K)) (b := a))
        exact ⟨U.mul_mem b.2 haU, hiff.mpr ⟨fun hbJ => False.elim (hb hbJ),
          fun haJmem => False.elim (haJ haJmem)⟩⟩
  have hUJUcard : Nat.card UJU = Nat.card UJ := by
    let e : UJU ≃ UJ :=
      {
        toFun := fun x => ⟨(x : PGL2 K), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun y => ⟨⟨(y : PGL2 K), y.2.1⟩,
          Subgroup.mem_subgroupOf.mpr y.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro y; rfl }
    exact Nat.card_congr e
  have hUJcard : Nat.card UJ = m := by
    have hmul := UJU.card_mul_index
    rw [hUJUindex, hUJUcard, hUcard] at hmul
    omega
  have h2dvd : 2 ∣ Nat.card UJ := by
    rw [hUJcard]
    exact even_iff_two_dvd.mp hmeven
  let : Fintype UJ := Fintype.ofFinite UJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card (G := UJ) (p := 2)
    (by simpa [Nat.card_eq_fintype_card] using h2dvd)
  let xG : PGL2 K := (x : UJ)
  have hxUJ : xG ∈ UJ := x.2
  have hxU : xG ∈ U := (inf_le_left : UJ ≤ U) hxUJ
  have hxJ : xG ∈ J := (inf_le_right : UJ ≤ J) hxUJ
  have hxpow : xG * xG = 1 := by
    have hxpow' : (x : UJ) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hxord] at h
    simpa [xG, pow_two] using congrArg Subtype.val hxpow'
  have hxne : xG ≠ 1 := by
    intro hx1
    have hx1' : x = 1 := by
      apply Subtype.ext
      change (x : PGL2 K) = 1
      exact hx1
    have hord1 : orderOf (1 : UJ) = 1 := by simp
    have : (1 : ℕ) = 2 := by simpa [hx1', hord1] using hxord
    norm_num at this
  have hxeq : xG = s := by
    exact unique_involution_of_cyclic_subgroup U hUcyc hsU hssq hsne hxU hxpow hxne
  rw [← hxeq]
  exact hxJ

private lemma centralizer_card_conj_eq_normal
    {G : Type u} [Group G] (J : Subgroup G) [J.Normal] {x y g : G}
    (hgy : g * x * g⁻¹ = y) :
    Nat.card ((Subgroup.centralizer ({x} : Set G) ⊓ J) : Subgroup G) =
      Nat.card ((Subgroup.centralizer ({y} : Set G) ⊓ J) : Subgroup G) := by
  classical
  let e : G ≃* G := MulAut.conj g
  have hmap_c : (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({y} : Set G) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp hw
      have h := congrArg e hw'
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (g * w * g⁻¹) * y = y * (g * w * g⁻¹)
      calc
        (g * w * g⁻¹) * y = (g * w * g⁻¹) * (g * x * g⁻¹) := by rw [hgy]
        _ = g * (w * x) * g⁻¹ := by group
        _ = g * (x * w) * g⁻¹ := by rw [hw']
        _ = y * (g * w * g⁻¹) := by rw [← hgy]; group
    · intro hz
      rw [Subgroup.mem_map]
      refine ⟨e.symm z, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hz' : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hz
        have h := congrArg e.symm hz'
        change (g⁻¹ * z * g) * x = x * (g⁻¹ * z * g)
        calc
          (g⁻¹ * z * g) * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * (z * y) * g := by rw [hgy]
          _ = g⁻¹ * (y * z) * g := by rw [hz']
          _ = x * (g⁻¹ * z * g) := by rw [← hgy]; group
      · simp
  have hmap_J : J.map e.toMonoidHom = J := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (inferInstance : J.Normal).conj_mem w hw g
    · intro hz
      rw [Subgroup.mem_map]
      refine ⟨e.symm z, ?_, ?_⟩
      · change (g⁻¹ * z * g) ∈ J
        simpa using ((inferInstance : J.Normal).conj_mem z hz g⁻¹)
      · simp
  have hmap : (Subgroup.centralizer ({x} : Set G) ⊓ J).map e.toMonoidHom =
      Subgroup.centralizer ({y} : Set G) ⊓ J := by
    rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, hmap_c, hmap_J]
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]

private lemma inner_involutions_conjugate_in_derived
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {x y : PGL2 K}
    (hxJ : x ∈ commutator (PGL2 K)) (hxI : IsInvolution x)
    (hyJ : y ∈ commutator (PGL2 K)) (hyI : IsInvolution y) :
    ∃ g : PGL2 K, g ∈ commutator (PGL2 K) ∧ g * x * g⁻¹ = y := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let eJ : J ≃* PSL2 K :=
    (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK hcard (MulEquiv.refl (PGL2 K))).some
  let xJ : J := ⟨x, hxJ⟩
  let yJ : J := ⟨y, hyJ⟩
  have hxI' : IsInvolution (eJ xJ) := by
    constructor
    · intro h
      apply hxI.1
      have hxJ1 : xJ = 1 := eJ.injective (by simpa using h)
      exact congrArg Subtype.val hxJ1
    · have hxJpow : xJ ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hxI.2
      change (eJ xJ) ^ 2 = 1
      simpa using congrArg eJ hxJpow
  have hyI' : IsInvolution (eJ yJ) := by
    constructor
    · intro h
      apply hyI.1
      have hyJ1 : yJ = 1 := eJ.injective (by simpa using h)
      exact congrArg Subtype.val hyJ1
    · have hyJpow : yJ ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hyI.2
      change (eJ yJ) ^ 2 = 1
      simpa using congrArg eJ hyJpow
  obtain ⟨h, hh⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power K hK
    (eJ xJ) (eJ yJ) hxI' hyI'
  refine ⟨(eJ.symm h : PGL2 K), ?_, ?_⟩
  · exact (eJ.symm h : J).2
  · have hh' : (eJ.symm h : J) * xJ * (eJ.symm h : J)⁻¹ = yJ := by
      apply eJ.injective
      change eJ ((eJ.symm h : J) * xJ * (eJ.symm h : J)⁻¹) = eJ yJ
      simpa using hh
    exact congrArg Subtype.val hh'

private lemma centralizer_derived_card_of_torus_data
    {K : Type u} [Field K] [Finite K]
    (hJindex : (commutator (PGL2 K)).index = 2)
    (U : Subgroup (PGL2 K)) (s w : PGL2 K)
    (hC : Subgroup.centralizer ({s} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : PGL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hUJ : ¬ U ≤ commutator (PGL2 K)) :
    Nat.card ((Subgroup.centralizer ({s} : Set (PGL2 K)) ⊓
        (commutator (PGL2 K) : Subgroup (PGL2 K))) : Subgroup (PGL2 K)) =
      Nat.card U := by
  classical
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let C : Subgroup (PGL2 K) := Subgroup.centralizer ({s} : Set (PGL2 K))
  have hCeq : C = U ⊔ Subgroup.zpowers w := by simpa [C] using hC
  have hmem : ∀ b : PGL2 K, b ∈ C → b ∈ U ∨ ∃ u : PGL2 K, u ∈ U ∧ b = u * w := by
    intro b hb
    rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp
        (by simpa [C, hCeq] using hb) with ⟨u, huU, heq | huw⟩
    · left
      simpa [heq] using huU
    · right
      exact ⟨u, huU, huw⟩
  let UC : Subgroup C := U.subgroupOf C
  have hUleC : U ≤ C := by rw [hCeq]; exact le_sup_left
  have hwC : w ∈ C := by
    rw [hCeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hUCindex : UC.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨w, hwC⟩, ?_, ?_⟩
    · intro h
      exact hwU (Subgroup.mem_subgroupOf.mp h)
    · intro b
      rcases hmem (b : PGL2 K) b.2 with hbU | ⟨u, hu, hbu⟩
      · right
        exact Subgroup.mem_subgroupOf.mpr hbU
      · left
        apply Subgroup.mem_subgroupOf.mpr
        change ((b : PGL2 K) * w) ∈ U
        rw [hbu]
        have huww : u * w * w = u := by
          calc
            u * w * w = u * (w * w) := by group
            _ = u := by rw [hwsq]; simp
        rw [huww]
        exact hu
  have hUCcard : Nat.card UC = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleC).toEquiv
  have hCcard : Nat.card C = 2 * Nat.card U := by
    have hmul := UC.card_mul_index
    rw [hUCindex, hUCcard] at hmul
    omega
  have hUJ' : ∃ a : PGL2 K, a ∈ U ∧ a ∉ J := by
    by_contra h
    apply hUJ
    intro x hx
    by_contra hxJ
    exact h ⟨x, hx, hxJ⟩
  rcases hUJ' with ⟨a, haU, haJ⟩
  have haC : a ∈ C := by
    rw [hCeq]
    exact (le_sup_left : U ≤ U ⊔ Subgroup.zpowers w) haU
  let JC : Subgroup C := J.subgroupOf C
  have hJCindex : JC.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨a, haC⟩, ?_, ?_⟩
    · intro h
      exact haJ (Subgroup.mem_subgroupOf.mp h)
    · intro b
      by_cases hb : (b : PGL2 K) ∈ J
      · right
        exact Subgroup.mem_subgroupOf.mpr hb
      · left
        apply Subgroup.mem_subgroupOf.mpr
        change ((b : PGL2 K) * a) ∈ J
        have hiff := (Subgroup.mul_mem_iff_of_index_two hJindex
          (a := (b : PGL2 K)) (b := a))
        exact hiff.mpr ⟨fun hbJ => False.elim (hb hbJ),
          fun haJmem => False.elim (haJ haJmem)⟩
  have hJCcard : Nat.card JC = Nat.card (J ⊓ C : Subgroup (PGL2 K)) := by
    let e : JC ≃ (J ⊓ C : Subgroup (PGL2 K)) :=
      {
        toFun := fun x => ⟨(x : PGL2 K),
          ⟨Subgroup.mem_subgroupOf.mp x.2, (x : C).2⟩⟩
        invFun := fun y => ⟨⟨(y : PGL2 K), y.2.2⟩,
          Subgroup.mem_subgroupOf.mpr y.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by intro y; rfl }
    exact Nat.card_congr e
  have hJCard : Nat.card (J ⊓ C : Subgroup (PGL2 K)) * 2 = Nat.card C := by
    have hmul := JC.card_mul_index
    rw [hJCindex, hJCcard] at hmul
    exact hmul
  calc
    Nat.card ((Subgroup.centralizer ({s} : Set (PGL2 K)) ⊓
        (commutator (PGL2 K) : Subgroup (PGL2 K))) : Subgroup (PGL2 K)) =
        Nat.card (J ⊓ C : Subgroup (PGL2 K)) := by
      rw [inf_comm]
    _ = Nat.card U := by
      omega

private lemma card_conjugates_eq_index_normalizer
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card (MulAction.orbit (ConjAct G) H) =
      (Subgroup.normalizer (H : Set G)).index := by
  classical
  let : Group (ConjAct G) := inferInstance
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer (G := ConjAct G) (x := H)]
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  have hmap : MulAction.stabilizer (ConjAct G) H =
      N.map (ConjAct.toConjAct : G ≃* ConjAct G) := by
    ext x
    constructor
    · intro hx
      rcases ConjAct.toConjAct.surjective x with ⟨g0, rfl⟩
      rw [Subgroup.mem_map]
      refine ⟨g0, ?_, rfl⟩
      exact (Subgroup.conjAct_pointwise_smul_iff.mp
        (MulAction.mem_stabilizer_iff.mp hx))
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨g0, hg0, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      exact (Subgroup.conjAct_pointwise_smul_iff.mpr hg0)
  rw [hmap, Subgroup.index_map_equiv N ConjAct.toConjAct]

public theorem pgl2_inner_involution_centralizer_card
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP)
    {t0 : PGL2 K} (ht0 : ∃ a : PGL2 K, t0 = a * T.t * a⁻¹) :
    Nat.card ((Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓
        (commutator (PGL2 K) : Subgroup (PGL2 K))) : Subgroup (PGL2 K)) =
      2 * (if Nat.card T.U = Nat.card K - 1 then
            (Nat.card K + 1) / 2
          else
            (Nat.card K - 1) / 2) := by
  classical
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    rw [hKcard]
    exact hpOdd.pow
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  let : J.Normal := by
    dsimp [J]
    infer_instance
  rcases ht0 with ⟨a, hta⟩
  have hconj0 : a * T.t * a⁻¹ = t0 := hta.symm
  by_cases hU : Nat.card T.U = Nat.card K - 1
  · obtain ⟨U0, s0, w0, hU0cyc, hU0card, hs0U, hssq0, hs0ne, hw0U, hwsq0,
        hwinv0, hcent0, hU0cross⟩ :=
      GorensteinWalter.pgl2_nonsplit_torus_centralizer_data K hqOdd
    have hU0crossJ : ¬ U0 ≤ J := by
      intro h
      exact hU0cross hqOdd
        (by simpa [J, pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using h)
    let hm : ℕ := (Nat.card K + 1) / 2
    have hU0card2 : Nat.card U0 = 2 * hm := by
      dsimp [hm]
      rw [hU0card]
      rcases hqOdd with ⟨b, hb⟩
      omega
    have hmeven : Even hm := by
      dsimp [hm]
      have hoddhalf : Odd ((Nat.card K - 1) / 2) := by
        simpa [hU] using T.U_half_odd
      have hplus : (Nat.card K - 1) / 2 + 1 = (Nat.card K + 1) / 2 := by
        rcases hqOdd with ⟨b, hb⟩
        omega
      rw [← hplus]
      rcases hoddhalf with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      omega
    have hs0J : s0 ∈ J :=
      torus_involution_mem_commutator hJindex U0 hU0cyc hs0U hssq0 hs0ne
        hU0card2 hmeven hU0crossJ
    have htJ : T.t ∈ J := by simpa [J] using T.t_mem_commutator
    have hs0I : IsInvolution s0 :=
      ⟨hs0ne, by simpa [pow_two] using hssq0⟩
    obtain ⟨g, _hgJ, hconj⟩ :=
      @inner_involutions_conjugate_in_derived K _ _ hK hcard T.t s0
        htJ T.t_involution hs0J hs0I
    have hcard_t : Nat.card ((Subgroup.centralizer ({T.t} : Set (PGL2 K)) ⊓ J
        : Subgroup (PGL2 K))) =
        Nat.card ((Subgroup.centralizer ({s0} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) :=
      centralizer_card_conj_eq_normal J hconj
    have hcard_s0 : Nat.card ((Subgroup.centralizer ({s0} : Set (PGL2 K)) ⊓ J
        : Subgroup (PGL2 K))) = Nat.card U0 :=
      centralizer_derived_card_of_torus_data hJindex U0 s0 w0 hcent0 hw0U
        hwsq0 hwinv0 hU0crossJ
    have hcard_t0 : Nat.card ((Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓ J
        : Subgroup (PGL2 K))) =
        Nat.card ((Subgroup.centralizer ({T.t} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) :=
      (centralizer_card_conj_eq_normal J hconj0).symm
    calc
      Nat.card ((Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) =
          Nat.card ((Subgroup.centralizer ({T.t} : Set (PGL2 K)) ⊓ J
            : Subgroup (PGL2 K))) := hcard_t0
      _ = Nat.card ((Subgroup.centralizer ({s0} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) := hcard_t
      _ = Nat.card U0 := hcard_s0
      _ = 2 * ((Nat.card K + 1) / 2) := by
        rw [hU0card]
        rcases hqOdd with ⟨b, hb⟩
        omega
      _ = 2 * (if Nat.card T.U = Nat.card K - 1 then
            (Nat.card K + 1) / 2
          else
            (Nat.card K - 1) / 2) := by rw [if_pos hU]
  · obtain ⟨U0, s0, w0, hU0cyc, hU0card, hs0U, hssq0, hs0ne, hw0U, hwsq0,
        hwinv0, hcent0, hU0cross⟩ :=
      GorensteinWalter.pgl2_split_torus_centralizer_data K hqOdd
    have hU0crossJ : ¬ U0 ≤ J := by
      intro h
      exact hU0cross hqOdd
        (by simpa [J, pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] using h)
    let hm : ℕ := (Nat.card K - 1) / 2
    have hU0card2 : Nat.card U0 = 2 * hm := by
      dsimp [hm]
      rw [hU0card]
      rcases hqOdd with ⟨b, hb⟩
      omega
    have hmeven : Even hm := by
      dsimp [hm]
      have hoddhalf : Odd ((Nat.card K + 1) / 2) := by
        have hUplus : Nat.card T.U = Nat.card K + 1 := T.U_card.resolve_left hU
        simpa [hUplus] using T.U_half_odd
      have hminus : (Nat.card K + 1) / 2 - 1 = (Nat.card K - 1) / 2 := by
        rcases hqOdd with ⟨b, hb⟩
        omega
      rw [← hminus]
      rcases hoddhalf with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    have hs0J : s0 ∈ J :=
      torus_involution_mem_commutator hJindex U0 hU0cyc hs0U hssq0 hs0ne
        hU0card2 hmeven hU0crossJ
    have htJ : T.t ∈ J := by simpa [J] using T.t_mem_commutator
    have hs0I : IsInvolution s0 :=
      ⟨hs0ne, by simpa [pow_two] using hssq0⟩
    obtain ⟨g, _hgJ, hconj⟩ :=
      @inner_involutions_conjugate_in_derived K _ _ hK hcard T.t s0
        htJ T.t_involution hs0J hs0I
    have hcard_t : Nat.card ((Subgroup.centralizer ({T.t} : Set (PGL2 K)) ⊓ J
        : Subgroup (PGL2 K))) =
        Nat.card ((Subgroup.centralizer ({s0} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) :=
      centralizer_card_conj_eq_normal J hconj
    have hcard_s0 : Nat.card ((Subgroup.centralizer ({s0} : Set (PGL2 K)) ⊓ J
        : Subgroup (PGL2 K))) = Nat.card U0 :=
      centralizer_derived_card_of_torus_data hJindex U0 s0 w0 hcent0 hw0U
        hwsq0 hwinv0 hU0crossJ
    have hcard_t0 : Nat.card ((Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓ J
        : Subgroup (PGL2 K))) =
        Nat.card ((Subgroup.centralizer ({T.t} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) :=
      (centralizer_card_conj_eq_normal J hconj0).symm
    calc
      Nat.card ((Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) =
          Nat.card ((Subgroup.centralizer ({T.t} : Set (PGL2 K)) ⊓ J
            : Subgroup (PGL2 K))) := hcard_t0
      _ = Nat.card ((Subgroup.centralizer ({s0} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) := hcard_t
      _ = Nat.card U0 := hcard_s0
      _ = 2 * ((Nat.card K - 1) / 2) := by
        rw [hU0card]
        rcases hqOdd with ⟨b, hb⟩
        omega
      _ = 2 * (if Nat.card T.U = Nat.card K - 1 then
            (Nat.card K + 1) / 2
          else
            (Nat.card K - 1) / 2) := by rw [if_neg hU]

set_option maxHeartbeats 800000 in
/-- Swapping the two outer involutions `s` and `ts` produces another
reflected-torus model in which the roles of `R` and `R*` are exchanged.  This
is the model-side symmetry used to transport `R*` through the same odd-core
argument already proved for `R`. -/
private theorem pgl2_low_reflected_tori_data_swap
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    ∃ T2 : PGL2LowReflectedToriData K P eP,
      T2.s = T.t * T.s ∧ T2.t = T.t ∧ T2.g = T.g ∧
      T2.R = T.Rstar ∧ T2.Rstar = T.R := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  let U2 : Subgroup (PGL2 K) :=
    T.U.map (MulAut.conj T.k).toMonoidHom
  let s2 : PGL2 K := T.k * T.s * T.k⁻¹
  let t2 : PGL2 K := T.t
  let k2 : PGL2 K := T.k⁻¹
  let g2 : PGL2 K := T.g
  let R2 : Subgroup (PGL2 K) := T.Rstar
  let Rstar2 : Subgroup (PGL2 K) := T.R
  let w2 : PGL2 K := T.t
  have hs2eq : s2 = T.t * T.s := by
    simpa [s2] using T.k_conj_s
  have hU2cyc : IsCyclic U2 := by
    let eU : T.U ≃* U2 :=
      Subgroup.equivMapOfInjective T.U (MulAut.conj T.k).toMonoidHom
        (MulAut.conj T.k).injective
    exact eU.isCyclic.mp T.U_cyclic
  have hU2card : Nat.card U2 = Nat.card T.U := by
    dsimp [U2]
    exact Subgroup.card_map_of_injective (MulAut.conj T.k).injective
  have hU2half : Odd (Nat.card U2 / 2) := by
    rw [hU2card]
    exact T.U_half_odd
  have hU2order : Nat.card U2 = Nat.card K - 1 ∨
      Nat.card U2 = Nat.card K + 1 := by
    rw [hU2card]
    exact T.U_card
  have htt2 : t2 * t2 = 1 := by
    dsimp [t2]
    simpa [pow_two] using T.t_involution.right
  have hss2 : s2 * s2 = 1 := by
    dsimp [s2]
    calc
      (T.k * T.s * T.k⁻¹) * (T.k * T.s * T.k⁻¹) =
          T.k * (T.s * T.s) * T.k⁻¹ := by group
      _ = 1 := by
        rw [show T.s * T.s = 1 by simpa [pow_two] using T.s_involution.right]
        simp
  have ht2I : IsInvolution t2 := by
    dsimp [t2]
    exact T.t_involution
  have hcomm2 : Commute t2 s2 := by
    dsimp [t2]
    rw [hs2eq]
    calc
      T.t * (T.t * T.s) = T.s := by
        rw [← mul_assoc]
        simpa [pow_two] using congrArg (fun x : PGL2 K => x * T.s)
          T.t_involution.right
      _ = (T.t * T.s) * T.t := by
        rw [mul_assoc, ← T.t_commutes_s.eq, ← mul_assoc]
        rw [show T.t * T.t = 1 by simpa [pow_two] using T.t_involution.right,
          one_mul]
  have hs2U2 : s2 ∈ U2 := by
    dsimp [s2, U2]
    exact Subgroup.mem_map.mpr ⟨T.s, T.s_mem_U, rfl⟩
  have hs2J : s2 ∉ J := by
    intro h
    rw [hs2eq] at h
    have hiff := (J.mul_mem_iff_of_index_two hJindex).mp h
    exact T.s_not_mem_commutator (hiff.mp T.t_mem_commutator)
  have hts2ne : t2 ≠ s2 := by
    intro h
    exact hs2J (by simpa [t2] using h ▸ T.t_mem_commutator)
  have hs2I : IsInvolution s2 := by
    constructor
    · intro h
      apply hs2J
      rw [hs2eq] at h
      rw [hs2eq, h]
      exact J.one_mem
    · simpa [pow_two] using hss2
  have ht2J : t2 ∈ J := by
    dsimp [t2]
    exact T.t_mem_commutator
  have ht2U2 : t2 ∉ U2 := by
    intro htU
    have htsq : t2 * t2 = 1 := htt2
    have htne : t2 ≠ 1 := by
      dsimp [t2]
      exact T.t_involution.1
    have heq := unique_involution_of_cyclic_subgroup (U := U2) (hUcyc := hU2cyc)
      (s := s2) (hsU := hs2U2) (hssq := hss2) (hsne := hs2I.1)
      (x := t2) (hxU := htU) (hxsq := htsq) (hxne := htne)
    exact hts2ne heq
  -- Conjugate centralizer equality: `C(s2) = U2 ⊔ ⟨k w k⁻¹⟩`.
  have hmap_c : (Subgroup.centralizer ({T.s} : Set (PGL2 K))).map
      (MulAut.conj T.k).toMonoidHom =
      Subgroup.centralizer ({s2} : Set (PGL2 K)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyc : y * T.s = T.s * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hy
      have h := congrArg (MulAut.conj T.k) hyc
      simpa [s2] using h
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨(MulAut.conj T.k).symm x, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hx' : x * s2 = s2 * x :=
          Subgroup.mem_centralizer_singleton_iff.mp hx
        calc
          (T.k⁻¹ * x * T.k) * T.s =
              T.k⁻¹ * (x * (T.k * T.s * T.k⁻¹)) * T.k := by group
          _ = T.k⁻¹ * (s2 * x) * T.k := by rw [hx']
          _ = T.s * (T.k⁻¹ * x * T.k) := by
            dsimp [s2]
            group
      · change T.k * (T.k⁻¹ * x * T.k) * T.k⁻¹ = x
        group
  let wk : PGL2 K := T.k * T.w * T.k⁻¹
  have hC2conj : Subgroup.centralizer ({s2} : Set (PGL2 K)) =
      U2 ⊔ Subgroup.zpowers wk := by
    calc
      Subgroup.centralizer ({s2} : Set (PGL2 K)) =
          (Subgroup.centralizer ({T.s} : Set (PGL2 K))).map
            (MulAut.conj T.k).toMonoidHom := hmap_c.symm
      _ = U2 ⊔ Subgroup.zpowers wk := by
        dsimp [U2, wk]
        rw [T.centralizer_eq]
        rw [Subgroup.map_sup]
        rw [MonoidHom.map_zpowers]
        rfl
  have ht2C : t2 ∈ Subgroup.centralizer ({s2} : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm2.eq
  have hwk2_inv : ∀ x : PGL2 K, x ∈ U2 → wk * x * wk⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hwinvy := T.w_inverts_U y hy
    dsimp [wk]
    calc
      (T.k * T.w * T.k⁻¹) * (T.k * y * T.k⁻¹) * (T.k * T.w * T.k⁻¹)⁻¹ =
          T.k * (T.w * y * T.w⁻¹) * T.k⁻¹ := by group
      _ = T.k * y⁻¹ * T.k⁻¹ := by rw [hwinvy]
      _ = (T.k * y * T.k⁻¹)⁻¹ := by group
  have hwk_not_U2 : wk ∉ U2 := by
    intro h
    rcases Subgroup.mem_map.mp h with ⟨y, hyU, hywk⟩
    apply T.w_not_mem_U
    have hwy : T.w = y := by
      have hw : T.k * T.w * T.k⁻¹ = T.k * y * T.k⁻¹ := by
        simpa [wk] using hywk.symm
      calc
        T.w = T.k⁻¹ * (T.k * T.w * T.k⁻¹) * T.k := by group
        _ = T.k⁻¹ * (T.k * y * T.k⁻¹) * T.k := by rw [hw]
        _ = y := by group
    simpa [hwy] using hyU
  have hwk_sq : wk * wk = 1 := by
    dsimp [wk]
    calc
      (T.k * T.w * T.k⁻¹) * (T.k * T.w * T.k⁻¹) =
          T.k * (T.w * T.w) * T.k⁻¹ := by group
      _ = 1 := by
        rw [T.w_involution]
        simp
  have ht2mem : t2 ∈ U2 ⊔ Subgroup.zpowers wk := by
    rw [← hC2conj]
    exact ht2C
  have hC2eq : Subgroup.centralizer ({s2} : Set (PGL2 K)) =
      U2 ⊔ Subgroup.zpowers t2 := by
    have hwk_mem : wk ∈ U2 ⊔ Subgroup.zpowers t2 := by
      rcases (mem_sup_zpowers_of_involution_inverts hwk_not_U2 hwk_sq
          hwk2_inv).mp ht2mem with ⟨a, haU, htab | htab⟩
      · exfalso
        exact ht2U2 (by simpa [htab] using haU)
      · have hwk_t : wk = (a : PGL2 K)⁻¹ * t2 := by
          calc
            wk = (a : PGL2 K)⁻¹ * ((a : PGL2 K) * wk) := by group
            _ = (a : PGL2 K)⁻¹ * t2 := by
              congr 1
              simpa [htab] using htab.symm
        rw [hwk_t]
        exact Subgroup.mul_mem_sup (Subgroup.inv_mem U2 haU) (Subgroup.mem_zpowers t2)
    apply le_antisymm
    · rw [hC2conj]
      apply sup_le
      · exact le_sup_left
      · rw [Subgroup.zpowers_le]
        exact hwk_mem
    · apply sup_le
      · rw [hC2conj]
        exact le_sup_left
      · rw [hC2conj, Subgroup.zpowers_le]
        exact ht2mem
  have htinvs2 : ∀ x : PGL2 K, x ∈ U2 → t2 * x * t2⁻¹ = x⁻¹ := by
    intro x hx
    rcases (mem_sup_zpowers_of_involution_inverts hwk_not_U2 hwk_sq
        hwk2_inv).mp ht2mem with ⟨a, haU, htab | htab⟩
    · exfalso
      exact ht2U2 (by simpa [htab] using haU)
    · have ht2eq : t2 = (a : PGL2 K) * wk := htab
      let : IsCyclic U2 := hU2cyc
      let : CommGroup U2 := IsCyclic.commGroup
      have ha_comm : a * x = x * a := by
        have h := mul_comm (⟨a, haU⟩ : U2) (⟨x, hx⟩ : U2)
        simpa using congrArg Subtype.val h
      calc
        t2 * x * t2⁻¹ = ((a : PGL2 K) * wk) * x * ((a : PGL2 K) * wk)⁻¹ := by
          rw [ht2eq]
        _ = (a : PGL2 K) * (wk * x * wk⁻¹) * (a : PGL2 K)⁻¹ := by group
        _ = (a : PGL2 K) * x⁻¹ * (a : PGL2 K)⁻¹ := by rw [hwk2_inv x hx]
        _ = x⁻¹ := by
          have hxU : x⁻¹ ∈ U2 := U2.inv_mem hx
          have h := mul_comm (⟨a, haU⟩ : U2) (⟨x⁻¹, hxU⟩ : U2)
          have hval : (a : PGL2 K) * x⁻¹ = x⁻¹ * (a : PGL2 K) :=
            by simpa using congrArg Subtype.val h
          calc
            (a : PGL2 K) * x⁻¹ * (a : PGL2 K)⁻¹ =
                x⁻¹ * (a : PGL2 K) * (a : PGL2 K)⁻¹ := by rw [hval]
            _ = x⁻¹ := by group
  have hk2J : k2 ∈ J := by
    dsimp [k2]
    exact J.inv_mem T.k_mem_commutator
  have hk2s : k2 * s2 * k2⁻¹ = t2 * s2 := by
    dsimp [k2, t2]
    rw [hs2eq]
    simp only [inv_inv]
    calc
      T.k⁻¹ * (T.t * T.s) * T.k = T.s := by
        rw [← hs2eq]
        change T.k⁻¹ * (T.k * T.s * T.k⁻¹) * T.k = T.s
        group
      _ = T.t * (T.t * T.s) := by
        calc
          T.s = 1 * T.s := by simp
          _ = (T.t * T.t) * T.s := by
            rw [show T.t * T.t = 1 by simpa [pow_two] using T.t_involution.right]
          _ = T.t * (T.t * T.s) := by group
  have hR2eq : R2 = U2 ⊓ J := by
    dsimp [R2, U2, J]
    rw [T.Rstar_eq, T.R_eq]
    rw [Subgroup.map_inf _ _ (MulAut.conj T.k).toMonoidHom
      (MulAut.conj T.k).injective]
    have hmapJ : (commutator (PGL2 K)).map (MulAut.conj T.k).toMonoidHom =
        commutator (PGL2 K) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (inferInstance : (commutator (PGL2 K)).Normal).conj_mem y hy T.k
      · intro hx
        rw [Subgroup.mem_map]
        refine ⟨(MulAut.conj T.k).symm x, ?_, ?_⟩
        · have hx' : (MulAut.conj T.k).symm x ∈ commutator (PGL2 K) := by
            simpa using (inferInstance : (commutator (PGL2 K)).Normal).conj_mem
              x hx T.k⁻¹
          exact hx'
        · change T.k * (T.k⁻¹ * x * T.k) * T.k⁻¹ = x
          group
    rw [hmapJ]
    rfl
  have hRstar2eq : Rstar2 = R2.map (MulAut.conj k2).toMonoidHom := by
    dsimp [Rstar2, R2, k2]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨T.k * x * T.k⁻¹, ?_, ?_⟩
      · rw [T.Rstar_eq]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · dsimp [MulAut.conj_apply]
        group
    · intro hy
      rw [Subgroup.mem_map] at hy
      rcases hy with ⟨z, hz, rfl⟩
      rw [T.Rstar_eq] at hz
      rcases hz with ⟨r, hr, rfl⟩
      have hxr : (MulAut.conj T.k⁻¹) ((MulAut.conj T.k) r) = r := by
        dsimp [MulAut.conj_apply]
        group
      change (MulAut.conj T.k⁻¹) ((MulAut.conj T.k) r) ∈ T.R
      rw [hxr]
      exact hr
  have hR2odd : Odd (Nat.card R2) := by
    dsimp [R2]
    rw [T.Rstar_eq, Subgroup.card_map_of_injective (MulAut.conj T.k).injective]
    exact T.R_card_odd
  have hR2gt : 1 < Nat.card R2 := by
    dsimp [R2]
    rw [T.Rstar_eq, Subgroup.card_map_of_injective (MulAut.conj T.k).injective]
    exact T.R_card_gt_one
  have hR2cent : R2 ≤ Subgroup.centralizer ({s2} : Set (PGL2 K)) := by
    intro x hx
    rw [hs2eq]
    exact T.Rstar_le_centralizer_ts hx
  have hRstar2cent : Rstar2 ≤ Subgroup.centralizer ({t2 * s2} : Set (PGL2 K)) := by
    intro x hx
    have hs2val : t2 * s2 = T.s := by
      dsimp [t2]
      change T.t * s2 = T.s
      rw [hs2eq]
      calc
        T.t * (T.t * T.s) = (T.t * T.t) * T.s := by group
        _ = 1 * T.s := by
          rw [show T.t * T.t = 1 by simpa [pow_two] using T.t_involution.right]
        _ = T.s := by simp
    rw [hs2val]
    exact T.R_le_centralizer_s hx
  have hg2_s : T.g * s2 * T.g⁻¹ ∈ (P : Subgroup (PGL2 K)) := by
    have hgtP : T.g * T.t * T.g⁻¹ ∈ (P : Subgroup (PGL2 K)) := by
      rw [T.conj_t_eq_central]
      exact (eP.symm (DihedralGroup.r
        (2 ^ (m - 1) : ZMod (2 ^ m)))).2
    have hgsP : T.g * T.s * T.g⁻¹ ∈ (P : Subgroup (PGL2 K)) :=
      T.conj_s_mem_P
    rw [hs2eq]
    change T.g * (T.t * T.s) * T.g⁻¹ ∈ (P : Subgroup (PGL2 K))
    have hprod : T.g * (T.t * T.s) * T.g⁻¹ =
        (T.g * T.t * T.g⁻¹) * (T.g * T.s * T.g⁻¹) := by group
    rw [hprod]
    exact P.mul_mem hgtP hgsP
  have hjoin : ((R2 ⊔ Subgroup.zpowers t2) ⊔ Rstar2) =
      ((T.R ⊔ Subgroup.zpowers T.t) ⊔ T.Rstar) := by
    dsimp [R2, Rstar2, t2]
    simp [sup_assoc, sup_comm, sup_left_comm]
  have hfour2 : 4 ∣ Nat.card (↥((R2 ⊔ Subgroup.zpowers t2) ⊔ Rstar2)) := by
    rw [hjoin]
    exact T.four_dvd_card
  exact ⟨⟨U2, s2, t2, k2, g2, R2, Rstar2,
    hU2cyc, hU2half, hU2order,
    hs2I, ht2I, hcomm2,
    hs2U2, hs2J,
    ht2J, ht2U2, htinvs2,
    w2, Or.inl rfl, ht2U2, htt2, htinvs2, hC2eq,
    hk2J, hk2s,
    hR2eq, hRstar2eq, hR2odd, hR2gt,
    hR2cent, hRstar2cent,
    (by
      intro x hx
      exact T.Rstar_le_commutator hx),
    (by
      intro x hx
      exact T.R_le_commutator hx),
    hg2_s, T.conj_t_eq_central, hfour2⟩,
    hs2eq, rfl, rfl, rfl, rfl⟩

/-- In the odd `PGL₂` model, the commutator of the inner reflector with the
derived-subgroup centralizer of the opposite outer involution is contained in
the second reflected torus `R*`.  This is the model-side half of the
`N_G(R*) ⊇ Syl₂(C_G(ts))` transfer: `R*` is the derived subgroup of
`J ⊓ C_G(ts)`. -/
private lemma pgl2_Rstar_commutator_le_Rstar
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    let J : Subgroup (PGL2 K) := commutator (PGL2 K)
    let C : Subgroup (PGL2 K) :=
      J ⊓ Subgroup.centralizer ({T.t * T.s} : Set (PGL2 K))
    ⁅Subgroup.zpowers T.t, C⁆ ≤ T.Rstar := by
  classical
  intro J C
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    rw [hKcard]
    exact hpOdd.pow
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  let : J.Normal := by
    dsimp [J]
    infer_instance
  let n : ℕ := Nat.card T.U / 2
  have hUtwo : Nat.card T.U = 2 * n := by
    dsimp [n]
    rcases T.U_card with hU | hU
    · rw [hU]
      rcases hqOdd with ⟨a, ha⟩
      omega
    · rw [hU]
      rcases hqOdd with ⟨a, ha⟩
      omega
  have hUJ : ¬ T.U ≤ J := by
    intro h
    exact T.s_not_mem_commutator (h T.s_mem_U)
  have hCcard : Nat.card C = 2 * n := by
    dsimp [C, n]
    have hconj : T.k * T.s * T.k⁻¹ = T.t * T.s := T.k_conj_s
    have hcard_s : Nat.card ((Subgroup.centralizer ({T.s} : Set (PGL2 K)) ⊓ J)
        : Subgroup (PGL2 K)) = Nat.card T.U :=
      centralizer_derived_card_of_torus_data hJindex T.U T.s T.w
        T.centralizer_eq T.w_not_mem_U T.w_involution T.w_inverts_U hUJ
    have hcard_ts : Nat.card ((Subgroup.centralizer ({T.t * T.s} : Set (PGL2 K)) ⊓ J)
        : Subgroup (PGL2 K)) = Nat.card T.U := by
      calc
        Nat.card ((Subgroup.centralizer ({T.t * T.s} : Set (PGL2 K)) ⊓ J)
            : Subgroup (PGL2 K)) =
            Nat.card ((Subgroup.centralizer ({T.s} : Set (PGL2 K)) ⊓ J)
              : Subgroup (PGL2 K)) :=
          (centralizer_card_conj_eq_normal J hconj).symm
        _ = Nat.card T.U := hcard_s
    calc
      Nat.card C = Nat.card ((Subgroup.centralizer ({T.t * T.s} : Set (PGL2 K)) ⊓ J)
          : Subgroup (PGL2 K)) := by
        rw [inf_comm]
      _ = Nat.card T.U := hcard_ts
      _ = 2 * n := hUtwo
  have hRstar_card : Nat.card T.Rstar = n := by
    dsimp [n]
    rw [T.Rstar_eq, Subgroup.card_map_of_injective (MulAut.conj T.k).injective]
    exact pgl2_reflected_torus_R_card_eq_half hK hcard P eP T
  have hRstar_leC : T.Rstar ≤ C := by
    intro x hx
    exact ⟨T.Rstar_le_commutator hx, T.Rstar_le_centralizer_ts hx⟩
  let RD : Subgroup C := T.Rstar.subgroupOf C
  have hRDcard : Nat.card RD = Nat.card T.Rstar :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRstar_leC).toEquiv
  have hnpos : 0 < n := by
    rw [← hRstar_card]
    exact Nat.card_pos
  have hRDindex : RD.index = 2 := by
    have hmul := RD.index_mul_card
    rw [hRDcard, hRstar_card, hCcard] at hmul
    exact Nat.eq_of_mul_eq_mul_right hnpos hmul
  have hRDnormal : RD.Normal := Subgroup.normal_of_index_eq_two hRDindex
  have hcommC_le_RD : commutator C ≤ RD :=
    commutator_le_of_normal_index_two (G := C) RD hRDnormal hRDindex
  have hcommC_amb_le_Rstar :
      ((commutator C).map C.subtype : Subgroup (PGL2 K)) ≤ T.Rstar := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hcommC_le_RD hy)
  have hcommC_amb : (commutator C).map C.subtype = ⁅C, C⁆ :=
    C.map_subtype_commutator
  have hCcomm_le_Rstar : (⁅C, C⁆ : Subgroup (PGL2 K)) ≤ T.Rstar := by
    rw [← hcommC_amb]
    exact hcommC_amb_le_Rstar
  have htJ : T.t ∈ J := by simpa [J] using T.t_mem_commutator
  have htC : T.t ∈ Subgroup.centralizer ({T.t * T.s} : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      T.t * (T.t * T.s) = T.s := by
        rw [← mul_assoc]
        simpa [pow_two] using congrArg (fun x : PGL2 K => x * T.s) T.t_involution.right
      _ = (T.t * T.s) * T.t := by
        rw [mul_assoc, ← T.t_commutes_s.eq, ← mul_assoc]
        rw [show T.t * T.t = 1 by simpa [pow_two] using T.t_involution.right, one_mul]
  have hZt_leC : Subgroup.zpowers T.t ≤ C := by
    intro x hx
    exact ⟨Subgroup.zpowers_le.mpr htJ hx, Subgroup.zpowers_le.mpr htC hx⟩
  exact (Subgroup.commutator_mono hZt_leC le_rfl).trans hCcomm_le_Rstar

/-- The two halves of `q±1` are coprime for odd `q`. -/
private lemma coprime_halves_of_odd {q : ℕ} (hq : Odd q) :
    Nat.Coprime ((q - 1) / 2) ((q + 1) / 2) := by
  rcases hq with ⟨a, ha⟩
  have h1 : (2 * a + 1 - 1) / 2 = a := by omega
  have h2 : (2 * a + 1 + 1) / 2 = a + 1 := by omega
  rw [ha, h1, h2]
  rw [Nat.coprime_comm]
  exact (Nat.coprime_self_add_left (m := a) (n := 1)).2 (Nat.coprime_one_left a)

/-! ## First containment: `R^y ≤ O(Ĥ)` -/

/-- Conjugation transport of a subgroup containment into a conjugate
subgroup, in both directions. -/
public theorem map_conj_le_iff_le_conjugate_t26
    {G : Type u} [Group G] (H : Subgroup G) (y : G)
    (A : Subgroup G) (hy2 : y * y = 1) :
    A.map (MulAut.conj y).toMonoidHom ≤ H ↔ A ≤ conjugateSubgroup H y := by
  classical
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  constructor
  · intro hA x hx
    rw [conjugateSubgroup, Subgroup.mem_map]
    refine ⟨y * x * y⁻¹, hA (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), ?_⟩
    change y * (y * x * y⁻¹) * y⁻¹ = x
    rw [hyinv]
    have hstep : y * (y * x * y) * y = (y * y) * x * (y * y) := by
      group
    rw [hstep]
    rw [hy2]
    simp
  · intro hA x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have ha' : a ∈ conjugateSubgroup H y := hA ha
    rw [conjugateSubgroup, Subgroup.mem_map] at ha'
    rcases ha' with ⟨b, hb, hba⟩
    have hba' : y * a * y⁻¹ = b := by
      calc
        y * a * y⁻¹ = y * (y * b * y⁻¹) * y⁻¹ := by
          rw [← hba]
          rfl
        _ = b := by
          rw [hyinv]
          have hstep : y * (y * b * y) * y = (y * y) * b * (y * y) := by
            group
          rw [hstep]
          rw [hy2]
          simp
    simpa [hba'] using hb

/-- The quotient image of the conjugated reflected torus is trivial.  This
is the model-transport core: the image lies in the `PSL₂` component, is
cyclic of odd order dividing the odd low-torus half, and is centralized by
the distinguished inner involution, so the Dickson partition kills it. -/
public structure Theorem26OuterLiftData
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (e : L ≃* PGL2 K) where
  Pmodel : Sylow 2 (PGL2 K)
  eP : Pmodel ≃* DihedralGroup (2 ^ c.m)
  T : PGL2LowReflectedToriData K Pmodel eP
  s : G
  hsS : s ∈ (c.S : Subgroup G)
  hsI : IsInvolution s
  hsE : s ∉ d.E
  hcomm : Commute c.t s
  sL : L
  tL : L
  hsL : (sL : c.Hhat ⧸ pPrimeCore 2 c.Hhat) =
    QuotientGroup.mk' (pPrimeCore 2 c.Hhat)
      ⟨s, ((S_le_H c).trans c.H_le_Hhat) hsS⟩
  htL : (tL : c.Hhat ⧸ pPrimeCore 2 c.Hhat) =
    QuotientGroup.mk' (pPrimeCore 2 c.Hhat)
      ⟨c.t, ((S_le_H c).trans c.H_le_Hhat) (c.S0_le_S c.t_mem_S0)⟩
  hs0eq : e sL = T.g * T.s * T.g⁻¹
  ht0eq : e tL = T.g * T.t * T.g⁻¹

/-- Package the model-bearing outer lift returned by
`pgl2_outer_involution_lift` into a structure the transport helpers can
consume. -/
public theorem exists_theorem26_outer_lift_data
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    Nonempty (Theorem26OuterLiftData d K L e) := by
  obtain ⟨Pmodel, eP, T, s, hsS, hsI, hsE, hcomm, hs0eq, ht0eq⟩ :=
    d.pgl2_outer_involution_lift K hK L hLnormal hLindex e
  let hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  let Pq : Sylow 2 (c.Hhat ⧸ pPrimeCore 2 c.Hhat) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 c.Hhat))
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  let sH : c.Hhat := ⟨s, hSle hsS⟩
  let tH : c.Hhat := ⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩
  let sL : L := ⟨QuotientGroup.mk' (pPrimeCore 2 c.Hhat) sH,
    hPqL (Subgroup.mem_map.mpr ⟨sH, hsS, rfl⟩)⟩
  let tL : L := ⟨QuotientGroup.mk' (pPrimeCore 2 c.Hhat) tH,
    hPqL (Subgroup.mem_map.mpr ⟨tH, c.S0_le_S c.t_mem_S0, rfl⟩)⟩
  exact ⟨⟨Pmodel, eP, T, s, hsS, hsI, hsE, hcomm, sL, tL,
    rfl, rfl, hs0eq, ht0eq⟩⟩

/-- The swapped outer lift: replace the outer torus involution `s` by the
opposite outer involution `ts` and the reflected torus `R` by `R*`.  The
existing odd-core transport then applies verbatim to `R*`. -/
public theorem exists_theorem26_outer_lift_data_swap
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e) :
    ∃ ld2 : Theorem26OuterLiftData d K L e,
      ld2.s = c.t * ld.s ∧ ld2.T.s = ld.T.t * ld.T.s ∧
      ld2.T.g = ld.T.g ∧ ld2.T.t = ld.T.t ∧
      ld2.T.R = ld.T.Rstar ∧ ld2.T.Rstar = ld.T.R := by
  classical
  have hend := d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e
  rcases hend with ⟨hEnormal, htE, _hfuse, _hcent⟩
  rcases d.pgl2_component_image_eq_commutator K hK L hLnormal hLindex e with
    ⟨hcard, _⟩
  obtain ⟨T2, hT2s, hT2t, hT2g, hT2R, hT2Rstar⟩ :=
    pgl2_low_reflected_tori_data_swap hK hcard ld.Pmodel ld.eP ld.T
  let s2 : G := c.t * ld.s
  have htt : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
  have hss : ld.s * ld.s = 1 := by simpa [pow_two] using ld.hsI.2
  have hsS2 : s2 ∈ (c.S : Subgroup G) := by
    exact (c.S : Subgroup G).mul_mem (c.S0_le_S c.t_mem_S0) ld.hsS
  have htsne : c.t ≠ ld.s := by
    intro h
    exact ld.hsE (by simpa [h] using htE)
  have hsI2 : IsInvolution s2 := by
    constructor
    · intro h
      apply htsne
      calc
        c.t = c.t * 1 := by simp
        _ = c.t * (ld.s * ld.s) := by rw [hss]
        _ = (c.t * ld.s) * ld.s := by group
        _ = 1 * ld.s := by
          change s2 * ld.s = 1 * ld.s
          rw [h]
        _ = ld.s := by simp
    · simpa [s2, pow_two] using
        (show (c.t * ld.s) * (c.t * ld.s) = 1 by
          calc
            (c.t * ld.s) * (c.t * ld.s) =
                c.t * (ld.s * c.t) * ld.s := by group
            _ = c.t * (c.t * ld.s) * ld.s := by rw [← ld.hcomm.eq]
            _ = (c.t * c.t) * (ld.s * ld.s) := by group
            _ = 1 := by rw [htt, hss]; simp)
  have hsE2 : s2 ∉ d.E := by
    intro h
    apply ld.hsE
    have hval : ld.s = c.t * (c.t * ld.s) := by
      calc
        ld.s = (c.t * c.t) * ld.s := by rw [htt]; simp
        _ = c.t * (c.t * ld.s) := by group
    rw [hval]
    exact d.E.mul_mem htE h
  have hcomm2 : Commute c.t s2 := by
    show c.t * s2 = s2 * c.t
    dsimp [s2]
    calc
      c.t * (c.t * ld.s) = ld.s := by
        rw [← mul_assoc]
        simpa [pow_two] using congrArg (fun x : G => x * ld.s) htt
      _ = (c.t * ld.s) * c.t := by
        rw [mul_assoc, ← ld.hcomm.eq, ← mul_assoc]
        rw [htt, one_mul]
  let hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  let Pq : Sylow 2 (c.Hhat ⧸ pPrimeCore 2 c.Hhat) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 c.Hhat))
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  let sH2 : c.Hhat := ⟨s2, hSle hsS2⟩
  let tH2 : c.Hhat := ⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩
  let sL2 : L := ⟨QuotientGroup.mk' (pPrimeCore 2 c.Hhat) sH2,
    hPqL (Subgroup.mem_map.mpr ⟨sH2, hsS2, rfl⟩)⟩
  let tL2 : L := ⟨QuotientGroup.mk' (pPrimeCore 2 c.Hhat) tH2,
    hPqL (Subgroup.mem_map.mpr ⟨tH2, c.S0_le_S c.t_mem_S0, rfl⟩)⟩
  have hqmul : QuotientGroup.mk' (pPrimeCore 2 c.Hhat)
        (⟨c.t * ld.s, hSle hsS2⟩ : c.Hhat) =
      QuotientGroup.mk' (pPrimeCore 2 c.Hhat)
        (⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩ : c.Hhat) *
      QuotientGroup.mk' (pPrimeCore 2 c.Hhat)
        (⟨ld.s, hSle ld.hsS⟩ : c.Hhat) := by
    simpa [s2] using
      (QuotientGroup.mk' (pPrimeCore 2 c.Hhat)).map_mul
        (⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩ : c.Hhat)
        (⟨ld.s, hSle ld.hsS⟩ : c.Hhat)
  have hsL2_eq : (sL2 : c.Hhat ⧸ pPrimeCore 2 c.Hhat) =
      (ld.tL : c.Hhat ⧸ pPrimeCore 2 c.Hhat) *
        (ld.sL : c.Hhat ⧸ pPrimeCore 2 c.Hhat) := by
    dsimp [sL2, s2]
    rw [ld.htL, ld.hsL]
    exact hqmul
  have htL2_eq : tL2 = ld.tL := by
    apply Subtype.ext
    exact ld.htL.symm
  have hs0eq2 : e sL2 = T2.g * T2.s * T2.g⁻¹ := by
    rw [hT2g, hT2s]
    calc
      e sL2 = e (ld.tL * ld.sL) := by
        apply congrArg e
        apply Subtype.ext
        exact hsL2_eq
      _ = e ld.tL * e ld.sL := e.map_mul _ _
      _ = (ld.T.g * ld.T.t * ld.T.g⁻¹) *
          (ld.T.g * ld.T.s * ld.T.g⁻¹) := by rw [ld.ht0eq, ld.hs0eq]
      _ = ld.T.g * (ld.T.t * ld.T.s) * ld.T.g⁻¹ := by group
  have ht0eq2 : e tL2 = T2.g * T2.t * T2.g⁻¹ := by
    rw [hT2g, hT2t]
    calc
      e tL2 = e ld.tL := by rw [htL2_eq]
      _ = ld.T.g * ld.T.t * ld.T.g⁻¹ := ld.ht0eq
  exact ⟨⟨ld.Pmodel, ld.eP, T2, s2, hsS2, hsI2, hsE2, hcomm2,
    sL2, tL2, rfl, rfl, hs0eq2, ht0eq2⟩,
    rfl, hT2s, hT2g, hT2t, hT2R, hT2Rstar⟩

/-- In the odd `PGL₂` model, the conjugated reflected commutator for the
opposite outer involution is exactly the conjugate of the reflected torus
`R*`. -/
public theorem pgl2_reflected_outer_commutator_eq_conj_Rstar
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    let C1 : Subgroup (PGL2 K) :=
      ⁅Subgroup.zpowers (T.g * T.t * T.g⁻¹),
        commutator (PGL2 K) ⊓ Subgroup.centralizer
          ({T.g * (T.t * T.s) * T.g⁻¹} : Set (PGL2 K))⁆
    C1 = T.Rstar.map (MulAut.conj T.g).toMonoidHom := by
  classical
  intro C1
  obtain ⟨T2, hT2s, hT2t, hT2g, hT2R, _hT2Rstar⟩ :=
    pgl2_low_reflected_tori_data_swap hK hcard P eP T
  have hs0 : T.g * (T.t * T.s) * T.g⁻¹ = T2.g * T2.s * T2.g⁻¹ := by
    rw [hT2g, hT2s]
  have ht0 : T.g * T.t * T.g⁻¹ = T2.g * T2.t * T2.g⁻¹ := by
    rw [hT2g, hT2t]
  have hEq := pgl2_reflected_outer_commutator_eq_conj_R hK hcard P eP T2
    (s0 := T.g * (T.t * T.s) * T.g⁻¹) (t0 := T.g * T.t * T.g⁻¹)
    (hs0 := hs0) (ht0 := ht0)
  dsimp at hEq
  change (⁅Subgroup.zpowers (T.g * T.t * T.g⁻¹),
      commutator (PGL2 K) ⊓ Subgroup.centralizer
        ({T.g * (T.t * T.s) * T.g⁻¹} : Set (PGL2 K))⁆ =
      T.Rstar.map (MulAut.conj T.g).toMonoidHom)
  rw [hEq, hT2R, hT2g]
  rfl

set_option maxHeartbeats 800000 in
public theorem reflected_R_image_outer_torus_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e)
    {y : G} (hyI : IsInvolution y) (hyts : y * c.t * y⁻¹ = ld.s)
    {n : ℕ} (hn : n = (Nat.card K - 1) / 2 ∨ n = (Nat.card K + 1) / 2)
    (hnodd : Odd n) :
    let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
    let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
    let CEs : Subgroup G := Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    let RH : Subgroup c.Hhat := R.subgroupOf c.Hhat
    let Rbar : Subgroup (c.Hhat ⧸ O) := RH.map q
    let R0 : Subgroup (PGL2 K) := (Rbar.subgroupOf L).map e.toMonoidHom
    let C1 : Subgroup (PGL2 K) :=
      ⁅Subgroup.zpowers (ld.T.g * ld.T.t * ld.T.g⁻¹),
        commutator (PGL2 K) ⊓ Subgroup.centralizer
          ({ld.T.g * ld.T.s * ld.T.g⁻¹} : Set (PGL2 K))⁆
    Rbar ≤ L ∧ IsCyclic R0 ∧ Nat.card R0 = n ∧ R0 = C1 ∧
      ∀ r : G, r ∈ R → r ∈ (O.map c.Hhat.subtype) → r = 1 := by
  classical
  intro O q CEs R RH Rbar R0 C1
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    rw [hKcard]
    exact hpOdd.pow
  have hcomp := d.pgl2_component_image_eq_commutator K hK L hLnormal hLindex e
  dsimp at hcomp
  rcases hcomp with ⟨hcard, _hEbarne, _hEbarperf, _hEbarsn, hEbarL, hJeq⟩
  have hend := d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e
  dsimp at hend
  rcases hend with ⟨hEnormal, htE, _hfuse, _hcent⟩
  have hRle := reflected_R_le_inter_of_conjugator_t26 c d.E
      htE d.isComponent.1 ld.hsS hyts hy2
  have hRleE : R ≤ d.E := hRle.1
  have hRleH : R ≤ c.Hhat := hRle.2.1
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
  let eEi : Ei ≃* d.E := Subgroup.subgroupOfEquivOfLe d.isComponent.1
  have hOodd : Odd (Nat.card O) := by
    have hOcop : Nat.Coprime 2 (Nat.card O) := by
      simpa [O] using (pPrimeCore_coprime_card (p := 2) (G := c.Hhat))
    exact Nat.coprime_two_left.mp hOcop
  have hkerdata := d.pgl2_component_kernel_eq_center K hK L hLnormal hLindex e
  dsimp [O, q, Ei, Ebar] at hkerdata
  rcases hkerdata with ⟨hker, _⟩
  have hZEi_odd : Odd (Nat.card (Subgroup.center Ei)) := by
    let : O.Normal := by
      dsimp [O]
      infer_instance
    exact center_odd_of_quotient_restriction_ker_eq_center Ei O hOodd hker
  have hZodd : Odd (Nat.card ((Subgroup.center d.E).map d.E.subtype)) := by
    have hcenterMap : (Subgroup.center Ei).map eEi.toMonoidHom =
        Subgroup.center d.E := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro z
        have hz : z = eEi (eEi.symm z) := (eEi.apply_symm_apply _).symm
        rw [hz]
        change eEi (eEi.symm z) * eEi y = eEi y * eEi (eEi.symm z)
        rw [← map_mul, ← map_mul]
        exact congrArg eEi (Subgroup.mem_center_iff.mp hy (eEi.symm z))
      · intro hx
        rw [Subgroup.mem_map]
        refine ⟨eEi.symm x, ?_, ?_⟩
        · rw [Subgroup.mem_center_iff]
          intro z
          apply MulEquiv.injective eEi
          rw [map_mul, map_mul]
          exact Subgroup.mem_center_iff.mp hx (eEi z)
        · simp
    have hcard1 : Nat.card (Subgroup.center d.E) =
        Nat.card (Subgroup.center Ei) := by
      calc
        Nat.card (Subgroup.center d.E) =
            Nat.card ((Subgroup.center Ei).map eEi.toMonoidHom) := by
              rw [hcenterMap]
        _ = Nat.card (Subgroup.center Ei) :=
          Subgroup.card_map_of_injective eEi.injective
    have hcard2 : Nat.card ((Subgroup.center d.E).map d.E.subtype) =
        Nat.card (Subgroup.center d.E) :=
      Subgroup.card_map_of_injective d.E.subtype_injective
    rw [hcard2, hcard1]
    exact hZEi_odd
  have hEamb_local : ∀ {h x : G}, h ∈ c.Hhat → x ∈ d.E → h * x * h⁻¹ ∈ d.E := by
    intro h x hh hx
    let hH : c.Hhat := ⟨h, hh⟩
    let xH : c.Hhat := ⟨x, d.isComponent.1 hx⟩
    have hxEi : xH ∈ d.E.subgroupOf c.Hhat := Subgroup.mem_subgroupOf.mpr hx
    have hconj : hH * xH * hH⁻¹ ∈ d.E.subgroupOf c.Hhat :=
      hEnormal.conj_mem xH hxEi hH
    exact Subgroup.mem_subgroupOf.mp hconj
  have hss : ld.s * ld.s = 1 := by simpa [pow_two] using ld.hsI.2
  have hsN : ld.s ∈ Subgroup.normalizer (d.E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hEamb_local (((S_le_H c).trans c.H_le_Hhat) ld.hsS) hx
    · intro hx
      have hx' : ld.s⁻¹ * (ld.s * x * ld.s⁻¹) * (ld.s⁻¹)⁻¹ ∈ d.E :=
        hEamb_local (c.Hhat.inv_mem (((S_le_H c).trans c.H_le_Hhat) ld.hsS))
          hx
      have hx'' : ld.s⁻¹ * (ld.s * x * ld.s⁻¹) * ld.s = x := by group
      simpa [hx''] using hx'
  have hsE : Subgroup.zpowers ld.s ≤ Subgroup.normalizer (d.E : Set G) :=
    Subgroup.zpowers_le.mpr hsN
  let fEi : Ei →* Ebar :=
    (q.comp Ei.subtype).codRestrict Ebar (fun x =>
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hker' : fEi.ker = Subgroup.center Ei := by
    simpa [fEi] using hker
  have hRbarL : Rbar ≤ L := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨rH, hrRH, rfl⟩
    have hrE : (rH : G) ∈ d.E := hRleE hrRH
    have hrEi : rH ∈ Ei := Subgroup.mem_subgroupOf.mpr hrE
    have hxE : q rH ∈ Ebar := Subgroup.mem_map.mpr ⟨rH, hrEi, rfl⟩
    exact hEbarL hxE
  have hSleG : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSleG
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ O)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  let tH : c.Hhat := ⟨c.t, hSleG (c.S0_le_S c.t_mem_S0)⟩
  let TH : Subgroup c.Hhat := (Subgroup.zpowers c.t).subgroupOf c.Hhat
  let CEH : Subgroup c.Hhat := CEs.subgroupOf c.Hhat
  let Lpre : Subgroup c.Hhat := Subgroup.comap q L
  have hTH_le : TH ≤ Lpre := by
    intro x hx
    rcases (Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)) with ⟨k, hk⟩
    have hxeq : x = tH ^ k := by
      apply Subtype.ext
      simpa [tH] using hk.symm
    rw [hxeq]
    change q (tH ^ k) ∈ L
    have htP : tH ∈ (P : Subgroup c.Hhat) := c.S0_le_S c.t_mem_S0
    have hqP : q (tH ^ k) ∈ (Pq : Subgroup (c.Hhat ⧸ O)) := by
      change q (tH ^ k) ∈ (P : Subgroup c.Hhat).map q
      exact Subgroup.mem_map.mpr ⟨tH ^ k, (P : Subgroup c.Hhat).zpow_mem htP k, rfl⟩
    exact hPqL hqP
  have hCEH_le : CEH ≤ Lpre := by
    intro x hx
    change q x ∈ L
    have hxE : (x : G) ∈ d.E :=
      (inf_le_right : CEs ≤ d.E) (Subgroup.mem_subgroupOf.mp hx)
    have hxEi : x ∈ Ei := Subgroup.mem_subgroupOf.mpr hxE
    have hqE : q x ∈ Ebar := Subgroup.mem_map.mpr ⟨x, hxEi, rfl⟩
    exact hEbarL hqE
  let S : Subgroup c.Hhat := TH ⊔ CEH
  have hS_le : S ≤ Lpre := sup_le hTH_le hCEH_le
  let f : S →* PGL2 K :=
    e.toMonoidHom.comp ((q.comp S.subtype).codRestrict L
      (fun x => by
        change q (x : c.Hhat) ∈ L
        exact Subgroup.mem_comap.mp (hS_le x.2)))
  have hRH_eq : RH = ⁅TH, CEH⁆ := by
    have hRHmap : RH.map c.Hhat.subtype = R := by
      simpa [RH] using Subgroup.map_subgroupOf_eq_of_le hRleH
    have hcommmap : (⁅TH, CEH⁆).map c.Hhat.subtype = R := by
      have hmap' := commutator_subgroupOf_map_eq c.Hhat CEs (Subgroup.zpowers c.t)
        ((inf_le_right : CEs ≤ d.E).trans d.isComponent.1)
        (Subgroup.zpowers_le.mpr (d.isComponent.1 htE))
      simpa [TH, CEH, R] using hmap'
    exact (Subgroup.map_subtype_inj.mp
      (by simpa [hRHmap, hcommmap]))
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let s0 : PGL2 K := ld.T.g * ld.T.s * ld.T.g⁻¹
  let t0 : PGL2 K := ld.T.g * ld.T.t * ld.T.g⁻¹
  have hst0 : ∃ a : PGL2 K, s0 = a * ld.T.s * a⁻¹ ∧
      t0 = a * ld.T.t * a⁻¹ :=
    ⟨ld.T.g, rfl, rfl⟩
  have hstd := pgl2_reflected_outer_commutator_card hK hcard
      ld.Pmodel ld.eP ld.T hst0
  dsimp at hstd
  rcases hstd with ⟨hC1cyc, hC1card⟩
  have hR0eqC1 : R0 = C1 := by
    let TH' : Subgroup S := TH.subgroupOf S
    let CEH' : Subgroup S := CEH.subgroupOf S
    let C0 : Subgroup S := ⁅TH', CEH'⁆
    have hTHS : TH ≤ S := le_sup_left
    have hCEHS : CEH ≤ S := le_sup_right
    have hC0map : C0.map S.subtype = RH := by
      rw [Subgroup.map_commutator]
      rw [Subgroup.map_subgroupOf_eq_of_le hTHS]
      rw [Subgroup.map_subgroupOf_eq_of_le hCEHS]
      exact hRH_eq.symm
    have htH_S : tH ∈ S := hTHS
      (by
        change tH ∈ TH
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c.t))
    have hf_t : f ⟨tH, htH_S⟩ = t0 := by
      dsimp [f, t0]
      change e (⟨q tH, hS_le htH_S⟩ : L) = ld.T.g * ld.T.t * ld.T.g⁻¹
      have hLeq : (⟨q tH, hS_le (htH_S)⟩ : L) = ld.tL := by
        apply Subtype.ext
        exact ld.htL.symm
      rw [hLeq]
      exact ld.ht0eq
    have hTHf : TH'.map f = Subgroup.zpowers t0 := by
      have hTH'_zp : TH' = Subgroup.zpowers (⟨tH, htH_S⟩ : S) := by
        ext x
        constructor
        · intro hx
          rcases (Subgroup.mem_zpowers_iff.mp
            (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hx))) with ⟨k, hk⟩
          rw [Subgroup.mem_zpowers_iff]
          refine ⟨k, ?_⟩
          apply Subtype.ext
          apply Subtype.ext
          simpa [tH] using hk
        · intro hx
          rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, rfl⟩
          apply Subgroup.mem_subgroupOf.mpr
          apply Subgroup.mem_subgroupOf.mpr
          exact (Subgroup.zpowers c.t).zpow_mem (Subgroup.mem_zpowers c.t) k
      rw [hTH'_zp, MonoidHom.map_zpowers f (⟨tH, htH_S⟩ : S), hf_t]
    have hCEf : CEH'.map f ≤ J ⊓
        Subgroup.centralizer ({s0} : Set (PGL2 K)) := by
      apply le_inf
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨ce, hce, rfl⟩
        have hceCEH : (ce : c.Hhat) ∈ CEH := Subgroup.mem_subgroupOf.mp hce
        have hceCEs : (ce : G) ∈ CEs := Subgroup.mem_subgroupOf.mp hceCEH
        have hceE : (ce : G) ∈ d.E := (inf_le_right : CEs ≤ d.E) hceCEs
        have hceEi : (ce : c.Hhat) ∈ Ei := Subgroup.mem_subgroupOf.mpr hceE
        have hqE : q (ce : c.Hhat) ∈ Ebar :=
          Subgroup.mem_map.mpr ⟨ce, hceEi, rfl⟩
        dsimp [f]
        change e (⟨q (ce : c.Hhat), hS_le ce.2⟩ : L) ∈ J
        have hLmem : (⟨q (ce : c.Hhat), hS_le ce.2⟩ : L) ∈
            Ebar.subgroupOf L := Subgroup.mem_subgroupOf.mpr hqE
        have hmap : e (⟨q (ce : c.Hhat), hS_le ce.2⟩ : L) ∈
            (Ebar.subgroupOf L).map e.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨⟨q (ce : c.Hhat), hS_le ce.2⟩, hLmem, rfl⟩
        simpa [J] using hJeq ▸ hmap
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨ce, hce, rfl⟩
        have hceCEH : (ce : c.Hhat) ∈ CEH := Subgroup.mem_subgroupOf.mp hce
        have hceCEs : (ce : G) ∈ CEs := Subgroup.mem_subgroupOf.mp hceCEH
        have hceC : (ce : G) ∈ Subgroup.centralizer ({ld.s} : Set G) :=
          (inf_le_left : CEs ≤ Subgroup.centralizer ({ld.s} : Set G)) hceCEs
        have hceS : (ce : G) * ld.s = ld.s * (ce : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hceC
        let sH : c.Hhat := ⟨ld.s, hSleG ld.hsS⟩
        have hceH : (ce : c.Hhat) * sH = sH * (ce : c.Hhat) := by
          apply Subtype.ext
          exact hceS
        have hqcomm : q (ce : c.Hhat) * q sH = q sH * q (ce : c.Hhat) := by
          have h := congrArg q hceH
          simpa [mul_assoc] using h
        let ceL : L := ⟨q (ce : c.Hhat), hS_le ce.2⟩
        have hsL_val : (ld.sL : c.Hhat ⧸ O) = q sH := ld.hsL
        have hqcomm' : (ceL : c.Hhat ⧸ O) * (ld.sL : c.Hhat ⧸ O) =
            (ld.sL : c.Hhat ⧸ O) * (ceL : c.Hhat ⧸ O) := by
          rw [hsL_val]
          change q (ce : c.Hhat) * q sH = q sH * q (ce : c.Hhat)
          exact hqcomm
        have hLcomm : ceL * ld.sL = ld.sL * ceL := by
          apply Subtype.ext
          exact hqcomm'
        have hecomm : e ceL * e ld.sL = e ld.sL * e ceL := by
          have h := congrArg e hLcomm
          simpa [mul_assoc] using h
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa [ceL, f, s0, ← ld.hs0eq] using hecomm
    have hCEf_ge : J ⊓ Subgroup.centralizer ({s0} : Set (PGL2 K)) ≤
        CEH'.map f := by
      intro x hx
      rcases hx with ⟨hxJ, hxC⟩
      have hxL : x ∈ (Ebar.subgroupOf L).map e.toMonoidHom := by
        have hxJ' : x ∈ commutator (PGL2 K) := by simpa [J] using hxJ
        rw [← hJeq] at hxJ'
        exact hxJ'
      rcases Subgroup.mem_map.mp hxL with ⟨yL, hyL, hxy⟩
      have hyEbar : (yL : c.Hhat ⧸ O) ∈ Ebar := Subgroup.mem_subgroupOf.mp hyL
      rcases Subgroup.mem_map.mp hyEbar with ⟨aH, haEi, hqa⟩
      have haE : (aH : G) ∈ d.E := Subgroup.mem_subgroupOf.mp haEi
      let aE : d.E := ⟨(aH : G), haE⟩
      have hfix : ld.s * (aE : G) * ld.s⁻¹ * (aE : G)⁻¹ ∈
          (Subgroup.center d.E).map d.E.subtype := by
        have hfixE : ld.s * (aH : G) * ld.s⁻¹ * (aH : G)⁻¹ ∈ d.E := by
          have h1 : ld.s * (aH : G) * ld.s⁻¹ ∈ d.E :=
            hEamb_local (((S_le_H c).trans c.H_le_Hhat) ld.hsS) haE
          exact d.E.mul_mem h1 (d.E.inv_mem haE)
        let fixH : c.Hhat := ⟨ld.s * (aH : G) * ld.s⁻¹ * (aH : G)⁻¹,
          d.isComponent.1 hfixE⟩
        have hfixEi : fixH ∈ Ei := Subgroup.mem_subgroupOf.mpr hfixE
        let fixEi : Ei := ⟨fixH, hfixEi⟩
        have hqfix : q fixH = 1 := by
          let sH : c.Hhat := ⟨ld.s, hSleG ld.hsS⟩
          have hsLval : (ld.sL : c.Hhat ⧸ O) = q sH := ld.hsL
          have hxcomm : x * s0 = s0 * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
          have hecomm : e yL * e ld.sL = e ld.sL * e yL := by
            simpa [s0, ← hxy, ld.hs0eq] using hxcomm
          have hcommL : yL * ld.sL = ld.sL * yL :=
            e.injective (by simpa [map_mul] using hecomm)
          have hcommL' : Commute (yL : L) (ld.sL : L) := hcommL
          have hcommLin : yL * (ld.sL : L)⁻¹ = (ld.sL : L)⁻¹ * yL :=
            hcommL'.inv_right.eq
          have hprodL : (ld.sL : L) * yL * (ld.sL : L)⁻¹ * yL⁻¹ = 1 := by
            calc
              (ld.sL : L) * yL * (ld.sL : L)⁻¹ * yL⁻¹ =
                  (ld.sL : L) * (yL * (ld.sL : L)⁻¹) * yL⁻¹ := by group
              _ = (ld.sL : L) * ((ld.sL : L)⁻¹ * yL) * yL⁻¹ := by
                rw [hcommLin]
              _ = ((ld.sL : L) * (ld.sL : L)⁻¹) * (yL * yL⁻¹) := by group
              _ = 1 := by simp
          have hprodQ : (ld.sL : c.Hhat ⧸ O) *
              (yL : c.Hhat ⧸ O) * (ld.sL : c.Hhat ⧸ O)⁻¹ *
              (yL : c.Hhat ⧸ O)⁻¹ = 1 := by
            exact congrArg Subtype.val hprodL
          calc
            q fixH = q (sH * aH * sH⁻¹ * aH⁻¹) := by
              congr 1
            _ = (q sH) * (q aH) * (q sH)⁻¹ * (q aH)⁻¹ := by
              simp [map_mul, map_inv]
            _ = (ld.sL : c.Hhat ⧸ O) * (yL : c.Hhat ⧸ O) *
                (ld.sL : c.Hhat ⧸ O)⁻¹ * (yL : c.Hhat ⧸ O)⁻¹ := by
              rw [hsLval, hqa]
            _ = 1 := hprodQ
        have hfixCenter : fixEi ∈ Subgroup.center Ei := by
          rw [← hker']
          apply MonoidHom.mem_ker.mpr
          apply Subtype.ext
          exact hqfix
        let fixE : d.E := eEi fixEi
        have hfixCenterE : fixE ∈ Subgroup.center d.E := by
          rw [Subgroup.mem_center_iff]
          intro z
          change eEi (eEi.symm z * fixEi) = eEi (fixEi * eEi.symm z)
          apply congrArg eEi
          exact Subgroup.mem_center_iff.mp hfixCenter (eEi.symm z)
        exact Subgroup.mem_map.mpr ⟨fixE, hfixCenterE, by
          change (fixE : G) = (fixH : G)
          rfl⟩
      have hlift := centralizer_lift_of_odd_center d.E ld.s hsE hss hZodd (x := aE) hfix
      rcases hlift with ⟨z, hzfix⟩
      have hzE : (z : G) ∈ d.E := Subgroup.map_subtype_le _ z.2
      let ceE : d.E := ⟨(z : G) * (aE : G), d.E.mul_mem hzE haE⟩
      have hceC : (ceE : G) ∈ Subgroup.centralizer ({ld.s} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hzfix' : ld.s * (ceE : G) * ld.s⁻¹ = (ceE : G) := by
          simpa [ceE] using hzfix
        have h' : ld.s⁻¹ * (ceE : G) * ld.s = (ceE : G) := by
          calc
            ld.s⁻¹ * (ceE : G) * ld.s =
                (ceE : G) * ld.s⁻¹ * ld.s := by
              have h1 : (ceE : G) * ld.s⁻¹ = ld.s⁻¹ * (ceE : G) := by
                calc
                  (ceE : G) * ld.s⁻¹ = ld.s⁻¹ * (ld.s * (ceE : G) * ld.s⁻¹) := by group
                  _ = ld.s⁻¹ * (ceE : G) := by rw [hzfix']
              rw [h1]
            _ = (ceE : G) := by group
        calc
          (ceE : G) * ld.s = ld.s * (ld.s⁻¹ * (ceE : G) * ld.s) := by group
          _ = ld.s * (ceE : G) := by rw [h']
      let ceH : c.Hhat := ⟨(ceE : G), d.isComponent.1 ceE.2⟩
      have hceCEs : (ceE : G) ∈ CEs := ⟨hceC, ceE.2⟩
      have hceCEH : ceH ∈ CEH := Subgroup.mem_subgroupOf.mpr hceCEs
      have hceS : ceH ∈ S := (le_sup_right : CEH ≤ S) hceCEH
      let hzH : c.Hhat := ⟨(z : G), d.isComponent.1 hzE⟩
      have hzEi : hzH ∈ Ei := by
        change hzH ∈ d.E.subgroupOf c.Hhat
        exact Subgroup.mem_subgroupOf.mpr hzE
      let zEi : Ei := ⟨hzH, hzEi⟩
      have hzCenterE : (⟨(z : G), hzE⟩ : d.E) ∈ Subgroup.center d.E := by
        rcases Subgroup.mem_map.mp z.2 with ⟨c, hc, hzc⟩
        have hcz : c = ⟨(z : G), hzE⟩ := Subtype.ext hzc
        simpa [hcz] using hc
      have hzCenterEi : zEi ∈ Subgroup.center Ei := by
        rw [Subgroup.mem_center_iff]
        intro w
        apply eEi.injective
        rw [map_mul, map_mul]
        have hzEval : (eEi zEi : d.E) = (⟨(z : G), hzE⟩ : d.E) := by
          apply Subtype.ext
          change (hzH : G) = (z : G)
          rfl
        rw [hzEval]
        exact Subgroup.mem_center_iff.mp hzCenterE (eEi w)
      have hzKer : zEi ∈ fEi.ker := by
        rw [hker']
        exact hzCenterEi
      have hqz : q hzH = 1 := by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hzKer)
        simpa [fEi, zEi] using h
      have hqce : q ceH = q aH := by
        calc
          q ceH = q (hzH * aH) := by
            congr 1
          _ = q hzH * q aH := by simp [map_mul]
          _ = q aH := by rw [hqz]; simp
      have hfeq : f ⟨ceH, hceS⟩ = x := by
        dsimp [f]
        change e.toMonoidHom (⟨q ceH, hS_le hceS⟩ : L) = x
        have hL : (⟨q ceH, hS_le hceS⟩ : L) = yL := by
          apply Subtype.ext
          exact hqce.trans hqa
        rw [hL]
        exact hxy
      exact Subgroup.mem_map.mpr ⟨⟨ceH, hceS⟩,
        (Subgroup.mem_subgroupOf.mpr hceCEH : ⟨ceH, hceS⟩ ∈ CEH'), hfeq⟩
    have hC0f_le : C0.map f ≤ C1 := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (by simpa [C1, t0, hTHf] using le_rfl) hCEf
    have hC1_le_C0f : C1 ≤ C0.map f := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (by simpa [C1, t0, hTHf] using le_rfl) hCEf_ge
    have hR0leC1 : R0 ≤ C1 := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨yL, hyL, rfl⟩
      have hyRbar : (yL : c.Hhat ⧸ O) ∈ Rbar :=
        Subgroup.mem_subgroupOf.mp hyL
      rcases Subgroup.mem_map.mp hyRbar with ⟨rH, hrRH, hry⟩
      have hrC0 : rH ∈ C0.map S.subtype := by
        rw [hC0map]
        exact hrRH
      rcases Subgroup.mem_map.mp hrC0 with ⟨sC0, hsC0, hs⟩
      have hLel : (⟨q (sC0 : c.Hhat), hS_le (sC0 : S).2⟩ : L) = yL := by
        apply Subtype.ext
        change q (S.subtype sC0) = (yL : c.Hhat ⧸ O)
        rw [hs]
        exact hry
      have hfeq : f (sC0 : S) = e yL := by
        dsimp [f]
        exact congrArg e hLel
      exact hC0f_le (Subgroup.mem_map.mpr ⟨(sC0 : S), hsC0, hfeq⟩)
    have hC1_le_R0 : C1 ≤ R0 := by
      intro x hx
      have hxC0 : x ∈ C0.map f := hC1_le_C0f hx
      rcases Subgroup.mem_map.mp hxC0 with ⟨c0, hc0, hfeq⟩
      let rH : c.Hhat := S.subtype c0
      have hrRH : rH ∈ RH := by
        rw [← hC0map]
        exact Subgroup.mem_map.mpr ⟨c0, hc0, rfl⟩
      have hrRbar : q rH ∈ Rbar := Subgroup.mem_map.mpr ⟨rH, hrRH, rfl⟩
      have hrL : (⟨q rH, hS_le c0.2⟩ : L) ∈ Rbar.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr hrRbar
      have hmap : e (⟨q rH, hS_le c0.2⟩ : L) = x := by
        simpa [f, hfeq]
      exact Subgroup.mem_map.mpr ⟨⟨q rH, hS_le c0.2⟩, hrL, hmap⟩
    exact le_antisymm hR0leC1 hC1_le_R0
  have hR0cyc : IsCyclic R0 := by
    rw [hR0eqC1]
    exact hC1cyc
  have hC1_eq_n : Nat.card C1 = n := by
    have hhalf : Nat.card C1 = Nat.card ld.T.U / 2 := by
      simpa [C1, s0, t0] using hC1card
    have hUhalf : Nat.card ld.T.U / 2 = (Nat.card K - 1) / 2 ∨
        Nat.card ld.T.U / 2 = (Nat.card K + 1) / 2 := by
      rcases ld.T.U_card with hU | hU
      · left
        rw [hU]
      · right
        rw [hU]
    rcases hn with hn' | hn'
    · rw [hn']
      rw [hhalf]
      change Nat.card ld.T.U / 2 = (Nat.card K - 1) / 2
      rcases hUhalf with hEq | hEq
      · exact hEq
      · exfalso
        have hplus : (Nat.card K - 1) / 2 + 1 = (Nat.card K + 1) / 2 := by
          rcases hqOdd with ⟨a, ha⟩
          omega
        have hEven : Even ((Nat.card K + 1) / 2) := by
          rw [← hplus]
          rcases hnodd with ⟨a, ha⟩
          refine ⟨a + 1, ?_⟩
          omega
        exact (Nat.not_odd_iff_even.mpr hEven)
          (by simpa [hEq] using ld.T.U_half_odd)
    · rw [hn']
      rw [hhalf]
      change Nat.card ld.T.U / 2 = (Nat.card K + 1) / 2
      rcases hUhalf with hEq | hEq
      · exfalso
        have hminus : (Nat.card K + 1) / 2 - 1 = (Nat.card K - 1) / 2 := by
          rcases hqOdd with ⟨a, ha⟩
          omega
        have hEven : Even ((Nat.card K - 1) / 2) := by
          rw [← hminus]
          rcases hnodd with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          omega
        exact (Nat.not_odd_iff_even.mpr hEven)
          (by simpa [hEq] using ld.T.U_half_odd)
      · exact hEq
  have hR0card_n : Nat.card R0 = n := by
    rw [hR0eqC1, hC1_eq_n]
  have hRinterO : ∀ r : G, r ∈ R → r ∈ (O.map c.Hhat.subtype) → r = 1 := by
    let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
    let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
    let f : Ei →* Ebar :=
      (q.comp Ei.subtype).codRestrict Ebar (fun x =>
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    have hkerdata := d.pgl2_component_kernel_eq_center
      K hK L hLnormal hLindex e
    dsimp [O, q, Ei, Ebar, f] at hkerdata
    rcases hkerdata with ⟨hker, _hquot⟩
    let ρ : R →* Rbar :=
      (((q.comp RH.subtype).codRestrict Rbar (fun x =>
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)).comp
          (Subgroup.subgroupOfEquivOfLe hRleH).symm.toMonoidHom)
    have hρker : ρ.ker ≤ Subgroup.center R := by
      intro x hx
      have hxker : ρ x = 1 := MonoidHom.mem_ker.mp hx
      let xH : c.Hhat := ⟨(x : G), hRleH x.2⟩
      have hq1 : q xH = 1 := by
        change q xH = (1 : c.Hhat ⧸ O)
        exact congrArg Subtype.val hxker
      have hxO : xH ∈ O :=
        (QuotientGroup.eq_one_iff (N := O) xH).mp hq1
      have hxE : (x : G) ∈ d.E := hRleE x.2
      have hxEi : xH ∈ Ei := Subgroup.mem_subgroupOf.mpr hxE
      let xEi : Ei := ⟨xH, hxEi⟩
      have hxkerf : xEi ∈ f.ker := by
        apply MonoidHom.mem_ker.mpr
        apply Subtype.ext
        exact hq1
      have hxcenterEi : xEi ∈ Subgroup.center Ei := by
        rw [← hker]
        exact hxkerf
      rw [Subgroup.mem_center_iff]
      intro y
      have hyE : (y : G) ∈ d.E := hRleE y.2
      let yH : c.Hhat := ⟨(y : G), hRleH y.2⟩
      have hyEi : yH ∈ Ei := Subgroup.mem_subgroupOf.mpr hyE
      let yEi : Ei := ⟨yH, hyEi⟩
      have hcommEi : xEi * yEi = yEi * xEi :=
        (Subgroup.mem_center_iff.mp hxcenterEi yEi).symm
      apply Subtype.ext
      exact (congrArg (fun z : Ei => (z : G)) hcommEi).symm
    have hRbar_cyclic : IsCyclic Rbar := by
      let e1 : Rbar ≃* Rbar.subgroupOf L :=
        (Subgroup.subgroupOfEquivOfLe hRbarL).symm
      let e2 : Rbar.subgroupOf L ≃* R0 :=
        Subgroup.equivMapOfInjective (Rbar.subgroupOf L)
          e.toMonoidHom e.injective
      exact (e1.trans e2).isCyclic.mpr hR0cyc
    let : IsCyclic Rbar := hRbar_cyclic
    let : CommGroup R := commGroupOfCyclicCenterQuotient ρ hρker
    have hRcomm : ∀ a b : G, a ∈ R → b ∈ R → a * b = b * a := by
      intro a b ha hb
      have h := (inferInstance : CommGroup R).mul_comm (⟨a, ha⟩ : R) (⟨b, hb⟩ : R)
      exact congrArg Subtype.val h
    have htt : c.t * c.t = 1 := by
      simpa [pow_two] using c.t_involution.2
    have htin : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right htt
    let CInvR : Subgroup R :=
      { carrier := {x : R | c.t * (x : G) * c.t⁻¹ = (x : G)⁻¹}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          have hcomm := hRcomm (a : G) (b : G) a.2 b.2
          calc
            c.t * ((a : G) * (b : G)) * c.t⁻¹ =
                (c.t * (a : G) * c.t⁻¹) * (c.t * (b : G) * c.t⁻¹) := by group
            _ = (a : G)⁻¹ * (b : G)⁻¹ := by rw [ha, hb]
            _ = ((a : G) * (b : G))⁻¹ := by
              rw [hcomm]
              simp
        inv_mem' := by
          intro a ha
          change c.t * (a : G)⁻¹ * c.t⁻¹ = ((a : G)⁻¹)⁻¹
          calc
            c.t * (a : G)⁻¹ * c.t⁻¹ = (c.t * (a : G) * c.t⁻¹)⁻¹ := by group
            _ = ((a : G)⁻¹)⁻¹ := by rw [ha] }
    have hgen : ∀ a : G, a ∈ Subgroup.zpowers c.t → ∀ b : G, b ∈ CEs →
        c.t * ⁅a, b⁆ * c.t⁻¹ = (⁅a, b⁆)⁻¹ := by
      intro a ha b hb
      rcases (Subgroup.mem_zpowers_iff.mp ha) with ⟨k, rfl⟩
      rcases zpow_eq_one_or_self_of_sq_eq_one htt k with hk | hk
      · simp [hk]
      · rw [hk]
        rw [htin]
        change c.t * ⁅c.t, b⁆ * c.t = (⁅c.t, b⁆)⁻¹
        simp only [commutatorElement_def]
        rw [htin]
        rw [show (c.t * b * c.t * b⁻¹)⁻¹ =
            b * c.t⁻¹ * b⁻¹ * c.t⁻¹ by group]
        rw [htin]
        calc
          c.t * (c.t * b * c.t * b⁻¹) * c.t =
              (c.t * c.t) * b * c.t * b⁻¹ * c.t := by group
          _ = b * c.t * b⁻¹ * c.t := by rw [htt]; simp
    have hRleInvR : (⊤ : Subgroup R) ≤ CInvR := by
      have hmap_le : (R : Subgroup G) ≤ CInvR.map R.subtype := by
        apply Subgroup.commutator_le.mpr
        intro a ha b hb
        have hmem : ⁅a, b⁆ ∈ R :=
          Subgroup.commutator_mem_commutator ha hb
        have hinv : c.t * ⁅a, b⁆ * c.t⁻¹ = (⁅a, b⁆)⁻¹ :=
          hgen a ha b hb
        exact Subgroup.mem_map.mpr
          ⟨(⟨⁅a, b⁆, hmem⟩ : R), hinv, rfl⟩
      intro x hx
      have hxG : (x : G) ∈ R := x.2
      have hxmap : (x : G) ∈ CInvR.map R.subtype := hmap_le hxG
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hyC, hxy⟩
      have hyx : y = x := by
        apply Subtype.ext
        exact hxy
      simpa [hyx] using hyC
    intro r hrR hO
    let rR : R := ⟨r, hrR⟩
    have hrinvR : rR ∈ CInvR := hRleInvR (by simp)
    have hrinv : c.t * r * c.t⁻¹ = r⁻¹ :=
      (⟨rR, hrinvR⟩ : CInvR).2
    let rH : c.Hhat := ⟨r, hRleH hrR⟩
    have hrH_Ei : rH ∈ Ei := Subgroup.mem_subgroupOf.mpr (hRleE hrR)
    let rHEi : Ei := ⟨rH, hrH_Ei⟩
    have hrH_O : rH ∈ O := by
      rcases Subgroup.mem_map.mp hO with ⟨o, hoO, hco⟩
      have ho_eq : o = rH := by
        apply Subtype.ext
        exact hco
      rwa [← ho_eq]
    have hrkerf : rHEi ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := O) rH).mpr hrH_O
    have hrcenterEi : rHEi ∈ Subgroup.center Ei := by
      rw [← hker]
      exact hrkerf
    have htH_Ei : (⟨c.t, hSleG (c.S0_le_S c.t_mem_S0)⟩ : c.Hhat) ∈ Ei :=
      Subgroup.mem_subgroupOf.mpr htE
    let tHEi : Ei := ⟨⟨c.t, hSleG (c.S0_le_S c.t_mem_S0)⟩, htH_Ei⟩
    have hcommEi : rHEi * tHEi = tHEi * rHEi :=
      (Subgroup.mem_center_iff.mp hrcenterEi tHEi).symm
    have hcommG : r * c.t = c.t * r := by
      have h := congrArg (fun z : Ei => (z : G)) hcommEi
      simpa using h
    have hr_eq_inv : r = r⁻¹ := by
      calc
        r = r * c.t * c.t⁻¹ := by group
        _ = c.t * r * c.t⁻¹ := by rw [hcommG]
        _ = r⁻¹ := hrinv
    have hr2 : r * r = 1 := by
      calc
        r * r = r⁻¹ * r := by rw [← hr_eq_inv]
        _ = 1 := by simp
    have hOodd : Odd (Nat.card O) := by
      have hcop : Nat.Coprime 2 (Nat.card O) := by
        simpa [O] using (pPrimeCore_coprime_card (p := 2) (G := c.Hhat))
      exact Nat.coprime_two_left.mp hcop
    have hord_dvd : orderOf r ∣ Nat.card O := by
      rcases Subgroup.mem_map.mp hO with ⟨o, hoO, hco⟩
      have hpowO : (⟨o, hoO⟩ : O) ^ Nat.card O = 1 :=
        pow_card_eq_one' (G := O) (x := ⟨o, hoO⟩)
      have hpow : r ^ Nat.card O = 1 := by
        have hpowG : (o : G) ^ Nat.card O = 1 := by
          exact congrArg (fun x : O => ((x : c.Hhat) : G)) hpowO
        have hov : (o : G) = r := hco
        simpa [hov] using hpowG
      exact orderOf_dvd_of_pow_eq_one hpow
    have hordOdd : Odd (orderOf r) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      have h2 : 2 ∣ orderOf r := (even_iff_two_dvd.mp heven)
      exact hOodd.not_two_dvd_nat (h2.trans hord_dvd)
    have hdvd2 : orderOf r ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hr2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      exact hordOdd.not_two_dvd_nat (by rw [h2])
  exact ⟨hRbarL, hR0cyc, hR0card_n, hR0eqC1, hRinterO⟩

set_option maxHeartbeats 800000 in
/-- The `R^y`-side of the torus transport: the quotient image lies in the
model subgroup and has order dividing the other half of `q±1`. -/
private theorem reflected_R_conj_image_inner_torus_card_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e)
    {y : G} (hyI : IsInvolution y) (hyts : y * c.t * y⁻¹ = ld.s)
    {m : ℕ}
    (hm : m = if Nat.card ld.T.U = Nat.card K - 1 then
        (Nat.card K + 1) / 2 else (Nat.card K - 1) / 2) :
    let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
    let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
    let CEs : Subgroup G := Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    let RyH : Subgroup c.Hhat :=
      (R.map (MulAut.conj y).toMonoidHom).subgroupOf c.Hhat
    let Rybar : Subgroup (c.Hhat ⧸ O) := RyH.map q
    let Ry0 : Subgroup (PGL2 K) := (Rybar.subgroupOf L).map e.toMonoidHom
    Rybar ≤ L ∧ Nat.card Ry0 ∣ m := by
  classical
  intro O q CEs R RyH Rybar Ry0
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    rw [hKcard]
    exact hpOdd.pow
  have hcomp := d.pgl2_component_image_eq_commutator K hK L hLnormal hLindex e
  dsimp at hcomp
  rcases hcomp with ⟨hcard, _hEbarne, _hEbarperf, _hEbarsn, _hEbarL, _hJeq⟩
  have hend := d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e
  dsimp at hend
  rcases hend with ⟨_hEnormal, htE, _hfuse, hcent⟩
  have hRle := reflected_R_le_inter_of_conjugator_t26 c d.E
      htE d.isComponent.1 ld.hsS hyts hy2
  have hRleE : R ≤ d.E := hRle.1
  have hRleH : R ≤ c.Hhat := hRle.2.1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hty : c.t = y⁻¹ * ld.s * y := by
    calc
      c.t = y⁻¹ * (y * c.t * y⁻¹) * y := by group
      _ = y⁻¹ * ld.s * y := by rw [hyts]
  let CEsy : Subgroup G := CEs.map (MulAut.conj y).toMonoidHom
  have hmapR : R.map (MulAut.conj y).toMonoidHom =
      ⁅Subgroup.zpowers ld.s, CEsy⁆ := by
    dsimp [R, CEs, CEsy]
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hyts]
  have hCEsy : CEsy ≤ Subgroup.centralizer ({c.t} : Set G) := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, hz⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz0C : z0 ∈ Subgroup.centralizer ({ld.s} : Set G) :=
      (inf_le_left : CEs ≤ Subgroup.centralizer ({ld.s} : Set G)) hz0
    have hz0s : z0 * ld.s = ld.s * z0 :=
      Subgroup.mem_centralizer_singleton_iff.mp hz0C
    have hzv : z = y * z0 * y⁻¹ := by
      simpa [MulAut.conj_apply, CEsy] using hz.symm
    subst z
    change (y * z0 * y⁻¹) * c.t = c.t * (y * z0 * y⁻¹)
    calc
      (y * z0 * y⁻¹) * c.t = (y * z0 * y) * c.t := by rw [hyinv]
      _ = (y * z0 * y) * (y⁻¹ * ld.s * y) := by rw [hty]
      _ = y * (z0 * ld.s) * y := by
        rw [hyinv]
        calc
          (y * z0 * y) * (y * ld.s * y) = y * z0 * (y * y) * ld.s * y := by group
          _ = y * (z0 * ld.s) * y := by rw [hy2]; simp [mul_assoc]
      _ = y * (ld.s * z0) * y := by rw [hz0s]
      _ = c.t * (y * z0 * y⁻¹) := by
        rw [hty, hyinv]
        calc
          y * (ld.s * z0) * y = y * ld.s * z0 * y := by group
          _ = y * ld.s * 1 * z0 * y := by simp
          _ = y * ld.s * (y * y) * z0 * y := by rw [← hy2]
          _ = (y * ld.s * y) * (y * z0 * y) := by group
  have hsC : ld.s ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact S_le_H c ld.hsS
  have hsCz : Subgroup.zpowers ld.s ≤
      Subgroup.centralizer ({c.t} : Set G) :=
    Subgroup.zpowers_le.mpr hsC
  have hRyC : R.map (MulAut.conj y).toMonoidHom ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    rw [hmapR]
    exact commutator_le_of_le_t26 (Subgroup.zpowers ld.s) CEsy
      (Subgroup.centralizer ({c.t} : Set G)) hsCz hCEsy
  have hM : Subgroup.centralizer ({c.t} : Set G) ≤ c.Hhat := by
    rw [← c.H_eq_centralizer]
    exact c.H_le_Hhat
  have hRyHle : R.map (MulAut.conj y).toMonoidHom ≤ c.Hhat := hRyC.trans hM
  have hCEsyH : CEsy ≤ c.Hhat := hCEsy.trans hM
  have hSleG : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let Ss : Subgroup c.Hhat := (Subgroup.zpowers ld.s).subgroupOf c.Hhat
  let CEHy : Subgroup c.Hhat := CEsy.subgroupOf c.Hhat
  let C0 : Subgroup c.Hhat := ⁅Ss, CEHy⁆
  have hSsH : Subgroup.zpowers ld.s ≤ c.Hhat :=
    Subgroup.zpowers_le.mpr (hSleG ld.hsS)
  have hC0_map : C0.map c.Hhat.subtype =
      ⁅Subgroup.zpowers ld.s, CEsy⁆ := by
    dsimp [C0, Ss, CEHy]
    rw [Subgroup.map_commutator]
    rw [Subgroup.map_subgroupOf_eq_of_le hSsH]
    rw [Subgroup.map_subgroupOf_eq_of_le hCEsyH]
  have hRyH_map : RyH.map c.Hhat.subtype = R.map (MulAut.conj y).toMonoidHom := by
    dsimp [RyH]
    exact Subgroup.map_subgroupOf_eq_of_le hRyHle
  have hRyH_eq : RyH = C0 := by
    apply Subgroup.map_subtype_inj.mp
    rw [hRyH_map, hC0_map, hmapR]
  let P : Sylow 2 c.Hhat := c.S.subtype hSleG
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ O)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  have hSs_leP : Ss ≤ (P : Subgroup c.Hhat) := by
    intro u hu
    exact (Subgroup.zpowers_le.mpr ld.hsS) (Subgroup.mem_subgroupOf.mp hu)
  have hqSs : Ss.map q ≤ L := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    have huP : u ∈ (P : Subgroup c.Hhat) := hSs_leP hu
    have hqP : q u ∈ (Pq : Subgroup (c.Hhat ⧸ O)) := by
      change q u ∈ (P : Subgroup c.Hhat).map q
      exact Subgroup.mem_map.mpr ⟨u, huP, rfl⟩
    exact hPqL hqP
  have hmapC : C0.map q = ⁅Ss.map q, CEHy.map q⁆ := by
    dsimp [C0]
    exact Subgroup.map_commutator (H₁ := Ss) (H₂ := CEHy) q
  have hcomm_le : ⁅Ss.map q, CEHy.map q⁆ ≤ L := by
    let : L.Normal := hLnormal
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have haL : a ∈ L := hqSs ha
    have hconj : b * a⁻¹ * b⁻¹ ∈ L :=
      (inferInstance : L.Normal).conj_mem a⁻¹ (L.inv_mem haL) b
    change a * b * a⁻¹ * b⁻¹ ∈ L
    have heq : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [heq]
    exact L.mul_mem haL hconj
  have hRybar_eq : Rybar = C0.map q := by
    dsimp [Rybar]
    rw [hRyH_eq]
  have hRybarL : Rybar ≤ L := by
    rw [hRybar_eq, hmapC]
    exact hcomm_le
  let tH : c.Hhat := ⟨c.t, hSleG (c.S0_le_S c.t_mem_S0)⟩
  let tL : L := ⟨q tH,
    hPqL (Subgroup.mem_map.mpr ⟨tH, c.S0_le_S c.t_mem_S0, rfl⟩)⟩
  let t0 : PGL2 K := ld.T.g * ld.T.t * ld.T.g⁻¹
  have ht0eq : e tL = t0 := by
    dsimp [t0]
    have hLeq : (⟨q tH, hPqL (Subgroup.mem_map.mpr ⟨tH,
        c.S0_le_S c.t_mem_S0, rfl⟩)⟩ : L) = ld.tL := by
      apply Subtype.ext
      exact ld.htL.symm
    dsimp [tL]
    rw [hLeq]
    exact ld.ht0eq
  have hRy0leC : Ry0 ≤ Subgroup.centralizer ({t0} : Set (PGL2 K)) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xL, hxL, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxRybar : (xL : c.Hhat ⧸ O) ∈ Rybar :=
      Subgroup.mem_subgroupOf.mp hxL
    rcases Subgroup.mem_map.mp hxRybar with ⟨r, hrRyH, hrq⟩
    have hrC : (r : G) ∈
        Subgroup.centralizer ({c.t} : Set G) :=
      hRyC (Subgroup.mem_subgroupOf.mp hrRyH)
    have hcommG : (r : G) * c.t = c.t * (r : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hrC
    have hcommH : r * tH = tH * r := Subtype.ext hcommG
    have hcommQ : q r * q tH = q tH * q r := by
      have h := congrArg q hcommH
      simpa [mul_assoc] using h
    have hcommL : xL * tL = tL * xL := by
      apply Subtype.ext
      change (xL : c.Hhat ⧸ O) * (tL : c.Hhat ⧸ O) =
        (tL : c.Hhat ⧸ O) * (xL : c.Hhat ⧸ O)
      rw [← hrq]
      change q r * q tH = q tH * q r
      exact hcommQ
    have hecomm : e xL * e tL = e tL * e xL := by
      have h := congrArg e hcommL
      simpa [mul_assoc] using h
    simpa [ht0eq] using hecomm
  let n : ℕ := Nat.card ld.T.U / 2
  have hn : n = (Nat.card K - 1) / 2 ∨ n = (Nat.card K + 1) / 2 := by
    dsimp [n]
    rcases ld.T.U_card with hU | hU
    · left
      rw [hU]
    · right
      rw [hU]
  have hnodd : Odd n := by
    simpa [n] using ld.T.U_half_odd
  have hR := reflected_R_image_outer_torus_t26 c d K hK L hLnormal hLindex e
      ld hyI hyts hn hnodd
  dsimp at hR
  rcases hR with ⟨hRbarL, _hR0cyc, hR0card, _hR0eq, hRinterO⟩
  let RH : Subgroup c.Hhat := R.subgroupOf c.Hhat
  let Rbar0 : Subgroup (c.Hhat ⧸ O) := RH.map q
  let R0 : Subgroup (PGL2 K) := (Rbar0.subgroupOf L).map e.toMonoidHom
  have hR0card' : Nat.card R0 ∣ n := by
    rw [show Nat.card R0 = n by simpa [R0, Rbar0, RH] using hR0card]
  have hqinjRH : Function.Injective (q.comp RH.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff (q.comp RH.subtype)).mp
    apply le_antisymm
    · intro x hx
      have hx1G : (x : G) = 1 := by
        have hq1 : q (x : c.Hhat) = 1 := by
          simpa [MonoidHom.mem_ker] using hx
        have hxO : (x : c.Hhat) ∈ O :=
          (QuotientGroup.eq_one_iff (N := O) (x : c.Hhat)).mp hq1
        exact hRinterO (x : G) x.2
          (Subgroup.mem_map.mpr ⟨x, hxO, rfl⟩)
      have hx1H : (x : c.Hhat) = 1 := by
        apply Subtype.ext
        simpa using hx1G
      exact Subtype.ext hx1H
    · intro x hx
      have hx1 : x = 1 := Subgroup.mem_bot.mp hx
      simp [hx1]
  have hcardR_R0 : Nat.card R = Nat.card R0 := by
    calc
      Nat.card R = Nat.card RH :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleH).toEquiv).symm
      _ = Nat.card Rbar0 := by
        have hmap : (⊤ : Subgroup RH).map (q.comp RH.subtype) = RH.map q := by
          ext x
          constructor
          · rintro ⟨y, _hy, rfl⟩
            exact Subgroup.mem_map.mpr ⟨(y : c.Hhat), y.2, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, trivial, rfl⟩
        change Nat.card ↥RH = Nat.card ↥(RH.map q)
        rw [← hmap]
        calc
          Nat.card ↥RH = Nat.card ↥(⊤ : Subgroup RH) := by
            exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
          _ = Nat.card ↥((⊤ : Subgroup RH).map (q.comp RH.subtype)) :=
            (Subgroup.card_map_of_injective (K := (⊤ : Subgroup RH))
              (f := q.comp RH.subtype) hqinjRH).symm
      _ = Nat.card (Rbar0.subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRbarL).toEquiv).symm
      _ = Nat.card R0 := by
        simpa [R0] using
          (Nat.card_congr (Subgroup.equivMapOfInjective (Rbar0.subgroupOf L)
            e.toMonoidHom e.injective).toEquiv)
  have hRodd : Odd (Nat.card R) := by
    rw [hcardR_R0]
    have hcop : Nat.Coprime 2 (Nat.card R0) :=
      (Nat.coprime_two_left.mpr hnodd).of_dvd_right hR0card'
    exact Nat.coprime_two_left.mp hcop
  have hRycard_eq : Nat.card Ry0 = Nat.card Rybar := by
    calc
      Nat.card Ry0 = Nat.card (Rybar.subgroupOf L) := by
        simpa [Ry0] using
          (Nat.card_congr (Subgroup.equivMapOfInjective (Rybar.subgroupOf L)
            e.toMonoidHom e.injective).toEquiv).symm
      _ = Nat.card Rybar :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRybarL).toEquiv
  have hRy0dvdR : Nat.card Rybar ∣ Nat.card R := by
    have h1 : Nat.card Rybar ∣ Nat.card RyH := by
      calc
        Nat.card Rybar = Nat.card (RyH.map q) := rfl
        _ ∣ Nat.card RyH := Subgroup.card_map_dvd (H := RyH) (f := q)
    have h2 : Nat.card RyH = Nat.card R := by
      calc
        Nat.card RyH = Nat.card (R.map (MulAut.conj y).toMonoidHom) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRyHle).toEquiv
        _ = Nat.card R :=
          Subgroup.card_map_of_injective (MulAut.conj y).injective
    refine h1.trans ?_
    rw [h2]
  have hRy0odd : Odd (Nat.card Ry0) := by
    rw [hRycard_eq]
    have hcop : Nat.Coprime 2 (Nat.card Rybar) :=
      (Nat.coprime_two_left.mpr hRodd).of_dvd_right hRy0dvdR
    exact Nat.coprime_two_left.mp hcop
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  have hRy0J : Ry0 ≤ J :=
    odd_card_subgroup_le_normal_index_two J Ry0 (by infer_instance)
      hJindex hRy0odd
  let C0model : Subgroup (PGL2 K) :=
    Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓ J
  have hRy0leC0model : Ry0 ≤ C0model :=
    le_inf hRy0leC hRy0J
  have hC0model_card : Nat.card C0model = 2 * m := by
    change Nat.card ((Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓ J
        : Subgroup (PGL2 K))) = 2 * m
    calc
      Nat.card ((Subgroup.centralizer ({t0} : Set (PGL2 K)) ⊓ J
          : Subgroup (PGL2 K))) =
          2 * (if Nat.card ld.T.U = Nat.card K - 1 then
                (Nat.card K + 1) / 2
              else
                (Nat.card K - 1) / 2) :=
        pgl2_inner_involution_centralizer_card hK hcard
          ld.Pmodel ld.eP ld.T ⟨ld.T.g, rfl⟩
      _ = 2 * m := by rw [hm]
  have hdvd : Nat.card Ry0 ∣ 2 * m := by
    have hdvd0 : Nat.card Ry0 ∣ Nat.card C0model :=
      Subgroup.card_dvd_of_le hRy0leC0model
    rwa [hC0model_card] at hdvd0
  refine ⟨hRybarL, ?_⟩
  exact (Nat.coprime_two_right.mpr hRy0odd).dvd_of_dvd_mul_left hdvd

/-- The quotient image of the conjugated reflected torus is trivial.  This
is the model-transport core: the image lies in the `PSL₂` component, is
cyclic of odd order dividing the odd low-torus half, and is centralized by
the distinguished inner involution, so the Dickson partition kills it. -/
private theorem reflected_R_conj_image_eq_bot_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e)
    {y : G} (hyI : IsInvolution y) (hyts : y * c.t * y⁻¹ = ld.s)
    (hRyH : (⁅Subgroup.zpowers c.t,
      Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E⁆).map
        (MulAut.conj y).toMonoidHom ≤ c.Hhat) :
    let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
    let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
    let CEs : Subgroup G := Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    ((R.map (MulAut.conj y).toMonoidHom).subgroupOf c.Hhat).map q = ⊥ := by
  classical
  intro O q CEs R
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
    rw [hKcard]
    exact hpOdd.pow
  have hRleHhat : R ≤ c.Hhat :=
    (reflected_R_le_inter_of_conjugator_t26 c d.E
      (d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e).2.1
      d.isComponent.1 ld.hsS hyts hy2).2.1
  let RyH : Subgroup c.Hhat :=
    (R.map (MulAut.conj y).toMonoidHom).subgroupOf c.Hhat
  let RH : Subgroup c.Hhat := R.subgroupOf c.Hhat
  let Rbar : Subgroup (c.Hhat ⧸ O) := RH.map q
  let Rybar : Subgroup (c.Hhat ⧸ O) := RyH.map q
  let n : ℕ := Nat.card ld.T.U / 2
  have hn : n = (Nat.card K - 1) / 2 ∨ n = (Nat.card K + 1) / 2 := by
    dsimp [n]
    rcases ld.T.U_card with hU | hU
    · left
      rw [hU]
    · right
      rw [hU]
  have hnodd : Odd n := by
    simpa [n] using ld.T.U_half_odd
  let m : ℕ := if Nat.card ld.T.U = Nat.card K - 1 then
    (Nat.card K + 1) / 2 else (Nat.card K - 1) / 2
  have hm : m = if Nat.card ld.T.U = Nat.card K - 1 then
      (Nat.card K + 1) / 2 else (Nat.card K - 1) / 2 := rfl
  have hcop : Nat.Coprime n m := by
    dsimp [n, m]
    by_cases hU : Nat.card ld.T.U = Nat.card K - 1
    · rw [if_pos hU, hU]
      exact coprime_halves_of_odd hqOdd
    · rw [if_neg hU]
      rcases ld.T.U_card with hU' | hU'
      · exfalso
        exact hU hU'
      · rw [hU', Nat.coprime_comm]
        exact coprime_halves_of_odd hqOdd
  -- the two transports
  have hR := reflected_R_image_outer_torus_t26 c d K hK L hLnormal hLindex e
      ld hyI hyts hn hnodd
  dsimp at hR
  rcases hR with ⟨hRbarL, hR0cyc, hR0card, _hR0eq, hRinterO⟩
  have hRy := reflected_R_conj_image_inner_torus_card_t26 c d K hK L hLnormal hLindex e
      ld hyI hyts hm
  dsimp at hRy
  rcases hRy with ⟨hRybarL, hRy0card⟩
  let R0 : Subgroup (PGL2 K) := (Rbar.subgroupOf L).map e.toMonoidHom
  let Ry0 : Subgroup (PGL2 K) := (Rybar.subgroupOf L).map e.toMonoidHom
  have hR0card' : Nat.card R0 ∣ n := by
    rw [show Nat.card R0 = n by simpa [R0, Rbar, RH] using hR0card]
  have hRy0card' : Nat.card Ry0 ∣ m := by
    simpa [Ry0, Rybar, RyH] using hRy0card
  -- injectivity of the odd-core quotient on `R`
  have hqinjRH : Function.Injective (q.comp RH.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff (q.comp RH.subtype)).mp
    apply le_antisymm
    · intro x hx
      have hx1G : (x : G) = 1 := by
        have hq1 : q (x : c.Hhat) = 1 := by
          simpa [MonoidHom.mem_ker] using hx
        have hxO : (x : c.Hhat) ∈ O :=
          (QuotientGroup.eq_one_iff (N := O) (x : c.Hhat)).mp hq1
        exact hRinterO (x : G) x.2
          (Subgroup.mem_map.mpr ⟨x, hxO, rfl⟩)
      have hx1H : (x : c.Hhat) = 1 := by
        apply Subtype.ext
        simpa using hx1G
      exact Subtype.ext hx1H
    · intro x hx
      have hx1 : x = 1 := Subgroup.mem_bot.mp hx
      simp [hx1]
  -- |R| = |q(R)| = |R0|
  have hcardR_R0 : Nat.card R = Nat.card R0 := by
    calc
      Nat.card R = Nat.card RH :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleHhat).toEquiv).symm
      _ = Nat.card Rbar := by
        have hmap : (⊤ : Subgroup RH).map (q.comp RH.subtype) = RH.map q := by
          ext x
          constructor
          · rintro ⟨y, _hy, rfl⟩
            exact Subgroup.mem_map.mpr ⟨(y : c.Hhat), y.2, rfl⟩
          · rintro ⟨y, hy, rfl⟩
            exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, trivial, rfl⟩
        change Nat.card ↥RH = Nat.card ↥(RH.map q)
        rw [← hmap]
        calc
          Nat.card ↥RH = Nat.card ↥(⊤ : Subgroup RH) := by
            exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).symm
          _ = Nat.card ↥((⊤ : Subgroup RH).map (q.comp RH.subtype)) :=
            (Subgroup.card_map_of_injective (K := (⊤ : Subgroup RH))
              (f := q.comp RH.subtype) hqinjRH).symm
      _ = Nat.card (Rbar.subgroupOf L) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRbarL).toEquiv).symm
      _ = Nat.card R0 := by
        simpa [R0] using
          (Nat.card_congr (Subgroup.equivMapOfInjective (Rbar.subgroupOf L)
            e.toMonoidHom e.injective).toEquiv)
  -- |Ry0| = |Rybar|
  have hRycard_eq : Nat.card Ry0 = Nat.card Rybar := by
    calc
      Nat.card Ry0 = Nat.card (Rybar.subgroupOf L) := by
        simpa [Ry0] using
          (Nat.card_congr (Subgroup.equivMapOfInjective (Rybar.subgroupOf L)
            e.toMonoidHom e.injective).toEquiv).symm
      _ = Nat.card Rybar :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRybarL).toEquiv
  -- |q(R^y)| divides the odd half `n`
  have hRycard_n : Nat.card Ry0 ∣ n := by
    have h1 : Nat.card Ry0 ∣ Nat.card RyH := by
      calc
        Nat.card Ry0 = Nat.card Rybar := hRycard_eq
        _ = Nat.card (RyH.map q) := rfl
        _ ∣ Nat.card RyH := Subgroup.card_map_dvd (H := RyH) (f := q)
    have h2 : Nat.card RyH = Nat.card R := by
      calc
        Nat.card RyH = Nat.card (R.map (MulAut.conj y).toMonoidHom) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRyH).toEquiv
        _ = Nat.card R :=
          Subgroup.card_map_of_injective (MulAut.conj y).injective
    refine h1.trans ?_
    rw [h2, hcardR_R0]
    exact hR0card'
  -- and it divides the other half `m`
  have hRycard_m : Nat.card Ry0 ∣ m := hRy0card'
  -- the halves are coprime, so the image is trivial
  have hgcd1 : Nat.gcd n m = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
  have hRy0card1 : Nat.card Ry0 = 1 := by
    apply Nat.dvd_one.mp
    rw [← hgcd1]
    exact Nat.dvd_gcd hRycard_n hRycard_m
  have hRybar1 : Nat.card Rybar = 1 := by
    rw [← hRycard_eq]
    exact hRy0card1
  exact Subgroup.eq_bot_of_card_eq (H := Rybar) hRybar1

/-- In the component branch, the reflected torus `R = [⟨t⟩, C_E(s)]`
conjugated by `y` (`t^y = s`) lies in the odd core `O(Ĥ)`. -/
public theorem reflected_R_conj_le_oddCore_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e)
    {y : G} (hyI : IsInvolution y) (hyts : y * c.t * y⁻¹ = ld.s) :
    let CEs : Subgroup G := Subgroup.centralizer ({ld.s} : Set G) ⊓ d.E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    R.map (MulAut.conj y).toMonoidHom ≤ oddCoreOf c.Hhat := by
  classical
  intro CEs R
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hend := d.pgl2_component_ambient_endpoint K hK L hLnormal hLindex e
  dsimp at hend
  rcases hend with ⟨hEnormal, htE, hfuse, hcent⟩
  have hRyH : R.map (MulAut.conj y).toMonoidHom ≤ c.Hhat := by
    have hRs : R ≤ c.Hhat := by
      rcases reflected_R_le_inter_of_conjugator_t26 c d.E
        htE d.isComponent.1 ld.hsS hyts hy2 with ⟨hRE, hRH, _hRconj⟩
      exact hRH
    have hRconj : R ≤ conjugateSubgroup c.Hhat y :=
      (reflected_R_le_inter_of_conjugator_t26 c d.E
        htE d.isComponent.1 ld.hsS hyts hy2).2.2
    exact (map_conj_le_iff_le_conjugate_t26 c.Hhat y R hy2).2 hRconj
  let RyH : Subgroup c.Hhat :=
    (R.map (MulAut.conj y).toMonoidHom).subgroupOf c.Hhat
  have hqbot := reflected_R_conj_image_eq_bot_t26 c d K hK L hLnormal hLindex e
      ld hyI hyts hRyH
  intro x hx
  have hxH : x ∈ c.Hhat := hRyH hx
  let xH : c.Hhat := ⟨x, hxH⟩
  have hxRyH : xH ∈ RyH := Subgroup.mem_subgroupOf.mpr hx
  have hker : RyH ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (H := RyH) (f := q)).mp hqbot
  have hxker : xH ∈ q.ker := hker hxRyH
  have hxO : xH ∈ O := by
    simpa [q, QuotientGroup.ker_mk'] using hxker
  change x ∈ (pPrimeCore 2 c.Hhat).map c.Hhat.subtype
  exact Subgroup.mem_map.mpr ⟨xH, hxO, rfl⟩

/-- The second reflected torus `R* = [t, C_E(ts)]`, conjugated by an element
which sends `t` to `ts` (and `ts` to `t`), lies in the odd core of `Ĥ`.  This
is the `R*`-side analogue of `reflected_R_conj_le_oddCore_t26`, obtained by
swapping the two outer involutions in the model. -/
public theorem reflected_Rstar_conj_le_oddCore_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K)
    (ld : Theorem26OuterLiftData d K L e)
    {g : G} (hgI : IsInvolution g)
    (hgt : g * c.t * g⁻¹ = c.t * ld.s) :
    let CEsts : Subgroup G :=
      Subgroup.centralizer ({c.t * ld.s} : Set G) ⊓ d.E
    let Rstar : Subgroup G := ⁅Subgroup.zpowers c.t, CEsts⁆
    Rstar.map (MulAut.conj g).toMonoidHom ≤ oddCoreOf c.Hhat := by
  classical
  intro CEsts Rstar
  obtain ⟨ld2, hs2, _hT2s, _hT2g, _hT2t, _hT2R, _hT2Rstar⟩ :=
    exists_theorem26_outer_lift_data_swap d K hK L hLnormal hLindex e ld
  have h := reflected_R_conj_le_oddCore_t26 c d K hK L hLnormal hLindex e
      ld2 hgI (by simpa [hs2] using hgt)
  simpa [CEsts, Rstar, hs2] using h

/-! ## Final assembly: normalizer transfer and the large intersection -/

/-- The selected component centralizes the odd core of `Ĥ`: `O(Ĥ)` is
solvable (Feit--Thompson), is normalized by the component layer, and the
layer centralizes every solvable subgroup it normalizes. -/
public theorem E_commutator_oddCore_eq_bot_t26
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c) :
    ⁅d.E, oddCoreOf c.Hhat⁆ = ⊥ := by
  classical
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let Oamb : Subgroup G := oddCoreOf c.Hhat
  have hOodd : Odd (Nat.card O) := by
    have hOcop : Nat.Coprime 2 (Nat.card O) := by
      simpa [O] using (pPrimeCore_coprime_card (p := 2) (G := c.Hhat))
    exact Nat.coprime_two_left.mp hOcop
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  have hOamb_le : Oamb ≤ c.Hhat := by
    dsimp [Oamb, oddCoreOf]
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hOamb_solv : Group.IsSolvable Oamb := by
    let eO : O ≃* Oamb :=
      Subgroup.equivMapOfInjective O c.Hhat.subtype c.Hhat.subtype_injective
    exact isSolvable_of_mulEquiv eO
  have hOamb_normal_in : IsNormalIn Oamb c.Hhat := by
    refine ⟨hOamb_le, ?_⟩
    intro h hh x hx
    let hH : c.Hhat := ⟨h, hh⟩
    rcases Subgroup.mem_map.mp hx with ⟨o, ho, hox⟩
    have hconj : hH * o * hH⁻¹ ∈ O :=
      (inferInstance : O.Normal).conj_mem o ho hH
    refine Subgroup.mem_map.mpr ⟨hH * o * hH⁻¹, hconj, ?_⟩
    change (h : G) * (o : G) * (h : G)⁻¹ = (h : G) * (x : G) * (h : G)⁻¹
    exact congrArg (fun z : G => h * z * h⁻¹) hox
  have hEN : componentLayerOf c.Hhat ≤
      Subgroup.normalizer (Oamb : Set G) :=
    (fstar_componentLayerOf_isNormalIn c.Hhat).1.trans
      (le_normalizer_of_isNormalIn hOamb_normal_in)
  have hcom : ⁅componentLayerOf c.Hhat, Oamb⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      c.Hhat Oamb hOamb_le hOamb_solv hEN
  have hE_le : d.E ≤ componentLayerOf c.Hhat := le_sSup d.isComponent
  have hEcent : d.E ≤ Subgroup.centralizer (Oamb : Set G) :=
    hE_le.trans ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcom)
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hEcent


end CFSG.GorensteinWalter
