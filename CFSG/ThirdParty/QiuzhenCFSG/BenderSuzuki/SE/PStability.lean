module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.corollary_9_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Abelian Sylow subgroups and the `SL(2,3)` obstruction

This module supplies the elementary group-theoretic part of the p-stability
input used in Section 7.  Having abelian Sylow subgroups passes to subgroups,
surjective images, and isomorphic groups.  The concrete group `SL(2,3)` does
not have abelian Sylow `2`-subgroups: it contains an explicit quaternion
subgroup of order eight.  Consequently a finite group with abelian Sylow
`2`-subgroups cannot involve `SL(2,3)`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped MatrixGroups IsMulCommutative commutatorElement
open PFAppendixIII PFchapter1section1

universe u v

/-- Every Sylow `p`-subgroup of `G` is abelian. -/
public def HasAbelianSylow (p : ℕ) (G : Type u) [Group G] : Prop :=
  ∀ P : Sylow p G, IsMulCommutative (P : Subgroup G)

/-- Subgroups inherit abelian Sylow subgroups. -/
public theorem HasAbelianSylow.subgroup
    {p : ℕ} {G : Type u} [Group G]
    (hG : HasAbelianSylow p G) (H : Subgroup G) :
    HasAbelianSylow p H := by
  intro P
  obtain ⟨Q, hQP⟩ := Sylow.exists_comap_subtype_eq P
  let : IsMulCommutative (Q : Subgroup G) := hG Q
  rw [← hQP]
  exact Subgroup.comap_injective_isMulCommutative
    (H := (Q : Subgroup G)) H.subtype_injective

/-- Surjective images inherit abelian Sylow subgroups. -/
public theorem HasAbelianSylow.mapSurjective
    {p : ℕ} {G : Type u} {H : Type v}
    [Group G] [Finite G] [Group H] [Fact p.Prime]
    (hG : HasAbelianSylow p G) (f : G →* H)
    (hf : Function.Surjective f) :
    HasAbelianSylow p H := by
  intro P
  obtain ⟨Q, hQP⟩ := Sylow.mapSurjective_surjective
    (f := f) hf p P
  rw [← hQP]
  let : IsMulCommutative (Q : Subgroup G) := hG Q
  exact Subgroup.map_isMulCommutative (Q : Subgroup G) f

/-- Abelian Sylow subgroups transport across a group isomorphism. -/
public theorem HasAbelianSylow.of_mulEquiv
    {p : ℕ} {G : Type u} {H : Type v}
    [Group G] [Finite G] [Group H] [Fact p.Prime]
    (hG : HasAbelianSylow p G) (e : G ≃* H) :
    HasAbelianSylow p H :=
  hG.mapSurjective e.toMonoidHom e.surjective

/-- An involution in a quotient by a normal odd-order subgroup has an
involution lift. -/
public theorem exists_involution_lift_of_odd_kernel
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {xq : H ⧸ N} (hxq : IsInvolution xq) :
    ∃ x : H, IsInvolution x ∧ QuotientGroup.mk' N x = xq := by
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let W : Subgroup (H ⧸ N) := Subgroup.zpowers xq
  let P : Subgroup H := W.comap q
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N xq
  have hxP : x ∈ P := by
    change q x ∈ W
    rw [hx]
    exact Subgroup.mem_zpowers xq
  let xP : P := ⟨x, hxP⟩
  have hxqOrder : orderOf xq = 2 :=
    orderOf_eq_prime hxq.sq_eq_one hxq.ne_one
  have htwoOrderX : 2 ∣ orderOf x := by
    rw [← hxqOrder, ← hx]
    exact orderOf_map_dvd q x
  have htwoCardP : 2 ∣ Nat.card P := by
    apply htwoOrderX.trans
    change orderOf (xP : H) ∣ Nat.card P
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard xP
  obtain ⟨t, htOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := P) 2 htwoCardP
  have htOrderH : orderOf (t : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact htOrder
  have htData := orderOf_eq_prime_iff.mp htOrderH
  have htInv : IsInvolution (t : H) := ⟨htData.2, htData.1⟩
  have hqtNe : q (t : H) ≠ 1 := by
    intro hqt
    have htN : (t : H) ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) (t : H)).mp hqt
    let tN : N := ⟨(t : H), htN⟩
    have htNI : IsInvolution tN := IsInvolution.subtype htInv htN
    have htNOrder : orderOf tN = 2 :=
      orderOf_eq_prime htNI.sq_eq_one htNI.ne_one
    have hdvd : 2 ∣ Nat.card N := by
      rw [← htNOrder]
      exact orderOf_dvd_natCard tN
    exact hNodd.not_two_dvd_nat hdvd
  have hqtW : q (t : H) ∈ W := t.property
  have hxqW : xq ∈ W := Subgroup.mem_zpowers xq
  have hcardW : Nat.card W = 2 := by
    simpa [W, Nat.card_zpowers] using hxqOrder
  have huniqueW :
      ∀ a b : W, a ≠ 1 → b ≠ 1 → a = b := by
    obtain ⟨w, hwne, hwuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : W)).mp hcardW
    intro a b ha hb
    exact (hwuniq a ha).trans (hwuniq b hb).symm
  have hqtEq : q (t : H) = xq := by
    have hsub : (⟨q (t : H), hqtW⟩ : W) = ⟨xq, hxqW⟩ := by
      apply huniqueW
      · intro h
        exact hqtNe (congrArg Subtype.val h)
      · intro h
        exact hxq.ne_one (congrArg Subtype.val h)
    exact congrArg Subtype.val hsub
  exact ⟨(t : H), htInv, hqtEq⟩

/-- In a strongly embedded subgroup, quotienting by a normal odd-order
subgroup makes the first Omega subgroup of the quotient 2-core abelian. -/
public theorem omega₁_pCore_quotient_isMulCommutative_of_stronglyEmbedded
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (N : Subgroup M) [N.Normal] (hNodd : Odd (Nat.card N)) :
    let P : Subgroup (M ⧸ N) := pCore 2 (M ⧸ N)
    IsMulCommutative
      ((omega₁ (G := P) (p := 2)).map P.subtype) := by
  classical
  dsimp only
  let P : Subgroup (M ⧸ N) := pCore 2 (M ⧸ N)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  have hP2 : IsPGroup 2 P := by
    simpa [P] using pCore_isPGroup (G := M ⧸ N) (p := 2)
  have hinvolution_center :
      ∀ x : P, IsInvolution x → x ∈ Subgroup.center P := by
    intro x hx
    let : Nontrivial P := ⟨⟨x, 1, hx.ne_one⟩⟩
    have hcenter_nontrivial : Nontrivial (Subgroup.center P) :=
      hP2.center_nontrivial
    have hcenter2 : IsPGroup 2 (Subgroup.center P) :=
      hP2.to_subgroup (Subgroup.center P)
    have htwo_center : 2 ∣ Nat.card (Subgroup.center P) := by
      rcases (IsPGroup.nontrivial_iff_card
        (p := 2) (G := Subgroup.center P) hcenter2).mp
          hcenter_nontrivial with ⟨n, hn, hcard⟩
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
    obtain ⟨zC, hzOrder⟩ :=
      exists_prime_orderOf_dvd_card'
        (G := Subgroup.center P) 2 htwo_center
    let z : P := (zC : P)
    have hzOrderP : orderOf z = 2 := by
      simpa [z] using (Subgroup.orderOf_coe zC).trans hzOrder
    have hzData := orderOf_eq_prime_iff.mp hzOrderP
    have hz : IsInvolution z := ⟨hzData.2, hzData.1⟩
    have hxq : IsInvolution (x : M ⧸ N) :=
      IsInvolution.map_of_injective hx P.subtype Subtype.val_injective
    have hzq : IsInvolution (z : M ⧸ N) :=
      IsInvolution.map_of_injective hz P.subtype Subtype.val_injective
    obtain ⟨xM, hxM, hqx⟩ :=
      exists_involution_lift_of_odd_kernel N hNodd hxq
    obtain ⟨zM, hzM, hqz⟩ :=
      exists_involution_lift_of_odd_kernel N hNodd hzq
    have hxX : IsInvolution (xM : X) :=
      IsInvolution.map_of_injective hxM M.subtype Subtype.val_injective
    have hzX : IsInvolution (zM : X) :=
      IsInvolution.map_of_injective hzM M.subtype Subtype.val_injective
    obtain ⟨g, hgM, hconj⟩ :=
      hM.involutions_conjugate_in xM.property hxX zM.property hzX
    let gM : M := ⟨g, hgM⟩
    let q : M →* M ⧸ N := QuotientGroup.mk' N
    have hconjM : rightConjugateElem xM gM = zM := by
      apply Subtype.ext
      exact hconj
    have hconjQ :
        rightConjugateElem (x : M ⧸ N) (q gM) = (z : M ⧸ N) := by
      calc
        rightConjugateElem (x : M ⧸ N) (q gM) =
            rightConjugateElem (q xM) (q gM) := by rw [hqx]
        _ = q (rightConjugateElem xM gM) := by
          simp [rightConjugateElem]
        _ = q zM := congrArg q hconjM
        _ = (z : M ⧸ N) := hqz
    rw [Subgroup.mem_center_iff]
    intro y
    let yg : P :=
      ⟨(q gM)⁻¹ * (y : M ⧸ N) * q gM, by
        simpa using
          (inferInstance : P.Normal).conj_mem
            (y : M ⧸ N) y.property (q gM)⁻¹⟩
    have hzyP : (yg : P) * z = z * yg :=
      (Subgroup.mem_center_iff.mp zC.property) yg
    have hzy :
        (yg : M ⧸ N) * (z : M ⧸ N) =
          (z : M ⧸ N) * (yg : M ⧸ N) :=
      congrArg Subtype.val hzyP
    have hxexpr :
        (x : M ⧸ N) = q gM * (z : M ⧸ N) * (q gM)⁻¹ := by
      calc
        (x : M ⧸ N) =
            q gM * rightConjugateElem (x : M ⧸ N) (q gM) *
              (q gM)⁻¹ := by simp [rightConjugateElem, mul_assoc]
        _ = q gM * (z : M ⧸ N) * (q gM)⁻¹ := by rw [hconjQ]
    have hyexpr :
        (y : M ⧸ N) = q gM * (yg : M ⧸ N) * (q gM)⁻¹ := by
      simp [yg, mul_assoc]
    apply Subtype.ext
    change (y : M ⧸ N) * (x : M ⧸ N) =
      (x : M ⧸ N) * (y : M ⧸ N)
    rw [hxexpr, hyexpr]
    calc
      (q gM * (yg : M ⧸ N) * (q gM)⁻¹) *
          (q gM * (z : M ⧸ N) * (q gM)⁻¹) =
          q gM * ((yg : M ⧸ N) * (z : M ⧸ N)) * (q gM)⁻¹ := by
            group
      _ = q gM * ((z : M ⧸ N) * (yg : M ⧸ N)) * (q gM)⁻¹ := by
        rw [hzy]
      _ = (q gM * (z : M ⧸ N) * (q gM)⁻¹) *
          (q gM * (yg : M ⧸ N) * (q gM)⁻¹) := by
            group
  have homega_center :
      omega₁ (G := P) (p := 2) ≤ Subgroup.center P := by
    rw [omega₁, omega, Subgroup.closure_le]
    intro x hxpow
    have hxsq : x ^ 2 = 1 := by simpa using hxpow
    by_cases hxone : x = 1
    · simp [hxone]
    · exact hinvolution_center x ⟨hxone, hxsq⟩
  let : IsMulCommutative (omega₁ (G := P) (p := 2)) := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply Subtype.ext
    exact ((Subgroup.mem_center_iff.mp (homega_center x.property)) y).symm
  exact Subgroup.map_isMulCommutative
    (omega₁ (G := P) (p := 2)) P.subtype

/-- An odd normal kernel and a commutative quotient force all Sylow
`2`-subgroups to be abelian. -/
public theorem hasAbelianSylowTwo_of_odd_normal_quotient_isMulCommutative
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    (hquot : IsMulCommutative (G ⧸ N)) :
    HasAbelianSylow 2 G := by
  classical
  intro P
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qP : P →* G ⧸ N := q.comp (P : Subgroup G).subtype
  have hPNcop : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card N) := by
    rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hNodd.coprime_two_left.pow_left n
  have hPinfN : (P : Subgroup G) ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hPNcop).eq_bot
  have hqP_inj : Function.Injective qP := by
    intro x y hxy
    apply Subtype.ext
    have hdiffN : (x : G)⁻¹ * (y : G) ∈ N := by
      apply QuotientGroup.eq.mp
      exact hxy
    have hdiffP : (x : G)⁻¹ * (y : G) ∈ (P : Subgroup G) :=
      P.mul_mem (P.inv_mem x.property) y.property
    have hdiffBot : (x : G)⁻¹ * (y : G) ∈
        ((P : Subgroup G) ⊓ N) := ⟨hdiffP, hdiffN⟩
    rw [hPinfN] at hdiffBot
    exact eq_of_inv_mul_eq_one (Subgroup.mem_bot.mp hdiffBot)
  let : IsMulCommutative (G ⧸ N) := hquot
  refine ⟨⟨?_⟩⟩
  intro x y
  apply hqP_inj
  simp only [map_mul]
  exact mul_comm (qP x) (qP y)

/-- Abelian Sylow `2`-subgroups lift across an odd-order quotient. -/
public theorem HasAbelianSylow.of_normal_odd_quotient
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hN : HasAbelianSylow 2 N)
    (hquotOdd : Odd (Nat.card (G ⧸ N))) :
    HasAbelianSylow 2 G := by
  classical
  intro P
  have hP_le_N : (P : Subgroup G) ≤ N := by
    let q : G →* G ⧸ N := QuotientGroup.mk' N
    let Pbar : Subgroup (G ⧸ N) := (P : Subgroup G).map q
    have hPbar2 : IsPGroup 2 Pbar := P.isPGroup'.map q
    have hPbarOdd : Odd (Nat.card Pbar) :=
      Odd.of_dvd_nat hquotOdd (Subgroup.card_subgroup_dvd_card Pbar)
    have hcard : Nat.card Pbar = 1 := by
      rcases hPbar2.card_eq_or_dvd with hcard | htwo
      · exact hcard
      · exact False.elim (hPbarOdd.not_two_dvd_nat htwo)
    have hPbarBot : Pbar = ⊥ := Subgroup.card_eq_one.mp hcard
    intro x hx
    have hxbar : q x ∈ Pbar := Subgroup.mem_map_of_mem q hx
    have hxone : q x = 1 := by
      simpa [hPbarBot] using hxbar
    exact (QuotientGroup.eq_one_iff (N := N) (x := x)).mp hxone
  let PN : Sylow 2 N := P.subtype hP_le_N
  let : IsMulCommutative (PN : Subgroup N) := hN PN
  have hmap : (PN : Subgroup N).map N.subtype = (P : Subgroup G) := by
    dsimp [PN]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP_le_N]
  rw [← hmap]
  exact Subgroup.map_isMulCommutative (PN : Subgroup N) N.subtype

/-! ## The two-dimensional Gorenstein endpoint -/

/-- In characteristic `p`, a `p`-element has determinant one in every
linear representation. -/
private theorem det_eq_one_of_isPElement_representation
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (rho : Representation F G V) {g : G}
    (hg : IsPElement (p := p) g) :
    LinearMap.det (rho g) = 1 := by
  rcases hg with ⟨n, hn⟩
  have hgpow : g ^ (p ^ n) = 1 := by
    rw [← hn, pow_orderOf_eq_one]
  have hrhopow : (rho g) ^ (p ^ n) = 1 := by
    simpa [MonoidHom.map_pow] using congrArg rho hgpow
  have hdetpow : LinearMap.det (rho g) ^ (p ^ n) = 1 := by
    calc
      LinearMap.det (rho g) ^ (p ^ n) =
          LinearMap.det ((rho g) ^ (p ^ n)) := by
            symm
            exact (LinearMap.det : Module.End F V →* F).map_pow
              (rho g) (p ^ n)
      _ = 1 := by rw [hrhopow]; exact map_one _
  have hsubpow :
      (LinearMap.det (rho g) - 1) ^ (p ^ n) = (0 : F) := by
    calc
      (LinearMap.det (rho g) - 1) ^ (p ^ n) =
          LinearMap.det (rho g) ^ (p ^ n) - (1 : F) ^ (p ^ n) := by
            simpa using sub_pow_char_pow
              (x := LinearMap.det (rho g)) (y := (1 : F)) (p := p) (n := n)
      _ = 0 := by simp [hdetpow]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsubpow)

/-- In odd characteristic, a nonidentity determinant-one two-dimensional
matrix whose square is one is the scalar matrix `-1`. -/
private theorem sl2_matrix_eq_neg_one
    {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (hpodd : Odd p)
    (A : Matrix (Fin 2) (Fin 2) F)
    (hdet : A.det = 1) (hsq : A ^ 2 = 1) (hne : A ≠ 1) :
    A = -1 := by
  have hCH := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two] at hCH
  simp [hdet, hsq] at hCH
  have h00 := congrFun (congrFun hCH 0) 0
  simp [Matrix.mul_apply, Matrix.algebraMap_eq_diagonal] at h00
  have h01 := congrFun (congrFun hCH 0) 1
  simp [Matrix.mul_apply, Matrix.algebraMap_eq_diagonal] at h01
  have h10 := congrFun (congrFun hCH 1) 0
  simp [Matrix.mul_apply, Matrix.algebraMap_eq_diagonal] at h10
  have h11 := congrFun (congrFun hCH 1) 1
  simp [Matrix.mul_apply, Matrix.algebraMap_eq_diagonal] at h11
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    exact (by decide : ¬ Odd 2) hpodd
  have htwo : (2 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  have htrace_ne : A.trace ≠ 0 := by
    intro htrace
    have htwo_zero : (2 : F) = 0 := by
      rw [htrace] at h00
      linear_combination h00
    exact htwo htwo_zero
  have hA01 : A 0 1 = 0 := h01.resolve_left htrace_ne
  have hA10 : A 1 0 = 0 := h10.resolve_left htrace_ne
  have htraceA00 : A.trace * A 0 0 = 2 := by
    linear_combination -h00
  have htraceA11 : A.trace * A 1 1 = 2 := by
    linear_combination -h11
  have hdiag : A 0 0 = A 1 1 := by
    apply mul_left_cancel₀ htrace_ne
    rw [htraceA00, htraceA11]
  have hsq' : A * A = 1 := by simpa [pow_two] using hsq
  have hsq00 := congrFun (congrFun hsq' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10] at hsq00
  have hA00_sq : (A 0 0) ^ 2 = 1 := by
    simpa [pow_two] using hsq00
  have hA00_ne_one : A 0 0 ≠ 1 := by
    intro hA00
    have hA11 : A 1 1 = 1 := hdiag.symm.trans hA00
    apply hne
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hA00, hA11, hA01, hA10]
  have hA00_neg : A 0 0 = -1 :=
    (sq_eq_one_iff.mp hA00_sq).resolve_left hA00_ne_one
  have hA11_neg : A 1 1 = -1 := hdiag.symm.trans hA00_neg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hA00_neg, hA11_neg, hA01, hA10]

/-- A faithful two-dimensional determinant-one representation in odd
characteristic has at most one element of order two. -/
private theorem unique_order_two_of_faithful_finrank_two_det_one
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (hpodd : Odd p)
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2)
    (hdet : ∀ g : G, LinearMap.det (rho g) = 1) :
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y := by
  classical
  let b : Module.Basis (Fin 2) F V := Module.finBasisOfFinrankEq F V hdim
  intro x y hx hy
  let Ax : Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrix b b (rho x)
  let Ay : Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrix b b (rho y)
  have hxpow : x ^ 2 = 1 := by
    rw [← hx, pow_orderOf_eq_one]
  have hypow : y ^ 2 = 1 := by
    rw [← hy, pow_orderOf_eq_one]
  have hrhoxpow : (rho x) ^ 2 = 1 := by
    simpa [MonoidHom.map_pow] using congrArg rho hxpow
  have hrhoypow : (rho y) ^ 2 = 1 := by
    simpa [MonoidHom.map_pow] using congrArg rho hypow
  have hAxpow : Ax ^ 2 = 1 := by
    dsimp [Ax]
    rw [pow_two, ← LinearMap.toMatrix_mul]
    rw [← pow_two, hrhoxpow, LinearMap.toMatrix_one]
  have hAypow : Ay ^ 2 = 1 := by
    dsimp [Ay]
    rw [pow_two, ← LinearMap.toMatrix_mul]
    rw [← pow_two, hrhoypow, LinearMap.toMatrix_one]
  have hAxdet : Ax.det = 1 := by
    simpa [Ax, LinearMap.det_toMatrix] using hdet x
  have hAydet : Ay.det = 1 := by
    simpa [Ay, LinearMap.det_toMatrix] using hdet y
  have hxne : x ≠ 1 := by
    intro hxone
    subst x
    simp at hx
  have hyne : y ≠ 1 := by
    intro hyone
    subst y
    simp at hy
  have hAxne : Ax ≠ 1 := by
    intro hAx
    apply hxne
    apply hrho
    apply (LinearMap.toMatrix b b).injective
    simpa [Ax, LinearMap.toMatrix_one] using hAx
  have hAyne : Ay ≠ 1 := by
    intro hAy
    apply hyne
    apply hrho
    apply (LinearMap.toMatrix b b).injective
    simpa [Ay, LinearMap.toMatrix_one] using hAy
  have hAxneg := sl2_matrix_eq_neg_one hpodd Ax hAxdet hAxpow hAxne
  have hAyneg := sl2_matrix_eq_neg_one hpodd Ay hAydet hAypow hAyne
  apply hrho
  apply (LinearMap.toMatrix b b).injective
  simpa [Ax, Ay] using hAxneg.trans hAyneg.symm

/-- A finite abelian `2`-group with at most one element of order two is
cyclic. -/
private theorem isCyclic_of_isPGroup_two_isMulCommutative_unique_order_two
    {G : Type*} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (hGcomm : IsMulCommutative G)
    (hunique : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y) :
    IsCyclic G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsMulCommutative G := hGcomm
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  let Omega : Subgroup G := omega₁ (G := G) (p := 2)
  have hOmegaElem : IsElementaryAbelian 2 Omega := by
    simpa [Omega] using
      IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2) (G := G)
  have : IsElementaryAbelian 2 Omega := hOmegaElem
  have hOmegaCard : Nat.card Omega ≤ 2 := by
    let f : Omega → Bool := fun x => decide (x = 1)
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx1 : x = 1
      · have hy1 : y = 1 := by
          by_contra hy1
          simp [f, hx1, hy1] at hxy
        exact hx1.trans hy1.symm
      · have hy1 : y ≠ 1 := by
          intro hy1
          simp [f, hx1, hy1] at hxy
        apply Subtype.ext
        have hxpow : x ^ (2 : ℕ) = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 Omega) x
        have hypow : y ^ (2 : ℕ) = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 Omega) y
        have hxord : orderOf (x : G) = 2 := by
          refine (orderOf_eq_prime_iff (x := (x : G)) (p := 2)).2 ⟨?_, ?_⟩
          · simpa using congrArg Subtype.val hxpow
          · intro hxG
            exact hx1 (Subtype.ext hxG)
        have hyord : orderOf (y : G) = 2 := by
          refine (orderOf_eq_prime_iff (x := (y : G)) (p := 2)).2 ⟨?_, ?_⟩
          · simpa using congrArg Subtype.val hypow
          · intro hyG
            exact hy1 (Subtype.ext hyG)
        exact hunique (x : G) (y : G) hxord hyord
    have hcard := Nat.card_le_card_of_injective f hf
    simpa using hcard
  have hquotCard : Nat.card (G ⧸ frattini G) ≤ 2 := by
    have hcardEq : Nat.card Omega = Nat.card (G ⧸ frattini G) := by
      simpa [Omega] using
        section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative
          (p := 2) G
    simpa [hcardEq] using hOmegaCard
  have hquotElem : IsElementaryAbelian 2 (G ⧸ frattini G) :=
    isElementaryAbelian_quotient_frattini (R := G) (p := 2)
  have : IsElementaryAbelian 2 (G ⧸ frattini G) := hquotElem
  have hquotRank : generatorRank (G ⧸ frattini G) ≤ 1 := by
    have hcardEq :
        Nat.card (G ⧸ frattini G) =
          2 ^ generatorRank (G ⧸ frattini G) := by
      simpa using elementaryAbelian_card_eq_pow_generatorRank
        (p := 2) (G ⧸ frattini G)
    by_contra hle
    have htwoLe : 2 ≤ generatorRank (G ⧸ frattini G) :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
    have hpowGe : 2 ^ 2 ≤ 2 ^ generatorRank (G ⧸ frattini G) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) htwoLe
    have hpowLe : 2 ^ generatorRank (G ⧸ frattini G) ≤ 2 := by
      simpa [hcardEq] using hquotCard
    have : 4 ≤ 2 := by simpa using hpowGe.trans hpowLe
    omega
  exact isCyclic_of_generatorRank_le_one
    ((generatorRank_le_generatorRank_quotient_frattini (p := 2) G).trans hquotRank)

/-- The odd-order endpoint: in dimension two, a faithful group generated by
two characteristic-`p` elements is a `p`-group. -/
private theorem odd_card_two_dimensional_generated_pElements_isPGroup
    {F H V : Type*} [Field F] [Group H] [Finite H]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (rho : Representation F H V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2)
    (x y : H) (hgen : Subgroup.closure ({x, y} : Set H) = ⊤)
    (hx : IsPElement (p := p) x) (hy : IsPElement (p := p) y)
    (hodd : Odd (Nat.card H)) :
    IsPGroup p H := by
  classical
  have hchar : ringChar F = p :=
    CharP.eq (R := F) (ringChar.charP F) (inferInstance : CharP F p)
  have hringPrime : Nat.Prime (ringChar F) := by
    simpa [hchar] using (Fact.out : Nat.Prime p)
  let : Fact (Nat.Prime (ringChar F)) := ⟨hringPrime⟩
  obtain ⟨P, _hPcomm, hcomm⟩ :=
    theorem_2_6_b (F := F) (G := H) hodd hdim hrho
  have hPnormal : (P : Subgroup H).Normal := by
    refine ⟨?_⟩
    intro n hn g
    have hgn : ⁅g, n⁆ ∈ (P : Subgroup H) := by
      exact hcomm (by
        rw [commutator_eq_closure]
        exact Subgroup.subset_closure (commutator_mem_commutatorSet g n))
    have hmul : ⁅g, n⁆ * n ∈ (P : Subgroup H) :=
      (P : Subgroup H).mul_mem hgn hn
    simpa [commutatorElement_def, mul_assoc] using hmul
  let : (P : Subgroup H).Normal := hPnormal
  have hmemP : ∀ z : H, IsPElement (p := p) z → z ∈ (P : Subgroup H) := by
    intro z hz
    let q : H →* H ⧸ (P : Subgroup H) := QuotientGroup.mk' (P : Subgroup H)
    rcases hz with ⟨m, hm⟩
    have hordP : orderOf (q z) ∣ p ^ m := by
      exact (orderOf_map_dvd q z).trans (by simp [hm])
    have hpQuot : Nat.Coprime p (Nat.card (H ⧸ (P : Subgroup H))) := by
      rw [← Subgroup.index_eq_card]
      exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr (by
        simpa [hchar] using P.not_dvd_index)
    have hordCard : orderOf (q z) ∣ Nat.card (H ⧸ (P : Subgroup H)) :=
      orderOf_dvd_natCard (q z)
    have hordOne : orderOf (q z) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hpQuot.pow_left m) hordP hordCard
    have hqz : q z = 1 := orderOf_eq_one_iff.mp hordOne
    exact (QuotientGroup.eq_one_iff (N := (P : Subgroup H)) (x := z)).mp hqz
  have hxP : x ∈ (P : Subgroup H) := hmemP x hx
  have hyP : y ∈ (P : Subgroup H) := hmemP y hy
  have hclosure : Subgroup.closure ({x, y} : Set H) ≤ (P : Subgroup H) := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxP
    · exact hyP
  have hPtop : (P : Subgroup H) = ⊤ := by
    rw [hgen] at hclosure
    exact top_le_iff.mp hclosure
  have hHring : IsPGroup (ringChar F) H := by
    let e : (P : Subgroup H) ≃* H :=
      (MulEquiv.subgroupCongr hPtop).trans Subgroup.topEquiv
    exact P.isPGroup'.of_equiv e
  simpa [hchar] using hHring

/-- Direct two-dimensional replacement for the final obstruction in
Gorenstein 3.8.1.  In odd characteristic, a faithful two-dimensional group
generated by two `p`-elements is a `p`-group whenever its Sylow
`2`-subgroups are abelian. -/
public theorem two_dimensional_generated_pElements_isPGroup_of_abelianSylowTwo
    {F H V : Type*} [Field F] [Group H] [Finite H]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    (rho : Representation F H V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2)
    (x y : H) (hgen : Subgroup.closure ({x, y} : Set H) = ⊤)
    (hpodd : Odd p)
    (hx : IsPElement (p := p) x) (hy : IsPElement (p := p) y)
    (hSylow : HasAbelianSylow 2 H) :
    IsPGroup p H := by
  classical
  let delta : H →* F :=
    (LinearMap.det : Module.End F V →* F).comp rho
  have hxker : x ∈ delta.ker := by
    rw [MonoidHom.mem_ker]
    exact det_eq_one_of_isPElement_representation rho hx
  have hyker : y ∈ delta.ker := by
    rw [MonoidHom.mem_ker]
    exact det_eq_one_of_isPElement_representation rho hy
  have hclosureKer : Subgroup.closure ({x, y} : Set H) ≤ delta.ker := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxker
    · exact hyker
  have hkerTop : delta.ker = ⊤ := by
    rw [hgen] at hclosureKer
    exact top_le_iff.mp hclosureKer
  have hdet : ∀ g : H, LinearMap.det (rho g) = 1 := by
    intro g
    have hgker : g ∈ delta.ker := by simp [hkerTop]
    simpa [delta, MonoidHom.mem_ker] using hgker
  have hunique : ∀ a b : H, orderOf a = 2 → orderOf b = 2 → a = b :=
    unique_order_two_of_faithful_finrank_two_det_one
      hpodd rho hrho hdim hdet
  by_cases hoddH : Odd (Nat.card H)
  · exact odd_card_two_dimensional_generated_pElements_isPGroup
      rho hrho hdim x y hgen hx hy hoddH
  · have hEven : Even (Nat.card H) := Nat.not_odd_iff_even.mp hoddH
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let S : Sylow 2 H := default
    have hScomm : IsMulCommutative S := hSylow S
    have hSunique :
        ∀ a b : S, orderOf a = 2 → orderOf b = 2 → a = b := by
      intro a b ha hb
      apply Subtype.ext
      exact hunique (a : H) (b : H)
        (by simpa [Subgroup.orderOf_coe] using ha)
        (by simpa [Subgroup.orderOf_coe] using hb)
    have hScyclic : IsCyclic S :=
      isCyclic_of_isPGroup_two_isMulCommutative_unique_order_two
        S.isPGroup' hScomm hSunique
    have hmin : (Nat.card H).minFac = 2 :=
      (Nat.minFac_eq_two_iff (Nat.card H)).2 hEven.two_dvd
    have hnormalizerCentralizer :
        Subgroup.normalizer ((S : Subgroup H) : Set H) ≤
          Subgroup.centralizer ((S : Subgroup H) : Set H) :=
      hScyclic.normalizer_le_centralizer hmin
    have hScenter :
        (S : Subgroup H) ≤
          centerIn (G := H) (Subgroup.normalizer ((S : Subgroup H) : Set H)) := by
      intro s hs
      refine ⟨S.le_normalizer hs, ?_⟩
      change s ∈ Subgroup.centralizer
        ((Subgroup.normalizer ((S : Subgroup H) : Set H)) : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact ((Subgroup.mem_centralizer_iff.mp
        (hnormalizerCentralizer hn)) s hs).symm
    obtain ⟨N, hNnormal, hNcop, hquotTwo⟩ :=
      exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer
        2 S hScenter
    let : N.Normal := hNnormal
    have hNodd : Odd (Nat.card N) := hNcop.odd_of_left
    let q : H →* H ⧸ N := QuotientGroup.mk' N
    have hkill : ∀ z : H, IsPElement (p := p) z → q z = 1 := by
      intro z hz
      rcases hz with ⟨m, hm⟩
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hquotTwo) (q z)
      have horderP : orderOf (q z) ∣ p ^ m :=
        (orderOf_map_dvd q z).trans (by simp [hm])
      have horderTwo : orderOf (q z) ∣ 2 ^ n := by rw [hn]
      have hcop : Nat.Coprime (p ^ m) (2 ^ n) :=
        (hpodd.coprime_two_right.pow_left m).pow_right n
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes hcop horderP horderTwo)
    have hxN : x ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) (x := x)).mp (hkill x hx)
    have hyN : y ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) (x := y)).mp (hkill y hy)
    have hclosureN : Subgroup.closure ({x, y} : Set H) ≤ N := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxN
      · exact hyN
    have hNtop : N = ⊤ := by
      rw [hgen] at hclosureN
      exact top_le_iff.mp hclosureN
    have hoddH' : Odd (Nat.card H) := by
      simpa [hNtop] using hNodd
    exact odd_card_two_dimensional_generated_pElements_isPGroup
      rho hrho hdim x y hgen hx hy hoddH'

private abbrev SL23Concrete := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private instance : DecidableEq SL23Concrete := fun A B =>
  decidable_of_iff (A.1 = B.1)
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private def sl23I : SL23Concrete :=
  ⟨!![(0 : ZMod 3), -1; 1, 0], by
    norm_num [Matrix.det_fin_two_of]⟩

private def sl23J : SL23Concrete :=
  ⟨!![(1 : ZMod 3), 1; 1, -1], by
    rw [Matrix.det_fin_two_of]
    decide⟩

/-- The standard quaternion subgroup of `SL(2,3)`. -/
private def quaternionToSL23 : QuaternionGroup 2 →* SL23Concrete where
  toFun
    | QuaternionGroup.a i => sl23I ^ i.val
    | QuaternionGroup.xa i => sl23J * sl23I ^ i.val
  map_one' := by
    rfl
  map_mul' := by
    rintro (i | i) (j | j)
    all_goals
      fin_cases i <;> fin_cases j <;>
        apply Subtype.ext <;>
        ext a b <;>
        fin_cases a <;> fin_cases b <;>
        decide

private theorem quaternionToSL23_injective :
    Function.Injective quaternionToSL23 := by
  decide

private theorem quaternionGroupTwo_isPGroup :
    IsPGroup 2 (QuaternionGroup 2) := by
  rw [IsPGroup.iff_card]
  refine ⟨3, ?_⟩
  norm_num [Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem quaternionGroupTwo_not_isMulCommutative :
    ¬ IsMulCommutative (QuaternionGroup 2) := by
  intro h
  let : IsMulCommutative (QuaternionGroup 2) := h
  have hcomm := (IsMulCommutative.is_comm
    (M := QuaternionGroup 2)).comm
      (QuaternionGroup.a 1 : QuaternionGroup 2)
      (QuaternionGroup.xa 0 : QuaternionGroup 2)
  simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
  have hbad := QuaternionGroup.xa.inj hcomm
  exact (by decide : (-(1 : ZMod 4)) ≠ 1) hbad

private theorem SL23_not_hasAbelianSylowTwo :
    ¬ HasAbelianSylow 2 SL23Concrete := by
  intro hSL
  have hRangeP : IsPGroup 2 quaternionToSL23.range := by
    have hrange :
        (⊤ : Subgroup (QuaternionGroup 2)).map quaternionToSL23 =
          quaternionToSL23.range := by
      ext x
      simp
    rw [← hrange]
    exact (quaternionGroupTwo_isPGroup.to_subgroup
      (⊤ : Subgroup (QuaternionGroup 2))).map quaternionToSL23
  obtain ⟨P, hRangePLe⟩ := hRangeP.exists_le_sylow
  let : IsMulCommutative (P : Subgroup SL23Concrete) := hSL P
  apply quaternionGroupTwo_not_isMulCommutative
  refine ⟨⟨?_⟩⟩
  intro x y
  apply quaternionToSL23_injective
  let xP : P := ⟨quaternionToSL23 x, hRangePLe ⟨x, rfl⟩⟩
  let yP : P := ⟨quaternionToSL23 y, hRangePLe ⟨y, rfl⟩⟩
  simpa [xP, yP] using congrArg Subtype.val (mul_comm xP yP)

/-- A finite group with abelian Sylow `2`-subgroups has no subquotient
isomorphic to `SL(2,3)`.  This is the exposed form of the obstruction; the
existing `Involves` definition currently has no public elimination theorem. -/
public theorem not_exists_SL23_section_of_hasAbelianSylowTwo
    {G : Type u} [Group G] [Finite G]
    (hG : HasAbelianSylow 2 G) :
    ¬ ∃ (H : Subgroup G) (N : Subgroup H) (_hN : N.Normal),
      Nonempty ((H ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  rintro ⟨H, N, hN, ⟨e⟩⟩
  let : N.Normal := hN
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply SL23_not_hasAbelianSylowTwo
  exact (hG.subgroup H).mapSurjective
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) |>.of_mulEquiv e

end CFSG.BenderSuzuki
