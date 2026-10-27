module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115QuotientLift

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: ambient normalization after the quotient lift

This module packages the source-independent algebra after the quotient/Sylow
lift.  The only hypothesis about the Lemma 11.5 subgroup `B` is the preceding
part-(c) anti-fixed-set characterization and its commutativity; no part-(d) or
part-(e) conclusion is assumed.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- A subgroup disjoint from the quotient kernel and mapping onto an abelian
quotient subgroup is itself abelian. -/
public theorem lemma115_lift_isMulCommutative
    {G : Type u} [Group G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup G) (Qbar : Subgroup (G ⧸ K))
    (hQmap : Q.map (QuotientGroup.mk' K) = Qbar)
    (hdisj : Disjoint Q K)
    (hQbarComm : IsMulCommutative Qbar) :
    IsMulCommutative Q := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hqInjective : Function.Injective (q.comp Q.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have hdivK : (x : G) / (y : G) ∈ K := by
      apply QuotientGroup.eq_iff_div_mem.mp
      exact hxy
    have hdivQ : (x : G) / (y : G) ∈ Q :=
      Q.div_mem x.property y.property
    have hdivBot : (x : G) / (y : G) ∈ (⊥ : Subgroup G) :=
      hdisj.le_bot ⟨hdivQ, hdivK⟩
    have hdivOne : (x : G) / (y : G) = 1 := by
      simpa using hdivBot
    exact div_eq_one.mp hdivOne
  refine IsMulCommutative.mk ⟨?_⟩
  intro x y
  apply hqInjective
  change q ((x * y : Q) : G) = q ((y * x : Q) : G)
  change q ((x : G) * (y : G)) = q ((y : G) * (x : G))
  rw [map_mul, map_mul]
  let xbar : Qbar := ⟨q (x : G), by
    rw [← hQmap]
    exact Subgroup.mem_map_of_mem q x.property⟩
  let ybar : Qbar := ⟨q (y : G), by
    rw [← hQmap]
    exact Subgroup.mem_map_of_mem q y.property⟩
  exact congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := Qbar)).comm xbar ybar)

/-- The lifted Sylow subgroup lies in the ambient anti-fixed subgroup once the
preceding part-(c) characterization of `B` is available. -/
public theorem lemma115_lift_Q_le_B
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d103 : Lemma103Conclusion M d.choice.P d83.u)
    {f : ℕ}
    (hL : Lemma115QuotientLiftConclusion d83 d d103 f)
    (B : Subgroup X)
    (hBset : (B : Set X) = peterfalviKSet
      (Subgroup.centralizer ({t * d83.u} : Set X)) d83.u) :
    hL.Q.map (lemma103NStar d.choice.P).subtype ≤ B := by
  classical
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  let q : Nstar →* (Nstar ⧸ core) := QuotientGroup.mk' core
  let Qx : Subgroup X := hL.Q.map Nstar.subtype
  have hQbarComm : IsMulCommutative d103.Qbar := by
    letI : Fact d103.q.Prime := ⟨d103.q_prime⟩
    letI : IsElementaryAbelian d103.q d103.Qbar :=
      d103.Qbar_elementaryAbelian
    infer_instance
  have hQcomm : IsMulCommutative hL.Q := by
    simpa [q, core, Nstar, P] using
      (lemma115_lift_isMulCommutative (K := core) (Q := hL.Q)
        (Qbar := d103.Qbar) hL.Q_map hL.Q_disjoint_core hQbarComm)
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨q0, hq0, hqx⟩
  have hq0inv : rightConjugateElem (q0 : X) d83.u = (q0 : X)⁻¹ := by
    have h := congrArg Subtype.val (hL.Q_inverted ⟨q0, hq0⟩)
    change (d103.uStar : X)⁻¹ * (q0 : X) * (d103.uStar : X) =
      ((q0 : Nstar)⁻¹ : X) at h
    rw [d103.uStar_eq] at h
    simpa [rightConjugateElem, d83.u_involution.inv_eq_self] using h
  have hq0tu : (q0 : X) * (t * d83.u) =
      (t * d83.u) * (q0 : X) := by
    have htuQ : (⟨q0, hq0⟩ : hL.Q) *
          (⟨hL.tuStar, hL.tuStar_mem_Q⟩ : hL.Q) =
        (⟨hL.tuStar, hL.tuStar_mem_Q⟩ : hL.Q) *
          (⟨q0, hq0⟩ : hL.Q) :=
      (IsMulCommutative.is_comm (M := hL.Q)).comm
        ⟨q0, hq0⟩ ⟨hL.tuStar, hL.tuStar_mem_Q⟩
    have htuX := congrArg (fun z : hL.Q => (z : Nstar)) htuQ
    have htuX' := congrArg (fun z : Nstar => (z : X)) htuX
    change (q0 : X) * (hL.tuStar : X) =
      (hL.tuStar : X) * (q0 : X) at htuX'
    rw [hL.tuStar_eq] at htuX'
    simpa using htuX'
  have hq0cent : (q0 : X) ∈
      Subgroup.centralizer ({t * d83.u} : Set X) := by
    exact Subgroup.mem_centralizer_singleton_iff.mpr hq0tu
  have hq0B : (q0 : X) ∈ B := by
    change (q0 : X) ∈ (B : Set X)
    rw [hBset]
    exact ⟨hq0cent, hq0inv⟩
  rw [← hqx]
  exact hq0B

/-- If `B` is abelian and contains `a`, its anti-fixed description relative to
`C_X(a)` can be shrunk to the centralizer of the whole subgroup `Q`. -/
public theorem lemma115_anti_fixed_centralizer_shrink
    {X : Type u} [Group X]
    {Q B : Subgroup X} {u a : X}
    (hBset : (B : Set X) = peterfalviKSet
      (Subgroup.centralizer ({a} : Set X)) u)
    (haQ : a ∈ Q) (hQB : Q ≤ B)
    (hBcomm : IsMulCommutative B) :
    (B : Set X) = peterfalviKSet
      (Subgroup.centralizer (Q : Set X)) u := by
  apply Set.Subset.antisymm
  · intro x hxB
    have hxAnti : x ∈ peterfalviKSet
        (Subgroup.centralizer ({a} : Set X)) u := by
      rw [← hBset]
      exact hxB
    refine ⟨?_, hxAnti.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hqQ
    have hqB : q ∈ B := hQB hqQ
    have hcomm :=
      (IsMulCommutative.is_comm (M := B)).comm
        (⟨q, hqB⟩ : B) (⟨x, hxB⟩ : B)
    exact congrArg Subtype.val hcomm
  · intro x hx
    rw [hBset]
    refine ⟨?_, hx.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx.1) a haQ).symm

/-- Conjugation by an element normalizing `Q` and centralizing `u` preserves the
anti-fixed set in `C_X(Q)`. -/
public theorem lemma115_normalizes_anti_fixed_centralizer
    {X : Type u} [Group X]
    {Q B : Subgroup X} {u c : X}
    (hBset : (B : Set X) = peterfalviKSet
      (Subgroup.centralizer (Q : Set X)) u)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set X))
    (hcu : c ∈ Subgroup.centralizer ({u} : Set X)) :
    c ∈ Subgroup.normalizer (B : Set X) := by
  have hforward : ∀ {g : X},
      g ∈ Subgroup.normalizer (Q : Set X) →
      g ∈ Subgroup.centralizer ({u} : Set X) →
      ∀ {x : X}, x ∈ B → g * x * g⁻¹ ∈ B := by
    intro g hgQ hgu x hx
    change x ∈ (B : Set X) at hx
    change g * x * g⁻¹ ∈ (B : Set X)
    rw [hBset] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqback : g⁻¹ * q * g ∈ Q := by
        have hiff := (Subgroup.mem_normalizer_iff.mp hgQ)
          (g⁻¹ * q * g)
        apply hiff.mpr
        simpa [mul_assoc] using hq
      have hxcomm : (g⁻¹ * q * g) * x =
          x * (g⁻¹ * q * g) :=
        (Subgroup.mem_centralizer_iff.mp hx.1) _ hqback
      calc
        q * (g * x * g⁻¹) = g * (g⁻¹ * q * g) * x * g⁻¹ := by
          group
        _ = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [hxcomm]
        _ = g * x * (g⁻¹ * q * g) * g⁻¹ := by group
        _ = (g * x * g⁻¹) * q := by group
    · have hguComm : Commute g u :=
        Subgroup.mem_centralizer_singleton_iff.mp hgu
      have hleft : u⁻¹ * g = g * u⁻¹ := hguComm.symm.inv_left
      have hright : g⁻¹ * u = u * g⁻¹ := hguComm.inv_left
      have hxinv : u⁻¹ * x * u = x⁻¹ := by
        simpa [rightConjugateElem] using hx.2
      calc
        u⁻¹ * (g * x * g⁻¹) * u =
            (u⁻¹ * g) * x * (g⁻¹ * u) := by group
        _ = (g * u⁻¹) * x * (u * g⁻¹) := by rw [hleft, hright]
        _ = g * (u⁻¹ * x * u) * g⁻¹ := by group
        _ = g * x⁻¹ * g⁻¹ := by rw [hxinv]
        _ = (g * x * g⁻¹)⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward hcQ hcu
  · intro hx
    have h := hforward
      ((Subgroup.normalizer (Q : Set X)).inv_mem hcQ)
      ((Subgroup.centralizer ({u} : Set X)).inv_mem hcu) hx
    simpa [mul_assoc] using h

/-- A normal subgroup of a subgroup `N` maps to an ambient subgroup normalized
by `N`. -/
public theorem lemma115_subtype_normalizes_normal_map
    {X : Type u} [Group X]
    (N : Subgroup X) (Q : Subgroup N)
    (hQnormal : Q.Normal) :
    N ≤ Subgroup.normalizer ((Q.map N.subtype : Subgroup X) : Set X) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le Q)).mp
  have hEq : (Q.map N.subtype).subgroupOf N = Q := by
    apply le_antisymm
    · intro x hx
      change (x : X) ∈ Q.map N.subtype at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
      have : y = x := by
        apply Subtype.ext
        exact hxy
      simpa [this] using hy
    · intro x hx
      change (x : X) ∈ Q.map N.subtype
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hEq]
  exact hQnormal

/-- The quotient-lift factorization normalizes the ambient anti-fixed subgroup.
The premise `hBset` is exactly the preceding part-(c) characterization. -/
public theorem lemma115_lift_normalizes_B
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d103 : Lemma103Conclusion M d.choice.P d83.u)
    {f : ℕ}
    (hL : Lemma115QuotientLiftConclusion d83 d d103 f)
    (B : Subgroup X)
    (hBset : (B : Set X) = peterfalviKSet
      (Subgroup.centralizer ({t * d83.u} : Set X)) d83.u)
    (hBcomm : IsMulCommutative B) :
    lemma103NStar d.choice.P ≤ Subgroup.normalizer (B : Set X) := by
  classical
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let Qx : Subgroup X := hL.Q.map Nstar.subtype
  letI : IsMulCommutative B := hBcomm
  letI : hL.Q.Normal := hL.Q_normal
  have hQB : Qx ≤ B := by
    simpa [Qx, Nstar, P] using
      lemma115_lift_Q_le_B d83 d d103 hL B hBset
  have htuQ : t * d83.u ∈ Qx := by
    refine Subgroup.mem_map.mpr ⟨hL.tuStar, hL.tuStar_mem_Q, ?_⟩
    exact hL.tuStar_eq
  have hBsetQ : (B : Set X) = peterfalviKSet
      (Subgroup.centralizer (Qx : Set X)) d83.u :=
    lemma115_anti_fixed_centralizer_shrink hBset htuQ hQB hBcomm
  have hNnormQ : Nstar ≤ Subgroup.normalizer (Qx : Set X) := by
    simpa [Qx] using
      lemma115_subtype_normalizes_normal_map Nstar hL.Q hL.Q_normal
  intro n hn
  let nStar : Nstar := ⟨n, by simpa [Nstar, P] using hn⟩
  have hnSup : nStar ∈ hL.Q ⊔
      Subgroup.centralizer ({d103.uStar} : Set Nstar) := by
    rw [hL.Q_factorization]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hnSup with
    ⟨q, hqQ, c, hcU, hqcn⟩
  have hqQx : (q : X) ∈ Qx := by
    exact Subgroup.mem_map.mpr ⟨q, hqQ, rfl⟩
  have hqB : (q : X) ∈ B := hQB hqQx
  have hqCentB : (q : X) ∈ Subgroup.centralizer (B : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := B)).comm
        (⟨b, hb⟩ : B) (⟨(q : X), hqB⟩ : B))
  have hqNormB : (q : X) ∈ Subgroup.normalizer (B : Set X) :=
    centralizer_le_normalizer B hqCentB
  have hcNormQ : (c : X) ∈ Subgroup.normalizer (Qx : Set X) :=
    hNnormQ c.property
  have hcCentU : (c : X) ∈
      Subgroup.centralizer ({d83.u} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hcU)
    change (c : X) * (d103.uStar : X) =
      (d103.uStar : X) * (c : X) at h
    simpa [d103.uStar_eq] using h
  have hcNormB : (c : X) ∈ Subgroup.normalizer (B : Set X) :=
    lemma115_normalizes_anti_fixed_centralizer
      hBsetQ hcNormQ hcCentU
  have hprod : (q : X) * (c : X) ∈
      Subgroup.normalizer (B : Set X) :=
    (Subgroup.normalizer (B : Set X)).mul_mem hqNormB hcNormB
  have hqcnX := congrArg (fun z : Nstar => (z : X)) hqcn
  change (q : X) * (c : X) = n at hqcnX
  rwa [hqcnX] at hprod

end CFSG.BenderSuzuki
