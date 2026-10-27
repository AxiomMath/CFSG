module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Hypotheses 1.1, 1.2 and the statements of Section 1

Formalization of the notation and statements of Section 1 of
Bender & Glauberman, *Characters of finite groups with dihedral Sylow
2-subgroups*, J. Algebra 70 (1981) 200--215, following
`refs/bender-glauberman-character.tex`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

/-- The subgroup `X` is inverted by the involution `s`. -/
@[expose]
public def IsInvertedBy {G : Type u} [Group G] (s : G) (X : Subgroup G) : Prop :=
  ∀ x : G, x ∈ X → s * x * s⁻¹ = x⁻¹

/-- `T` is a TI-set of `G`: any conjugate of `T` is either equal to `T` or
disjoint from it. -/
@[expose]
public def IsTISet {G : Type u} [Group G] (T : Set G) : Prop :=
  ∀ g : G, (fun t : G => g * t * g⁻¹) '' T = T ∨ T ∩ (fun t : G => g * t * g⁻¹) '' T = ∅

/-- The class function of `H` induced from `φ : ClassFunction ↥H0`, where
`H0 ≤ H`; this is the paper's `φ^H`. -/
public abbrev inducedFromSub {G : Type u} [Group G] [Fintype G] {H0 H : Subgroup G}
    (_hH0 : H0 ≤ H) (φ : ClassFunction (↥H0)) : ClassFunction (↥H) :=
  inducedClassFunction (H0.subgroupOf H)
    (fun x : ↥(H0.subgroupOf H) => φ ⟨(x : G), (Subgroup.mem_subgroupOf.mp x.2)⟩)

/-- `K` is a nontrivial normal subgroup of `X` on which every element outside
`K` acts fixed-point-freely (a Frobenius group with kernel `K`).

The nontriviality clause is part of the usual meaning of "Frobenius kernel"
and matches `IsFrobeniusGroupWithKernelComplement`. -/
public def IsFrobeniusGroupWithKernel {G : Type u} [Group G] (X K : Subgroup G) : Prop :=
  IsNormalIn K X ∧
    (∀ x : G, x ∈ X → x ∉ K → ∀ k : G, k ∈ K → k ≠ 1 → x * k * x⁻¹ ≠ k) ∧
      K ≠ ⊥

/-! ## Hypothesis 1.1 and the notation -/

/-- Hypothesis 1.1 and the notation block of the paper:

* `G` has a dihedral Sylow `2`-subgroup `S`;
* `S0` is a cyclic subgroup of index `2` in `S`;
* `t` is the involution in `S0`, `s` an involution in `S - S0`;
* `t1, t2` are involutions in `S - S0` with `S0 = ⟨t1·t2⟩`;
* `H = C_G(t)`;
* `H = U·S` with `U = O(H)` — the paper's notation block asserts
  `H0 = US0` is a subgroup of index `2` in `H = US = H0⟨s⟩`
  (`refs/bender-glauberman-character.tex` L79; recalled from the
  Gorenstein--Walter structure theorem [10]);
* `G` has exactly one class of involutions.
-/
public structure Hyp11 (G : Type u) [Group G] [Finite G] where
  S : Sylow 2 G
  m : ℕ
  one_le_m : 1 ≤ m
  dihedralEquiv : Nonempty (S ≃* DihedralGroup (2 ^ m))
  S0 : Subgroup G
  S0_le_S : S0 ≤ (S : Subgroup G)
  S0_cyclic : IsCyclic S0
  S_index_two : Nat.card S = 2 * Nat.card S0
  t : G
  t_mem_S0 : t ∈ S0
  t_involution : IsInvolution t
  one_involution_class : ∀ x y : G, IsInvolution x → IsInvolution y →
    ∃ g : G, g * x * g⁻¹ = y
  s : G
  s_mem_S : s ∈ (S : Subgroup G)
  s_not_mem_S0 : s ∉ S0
  s_involution : IsInvolution s
  t1 : G
  t2 : G
  t1_mem_S : t1 ∈ (S : Subgroup G)
  t1_not_mem_S0 : t1 ∉ S0
  t1_involution : IsInvolution t1
  t2_mem_S : t2 ∈ (S : Subgroup G)
  t2_not_mem_S0 : t2 ∉ S0
  t2_involution : IsInvolution t2
  S0_eq_zpowers : S0 = Subgroup.zpowers (t1 * t2)
  H : Subgroup G
  H_eq_centralizer : H = Subgroup.centralizer ({t} : Set G)
  H_eq_US : (oddCoreOf H : Subgroup G) ⊔ (S : Subgroup G) = H

/-- The auxiliary `K₁`/`K₂` data from the notation following Hypothesis 1.1.

The structural hypotheses in `Hyp11` do not by themselves imply that a
largest odd-order subgroup inverted by `tᵢ` exists: inverted subgroups are not
closed under joins in general.  Consequently this paper-specific choice is a
separate contract, required only by the results that use `K₁`, `K₂`, or
`K = K₁ ∩ K₂`. -/
public class Hyp11KData {G : Type u} [Group G] [Finite G] (c : Hyp11 G) where
  K1 : Subgroup G
  K2 : Subgroup G
  K1_le_H : K1 ≤ c.H
  K2_le_H : K2 ≤ c.H
  K1_odd : Nat.Coprime 2 (Nat.card K1)
  K2_odd : Nat.Coprime 2 (Nat.card K2)
  K1_inverted : IsInvertedBy c.t1 K1
  K2_inverted : IsInvertedBy c.t2 K2
  K1_maximal : ∀ X : Subgroup G, X ≤ c.H →
    Nat.Coprime 2 (Nat.card X) → IsInvertedBy c.t1 X → X ≤ K1
  K2_maximal : ∀ X : Subgroup G, X ≤ c.H →
    Nat.Coprime 2 (Nat.card X) → IsInvertedBy c.t2 X → X ≤ K2

namespace Hyp11

variable {G : Type u} [Group G] [Finite G] (c : Hyp11 G)

/-! ## Optional `K₁`/`K₂` notation -/

/-- The largest odd-order subgroup of `H` selected as inverted by `t₁`. -/
@[expose]
public def K1 (c : Hyp11 G) [h : Hyp11KData c] : Subgroup G := h.K1

/-- The largest odd-order subgroup of `H` selected as inverted by `t₂`. -/
@[expose]
public def K2 (c : Hyp11 G) [h : Hyp11KData c] : Subgroup G := h.K2

public theorem K1_le_H (c : Hyp11 G) [h : Hyp11KData c] : c.K1 ≤ c.H :=
  h.K1_le_H

public theorem K2_le_H (c : Hyp11 G) [h : Hyp11KData c] : c.K2 ≤ c.H :=
  h.K2_le_H

public theorem K1_odd (c : Hyp11 G) [h : Hyp11KData c] :
    Nat.Coprime 2 (Nat.card c.K1) :=
  h.K1_odd

public theorem K2_odd (c : Hyp11 G) [h : Hyp11KData c] :
    Nat.Coprime 2 (Nat.card c.K2) :=
  h.K2_odd

public theorem K1_inverted (c : Hyp11 G) [h : Hyp11KData c] :
    IsInvertedBy c.t1 c.K1 :=
  h.K1_inverted

public theorem K2_inverted (c : Hyp11 G) [h : Hyp11KData c] :
    IsInvertedBy c.t2 c.K2 :=
  h.K2_inverted

public theorem K1_maximal (c : Hyp11 G) [h : Hyp11KData c] :
    ∀ X : Subgroup G, X ≤ c.H → Nat.Coprime 2 (Nat.card X) →
      IsInvertedBy c.t1 X → X ≤ c.K1 :=
  h.K1_maximal

public theorem K2_maximal (c : Hyp11 G) [h : Hyp11KData c] :
    ∀ X : Subgroup G, X ≤ c.H → Nat.Coprime 2 (Nat.card X) →
      IsInvertedBy c.t2 X → X ≤ c.K2 :=
  h.K2_maximal

/-- `U = O(H)`. -/
@[expose]
public def U (c : Hyp11 G) : Subgroup G := oddCoreOf c.H

/-- `H0 = U·S0`. -/
@[expose]
public def H0 (c : Hyp11 G) : Subgroup G := c.U ⊔ (c.S0 : Subgroup G)

/-- `Bi = C_U(ti)`. -/
public def B1 (c : Hyp11 G) : Subgroup G := centralizerIn c.U c.t1

/-- `Bi = C_U(ti)`. -/
public def B2 (c : Hyp11 G) : Subgroup G := centralizerIn c.U c.t2

/-- `B = B1 ∩ B2 = C_U(S)`. -/
public def B (c : Hyp11 G) : Subgroup G := c.B1 ⊓ c.B2

/-- `ki = |H : C_H(ti)|`. -/
@[expose]
public def k1 (c : Hyp11 G) : ℕ := ((centralizerIn c.H c.t1).subgroupOf c.H).index

/-- `ki = |H : C_H(ti)|`. -/
@[expose]
public def k2 (c : Hyp11 G) : ℕ := ((centralizerIn c.H c.t2).subgroupOf c.H).index

/-- `k = k1 + k2`. -/
@[expose]
public def k (c : Hyp11 G) : ℕ := c.k1 + c.k2

/-- `K = K1 ∩ K2`. -/
@[expose]
public def K (c : Hyp11 G) [Hyp11KData c] : Subgroup G := c.K1 ⊓ c.K2

/-- `T = H0 - U`. -/
@[expose]
public def T (c : Hyp11 G) : Set G := (c.H0 : Set G) \ (c.U : Set G)

end Hyp11

/-! ## Hypothesis 1.2 -/

/-- Hypothesis 1.2: `H0' ≤ U ⊲ H0 ⊲ H ≤ G`, `T = H0 - U` is a TI-set with
`N_G(T) = H`, and `Λ` is the set of linear characters of `H0/U`. -/
public structure Hyp12 {G : Type u} [Group G] [Finite G] (c : Hyp11 G) where
  H0_comm_le_U : ⁅c.H0, c.H0⁆ ≤ c.U
  U_normal_in_H0 : IsNormalIn c.U c.H0
  H0_normal_in_H : IsNormalIn c.H0 c.H
  T_is_TI : IsTISet c.T
  T_normalizer : Subgroup.normalizer c.T = c.H
  Lambda : Set (ClassFunction (↥c.H0))
  Lambda_eq : Lambda = {lam : ClassFunction (↥c.H0) | IsLinearCharacter lam ∧
    ∀ u : ↥c.H0, (u : G) ∈ c.U → lam u = 1}

end CFSG.BenderGlauberman
