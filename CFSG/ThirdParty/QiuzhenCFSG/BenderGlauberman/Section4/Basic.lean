module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark31
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 4 — shared infrastructure

The Section-4 preamble: the case `|S| = 4`, the generalized characters
`δν := ν̃ − λ̃₂ν`, the irreducible character `ν̂` of `B` (Glauberman
correspondence), the graph `Δ`, and the normalizer transport facts.  This
module is the separately assigned shared-infrastructure exception to
one-theorem-per-file; it imports only the compiled lower Section-3 modules
(not the currently broken full `BenderGlauberman.Section3` wrapper).
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character
open Sylow

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section4

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- The hypothesis of Section 4 of the paper: `|S| = 4` (in force throughout
Section 4, on top of `Section3Hyp`). -/
@[expose] public def Section4Hyp (c : Hyp11 G) : Prop :=
  Nat.card (↥(c.S : Subgroup G)) = 4

/-- `|S0| = 2` in the Section-4 case `|S| = 4`. -/
public lemma S0_card_eq_two_of_section4 (c : Hyp11 G) (hS4 : Section4Hyp c) :
    Nat.card (↥(c.S0 : Subgroup G)) = 2 := by
  unfold Section4Hyp at hS4
  have h4 : 2 * Nat.card (↥(c.S0 : Subgroup G)) = 4 := by
    rw [← c.S_index_two, hS4]
  omega

/-- The index-two subgroup `S' ≤ S0` is trivial when `|S| = 4`. -/
public lemma SPrime_eq_bot_of_section4 (c : Hyp11 G) (hS4 : Section4Hyp c) :
    SPrime c = ⊥ := by
  classical
  have hS0card : Nat.card (↥(c.S0 : Subgroup G)) = 2 :=
    S0_card_eq_two_of_section4 c hS4
  have hsq : (c.t1 * c.t2) ^ 2 = 1 := by
    have h2 :
        (⟨c.t1 * c.t2, S0_generator_mem_S0 c⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 :=
      sq_eq_one_of_card_two hS0card _
    simpa [Subgroup.coe_pow] using congrArg Subtype.val h2
  unfold SPrime
  rw [hsq, Subgroup.zpowers_one_eq_bot]

/-- `λ2·ν`: the product of the linear character `λ2` with `ν ∈ Irr(H0)`,
again an irreducible character of `H0` (the paper's `λ2ν`). -/
@[expose] public def lambdaTwoMul (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) : Irr (↥c.H0) :=
  ⟨LambdaChar (lambdaTwo c h12).1 * ν.1,
    isIrreducibleCharacter_mul_linear
      (isLinearCharacter_of_hom (lambdaTwo c h12).1) ν.2⟩

/-- `λ2·ν` is `Λ`-equivalent to `ν` (the hypothesis of Coherence 2.3(ii)
for the pair `λ2ν`, `ν`). -/
public theorem lambdaTwoMul_equiv (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : Irr (↥c.H0)) :
    LambdaChar (lambdaTwo c h12).1 * ν.1 ∈ orbit c.H0 c.U ν.1 := by
  classical
  exact Finset.mem_image.mpr ⟨lambdaTwo c h12, Finset.mem_univ _, rfl⟩

/-- `δν := ν̃ − λ̃₂ν`: the paper's `δν = (ν−λ2ν)* = ν̃ − λ̃₂ν` for
`ν = ν^s ∈ Irr(H0)` with `ν(t) = ν(1)` (see `deltaNu_eq_induced` for the
induced form). -/
@[expose] public def deltaNu (c : Hyp11 G) (h12 : Hyp12 c) (ν : Irr (↥c.H0)) :
    ClassFunction G :=
  tildeNu c h12 ν - tildeNu c h12 (lambdaTwoMul c h12 ν)

/-- Orbits are symmetric: `μ ∈ orbit ν` implies `ν ∈ orbit μ`. -/
private lemma orbit_symm (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμ : μ ∈ orbit c.H0 c.U ν) : ν ∈ orbit c.H0 c.U μ := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, hEq⟩
  have hL : LambdaChar l.1 * ν = μ := hEq
  refine Finset.mem_image.mpr ⟨l⁻¹, Finset.mem_univ _, ?_⟩
  rw [← hL]
  ext x
  simp [LambdaChar]

/-- `δν = (ν−λ2ν)*`: the induced form of `δν`, by Coherence 2.3(ii) applied
to the `Λ`-equivalent characters `ν` and `λ2ν`. -/
public theorem deltaNu_eq_induced (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) :
    deltaNu c h12 ν =
      inducedClassFunction c.H0 (ν.1 - LambdaChar (lambdaTwo c h12).1 * ν.1) := by
  classical
  let lν : Irr (↥c.H0) := lambdaTwoMul c h12 ν
  have hL : ν.1 ∈ orbit c.H0 c.U lν.1 := by
    exact orbit_symm c (lambdaTwoMul_equiv c h12 ν)
  rw [deltaNu]
  exact (tildeNu_ind c h12 (μ := ν) (ν := lν) hL).symm

/-- The constant-one class function is an irreducible character. -/
private theorem trivial_isIrreducible (G : Type u) [Group G] [Fintype G] :
    IsIrreducibleCharacter (1 : ClassFunction G) := by
  refine isIrreducibleCharacter_of_norm_one_inv
    (show IsCharacter (1 : ClassFunction G) by
      refine ⟨1, Representation.trivial ℂ G (Fin 1 → ℂ), ?_⟩
      ext g
      simp [Representation.character, LinearMap.trace_id, Representation.isTrivial_def]) ?_
  unfold scalarProductInv
  simp [Finset.sum_const]

/-- The trivial irreducible character of a finite group. -/
private noncomputable def trivialIrr (G : Type u) [Group G] [Fintype G] : Irr G :=
  ⟨(1 : ClassFunction G), trivial_isIrreducible G⟩

/-! ## `B = C_U(S)` as the fixed subgroup of the conjugation action -/

/-- `S ≤ N_G(U)`. -/
public lemma S4_S_le_normalizer_U (c : Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact S_normalizes_U c s hs u hu
  · intro hsu
    have h1 := S_normalizes_U c s⁻¹ ((c.S : Subgroup G).inv_mem hs) (s * u * s⁻¹) hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

public instance S4_instNormalizesS {G : Type u} [Group G] [Fintype G]
    {c : Hyp11 G} :
    Subgroup.Normalizes (c.S : Subgroup G) c.U := ⟨S4_S_le_normalizer_U c⟩

/-- `B ≤ U`. -/
public lemma mem_U_of_mem_B_s4 (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) : b ∈ c.U := by
  have hbB' : b ∈ Hyp11.B1 c ⊓ Hyp11.B2 c := by simpa [Hyp11.B] using hbB
  have hbB1 : b ∈ Hyp11.B1 c := (inf_le_left : Hyp11.B1 c ⊓ Hyp11.B2 c ≤ Hyp11.B1 c) hbB'
  have hbB1' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) := by
    simpa [Hyp11.B1, centralizerIn] using hbB1
  exact (inf_le_left : c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) ≤ c.U) hbB1'

/-- Every element of `B = C_U(t1) ∩ C_U(t2)` is fixed by the conjugation
action of the whole 2-subgroup `S` on `U` (`S = ⟨t1, t2⟩`, since `t1`, `t2`
are the two reflections of the dihedral group `S`). -/
public lemma b_mem_fixedSubgroup_s4 (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) :
    (⟨b, mem_U_of_mem_B_s4 c hbB⟩ : ↥c.U) ∈
      fixedSubgroup (c.S : Subgroup G) c.U := by
  classical
  rw [mem_fixedSubgroup_iff]
  intro a
  apply Subtype.ext
  change (a : G) * b * (a : G)⁻¹ = b
  have hbt1 : Commute c.t1 b := by
    have hbB1 : b ∈ Hyp11.B1 c :=
      (inf_le_left : Hyp11.B1 c ⊓ Hyp11.B2 c ≤ Hyp11.B1 c) hbB
    have hbB1' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) := by
      simpa [Hyp11.B1, centralizerIn] using hbB1
    have hbcent : b ∈ Subgroup.centralizer ({c.t1} : Set G) := hbB1'.2
    have hcomm : c.t1 * b = b * c.t1 :=
      (Subgroup.mem_centralizer_iff).1 hbcent c.t1 (by simp)
    exact hcomm
  have hbt2 : Commute c.t2 b := by
    have hbB2 : b ∈ Hyp11.B2 c :=
      (inf_le_right : Hyp11.B1 c ⊓ Hyp11.B2 c ≤ Hyp11.B2 c) hbB
    have hbB2' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t2} : Set G) := by
      simpa [Hyp11.B2, centralizerIn] using hbB2
    have hbcent : b ∈ Subgroup.centralizer ({c.t2} : Set G) := hbB2'.2
    have hcomm : c.t2 * b = b * c.t2 :=
      (Subgroup.mem_centralizer_iff).1 hbcent c.t2 (by simp)
    exact hcomm
  have hbt1t2 : Commute (c.t1 * c.t2) b :=
    (Commute.mul_right hbt1.symm hbt2.symm).symm
  by_cases haS0 : (a : G) ∈ (c.S0 : Subgroup G)
  · rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using haS0)) with
      ⟨k, hk⟩
    have hk' : Commute ((c.t1 * c.t2) ^ k) b := hbt1t2.zpow_left k
    have hEq : (a : G) * b * (a : G)⁻¹ = b := by
      rw [← hk]
      rw [hk'.eq]
      group
    exact hEq
  · let aS : ↥(c.S : Subgroup G) := a
    let t1S : ↥(c.S : Subgroup G) := ⟨c.t1, c.t1_mem_S⟩
    have haS : aS ∉ (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G) := by
      exact fun h => haS0 (Subgroup.mem_subgroupOf.mp h)
    have ht1S : t1S ∉ (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G) := by
      exact fun h => c.t1_not_mem_S0 (Subgroup.mem_subgroupOf.mp h)
    have hmul : aS * t1S ∈ (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G) := by
      exact (Subgroup.mul_mem_iff_of_index_two (S0_index c)).2 (by simpa [haS, ht1S])
    have hrS0 : (a : G) * c.t1 ∈ (c.S0 : Subgroup G) := by
      simpa [aS, t1S, Subgroup.coe_mul] using (Subgroup.mem_subgroupOf.mp hmul)
    rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using hrS0)) with
      ⟨k, hk⟩
    have hbr : Commute ((a : G) * c.t1) b := by
      simpa [hk.symm] using hbt1t2.zpow_left k
    have hb_rt : Commute b ((a : G) * c.t1 * c.t1) :=
      Commute.mul_right hbr.symm hbt1.symm
    have ha_eq : (a : G) = (a : G) * c.t1 * c.t1 := by
      calc
        (a : G) = (a : G) * 1 := by simp
        _ = (a : G) * (c.t1 * c.t1) := by rw [← pow_two, c.t1_involution.2]
        _ = (a : G) * c.t1 * c.t1 := by group
    have hb_a : Commute b (a : G) := by
      simpa [ha_eq.symm] using hb_rt
    have hEq : (a : G) * b * (a : G)⁻¹ = b := by
      rw [hb_a.symm.eq]
      group
    exact hEq

/-- An element of `U` fixed by all of `S` lies in `B`. -/
public lemma mem_B_of_fixed_s4 (c : Hyp11 G) {b : ↥c.U}
    (hb : b ∈ fixedSubgroup (c.S : Subgroup G) c.U) :
    (b : G) ∈ c.B := by
  classical
  rw [mem_fixedSubgroup_iff] at hb
  have hb1 : (b : G) ∈ Hyp11.B1 c := by
    rw [Hyp11.B1, centralizerIn]
    constructor
    · exact b.2
    · change (b : G) ∈ Subgroup.centralizer ({c.t1} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have ht : h = c.t1 := by simpa using hh
      subst h
      have hfix := hb ⟨c.t1, c.t1_mem_S⟩
      have hcoef : (((⟨c.t1, c.t1_mem_S⟩ : ↥(c.S : Subgroup G)) • b : ↥c.U) : G) =
          c.t1 * (b : G) * c.t1⁻¹ := by
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      have hEq : c.t1 * (b : G) * c.t1⁻¹ = (b : G) := by
        simpa [hcoef] using congrArg Subtype.val hfix
      have hcomm : c.t1 * (b : G) = (b : G) * c.t1 := by
        calc
          c.t1 * (b : G) = (c.t1 * (b : G) * c.t1⁻¹) * c.t1 := by group
          _ = (b : G) * c.t1 := by rw [hEq]
      simpa using hcomm
  have hb2 : (b : G) ∈ Hyp11.B2 c := by
    rw [Hyp11.B2, centralizerIn]
    constructor
    · exact b.2
    · change (b : G) ∈ Subgroup.centralizer ({c.t2} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have ht : h = c.t2 := by simpa using hh
      subst h
      have hfix := hb ⟨c.t2, c.t2_mem_S⟩
      have hcoef : (((⟨c.t2, c.t2_mem_S⟩ : ↥(c.S : Subgroup G)) • b : ↥c.U) : G) =
          c.t2 * (b : G) * c.t2⁻¹ := by
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      have hEq : c.t2 * (b : G) * c.t2⁻¹ = (b : G) := by
        simpa [hcoef] using congrArg Subtype.val hfix
      have hcomm : c.t2 * (b : G) = (b : G) * c.t2 := by
        calc
          c.t2 * (b : G) = (c.t2 * (b : G) * c.t2⁻¹) * c.t2 := by group
          _ = (b : G) * c.t2 := by rw [hEq]
      simpa using hcomm
  rw [Hyp11.B]
  exact ⟨hb1, hb2⟩

/-- The subgroup equivalence `B ≃* C_U(S)`: elements of `B` are exactly the
`S`-fixed points of the conjugation action on `U`. -/
public noncomputable def B_fixedSubgroup_equiv (c : Hyp11 G) :
    ↥c.B ≃* fixedSubgroup (c.S : Subgroup G) c.U where
  toFun b :=
    ⟨⟨(b : G), mem_U_of_mem_B_s4 c b.2⟩, b_mem_fixedSubgroup_s4 c b.2⟩
  invFun u :=
    ⟨(((u : fixedSubgroup (c.S : Subgroup G) c.U) : ↥c.U) : G),
      mem_B_of_fixed_s4 c u.2⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' b b' := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-! ## The odd-order elements of `C_G(S)` are exactly `B` -/

/-- `U ≤ H`. -/
private lemma U_le_H_s4 (c : Hyp11 G) : c.U ≤ c.H := by
  intro x hx
  have huU : x ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hx
  exact SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU

/-- `|U|` is coprime to `2`. -/
public lemma U_coprime_two (c : Hyp11 G) : Nat.Coprime 2 (Nat.card (↥c.U)) := by
  have h1 : Nat.card (↥c.U) = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  rw [h1]
  exact pPrimeCore_coprime_card (p := 2) (G := c.H)

/-- `U ∩ S = 1`. -/
private lemma U_inter_S_eq_bot_s4 (c : Hyp11 G) {x : G} (hxU : x ∈ c.U)
    (hxS : x ∈ (c.S : Subgroup G)) : x = 1 := by
  classical
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := U_coprime_two c
  by_contra hx1
  have hordU : orderOf x ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨x, hxU⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨x, hxU⟩ : ↥c.U)]
    have hxU' : orderOf (⟨x, hxU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨x, hxU⟩)
    rwa [← Nat.card_eq_fintype_card] at hxU'
  have hordS : orderOf x ∣ Nat.card (c.S : Subgroup G) := by
    change orderOf ((c.S : Subgroup G).subtype (⟨x, hxS⟩ : ↥(c.S : Subgroup G))) ∣
      Nat.card (c.S : Subgroup G)
    rw [orderOf_injective (c.S : Subgroup G).subtype
      (Subgroup.subtype_injective (c.S : Subgroup G)) (⟨x, hxS⟩ : ↥(c.S : Subgroup G))]
    have hxS' : orderOf (⟨x, hxS⟩ : ↥(c.S : Subgroup G)) ∣
        Fintype.card ↥(c.S : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S : Subgroup G)) (x := ⟨x, hxS⟩)
    rwa [← Nat.card_eq_fintype_card] at hxS'
  have hpow : orderOf x ∣ 2 * 2 ^ c.m := by
    rw [← S_nat_card c]
    exact hordS
  have hpow' : orderOf x ∣ 2 ^ (c.m + 1) := by
    rw [pow_succ]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow
  have hcop' : Nat.Coprime (2 ^ (c.m + 1)) (Nat.card ↥c.U) := hcop.pow_left _
  have h1' : orderOf x = 1 := by
    have hdvd : orderOf x ∣ 1 := by
      rw [← hcop'.gcd_eq_one]
      exact Nat.dvd_gcd hpow' hordU
    exact Nat.dvd_one.mp hdvd
  exact hx1 (orderOf_eq_one_iff.mp h1')

/-- `H = U·S` as set products. -/
private lemma H_eq_U_mul_S_s4 (c : Hyp11 G) :
    (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
  rw [← c.H_eq_US]
  exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
    (S4_S_le_normalizer_U c)

/-- Uniqueness of the `U·K`-decomposition (`U ∩ K = 1`). -/
private lemma U_mul_K_decomp_unique_s4 (c : Hyp11 G) (K : Subgroup G)
    (hK : ∀ {x : G}, x ∈ c.U → x ∈ K → x = 1)
    {u₁ u₂ : ↥c.U} {s₁ s₂ : ↥K}
    (h : (u₁ : G) * (s₁ : G) = (u₂ : G) * (s₂ : G)) :
    u₁ = u₂ ∧ s₁ = s₂ := by
  have h1 : (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ = 1 := by
    calc
      (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ =
          (u₂ : G)⁻¹ * ((u₁ : G) * (s₁ : G)) * (s₂ : G)⁻¹ := by group
      _ = (u₂ : G)⁻¹ * ((u₂ : G) * (s₂ : G)) * (s₂ : G)⁻¹ := by rw [h]
      _ = 1 := by group
  have hU : (u₂ : G)⁻¹ * (u₁ : G) ∈ c.U := c.U.mul_mem (c.U.inv_mem u₂.2) u₁.2
  have hS : (s₂ : G) * (s₁ : G)⁻¹ ∈ K := K.mul_mem s₂.2 (K.inv_mem s₁.2)
  have hEq2 : (u₂ : G)⁻¹ * (u₁ : G) = (s₂ : G) * (s₁ : G)⁻¹ := by
    calc
      (u₂ : G)⁻¹ * (u₁ : G) =
          (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ * (s₂ : G) * (s₁ : G)⁻¹ := by group
      _ = 1 * (s₂ : G) * (s₁ : G)⁻¹ := by rw [h1]
      _ = (s₂ : G) * (s₁ : G)⁻¹ := by simp
  have hU2 : (u₂ : G)⁻¹ * (u₁ : G) ∈ K := by
    rw [hEq2]
    exact hS
  have h1' : (u₂ : G)⁻¹ * (u₁ : G) = 1 := hK hU hU2
  have hu12 : (u₁ : G) = (u₂ : G) := by
    calc
      (u₁ : G) = (u₂ : G) * ((u₂ : G)⁻¹ * (u₁ : G)) := by group
      _ = (u₂ : G) := by rw [h1']; simp
  constructor
  · apply Subtype.ext
    exact hu12
  · apply Subtype.ext
    calc
      (s₁ : G) = (u₁ : G)⁻¹ * ((u₁ : G) * (s₁ : G)) := by group
      _ = (u₂ : G)⁻¹ * ((u₂ : G) * (s₂ : G)) := by rw [h, hu12]
      _ = (s₂ : G) := by group

/-- The bijection `U × S ≃ H` (`H = U·S`, `U ∩ S = 1`). -/
private noncomputable def H_equiv_U_mul_S_s4 (c : Hyp11 G) :
    ↥c.U × ↥(c.S : Subgroup G) ≃ ↥c.H := by
  classical
  refine Equiv.ofBijective (fun p : ↥c.U × ↥(c.S : Subgroup G) =>
    ⟨(p.1 : G) * (p.2 : G), c.H.mul_mem (U_le_H_s4 c p.1.2) (S_le_H c p.2.2)⟩) ⟨?_, ?_⟩
  · intro p₁ p₂ h
    rcases U_mul_K_decomp_unique_s4 c (c.S : Subgroup G)
      (fun hxU hxK => U_inter_S_eq_bot_s4 c hxU hxK)
      (by exact congrArg (fun z : ↥c.H => (z : G)) h) with ⟨hu, hs⟩
    ext
    · exact congrArg (fun z : ↥c.U => (z : G)) hu
    · exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hs
  · intro x
    have hx : (x : G) ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
      rw [← H_eq_U_mul_S_s4 c]
      exact x.2
    rcases hx with ⟨u, hu, s, hs, hxeq⟩
    refine ⟨(⟨u, hu⟩, ⟨s, hs⟩), ?_⟩
    apply Subtype.ext
    exact hxeq

/-- `|H| = |U|·|S|`. -/
private lemma H_card_eq_s4 (c : Hyp11 G) :
    Nat.card (↥c.H) = Nat.card ↥c.U * Nat.card (c.S : Subgroup G) := by
  simpa [Nat.card_prod] using (Nat.card_congr (H_equiv_U_mul_S_s4 c).symm)

/-- An odd-order element of `H` lies in `U = O(H)` (the quotient
`H/U ≅ S` is a `2`-group). -/
private lemma odd_order_mem_U (c : Hyp11 G) {x : G} (hxH : x ∈ c.H)
    (hxodd : Odd (orderOf x)) : x ∈ c.U := by
  classical
  let K : Subgroup (↥c.H) := c.U.subgroupOf c.H
  have hUleH : c.U ≤ c.H := U_le_H_s4 c
  have : K.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUleH]
    intro h k hU kH
    exact U_normal_in_H c kH hU
  let q : ↥c.H →* (↥c.H ⧸ K) := QuotientGroup.mk' K
  let xH : ↥c.H := ⟨x, hxH⟩
  have hqodd : Odd (orderOf (q xH)) := by
    have hdvd : orderOf (q xH) ∣ orderOf xH := orderOf_map_dvd q xH
    have hxord : orderOf xH = orderOf x := by
      simpa [xH] using (orderOf_injective (c.H).subtype
        (Subgroup.subtype_injective c.H) xH)
    exact hxodd.of_dvd_nat (by simpa [hxord] using hdvd)
  have hKcard : Nat.card (↥K) = Nat.card ↥c.U := by
    exact Nat.card_congr {
      toFun := fun y : ↥K => ⟨(y : G), Subgroup.mem_subgroupOf.mp y.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), U_le_H_s4 c y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index K
  have hH' : Nat.card (↥K) * K.index = Nat.card (↥c.H) := hcm
  have hH'' : Nat.card ↥c.U * K.index = Nat.card (↥c.H) := by
    rwa [hKcard] at hH'
  have hKindex : K.index = Nat.card (c.S : Subgroup G) := by
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥c.U)) (by
      calc
        Nat.card ↥c.U * K.index = Nat.card (↥c.H) := hH''
        _ = Nat.card ↥c.U * Nat.card (c.S : Subgroup G) := H_card_eq_s4 c)
  have hquotCard : Nat.card (↥c.H ⧸ K) = Nat.card (c.S : Subgroup G) := by
    rw [← Subgroup.index_eq_card, hKindex]
  have hqpow : orderOf (q xH) ∣ Nat.card (c.S : Subgroup G) := by
    rw [← hquotCard]
    exact orderOf_dvd_natCard (q xH)
  have hS2 : Nat.Coprime (orderOf (q xH)) (Nat.card (c.S : Subgroup G)) := by
    have hcop2 : Nat.Coprime 2 (orderOf (q xH)) := by
      have hnot2 : ¬ 2 ∣ orderOf (q xH) := by
        rw [← even_iff_two_dvd]
        exact Nat.not_even_iff_odd.mpr hqodd
      exact Nat.prime_two.coprime_iff_not_dvd.mpr hnot2
    rcases IsPGroup.exists_card_eq (p := 2) (G := ↥(c.S : Subgroup G)) c.S.isPGroup'
      with ⟨k, hk⟩
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.Coprime.symm hcop2)
  have hq1 : orderOf (q xH) = 1 := Nat.Coprime.eq_one_of_dvd hS2 hqpow
  have hq : q xH = 1 := orderOf_eq_one_iff.mp hq1
  have hxK : xH ∈ K := by
    rw [← QuotientGroup.ker_mk' K]
    exact MonoidHom.mem_ker.mpr hq
  exact Subgroup.mem_subgroupOf.mp hxK

/-- Every element of `B` has odd order. -/
private lemma odd_order_of_mem_B (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) :
    Odd (orderOf b) := by
  classical
  have hbU : b ∈ c.U := mem_U_of_mem_B_s4 c hbB
  have hord : orderOf b ∣ Nat.card (↥c.U) := by
    change orderOf (c.U.subtype (⟨b, hbU⟩ : ↥c.U)) ∣ Nat.card (↥c.U)
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨b, hbU⟩ : ↥c.U)]
    have hbU' : orderOf (⟨b, hbU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨b, hbU⟩)
    rwa [← Nat.card_eq_fintype_card] at hbU'
  have hcop2 : Nat.Coprime 2 (orderOf b) :=
    Nat.Coprime.coprime_dvd_right hord (U_coprime_two c)
  exact Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact (Nat.prime_two.coprime_iff_not_dvd).mp hcop2)

/-! ## Fixed full `Λ`-orbits and the Section-4 `ν̂` input -/

/-- The `s`-conjugate of a `Λ`-character is again a `Λ`-character
(`s` normalizes `U`). -/
private def conjLambda_s4 (c : Hyp11 G) (h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) : LambdaHom c.H0 c.U := by
  classical
  refine ⟨l.1.comp (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)), ?_⟩
  intro u hu
  change l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) = 1
  exact l.2 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) (by
    change c.s * (u : G) * c.s⁻¹ ∈ c.U
    exact s_normalizes_U c hu)

/-- `s·(s·x·s⁻¹)·s⁻¹ = x` for the involution `s`. -/
private lemma s_conj_sq_s4 (c : Hyp11 G) (x : G) :
    c.s * (c.s * x * c.s⁻¹) * c.s⁻¹ = x := by
  have hs2 : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
  calc
    c.s * (c.s * x * c.s⁻¹) * c.s⁻¹ = (c.s * c.s) * x * (c.s⁻¹ * c.s⁻¹) := by group
    _ = x := by
      have hs2' : c.s⁻¹ * c.s⁻¹ = 1 := by
        rw [← mul_inv_rev]
        rw [hs2]
        simp
      rw [hs2, hs2']
      simp

/-- Conjugation by `s` is an involution on `H0`. -/
private lemma conjMonoidHom_conjMonoidHom_s4 (c : Hyp11 G) (h12 : Hyp12 c)
    (x : ↥c.H0) :
    (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
      (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) : ↥c.H0) = x := by
  apply Subtype.ext
  exact s_conj_sq_s4 c (x : G)

/-- Conjugation by `s` maps the orbit of `ν^s` into the orbit of `ν`:
`μ ∈ orbit(ν^s)` implies `μ^s ∈ orbit ν`. -/
private lemma orbit_conjChar_subset_s4 (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (μ : ClassFunction (↥c.H0))
    (hμ : μ ∈ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν)) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ ∈ orbit c.H0 c.U ν := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  refine Finset.mem_image.mpr ⟨conjLambda_s4 c h12 l, Finset.mem_univ _, ?_⟩
  ext x
  simp [conjChar, conjLambda_s4, LambdaChar]
  have hx : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x : ↥c.H0) =
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ := rfl
  rw [hx]
  have hx' : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ↥c.H0) = x := by
    apply Subtype.ext
    exact s_conj_sq_s4 c (x : G)
  rw [hx']

/-- `α` lies in its own `S0`-orbit. -/
private lemma s0Orbit_self_mem_s4 (c : Hyp11 G) (α : Irr (↥c.U)) :
    α ∈ s0Orbit c α := by
  refine Finset.mem_image.mpr ⟨(1 : ↥(c.S0 : Subgroup G)), Finset.mem_univ _, ?_⟩
  exact conjIrrS_one c α

/-- A class function lies in its own `Λ`-orbit. -/
private lemma orbit_self_mem_s4 (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : ClassFunction (↥c.H0)) :
    ν ∈ orbit c.H0 c.U ν := by
  classical
  refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
  have h1 : LambdaChar (1 : LambdaHom c.H0 c.U).1 = (1 : ClassFunction (↥c.H0)) := by
    ext x
    simp [LambdaChar]
  rw [h1, one_mul]

/-- A singleton `S0`-orbit is `{α}`. -/
private lemma s0Orbit_eq_singleton_of_card_one_s4 (c : Hyp11 G) (α : Irr (↥c.U))
    (hcard : (s0Orbit c α).card = 1) : s0Orbit c α = {α} := by
  classical
  rcases Finset.card_eq_one.mp hcard with ⟨β, hβ⟩
  have hαmem : α ∈ s0Orbit c α := s0Orbit_self_mem_s4 c α
  have hαβ : α = β := by
    rw [hβ] at hαmem
    simpa using hαmem
  rw [hβ, hαβ]

/-- In a singleton `S0`-orbit, the orbit sum is just `α`. -/
private lemma sum_s0Orbit_eq_α_of_card_one_s4 (c : Hyp11 G) (α : Irr (↥c.U))
    (hcard : (s0Orbit c α).card = 1) :
    (∑ α' ∈ s0Orbit c α, α'.1) = α.1 := by
  rw [s0Orbit_eq_singleton_of_card_one_s4 c α hcard]
  simp

/-- Evaluation of an `S`-conjugate character agrees with the action. -/
private lemma conjIrrS_eval_smul_s4 (c : Hyp11 G) {g : G}
    (hg : g ∈ (c.S : Subgroup G)) (α : Irr (↥c.U)) (u : ↥c.U) :
    (conjIrrS c hg α).1 u = α.1 ((⟨g, hg⟩ : ↥(c.S : Subgroup G)) • u) := by
  classical
  change α.1 ⟨g * (u : G) * g⁻¹, S_normalizes_U c g hg (u : G) u.2⟩ =
    α.1 ((⟨g, hg⟩ : ↥(c.S : Subgroup G)) • u)
  congr 1

/-- `|H0 : U| = |S0|` (the `H0 = U·S0` product decomposition). -/
private lemma U_index_eq_S0_card_s4 (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) := by
  classical
  let f : ↥c.U × ↥c.S0 → ↥c.H0 := fun p =>
    ⟨(p.1 : G) * (p.2 : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 p.1.2) (S0_le_H0 c p.2.2)⟩
  have hinj : Function.Injective f := by
    intro p q hEq
    have hEq' : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val hEq
    have h₁ : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G) = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hEq']
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hU : (q.1 : G)⁻¹ * (p.1 : G) ∈ c.U := (c.U).mul_mem ((c.U).inv_mem q.1.2) p.1.2
    have hS0 : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.S0 := (c.S0).mul_mem q.2.2 ((c.S0).inv_mem p.2.2)
    have honeU : (q.1 : G)⁻¹ * (p.1 : G) = 1 := U_inter_S0_eq_bot c hU (by
      rw [h₁]
      exact hS0)
    have hS0inU : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.U := by
      rw [← h₁]
      exact hU
    have honeS : (q.2 : G) * (p.2 : G)⁻¹ = 1 := U_inter_S0_eq_bot c hS0inU hS0
    apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel (a := (q.1 : G)⁻¹) (by
        calc
          (q.1 : G)⁻¹ * (p.1 : G) = 1 := honeU
          _ = (q.1 : G)⁻¹ * (q.1 : G) := by group)
    · apply Subtype.ext
      exact (calc
        (q.2 : G) = (q.2 : G) * (p.2 : G)⁻¹ * (p.2 : G) := by group
        _ = (p.2 : G) := by rw [honeS]; simp).symm
  have hsurj : ∀ x : ↥c.H0, ∃ p : ↥c.U × ↥c.S0, f p = x := by
    intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hEq⟩
    refine ⟨(u, r), ?_⟩
    apply Subtype.ext
    exact hEq.symm
  have hcardcong : Nat.card (↥c.H0) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by
    let e : ↥c.U × ↥c.S0 ≃ ↥c.H0 := Equiv.ofBijective f ⟨hinj, hsurj⟩
    have hc : Nat.card (↥c.U × ↥c.S0) = Nat.card (↥c.H0) := Nat.card_congr e
    rw [← hc]
    simp
  have hUcard : Nat.card (↥(c.U.subgroupOf c.H0)) = Nat.card (↥c.U) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.U.subgroupOf c.H0) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩,
        Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.U.subgroupOf c.H0)
  have h1 : (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    rw [← hUcard]
    rw [mul_comm]
    exact hcm
  have h2 : Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    calc
      Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by rw [mul_comm]
      _ = Nat.card (↥c.H0) := hcardcong.symm
  exact mul_right_cancel₀ (b := Nat.card (↥c.U)) (Nat.card_pos (α := ↥c.U)).ne' (by
    calc
      (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := h1
      _ = Nat.card (↥c.S0) * Nat.card (↥c.U) := h2.symm)

/-- A full fixed `Λ`-orbit restricts to an irreducible `α` fixed by all of
`S` (the Section-4 input for the Glauberman correspondence). -/
private lemma fixed_full_orbit_restrict_s4 (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {ν : Irr (↥c.H0)}
    (hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (horbit : (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index) :
    ∃ α : Irr (↥c.U),
      orbit c.H0 c.U ν.1 = orbitOfAlpha c h12 hSC α ∧
      restrictU c h12 ν.1 = α.1 ∧
      FixedIrr (c.S : Subgroup G) c.U α := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC ν with ⟨α, hOrbitEq⟩
  have hindex2 : 2 ≤ (c.U.subgroupOf c.H0).index := by
    rw [U_index_eq_S0_card_s4 c h12]
    rw [S0_nat_card c]
    have hpow : 2 ^ 1 ≤ 2 ^ c.m := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) c.one_le_m
    simpa using hpow
  have hmain : (c.U.subgroupOf c.H0).index =
      (c.U.subgroupOf c.H0).index / (s0Orbit c α).card := by
    rw [← orbitOfAlpha_card c h12 hSC α]
    simpa [hOrbitEq] using horbit.symm
  have hcardα : (s0Orbit c α).card = 1 := by
    have hnle : (s0Orbit c α).card ≤ 2 := (remark_3_1 c h12 hSC α).2.1
    have hnpos : 0 < (s0Orbit c α).card := Finset.card_pos.mpr ⟨α, s0Orbit_self_mem_s4 c α⟩
    by_cases hn1 : (s0Orbit c α).card = 1
    · exact hn1
    · have hn2 : (s0Orbit c α).card = 2 := by omega
      exfalso
      have hlt : (c.U.subgroupOf c.H0).index / 2 < (c.U.subgroupOf c.H0).index :=
        Nat.div_lt_self (by omega : 0 < (c.U.subgroupOf c.H0).index) (by norm_num : 1 < 2)
      rw [hn2] at hmain
      exact (not_lt_of_ge (by omega : (c.U.subgroupOf c.H0).index ≤
        (c.U.subgroupOf c.H0).index / 2)) hlt
  have hres : restrictU c h12 ν.1 = α.1 := by
    have hspec := (orbitOfAlpha_spec c h12 hSC α).2 ν.1 (by
      simpa [hOrbitEq] using orbit_self_mem_s4 c ν.1)
    rw [hspec, sum_s0Orbit_eq_α_of_card_one_s4 c α hcardα]
  have hfixorb : ∀ μ : ClassFunction (↥c.H0), μ ∈ orbitOfAlpha c h12 hSC α →
      conjChar c.H0 (s_normalizes_H0 c h12) μ ∈ orbitOfAlpha c h12 hSC α := by
    intro μ hμ
    have hμ' : μ ∈ orbit c.H0 c.U ν.1 := by simpa [hOrbitEq] using hμ
    rw [← hfix] at hμ'
    have hc := orbit_conjChar_subset_s4 c h12 μ hμ'
    simpa [hOrbitEq] using hc
  have hnotle : ¬ stabilizerS c α ≤ (c.S0 : Subgroup G) := by
    intro hle
    exact (orbitOfAlpha_fixed_iff c h12 hSC α).1 hfixorb hle
  have hstab : stabilizerS c α = (c.S : Subgroup G) := by
    rcases (stabilizerS_not_le_S0_iff c h12 hSC α).1 hnotle with h | h
    · exact h.2
    · exfalso
      omega
  have hfixIr : FixedIrr (c.S : Subgroup G) c.U α := by
    intro s
    funext u
    have hmem : (s : G) ∈ stabilizerS c α := by
      rw [hstab]
      exact s.2
    rcases hmem with ⟨hsS, hconj⟩
    have hsub : (⟨(s : G), hsS⟩ : ↥(c.S : Subgroup G)) = s := by
      apply Subtype.ext
      rfl
    have hconj' : conjIrrS c s.2 α = α := by
      simpa [hsub] using hconj
    have heq := congrFun (congrArg Subtype.val hconj') u
    rw [conjIrrS_eval_smul_s4 c s.2 α u] at heq
    exact heq
  exact ⟨α, hOrbitEq, hres, hfixIr⟩

/-- Under Section 4, a fixed `ν` with `ν(t) = ν(1)` has a full `Λ`-orbit. -/
private lemma section4_orbit_card_eq_index (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (_hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (_hνt : ν.1 (tH0 c) = ν.1 1) :
    (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index := by
  classical
  have hS0card : Nat.card (c.S0 : Subgroup G) = 2 := by
    have h4 : 2 * Nat.card (c.S0 : Subgroup G) = 4 := by
      rw [← c.S_index_two, hS4]
    omega
  have hS0pow : 2 ^ c.m = 2 := by
    rw [← S0_nat_card c, hS0card]
  have hsq : (c.t1 * c.t2) ^ 2 = 1 := by
    have h2 : (⟨c.t1 * c.t2, S0_generator_mem_S0 c⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 :=
      sq_eq_one_of_card_two hS0card _
    simpa [Subgroup.coe_pow] using congrArg Subtype.val h2
  have hSPbot : SPrime c = ⊥ := by
    unfold SPrime
    rw [hsq, Subgroup.zpowers_one_eq_bot]
  have hext : extensionSubgroup c = c.U := by
    unfold extensionSubgroup
    rw [hSPbot, bot_sup_eq]
  have htX : (tH0 c : G) ∉ extensionSubgroup c := by
    rw [hext]
    exact t_not_mem_U c
  have hlt : (lambdaTwo c h12).1 (tH0 c) = (-1 : ℂˣ) :=
    lambdaTwo_val_neg_one_of_not_mem_extensionSubgroup c h12 hSC (tH0 c) htX
  have hνt0 : ν.1 (tH0 c) ≠ 0 := char_apply_central_ne_zero
    (G := ↥c.H0) (t := tH0 c)
    (by simpa [tH0] using t_central_H0' c) (by simpa [tH0] using t_H0_sq c) ν.2
  have hlne : LambdaChar (lambdaTwo c h12).1 * ν.1 ≠ ν.1 := by
    intro hEq
    have hpt := congrFun hEq (tH0 c)
    have hpt' : ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) = ν.1 (tH0 c) := by
      simpa [LambdaChar] using hpt
    have hpt'' : ((lambdaTwo c h12).1 (tH0 c) : ℂ) * ν.1 (tH0 c) =
        1 * ν.1 (tH0 c) := by simpa using hpt'
    have hl1 : ((lambdaTwo c h12).1 (tH0 c) : ℂ) = 1 := mul_right_cancel₀ hνt0 hpt''
    have hlneg : ((lambdaTwo c h12).1 (tH0 c) : ℂ) = -1 :=
      congrArg (fun u : ℂˣ => (u : ℂ)) hlt
    have hbad : (1 : ℂ) = -1 := hl1.symm.trans hlneg
    norm_num at hbad
  have hLcard : Fintype.card (LambdaHom c.H0 c.U) = 2 := by
    have hNat : Nat.card (LambdaHom c.H0 c.U) = 2 := by
      rw [lambda_card_eq_index c h12, U_index_eq_S0_card_s4 c h12, hS0card]
    simpa [Nat.card_eq_fintype_card] using hNat
  have hLpair : ∀ l : LambdaHom c.H0 c.U, l = 1 ∨ l = lambdaTwo c h12 := by
    have hsub : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) ⊆ Finset.univ := by
      intro x hx
      simp
    have hEq : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_univ, hLcard]
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      · intro h
        exact lambdaTwo_ne_one c h12 (Finset.mem_singleton.mp h).symm
    intro l
    have hl : l ∈ Finset.univ := Finset.mem_univ l
    rw [← hEq] at hl
    simpa using hl
  have hstabcard : (Finset.univ.filter
      (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1)).card = 1 := by
    have hstab_le : (Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1)) ⊆
        ({1} : Finset (LambdaHom c.H0 c.U)) := by
      intro l hl
      have hlmem := (Finset.mem_filter.mp hl).1
      have hlfix := (Finset.mem_filter.mp hl).2
      rcases hLpair l with hl1 | hl2
      · rw [Finset.mem_singleton]
        exact hl1
      · exfalso
        exact hlne (by simpa [hl2] using hlfix)
    have hmem1 : (1 : LambdaHom c.H0 c.U) ∈ Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1) :=
      one_mem_stab c.H0 c.U ν.1
    have hsub1 : ({1} : Finset (LambdaHom c.H0 c.U)) ⊆ Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1) := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      exact hmem1
    have hEq : (Finset.univ.filter
        (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν.1 = ν.1)) =
        ({1} : Finset (LambdaHom c.H0 c.U)) :=
      Finset.eq_of_subset_of_card_le hstab_le (Finset.card_le_card hsub1)
    rw [hEq]
    simp
  have hmul := orbit_card_mul_stab c.H0 c.U ν.1
  rw [hstabcard, hLcard] at hmul
  have horbit : (orbit c.H0 c.U ν.1).card = 2 := by
    norm_num at hmul
    exact hmul
  rw [U_index_eq_S0_card_s4 c h12, hS0card]
  exact horbit

/-- For Section-4 `ν` (fixed by `s` and with `ν(t) = ν(1)`), the
correspondence input exists: an irreducible restriction to `U` fixed by all
of `S`. -/
public theorem exists_fixed_alpha_of_section4 (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) :
    ∃ α : Irr (↥c.U),
      FixedIrr (c.S : Subgroup G) c.U α ∧ restrictU c h12 ν.1 = α.1 := by
  classical
  rcases fixed_full_orbit_restrict_s4 c h12 hSC hνs
    (section4_orbit_card_eq_index c h12 hSC hS4 hνs hνt) with ⟨α, _hOrbit, hres, hfix⟩
  exact ⟨α, hfix, hres⟩

/-! ## The Glauberman correspondence and `ν̂` -/

/-- The irreducible characters are invariant under group isomorphism
(local copy: `Lemma19.irrCongr` is not reducible under `module`
transparency). -/
private noncomputable def irrCongr_s4 {G H : Type u} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : H ≃* G) : IrrBG19 G ≃ IrrBG19 H where
  toFun α := ⟨fun h : H => α.1 (e h), isIrreducibleCharacter_congr e α.2⟩
  invFun β := ⟨fun g : G => β.1 (e.symm g), isIrreducibleCharacter_congr e.symm β.2⟩
  left_inv α := by
    apply Subtype.ext
    funext g
    change α.1 (e (e.symm g)) = α.1 g
    rw [e.apply_symm_apply]
  right_inv β := by
    apply Subtype.ext
    funext h
    change β.1 (e.symm (e h)) = β.1 h
    rw [e.symm_apply_apply]

/-- The Glauberman correspondence for `S` acting on `U` by conjugation,
transported from `C_U(S)` to the Section-4 subgroup `B`. -/
private noncomputable def glaubermanEquiv (c : Hyp11 G) :
    {α : IrrBG19 (↥c.U) // FixedIrr (c.S : Subgroup G) c.U α} ≃
      IrrBG19 (↥c.B) := by
  classical
  let e0 := Classical.choose (glauberman_correspondence
    (S := ↥(c.S : Subgroup G)) (U := ↥c.U)
    c.S.isPGroup' (U_coprime_two c))
  exact e0.trans (irrCongr_s4 (B_fixedSubgroup_equiv c))

/-- The transported correspondence is congruent to `α` on `B`. -/
private theorem glaubermanEquiv_congr (c : Hyp11 G)
    (α : IrrBG19 (↥c.U)) (hfix : FixedIrr (c.S : Subgroup G) c.U α)
    (b : ↥c.B) :
    CongruentModTwo
      (α.1 ((B_fixedSubgroup_equiv c b :
          fixedSubgroup (c.S : Subgroup G) c.U) : ↥c.U))
      ((glaubermanEquiv c ⟨α, hfix⟩).1 b) := by
  classical
  let e0 := Classical.choose (glauberman_correspondence
    (S := ↥(c.S : Subgroup G)) (U := ↥c.U)
    c.S.isPGroup' (U_coprime_two c))
  have hspec : ∀ (α' : {α : IrrBG19 (↥c.U) // FixedIrr (c.S : Subgroup G) c.U α})
      (b' : ↥(fixedSubgroup (c.S : Subgroup G) c.U)),
      CongruentModTwo (α'.1.1 (b' : ↥c.U)) ((e0 α').1 b') :=
    Classical.choose_spec (glauberman_correspondence
      (S := ↥(c.S : Subgroup G)) (U := ↥c.U)
      c.S.isPGroup' (U_coprime_two c))
  have h := hspec ⟨α, hfix⟩ (B_fixedSubgroup_equiv c b)
  simpa [glaubermanEquiv, e0, irrCongr_s4] using h

/-- `ν̂`: the irreducible character of `B` satisfying `ν̂ ≡ ν` on `B`, for
`ν = ν^s ∈ Irr(H0)` with `ν(t) = ν(1)` (Lemma 1.9, the Glauberman
correspondence; the defining congruence is `nuHat_congruence`).  When the
required fixed irreducible restriction is not inhabited, the trivial
irreducible character is returned. -/
public noncomputable def nuHat (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) : Irr (↥c.B) := by
  classical
  let P : Prop := ∃ α : Irr (↥c.U),
    FixedIrr (c.S : Subgroup G) c.U α ∧ restrictU c h12 ν.1 = α.1
  if h : P then
    let α : IrrBG19 (↥c.U) := Classical.choose h
    exact glaubermanEquiv c ⟨α, (Classical.choose_spec h).1⟩
  else
    exact trivialIrr (↥c.B)

/-- `ν̂ ≡ ν` on `B`: for Section-4 `ν` (`ν^s = ν`, `ν(t) = ν(1)`), the
character `ν̂` of `B` satisfies `ν̂ ≡ ν (mod 2)` on `B` (Lemma 1.9).  This
is the corrected statement: the old wrapper statement omitted both
`Section3Hyp` and the section-wide `Section4Hyp`; the latter is essential
because it is the input that makes the restriction of `ν` to `U` an
`S`-fixed irreducible. -/
public theorem nuHat_congruence (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) :
    ∀ b : ↥c.B, (hb : (b : G) ∈ c.H0) →
      CongruentModTwo ((nuHat c h12 ν).1 b) (ν.1 ⟨(b : G), hb⟩) := by
  classical
  intro b hb
  rcases exists_fixed_alpha_of_section4 c h12 hSC hS4 hνs hνt with ⟨α, hfix, hres⟩
  let P : Prop := ∃ α0 : Irr (↥c.U),
    FixedIrr (c.S : Subgroup G) c.U α0 ∧ restrictU c h12 ν.1 = α0.1
  have hP : P := ⟨α, hfix, hres⟩
  let α0 : IrrBG19 (↥c.U) := Classical.choose hP
  have hfix0 : FixedIrr (c.S : Subgroup G) c.U α0 := (Classical.choose_spec hP).1
  have hres0 : restrictU c h12 ν.1 = α0.1 := (Classical.choose_spec hP).2
  have hC := glaubermanEquiv_congr c α0 hfix0 b
  let u : ↥c.U := ((B_fixedSubgroup_equiv c b :
      fixedSubgroup (c.S : Subgroup G) c.U) : ↥c.U)
  have hEq1 : α0.1 u = ν.1 ⟨(b : G), hb⟩ := by
    have hAt := congrFun hres0 u
    change ν.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ = α0.1 u at hAt
    have hu : (u : G) = (b : G) := rfl
    have hsub : (⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ : ↥c.H0) = ⟨(b : G), hb⟩ := by
      apply Subtype.ext
      exact hu
    rw [hAt.symm, hsub]
  have hnu : (nuHat c h12 ν).1 b = (glaubermanEquiv c ⟨α0, hfix0⟩).1 b := by
    unfold nuHat
    rw [dif_pos hP]
  have hC' : CongruentModTwo (α0.1 u) ((nuHat c h12 ν).1 b) := by
    rwa [← hnu] at hC
  exact (CongruentModTwo.symm hC').trans (CongruentModTwo.of_eq hEq1)

/-- An element of `G` centralizing `S` and of odd order lies in `B`. -/
private lemma mem_B_of_centralizes_S_and_odd_order (c : Hyp11 G) {x : G}
    (hxS : ∀ s : G, s ∈ (c.S : Subgroup G) → x * s = s * x)
    (hxodd : Odd (orderOf x)) : x ∈ c.B := by
  have hxH : x ∈ c.H := by
    rw [c.H_eq_centralizer]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzS : z = c.t := by simpa using hz
    rw [hzS]
    exact (hxS c.t (c.S0_le_S c.t_mem_S0)).symm
  have hxU : x ∈ c.U := odd_order_mem_U c hxH hxodd
  have hb1 : x ∈ Hyp11.B1 c := by
    rw [Hyp11.B1, centralizerIn]
    constructor
    · exact hxU
    · change x ∈ Subgroup.centralizer ({c.t1} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzS : z = c.t1 := by simpa using hz
      rw [hzS]
      exact (hxS c.t1 c.t1_mem_S).symm
  have hb2 : x ∈ Hyp11.B2 c := by
    rw [Hyp11.B2, centralizerIn]
    constructor
    · exact hxU
    · change x ∈ Subgroup.centralizer ({c.t2} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzS : z = c.t2 := by simpa using hz
      rw [hzS]
      exact (hxS c.t2 c.t2_mem_S).symm
  rw [Hyp11.B]
  exact ⟨hb1, hb2⟩

/-- `N_G(S)`: the normalizer of the Sylow `2`-subgroup `S` in `G`. -/
public def normalizerS (c : Hyp11 G) : Subgroup G :=
  Subgroup.normalizer ((c.S : Subgroup G) : Set G)

/-- Elements of `N_G(B)` conjugate `B` to itself. -/
public theorem B_conj_mem_of_normalizer (c : Hyp11 G) {g : G} (hg : g ∈ normalizerB c) :
    ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B := by
  intro b
  exact (Subgroup.mem_normalizer_iff.mp (by simpa [normalizerB] using hg) (b : G)).1 b.2

/-- Elements of `N_G(S)` conjugate `B` to itself.  The transport is not
literal conjugation of `U`: an `N_G(S)`-element may permute the three
involutions of `S`, so the proof instead shows `g·b·g⁻¹` still centralizes
`S` and still has odd order, and that those two conditions characterize `B`. -/
public theorem B_conj_mem_of_normalizerS (c : Hyp11 G) {g : G} (hg : g ∈ normalizerS c) :
    ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B := by
  intro b
  have hbodd : Odd (orderOf (b : G)) := odd_order_of_mem_B c b.2
  have hord : Odd (orderOf (g * (b : G) * g⁻¹)) := by
    rwa [orderOf_conj_eq g (b : G)]
  have hbs (s0 : ↥(c.S : Subgroup G)) :
      (s0 : G) * (b : G) * (s0 : G)⁻¹ = (b : G) := by
    have hsmul := congrArg Subtype.val
      ((mem_fixedSubgroup_iff (c.S : Subgroup G) c.U
        (⟨(b : G), mem_U_of_mem_B_s4 c b.2⟩ : ↥c.U)).1
          (b_mem_fixedSubgroup_s4 c b.2) s0)
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at hsmul
    exact hsmul
  have hcent : ∀ s : G, s ∈ (c.S : Subgroup G) →
      (g * (b : G) * g⁻¹) * s = s * (g * (b : G) * g⁻¹) := by
    intro s hs
    have hginv : g⁻¹ ∈ normalizerS c := (normalizerS c).inv_mem hg
    have hgs : g⁻¹ * s * g ∈ (c.S : Subgroup G) := by
      have h0 : g⁻¹ * s * (g⁻¹)⁻¹ ∈ (c.S : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp
        (by simpa [normalizerS] using hginv) s).1 hs
      have hgi : (g⁻¹)⁻¹ = g := by simp
      rwa [hgi] at h0
    have hbs' : (g⁻¹ * s * g) * (b : G) * (g⁻¹ * s * g)⁻¹ = (b : G) :=
      hbs ⟨g⁻¹ * s * g, hgs⟩
    have hrb : (g⁻¹ * s * g) * (b : G) = (b : G) * (g⁻¹ * s * g) := by
      calc
        (g⁻¹ * s * g) * (b : G)
            = (g⁻¹ * s * g) * (b : G) * (g⁻¹ * s * g)⁻¹ * (g⁻¹ * s * g) := by group
        _ = (b : G) * (g⁻¹ * s * g) := by rw [hbs']
    calc
      (g * (b : G) * g⁻¹) * s = g * ((b : G) * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s * g) * (b : G)) * g⁻¹ := by rw [hrb]
      _ = s * (g * (b : G) * g⁻¹) := by group
  exact mem_B_of_centralizes_S_and_odd_order c hcent hord

/-! ## Conjugation of irreducible characters of `B` -/

/-- The `g`-conjugate of `β ∈ Irr(B)` for `g` conjugating `B` to itself:
`β^g(b) = β(g·b·g⁻¹)` (same convention as `conjChar`). -/
@[expose]
public noncomputable def conjIrrB (c : Hyp11 G) {g : G}
    (hg : ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B)
    (β : Irr (↥c.B)) : Irr (↥c.B) :=
  let f : ↥c.B →* ↥c.B :=
    { toFun := fun b : ↥c.B => ⟨g * (b : G) * g⁻¹, hg b⟩
      map_one' := by
        apply Subtype.ext
        change g * (1 : G) * g⁻¹ = 1
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        change g * ((a : G) * (b : G)) * g⁻¹ =
          (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
        group }
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    change g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ at h'
    calc
      (a : G) = g⁻¹ * (g * (a : G) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (b : G) * g⁻¹) * g := by rw [h']
      _ = (b : G) := by group
  have hbij : Function.Bijective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, rfl⟩
  let e : ↥c.B ≃* ↥c.B := MulEquiv.ofBijective f hbij
  ⟨fun b : ↥c.B => β.1 ⟨g * (b : G) * g⁻¹, hg b⟩,
    isIrreducibleCharacter_congr (e := e) β.2⟩

/-! ## The graph `Δ` and the set `B′(χ)` -/

/-- `B′(χ)`: the set of all such `ν` with `(χ, δν)_G ≠ 0`, i.e. the set of
`ν ∈ Irr(H0)` with `ν^s = ν`, `ν(t) = ν(1)` and `(χ, δν)_G ≠ 0`. -/
public noncomputable def BPrimeOf (c : Hyp11 G) (h12 : Hyp12 c)
    (χ : ClassFunction G) : Finset (Irr (↥c.H0)) := by
  classical
  exact Finset.univ.filter (fun ν : Irr (↥c.H0) =>
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧ ν.1 (tH0 c) = ν.1 1 ∧
      scalarProduct G χ (deltaNu c h12 ν) ≠ 0)

/-- `Δ`: the set of all `δν` for `ν ∈ Irr(H0)` with `ν^s = ν` and
`ν(t) = ν(1)`. -/
@[expose] public noncomputable def Delta (c : Hyp11 G) (h12 : Hyp12 c) :
    Set (ClassFunction G) :=
  {δ : ClassFunction G | ∃ ν : Irr (↥c.H0),
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧ ν.1 (tH0 c) = ν.1 1 ∧
      δ = deltaNu c h12 ν}

/-- Two vertices of `Δ` are adjacent in the graph `Δ` when they are distinct
and not disjoint (hence having exactly two or four irreducible characters of
`G` in common).  The endpoint conditions make this the induced graph on
`Delta`; without them the connected-component maximality condition below
would quantify over unrelated class functions outside the graph. -/
@[expose] public def deltaAdjacent (c : Hyp11 G) (h12 : Hyp12 c)
    (δ1 δ2 : ClassFunction G) : Prop :=
  δ1 ∈ Delta c h12 ∧ δ2 ∈ Delta c h12 ∧
    δ1 ≠ δ2 ∧ ¬ Theory.Character.Disjoint δ1 δ2

/-- `Δ0` is a connected component of the graph `Δ` (minimal modeling of the
paper's notion): a nonempty subset of `Δ` in which any two vertices are
joined by a chain of adjacent vertices, and no vertex outside `Δ0` is
adjacent to a vertex inside it (maximality). -/
@[expose] public def IsConnectedComponent (c : Hyp11 G) (h12 : Hyp12 c)
    (Δ0 : Set (ClassFunction G)) : Prop :=
  Δ0.Nonempty ∧ Δ0 ⊆ Delta c h12 ∧
    (∀ δ1 δ2 : ClassFunction G, δ1 ∈ Δ0 → δ2 ∈ Δ0 →
      Relation.ReflTransGen (deltaAdjacent c h12) δ1 δ2) ∧
    (∀ δ : ClassFunction G, δ ∉ Δ0 → ∀ δ0 : ClassFunction G, δ0 ∈ Δ0 →
      ¬ deltaAdjacent c h12 δ δ0)

/-- The set `{ν̂ | ν ∈ A}`: the Glauberman-correspondence characters of `B`
corresponding to the members of the finset `A ⊆ Irr(H0)`. -/
public noncomputable def nuHatImage (c : Hyp11 G) (h12 : Hyp12 c)
    (A : Finset (Irr (↥c.H0))) : Set (Irr (↥c.B)) :=
  {β : Irr (↥c.B) | ∃ ν : Irr (↥c.H0), ν ∈ A ∧ β = nuHat c h12 ν}

end Section4

end CFSG.BenderGlauberman
