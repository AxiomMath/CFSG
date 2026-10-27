module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunctionProduct

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 3 — shared infrastructure

The definitions and foundational group-theoretic helpers of Section 3
(the case `|S0 : C_{S0}(U)| ≤ 2`): `Section3Hyp`, `S_normalizes_U`,
`conjIrrS` (the `S`-conjugates of `α ∈ Irr(U)`), `s0Orbit` (the
`S0`-conjugates), `stabilizerS` (`S_α`), `restrictU`, `charKernel` (the
kernel of a character), and `normalizerB` (`G1 = N_G(B)`).
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

section Section3

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- The hypothesis of Section 3 of the paper: `S'`, the subgroup of index
`2` in `S0`, centralizes `U`. -/
@[expose] public def Section3Hyp (c : Hyp11 G) : Prop :=
  Centralizes (SPrime c) c.U

/-- Every element of `S` normalizes `U` (`S ≤ H` and `U = O(H)` is
characteristic in `H`). -/
public theorem S_normalizes_U (c : Hyp11 G) (g : G) (hg : g ∈ (c.S : Subgroup G))
    (u : G) (hu : u ∈ c.U) : g * u * g⁻¹ ∈ c.U := by
  have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hu
  have huH : u ∈ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
  have hgH : g ∈ c.H := S_le_H c hg
  have hchar : (pPrimeCore 2 c.H).Characteristic :=
    pPrimeCore_characteristic (p := 2) (G := c.H)
  have hcomap : (pPrimeCore 2 c.H) ≤ (pPrimeCore 2 c.H).comap
      (MulAut.conj ⟨g, hgH⟩).toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) (MulAut.conj ⟨g, hgH⟩)
  have huK : (⟨u, huH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
    rcases (Subgroup.mem_map.mp huU) with ⟨x, hx, hxeq⟩
    have hxeq' : (⟨u, huH⟩ : ↥c.H) = x := by
      ext
      simpa using hxeq.symm
    simpa [hxeq'] using hx
  have hconj : (MulAut.conj ⟨g, hgH⟩) ⟨u, huH⟩ ∈ pPrimeCore 2 c.H :=
    Subgroup.mem_comap.mp (hcomap huK)
  refine (Subgroup.mem_map.mpr ?_)
  refine ⟨⟨g * u * g⁻¹, c.H.mul_mem (c.H.mul_mem hgH huH) (c.H.inv_mem hgH)⟩, ?_, rfl⟩
  have hcx : (MulAut.conj ⟨g, hgH⟩) ⟨u, huH⟩ =
      (⟨g * u * g⁻¹, c.H.mul_mem (c.H.mul_mem hgH huH) (c.H.inv_mem hgH)⟩ : ↥c.H) := by
    ext
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hcx]
  exact hconj

/-- The `g`-conjugate of `α ∈ Irr(U)` for `g ∈ S` (an element of
`Irr(U)` again). -/
@[expose] public def conjIrrS (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G))
    (α : Irr (↥c.U)) : Irr (↥c.U) :=
  ⟨conjChar c.U (fun x : ↥c.U => S_normalizes_U c g hg x.1 x.2) α.1, by
    exact isIrreducibleCharacter_conjChar c.U (s := g)
      (fun x : ↥c.U => S_normalizes_U c g hg x.1 x.2)
      (fun x : ↥c.U => by
        simpa using S_normalizes_U c g⁻¹ ((c.S : Subgroup G).inv_mem hg) x.1 x.2)
      α.2⟩

/-- Conjugation by `a·b` is conjugation by `a` after conjugation by `b`. -/
public lemma conjIrrS_mul (c : Hyp11 G) {a b : G} (ha : a ∈ (c.S : Subgroup G))
    (hb : b ∈ (c.S : Subgroup G)) (α : Irr (↥c.U)) :
    conjIrrS c ((c.S : Subgroup G).mul_mem ha hb) α = conjIrrS c hb (conjIrrS c ha α) := by
  ext x
  simp only [conjIrrS, conjChar, conjMonoidHom]
  change α.1 ⟨(a * b) * (x : G) * (a * b)⁻¹, _⟩ =
    α.1 ⟨a * (b * (x : G) * b⁻¹) * a⁻¹, _⟩
  apply congrArg α.1
  apply Subtype.ext
  group

/-- Conjugation by `g⁻¹` undoes conjugation by `g`. -/
public lemma conjIrrS_inv (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G))
    (α : Irr (↥c.U)) :
    conjIrrS c ((c.S : Subgroup G).inv_mem hg) (conjIrrS c hg α) = α := by
  ext x
  simp only [conjIrrS, conjChar, conjMonoidHom]
  change α.1 ⟨g * (g⁻¹ * (x : G) * (g⁻¹)⁻¹) * g⁻¹, _⟩ = α.1 x
  apply congrArg α.1
  apply Subtype.ext
  group

/-- The `S0`-conjugates of `α ∈ Irr(U)` as a finset of distinct characters:
the paper's `α1, …, αn`. -/
@[expose] public noncomputable def s0Orbit (c : Hyp11 G) (α : Irr (↥c.U)) : Finset (Irr (↥c.U)) := by
  classical
  exact Finset.univ.image (fun g : ↥(c.S0 : Subgroup G) => conjIrrS c (c.S0_le_S g.2) α)

/-- `S_α`: the subgroup of elements of `S` fixing `α ∈ Irr(U)`, as a
subgroup of `G`. -/
@[expose] public def stabilizerS (c : Hyp11 G) (α : Irr (↥c.U)) : Subgroup G where
  carrier := {g : G | ∃ hg : g ∈ (c.S : Subgroup G), conjIrrS c hg α = α}
  one_mem' := by
    refine ⟨(c.S : Subgroup G).one_mem, ?_⟩
    ext x
    simp only [conjIrrS, conjChar, conjMonoidHom]
    change α.1 ⟨1 * (x : G) * 1⁻¹, _⟩ = α.1 x
    apply congrArg α.1
    apply Subtype.ext
    group
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨haS, hafix⟩
    rcases hb with ⟨hbS, hbfix⟩
    refine ⟨(c.S : Subgroup G).mul_mem haS hbS, ?_⟩
    rw [conjIrrS_mul c haS hbS α]
    rw [hafix, hbfix]
  inv_mem' := by
    intro g hg
    rcases hg with ⟨hgS, hgfix⟩
    refine ⟨(c.S : Subgroup G).inv_mem hgS, ?_⟩
    have h := conjIrrS_inv c hgS α
    rw [hgfix] at h
    exact h

/-- The restriction of a character of `H0` to `U`: the paper's `μ|_U`. -/
@[expose] public def restrictU (c : Hyp11 G) (h12 : Hyp12 c) (μ : ClassFunction (↥c.H0)) :
    ClassFunction (↥c.U) :=
  fun u : ↥c.U => μ ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩

/-- The kernel of a character: the subgroup of elements on which a
representation affording the character acts trivially. -/
@[expose] public noncomputable def charKernel {G : Type u} [Group G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) : Subgroup G :=
  (Classical.choose (Classical.choose_spec hχ)).ker

/-- `G1 = N_G(B)`, the normalizer of `B` in `G`. -/
@[expose] public def normalizerB (c : Hyp11 G) : Subgroup G :=
  Subgroup.normalizer ((c.B : Subgroup G) : Set G)

/-- `U ≤ H0 = U·S0`. -/
public lemma U_le_H0 (c : Hyp11 G) : c.U ≤ c.H0 := by
  exact le_sup_left

/-- `S' ≤ H0 = U·S0`. -/
public lemma SPrime_le_H0 (c : Hyp11 G) : SPrime c ≤ c.H0 := by
  exact le_trans (SPrime_le_S0 c) (S0_le_H0 c)

/-- `X := S'·U ≤ H0`: the subgroup of `H0` generated by `S'` and `U`, which
is the direct product `S' × U` under the Section 3 hypothesis. -/
public lemma SPrimeMulU_le_H0 (c : Hyp11 G) : SPrime c ⊔ c.U ≤ c.H0 := by
  exact sup_le (SPrime_le_H0 c) (U_le_H0 c)

/-- `U ⊴ X := S'·U` (conjugation by `S'` is trivial on `U`). -/
public lemma U_normal_in_SPrimeMulU (c : Hyp11 G) (hSC : Section3Hyp c) :
    IsNormalIn c.U (SPrime c ⊔ c.U) := by
  constructor
  · exact le_sup_right
  · intro x hx u hu
    have hSPN : SPrime c ≤ Subgroup.normalizer ((c.U : Subgroup G) : Set G) := by
      exact le_trans hSC (Subgroup.centralizer_le_normalizer ((c.U : Subgroup G) : Set G))
    have hUN : c.U ≤ Subgroup.normalizer ((c.U : Subgroup G) : Set G) :=
      Subgroup.le_normalizer
    have hxN : x ∈ Subgroup.normalizer ((c.U : Subgroup G) : Set G) :=
      (sup_le hSPN hUN) hx
    exact ((Subgroup.mem_normalizer_iff.mp hxN) u).1 hu

/-- `S' ∩ U = 1`. -/
public lemma SPrime_inter_U_eq_bot (c : Hyp11 G) : SPrime c ⊓ c.U = ⊥ := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    rcases (Subgroup.mem_inf.mp hx) with ⟨hxSP, hxU⟩
    have hx1 : x = 1 := U_inter_S0_eq_bot c hxU (SPrime_le_S0 c hxSP)
    simp [hx1]
  · intro hx
    have hx1 : x = 1 := (Subgroup.mem_bot.mp hx)
    simp [hx1]

/-- `X = S'·U`: the subgroup of `H0` generated by `S'` and `U` (a direct
product `S' × U` under the Section 3 hypothesis). -/
@[expose] public def extensionSubgroup (c : Hyp11 G) : Subgroup G :=
  SPrime c ⊔ c.U

/-- `S' ≤ N_G(U)` (from `S'` centralizes `U`). -/
public lemma SPrime_le_normalizer_U (c : Hyp11 G) (hSC : Section3Hyp c) :
    SPrime c ≤ Subgroup.normalizer ((c.U : Subgroup G) : Set G) := by
  exact le_trans hSC (Subgroup.centralizer_le_normalizer ((c.U : Subgroup G) : Set G))

/-- The carrier of `X = S'·U` is the product set `S'·U`. -/
public lemma extensionSubgroup_carrier_eq_mul (c : Hyp11 G) (hSC : Section3Hyp c) :
    ((extensionSubgroup c : Subgroup G) : Set G) =
      (SPrime c : Set G) * (c.U : Set G) := by
  unfold extensionSubgroup
  exact Subgroup.coe_mul_of_left_le_normalizer_right (SPrime c) c.U
    (SPrime_le_normalizer_U c hSC)

/-- Every element of `X = S'·U` decomposes uniquely as `u·s'` with
`u ∈ U`, `s' ∈ S'`. -/
public lemma exists_decomp (c : Hyp11 G) (hSC : Section3Hyp c) (x : ↥(extensionSubgroup c)) :
    ∃ p : ↥c.U × ↥(SPrime c), (x : G) = (p.1 : G) * (p.2 : G) := by
  classical
  have hx : (x : G) ∈ (SPrime c : Set G) * (c.U : Set G) := by
    rw [← extensionSubgroup_carrier_eq_mul c hSC]
    exact x.2
  rcases (Set.mem_mul.mp hx) with ⟨s', hs', u, hu, hxeq⟩
  have hcomm : (u : G) * s' = s' * (u : G) := by
    have hc : s' ∈ Subgroup.centralizer ((c.U : Subgroup G) : Set G) := hSC hs'
    exact (Subgroup.mem_centralizer_iff.mp hc) u hu
  refine ⟨⟨⟨u, hu⟩, ⟨s', hs'⟩⟩, ?_⟩
  rw [← hxeq]
  exact hcomm.symm

/-- Uniqueness of the decomposition of `X = S'·U` into `U`- and `S'`-parts. -/
public lemma decomp_unique (c : Hyp11 G) {u u' : ↥c.U} {s s' : ↥(SPrime c)}
    (h : (u : G) * (s : G) = (u' : G) * (s' : G)) :
    u = u' ∧ s = s' := by
  have hmemS : (s : G) * (s' : G)⁻¹ ∈ SPrime c :=
    (SPrime c).mul_mem s.2 ((SPrime c).inv_mem s'.2)
  have hmemU : (s : G) * (s' : G)⁻¹ ∈ c.U := by
    have huu : (u : G)⁻¹ * (u' : G) ∈ c.U := (c.U).mul_mem ((c.U).inv_mem u.2) u'.2
    have hEq : (s : G) * (s' : G)⁻¹ = (u : G)⁻¹ * (u' : G) := by
      calc
        (s : G) * (s' : G)⁻¹ = (u : G)⁻¹ * ((u : G) * (s : G)) * (s' : G)⁻¹ := by group
        _ = (u : G)⁻¹ * ((u' : G) * (s' : G)) * (s' : G)⁻¹ := by rw [h]
        _ = (u : G)⁻¹ * (u' : G) := by group
    rw [hEq]
    exact huu
  have h1 : (s : G) * (s' : G)⁻¹ = 1 :=
    U_inter_S0_eq_bot c hmemU (SPrime_le_S0 c hmemS)
  have hss' : s = s' := by
    apply Subtype.ext
    calc
      (s : G) = (s : G) * ((s' : G)⁻¹ * (s' : G)) := by group
      _ = ((s : G) * (s' : G)⁻¹) * (s' : G) := by rw [mul_assoc]
      _ = 1 * (s' : G) := by rw [h1]
      _ = (s' : G) := by simp
  have huu' : u = u' := by
    apply Subtype.ext
    have hEq : (u : G) * (s : G) = (u' : G) * (s : G) := by simpa [hss'] using h
    exact mul_right_cancel hEq
  exact ⟨huu', hss'⟩

/-- The natural generator `r0 = t1·t2` of the cyclic group `S0`. -/
@[expose] public def S0_generator (c : Hyp11 G) : G := c.t1 * c.t2

/-- The generator `r0 = t1·t2` lies in `S0` (which is `⟨r0⟩`). -/
public lemma S0_generator_mem_S0 (c : Hyp11 G) : S0_generator c ∈ (c.S0 : Subgroup G) := by
  rw [c.S0_eq_zpowers]
  exact Subgroup.mem_zpowers (S0_generator c)

/-- The generator `r0 = t1·t2` has order `2^m = |S0|`. -/
public lemma S0_generator_orderOf (c : Hyp11 G) : orderOf (S0_generator c) = 2 ^ c.m := by
  have hc : Nat.card (Subgroup.zpowers (S0_generator c) : Subgroup G) = 2 ^ c.m := by
    dsimp [S0_generator]
    rw [← c.S0_eq_zpowers]
    exact S0_nat_card c
  rw [← Nat.card_zpowers]
  exact hc

/-- The generator `r0 = t1·t2` lies in `H0`. -/
public lemma S0_generator_mem_H0 (c : Hyp11 G) : S0_generator c ∈ c.H0 := by
  exact S0_le_H0 c (S0_generator_mem_S0 c)

/-- The generator `r0 = t1·t2` is not in `S'` (`S' = ⟨r0²⟩` has index `2` in
`S0 = ⟨r0⟩`). -/
public lemma S0_generator_not_mem_SPrime (c : Hyp11 G) : S0_generator c ∉ SPrime c := by
  simpa [S0_generator] using t1t2_not_mem_SPrime c

/-- The generator `r0 = t1·t2` is not in `X = S'·U`. -/
public lemma S0_generator_not_mem_extensionSubgroup (c : Hyp11 G) (hSC : Section3Hyp c) :
    S0_generator c ∉ extensionSubgroup c := by
  intro h
  rcases (exists_decomp c hSC ⟨S0_generator c, h⟩) with ⟨p, hp⟩
  have hmemU : (S0_generator c) * (p.2 : G)⁻¹ ∈ c.U := by
    have hEq : (S0_generator c) * (p.2 : G)⁻¹ = (p.1 : G) := by
      calc
        (S0_generator c) * (p.2 : G)⁻¹ = ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by rw [← hp]
        _ = (p.1 : G) := by group
    rw [hEq]
    exact p.1.2
  have hmemS0 : (S0_generator c) * (p.2 : G)⁻¹ ∈ (c.S0 : Subgroup G) :=
    (c.S0 : Subgroup G).mul_mem (S0_generator_mem_S0 c)
      ((c.S0 : Subgroup G).inv_mem (SPrime_le_S0 c p.2.2))
  have h1 : (S0_generator c) * (p.2 : G)⁻¹ = 1 := U_inter_S0_eq_bot c hmemU hmemS0
  have hrsp : (S0_generator c) = (p.2 : G) := by
    calc
      (S0_generator c) = (S0_generator c) * ((p.2 : G)⁻¹ * (p.2 : G)) := by group
      _ = ((S0_generator c) * (p.2 : G)⁻¹) * (p.2 : G) := by rw [mul_assoc]
      _ = 1 * (p.2 : G) := by rw [h1]
      _ = (p.2 : G) := by simp
  exact S0_generator_not_mem_SPrime c (by
    rw [hrsp]
    exact p.2.2)

/-- Conjugation by the generator `r0 = t1·t2` preserves `X = S'·U`
(`r0` normalizes `U` as an element of `S`, and commutes with every element of
`S' ≤ S0` since `S0` is cyclic). -/
public lemma S0_generator_normalizes_extensionSubgroup (c : Hyp11 G) (hSC : Section3Hyp c) :
    ∀ x : ↥(extensionSubgroup c),
      (S0_generator c) * (x : G) * (S0_generator c)⁻¹ ∈ extensionSubgroup c := by
  intro x
  rcases (exists_decomp c hSC x) with ⟨p, hp⟩
  have hU : (S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹ ∈ c.U := by
    exact S_normalizes_U c (S0_generator c)
      (c.S0_le_S (S0_generator_mem_S0 c)) (p.1 : G) p.1.2
  have hS : (S0_generator c) * (p.2 : G) * (S0_generator c)⁻¹ ∈ SPrime c := by
    have hrS0 : S0_generator c ∈ (c.S0 : Subgroup G) := S0_generator_mem_S0 c
    have hpS0 : (p.2 : G) ∈ (c.S0 : Subgroup G) := SPrime_le_S0 c p.2.2
    let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
    have hc : (S0_generator c) * (p.2 : G) = (p.2 : G) * (S0_generator c) := by
      simpa using congrArg (fun y : ↥(c.S0 : Subgroup G) => (y : G))
        (mul_comm' (⟨S0_generator c, hrS0⟩ : ↥(c.S0 : Subgroup G)) ⟨(p.2 : G), hpS0⟩)
    have hcomm : (S0_generator c) * (p.2 : G) * (S0_generator c)⁻¹ = (p.2 : G) := by
      rw [hc]
      group
    rw [hcomm]
    exact p.2.2
  have hx' : (S0_generator c) * (x : G) * (S0_generator c)⁻¹ =
      ((S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹) *
        ((S0_generator c) * (p.2 : G) * (S0_generator c)⁻¹) := by
    rw [hp]
    group
  rw [hx']
  exact (extensionSubgroup c).mul_mem
    (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) hU)
    (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) hS)

/-- Every element of `S0` lies in `S'` or in `r0·S'` (since `S0 = ⟨r0⟩` and
`S' = ⟨r0²⟩` has index `2`). -/
public lemma S0_mem_SPrime_or_r0_mul (c : Hyp11 G) {g : G} (hg : g ∈ (c.S0 : Subgroup G)) :
    g ∈ SPrime c ∨ (S0_generator c) * g ∈ SPrime c := by
  by_cases hgSP : g ∈ SPrime c
  · exact Or.inl hgSP
  · right
    let a : ↥(c.S0 : Subgroup G) := ⟨S0_generator c, S0_generator_mem_S0 c⟩
    let b : ↥(c.S0 : Subgroup G) := ⟨g, hg⟩
    have hindex : ((SPrime c).subgroupOf (c.S0 : Subgroup G)).index = 2 := SPrime_index c
    have hiff := Subgroup.mul_mem_iff_of_index_two hindex (a := a) (b := b)
    have hr0 : (a : ↥(c.S0 : Subgroup G)) ∉ (SPrime c).subgroupOf (c.S0 : Subgroup G) := by
      intro h
      exact S0_generator_not_mem_SPrime c (Subgroup.mem_subgroupOf.mp h)
    have hb : (b : ↥(c.S0 : Subgroup G)) ∉ (SPrime c).subgroupOf (c.S0 : Subgroup G) := by
      intro h
      exact hgSP (Subgroup.mem_subgroupOf.mp h)
    have hab : a * b ∈ (SPrime c).subgroupOf (c.S0 : Subgroup G) :=
      hiff.mpr (by simpa [hr0, hb])
    exact (Subgroup.mem_subgroupOf.mp hab)

/-- `X = S'·U` has index `2` in `H0 = U·S0` (the two cosets are `X` and
`r0·X`). -/
public lemma extensionSubgroup_index_two (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) : ((extensionSubgroup c).subgroupOf c.H0).index = 2 := by
  classical
  have hrel : (SPrime c).relIndex (c.S0 : Subgroup G) = 2 := by
    simpa [Subgroup.relIndex] using SPrime_index c
  rcases (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hrel) with
    ⟨a, haS0, haSP, hall⟩
  have hrelX : (extensionSubgroup c).relIndex c.H0 = 2 := by
    refine (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mpr
      ⟨a, S0_le_H0 c haS0, ?_, ?_⟩)
    · intro haX
      rcases (exists_decomp c hSC ⟨a, haX⟩) with ⟨p, hp⟩
      have hmemS0 : (p.1 : G) ∈ (c.S0 : Subgroup G) := by
        have hEq : (p.1 : G) = a * (p.2 : G)⁻¹ := by
          calc
            (p.1 : G) = (p.1 : G) * ((p.2 : G) * (p.2 : G)⁻¹) := by group
            _ = ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by rw [mul_assoc]
            _ = a * (p.2 : G)⁻¹ := by rw [← hp]
        rw [hEq]
        exact (c.S0 : Subgroup G).mul_mem haS0
          ((c.S0 : Subgroup G).inv_mem (SPrime_le_S0 c p.2.2))
      have h1 : (p.1 : G) = 1 := U_inter_S0_eq_bot c p.1.2 hmemS0
      have haEq : a = (p.2 : G) := by
        calc
          a = (p.1 : G) * (p.2 : G) := hp
          _ = 1 * (p.2 : G) := by rw [h1]
          _ = (p.2 : G) := by simp
      exact haSP (by
        rw [haEq]
        exact p.2.2)
    · intro b hbH0
      rcases (H0_eq_U_mul_S0 c h12 (x := ⟨b, hbH0⟩)) with ⟨u, r, hbEq⟩
      have hbEq' : b = (u : G) * (r : G) := by
        simpa [Subtype.coe_mk] using hbEq
      rcases (hall (r : G) r.2) with harSP | hrSP
      · left
        have haU : a * (u : G) * a⁻¹ ∈ c.U :=
          S_normalizes_U c a (c.S0_le_S haS0) (u : G) u.2
        have hEq : a * b = (a * (u : G) * a⁻¹) * (a * (r : G)) := by
          rw [hbEq']
          group
        rw [hEq]
        exact (extensionSubgroup c).mul_mem
          (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) haU)
          (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) harSP)
      · right
        rw [hbEq']
        exact (extensionSubgroup c).mul_mem
          (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2)
          (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) hrSP)
  simpa [Subgroup.relIndex] using hrelX

/-- `X = S'·U ≃ U × S'` (a direct product, since `S'` centralizes `U`). -/
public noncomputable def extensionEquiv (c : Hyp11 G) (hSC : Section3Hyp c) :
    ↥(extensionSubgroup c) ≃* (↥c.U × ↥(SPrime c)) := by
  classical
  refine
    { toFun := fun x =>
        let p := Classical.choose (exists_decomp c hSC x)
        ⟨p.1, p.2⟩
      invFun := fun p => ⟨(p.1 : G) * (p.2 : G),
        (extensionSubgroup c).mul_mem
          (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) p.1.2)
          (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) p.2.2)⟩
      left_inv := by
        intro x
        let p := Classical.choose (exists_decomp c hSC x)
        have hx : (x : G) = (p.1 : G) * (p.2 : G) :=
          Classical.choose_spec (exists_decomp c hSC x)
        apply Subtype.ext
        simpa using hx.symm
      right_inv := by
        intro p
        let p' := Classical.choose (exists_decomp c hSC
          (⟨(p.1 : G) * (p.2 : G),
            (extensionSubgroup c).mul_mem
              (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) p.1.2)
              (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) p.2.2)⟩ :
              ↥(extensionSubgroup c)))
        have hx : ((p.1 : G) * (p.2 : G)) = (p'.1 : G) * (p'.2 : G) :=
          Classical.choose_spec (exists_decomp c hSC
            (⟨(p.1 : G) * (p.2 : G),
              (extensionSubgroup c).mul_mem
                (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) p.1.2)
                (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) p.2.2)⟩ :
                ↥(extensionSubgroup c)))
        have hdecomp : (p'.1 : G) * (p'.2 : G) = (p.1 : G) * (p.2 : G) := hx.symm
        have hunique := decomp_unique c hdecomp
        rcases hunique with ⟨hu, hs⟩
        change (p'.1, p'.2) = p
        ext
        · simpa using hu
        · simpa using hs
      map_mul' := by
        intro x y
        let pxy := Classical.choose (exists_decomp c hSC (x * y))
        let px := Classical.choose (exists_decomp c hSC x)
        let py := Classical.choose (exists_decomp c hSC y)
        have hxy : ((x * y : ↥(extensionSubgroup c)) : G) =
            (pxy.1 : G) * (pxy.2 : G) :=
          Classical.choose_spec (exists_decomp c hSC (x * y))
        have hx : (x : G) = (px.1 : G) * (px.2 : G) :=
          Classical.choose_spec (exists_decomp c hSC x)
        have hy : (y : G) = (py.1 : G) * (py.2 : G) :=
          Classical.choose_spec (exists_decomp c hSC y)
        have hcomm : (py.1 : G) * (px.2 : G) = (px.2 : G) * (py.1 : G) := by
          have hc : (px.2 : G) ∈ Subgroup.centralizer ((c.U : Subgroup G) : Set G) :=
            hSC px.2.2
          exact (Subgroup.mem_centralizer_iff.mp hc) py.1 py.1.2
        have hEq : ((x * y : ↥(extensionSubgroup c)) : G) =
            (px.1 : G) * (py.1 : G) * (px.2 : G) * (py.2 : G) := by
          calc
            ((x * y : ↥(extensionSubgroup c)) : G) = (x : G) * (y : G) := rfl
            _ = (px.1 : G) * (px.2 : G) * (py.1 : G) * (py.2 : G) := by
              rw [hx, hy]
              group
            _ = (px.1 : G) * (py.1 : G) * (px.2 : G) * (py.2 : G) := by
              calc
                (px.1 : G) * (px.2 : G) * (py.1 : G) * (py.2 : G)
                    = (px.1 : G) * ((px.2 : G) * (py.1 : G)) * (py.2 : G) := by group
                _ = (px.1 : G) * ((py.1 : G) * (px.2 : G)) * (py.2 : G) := by rw [hcomm]
                _ = (px.1 : G) * (py.1 : G) * (px.2 : G) * (py.2 : G) := by group
        have hEq2 : (pxy.1 : G) * (pxy.2 : G) =
            (px.1 * py.1 : G) * (px.2 * py.2 : G) := by
          calc
            (pxy.1 : G) * (pxy.2 : G) = ((x * y : ↥(extensionSubgroup c)) : G) := hxy.symm
            _ = (px.1 : G) * (py.1 : G) * (px.2 : G) * (py.2 : G) := hEq
            _ = (px.1 * py.1 : G) * (px.2 * py.2 : G) := by
              group
        have hunique := decomp_unique c (u := pxy.1) (s := pxy.2)
          (u' := px.1 * py.1) (s' := px.2 * py.2) hEq2
        change (pxy.1, pxy.2) = (px.1 * py.1, px.2 * py.2)
        exact Prod.ext hunique.1 hunique.2 }

/-- The extension of `α ∈ Irr(U)` by the linear character `lam` of `S'` to
`X = S'·U`: `x ↦ α(u)·lam(s')` for `x = u·s'`. -/
public noncomputable def extensionChar (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    ClassFunction (↥(extensionSubgroup c)) :=
  fun x => α.1 ((extensionEquiv c hSC x).1) * ((lam ((extensionEquiv c hSC x).2) : ℂˣ) : ℂ)

/-- `extensionChar` is a character of `X` (a product of the pullbacks of `α`
and `lam` along `X ≃ U × S'`). -/
public lemma extensionChar_isCharacter (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    IsCharacter (extensionChar c hSC α lam) := by
  classical
  let P : ↥c.U × ↥(SPrime c) → ℂ := fun p => α.1 p.1 * ((lam p.2 : ℂˣ) : ℂ)
  have hαc : IsCharacter (fun p : ↥c.U × ↥(SPrime c) => α.1 p.1) := by
    rcases α.2 with ⟨n, ρ, hρ, hαeq⟩
    refine ⟨n, ρ.comp (MonoidHom.fst (↥c.U) (↥(SPrime c))), ?_⟩
    ext p
    rw [hαeq]
    rfl
  have hlamc : IsLinearCharacter (fun p : ↥c.U × ↥(SPrime c) => ((lam p.2 : ℂˣ) : ℂ)) := by
    exact isLinearCharacter_of_hom (lam.comp (MonoidHom.snd (↥c.U) (↥(SPrime c))))
  have hP' : IsCharacter ((fun p : ↥c.U × ↥(SPrime c) => ((lam p.2 : ℂˣ) : ℂ)) *
      (fun p : ↥c.U × ↥(SPrime c) => α.1 p.1)) := by
    exact isCharacter_mul_linear hlamc hαc
  have hP : IsCharacter P := by
    convert hP' using 1
    ext p
    simp [P, mul_comm]
  rcases hP with ⟨n, ρ, hρeq⟩
  refine ⟨n, ρ.comp (extensionEquiv c hSC), ?_⟩
  ext x
  change extensionChar c hSC α lam x = ρ.character (extensionEquiv c hSC x)
  have hx : P (extensionEquiv c hSC x) = ρ.character (extensionEquiv c hSC x) :=
    congrFun hρeq (extensionEquiv c hSC x)
  rw [show extensionChar c hSC α lam x = P (extensionEquiv c hSC x) by
    simp [extensionChar, P]]
  exact hx

/-- Every extension of an irreducible character of `U` to `X = S'·U` is
irreducible (norm-one via the product scalar-product factorization). -/
public lemma extensionChar_isIrreducible (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    IsIrreducibleCharacter (extensionChar c hSC α lam) := by
  refine isIrreducibleCharacter_of_norm_one_inv
    (extensionChar_isCharacter c hSC α lam) ?_
  calc
    scalarProductInv (↥(extensionSubgroup c)) (extensionChar c hSC α lam)
        (extensionChar c hSC α lam)
        = scalarProductInv (↥c.U × ↥(SPrime c))
            (fun p : ↥c.U × ↥(SPrime c) => α.1 p.1 * ((lam p.2 : ℂˣ) : ℂ))
            (fun p : ↥c.U × ↥(SPrime c) => α.1 p.1 * ((lam p.2 : ℂˣ) : ℂ)) := by
            rw [scalarProductInv_congr (e := extensionEquiv c hSC)
              (φ := extensionChar c hSC α lam) (ψ := extensionChar c hSC α lam)]
            congr 1 <;> ext p <;> simp [extensionChar]
    _ = scalarProductInv (↥c.U) α.1 α.1 *
        scalarProductInv (↥(SPrime c)) (fun s : ↥(SPrime c) => ((lam s : ℂˣ) : ℂ))
          (fun s : ↥(SPrime c) => ((lam s : ℂˣ) : ℂ)) := by
            simpa using (scalarProductInv_prod_mul (α := α.1)
              (β := fun s : ↥(SPrime c) => ((lam s : ℂˣ) : ℂ)))
    _ = 1 := by
            rw [isIrreducible_norm_inv_one α.2]
            rw [isIrreducible_norm_inv_one (isLinearCharacter_of_hom lam).1]
            norm_num

/-- `extensionChar` restricts to `α` on `U`. -/
public lemma extensionChar_restrict (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    ∀ u : ↥c.U, extensionChar c hSC α lam
      ⟨(u : G), SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩ = α.1 u := by
  intro u
  let x : ↥(extensionSubgroup c) :=
    ⟨(u : G), SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩
  let p := Classical.choose (exists_decomp c hSC x)
  have hx : (x : G) = (p.1 : G) * (p.2 : G) := Classical.choose_spec (exists_decomp c hSC x)
  have hunique := decomp_unique c (u := p.1) (s := p.2) (u' := u) (s' := 1) (by
    calc
      (p.1 : G) * (p.2 : G) = (x : G) := hx.symm
      _ = (u : G) := rfl
      _ = (u : G) * (1 : G) := by simp)
  have heq : extensionEquiv c hSC x = (⟨u, (1 : ↥(SPrime c))⟩ : ↥c.U × ↥(SPrime c)) := by
    change (p.1, p.2) = (⟨u, (1 : ↥(SPrime c))⟩ : ↥c.U × ↥(SPrime c))
    exact Prod.ext hunique.1 hunique.2
  rw [extensionChar, heq]
  simp

/-- Every irreducible character of `X = S'·U` is an extension of some
`α ∈ Irr(U)` (via the direct-product factorization `X ≃ U × S'` and the
linearity of irreducible characters of the cyclic group `S'`). -/
public theorem exists_extensionChar_of_isIrreducible (c : Hyp11 G) (hSC : Section3Hyp c)
    {ξ : ClassFunction (↥(extensionSubgroup c))} (hξ : IsIrreducibleCharacter ξ) :
    ∃ α : Irr (↥c.U), ∃ lam : ↥(SPrime c) →* ℂˣ,
      ξ = extensionChar c hSC α lam := by
  classical
  let e : ↥(extensionSubgroup c) ≃* ↥c.U × ↥(SPrime c) := extensionEquiv c hSC
  let φ : ClassFunction (↥c.U × ↥(SPrime c)) := fun p => ξ (e.symm p)
  have hφ : IsIrreducibleCharacter φ :=
    isIrreducibleCharacter_congr (e := e.symm) (χ := ξ) hξ
  rcases irreducibleCharacter_eq_prodChar φ hφ with ⟨α, ψ, hprod⟩
  let : IsCyclic ↥(SPrime c) := by
    change IsCyclic ↥(Subgroup.zpowers ((c.t1 * c.t2) ^ 2))
    infer_instance
  have hlin : IsLinearCharacter ψ.1 :=
    isLinearCharacter_of_isIrreducible_of_isCyclic ψ.2
  let lam : ↥(SPrime c) →* ℂˣ := linearCharHom hlin
  refine ⟨α, lam, ?_⟩
  ext x
  have hx : ξ x = α.1 (e x).1 * ψ.1 (e x).2 := by
    have hc := congrFun hprod (e x)
    change prodChar α.1 ψ.1 (e x) = ξ (e.symm (e x)) at hc
    simpa [prodChar] using hc.symm
  rw [extensionChar]
  change ξ x = α.1 (e x).1 * ((lam ((e x).2) : ℂˣ) : ℂ)
  rw [linearCharHom_apply hlin ((e x).2)]
  exact hx

/-- The restriction of an irreducible character of `X = S'·U` to `U` is an
irreducible character of `U`. -/
public theorem exists_irr_restrict_of_isIrreducible (c : Hyp11 G) (hSC : Section3Hyp c)
    {ξ : ClassFunction (↥(extensionSubgroup c))} (hξ : IsIrreducibleCharacter ξ) :
    ∃ α : Irr (↥c.U), ∀ u : ↥c.U,
      ξ ⟨(u : G), SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩ =
        α.1 u := by
  rcases exists_extensionChar_of_isIrreducible c hSC hξ with ⟨α, lam, hEq⟩
  refine ⟨α, ?_⟩
  intro u
  rw [hEq]
  simpa using extensionChar_restrict c hSC α lam u

/-- The induction of `extensionChar` from `X = S'·U` to `H0`: the paper's
`α̂^{H0}`. -/
@[expose] public noncomputable def extensionChar_ind (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    ClassFunction (↥c.H0) :=
  inducedFromSub (SPrimeMulU_le_H0 c) (extensionChar c hSC α lam)

/-- `Ind_X^{H0}(α̂)` is a character of `H0` (index-two induction). -/
public lemma extensionChar_ind_isCharacter (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    IsCharacter (extensionChar_ind c hSC α lam) := by
  unfold extensionChar_ind
  exact isCharacter_ind_index_two (extensionSubgroup c) c.H0
    (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
    (s := S0_generator c) (S0_generator_mem_H0 c)
    (S0_generator_not_mem_extensionSubgroup c hSC)
    (extensionChar_isIrreducible c hSC α lam)
    (S0_generator_normalizes_extensionSubgroup c hSC)

/-- The restriction of `Ind_X^{H0}(α̂)` to `U` is `α + α^r0`: over the two
cosets of `X` in `H0` (representative `r0 = t1·t2`), the induced value at
`u ∈ U` is `α(u) + α(r0·u·r0⁻¹)`. -/
public lemma extensionChar_ind_restrict (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    restrictU c h12 (extensionChar_ind c hSC α lam) =
      fun u : ↥c.U =>
        α.1 u + α.1 ⟨(S0_generator c) * (u : G) * (S0_generator c)⁻¹,
          S_normalizes_U c (S0_generator c) (c.S0_le_S (S0_generator_mem_S0 c)) (u : G) u.2⟩ := by
  ext u
  classical
  have huX : (u : G) ∈ extensionSubgroup c :=
    SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2
  let hx : ↥(extensionSubgroup c) := ⟨(u : G), huX⟩
  have hsh : (S0_generator c) * (u : G) * (S0_generator c)⁻¹ ∈ extensionSubgroup c :=
    S0_generator_normalizes_extensionSubgroup c hSC hx
  have hmain := inducedFromSub_eq_add_conj_index_two (extensionSubgroup c) c.H0
    (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
    (s := S0_generator c) (S0_generator_mem_H0 c)
    (S0_generator_not_mem_extensionSubgroup c hSC)
    (extensionChar c hSC α lam)
    (isCharacter_isClassFunction (extensionChar_isCharacter c hSC α lam)) huX hsh
  have hUu : (S0_generator c) * (u : G) * (S0_generator c)⁻¹ ∈ c.U :=
    S_normalizes_U c (S0_generator c) (c.S0_le_S (S0_generator_mem_S0 c)) (u : G) u.2
  have hν1 : extensionChar c hSC α lam ⟨(u : G), huX⟩ = α.1 u := by
    exact extensionChar_restrict c hSC α lam u
  have hν2 : extensionChar c hSC α lam
      ⟨(S0_generator c) * (u : G) * (S0_generator c)⁻¹, hsh⟩ =
      α.1 ⟨(S0_generator c) * (u : G) * (S0_generator c)⁻¹, hUu⟩ := by
    have hEqX : (⟨(S0_generator c) * (u : G) * (S0_generator c)⁻¹, hsh⟩ :
          ↥(extensionSubgroup c)) =
        ⟨(S0_generator c) * (u : G) * (S0_generator c)⁻¹,
          SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) hUu⟩ := by
      apply Subtype.ext
      rfl
    rw [hEqX]
    exact extensionChar_restrict c hSC α lam
      ⟨(S0_generator c) * (u : G) * (S0_generator c)⁻¹, hUu⟩
  change @inducedFromSub G _ _ (extensionSubgroup c) c.H0 (SPrimeMulU_le_H0 c)
      (extensionChar c hSC α lam) ⟨(u : G), SPrimeMulU_le_H0 c huX⟩ =
    α.1 u + α.1 ⟨(S0_generator c) * (u : G) * (S0_generator c)⁻¹, hUu⟩
  rw [hmain, hν1, hν2]

/-- Evaluating `extensionChar` at the explicit product `u·s'` gives
`α(u)·lam(s')`. -/
public lemma extensionChar_mul (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) (u : ↥c.U) (s' : ↥(SPrime c)) :
    extensionChar c hSC α lam ⟨(u : G) * (s' : G),
      (extensionSubgroup c).mul_mem
        (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2)
        (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s'.2)⟩ =
      α.1 u * ((lam s' : ℂˣ) : ℂ) := by
  classical
  let x : ↥(extensionSubgroup c) := ⟨(u : G) * (s' : G),
    (extensionSubgroup c).mul_mem
      (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2)
      (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s'.2)⟩
  let p := Classical.choose (exists_decomp c hSC x)
  have hx : (x : G) = (p.1 : G) * (p.2 : G) := Classical.choose_spec (exists_decomp c hSC x)
  have hunique := decomp_unique c (u := p.1) (s := p.2) (u' := u) (s' := s') (by
    calc
      (p.1 : G) * (p.2 : G) = (x : G) := hx.symm
      _ = (u : G) * (s' : G) := rfl)
  have heq : extensionEquiv c hSC x = (⟨u, s'⟩ : ↥c.U × ↥(SPrime c)) := by
    change (p.1, p.2) = (⟨u, s'⟩ : ↥c.U × ↥(SPrime c))
    exact Prod.ext hunique.1 hunique.2
  rw [extensionChar, heq]

/-- The map `α ↦ extensionChar α lam` is injective (restriction to `U`
recovers `α`). -/
public lemma extensionChar_injective (c : Hyp11 G) (hSC : Section3Hyp c)
    {α β : Irr (↥c.U)} (lam : ↥(SPrime c) →* ℂˣ)
    (h : extensionChar c hSC α lam = extensionChar c hSC β lam) : α = β := by
  apply Subtype.ext
  funext u
  have h1 := congrFun h
    ⟨(u : G), SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩
  rw [← extensionChar_restrict c hSC α lam u, h1, extensionChar_restrict c hSC β lam u]

/-- For fixed `α`, the map `lam ↦ extensionChar α lam` is injective
(evaluate at `S'` and cancel the nonzero degree `α(1)`). -/
public lemma extensionChar_lam_injective (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) {lam lam' : ↥(SPrime c) →* ℂˣ}
    (h : extensionChar c hSC α lam = extensionChar c hSC α lam') : lam = lam' := by
  apply MonoidHom.ext
  intro s
  apply Units.ext
  have h1 := congrFun h ⟨(s : G),
    SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2⟩
  have hL : extensionChar c hSC α lam ⟨(s : G),
      SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2⟩ =
      α.1 1 * ((lam s : ℂˣ) : ℂ) := by
    simpa using extensionChar_mul c hSC α lam (1 : ↥c.U) s
  have hR : extensionChar c hSC α lam' ⟨(s : G),
      SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2⟩ =
      α.1 1 * ((lam' s : ℂˣ) : ℂ) := by
    simpa using extensionChar_mul c hSC α lam' (1 : ↥c.U) s
  have hcast : ((lam s : ℂˣ) : ℂ) = ((lam' s : ℂˣ) : ℂ) := by
    rw [hL, hR] at h1
    exact mul_left_cancel₀ (irreducible_char_one_ne_zero α.2) h1
  simpa using hcast

/-- Extensions of distinct characters of `U` are distinct (restriction to `U`
recovers the character). -/
public lemma extensionChar_ne_of_ne_alpha (c : Hyp11 G) (hSC : Section3Hyp c)
    {α β : Irr (↥c.U)} (hαβ : α ≠ β)
    (lam lam' : ↥(SPrime c) →* ℂˣ) :
    extensionChar c hSC α lam ≠ extensionChar c hSC β lam' := by
  intro hEq
  apply hαβ
  apply Subtype.ext
  funext u
  have h1 := congrFun hEq ⟨(u : G),
    SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩
  simpa [extensionChar_restrict c hSC α lam u, extensionChar_restrict c hSC β lam' u] using h1

/-- Conjugation by `r0 = t1·t2` sends the extension of `α` by `lam` to the
extension of the `r0`-conjugate of `α` by the same `lam`. -/
public lemma extensionChar_conj_r0 (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) :
    conjChar (extensionSubgroup c) (s := S0_generator c)
      (S0_generator_normalizes_extensionSubgroup c hSC)
      (extensionChar c hSC α lam) =
    extensionChar c hSC (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) lam := by
  ext x
  rcases (exists_decomp c hSC x) with ⟨p, hp⟩
  have hU : (S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹ ∈ c.U :=
    S_normalizes_U c (S0_generator c) (c.S0_le_S (S0_generator_mem_S0 c)) (p.1 : G) p.1.2
  have hcommS : (S0_generator c) * (p.2 : G) = (p.2 : G) * (S0_generator c) := by
    have hrS0 : S0_generator c ∈ (c.S0 : Subgroup G) := S0_generator_mem_S0 c
    have hpS0 : (p.2 : G) ∈ (c.S0 : Subgroup G) := SPrime_le_S0 c p.2.2
    let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
    simpa using congrArg (fun y : ↥(c.S0 : Subgroup G) => (y : G))
      (mul_comm' (⟨S0_generator c, hrS0⟩ : ↥(c.S0 : Subgroup G)) ⟨(p.2 : G), hpS0⟩)
  have hEq : (S0_generator c) * (x : G) * (S0_generator c)⁻¹ =
      ((S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹) * (p.2 : G) := by
    rw [hp]
    calc
      (S0_generator c) * ((p.1 : G) * (p.2 : G)) * (S0_generator c)⁻¹
          = ((S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹) *
              ((S0_generator c) * (p.2 : G) * (S0_generator c)⁻¹) := by group
      _ = ((S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹) * (p.2 : G) := by
            congr 1
            calc
              (S0_generator c) * (p.2 : G) * (S0_generator c)⁻¹
                  = (p.2 : G) * (S0_generator c) * (S0_generator c)⁻¹ := by rw [hcommS]
              _ = (p.2 : G) := by group
  change extensionChar c hSC α lam
      ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
        S0_generator_normalizes_extensionSubgroup c hSC x⟩ =
    extensionChar c hSC (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) lam x
  have hL : extensionChar c hSC α lam
      ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
        S0_generator_normalizes_extensionSubgroup c hSC x⟩ =
      α.1 ⟨(S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹, hU⟩ * ((lam p.2 : ℂˣ) : ℂ) := by
    rw [show (⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
          S0_generator_normalizes_extensionSubgroup c hSC x⟩ : ↥(extensionSubgroup c)) =
        ⟨((S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹) * (p.2 : G),
          (extensionSubgroup c).mul_mem
            (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) hU)
            (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) p.2.2)⟩ by
        apply Subtype.ext
        exact hEq]
    exact extensionChar_mul c hSC α lam
      ⟨(S0_generator c) * (p.1 : G) * (S0_generator c)⁻¹, hU⟩ p.2
  have hR : extensionChar c hSC (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) lam x =
      (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 p.1 * ((lam p.2 : ℂˣ) : ℂ) := by
    rw [show (x : ↥(extensionSubgroup c)) =
        ⟨(p.1 : G) * (p.2 : G),
          (extensionSubgroup c).mul_mem
            (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) p.1.2)
            (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) p.2.2)⟩ by
        apply Subtype.ext
        exact hp]
    exact extensionChar_mul c hSC (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) lam p.1 p.2
  rw [hL, hR]
  congr 1

/-- If `r0 = t1·t2` moves `α`, the induced extension `Ind_X^{H0}(α̂)` is
irreducible. -/
public lemma extensionChar_ind_isIrreducible_of_not_fixed (c : Hyp11 G)
    (hSC : Section3Hyp c) (h12 : Hyp12 c) (α : Irr (↥c.U))
    (lam : ↥(SPrime c) →* ℂˣ)
    (hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    IsIrreducibleCharacter (extensionChar_ind c hSC α lam) := by
  refine isIrreducibleCharacter_of_norm_one_inv
    (extensionChar_ind_isCharacter c hSC h12 α lam) ?_
  unfold extensionChar_ind
  refine scalarProductInv_ind_index_two (extensionSubgroup c) c.H0
    (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
    (s := S0_generator c) (S0_generator_mem_H0 c)
    (S0_generator_not_mem_extensionSubgroup c hSC)
    (extensionChar_isIrreducible c hSC α lam)
    (S0_generator_normalizes_extensionSubgroup c hSC)
    ?hνs_ne
  · intro h
    rw [extensionChar_conj_r0] at h
    exact hα (extensionChar_injective c hSC
      (α := conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) (β := α) lam h)

/-- If `r0 = t1·t2` fixes `α`, the induced extension has star-scalar-product
norm two (Remark 1.4: `ν^s = ν` gives `|ν^H| = 2`). -/
public lemma extensionChar_ind_norm_two_of_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ)
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α) :
    scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam)
      (extensionChar_ind c hSC α lam) = 2 := by
  have hνs_eq : conjChar (extensionSubgroup c) (s := S0_generator c)
      (S0_generator_normalizes_extensionSubgroup c hSC)
      (extensionChar c hSC α lam) = extensionChar c hSC α lam := by
    rw [extensionChar_conj_r0]
    exact congrArg (fun β : Irr (↥c.U) => extensionChar c hSC β lam) hfix
  have hspInv : scalarProductInv (↥c.H0) (extensionChar_ind c hSC α lam)
      (extensionChar_ind c hSC α lam) = 2 := by
    unfold extensionChar_ind
    exact scalarProductInv_ind_index_two_of_fixed (extensionSubgroup c) c.H0
      (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
      (s := S0_generator c) (S0_generator_mem_H0 c)
      (S0_generator_not_mem_extensionSubgroup c hSC)
      (extensionChar_isIrreducible c hSC α lam)
      (S0_generator_normalizes_extensionSubgroup c hSC) hνs_eq
  have hb : star (scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam)
      (extensionChar_ind c hSC α lam)) =
      scalarProductInv (↥c.H0) (extensionChar_ind c hSC α lam)
        (extensionChar_ind c hSC α lam) :=
    star_scalarProduct_eq_inv_of_char (extensionChar_ind_isCharacter c hSC h12 α lam)
  exact star_inj.mp (by simpa using hb.trans hspInv)

/-- When `r0 = t1·t2` fixes `α`, the induced extension splits into two
distinct irreducible constituents (Remark 1.4). -/
public lemma extensionChar_ind_decomp_of_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ)
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α) :
    ∃ σ₁ σ₂ : ClassFunction (↥c.H0),
      IsIrreducibleCharacter σ₁ ∧ IsIrreducibleCharacter σ₂ ∧ σ₁ ≠ σ₂ ∧
      extensionChar_ind c hSC α lam = σ₁ + σ₂ := by
  exact char_norm_two_decomp (extensionChar_ind_isCharacter c hSC h12 α lam)
    (extensionChar_ind_norm_two_of_fixed c hSC h12 α lam hfix)

/-- When `r0 = t1·t2` fixes `α`, the induced extension equals `2·α̂` on
`X = S'·U`. -/
public lemma extensionChar_ind_on_X_of_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ)
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α) :
    ∀ x : ↥(extensionSubgroup c),
      extensionChar_ind c hSC α lam ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ =
        2 * extensionChar c hSC α lam x := by
  intro x
  have hνs_eq : conjChar (extensionSubgroup c) (s := S0_generator c)
      (S0_generator_normalizes_extensionSubgroup c hSC)
      (extensionChar c hSC α lam) = extensionChar c hSC α lam := by
    rw [extensionChar_conj_r0]
    exact congrArg (fun β : Irr (↥c.U) => extensionChar c hSC β lam) hfix
  have hmain := inducedFromSub_eq_add_conj_index_two (extensionSubgroup c) c.H0
    (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
    (s := S0_generator c) (S0_generator_mem_H0 c)
    (S0_generator_not_mem_extensionSubgroup c hSC)
    (extensionChar c hSC α lam)
    (isCharacter_isClassFunction (extensionChar_isCharacter c hSC α lam)) x.2
    (S0_generator_normalizes_extensionSubgroup c hSC x)
  change @inducedFromSub G _ _ (extensionSubgroup c) c.H0 (SPrimeMulU_le_H0 c)
      (extensionChar c hSC α lam) ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ =
      2 * extensionChar c hSC α lam x
  have hsecond : extensionChar c hSC α lam
      ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
        S0_generator_normalizes_extensionSubgroup c hSC x⟩ =
      extensionChar c hSC α lam x := by
    have hc : extensionChar c hSC α lam
        ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
          S0_generator_normalizes_extensionSubgroup c hSC x⟩ =
        conjChar (extensionSubgroup c) (s := S0_generator c)
          (S0_generator_normalizes_extensionSubgroup c hSC)
          (extensionChar c hSC α lam) x := by
      rfl
    rw [hc, hνs_eq]
  rw [hmain, hsecond]
  ring

/-- Each irreducible constituent of `Ind_X^{H0}(α̂)` coincides with `α̂` on
`X = S'·U` when `r0 = t1·t2` fixes `α`. -/
public lemma extensionChar_ind_constituent_on_X_of_fixed (c : Hyp11 G)
    (hSC : Section3Hyp c) (h12 : Hyp12 c) (α : Irr (↥c.U))
    (lam : ↥(SPrime c) →* ℂˣ)
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α)
    {σ : ClassFunction (↥c.H0)} (hσ : IsIrreducibleCharacter σ)
    (hσin : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) σ ≠ 0) :
    ∀ x : ↥(extensionSubgroup c),
      σ ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ = extensionChar c hSC α lam x := by
  classical
  let K : Subgroup (↥c.H0) := (extensionSubgroup c).subgroupOf c.H0
  let alphaHatK : ClassFunction (↥K) :=
    fun x => extensionChar c hSC α lam ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  let τK (τ : ClassFunction (↥c.H0)) : ClassFunction (↥K) :=
    fun x => τ (x : ↥c.H0)
  rcases extensionChar_ind_decomp_of_fixed c hSC h12 α lam hfix with ⟨σ₁, σ₂, hσ₁, hσ₂, hne, hsum⟩
  have hsum' : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) σ =
      scalarProduct (↥c.H0) (σ₁ + σ₂) σ := by rw [hsum]
  have hEqσ : σ = σ₁ ∨ σ = σ₂ := by
    rw [hsum'] at hσin
    rw [scalarProduct_add_left] at hσin
    by_cases h1 : σ₁ = σ
    · left
      exact h1.symm
    · by_cases h2 : σ₂ = σ
      · right
        exact h2.symm
      · exfalso
        apply hσin
        rw [scalarProduct_irreducible_orthogonal hσ₁ hσ h1,
            scalarProduct_irreducible_orthogonal hσ₂ hσ h2]
        norm_num
  have hIndσ : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) σ = 1 := by
    rcases hEqσ with rfl | rfl
    · rw [hsum, scalarProduct_add_left]
      rw [scalarProduct_irreducible_self hσ₁]
      rw [scalarProduct_irreducible_orthogonal hσ₂ hσ₁ (fun h => hne h.symm)]
      norm_num
    · rw [hsum, scalarProduct_add_left]
      rw [scalarProduct_irreducible_orthogonal hσ₁ hσ₂ hne]
      rw [scalarProduct_irreducible_self hσ₂]
      norm_num
  have hIndσ₁ : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) σ₁ = 1 := by
    rw [hsum, scalarProduct_add_left]
    rw [scalarProduct_irreducible_self hσ₁]
    rw [scalarProduct_irreducible_orthogonal hσ₂ hσ₁ (fun h => hne h.symm)]
    norm_num
  have hIndσ₂ : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) σ₂ = 1 := by
    rw [hsum, scalarProduct_add_left]
    rw [scalarProduct_irreducible_orthogonal hσ₁ hσ₂ hne]
    rw [scalarProduct_irreducible_self hσ₂]
    norm_num
  have hKsp (τ : ClassFunction (↥c.H0)) (hτ : IsIrreducibleCharacter τ)
      (hIndτ : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) τ = 1) :
      scalarProduct (↥K) alphaHatK (τK τ) = 1 := by
    have hf := frobenius_reciprocity (G := ↥c.H0) (H := K) alphaHatK
      (isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter hτ))
    have hInd : scalarProduct (↥c.H0) (inducedClassFunction K alphaHatK) τ =
        scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) τ := by
      rfl
    have hInd' : scalarProduct (↥c.H0) (inducedClassFunction K alphaHatK) τ = 1 := by
      rw [hInd]
      exact hIndτ
    exact hf.symm.trans hInd'
  have hσX_irr : IsIrreducibleCharacter alphaHatK := by
    let e : ↥K ≃* ↥(extensionSubgroup c) :=
      Subgroup.subgroupOfEquivOfLe (H := extensionSubgroup c) (K := c.H0) (SPrimeMulU_le_H0 c)
    have h := isIrreducibleCharacter_congr e (extensionChar_isIrreducible c hSC α lam)
    have hval : ∀ x : ↥K, e x = ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩ := by
      intro x
      rfl
    have h' : IsIrreducibleCharacter (fun x : ↥K =>
        extensionChar c hSC α lam ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩) := by
      simpa [e, hval] using h
    simpa [alphaHatK] using h'
  have hdeg_le (τ : ClassFunction (↥c.H0)) (hτ : IsIrreducibleCharacter τ)
      (hIndτ : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) τ = 1) :
      ∃ rτ rα : ℕ, τK τ 1 = (rτ : ℂ) ∧ alphaHatK 1 = (rα : ℂ) ∧ rα ≤ rτ := by
    exact irreducible_char_degree_le_of_scalarProduct_one
      (isCharacter_restrict (G := ↥c.H0) (H := K) (isCharacter_of_isIrreducibleCharacter hτ))
      hσX_irr (hKsp τ hτ hIndτ)
  have hdeg_sum : σ₁ 1 + σ₂ 1 = 2 * extensionChar c hSC α lam 1 := by
    have hInd1 : extensionChar_ind c hSC α lam 1 = 2 * extensionChar c hSC α lam 1 := by
      change extensionChar_ind c hSC α lam ⟨(1 : G), (c.H0).one_mem⟩ =
        2 * extensionChar c hSC α lam (1 : ↥(extensionSubgroup c))
      simpa using extensionChar_ind_on_X_of_fixed c hSC h12 α lam hfix
        (1 : ↥(extensionSubgroup c))
    have hsum1 : extensionChar_ind c hSC α lam 1 = σ₁ 1 + σ₂ 1 := by
      rw [hsum]
      rfl
    rw [← hsum1, hInd1]
  rcases hdeg_le σ₁ hσ₁ hIndσ₁ with ⟨r₁, rα₁, hr₁, hα₁, hle₁⟩
  rcases hdeg_le σ₂ hσ₂ hIndσ₂ with ⟨r₂, rα₂, hr₂, hα₂, hle₂⟩
  have hrα : rα₁ = rα₂ := by
    exact_mod_cast (hα₁.symm.trans hα₂)
  have h1X : (⟨(1 : G), Subgroup.mem_subgroupOf.mp (1 : ↥K).2⟩ : ↥(extensionSubgroup c)) =
      (1 : ↥(extensionSubgroup c)) := by
    apply Subtype.ext
    rfl
  have hdeg_nat : r₁ + r₂ = 2 * rα₁ := by
    have hc : (r₁ + r₂ : ℂ) = (2 * rα₁ : ℂ) := by
      calc
        (r₁ + r₂ : ℂ) = σ₁ 1 + σ₂ 1 := by
              rw [← hr₁, ← hr₂]
              rfl
        _ = 2 * extensionChar c hSC α lam 1 := hdeg_sum
        _ = 2 * (rα₁ : ℂ) := by
              have hα₁' : extensionChar c hSC α lam 1 = (rα₁ : ℂ) := by
                simpa [alphaHatK, h1X] using hα₁
              rw [hα₁']
    exact_mod_cast hc
  have hr₁eq : r₁ = rα₁ := by omega
  have hr₂eq : r₂ = rα₁ := by omega
  have hσdeg : σ 1 = extensionChar c hSC α lam 1 := by
    rcases hEqσ with hσ₁eq | hσ₂eq
    · calc
        σ 1 = (r₁ : ℂ) := by rw [hσ₁eq]; simpa [τK] using hr₁
        _ = (rα₁ : ℂ) := by rw [hr₁eq]
        _ = extensionChar c hSC α lam 1 := by simpa [alphaHatK, h1X] using hα₁.symm
    · calc
        σ 1 = (r₂ : ℂ) := by rw [hσ₂eq]; simpa [τK] using hr₂
        _ = (rα₁ : ℂ) := by rw [hr₂eq]
        _ = extensionChar c hSC α lam 1 := by simpa [alphaHatK, h1X] using hα₁.symm
  have hσK_eq : τK σ = alphaHatK := by
    exact char_eq_irreducible_of_scalarProduct_one_and_degree
      (isCharacter_restrict (G := ↥c.H0) (H := K) (isCharacter_of_isIrreducibleCharacter hσ))
      hσX_irr (hKsp σ hσ hIndσ) (by simpa [τK, alphaHatK, h1X] using hσdeg)
  intro x
  have h := congrFun hσK_eq ⟨⟨(x : G), SPrimeMulU_le_H0 c x.2⟩,
    Subgroup.mem_subgroupOf.mpr x.2⟩
  simpa [τK, alphaHatK] using h

/-- Each irreducible constituent of `Ind_X^{H0}(α̂)` restricts to `α` on `U`
when `r0 = t1·t2` fixes `α`. -/
public lemma extensionChar_ind_constituent_restrict_of_fixed (c : Hyp11 G)
    (hSC : Section3Hyp c) (h12 : Hyp12 c) (α : Irr (↥c.U))
    (lam : ↥(SPrime c) →* ℂˣ)
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α)
    {σ : ClassFunction (↥c.H0)} (hσ : IsIrreducibleCharacter σ)
    (hσin : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) σ ≠ 0) :
    restrictU c h12 σ = α.1 := by
  classical
  ext u
  have hx := extensionChar_ind_constituent_on_X_of_fixed c hSC h12 α lam hfix hσ hσin
    ⟨(u : G), SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩
  have hval : σ ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ = α.1 u := by
    rw [show (⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ : ↥c.H0) =
        ⟨(u : G), SPrimeMulU_le_H0 c
          (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2)⟩ by
          apply Subtype.ext
          rfl]
    simpa [extensionChar_restrict c hSC α lam u] using hx
  simpa [restrictU] using hval

/-- Every linear character of `S'` extends to a `Λ`-character of
`H0` (trivial on `U`): extend `S' → ℂˣ` to `S0 → ℂˣ` and pull back along
`H0 → S0`. -/
public theorem exists_lambdaHom_extending_lam (c : Hyp11 G) (h12 : Hyp12 c)
    (lam : ↥(SPrime c) →* ℂˣ) :
    ∃ l : LambdaHom c.H0 c.U,
      ∀ s : ↥(SPrime c), l.1 ⟨(s : G), SPrime_le_H0 c s.2⟩ = (lam s : ℂˣ) := by
  classical
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
  let H : Subgroup (↥(c.S0 : Subgroup G)) :=
    (SPrime c).subgroupOf (c.S0 : Subgroup G)
  let e : H ≃* ↥(SPrime c) :=
    Subgroup.subgroupOfEquivOfLe (H := SPrime c) (K := c.S0) (SPrime_le_S0 c)
  let lamH : H →* ℂˣ := lam.comp e
  have hsurj : Function.Surjective (MonoidHom.restrictHom H ℂˣ) :=
    MonoidHom.restrict_surjective (G := ↥(c.S0 : Subgroup G)) (M := ℂ) H
  rcases hsurj lamH with ⟨φ, hφ⟩
  let l : LambdaHom c.H0 c.U := ⟨s0Char c h12 φ, s0Char_mem c h12 φ⟩
  refine ⟨l, ?_⟩
  intro s
  have hπ : s0Projection c h12 ⟨(s : G), SPrime_le_H0 c s.2⟩ =
      ⟨(s : G), SPrime_le_S0 c s.2⟩ := by
    change s0Part c h12 ⟨(s : G), SPrime_le_H0 c s.2⟩ =
      ⟨(s : G), SPrime_le_S0 c s.2⟩
    apply s0Part_unique c h12 (u := 1) (r := ⟨(s : G), SPrime_le_S0 c s.2⟩)
    simp
  change φ (s0Projection c h12 ⟨(s : G), SPrime_le_H0 c s.2⟩) = (lam s : ℂˣ)
  rw [hπ]
  have hφfun : (fun x : H => φ x) = lamH := by
    exact congrArg (fun f : H →* ℂˣ => (fun x : H => f x)) hφ
  have hφ' := congrFun hφfun ⟨⟨(s : G), SPrime_le_S0 c s.2⟩,
    Subgroup.mem_subgroupOf.mpr s.2⟩
  have he : e ⟨⟨(s : G), SPrime_le_S0 c s.2⟩,
      Subgroup.mem_subgroupOf.mpr s.2⟩ = s := by
    rfl
  simpa [lamH, he] using hφ'

/-- Multiplying the extension by the `Λ`-character `l` (which extends `lam`
on `S'`) gives the extension by `lam`. -/
public lemma extensionChar_lambda_mul (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ) (l : LambdaHom c.H0 c.U)
    (hl : ∀ s : ↥(SPrime c), l.1 ⟨(s : G), SPrime_le_H0 c s.2⟩ = (lam s : ℂˣ))
    (x : ↥(extensionSubgroup c)) :
    (LambdaChar l.1) ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ *
        extensionChar c hSC α 1 x = extensionChar c hSC α lam x := by
  classical
  rcases exists_decomp c hSC x with ⟨p, hp⟩
  have hxH0 : (⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ : ↥c.H0) =
      (⟨(p.1 : G), U_le_H0 c p.1.2⟩ : ↥c.H0) *
        (⟨(p.2 : G), SPrime_le_H0 c p.2.2⟩ : ↥c.H0) := by
    apply Subtype.ext
    exact hp
  have hlx : l.1 (⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ : ↥c.H0) = (lam p.2 : ℂˣ) := by
    rw [hxH0, map_mul]
    have hu : l.1 ⟨(p.1 : G), U_le_H0 c p.1.2⟩ = 1 :=
      l.2 ⟨(p.1 : G), U_le_H0 c p.1.2⟩ p.1.2
    rw [hu, hl p.2]
    simp
  have hxprod : x = ⟨(p.1 : G) * (p.2 : G),
      (extensionSubgroup c).mul_mem
        (SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) p.1.2)
        (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) p.2.2)⟩ := by
    apply Subtype.ext
    exact hp
  calc
    (LambdaChar l.1) ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ *
        extensionChar c hSC α 1 x
      = ((lam p.2 : ℂˣ) : ℂ) * α.1 p.1 := by
          rw [LambdaChar, hlx, hxprod, extensionChar_mul c hSC α 1 p.1 p.2]
          simp [mul_comm]
    _ = extensionChar c hSC α lam x := by
          rw [hxprod, extensionChar_mul c hSC α lam p.1 p.2]
          simp [mul_comm]

/-- A `Λ`-character is constant on the `r0`-conjugacy within `X`: its value at
`r0·x·r0⁻¹` equals its value at `x` (since `ℂˣ` is commutative). -/
public lemma lambdaHom_conj_eq (c : Hyp11 G) (hSC : Section3Hyp c) (h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U)
    {x : ↥(extensionSubgroup c)} :
    l.1 ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
        SPrimeMulU_le_H0 c (S0_generator_normalizes_extensionSubgroup c hSC x)⟩ =
      l.1 ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ := by
  let a : ↥c.H0 := ⟨S0_generator c, S0_generator_mem_H0 c⟩
  let b : ↥c.H0 := ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩
  have hxy : (⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
      SPrimeMulU_le_H0 c (S0_generator_normalizes_extensionSubgroup c hSC x)⟩ : ↥c.H0) =
      a * b * a⁻¹ := by
    apply Subtype.ext
    rfl
  calc
    l.1 ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹,
        SPrimeMulU_le_H0 c (S0_generator_normalizes_extensionSubgroup c hSC x)⟩
        = l.1 (a * b * a⁻¹) := by rw [hxy]
    _ = l.1 b := by
          rw [map_mul, map_mul, map_inv]
          change ((l.1 a : ℂˣ) * (l.1 b : ℂˣ) * (l.1 a : ℂˣ)⁻¹) = (l.1 b : ℂˣ)
          simp [mul_assoc, mul_comm, mul_left_comm]

/-- `λ₂` takes the value `-1` at the generator `r0 = t1·t2`. -/
public theorem lambdaTwo_val_r0_eq_neg_one (c : Hyp11 G) (h12 : Hyp12 c) :
    ((lambdaTwo c h12).1 ⟨S0_generator c, S0_le_H0 c (S0_generator_mem_S0 c)⟩ : ℂ) = -1 := by
  classical
  let l := lambdaTwo c h12
  let r0H0 : ↥c.H0 := ⟨S0_generator c, S0_le_H0 c (S0_generator_mem_S0 c)⟩
  have hne1 : l.1 r0H0 ≠ 1 := by
    intro h1
    apply lambdaTwo_ne_one c h12
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hxeq⟩
    have hxH0 : x = ⟨(u : G), U_le_H0 c u.2⟩ * ⟨(r : G), S0_le_H0 c r.2⟩ := by
      apply Subtype.ext
      exact hxeq
    rw [hxH0, map_mul]
    have hu : l.1 ⟨(u : G), U_le_H0 c u.2⟩ = 1 := l.2 _ u.2
    rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using r.2)) with ⟨k, hk⟩
    have hreq : ⟨(r : G), S0_le_H0 c r.2⟩ = r0H0 ^ k := by
      apply Subtype.ext
      simpa [r0H0, S0_generator] using hk.symm
    have hr : l.1 ⟨(r : G), S0_le_H0 c r.2⟩ = 1 := by
      rw [hreq, map_zpow, h1]
      simp
    rw [hu, hr]
    simp
  have hsq : (l.1 r0H0 : ℂ) ^ 2 = 1 := by
    have h := congrArg (fun z : LambdaHom c.H0 c.U => ((z.1 r0H0 : ℂˣ) : ℂ))
      (lambdaTwo_sq_eq_one c h12)
    simpa [pow_two] using h
  have hz : (l.1 r0H0 : ℂˣ) = -1 := by
    apply Units.ext
    have hneC : (l.1 r0H0 : ℂ) ≠ 1 := by
      intro h
      exact hne1 (Units.ext h)
    have hfac : (((l.1 r0H0 : ℂ) - 1) * ((l.1 r0H0 : ℂ) + 1)) = 0 := by
      have hsqsub : (((l.1 r0H0 : ℂ) - 1) * ((l.1 r0H0 : ℂ) + 1)) =
          ((l.1 r0H0 : ℂ) ^ 2 - 1) := by ring
      rw [hsqsub, hsq]
      norm_num
    have hcases : (l.1 r0H0 : ℂ) = 1 ∨ (l.1 r0H0 : ℂ) = -1 := by
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · left
        exact sub_eq_zero.mp hsub
      · right
        exact eq_neg_of_add_eq_zero_left hadd
    rcases hcases with h | h
    · exact False.elim (hneC h)
    · exact h
  simpa [l] using congrArg (fun u : ℂˣ => (u : ℂ)) hz

/-- `λ₂` is trivial on `X = S'·U` (it kills `S'` and all of `U`). -/
public lemma lambdaTwo_trivial_on_extensionSubgroup (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {x : ↥c.H0} (hx : (x : G) ∈ extensionSubgroup c) :
    (lambdaTwo c h12).1 x = 1 := by
  classical
  let xX : ↥(extensionSubgroup c) := ⟨(x : G), hx⟩
  rcases exists_decomp c hSC xX with ⟨p, hp⟩
  have hxH0 : x = (⟨(p.1 : G), U_le_H0 c p.1.2⟩ : ↥c.H0) *
      (⟨(p.2 : G), SPrime_le_H0 c p.2.2⟩ : ↥c.H0) := by
    apply Subtype.ext
    exact hp
  rw [hxH0, map_mul]
  have hu : (lambdaTwo c h12).1 ⟨(p.1 : G), U_le_H0 c p.1.2⟩ = 1 :=
    (lambdaTwo c h12).2 _ p.1.2
  rw [hu]
  rw [lambdaTwo_trivial_on_SPrime c h12 ⟨(p.2 : G), SPrime_le_H0 c p.2.2⟩ p.2.2]
  simp

/-- `λ₂` takes the value `-1` on the nontrivial coset `H0 \ X`. -/
public lemma lambdaTwo_val_neg_one_of_not_mem_extensionSubgroup (c : Hyp11 G)
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (x : ↥c.H0)
    (hx : (x : G) ∉ extensionSubgroup c) :
    (lambdaTwo c h12).1 x = -1 := by
  classical
  let K : Subgroup (↥c.H0) := (extensionSubgroup c).subgroupOf c.H0
  let r0' : ↥c.H0 := ⟨S0_generator c, S0_generator_mem_H0 c⟩
  let l := lambdaTwo c h12
  have hindex : K.index = 2 := by
    simpa [K] using extensionSubgroup_index_two c hSC h12
  have hr0K : r0' ∉ K := by
    intro h
    exact S0_generator_not_mem_extensionSubgroup c hSC (Subgroup.mem_subgroupOf.mp h)
  have hxK : x ∉ K := by
    intro h
    exact hx (Subgroup.mem_subgroupOf.mp h)
  have hiff : r0' * x ∈ K ↔ (r0' ∈ K ↔ x ∈ K) :=
    Subgroup.mul_mem_iff_of_index_two hindex (a := r0') (b := x)
  have hyK : r0' * x ∈ K := by
    rw [hiff]
    simp [hr0K, hxK]
  let y : ↥K := ⟨r0' * x, hyK⟩
  have hxeq : x = (r0'⁻¹ : ↥c.H0) * (y : ↥c.H0) := by
    apply Subtype.ext
    change (x : G) = (r0' : G)⁻¹ * ((r0' : G) * (x : G))
    group
  have hy1 : l.1 (y : ↥c.H0) = 1 := by
    have hyX : ((y : ↥c.H0) : G) ∈ extensionSubgroup c := Subgroup.mem_subgroupOf.mp y.2
    exact lambdaTwo_trivial_on_extensionSubgroup c h12 hSC hyX
  have hr0 : l.1 r0' = (-1 : ℂˣ) := by
    apply Units.ext
    simpa [l, r0'] using lambdaTwo_val_r0_eq_neg_one c h12
  calc
    l.1 x = l.1 ((r0'⁻¹ : ↥c.H0) * (y : ↥c.H0)) := by rw [hxeq]
    _ = l.1 (r0'⁻¹ : ↥c.H0) * l.1 (y : ↥c.H0) := by rw [map_mul]
    _ = (l.1 r0')⁻¹ * l.1 (y : ↥c.H0) := by rw [map_inv]
    _ = (-1 : ℂˣ)⁻¹ * 1 := by rw [hr0, hy1]
    _ = -1 := by simp

/-- In the fixed branch (`r0` fixes `α`), multiplying the first constituent
of `Ind_X^{H0}(α̂_1)` by `λ₂` gives the second: `Λ₂·σ₁ = σ₂`. -/
public lemma lambdaTwo_mul_sigma1_eq_sigma2_of_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) (α : Irr (↥c.U))
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α)
    {σ₁ σ₂ : ClassFunction (↥c.H0)} (hσ₁ : IsIrreducibleCharacter σ₁)
    (hσ₂ : IsIrreducibleCharacter σ₂) (hne : σ₁ ≠ σ₂)
    (hsum : extensionChar_ind c hSC α 1 = σ₁ + σ₂) :
    LambdaChar (lambdaTwo c h12).1 * σ₁ = σ₂ := by
  classical
  ext x
  by_cases hxX : (x : G) ∈ extensionSubgroup c
  · have hlam : (lambdaTwo c h12).1 x = 1 :=
      lambdaTwo_trivial_on_extensionSubgroup c h12 hSC hxX
    have hsp₁ : scalarProduct (↥c.H0) (extensionChar_ind c hSC α 1) σ₁ ≠ 0 := by
      rw [hsum, scalarProduct_add_left]
      rw [scalarProduct_irreducible_self hσ₁]
      rw [scalarProduct_irreducible_orthogonal hσ₂ hσ₁ (fun hEq => hne hEq.symm)]
      norm_num
    have hsp₂ : scalarProduct (↥c.H0) (extensionChar_ind c hSC α 1) σ₂ ≠ 0 := by
      rw [hsum, scalarProduct_add_left]
      rw [scalarProduct_irreducible_orthogonal hσ₁ hσ₂ hne]
      rw [scalarProduct_irreducible_self hσ₂]
      norm_num
    have h₁ : σ₁ x = extensionChar c hSC α 1 ⟨(x : G), hxX⟩ := by
      have h := extensionChar_ind_constituent_on_X_of_fixed c hSC h12 α 1 hfix hσ₁ hsp₁
        ⟨(x : G), hxX⟩
      change σ₁ ⟨(x : G), SPrimeMulU_le_H0 c hxX⟩ = extensionChar c hSC α 1 ⟨(x : G), hxX⟩
      exact h
    have h₂ : σ₂ x = extensionChar c hSC α 1 ⟨(x : G), hxX⟩ := by
      have h := extensionChar_ind_constituent_on_X_of_fixed c hSC h12 α 1 hfix hσ₂ hsp₂
        ⟨(x : G), hxX⟩
      change σ₂ ⟨(x : G), SPrimeMulU_le_H0 c hxX⟩ = extensionChar c hSC α 1 ⟨(x : G), hxX⟩
      exact h
    simp [LambdaChar, hlam, h₁, h₂]
  · have hlamu : (lambdaTwo c h12).1 x = -1 :=
      lambdaTwo_val_neg_one_of_not_mem_extensionSubgroup c h12 hSC x hxX
    have hlc : (((lambdaTwo c h12).1 x : ℂˣ) : ℂ) = -1 := by
      exact congrArg (fun u : ℂˣ => (u : ℂ)) hlamu
    have hInd0 : extensionChar_ind c hSC α 1 x = 0 :=
      inducedFromSub_eq_zero_of_not_mem (extensionSubgroup c) c.H0
        (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
        (ν := extensionChar c hSC α 1) (x := x) hxX
    have hsumx : σ₁ x + σ₂ x = 0 := by
      have h := congrFun hsum x
      rw [hInd0] at h
      exact h.symm
    have hneg : σ₂ x = -(σ₁ x) := eq_neg_of_add_eq_zero_right hsumx
    simp [LambdaChar, hlc, hneg]

/-- Multiplying the induced extension by the `Λ`-character `l` (which extends
`lam` on `S'`) gives the induced extension by `lam`. -/
public lemma extensionChar_ind_lambda_mul (c : Hyp11 G) (hSC : Section3Hyp c)
    (h12 : Hyp12 c) (α : Irr (↥c.U)) (lam : ↥(SPrime c) →* ℂˣ)
    (l : LambdaHom c.H0 c.U)
    (hl : ∀ s : ↥(SPrime c), l.1 ⟨(s : G), SPrime_le_H0 c s.2⟩ = (lam s : ℂˣ)) :
    LambdaChar l.1 * extensionChar_ind c hSC α 1 = extensionChar_ind c hSC α lam := by
  ext x
  change (LambdaChar l.1) x * extensionChar_ind c hSC α 1 x =
    extensionChar_ind c hSC α lam x
  by_cases hxX : (x : G) ∈ extensionSubgroup c
  · let xX : ↥(extensionSubgroup c) := ⟨(x : G), hxX⟩
    have hxnorm : (S0_generator c) * (x : G) * (S0_generator c)⁻¹ ∈ extensionSubgroup c :=
      S0_generator_normalizes_extensionSubgroup c hSC xX
    have hmain1 := inducedFromSub_eq_add_conj_index_two (extensionSubgroup c) c.H0
      (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
      (s := S0_generator c) (S0_generator_mem_H0 c)
      (S0_generator_not_mem_extensionSubgroup c hSC)
      (extensionChar c hSC α 1)
      (isCharacter_isClassFunction (extensionChar_isCharacter c hSC α 1)) hxX hxnorm
    have hmain2 := inducedFromSub_eq_add_conj_index_two (extensionSubgroup c) c.H0
      (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
      (s := S0_generator c) (S0_generator_mem_H0 c)
      (S0_generator_not_mem_extensionSubgroup c hSC)
      (extensionChar c hSC α lam)
      (isCharacter_isClassFunction (extensionChar_isCharacter c hSC α lam)) hxX hxnorm
    have h1 := extensionChar_lambda_mul c hSC α lam l hl xX
    have h2 := extensionChar_lambda_mul c hSC α lam l hl
      ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹, hxnorm⟩
    change (LambdaChar l.1) x *
        @inducedFromSub G _ _ (extensionSubgroup c) c.H0 (SPrimeMulU_le_H0 c)
          (extensionChar c hSC α 1) x =
      @inducedFromSub G _ _ (extensionSubgroup c) c.H0 (SPrimeMulU_le_H0 c)
          (extensionChar c hSC α lam) x
    rw [hmain1, hmain2, LambdaChar]
    rw [← h1, ← h2]
    simp only [LambdaChar] at h1 h2 ⊢
    rw [← lambdaHom_conj_eq c hSC h12 l (x := xX)]
    simp only [xX] at ⊢
    ring_nf
  · have h0₁ : (extensionChar_ind c hSC α 1) x = 0 :=
      inducedFromSub_eq_zero_of_not_mem (extensionSubgroup c) c.H0
        (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
        (ν := extensionChar c hSC α 1) (x := x) (by
          intro hx
          exact hxX hx)
    have h0₂ : (extensionChar_ind c hSC α lam) x = 0 :=
      inducedFromSub_eq_zero_of_not_mem (extensionSubgroup c) c.H0
        (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
        (ν := extensionChar c hSC α lam) (x := x) (by
          intro hx
          exact hxX hx)
    simp [LambdaChar, h0₁, h0₂]

end Section3

end CFSG.BenderGlauberman
