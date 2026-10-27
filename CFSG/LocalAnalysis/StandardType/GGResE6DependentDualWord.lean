module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.E6DependentDualSeven

open Module
open CFSG.StandardType

abbrev K := ZMod 3
abbrev V7 := Fin 7 → K

@[expose] def coord (i : Fin 7) : Module.Dual K V7 :=
  LinearMap.proj (R := K) (φ := fun _ : Fin 7 => K) i

@[expose] def e6Col (i : Fin 6) : V7 :=
  Fin.snoc (fun j : Fin 6 => ((CartanMatrix.E 6) j i : K)) 0

@[expose] def e6F (i : Fin 6) : Module.Dual K V7 := coord i.castSucc

lemma e6F_e6Col (i : Fin 6) : e6F i (e6Col i) = 2 := by
  simp [e6F, e6Col, coord, CartanMatrix.E]

@[expose] def s (i : Fin 6) : V7 ≃ₗ[K] V7 := Module.reflection (e6F_e6Col i)

@[expose] def rRoot : V7 := ![0, 0, 0, 0, 1, 1, 1]

@[expose] def rF : Module.Dual K V7 :=
  coord (5 : Fin 7) + coord (6 : Fin 7)

lemma rF_rRoot : rF rRoot = 2 := by
  norm_num [rF, rRoot, coord]

@[expose] def r : V7 ≃ₗ[K] V7 := Module.reflection rF_rRoot

@[expose] def codeLin (a : Fin 7) : V7 ≃ₗ[K] V7 :=
  if h : a.val < 6 then s ⟨a.val, h⟩ else r

@[expose] def wordCodes : List (Fin 7) :=
  [    3, 6, 5, 1, 3, 0, 5, 3, 2, 5, 2, 1, 3, 4, 1, 2,
    0, 1, 0, 5, 0, 3, 2, 6, 5, 4, 2, 1, 0, 5, 0, 1,
    6, 1, 5, 4, 1, 4, 3, 2, 4, 6, 4, 0, 5, 2, 6, 4,
    3, 0, 6, 5, 1, 4, 6, 1, 6, 4, 0, 2, 4, 6, 0, 3,
    2, 6, 2, 1, 4, 6, 4, 0, 5, 6, 1, 3, 6, 0, 6, 5,
    6, 5, 3, 0, 6, 3, 5, 2, 1, 5, 2, 0, 1, 2, 4, 5,
    4, 2, 0, 2, 3, 0, 4, 2, 3, 6, 1, 2, 4, 2, 1, 0,
    6, 4, 2, 0, 5, 4]

@[expose] def wordProd : V7 ≃ₗ[K] V7 :=
  (wordCodes.reverse.map codeLin).prod

@[expose] def wordLin : V7 →ₗ[K] V7 := (wordProd : V7 →ₗ[K] V7)

@[expose] def tF : Module.Dual K V7 :=
  coord (0 : Fin 7) + (2 : K) • coord (2 : Fin 7) +
    coord (4 : Fin 7) + (2 : K) • coord (5 : Fin 7)

@[expose] def tU : V7 := Pi.single (6 : Fin 7) 1

@[expose] def tA : V7 →ₗ[K] V7 := tF.smulRight tU

@[expose] def tMap : V7 →ₗ[K] V7 := LinearMap.id + tA

@[expose] def tMapInv : V7 →ₗ[K] V7 := LinearMap.id - tA

lemma tF_tU : tF tU = 0 := by
  simp [tF, tU, coord]

lemma tA_comp_self : tA * tA = 0 := by
  ext v
  simp [tA, LinearMap.smulRight_apply, tF_tU]

lemma tA_apply_apply (v : V7) : tA (tA v) = 0 := by
  simpa [Module.End.mul_apply] using
    congrArg (fun f : V7 →ₗ[K] V7 => f v) tA_comp_self

lemma tMap_comp_tMapInv : tMap.comp tMapInv = LinearMap.id := by
  ext v
  simp [tMap, tMapInv, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply, tA_apply_apply]

lemma tMapInv_comp_tMap : tMapInv.comp tMap = LinearMap.id := by
  ext v
  simp [tMap, tMapInv, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply, tA_apply_apply]

@[expose] noncomputable def T : V7 ≃ₗ[K] V7 :=
  LinearEquiv.ofLinearMap tMap tMapInv tMap_comp_tMapInv tMapInv_comp_tMap

lemma T_toLinearMap : (T : V7 →ₗ[K] V7) = tMap := rfl

lemma T_apply (v : V7) : T v = v + tF v • tU := by
  change tMap v = v + tF v • tU
  simp [tMap, tA, LinearMap.smulRight_apply]

lemma tU_ne_zero : tU ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa [tU] using congrArg (fun v : V7 => v (6 : Fin 7)) h
  exact one_ne_zero h1

lemma tF_ne_zero : tF ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa [tF, coord] using
      congrArg (fun f : Module.Dual K V7 => f (Pi.single (0 : Fin 7) 1)) h
  exact one_ne_zero h1

attribute [irreducible] wordLin

theorem isTransvection_T : QTwoLin.IsTransvectionLin T := by
  refine ⟨tU, tF, tU_ne_zero, tF_ne_zero, tF_tU, fun v => T_apply v⟩

end CFSG.StandardType.E6DependentDualSeven

namespace CFSG.StandardType.E6DependentDualSeven.At72

open Module
open CFSG.StandardType

abbrev K := ZMod 3
abbrev V7 := Fin 7 → K

@[expose] def u72 : Fin 6 → K := ![0, 0, 0, 0, 1, 1]

@[expose] def alpha (c d : K) : Module.Dual K V7 :=
  c • E6DependentDualSeven.coord (0 : Fin 7) +
    (2 * c) • E6DependentDualSeven.coord (2 : Fin 7) +
    c • E6DependentDualSeven.coord (4 : Fin 7) +
    d • E6DependentDualSeven.coord (5 : Fin 7) +
    E6DependentDualSeven.coord (6 : Fin 7)

@[expose] def root (c d : K) : V7 := Fin.snoc u72 (2 - c - d)

lemma alpha_root (c d : K) : alpha c d (root c d) = 2 := by
  simp [alpha, root, u72, E6DependentDualSeven.coord]

@[expose] noncomputable def rCD (c d : K) : V7 ≃ₗ[K] V7 :=
  Module.reflection (alpha_root c d)

lemma alpha_axis (c d : K) : alpha c d E6DependentDualSeven.tU = 1 := by
  simp [alpha, E6DependentDualSeven.tU, E6DependentDualSeven.coord]

lemma root_ne_zero (c d : K) : root c d ≠ 0 := by
  intro h
  have h4 := congrArg (fun v : V7 => v (4 : Fin 7)) h
  simp [root, u72] at h4

lemma alpha_s4_fixed_all :
    ∀ c d : K, c + d = 0 →
      ∀ v : V7, alpha c d (E6DependentDualSeven.s 4 v) = alpha c d v := by
  decide +kernel

lemma s4_root_ne_all :
    ∀ c d : K, c + d = 0 →
      E6DependentDualSeven.s 4 (root c d) ≠ root c d := by
  decide +kernel

lemma s5_root_neg_all :
    ∀ c d : K, c + d = 2 →
      E6DependentDualSeven.s 5 (root c d) = -root c d := by
  decide +kernel

lemma s5_axis :
    E6DependentDualSeven.s 5 E6DependentDualSeven.tU = E6DependentDualSeven.tU := by
  decide +kernel

private lemma conj_reflection_eq_of_dual_fixed
    {K' V : Type*} [Field K'] [AddCommGroup V] [Module K' V]
    {g : V ≃ₗ[K'] V} {φ : Module.Dual K' V} {c : V}
    (hφ : φ c = 2) (hfix : ∀ v, φ (g v) = φ v) (hgc : φ (g c) = 2) :
    g * Module.reflection hφ * g⁻¹ = Module.reflection hgc := by
  ext v
  change g (g.symm v - φ (g.symm v) • c) = v - φ v • g c
  rw [map_sub, map_smul, g.apply_symm_apply]
  have hfixv : φ (g.symm v) = φ v := by
    simpa using (hfix (g.symm v)).symm
  rw [hfixv]

@[expose] def codeR (rExtra : V7 ≃ₗ[K] V7) (a : Fin 7) : V7 ≃ₗ[K] V7 :=
  if h : a.val < 6 then E6DependentDualSeven.s ⟨a.val, h⟩ else rExtra

@[expose] def wordProdR (rExtra : V7 ≃ₗ[K] V7) : V7 ≃ₗ[K] V7 :=
  (E6DependentDualSeven.wordCodes.reverse.map (codeR rExtra)).prod

@[expose] def wordLinR (rExtra : V7 ≃ₗ[K] V7) : V7 →ₗ[K] V7 :=
  (wordProdR rExtra : V7 →ₗ[K] V7)

lemma wordLinR_sum_one_basis :
    ∀ c d : K, c + d = 1 →
      ∀ k : Fin 7,
        (wordLinR (rCD c d) : V7 → V7) (Pi.single k 1) =
          E6DependentDualSeven.tMap (Pi.single k 1) := by
  decide +kernel

lemma wordLinR_eq_wordProdR (rExtra : V7 ≃ₗ[K] V7) :
    wordLinR rExtra = (wordProdR rExtra : V7 →ₗ[K] V7) := rfl

attribute [irreducible] wordLinR

lemma wordLinR_sum_one_eq_tMap (c d : K) (h : c + d = 1) :
    wordLinR (rCD c d) = E6DependentDualSeven.tMap := by
  apply (Pi.basisFun K (Fin 7)).ext
  intro k
  rw [Pi.basisFun_apply]
  exact wordLinR_sum_one_basis c d h k

lemma wordProdR_sum_one_eq_T (c d : K) (h : c + d = 1) :
    wordProdR (rCD c d) = E6DependentDualSeven.T := by
  apply LinearEquiv.toLinearMap_injective
  rw [← wordLinR_eq_wordProdR, wordLinR_sum_one_eq_tMap c d h]
  exact E6DependentDualSeven.T_toLinearMap.symm

private lemma noTF_of_word (rExtra : V7 ≃ₗ[K] V7)
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, E6DependentDualSeven.s i ∈ H)
    (hr : rExtra ∈ H)
    (hword : wordProdR rExtra = E6DependentDualSeven.T) : False := by
  have hcode : ∀ a : Fin 7, codeR rExtra a ∈ H := by
    intro a
    fin_cases a
    · simpa [codeR] using hs 0
    · simpa [codeR] using hs 1
    · simpa [codeR] using hs 2
    · simpa [codeR] using hs 3
    · simpa [codeR] using hs 4
    · simpa [codeR] using hs 5
    · simpa [codeR] using hr
  have hmem : wordProdR rExtra ∈ H := by
    unfold wordProdR
    refine H.toSubmonoid.list_prod_mem ?_
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact hcode a
  rw [hword] at hmem
  exact hTF E6DependentDualSeven.T hmem E6DependentDualSeven.isTransvection_T

lemma noTF_sum_zero (c d : K) (h : c + d = 0)
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, E6DependentDualSeven.s i ∈ H)
    (hr : rCD c d ∈ H) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfix := alpha_s4_fixed_all c d h
  have hroot_ne := s4_root_ne_all c d h
  let g : V7 ≃ₗ[K] V7 := E6DependentDualSeven.s 4
  have hg : g ∈ H := hs 4
  let hgc : alpha c d (g (root c d)) = 2 := by
    rw [hfix (root c d), alpha_root c d]
  have hconj := conj_reflection_eq_of_dual_fixed
    (K' := K) (V := V7) (g := g) (φ := alpha c d) (c := root c d)
    (alpha_root c d) hfix hgc
  have hmem : Module.reflection hgc ∈ H := by
    rw [← hconj]
    exact H.mul_mem (H.mul_mem hg hr) (H.inv_mem hg)
  have heq := QTwoLin.reflection_root_eq_of_transvectionFree hTF (alpha_root c d) hgc hr hmem
  exact hroot_ne heq.symm

lemma noTF_sum_two (c d : K) (h : c + d = 2)
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, E6DependentDualSeven.s i ∈ H)
    (hr : rCD c d ∈ H) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hneg := s5_root_neg_all c d h
  have hfix := QTwoLin.reflection_fixes_of_negated_root
    (K := K) (V := V7) (A := H) (c := root c d) (x := E6DependentDualSeven.tU)
    (φ := alpha c d) (z := E6DependentDualSeven.s 5)
    hTF (alpha_root c d) hr (hs 5) hneg s5_axis
  have htrans : rCD c d E6DependentDualSeven.tU =
      E6DependentDualSeven.tU - root c d := by
    simp [rCD, Module.reflection_apply, alpha_axis]
  have h' : E6DependentDualSeven.tU - root c d = E6DependentDualSeven.tU := by
    rw [← htrans]
    exact hfix
  have hnegroot : -root c d = 0 := by
    have := congrArg (fun x : V7 => x - E6DependentDualSeven.tU) h'
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  exact root_ne_zero c d (neg_eq_zero.mp hnegroot)

lemma noTF_sum_one (c d : K) (h : c + d = 1)
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, E6DependentDualSeven.s i ∈ H)
    (hr : rCD c d ∈ H) : False :=
  noTF_of_word (rCD c d) H hTF hs hr (wordProdR_sum_one_eq_T c d h)

theorem no_transvectionFree_subgroup_at72
    (c d : K)
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, E6DependentDualSeven.s i ∈ H)
    (hr : rCD c d ∈ H) : False := by
  by_cases h0 : c + d = 0
  · exact noTF_sum_zero c d h0 H hTF hs hr
  · by_cases h2 : c + d = 2
    · exact noTF_sum_two c d h2 H hTF hs hr
    · have h1 : c + d = 1 := by
        have hcases : ∀ x : K, x = 0 ∨ x = 1 ∨ x = 2 := by decide
        rcases hcases (c + d) with h' | h' | h'
        · exact absurd h' h0
        · exact h'
        · exact absurd h' h2
      exact noTF_sum_one c d h1 H hTF hs hr

end CFSG.StandardType.E6DependentDualSeven.At72

namespace CFSG.StandardType.E6DependentDualSeven.At72AxisZero

open Module
open E6DependentDualSeven

@[expose] def alpha0 (c d : K) : Module.Dual K V7 :=
  c • coord (0 : Fin 7) + (2 * c) • coord (2 : Fin 7) +
    c • coord (4 : Fin 7) + d • coord (5 : Fin 7)

@[expose] def u72 : Fin 6 → K := ![0, 0, 0, 0, 1, 1]

@[expose] def vT (t : K) : V7 := Fin.snoc u72 t

lemma alpha0_vT (c d t : K) (h : c + d = 2) : alpha0 c d (vT t) = 2 := by
  simp [alpha0, vT, u72, coord]
  linear_combination h

@[expose] noncomputable def r0 (c d t : K) (h : c + d = 2) : V7 ≃ₗ[K] V7 :=
  Module.reflection (alpha0_vT c d t h)

@[expose] noncomputable def codeA (c d t : K) (h : c + d = 2) (a : Fin 7) : V7 ≃ₗ[K] V7 :=
  if ha : a.val < 6 then s ⟨a.val, ha⟩ else r0 c d t h

@[expose] noncomputable def wordA (c d t : K) (h : c + d = 2) (L : List (Fin 7)) : V7 ≃ₗ[K] V7 :=
  (L.reverse.map (codeA c d t h)).prod

@[expose] noncomputable def wordLinA (c d t : K) (h : c + d = 2) (L : List (Fin 7)) : V7 →ₗ[K] V7 :=
  (wordA c d t h L : V7 →ₗ[K] V7)

@[expose] def kF : Module.Dual K V7 :=
  (2 : K) • coord (0 : Fin 7) + coord (2 : Fin 7) +
    (2 : K) • coord (4 : Fin 7) + coord (5 : Fin 7)

@[expose] def e5F : Module.Dual K V7 := coord (5 : Fin 7)

lemma kF_axis : kF tU = 0 := by
  simp [kF, tU, coord]

lemma e5F_axis : e5F tU = 0 := by
  simp [e5F, tU, coord]

lemma kF_ne_zero : kF ≠ 0 := by
  intro h
  have h1 : kF (Pi.single (0 : Fin 7) 1) = 0 := by rw [h]; rfl
  simp [kF, coord] at h1
  exact (by decide : (2 : K) ≠ 0) h1

lemma e5F_ne_zero : e5F ≠ 0 := by
  intro h
  have h1 : e5F (Pi.single (5 : Fin 7) 1) = 0 := by rw [h]; rfl
  simp [e5F, coord] at h1

lemma check_1_1_0 :
    ∀ k : Fin 7,
      (wordLinA 1 1 0 (by decide) [5, 6]) (Pi.single k 1) =
        (Pi.single k 1 : V7) + kF (Pi.single k 1) • vT 0 := by
  decide +kernel

lemma check_2_0_0 :
    ∀ k : Fin 7,
      (wordLinA 2 0 0 (by decide) [5, 6]) (Pi.single k 1) =
        (Pi.single k 1 : V7) + ((2 : K) • kF) (Pi.single k 1) • vT 0 := by
  decide +kernel

lemma check_0_2_1 :
    ∀ k : Fin 7,
      (wordLinA 0 2 1 (by decide) [5, 6]) (Pi.single k 1) =
        (Pi.single k 1 : V7) + ((2 : K) • e5F) (Pi.single k 1) • tU := by
  decide +kernel

lemma check_0_2_2 :
    ∀ k : Fin 7,
      (wordLinA 0 2 2 (by decide) [5, 6]) (Pi.single k 1) =
        (Pi.single k 1 : V7) + e5F (Pi.single k 1) • tU := by
  decide +kernel

@[expose] def hardCodes1 : List (Fin 7) :=
  [2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 5, 4, 3, 1, 2, 0, 3, 2, 5, 1,
   3, 4, 6, 5, 4, 3, 1, 5, 3, 4, 6, 5, 4, 3, 4, 6, 5, 4]

@[expose] def hardCodes2 : List (Fin 7) :=
  [5, 0, 2, 3, 4, 6, 5, 4, 3, 2, 0, 5, 5, 2, 3, 4, 6, 5,
   4, 3, 2, 5, 3, 4, 6, 5, 4, 3, 4, 6, 5, 4]

lemma check_1_1_1 :
    ∀ k : Fin 7,
      (wordLinA 1 1 1 (by decide) hardCodes1) (Pi.single k 1) =
        (Pi.single k 1 : V7) + kF (Pi.single k 1) • tU := by
  decide +kernel

lemma check_2_0_1 :
    ∀ k : Fin 7,
      (wordLinA 2 0 1 (by decide) hardCodes1) (Pi.single k 1) =
        (Pi.single k 1 : V7) + kF (Pi.single k 1) • tU := by
  decide +kernel

lemma check_1_1_2 :
    ∀ k : Fin 7,
      (wordLinA 1 1 2 (by decide) hardCodes2) (Pi.single k 1) =
        (Pi.single k 1 : V7) + kF (Pi.single k 1) • tU := by
  decide +kernel

lemma check_2_0_2 :
    ∀ k : Fin 7,
      (wordLinA 2 0 2 (by decide) hardCodes2) (Pi.single k 1) =
        (Pi.single k 1 : V7) + kF (Pi.single k 1) • tU := by
  decide +kernel

lemma vT_ne_zero (t : K) : vT t ≠ 0 := by
  intro h
  have h4 := congrArg (fun v : V7 => v (4 : Fin 7)) h
  simp [vT, u72] at h4

lemma kF_vT (t : K) : kF (vT t) = 0 := by
  simp [kF, vT, u72, coord]
  decide

lemma isTransvection_of_basis (e : V7 ≃ₗ[K] V7) (ψ : Module.Dual K V7) (u : V7)
    (hu : u ≠ 0) (hψ : ψ ≠ 0) (hψu : ψ u = 0)
    (h : ∀ k : Fin 7, e (Pi.single k 1) = Pi.single k 1 + ψ (Pi.single k 1) • u) :
    QTwoLin.IsTransvectionLin e := by
  refine ⟨u, ψ, hu, hψ, hψu, fun v => ?_⟩
  have hlin : (e : V7 →ₗ[K] V7) = LinearMap.id + ψ.smulRight u := by
    apply (Pi.basisFun K (Fin 7)).ext
    intro k
    rw [Pi.basisFun_apply]
    simpa [LinearMap.add_apply, LinearMap.smulRight_apply] using h k
  have hv := congrArg (fun f : V7 →ₗ[K] V7 => f v) hlin
  simpa [LinearMap.add_apply, LinearMap.smulRight_apply] using hv

lemma isTransvection_1_1_0 :
    QTwoLin.IsTransvectionLin (wordA 1 1 0 (by decide) [5, 6]) :=
  isTransvection_of_basis _ kF (vT 0) (vT_ne_zero 0) kF_ne_zero (kF_vT 0)
    check_1_1_0

lemma isTransvection_2_0_0 :
    QTwoLin.IsTransvectionLin (wordA 2 0 0 (by decide) [5, 6]) :=
  isTransvection_of_basis _ ((2 : K) • kF) (vT 0) (vT_ne_zero 0)
    (fun h => kF_ne_zero ((smul_eq_zero.mp h).resolve_left (by decide : (2 : K) ≠ 0)))
    (by simp [kF_vT 0]) check_2_0_0

lemma isTransvection_0_2_1 :
    QTwoLin.IsTransvectionLin (wordA 0 2 1 (by decide) [5, 6]) :=
  isTransvection_of_basis _ ((2 : K) • e5F) tU tU_ne_zero
    (fun h => e5F_ne_zero ((smul_eq_zero.mp h).resolve_left (by decide : (2 : K) ≠ 0)))
    (by simp [e5F_axis]) check_0_2_1

lemma isTransvection_0_2_2 :
    QTwoLin.IsTransvectionLin (wordA 0 2 2 (by decide) [5, 6]) :=
  isTransvection_of_basis _ e5F tU tU_ne_zero e5F_ne_zero e5F_axis check_0_2_2

lemma isTransvection_1_1_1 :
    QTwoLin.IsTransvectionLin (wordA 1 1 1 (by decide) hardCodes1) :=
  isTransvection_of_basis _ kF tU tU_ne_zero kF_ne_zero kF_axis check_1_1_1

lemma isTransvection_2_0_1 :
    QTwoLin.IsTransvectionLin (wordA 2 0 1 (by decide) hardCodes1) :=
  isTransvection_of_basis _ kF tU tU_ne_zero kF_ne_zero kF_axis check_2_0_1

lemma isTransvection_1_1_2 :
    QTwoLin.IsTransvectionLin (wordA 1 1 2 (by decide) hardCodes2) :=
  isTransvection_of_basis _ kF tU tU_ne_zero kF_ne_zero kF_axis check_1_1_2

lemma isTransvection_2_0_2 :
    QTwoLin.IsTransvectionLin (wordA 2 0 2 (by decide) hardCodes2) :=
  isTransvection_of_basis _ kF tU tU_ne_zero kF_ne_zero kF_axis check_2_0_2

lemma wordA_mem {c d t : K} (hcd : c + d = 2)
    {H : Subgroup (V7 ≃ₗ[K] V7)}
    (hs : ∀ i : Fin 6, E6DependentDualSeven.s i ∈ H)
    (hr : r0 c d t hcd ∈ H) (L : List (Fin 7)) :
    wordA c d t hcd L ∈ H := by
  have hcode : ∀ a : Fin 7, codeA c d t hcd a ∈ H := by
    intro a
    fin_cases a
    · simpa [codeA] using hs 0
    · simpa [codeA] using hs 1
    · simpa [codeA] using hs 2
    · simpa [codeA] using hs 3
    · simpa [codeA] using hs 4
    · simpa [codeA] using hs 5
    · simpa [codeA] using hr
  unfold wordA
  refine H.toSubmonoid.list_prod_mem ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact hcode a

lemma r0_zero_two_zero_eq_s5 : r0 0 2 0 (by decide) = E6DependentDualSeven.s 5 := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 7)).ext
  intro k
  rw [Pi.basisFun_apply]
  decide +kernel +revert

theorem no_transvectionFree_axis_zero
    (c d t : K) (hcd : c + d = 2)
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, E6DependentDualSeven.s i ∈ H)
    (hself : alpha0 c d (vT t) = 2)
    (hr : Module.reflection hself ∈ H) :
    c = 0 ∧ d = 2 ∧ t = 0 := by
  have hcases : ∀ x : K, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hr0 : r0 c d t hcd ∈ H := by
    unfold r0
    rw [← Subsingleton.elim hself (alpha0_vT c d t hcd)]
    exact hr
  by_cases hc : c = 0
  · by_cases ht : t = 0
    · refine ⟨hc, ?_, ht⟩
      subst hc
      simpa using hcd
    · exfalso
      subst hc
      have hd : d = 2 := by simpa using hcd
      subst hd
      rcases hcases t with rfl | rfl | rfl
      · exact absurd rfl ht
      · rw [show hcd = (by decide : (0 : K) + 2 = 2) from Subsingleton.elim _ _] at hr0
        exact hTF _ (wordA_mem (by decide) hs hr0 [5, 6]) isTransvection_0_2_1
      · rw [show hcd = (by decide : (0 : K) + 2 = 2) from Subsingleton.elim _ _] at hr0
        exact hTF _ (wordA_mem (by decide) hs hr0 [5, 6]) isTransvection_0_2_2
  · by_cases ht : t = 0
    · exfalso
      subst ht
      rcases hcases c with rfl | rfl | rfl
      · exact absurd rfl hc
      · have hd : d = 1 := by linear_combination hcd
        subst hd
        rw [show hcd = (by decide : (1 : K) + 1 = 2) from Subsingleton.elim _ _] at hr0
        exact hTF _ (wordA_mem (by decide) hs hr0 [5, 6]) isTransvection_1_1_0
      · have hd : d = 0 := by linear_combination hcd
        subst hd
        rw [show hcd = (by decide : (2 : K) + 0 = 2) from Subsingleton.elim _ _] at hr0
        exact hTF _ (wordA_mem (by decide) hs hr0 [5, 6]) isTransvection_2_0_0
    · exfalso
      rcases hcases c with rfl | rfl | rfl
      · exact absurd rfl hc
      · rcases hcases t with rfl | rfl | rfl
        · exact absurd rfl ht
        · have hd : d = 1 := by linear_combination hcd
          subst hd
          rw [show hcd = (by decide : (1 : K) + 1 = 2) from Subsingleton.elim _ _] at hr0
          exact hTF _ (wordA_mem (by decide) hs hr0 hardCodes1) isTransvection_1_1_1
        · have hd : d = 1 := by linear_combination hcd
          subst hd
          rw [show hcd = (by decide : (1 : K) + 1 = 2) from Subsingleton.elim _ _] at hr0
          exact hTF _ (wordA_mem (by decide) hs hr0 hardCodes2) isTransvection_1_1_2
      · rcases hcases t with rfl | rfl | rfl
        · exact absurd rfl ht
        · have hd : d = 0 := by linear_combination hcd
          subst hd
          rw [show hcd = (by decide : (2 : K) + 0 = 2) from Subsingleton.elim _ _] at hr0
          exact hTF _ (wordA_mem (by decide) hs hr0 hardCodes1) isTransvection_2_0_1
        · have hd : d = 0 := by linear_combination hcd
          subst hd
          rw [show hcd = (by decide : (2 : K) + 0 = 2) from Subsingleton.elim _ _] at hr0
          exact hTF _ (wordA_mem (by decide) hs hr0 hardCodes2) isTransvection_2_0_2

end CFSG.StandardType.E6DependentDualSeven.At72AxisZero
