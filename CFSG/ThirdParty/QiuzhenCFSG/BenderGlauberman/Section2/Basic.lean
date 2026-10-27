module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.DihedralStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunctionHelpers
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Congruence
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import Mathlib.GroupTheory.PGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 2 setup and the general situation

The structure of `S0`, `t`, `s` under Hypothesis 1.1 and the `λ2`/`κ1`
machinery.  The coherence cluster (`CoherenceData`, `tildeNu`, `BOf`) and
the statements of Lemma 2.2, Lemma 2.4 and Lemma 2.5 live in
`Section2/Coherence.lean`, `Section2/Lemma22.lean`, `Section2/Lemma24.lean`
and `Section2/Lemma25.lean` respectively.
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

section Section2

variable {G : Type u} [Group G] [Fintype G]

/-- For an element `t` with `t² = 1`, every character of the dual group takes
the value `±1` at `t`. -/
private lemma lambda_sq_eq_one (H0 U : Subgroup G) (t : ↥H0) (ht_sq : t ^ 2 = 1)
    (l : LambdaHom H0 U) : (l.1 t : ℂ) ^ 2 = 1 := by
  have hsq : (l.1 t) ^ 2 = 1 := by
    calc
      (l.1 t) ^ 2 = l.1 (t ^ 2) := by rw [map_pow]
      _ = 1 := by
        rw [ht_sq]
        simp
  simpa using (congrArg (fun u : ℂˣ => (u : ℂ)) hsq)

/-- When `t ∉ U` and `t² = 1`, some dual character takes the value `-1` at `t`. -/
private lemma exists_lambda_neg_one (H0 U : Subgroup G)
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    {t : ↥H0} (ht_not_U : (t : G) ∉ U) (ht_sq : t ^ 2 = 1) :
    ∃ l : LambdaHom H0 U, (l.1 t : ℂ) = -1 := by
  rcases LambdaHom_separates H0 U hK hcomm t ht_not_U with ⟨l, hl⟩
  have hsq : (l.1 t : ℂ) ^ 2 = 1 := lambda_sq_eq_one H0 U t ht_sq l
  have hcases : (l.1 t : ℂ) = 1 ∨ (l.1 t : ℂ) = -1 := by
    rw [← sq_eq_one_iff]
    exact hsq
  rcases hcases with h1 | hm1
  · exfalso
    exact hl (Units.ext h1)
  · exact ⟨l, hm1⟩

/-- The two fibers of the evaluation `λ ↦ λ(t)` over `±1` have equal size
(they are cosets of each other), when `t ∉ U` and `t² = 1`. -/
private lemma lambdaOne_fiber_card (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    {t : ↥H0} (ht_not_U : (t : G) ∉ U) (ht_sq : t ^ 2 = 1) :
    (Finset.univ.filter (fun l : LambdaHom H0 U => (l.1 t : ℂ) = -1)).card =
      (Finset.univ.filter (fun l : LambdaHom H0 U => (l.1 t : ℂ) = 1)).card := by
  classical
  rcases exists_lambda_neg_one H0 U hK hcomm ht_not_U ht_sq with ⟨l₀, hl₀⟩
  refine Finset.card_bij (fun k hk => l₀ * k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    simp [hk, hl₀]
  · intro a₁ ha₁ a₂ ha₂ hEq
    exact mul_left_cancel hEq
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    refine ⟨l₀⁻¹ * l, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp [hl, hl₀]
    · simp

/-- The subgroup `Λ₁ = {λ ∈ Λ | λ(t) = 1}` has exactly half the size of `Λ`,
i.e. `2·|Λ₁| = |Λ|`, when `t ∉ U` and `t² = 1`. -/
private lemma lambdaOne_card_mul_two (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    {t : ↥H0} (ht_not_U : (t : G) ∉ U) (ht_sq : t ^ 2 = 1) :
    (Finset.univ.filter (fun l : LambdaHom H0 U => (l.1 t : ℂ) = 1)).card * 2 =
      Fintype.card (LambdaHom H0 U) := by
  classical
  let A := Finset.univ.filter (fun l : LambdaHom H0 U => (l.1 t : ℂ) = 1)
  let B := Finset.univ.filter (fun l : LambdaHom H0 U => (l.1 t : ℂ) = -1)
  have hpart : Finset.univ = A ∪ B := by
    ext l
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_filter, true_and, A, B]
    rw [← sq_eq_one_iff]
    exact lambda_sq_eq_one H0 U t ht_sq l
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hEq
    have ha1 : (a.1 t : ℂ) = 1 := (Finset.mem_filter.mp ha).2
    have hb1 : (b.1 t : ℂ) = -1 := (Finset.mem_filter.mp hb).2
    have hne : (1 : ℂ) ≠ -1 := by norm_num
    exact hne (ha1.symm.trans (by simpa [← hEq] using hb1))
  have hB : B.card = A.card := lambdaOne_fiber_card H0 U hK hcomm ht_not_U ht_sq
  have hsum : A.card + B.card = Fintype.card (LambdaHom H0 U) := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hpart]
    simp
  rw [hB] at hsum
  simpa [mul_two, A] using hsum

/-- The identity always stabilizes `ν`. -/
public lemma one_mem_stab (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) :
    (1 : LambdaHom H0 U) ∈ Finset.univ.filter
      (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν) := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : LambdaChar (1 : ↥(LambdaHom H0 U)).1 = (1 : ClassFunction (↥H0)) := by
    ext x
    simp [LambdaChar]
  rw [h1, one_mul]

/-- `|orbit| · |Stab ν| = |Λ|` — the orbit of `ν` decomposes into equal
`|Stab ν|`-sized fibers of the orbit map `λ ↦ λ·ν`. -/
public lemma orbit_card_mul_stab (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) :
    (orbit H0 U ν).card *
        (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card =
      Fintype.card (LambdaHom H0 U) := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun l : LambdaHom H0 U => LambdaChar l.1 * ν)
    (s := Finset.univ) (t := orbit H0 U ν)
    (by intro l _; exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)
  calc
    (orbit H0 U ν).card *
        (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card =
      ∑ μ ∈ orbit H0 U ν,
        (Finset.univ.filter (fun l : LambdaHom H0 U => LambdaChar l.1 * ν = μ)).card := by
          rw [Finset.sum_congr rfl (fun μ hμ => orbit_fiber_card H0 U ν μ hμ)]
          rw [← Finset.sum_const_nat (fun μ hμ => rfl)]
    _ = (Finset.univ : Finset (LambdaHom H0 U)).card := by
          rw [← hfib]
    _ = Fintype.card (LambdaHom H0 U) := by simp

/-- Counting the `P`-preimage of the orbit: every orbit element is hit
`|Stab ν|` times, so `|{λ : P(λ·ν)}| = |orbit.filter P| · |Stab ν|`. -/
private lemma orbit_filter_preimage_card (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (ν : ClassFunction (↥H0)) (P : ClassFunction (↥H0) → Prop) :
    (Finset.univ.filter (fun l : LambdaHom H0 U => P (LambdaChar l.1 * ν))).card =
      ((orbit H0 U ν).filter P).card *
        (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card := by
  classical
  have hpre : Finset.univ.filter (fun l : LambdaHom H0 U => P (LambdaChar l.1 * ν)) =
      Finset.univ.filter (fun l : LambdaHom H0 U =>
        LambdaChar l.1 * ν ∈ (orbit H0 U ν).filter P) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hP
      exact ⟨Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩, hP⟩
    · intro h
      exact h.2
  calc
    (Finset.univ.filter (fun l : LambdaHom H0 U => P (LambdaChar l.1 * ν))).card
        = (Finset.univ.filter (fun l : LambdaHom H0 U =>
            LambdaChar l.1 * ν ∈ (orbit H0 U ν).filter P)).card := by rw [hpre]
    _ = ∑ μ ∈ (orbit H0 U ν).filter P,
          (Finset.univ.filter (fun l : LambdaHom H0 U => LambdaChar l.1 * ν = μ)).card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter]
    _ = ((orbit H0 U ν).filter P).card *
          (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card := by
          calc
            ∑ μ ∈ (orbit H0 U ν).filter P,
                (Finset.univ.filter (fun l : LambdaHom H0 U => LambdaChar l.1 * ν = μ)).card
                = ∑ μ ∈ (orbit H0 U ν).filter P,
                    (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card := by
                    refine Finset.sum_congr rfl ?_
                    intro μ hμ
                    exact orbit_fiber_card H0 U ν μ (Finset.mem_of_mem_filter μ hμ)
            _ = ((orbit H0 U ν).filter P).card *
                  (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card := by
                  rw [Finset.sum_const_nat (fun μ hμ => rfl)]

/-- Lemma 2.1(i): exactly half of the characters in the `Λ`-orbit of an
irreducible character `ν` of `H0` have `t` in their kernel.
Here `t` is a central involution of `H0` outside `U`. -/
public theorem lemma_2_1_a (H0 U : Subgroup G) [Fintype ↥(LambdaHom H0 U)]
    (hK : (U.subgroupOf H0).Normal)
    (hcomm : ∀ x y : ↥H0, (x * y) / (y * x) ∈ U.subgroupOf H0)
    {t : ↥H0} (ht_not_U : (t : G) ∉ U) (ht_sq : t ^ 2 = 1)
    (ht_central : ∀ x : ↥H0, t * x = x * t)
    {ν : ClassFunction (↥H0)} (hν : IsIrreducibleCharacter ν) :
    ((orbit H0 U ν).filter (fun μ => μ t = μ 1)).card * 2 = (orbit H0 U ν).card := by
  classical
  let P : ClassFunction (↥H0) → Prop := fun μ => μ t = μ 1
  change ((orbit H0 U ν).filter P).card * 2 = (orbit H0 U ν).card
  let A := Finset.univ.filter (fun l : LambdaHom H0 U => (l.1 t : ℂ) = 1)
  let B := Finset.univ.filter (fun l : LambdaHom H0 U => (l.1 t : ℂ) = -1)
  let pre := Finset.univ.filter (fun l : LambdaHom H0 U => P (LambdaChar l.1 * ν))
  let stabCard := (Finset.univ.filter (fun s : LambdaHom H0 U => LambdaChar s.1 * ν = ν)).card
  have hA2 : A.card * 2 = Fintype.card (LambdaHom H0 U) :=
    lambdaOne_card_mul_two H0 U hK hcomm ht_not_U ht_sq
  have hOrbit : (orbit H0 U ν).card * stabCard = Fintype.card (LambdaHom H0 U) :=
    orbit_card_mul_stab H0 U ν
  have hpre_card : pre.card = ((orbit H0 U ν).filter P).card * stabCard := by
    simpa [pre, stabCard] using orbit_filter_preimage_card H0 U ν P
  have hstab_ne : stabCard ≠ 0 := by
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, one_mem_stab H0 U ν⟩)
  have htail : pre.card = A.card → ((orbit H0 U ν).filter P).card * 2 = (orbit H0 U ν).card := by
    intro hpreCard
    have hstep : ((orbit H0 U ν).filter P).card * stabCard * 2 =
        (orbit H0 U ν).card * stabCard := by
      calc
        ((orbit H0 U ν).filter P).card * stabCard * 2 = pre.card * 2 := by rw [← hpre_card]
        _ = A.card * 2 := by rw [hpreCard]
        _ = Fintype.card (LambdaHom H0 U) := hA2
        _ = (orbit H0 U ν).card * stabCard := by rw [← hOrbit]
    have hstep' : ((orbit H0 U ν).filter P).card * 2 * stabCard =
        (orbit H0 U ν).card * stabCard := by
      rw [← hstep]
      ac_rfl
    exact mul_right_cancel₀ hstab_ne hstep'
  have hsign := char_apply_central_sign ht_central ht_sq hν
  have hν1ne : ν 1 ≠ 0 := irreducible_char_one_ne_zero hν
  rcases hsign with hpos | hneg
  · have hpreA : pre = A := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pre, A, P, LambdaChar,
        Pi.mul_apply, map_one, Units.val_one, one_mul, hpos]
      constructor
      · intro h
        have hsub : ((l.1 t : ℂ) - 1) * ν 1 = 0 := by
          rw [sub_mul, h, one_mul]
          ring
        exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hν1ne)
      · intro h
        rw [h]
        simp
    exact htail (by rw [hpreA])
  · have hpreB : pre = B := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pre, B, P, LambdaChar,
        Pi.mul_apply, map_one, Units.val_one, one_mul, hneg]
      constructor
      · intro h
        have h' : (l.1 t : ℂ) * ν 1 = -ν 1 := neg_eq_iff_eq_neg.mp (by simpa [mul_neg] using h)
        have hsum : ((l.1 t : ℂ) + 1) * ν 1 = 0 := by
          rw [add_mul, one_mul, h']
          ring
        exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hsum).resolve_right hν1ne)
      · intro h
        rw [h]
        ring
    exact htail (by rw [hpreB, lambdaOne_fiber_card H0 U hK hcomm ht_not_U ht_sq])

/-- `s` normalizes `U = O(H)` (the odd core is characteristic in `H`). -/
public lemma s_normalizes_U (c : Hyp11 G) {u : G} (hu : u ∈ c.U) :
    c.s * u * c.s⁻¹ ∈ c.U := by
  have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hu
  have huH : u ∈ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
  have hsH : c.s ∈ c.H := s_mem_H c
  have hchar : (pPrimeCore 2 c.H).Characteristic :=
    pPrimeCore_characteristic (p := 2) (G := c.H)
  have hcomap : (pPrimeCore 2 c.H) ≤ (pPrimeCore 2 c.H).comap
      (MulAut.conj ⟨c.s, hsH⟩).toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) (MulAut.conj ⟨c.s, hsH⟩)
  have huK : (⟨u, huH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
    rcases (Subgroup.mem_map.mp huU) with ⟨x, hx, hxeq⟩
    have hxeq' : (⟨u, huH⟩ : ↥c.H) = x := by
      ext
      simpa using hxeq.symm
    simpa [hxeq'] using hx
  have hconj : (MulAut.conj ⟨c.s, hsH⟩) ⟨u, huH⟩ ∈ pPrimeCore 2 c.H :=
    Subgroup.mem_comap.mp (hcomap huK)
  refine (Subgroup.mem_map.mpr ?_)
  refine ⟨⟨c.s * u * c.s⁻¹, c.H.mul_mem (c.H.mul_mem hsH huH) (c.H.inv_mem hsH)⟩, ?_, rfl⟩
  have hcx : (MulAut.conj ⟨c.s, hsH⟩) ⟨u, huH⟩ =
      (⟨c.s * u * c.s⁻¹, c.H.mul_mem (c.H.mul_mem hsH huH) (c.H.inv_mem hsH)⟩ : ↥c.H) := by
    ext
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hcx]
  exact hconj

/-- `s` normalizes `H0` (from `H0 ⊴ H` and `s ∈ H`). -/
public lemma s_normalizes_H0 (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : ↥c.H0, c.s * (x : G) * c.s⁻¹ ∈ c.H0 := fun x =>
  (h12.H0_normal_in_H).2 c.s (s_mem_H c) (x : G) x.2

open DihedralGroup

/-- In the dihedral model `D_n` (`n = 2^m`), any element outside the rotation
subgroup `⟨r 1⟩` inverts every rotation. -/
private lemma dihedral_conj_rotate_inv (n : ℕ) [NeZero n] {w x : DihedralGroup n}
    (hw : w ∉ Subgroup.zpowers (r 1 : DihedralGroup n))
    (hx : x ∈ Subgroup.zpowers (r 1 : DihedralGroup n)) :
    w * x * w⁻¹ = x⁻¹ := by
  rcases x with ⟨b⟩ | ⟨b⟩
  · -- x = r b
    rcases w with ⟨i⟩ | ⟨i⟩
    · -- w = r i ∈ ⟨r 1⟩: contradiction
      exfalso
      exact hw (by
        refine (Subgroup.mem_zpowers_iff).2 ?_
        refine ⟨(i.val : ℤ), ?_⟩
        rw [r_one_zpow]
        congr 1
        simp)
    · -- w = sr i inverts r b
      rw [sr_mul_r, inv_sr, sr_mul_sr, inv_r]
      congr 1
      abel
  · -- x = sr b ∉ ⟨r 1⟩: contradiction
    have hnot : sr b ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
      intro h
      rcases (Subgroup.mem_zpowers_iff.mp h) with ⟨k, hk⟩
      rw [r_one_zpow] at hk
      cases hk
    exfalso
    exact hnot hx

/-- For `m ≥ 2`, the image of `S0` in the dihedral model is the rotation
subgroup `⟨r 1⟩`. -/
private lemma eS0_eq_zpowers_r1 (c : Hyp11 G) (hm2 : 2 ≤ c.m)
    (e : ↥(c.S : Subgroup G) ≃* DihedralGroup (2 ^ c.m)) :
    (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
        (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) =
      Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
  have : NeZero (2 ^ c.m) := ⟨pow_ne_zero c.m (by norm_num)⟩
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  rcases IsCyclic.exists_generator (α := ↥(c.S0 : Subgroup G)) with ⟨g, hg⟩
  have hgorder : orderOf g = 2 ^ c.m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, S0_nat_card c]
  have hgorder4 : 4 ≤ orderOf g := by
    rw [hgorder]
    exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm2
  have hegr : ∃ a : ZMod (2 ^ c.m), e (Subgroup.inclusion c.S0_le_S g) = r a := by
    rcases h : e (Subgroup.inclusion c.S0_le_S g) with ⟨a⟩ | ⟨a⟩
    · exact ⟨a, rfl⟩
    · exfalso
      have hord : orderOf (e (Subgroup.inclusion c.S0_le_S g)) = 2 ^ c.m := by
        rw [MulEquiv.orderOf_eq e]
        rw [orderOf_injective (Subgroup.inclusion c.S0_le_S)
          (Subgroup.inclusion_injective c.S0_le_S) g]
        exact hgorder
      have h2 : (2 : ℕ) = 2 ^ c.m := by
        calc
          2 = orderOf (sr a : DihedralGroup (2 ^ c.m)) := by rw [orderOf_sr]
          _ = orderOf (e (Subgroup.inclusion c.S0_le_S g)) := by rw [h]
          _ = 2 ^ c.m := hord
      omega
  have hsub : (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
      (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) ≤
      Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
    intro y hy
    rcases (Subgroup.mem_map.mp hy) with ⟨x, hx, rfl⟩
    rcases (Subgroup.mem_zpowers_iff.mp (hg x)) with ⟨k, hk⟩
    rcases hegr with ⟨a, hega⟩
    have hcast : (((a * (k : ZMod (2 ^ c.m))).val : ℤ) : ZMod (2 ^ c.m)) =
        a * (k : ZMod (2 ^ c.m)) := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_zmod_val (a * (k : ZMod (2 ^ c.m)))
    refine (Subgroup.mem_zpowers_iff).2 ?_
    refine ⟨((a * (k : ZMod (2 ^ c.m))).val : ℤ), ?_⟩
    rw [r_one_zpow]
    rw [hcast]
    rw [← r_zpow]
    rw [← hega]
    have hmp : e ((Subgroup.inclusion c.S0_le_S g) ^ k) =
        (e (Subgroup.inclusion c.S0_le_S g)) ^ k := by
      simp
    rw [← hmp]
    rw [← (Subgroup.inclusion c.S0_le_S).map_zpow]
    rw [hk]
    simp [MulEquiv.toMonoidHom_eq_coe]
  apply le_antisymm
  · exact hsub
  · -- |⟨r 1⟩| = 2^m ≤ 2^m = |K₀|
    have hcard : Nat.card (Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m))) ≤
        Nat.card ((⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
          (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S))) := by
      rw [Nat.card_zpowers, orderOf_r_one]
      rw [Subgroup.card_map_of_injective (f := e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S))
        (by
          intro a b hab
          exact (Subgroup.inclusion_injective c.S0_le_S) (e.injective (by simpa using hab)))]
      rw [Subgroup.card_top, S0_nat_card c]
    exact (Subgroup.eq_of_le_of_card_ge hsub hcard).ge

/-- `s` inverts every element of `S0` (dihedral structure of `S`). -/
private lemma s_inverts_S0 (c : Hyp11 G) {x : G} (hx : x ∈ (c.S0 : Subgroup G)) :
    c.s * x * c.s⁻¹ = x⁻¹ := by
  by_cases hm1 : c.m = 1
  · -- m = 1: |S0| = 2, so x = 1 or x = t
    have hcard : Fintype.card ↥(c.S0 : Subgroup G) = 2 := by
      rw [← Nat.card_eq_fintype_card, S0_nat_card c, hm1]
      norm_num
    have hpow : (⟨x, hx⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
      have h := pow_card_eq_one (G := ↥(c.S0 : Subgroup G)) (x := ⟨x, hx⟩)
      simpa [hcard] using h
    rcases (S0_sq_eq_one_iff c (x := ⟨x, hx⟩)).1 hpow with h1 | ht
    · have hx1 : x = 1 := by simpa using (Subtype.ext_iff.mp h1)
      simp [hx1]
    · have hxt : x = c.t := by simpa using (Subtype.ext_iff.mp ht)
      rw [hxt]
      rw [s_conj_t c]
      have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
      rw [inv_eq_of_mul_eq_one_left ht2]
  · -- m ≥ 2: transport through the dihedral model
    have hm2 : 2 ≤ c.m := by
      exact Nat.succ_le_of_lt (lt_of_le_of_ne c.one_le_m (Ne.symm hm1))
    let e : ↥(c.S : Subgroup G) ≃* DihedralGroup (2 ^ c.m) := Classical.choice c.dihedralEquiv
    have heq : (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
        (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) =
        Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) :=
      eS0_eq_zpowers_r1 c hm2 e
    let xS : ↥(c.S : Subgroup G) := ⟨x, c.S0_le_S hx⟩
    let sS : ↥(c.S : Subgroup G) := ⟨c.s, c.s_mem_S⟩
    have hxS : e xS ∈ Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
      rw [← heq]
      refine (Subgroup.mem_map).2 ?_
      refine ⟨⟨x, hx⟩, by simp, ?_⟩
      rfl
    have hsS : e sS ∉ Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
      intro h
      rw [← heq] at h
      rcases (Subgroup.mem_map.mp h) with ⟨y, hy, hyeq⟩
      have hys : (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) y = e sS := hyeq
      have hι : Subgroup.inclusion c.S0_le_S y = sS := e.injective hys
      have hyG : (y : G) = c.s := by
        exact (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hι)
      apply c.s_not_mem_S0
      rw [← hyG]
      exact y.2
    have hmain : e (sS * xS * sS⁻¹) = e (xS⁻¹) := by
      have hM := dihedral_conj_rotate_inv (n := 2 ^ c.m) (w := e sS) hsS hxS
      calc
        e (sS * xS * sS⁻¹) = e sS * e xS * (e sS)⁻¹ := by simp [map_mul, map_inv]
        _ = (e xS)⁻¹ := hM
        _ = e (xS⁻¹) := by simp [map_inv]
    have hS : sS * xS * sS⁻¹ = xS⁻¹ := e.injective hmain
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
      (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hS)

/-- `S0 ≤ H0`. -/
public lemma S0_le_H0 (c : Hyp11 G) : (c.S0 : Subgroup G) ≤ c.H0 := by
  intro y hy
  exact SetLike.le_def.mp le_sup_right hy

/-- `S0` normalizes `U` (from `U ⊴ H0` and `S0 ≤ H0`). -/
private lemma S0_le_normalizer_U (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.S0 : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact (h12.U_normal_in_H0).2 r (S0_le_H0 c hr) u hu
  · intro hru
    have hr' : r⁻¹ ∈ c.H0 := c.H0.inv_mem (S0_le_H0 c hr)
    have h1 : r⁻¹ * (r * u * r⁻¹) * r⁻¹⁻¹ ∈ c.U :=
      (h12.U_normal_in_H0).2 (r⁻¹) hr' (r * u * r⁻¹) hru
    have h1' : r⁻¹ * (r * u * r⁻¹) * r ∈ c.U := by simpa using h1
    have h2 : r⁻¹ * (r * u * r⁻¹) * r = u := by group
    rwa [h2] at h1'

/-- Every element of `H0` is a product `u·r` with `u ∈ U`, `r ∈ S0`
(`H0 = U·S0`; from `S0 ≤ N_G(U)`). -/
public lemma H0_eq_U_mul_S0 (c : Hyp11 G) (h12 : Hyp12 c) {x : ↥c.H0} :
    ∃ u : ↥c.U, ∃ r : ↥c.S0, (x : G) = (u : G) * (r : G) := by
  have hset : (↑c.H0 : Set G) = (c.U : Set G) * (c.S0 : Set G) := by
    dsimp [Hyp11.H0]
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S0 : Subgroup G)
      (S0_le_normalizer_U c h12)
  have hx' : (x : G) ∈ (c.U : Set G) * (c.S0 : Set G) := by
    rw [← hset]
    exact x.2
  rcases hx' with ⟨uu, huu, rr, hrr, hEq⟩
  refine ⟨⟨uu, huu⟩, ⟨rr, hrr⟩, ?_⟩
  exact hEq.symm

/-- Conjugation by `s` inverts every element of `Λ`: `l^s = l⁻¹` on `H0`.
Uses `s`-inverting `S0`, `s` normalizing `U`, and `H0 = U·S0`. -/
private lemma lambda_conj_s_inv (c : Hyp11 G) (h12 : Hyp12 c)
    {l : ↥(LambdaHom c.H0 c.U)} (x : ↥c.H0) :
    l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) = (l.1 x)⁻¹ := by
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  let uH0 : ↥c.H0 := ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩
  let rH0 : ↥c.H0 := ⟨(r : G), S0_le_H0 c r.2⟩
  have hxeq : x = uH0 * rH0 := by
    ext
    simpa [uH0, rH0] using hx
  have hsu : (c.s * (u : G) * c.s⁻¹) ∈ c.U := s_normalizes_U c u.2
  have hsuH0 : (c.s * (u : G) * c.s⁻¹) ∈ c.H0 := (h12.U_normal_in_H0).1 hsu
  have hsr' : c.s * (r : G) * c.s⁻¹ = (r : G)⁻¹ := s_inverts_S0 c r.2
  have hsr : (c.s * (r : G) * c.s⁻¹) ∈ c.S0 := by
    rw [hsr']
    exact (c.S0 : Subgroup G).inv_mem r.2
  have hsrH0 : (c.s * (r : G) * c.s⁻¹) ∈ c.H0 := S0_le_H0 c hsr
  have hcj : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x : G) =
      (c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹) := by
    dsimp [conjMonoidHom]
    rw [hx]
    group
  have hprodH0 : (c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹) ∈ c.H0 :=
    c.H0.mul_mem hsuH0 hsrH0
  have hl_u : l.1 ⟨(c.s * (u : G) * c.s⁻¹), hsuH0⟩ = 1 :=
    l.2 ⟨(c.s * (u : G) * c.s⁻¹), hsuH0⟩ hsu
  have hl_r : l.1 ⟨(c.s * (r : G) * c.s⁻¹), hsrH0⟩ = (l.1 rH0)⁻¹ := by
    have hpair : ⟨(c.s * (r : G) * c.s⁻¹), hsrH0⟩ = rH0⁻¹ := by
      apply Subtype.ext
      change c.s * (r : G) * c.s⁻¹ = (r : G)⁻¹
      exact hsr'
    rw [hpair]
    exact map_inv l.1 rH0
  calc
    l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x)
        = l.1 ⟨(c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹), hprodH0⟩ := by
          apply congrArg l.1
          apply Subtype.ext
          exact hcj
    _ = l.1 ⟨(c.s * (u : G) * c.s⁻¹), hsuH0⟩ * l.1 ⟨(c.s * (r : G) * c.s⁻¹), hsrH0⟩ := by
          change l.1 (⟨(c.s * (u : G) * c.s⁻¹), hsuH0⟩ * ⟨(c.s * (r : G) * c.s⁻¹), hsrH0⟩) =
            l.1 ⟨(c.s * (u : G) * c.s⁻¹), hsuH0⟩ * l.1 ⟨(c.s * (r : G) * c.s⁻¹), hsrH0⟩
          exact map_mul l.1 ⟨(c.s * (u : G) * c.s⁻¹), hsuH0⟩ ⟨(c.s * (r : G) * c.s⁻¹), hsrH0⟩
    _ = 1 * (l.1 rH0)⁻¹ := by rw [hl_u, hl_r]
    _ = (l.1 rH0)⁻¹ := by rw [one_mul]
    _ = (l.1 x)⁻¹ := by
          have hlx : l.1 x = l.1 rH0 := by
            rw [hxeq]
            have hl_u' : l.1 uH0 = 1 := l.2 uH0 u.2
            simp [hl_u']
          rw [hlx]

/-- `U ⊴ H0` as a `Subgroup.Normal` statement on the subgroup-of. -/
public lemma U_normal_subgroupOf (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).Normal := by
  refine ⟨?_⟩
  intro n hn g
  apply (Subgroup.mem_subgroupOf).2
  simpa using (h12.U_normal_in_H0).2 (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.mp hn)

/-- The commutator hypothesis for `Λ` (from `H0' ≤ U`). -/
public lemma lambda_hcomm (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x y : ↥c.H0, (x * y) / (y * x) ∈ c.U.subgroupOf c.H0 := by
  intro x y
  apply (Subgroup.mem_subgroupOf).2
  have hc : (((x * y) / (y * x) : ↥c.H0) : G) = ⁅(x : G), (y : G)⁆ := by
    rw [commutatorElement_def]
    simp [div_eq_mul_inv, mul_inv_rev]
    group
  rw [hc]
  exact SetLike.le_def.mp h12.H0_comm_le_U
    (Subgroup.commutator_mem_commutator (H₁ := c.H0) (H₂ := c.H0) x.2 y.2)

/-- `t ∉ U` (the odd core `U = O(H)` has odd order). -/
public lemma t_not_mem_U (c : Hyp11 G) : (c.t : G) ∉ c.U := by
  intro ht
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hord : orderOf (⟨c.t, ht⟩ : ↥c.U) = 2 := by
    apply (orderOf_eq_prime_iff (p := 2)).mpr
    constructor
    · apply Subtype.ext
      simpa [Subgroup.coe_pow, pow_two] using c.t_involution.2
    · intro h1
      exact c.t_involution.1 (by simpa using (Subtype.ext_iff.mp h1))
  have h2dvd : 2 ∣ Fintype.card ↥c.U := by
    rw [← hord]
    exact orderOf_dvd_card (G := ↥c.U) (x := ⟨c.t, ht⟩)
  have h2dvd' : 2 ∣ Nat.card ↥c.U := by
    rwa [Nat.card_eq_fintype_card]
  exact ((Nat.prime_two.coprime_iff_not_dvd).mp hcop) h2dvd'

/-- For `l ∈ Λ` and `x = u·r` (`u ∈ U`, `r ∈ S0`): `l(x) = l(r)`. -/
private lemma lambda_eq_on_S0_part (c : Hyp11 G) (h12 : Hyp12 c)
    {l : ↥(LambdaHom c.H0 c.U)} {x : ↥c.H0} {u : ↥c.U} {r : ↥c.S0}
    (hx : (x : G) = (u : G) * (r : G)) :
    l.1 x = l.1 ⟨(r : G), S0_le_H0 c r.2⟩ := by
  let uH0 : ↥c.H0 := ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩
  let rH0 : ↥c.H0 := ⟨(r : G), S0_le_H0 c r.2⟩
  have hxeq : x = uH0 * rH0 := by
    ext
    simpa [uH0, rH0] using hx
  calc
    l.1 x = l.1 (uH0 * rH0) := by rw [hxeq]
    _ = l.1 uH0 * l.1 rH0 := by exact map_mul l.1 uH0 rH0
    _ = 1 * l.1 rH0 := by rw [l.2 uH0 u.2]
    _ = l.1 rH0 := by rw [one_mul]

/-- An element of `Λ` is determined by its values on `S0`. -/
private lemma lambda_ext_on_S0 (c : Hyp11 G) (h12 : Hyp12 c)
    {l₁ l₂ : ↥(LambdaHom c.H0 c.U)}
    (h : ∀ r : ↥c.S0, l₁.1 ⟨(r : G), S0_le_H0 c r.2⟩ = l₂.1 ⟨(r : G), S0_le_H0 c r.2⟩) :
    l₁ = l₂ := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  calc
    l₁.1 x = l₁.1 ⟨(r : G), S0_le_H0 c r.2⟩ := lambda_eq_on_S0_part c h12 hx
    _ = l₂.1 ⟨(r : G), S0_le_H0 c r.2⟩ := h r
    _ = l₂.1 x := (lambda_eq_on_S0_part c h12 (l := l₂) hx).symm

/-- `t` is an involution of `H0`. -/
public lemma t_H0_sq (c : Hyp11 G) :
    (⟨c.t, S0_le_H0 c c.t_mem_S0⟩ : ↥c.H0) ^ 2 = 1 := by
  apply Subtype.ext
  simpa [Subgroup.coe_pow, pow_two] using c.t_involution.2

/-- The elements of `Λ` of order dividing two are exactly two (the trivial
character and the unique character with `λ(t) = -1`). -/
private lemma lambda_two_torsion_card (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] :
    (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = 1)).card = 2 := by
  classical
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  rcases IsCyclic.exists_generator (α := ↥(c.S0 : Subgroup G)) with ⟨r0, hr0⟩
  let r0H0 : ↥c.H0 := ⟨(r0 : G), S0_le_H0 c r0.2⟩
  let tH0 : ↥c.H0 := ⟨c.t, S0_le_H0 c c.t_mem_S0⟩
  have ht_sq : tH0 ^ 2 = 1 := by
    simpa [tH0] using t_H0_sq c
  have h2dvd : 2 ∣ Fintype.card (LambdaHom c.H0 c.U) := by
    refine ⟨(Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
      (l.1 tH0 : ℂ) = 1)).card, ?_⟩
    simpa [mul_comm] using (lambdaOne_card_mul_two c.H0 c.U (U_normal_subgroupOf c h12)
      (lambda_hcomm c h12) (t_not_mem_U c) ht_sq).symm
  have hcauchy : ∃ l : LambdaHom c.H0 c.U, orderOf l = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : 2 ∣ Nat.card (LambdaHom c.H0 c.U) := by
      rwa [Nat.card_eq_fintype_card]
    exact exists_prime_orderOf_dvd_card' (G := LambdaHom c.H0 c.U) 2 hdvd
  rcases hcauchy with ⟨l0, hl0⟩
  have hl0sq : l0 ^ 2 = 1 := (orderOf_eq_prime_iff.mp hl0).1
  have hl0ne : l0 ≠ 1 := (orderOf_eq_prime_iff.mp hl0).2
  -- ≤ 2: inject `Λ[2]` into the two square roots of unity
  have hcard2 : ({1, -1} : Finset ℂˣ).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · intro h
      have : (1 : ℂ) = -1 :=
        by simpa using congrArg (fun u : ℂˣ => (u : ℂ)) (Finset.mem_singleton.mp h)
      norm_num at this
  have hle : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = 1)).card ≤
      ({1, -1} : Finset ℂˣ).card := by
    refine Finset.card_le_card_of_injOn (f := fun l : LambdaHom c.H0 c.U => l.1 r0H0) ?_ ?_
    · intro a ha
      have ha' : a ^ 2 = 1 := by simpa using ha
      -- (a.1 r0H0)^2 = 1 ⟹ a.1 r0H0 = ±1
      have hl2 : a.1 ^ 2 = 1 := by
        -- a ^ 2 = 1 as a subgroup element ⟹ the hom squares to the trivial hom
        simpa using congrArg (fun x : ↥(LambdaHom c.H0 c.U) => x.1) ha'
      have hsq : (a.1 r0H0) ^ 2 = 1 := by
        calc
          (a.1 r0H0) ^ 2 = (a.1 ^ 2) r0H0 := by simp [pow_two]
          _ = 1 := by rw [hl2]; rfl
      have hzc : (a.1 r0H0 : ℂ) ^ 2 = 1 := by
        simpa [← Units.val_pow_eq_pow_val] using congrArg (fun u : ℂˣ => (u : ℂ)) hsq
      rcases (sq_eq_one_iff.mp hzc) with h1 | h2
      · simpa [Finset.mem_insert, Finset.mem_singleton] using Or.inl (Units.ext h1)
      · simpa [Finset.mem_insert, Finset.mem_singleton] using Or.inr (Units.ext h2)
    · intro a ha b hb hf
      apply lambda_ext_on_S0 c h12
      intro r
      rcases (Subgroup.mem_zpowers_iff.mp (hr0 r)) with ⟨k, hk⟩
      have hk' : ⟨(r : G), S0_le_H0 c r.2⟩ = r0H0 ^ k := by
        apply Subtype.ext
        simpa [r0H0] using (congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hk).symm
      calc
        a.1 ⟨(r : G), S0_le_H0 c r.2⟩ = a.1 (r0H0 ^ k) := by rw [hk']
        _ = (a.1 r0H0) ^ k := by exact map_zpow a.1 r0H0 k
        _ = (b.1 r0H0) ^ k := by simpa using congrArg (fun z : ℂˣ => z ^ k) hf
        _ = b.1 (r0H0 ^ k) := by rw [map_zpow]
        _ = b.1 ⟨(r : G), S0_le_H0 c r.2⟩ := by rw [hk']
  -- ≥ 2: `1` and the Cauchy element
  have hge : 2 ≤ (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = 1)).card := by
    have hsub : ({1, l0} : Finset (LambdaHom c.H0 c.U)) ≤
        Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = 1) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp
      · simp [hl0sq]
    have hpair : ({1, l0} : Finset (LambdaHom c.H0 c.U)).card = 2 := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · simpa [ne_eq] using (Ne.symm hl0ne)
    have hle' : ({1, l0} : Finset (LambdaHom c.H0 c.U)).card ≤
        (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = 1)).card :=
      Finset.card_le_card hsub
    rwa [hpair] at hle'
  exact le_antisymm (by rwa [hcard2] at hle) hge

/-- `t` is central in `H0` (from `t ∈ H = C_G(t)` and `H0 ≤ H`). -/
private lemma t_central_H0 (c : Hyp11 G) (x : ↥c.H0) : c.t * (x : G) = (x : G) * c.t := by
  have hUleH : c.U ≤ c.H := Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hH0H : c.H0 ≤ c.H := by
    exact sup_le hUleH (fun g hg => S_le_H c (c.S0_le_S hg))
  have hx : (x : G) ∈ c.H := hH0H x.2
  have hx' : (x : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact hx
  exact (Subgroup.mem_centralizer_iff.mp hx') c.t (by simp)

/-- `t` centralizes `H0`, as an element of `H0`. -/
public lemma t_central_H0' (c : Hyp11 G) :
    ∀ g : ↥c.H0, (⟨c.t, S0_le_H0 c c.t_mem_S0⟩ : ↥c.H0) * g =
      g * ⟨c.t, S0_le_H0 c c.t_mem_S0⟩ := by
  intro g
  apply Subtype.ext
  simpa using t_central_H0 c g

/-- The value of a unit in a field is nonzero. -/
public lemma unit_val_ne_zero {K : Type*} [Field K] (u : Kˣ) : (u : K) ≠ 0 := by
  intro hz
  have hv := u.val_inv
  rw [hz] at hv
  norm_num at hv

/-- The stabilizer of `ν` lies in `Λ₁` (from `ν(t) ≠ 0`). -/
private lemma Stab_le_L1 (c : Hyp11 G) (ν : ClassFunction (↥c.H0))
    (hν : IsIrreducibleCharacter ν) (tH0 : ↥c.H0) (ht_sq : tH0 ^ 2 = 1)
    (ht_central : ∀ g : ↥c.H0, tH0 * g = g * tH0) :
    ∀ l : ↥(LambdaHom c.H0 c.U), LambdaChar l.1 * ν = ν → (l.1 tH0 : ℂ) = 1 := by
  intro l hl
  have hνt : ν tH0 ≠ 0 := char_apply_central_ne_zero
    (G := ↥c.H0) (t := tH0) ht_central ht_sq hν
  have hpt : (l.1 tH0 : ℂ) * ν tH0 = 1 * ν tH0 := by
    have h := congrFun hl tH0
    simpa [LambdaChar] using h
  exact mul_right_cancel₀ hνt hpt

/-- The squaring fibers over `Λ₁` have exactly two elements. -/
private lemma lambda_sq_fiber_card (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (tH0 : ↥c.H0) (ht_sq : tH0 ^ 2 = 1)
    (ht_not_U : (tH0 : G) ∉ c.U) {mu : LambdaHom c.H0 c.U}
    (hmu : (mu.1 tH0 : ℂ) = 1) :
    (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => l ^ 2 = mu)).card = 2 := by
  classical
  let Λ := LambdaHom c.H0 c.U
  let L1 := Finset.univ.filter (fun l : Λ => (l.1 tH0 : ℂ) = 1)
  have hker : (Finset.univ.filter (fun l : Λ => l ^ 2 = 1)).card = 2 :=
    lambda_two_torsion_card c h12
  have hfib : ∀ y : Λ, y ∈ (Finset.univ.image (fun l : Λ => l ^ 2)) →
      (Finset.univ.filter (fun l : Λ => l ^ 2 = y)).card = 2 := by
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨l₀, hl₀, rfl⟩
    calc
      (Finset.univ.filter (fun l : Λ => l ^ 2 = l₀ ^ 2)).card
          = (Finset.univ.filter (fun k : Λ => k ^ 2 = 1)).card := by
            refine (Finset.card_bij (fun k hk => k * l₀) ?_ ?_ ?_).symm
            · intro k hk
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
              calc
                (k * l₀) ^ 2 = k ^ 2 * l₀ ^ 2 := by rw [mul_pow]
                _ = 1 * l₀ ^ 2 := by rw [hk]
                _ = l₀ ^ 2 := by rw [one_mul]
            · intro a₁ ha₁ a₂ ha₂ hEq
              exact mul_right_cancel hEq
            · intro l hl
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
              refine ⟨l * l₀⁻¹, ?_, ?_⟩
              · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                calc
                  (l * l₀⁻¹) ^ 2 = l ^ 2 * (l₀⁻¹) ^ 2 := by rw [mul_pow]
                  _ = l₀ ^ 2 * (l₀⁻¹) ^ 2 := by rw [hl]
                  _ = l₀ ^ 2 * (l₀ ^ 2)⁻¹ := by rw [inv_pow]
                  _ = 1 := by rw [mul_inv_cancel]
              · simp
      _ = 2 := hker
  have hsum : (Finset.univ : Finset Λ).card =
      ∑ y ∈ Finset.univ.image (fun l : Λ => l ^ 2), 2 := by
    calc
      (Finset.univ : Finset Λ).card = ∑ y ∈ Finset.univ.image (fun l : Λ => l ^ 2),
          (Finset.univ.filter (fun l : Λ => l ^ 2 = y)).card := by
            exact Finset.card_eq_sum_card_fiberwise (f := fun l : Λ => l ^ 2)
              (s := Finset.univ) (t := Finset.univ.image (fun l : Λ => l ^ 2))
              (by intro l _; exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)
      _ = ∑ y ∈ Finset.univ.image (fun l : Λ => l ^ 2), 2 := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            exact hfib y hy
  have hsum' : (Finset.univ : Finset Λ).card =
      2 * (Finset.univ.image (fun l : Λ => l ^ 2)).card := by
    rw [hsum]
    rw [Finset.sum_const_nat (fun y hy => rfl)]
    rw [mul_comm]
  have hL : (Finset.univ : Finset Λ).card = 2 * L1.card := by
    have h := lambdaOne_card_mul_two c.H0 c.U (U_normal_subgroupOf c h12) (lambda_hcomm c h12)
      ht_not_U ht_sq
    simpa [L1, Λ, mul_comm] using h.symm
  have himg : (Finset.univ.image (fun l : Λ => l ^ 2)).card = L1.card := by
    exact (Nat.mul_right_cancel (by norm_num : 0 < 2) (by
      calc
        (Finset.univ.image (fun l : Λ => l ^ 2)).card * 2
            = 2 * (Finset.univ.image (fun l : Λ => l ^ 2)).card := by rw [mul_comm]
        _ = (Finset.univ : Finset Λ).card := hsum'.symm
        _ = L1.card * 2 := by rw [hL, mul_comm]))
  have hsubimg : (Finset.univ.image (fun l : Λ => l ^ 2)) ⊆ L1 := by
    intro y hy
    rcases (Finset.mem_image.mp hy) with ⟨l, hl, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, L1]
    change (l.1 tH0 : ℂ) ^ 2 = 1
    exact lambda_sq_eq_one c.H0 c.U tH0 ht_sq l
  have hmu_img : mu ∈ Finset.univ.image (fun l : Λ => l ^ 2) := by
    have hEq : Finset.univ.image (fun l : Λ => l ^ 2) = L1 :=
      Finset.eq_of_subset_of_card_le hsubimg (by rw [himg])
    rw [hEq]
    simp [L1]
    simpa using hmu
  rcases (Finset.mem_image.mp hmu_img) with ⟨l₀, hl₀, rfl⟩
  exact hfib (l₀ ^ 2) (Finset.mem_image.mpr ⟨l₀, Finset.mem_univ l₀, rfl⟩)

/-- Lemma 2.1(ii): if `ν^s ∈ Lν`, exactly two characters of the orbit `Lν`
are fixed by `s`. -/
public theorem lemma_2_1_b (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν) :
    ((orbit c.H0 c.U ν).filter (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2 := by
  classical
  let tH0 : ↥c.H0 := ⟨c.t, S0_le_H0 c c.t_mem_S0⟩
  have ht_sq : tH0 ^ 2 = 1 := by
    simpa [tH0] using t_H0_sq c
  have ht_not_U : (tH0 : G) ∉ c.U := t_not_mem_U c
  rcases (Finset.mem_image.mp hνs) with ⟨mu, hmu, hμeq⟩
  -- μ₀ ∈ Λ₁: ν^s(t) = ν(t) (s fixes t) and ν(t) ≠ 0
  have hνt : ν tH0 ≠ 0 := char_apply_central_ne_zero
    (G := ↥c.H0) (t := tH0) (htc := by simpa [tH0] using t_central_H0' c) ht_sq hν
  have hmu_t : (mu.1 tH0 : ℂ) = 1 := by
    have hct : conjChar c.H0 (s_normalizes_H0 c h12) ν tH0 = ν tH0 := by
      change ν (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) tH0) = ν tH0
      congr 1
      apply Subtype.ext
      change c.s * c.t * c.s⁻¹ = c.t
      exact s_conj_t c
    have hpt : (mu.1 tH0 : ℂ) * ν tH0 = 1 * ν tH0 := by
      have h := congrFun hμeq tH0
      -- (LambdaChar mu.1 * ν) tH0 = conjChar ν tH0
      rw [hct] at h
      simpa [LambdaChar] using h
    exact mul_right_cancel₀ hνt hpt
  -- the fixed-point equation
  have hfix : ∀ l : ↥(LambdaHom c.H0 c.U),
      conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 * ν) = LambdaChar l.1 * ν ↔
        LambdaChar (mu⁻¹ * l ^ 2).1 * ν = ν := by
    intro l
    have hc1 : conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) = (LambdaChar l.1)⁻¹ := by
      ext x
      change (l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) : ℂ) = (l.1 x : ℂ)⁻¹
      simpa [Units.val_inv] using congrArg (fun u : ℂˣ => (u : ℂ))
        (lambda_conj_s_inv c h12 (l := l) x)
    have hbase : conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 * ν) =
        (LambdaChar l.1)⁻¹ * (LambdaChar mu.1 * ν) := by
      calc
        conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 * ν)
            = conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) *
                conjChar c.H0 (s_normalizes_H0 c h12) ν := by
                  ext x
                  rfl
        _ = (LambdaChar l.1)⁻¹ * (LambdaChar mu.1 * ν) := by rw [hc1, ← hμeq]
    constructor
    · intro hl
      -- (LambdaChar l.1)⁻¹ · LambdaChar mu.1 · ν = LambdaChar l.1 · ν ⟹ LambdaChar (mu⁻¹l²).1 · ν = ν
      have hpt : ∀ x : ↥c.H0, (mu.1 x : ℂ) * ν x = (l.1 x : ℂ) ^ 2 * ν x := by
        intro x
        have h1 := congrFun hl x
        have hb := congrFun hbase x
        rw [hb] at h1
        have h1' : (l.1 x : ℂ) * (((LambdaChar l.1)⁻¹ * (LambdaChar mu.1 * ν)) x) =
            (l.1 x : ℂ) * ((LambdaChar l.1 * ν) x) := by rw [h1]
        have hL : (l.1 x : ℂ) * (((LambdaChar l.1)⁻¹ * (LambdaChar mu.1 * ν)) x) =
            (mu.1 x : ℂ) * ν x := by
          simp [LambdaChar, mul_assoc, mul_left_comm, mul_comm]
        have hR : (l.1 x : ℂ) * ((LambdaChar l.1 * ν) x) = (l.1 x : ℂ) ^ 2 * ν x := by
          simp [LambdaChar, pow_two, mul_left_comm, mul_comm]
        rw [hL, hR] at h1'
        exact h1'
      ext x
      change (LambdaChar (mu⁻¹ * l ^ 2).1 x : ℂ) * ν x = ν x
      simp [LambdaChar, pow_two]
      have h := hpt x
      have h' : (mu.1 x : ℂ)⁻¹ * ((mu.1 x : ℂ) * ν x) =
          (mu.1 x : ℂ)⁻¹ * ((l.1 x : ℂ) ^ 2 * ν x) := by rw [h]
      have hL' : (mu.1 x : ℂ)⁻¹ * ((mu.1 x : ℂ) * ν x) = ν x := by
        rw [← mul_assoc, inv_mul_cancel₀ (unit_val_ne_zero (mu.1 x)), one_mul]
      have h'' : ν x = (mu.1 x : ℂ)⁻¹ * ((l.1 x : ℂ) ^ 2 * ν x) := by
        calc
          ν x = (mu.1 x : ℂ)⁻¹ * ((mu.1 x : ℂ) * ν x) := hL'.symm
          _ = (mu.1 x : ℂ)⁻¹ * ((l.1 x : ℂ) ^ 2 * ν x) := h'
      exact (by simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h''.symm)
    · intro hl
      -- hl : LambdaChar (mu⁻¹·l²).1·ν = ν ⟹ conjChar (LambdaChar l.1·ν) = LambdaChar l.1·ν
      ext x
      rw [hbase]
      -- want: (l.1 x : ℂ)⁻¹ * (mu.1 x : ℂ) * ν x = (l.1 x : ℂ) * ν x
      change (l.1 x : ℂ)⁻¹ * ((mu.1 x : ℂ) * ν x) = (l.1 x : ℂ) * ν x
      have hpt := congrFun hl x
      -- hpt : (ΛChar (mu⁻¹·l²).1 * ν) x = ν x
      have hpt' : (mu.1 x : ℂ) * ((LambdaChar (mu⁻¹ * l ^ 2).1 * ν) x) =
          (mu.1 x : ℂ) * ν x := by rw [hpt]
      have hL : (mu.1 x : ℂ) * ((LambdaChar (mu⁻¹ * l ^ 2).1 * ν) x) =
          (l.1 x : ℂ) ^ 2 * ν x := by
        change (mu.1 x : ℂ) * (((mu⁻¹ * l ^ 2 : ↥(LambdaHom c.H0 c.U)).1 x : ℂ) * ν x) =
          (l.1 x : ℂ) ^ 2 * ν x
        simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        left
        field_simp [unit_val_ne_zero (mu.1 x)]
      rw [hL] at hpt'
      -- hpt' : (l.1 x : ℂ)^2 * ν x = (mu.1 x : ℂ) * ν x
      have hc := congrArg (fun z : ℂ => (l.1 x : ℂ)⁻¹ * z) hpt'
      have hc' : (l.1 x : ℂ)⁻¹ * ((l.1 x : ℂ) ^ 2 * ν x) = (l.1 x : ℂ) * ν x := by
        field_simp [unit_val_ne_zero (l.1 x)]
      rw [hc'] at hc
      -- hc : (l.1 x : ℂ) * ν x = (l.1 x : ℂ)⁻¹ * ((mu.1 x : ℂ) * ν x)
      simpa [mul_assoc] using hc.symm
  -- count the fixed orbit elements: preimage of the fixed filter
  let P : ClassFunction (↥c.H0) → Prop := fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ
  have hpre := orbit_filter_preimage_card c.H0 c.U ν
    (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)
  let StabF := Finset.univ.filter (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν = ν)
  have hpre_eq : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => P (LambdaChar l.1 * ν))).card =
      (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => LambdaChar (mu⁻¹ * l ^ 2).1 * ν = ν)).card := by
    apply congrArg Finset.card
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
    exact hfix l
  have hpre_eq2 : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
      LambdaChar (mu⁻¹ * l ^ 2).1 * ν = ν)).card =
      2 * StabF.card := by
    -- the fiber sum over the stabilizer
    have hsum : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
        LambdaChar (mu⁻¹ * l ^ 2).1 * ν = ν)).card =
        ∑ s ∈ StabF, (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
          mu⁻¹ * l ^ 2 = s)).card := by
      have hcong : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
            LambdaChar (mu⁻¹ * l ^ 2).1 * ν = ν)) =
          (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => mu⁻¹ * l ^ 2 ∈ StabF)) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp [StabF]
      rw [hcong]
      rw [Finset.sum_card_fiberwise_eq_card_filter]
    calc
      (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
          LambdaChar (mu⁻¹ * l ^ 2).1 * ν = ν)).card
          = ∑ s ∈ StabF, (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
              mu⁻¹ * l ^ 2 = s)).card := hsum
      _ = ∑ s ∈ StabF, 2 := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsL1 : ((mu * s).1 tH0 : ℂ) = 1 := by
              have hs1 : (s.1 tH0 : ℂ) = 1 :=
                Stab_le_L1 c ν hν tH0 ht_sq (by simpa [tH0] using t_central_H0' c)
                  s (Finset.mem_filter.mp hs).2
              simp [hs1, hmu_t]
            have hfib2 : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
                l ^ 2 = mu * s)).card = 2 :=
              lambda_sq_fiber_card c h12 tH0 ht_sq ht_not_U hsL1
            have hEq : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
                mu⁻¹ * l ^ 2 = s)) = (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
                  l ^ 2 = mu * s)) := by
              ext l
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h
                have h1 : mu * (mu⁻¹ * l ^ 2) = mu * s := by rw [h]
                simpa [mul_assoc] using h1
              · intro h
                calc
                  mu⁻¹ * l ^ 2 = mu⁻¹ * (mu * s) := by rw [h]
                  _ = s := by simp
            rwa [hEq]
      _ = 2 * StabF.card := by
            rw [Finset.sum_const_nat (fun s hs => rfl)]
            rw [mul_comm]
  -- |fixed-filter| · |Stab| = |pre| = 2·|Stab|
  have hstab_ne : StabF.card ≠ 0 :=
    (Finset.card_pos.mpr ⟨(1 : LambdaHom c.H0 c.U), one_mem_stab c.H0 c.U ν⟩).ne'
  have hpreP : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => P (LambdaChar l.1 * ν))).card =
      ((orbit c.H0 c.U ν).filter P).card * StabF.card := by
    convert hpre using 1
    · congr 1
      ext l
      simp [P]
    · congr 2
      ext l
      simp [P]
  have hfixed : ((orbit c.H0 c.U ν).filter P).card = 2 := by
    have h1 : ((orbit c.H0 c.U ν).filter P).card * StabF.card =
        2 * StabF.card := by
      calc
        ((orbit c.H0 c.U ν).filter P).card * StabF.card
            = (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => P (LambdaChar l.1 * ν))).card := by
              convert hpreP.symm using 1
        _ = (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
                LambdaChar (mu⁻¹ * l ^ 2).1 * ν = ν)).card := hpre_eq
        _ = 2 * StabF.card := hpre_eq2
    exact mul_right_cancel₀ hstab_ne h1
  change ((orbit c.H0 c.U ν).filter (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2
  exact hfixed

/-! ## Section 2: the general situation

The preamble of Section 2 of the paper: `λ2` (the non-trivial character of
`Λ` whose kernel contains `S'`, the subgroup of index `2` in `S0`), `κ1` (a
linear character of `H0` whose kernel contains `S0` and `[S,U]`), `κi =
λi·κ1`.  The statements of Lemma 2.2, the Coherence Theorem 2.3 (with
`B(χ)`), Lemma 2.4 and Lemma 2.5 live in `Section2/Lemma22.lean`,
`Section2/Coherence.lean`, `Section2/Lemma24.lean` and `Section2/Lemma25.lean`.
-/

/-- `Irr(G)`: the irreducible characters of `G`, as a subtype of class
functions. -/
public abbrev Irr (G : Type u) [Group G] : Type u :=
  {ν : ClassFunction G // IsIrreducibleCharacter ν}

/-- `±Irr(G)`: `φ` or `-φ` is an irreducible character of `G`. -/
public abbrev IsPMIrr (G : Type u) [Group G] (φ : ClassFunction G) : Prop :=
  IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)

/-- `S'`: the subgroup of index `2` in `S0` (generated by `(t1·t2)²`, since
`S0 = ⟨t1·t2⟩`). -/
@[expose] public def SPrime (c : Hyp11 G) : Subgroup G :=
  Subgroup.zpowers ((c.t1 * c.t2) ^ 2)

/-- The square `(t1·t2)²` lies in `S'`. -/
public lemma SPrime_mem_pow_two (c : Hyp11 G) : (c.t1 * c.t2) ^ 2 ∈ SPrime c := by
  rw [SPrime]
  exact Subgroup.mem_zpowers ((c.t1 * c.t2) ^ 2)

/-- `S' ≤ S0`. -/
public theorem SPrime_le_S0 (c : Hyp11 G) : SPrime c ≤ (c.S0 : Subgroup G) := by
  rw [c.S0_eq_zpowers]
  change Subgroup.zpowers ((c.t1 * c.t2) ^ 2) ≤ Subgroup.zpowers (c.t1 * c.t2)
  rw [Subgroup.zpowers_le]
  exact (Subgroup.mem_zpowers_iff).mpr ⟨2, by simp [zpow_ofNat]⟩

/-- `|S0 : S'| = 2`. -/
public theorem SPrime_index (c : Hyp11 G) :
    ((SPrime c).subgroupOf (c.S0 : Subgroup G)).index = 2 := by
  classical
  let z : G := c.t1 * c.t2
  have hz_order : orderOf z = 2 ^ c.m := by
    have hc : Nat.card (Subgroup.zpowers z : Subgroup G) = 2 ^ c.m := by
      rw [← c.S0_eq_zpowers]
      exact S0_nat_card c
    rw [← Nat.card_zpowers]
    exact hc
  have hz2 : orderOf (z ^ 2) = 2 ^ (c.m - 1) := by
    have h2dvd : 2 ∣ orderOf z := by
      rw [hz_order]
      rw [show 2 ^ c.m = 2 * 2 ^ (c.m - 1) by
        rw [← pow_succ', Nat.sub_add_cancel c.one_le_m]]
      exact dvd_mul_right 2 (2 ^ (c.m - 1))
    rw [orderOf_pow_of_dvd (x := z) (n := 2) (by norm_num) h2dvd,
      hz_order]
    rw [show 2 ^ c.m = 2 * 2 ^ (c.m - 1) by
      rw [← pow_succ', Nat.sub_add_cancel c.one_le_m]]
    omega
  have hcardSP : Nat.card (SPrime c : Subgroup G) = 2 ^ (c.m - 1) := by
    dsimp [SPrime]
    rw [Nat.card_zpowers]
    exact hz2
  have hcardSub : Nat.card ((SPrime c).subgroupOf (c.S0 : Subgroup G)) =
      2 ^ (c.m - 1) := by
    let e : (SPrime c).subgroupOf (c.S0 : Subgroup G) ≃* SPrime c :=
      Subgroup.subgroupOfEquivOfLe (H := SPrime c) (K := c.S0) (SPrime_le_S0 c)
    rw [Nat.card_congr e.toEquiv]
    exact hcardSP
  have hcardS0 : Nat.card (c.S0 : Subgroup G) = 2 ^ c.m := S0_nat_card c
  have hmul : ((SPrime c).subgroupOf (c.S0 : Subgroup G)).index *
        Nat.card ((SPrime c).subgroupOf (c.S0 : Subgroup G)) =
      Nat.card (c.S0 : Subgroup G) :=
    Subgroup.index_mul_card (H := (SPrime c).subgroupOf (c.S0 : Subgroup G))
      (G := (c.S0 : Subgroup G))
  have hpow : 2 ^ c.m = 2 * 2 ^ (c.m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel c.one_le_m]
  rw [hcardSub, hcardS0, hpow] at hmul
  exact Nat.mul_right_cancel (pow_pos (by norm_num) (c.m - 1)) hmul

/-- `t` as an element of `H0`. -/
@[expose]
public def tH0 (c : Hyp11 G) : ↥c.H0 := ⟨c.t, S0_le_H0 c c.t_mem_S0⟩

/-- `s⁻¹` normalizes `H0` (`s` is an involution). -/
theorem s_inv_normalizes_H0 (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
  intro x
  have hsq : c.s⁻¹ = c.s := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.s_involution.2)
  have hx : c.s * (x : G) * c.s⁻¹ ∈ c.H0 := s_normalizes_H0 c h12 x
  simpa [hsq] using hx

/-- The `s`-conjugate of an element of `Irr(H0)`, again an element of
`Irr(H0)`. -/
public def conjIrr (c : Hyp11 G) (h12 : Hyp12 c) (ν : Irr (↥c.H0)) : Irr (↥c.H0) :=
  ⟨conjChar c.H0 (s_normalizes_H0 c h12) ν.1,
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12)
      (s_inv_normalizes_H0 c h12) ν.2⟩

/-- The underlying class function of `conjIrr` is conjugation by `s`.
This exposed projection theorem is the module-level interface for the
otherwise opaque public definition. -/
@[simp]
public theorem conjIrr_coe (c : Hyp11 G) (h12 : Hyp12 c) (ν : Irr (↥c.H0)) :
    (conjIrr c h12 ν).1 = conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
  unfold conjIrr
  rfl

/-- `S' ≤ H0`. -/
private lemma SPrime_le_H0 (c : Hyp11 G) : SPrime c ≤ c.H0 :=
  le_trans (SPrime_le_S0 c) (S0_le_H0 c)

/-- `t1·t2 ∈ S0` (`S0 = ⟨t1·t2⟩`). -/
private lemma t1t2_mem_S0 (c : Hyp11 G) : c.t1 * c.t2 ∈ (c.S0 : Subgroup G) := by
  rw [c.S0_eq_zpowers]
  exact Subgroup.mem_zpowers (c.t1 * c.t2)

/-- `t1·t2 ∈ H0`. -/
private lemma t1t2_mem_H0 (c : Hyp11 G) : c.t1 * c.t2 ∈ c.H0 :=
  S0_le_H0 c (t1t2_mem_S0 c)

/-- The order of `z = t1·t2` is `2^m` (it generates `S0`, and `|S0| = 2^m`). -/
private lemma t1t2_orderOf (c : Hyp11 G) : orderOf (c.t1 * c.t2) = 2 ^ c.m := by
  have hc : Nat.card ↥(Subgroup.zpowers (c.t1 * c.t2) : Subgroup G) = 2 ^ c.m := by
    rw [← c.S0_eq_zpowers]
    exact S0_nat_card c
  rw [← Nat.card_zpowers (c.t1 * c.t2)]
  exact hc

/-- `t1·t2 ∉ S'` (the generator of `S0` is not in the index-2 subgroup). -/
public lemma t1t2_not_mem_SPrime (c : Hyp11 G) : (c.t1 * c.t2 : G) ∉ SPrime c := by
  intro hz
  rcases (Subgroup.mem_zpowers_iff.mp hz) with ⟨k, hk⟩
  have h1 : (c.t1 * c.t2) ^ (2 * k) = (c.t1 * c.t2) := by
    rw [zpow_mul (c.t1 * c.t2) 2 k]
    rw [← zpow_ofNat (c.t1 * c.t2) 2] at hk
    exact hk
  have h2 : (c.t1 * c.t2) ^ (2 * k - 1) = 1 := by
    calc
      (c.t1 * c.t2) ^ (2 * k - 1) = (c.t1 * c.t2) ^ (2 * k) * (c.t1 * c.t2)⁻¹ := by
        rw [zpow_sub (c.t1 * c.t2) (2 * k) 1]
        simp
      _ = (c.t1 * c.t2) * (c.t1 * c.t2)⁻¹ := by rw [h1]
      _ = 1 := by group
  have hdiv : (orderOf (c.t1 * c.t2) : ℤ) ∣ (2 * k - 1) :=
    (orderOf_dvd_iff_zpow_eq_one (x := c.t1 * c.t2) (i := 2 * k - 1)).mpr h2
  have h2dvd : 2 ∣ orderOf (c.t1 * c.t2) := by
    rw [t1t2_orderOf c]
    rw [show 2 ^ c.m = 2 * 2 ^ (c.m - 1) by
      rw [← pow_succ', Nat.sub_add_cancel c.one_le_m]]
    exact dvd_mul_right 2 (2 ^ (c.m - 1))
  have h2dvd' : (2 : ℤ) ∣ (orderOf (c.t1 * c.t2) : ℤ) := by exact_mod_cast h2dvd
  have h2dvd'' : (2 : ℤ) ∣ (2 * k - 1) := Int.dvd_trans h2dvd' hdiv
  have hodd : ¬ (2 : ℤ) ∣ (2 * k - 1) := by
    intro h
    rcases h with ⟨t, ht⟩
    omega
  exact hodd h2dvd''

/-- `U ∩ S0 = 1`. -/
public lemma U_inter_S0_eq_bot (c : Hyp11 G) {x : G} (hxU : x ∈ c.U)
    (hxS0 : x ∈ (c.S0 : Subgroup G)) : x = 1 := by
  classical
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  by_contra hx1
  have hordU : orderOf x ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨x, hxU⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨x, hxU⟩ : ↥c.U)]
    have hxU' : orderOf (⟨x, hxU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨x, hxU⟩)
    rwa [← Nat.card_eq_fintype_card] at hxU'
  have hordS : orderOf x ∣ Nat.card (c.S0 : Subgroup G) := by
    change orderOf ((c.S0 : Subgroup G).subtype (⟨x, hxS0⟩ : ↥(c.S0 : Subgroup G))) ∣
      Nat.card (c.S0 : Subgroup G)
    rw [orderOf_injective (c.S0 : Subgroup G).subtype
      (Subgroup.subtype_injective (c.S0 : Subgroup G)) (⟨x, hxS0⟩ : ↥(c.S0 : Subgroup G))]
    have hxS' : orderOf (⟨x, hxS0⟩ : ↥(c.S0 : Subgroup G)) ∣
        Fintype.card ↥(c.S0 : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S0 : Subgroup G)) (x := ⟨x, hxS0⟩)
    rwa [← Nat.card_eq_fintype_card] at hxS'
  have hpow : orderOf x ∣ 2 ^ c.m := by
    rw [← S0_nat_card c]
    exact hordS
  have hcop' : Nat.Coprime (2 ^ c.m) (Nat.card ↥c.U) := hcop.pow_left _
  have h1' : orderOf x = 1 := by
    have hdvd : orderOf x ∣ 1 := by
      rw [← hcop'.gcd_eq_one]
      exact Nat.dvd_gcd hpow hordU
    exact Nat.dvd_one.mp hdvd
  exact hx1 (orderOf_eq_one_iff.mp h1')

/-- The `S0`-part of an element of `H0 = U·S0` is unique (`U ∩ S0 = 1`). -/
private lemma H0_decomp_unique (c : Hyp11 G) (_h12 : Hyp12 c)
    {x : ↥c.H0} {u u' : ↥c.U} {r r' : ↥c.S0}
    (h : (x : G) = (u : G) * (r : G)) (h' : (x : G) = (u' : G) * (r' : G)) :
    r = r' := by
  have hEq : (u : G) * (r : G) = (u' : G) * (r' : G) := by rw [← h, ← h']
  have h1 : (u' : G)⁻¹ * (u : G) * (r : G) * (r' : G)⁻¹ = 1 := by
    calc
      (u' : G)⁻¹ * (u : G) * (r : G) * (r' : G)⁻¹ = (u' : G)⁻¹ * ((u : G) * (r : G)) * (r' : G)⁻¹ := by group
      _ = (u' : G)⁻¹ * ((u' : G) * (r' : G)) * (r' : G)⁻¹ := by rw [hEq]
      _ = 1 := by group
  have hU : (u' : G)⁻¹ * (u : G) ∈ c.U := c.U.mul_mem (c.U.inv_mem u'.2) u.2
  have hS : (r' : G) * (r : G)⁻¹ ∈ (c.S0 : Subgroup G) :=
    (c.S0 : Subgroup G).mul_mem r'.2 ((c.S0 : Subgroup G).inv_mem r.2)
  have hEq2 : (u' : G)⁻¹ * (u : G) = (r' : G) * (r : G)⁻¹ := by
    calc
      (u' : G)⁻¹ * (u : G) = (u' : G)⁻¹ * (u : G) * (r : G) * (r' : G)⁻¹ * (r' : G) * (r : G)⁻¹ := by group
      _ = 1 * (r' : G) * (r : G)⁻¹ := by rw [h1]
      _ = (r' : G) * (r : G)⁻¹ := by simp
  have hU2 : (u' : G)⁻¹ * (u : G) ∈ (c.S0 : Subgroup G) := by
    rw [hEq2]
    exact hS
  have h1' : (u' : G)⁻¹ * (u : G) = 1 := U_inter_S0_eq_bot c hU hU2
  apply Subtype.ext
  calc
    (r : G) = (u : G)⁻¹ * ((u : G) * (r : G)) := by group
    _ = (u : G)⁻¹ * ((u' : G) * (r' : G)) := by rw [hEq]
    _ = (r' : G) := by
      have hu : (u : G)⁻¹ * (u' : G) = 1 := by
        calc
          (u : G)⁻¹ * (u' : G) = ((u' : G)⁻¹ * (u : G))⁻¹ := by group
          _ = 1 := by rw [h1']; simp
      rw [← mul_assoc]
      rw [hu]
      simp

/-- The `S0`-part of `x ∈ H0 = U·S0`. -/
@[expose] public noncomputable def s0Part (c : Hyp11 G) (h12 : Hyp12 c) (x : ↥c.H0) :
    ↥(c.S0 : Subgroup G) :=
  Classical.choose (Classical.choose_spec (H0_eq_U_mul_S0 c h12 (x := x)))

/-- The defining property of `s0Part`. -/
public lemma s0Part_spec (c : Hyp11 G) (h12 : Hyp12 c) (x : ↥c.H0) :
    ∃ u : ↥c.U, (x : G) = (u : G) * (s0Part c h12 x : G) := by
  classical
  exact ⟨Classical.choose (H0_eq_U_mul_S0 c h12 (x := x)),
    Classical.choose_spec (Classical.choose_spec (H0_eq_U_mul_S0 c h12 (x := x)))⟩

/-- The `S0`-part is well-defined. -/
public lemma s0Part_unique (c : Hyp11 G) (h12 : Hyp12 c) {x : ↥c.H0}
    {u : ↥c.U} {r : ↥c.S0} (h : (x : G) = (u : G) * (r : G)) :
    s0Part c h12 x = r := by
  rcases s0Part_spec c h12 x with ⟨u₀, h₀⟩
  exact H0_decomp_unique c h12 h₀ h

/-- The projection `H0 → S0` along `U` (a group hom, `H0 = U·S0`, `U ∩ S0 = 1`). -/
@[expose] public noncomputable def s0Projection (c : Hyp11 G) (h12 : Hyp12 c) :
    ↥c.H0 →* ↥(c.S0 : Subgroup G) where
  toFun := s0Part c h12
  map_one' := by
    apply s0Part_unique c h12 (u := 1) (r := 1)
    simp
  map_mul' := by
    intro x y
    rcases s0Part_spec c h12 x with ⟨u₁, hx⟩
    rcases s0Part_spec c h12 y with ⟨u₂, hy⟩
    have hconj : ((s0Part c h12 x : G) * (u₂ : G) * ((s0Part c h12 x : G))⁻¹) ∈ c.U :=
      (h12.U_normal_in_H0).2 (s0Part c h12 x : G) (S0_le_H0 c (s0Part c h12 x).2) (u₂ : G) u₂.2
    have hxy : (x * y : G) =
        ((u₁ : G) * ((s0Part c h12 x : G) * (u₂ : G) * ((s0Part c h12 x : G))⁻¹)) *
          ((s0Part c h12 x : G) * (s0Part c h12 y : G)) := by
      calc
        (x * y : G) = (x : G) * (y : G) := rfl
        _ = ((u₁ : G) * (s0Part c h12 x : G)) * ((u₂ : G) * (s0Part c h12 y : G)) := by rw [hx, hy]
        _ = ((u₁ : G) * ((s0Part c h12 x : G) * (u₂ : G) * ((s0Part c h12 x : G))⁻¹)) *
            ((s0Part c h12 x : G) * (s0Part c h12 y : G)) := by group
    have hmain : s0Part c h12 (x * y) = s0Part c h12 x * s0Part c h12 y := by
      apply s0Part_unique c h12
        (u := ⟨(u₁ : G) * ((s0Part c h12 x : G) * (u₂ : G) * ((s0Part c h12 x : G))⁻¹), c.U.mul_mem u₁.2 hconj⟩)
        (r := ⟨(s0Part c h12 x : G) * (s0Part c h12 y : G),
          (c.S0 : Subgroup G).mul_mem (s0Part c h12 x).2 (s0Part c h12 y).2⟩)
      exact hxy
    exact hmain

/-- `S0` is abelian (cyclic). -/
private lemma s0_commGroup (c : Hyp11 G) : IsMulCommutative ↥(c.S0 : Subgroup G) := by
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
  infer_instance

/-- `S'` is normal in `S0`. -/
private lemma sPrime_subgroupOf_normal (c : Hyp11 G) :
    ((SPrime c).subgroupOf (c.S0 : Subgroup G)).Normal := by
  let : IsMulCommutative ↥(c.S0 : Subgroup G) := s0_commGroup c
  exact Subgroup.normal_of_comm ((SPrime c).subgroupOf (c.S0 : Subgroup G))

/-- The commutator hypothesis for the `S0`-instance of the `Λ`-machinery. -/
private lemma sPrime_hcomm (c : Hyp11 G) :
    ∀ x y : ↥(c.S0 : Subgroup G), (x * y) / (y * x) ∈ (SPrime c).subgroupOf (c.S0 : Subgroup G) := by
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
  intro x y
  apply (Subgroup.mem_subgroupOf).2
  have h : (x * y) / (y * x) = 1 := by
    rw [div_eq_mul_inv]
    rw [mul_comm y x]
    exact mul_inv_cancel (x * y)
  rw [h]
  simp

/-- A character of `S0` killing `S'` and nontrivial at `t1·t2`. -/
private lemma exists_s0_char (c : Hyp11 G) (_h12 : Hyp12 c) :
    ∃ φ : ↥(c.S0 : Subgroup G) →* ℂˣ,
      (∀ r : ↥(c.S0 : Subgroup G), (r : G) ∈ SPrime c → φ r = 1) ∧
      φ ⟨c.t1 * c.t2, t1t2_mem_S0 c⟩ ≠ 1 := by
  classical
  rcases (LambdaHom_separates (H0 := (c.S0 : Subgroup G)) (U := SPrime c)
      (sPrime_subgroupOf_normal c) (sPrime_hcomm c)
      ⟨c.t1 * c.t2, t1t2_mem_S0 c⟩ (t1t2_not_mem_SPrime c)) with ⟨φ, hφ⟩
  exact ⟨φ.1, φ.2, hφ⟩

/-- Extend a character of `S0` to `H0 = U·S0` (trivial on `U`). -/
@[expose] public noncomputable def s0Char (c : Hyp11 G) (h12 : Hyp12 c)
    (φ : ↥(c.S0 : Subgroup G) →* ℂˣ) : ↥c.H0 →* ℂˣ :=
  φ.comp (s0Projection c h12)

/-- The extension lies in `Λ = LambdaHom H0 U`. -/
public lemma s0Char_mem (c : Hyp11 G) (h12 : Hyp12 c)
    (φ : ↥(c.S0 : Subgroup G) →* ℂˣ) : s0Char c h12 φ ∈ LambdaHom c.H0 c.U := by
  intro u hu
  change φ (s0Projection c h12 u) = 1
  have hπ : s0Projection c h12 u = 1 := by
    apply s0Part_unique c h12 (u := ⟨(u : G), hu⟩) (r := 1)
    simp
  rw [hπ]
  simp

/-- `x² ∈ U·S'` for every `x ∈ H0` (from `x = u·r`: `x² = u·(r·u·r⁻¹)·r²`). -/
private lemma sq_mem_U_mul_SPrime (c : Hyp11 G) (h12 : Hyp12 c) (x : ↥c.H0) :
    ∃ u : ↥c.U, ∃ r : ↥(SPrime c), (x : G) ^ 2 = (u : G) * (r : G) := by
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u₁, r₁, hx⟩
  have hconj : (r₁ : G) * (u₁ : G) * (r₁ : G)⁻¹ ∈ c.U :=
    (h12.U_normal_in_H0).2 (r₁ : G) (S0_le_H0 c r₁.2) (u₁ : G) u₁.2
  have hr1sq : (r₁ : G) ^ 2 ∈ SPrime c := by
    rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using r₁.2)) with ⟨k, hk⟩
    change (r₁ : G) ^ 2 ∈ Subgroup.zpowers ((c.t1 * c.t2) ^ 2)
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    calc
      ((c.t1 * c.t2) ^ 2) ^ k = (c.t1 * c.t2) ^ (2 * k) := by
        rw [← zpow_ofNat (c.t1 * c.t2) 2]
        rw [zpow_mul (c.t1 * c.t2) 2 k]
      _ = (c.t1 * c.t2) ^ (k + k) := by congr 1; ring
      _ = (c.t1 * c.t2) ^ k * (c.t1 * c.t2) ^ k := by rw [zpow_add (c.t1 * c.t2) k k]
      _ = ((c.t1 * c.t2) ^ k) ^ 2 := by rw [pow_two]
      _ = (r₁ : G) ^ 2 := by rw [hk]
  refine ⟨⟨(u₁ : G) * ((r₁ : G) * (u₁ : G) * (r₁ : G)⁻¹), c.U.mul_mem u₁.2 hconj⟩,
      ⟨(r₁ : G) ^ 2, hr1sq⟩, ?_⟩
  calc
    (x : G) ^ 2 = ((u₁ : G) * (r₁ : G)) * ((u₁ : G) * (r₁ : G)) := by rw [pow_two, hx]
    _ = (u₁ : G) * ((r₁ : G) * (u₁ : G) * (r₁ : G)⁻¹) * ((r₁ : G) * (r₁ : G)) := by group
    _ = (u₁ : G) * ((r₁ : G) * (u₁ : G) * (r₁ : G)⁻¹) * (r₁ : G) ^ 2 := by rw [← pow_two (r₁ : G)]

/-- Any `l ∈ Λ` trivial on `S'` has order dividing two. -/
public lemma lambda_sq_eq_one_of_kills_SPrime (c : Hyp11 G) (h12 : Hyp12 c)
    {l : ↥(LambdaHom c.H0 c.U)}
    (hk : ∀ x : ↥c.H0, (x : G) ∈ SPrime c → l.1 x = 1) :
    l ^ 2 = 1 := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  change (l.1 x) ^ 2 = 1
  rcases sq_mem_U_mul_SPrime c h12 x with ⟨u, r, hx2⟩
  calc
    (l.1 x) ^ 2 = l.1 (x ^ 2) := by rw [← map_pow l.1 x 2]
    _ = 1 := by
      have huH0 : (u : G) ∈ c.H0 := (h12.U_normal_in_H0).1 u.2
      have hrH0 : (r : G) ∈ c.H0 := SPrime_le_H0 c r.2
      have hx2' : (x ^ 2 : ↥c.H0) = ⟨(u : G) * (r : G), c.H0.mul_mem huH0 hrH0⟩ := by
        apply Subtype.ext
        simpa [Subgroup.coe_pow] using hx2
      rw [hx2']
      change l.1 (⟨(u : G), huH0⟩ * ⟨(r : G), hrH0⟩) = 1
      rw [map_mul]
      have hlU : l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ = 1 :=
        l.2 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ u.2
      have hlR : l.1 ⟨(r : G), SPrime_le_H0 c r.2⟩ = 1 := hk ⟨(r : G), SPrime_le_H0 c r.2⟩ r.2
      rw [hlU, hlR]
      simp

/-- Existence of `λ2`: a non-trivial character of `Λ` whose kernel contains
`S'`. -/
theorem exists_lambdaTwo (c : Hyp11 G) (h12 : Hyp12 c) :
    ∃ l : LambdaHom c.H0 c.U, l ≠ 1 ∧
      ∀ x : ↥c.H0, (x : G) ∈ SPrime c → l.1 x = 1 := by
  classical
  rcases exists_s0_char c h12 with ⟨φ, hφkill, hφne⟩
  let l : LambdaHom c.H0 c.U := ⟨s0Char c h12 φ, s0Char_mem c h12 φ⟩
  refine ⟨l, ?_, ?_⟩
  · intro hl
    have hz : l.1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ ≠ 1 := by
      change φ (s0Projection c h12 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩) ≠ 1
      have hπ : s0Projection c h12 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ =
          ⟨c.t1 * c.t2, t1t2_mem_S0 c⟩ := by
        apply s0Part_unique c h12 (u := 1) (r := ⟨c.t1 * c.t2, t1t2_mem_S0 c⟩)
        simp
      rw [hπ]
      exact hφne
    have hl' : l.1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = 1 := by
      have h1 := congrArg (fun z : LambdaHom c.H0 c.U => z.1) hl
      have h2 := congrArg (fun z : ↥c.H0 →* ℂˣ => z ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩) h1
      simpa using h2
    exact hz hl'
  · intro x hxSP
    change φ (s0Projection c h12 x) = 1
    have hπ : s0Projection c h12 x = ⟨(x : G), SPrime_le_S0 c hxSP⟩ := by
      apply s0Part_unique c h12 (u := 1) (r := ⟨(x : G), SPrime_le_S0 c hxSP⟩)
      simp
    rw [hπ]
    exact hφkill ⟨(x : G), SPrime_le_S0 c hxSP⟩ hxSP

/-- `λ2`: the non-trivial character in `Λ` whose kernel contains `S'`, the
subgroup of index `2` in `S0`. -/
public noncomputable def lambdaTwo (c : Hyp11 G) (h12 : Hyp12 c) : LambdaHom c.H0 c.U :=
  Classical.choose (exists_lambdaTwo c h12)

/-- `λ2` is non-trivial. -/
public theorem lambdaTwo_ne_one (c : Hyp11 G) (h12 : Hyp12 c) : lambdaTwo c h12 ≠ 1 := by
  exact (Classical.choose_spec (exists_lambdaTwo c h12)).1

/-- The kernel of `λ2` contains `S'`. -/
public theorem lambdaTwo_trivial_on_SPrime (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : ↥c.H0, (x : G) ∈ SPrime c → (lambdaTwo c h12).1 x = 1 := by
  exact (Classical.choose_spec (exists_lambdaTwo c h12)).2

/-- `λ2` has order two (it is the unique element of order `2` in `Λ`). -/
public theorem lambdaTwo_sq_eq_one (c : Hyp11 G) (h12 : Hyp12 c) :
    lambdaTwo c h12 ^ 2 = 1 := by
  exact lambda_sq_eq_one_of_kills_SPrime c h12 (lambdaTwo_trivial_on_SPrime c h12)

/-- The only elements of `Λ` of order dividing two are `1` and `λ₂`. -/
public theorem lambda_eq_one_or_two_of_sq_one (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (l : LambdaHom c.H0 c.U)
    (hl : l ^ 2 = 1) : l = 1 ∨ l = lambdaTwo c h12 := by
  classical
  let F : Finset (LambdaHom c.H0 c.U) :=
    Finset.univ.filter (fun l => l ^ 2 = 1)
  have hcard : F.card = 2 := by
    simpa [F] using lambda_two_torsion_card c h12
  have hsub : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) ⊆ F := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [F]
    · simp [F, lambdaTwo_sq_eq_one]
  have hcard2 : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · intro h
      exact (lambdaTwo_ne_one c h12) (Finset.mem_singleton.mp h).symm
  have hpair_eq : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) = F :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])
  have hF : F = ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) := hpair_eq.symm
  have hlF : l ∈ F := by
    simp [F, hl]
  rw [hF] at hlF
  simpa using hlF

/-- `λ1` and `λ2` are the only characters of `Λ` fixed by `s`. -/
public theorem lambda_fixed_by_s_iff (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (l : LambdaHom c.H0 c.U) :
    conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) = LambdaChar l.1 ↔
      l = 1 ∨ l = lambdaTwo c h12 := by
  have hc1 : conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) =
      (LambdaChar l.1)⁻¹ := by
    ext x
    change (l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) : ℂ) =
      (l.1 x : ℂ)⁻¹
    simpa [Units.val_inv] using congrArg (fun u : ℂˣ => (u : ℂ))
      (lambda_conj_s_inv c h12 (l := l) x)
  have hfix_sq : (conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) =
      LambdaChar l.1) ↔ l ^ 2 = 1 := by
    constructor
    · intro hl
      have hinv : (LambdaChar l.1)⁻¹ = LambdaChar l.1 := by simpa [hc1] using hl
      apply Subtype.ext
      apply MonoidHom.ext
      intro x
      have hx := congrFun hinv x
      have hx' : (l.1 x : ℂ)⁻¹ = (l.1 x : ℂ) := by simpa [LambdaChar] using hx
      have hmul : (l.1 x : ℂ) * (l.1 x : ℂ) = 1 := by
        calc
          (l.1 x : ℂ) * (l.1 x : ℂ) = (l.1 x : ℂ) * (l.1 x : ℂ)⁻¹ := by rw [hx']
          _ = 1 := by simp
      have hunit : l.1 x * l.1 x = 1 := by
        apply Units.ext
        simpa using hmul
      simpa [pow_two] using hunit
    · intro hl
      ext x
      change (l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) : ℂ) =
        (l.1 x : ℂ)
      rw [lambda_conj_s_inv c h12 x]
      have hx : (l.1 x : ℂ) ^ 2 = 1 := by
        have h : ((l ^ 2).1 x : ℂˣ) = 1 := by rw [hl]; rfl
        have hc : ((l ^ 2).1 x : ℂ) = 1 := by
          exact congrArg (fun u : ℂˣ => (u : ℂ)) h
        simpa [pow_two] using hc
      have hmul : (l.1 x : ℂ) * (l.1 x : ℂ) = 1 := by simpa [pow_two] using hx
      simpa using inv_eq_of_mul_eq_one_right hmul
  let F : Finset (LambdaHom c.H0 c.U) :=
    Finset.univ.filter (fun l => l ^ 2 = 1)
  have hcard : F.card = 2 := by
    simpa [F] using lambda_two_torsion_card c h12
  have hsub : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) ⊆ F := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [F]
    · simp [F, lambdaTwo_sq_eq_one]
  have hcard2 : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · intro h
      exact (lambdaTwo_ne_one c h12) (Finset.mem_singleton.mp h).symm
  have hpair_eq : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) = F :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])
  have hF : F = ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) := hpair_eq.symm
  rw [hfix_sq]
  rw [show (l ^ 2 = 1) ↔ l ∈ F by simp [F]]
  rw [hF]
  simp

/-- Existence of `κ1`: a linear character of `H0` whose kernel contains `S0`
and `[S,U]`. -/
theorem exists_kappaOne (c : Hyp11 G) (h12 : Hyp12 c) :
    ∃ κ1 : ClassFunction (↥c.H0), IsLinearCharacter κ1 ∧
      (∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1) ∧
      (∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1) := by
  refine ⟨(1 : ClassFunction (↥c.H0)), isLinearCharacter_one, ?_, ?_⟩
  · intro x hx
    rfl
  · intro x hx
    rfl

/-- `κ1`: a linear character of `H0` whose kernel contains `S0` and `[S,U]`. -/
noncomputable def kappaOne (c : Hyp11 G) (h12 : Hyp12 c) : ClassFunction (↥c.H0) :=
  Classical.choose (exists_kappaOne c h12)

/-- `κ1` is a linear character of `H0`. -/
theorem kappaOne_isLinear (c : Hyp11 G) (h12 : Hyp12 c) :
    IsLinearCharacter (kappaOne c h12) := by
  exact (Classical.choose_spec (exists_kappaOne c h12)).1

/-- The kernel of `κ1` contains `S0`. -/
theorem kappaOne_trivial_on_S0 (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → kappaOne c h12 x = 1 := by
  exact (Classical.choose_spec (exists_kappaOne c h12)).2.1

/-- The kernel of `κ1` contains `[S,U]`. -/
theorem kappaOne_trivial_on_comm (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → kappaOne c h12 x = 1 := by
  exact (Classical.choose_spec (exists_kappaOne c h12)).2.2

/-- `κ1` is fixed by `s` (`κ1^s = κ1`): `κ1` kills `S0` and `[S,U]`, and
`H0 = U·S0` with `s` inverting `S0` and normalizing `U`. -/
theorem kappaOne_fixed_by_s (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1) :
    conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1 := by
  classical
  funext x
  unfold conjChar conjMonoidHom
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  have hsq : c.s⁻¹ = c.s := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.s_involution.2)
  have hsr : c.s * (r : G) * c.s⁻¹ = (r : G)⁻¹ := s_inverts_S0 c r.2
  have hcom : ⁅(c.s : G), (u : G)⁆ ∈ ⁅(c.S : Subgroup G), c.U⁆ := by
    let S : Subgroup G := (c.S : Subgroup G)
    have hc : ⁅(c.s : G), (u : G)⁆ ∈ ⁅S, c.U⁆ := by
      exact Subgroup.commutator_mem_commutator (H₁ := S) (H₂ := c.U) c.s_mem_S u.2
    simpa [S] using hc
  have hdecomp' : (c.s * (u : G) * c.s⁻¹) = ⁅(c.s : G), (u : G)⁆ * (u : G) := by
    rw [commutatorElement_def]
    group
  have hfac : c.s * ((u : G) * (r : G)) * c.s⁻¹ =
      (c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹) := by
    group
  have hval : (c.s * ((u : G) * (r : G)) * c.s⁻¹ : G) =
      ⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹ := by
    rw [hfac, hsr, hdecomp']
  have hk1 : κ1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ = κ1 x := by
    have hxeq : x = ⟨(u : G) * (r : G),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ := by
      apply Subtype.ext
      exact hx
    rw [hxeq]
    have hcu : ⁅(c.s : G), (u : G)⁆ ∈ c.H0 := by
      have hu1 : c.s * (u : G) * c.s⁻¹ ∈ c.U := s_normalizes_U c u.2
      have hw : (c.s * (u : G) * c.s⁻¹) * (u : G)⁻¹ = ⁅(c.s : G), (u : G)⁆ := by
        rw [commutatorElement_def]
      rw [← hw]
      exact (h12.U_normal_in_H0).1 (c.U.mul_mem hu1 (c.U.inv_mem u.2))
    have hconj : (⟨c.s * ((u : G) * (r : G)) * c.s⁻¹,
          s_normalizes_H0 c h12 ⟨(u : G) * (r : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩⟩ : ↥c.H0) =
        ⟨⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹,
          c.H0.mul_mem (c.H0.mul_mem hcu ((h12.U_normal_in_H0).1 u.2))
            (S0_le_H0 c (c.S0.inv_mem r.2))⟩ := by
      apply Subtype.ext
      exact hval
    rw [hconj]
    have h1 : κ1 ⟨⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹,
          c.H0.mul_mem (c.H0.mul_mem hcu ((h12.U_normal_in_H0).1 u.2))
            (S0_le_H0 c (c.S0.inv_mem r.2))⟩ =
        κ1 ⟨⁅(c.s : G), (u : G)⁆, hcu⟩ * κ1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ *
          κ1 ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ := by
      have hpr : (⟨⁅(c.s : G), (u : G)⁆, hcu⟩ *
            ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ *
            ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ : ↥c.H0) =
          ⟨⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹,
            c.H0.mul_mem (c.H0.mul_mem hcu ((h12.U_normal_in_H0).1 u.2))
              (S0_le_H0 c (c.S0.inv_mem r.2))⟩ := rfl
      rw [← hpr]
      rw [linearChar_mul hκ1lin]
      rw [linearChar_mul hκ1lin]
    rw [h1]
    have hκ1com : κ1 ⟨⁅(c.s : G), (u : G)⁆, hcu⟩ = 1 :=
      hκ1comm ⟨⁅(c.s : G), (u : G)⁆, hcu⟩ hcom
    have hκ1r : κ1 ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ = 1 :=
      hκ1S0 ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ (c.S0.inv_mem r.2)
    rw [hκ1com, hκ1r]
    have h2 : κ1 ⟨(u : G) * (r : G),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ =
        κ1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ * κ1 ⟨(r : G), S0_le_H0 c r.2⟩ := by
      have hpr : (⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ * ⟨(r : G), S0_le_H0 c r.2⟩ : ↥c.H0) =
          ⟨(u : G) * (r : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ := rfl
      rw [← hpr]
      rw [linearChar_mul hκ1lin]
    rw [h2]
    have hκ1r2 : κ1 ⟨(r : G), S0_le_H0 c r.2⟩ = 1 := hκ1S0 ⟨(r : G), S0_le_H0 c r.2⟩ r.2
    rw [hκ1r2]
    ring
  exact hk1

/-- `Λ_{κ1} = 1`: the stabilizer of `κ1` in `Λ` is trivial, so `|Λ·κ1| = |Λ|`. -/
theorem kappaOne_stab (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] :
    (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
      LambdaChar l.1 * kappaOne c h12 = kappaOne c h12)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  apply Finset.ext
  intro l
  constructor
  · intro hl
    have h := (Finset.mem_filter.mp hl).2
    rw [Finset.mem_singleton]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change l.1 x = 1
    have hx := congrFun h x
    have hx' : (l.1 x : ℂ) * (kappaOne c h12 x : ℂ) =
        (kappaOne c h12 x : ℂ) := by
      simpa [LambdaChar] using hx
    have hκnz : (kappaOne c h12 x : ℂ) ≠ 0 :=
      linearChar_ne_zero (kappaOne_isLinear c h12) x
    have hx'' : (l.1 x : ℂ) = 1 :=
      mul_right_cancel₀ hκnz (by simpa [one_mul] using hx')
    exact Units.ext hx''
  · intro hl
    have hl1 : l = 1 := by simpa using (Finset.mem_singleton.mp hl)
    subst l
    rw [Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    funext x
    simp [LambdaChar]

/-- `κl = λl·κ1` (the paper's `κi = λi·κ1`). -/
public def kappa (c : Hyp11 G) (κ1 : ClassFunction (↥c.H0))
    (l : LambdaHom c.H0 c.U) : ClassFunction (↥c.H0) :=
  LambdaChar l.1 * κ1

/-- The defining equation for `kappa`, exposed without making downstream
simplification unfold the definition itself. -/
public theorem kappa_eq_lambda_mul (c : Hyp11 G)
    (κ1 : ClassFunction (↥c.H0)) (l : LambdaHom c.H0 c.U) :
    kappa c κ1 l = LambdaChar l.1 * κ1 := by
  unfold kappa
  rfl

/-- The product of two linear characters is linear. -/
private lemma isLinearCharacter_mul (c : Hyp11 G) (h12 : Hyp12 c)
    {φ ψ : ClassFunction (↥c.H0)} (hφ : IsLinearCharacter φ) (hψ : IsLinearCharacter ψ) :
    IsLinearCharacter (φ * ψ) := by
  let φh := linearCharHom hφ
  let ψh := linearCharHom hψ
  convert isLinearCharacter_of_hom (G := ↥c.H0) (φh * ψh) using 1
  funext x
  rfl

/-- `ΛChar l` is a linear character for every `l ∈ Λ`. -/
private lemma LambdaChar_isLinear (c : Hyp11 G) (l : LambdaHom c.H0 c.U) :
    IsLinearCharacter (LambdaChar l.1) := by
  convert isLinearCharacter_of_hom (G := ↥c.H0) (l.1) using 1
  rfl

/-- `λ^s = λ⁻¹` for `λ ∈ Λ` (`s` inverts `S0` and `U` is `s`-invariant, `λ`
is trivial on `U`). -/
private lemma LambdaChar_conj_eq_inv (c : Hyp11 G) (h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) :
    conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) = (LambdaChar l.1)⁻¹ := by
  classical
  funext x
  change (l.1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ℂ) = (l.1 x : ℂ)⁻¹
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  have hsr : c.s * (r : G) * c.s⁻¹ = (r : G)⁻¹ := s_inverts_S0 c r.2
  have hsu : c.s * (u : G) * c.s⁻¹ ∈ c.U := s_normalizes_U c u.2
  have hxeq : (⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ↥c.H0) =
      ⟨(c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 hsu) (S0_le_H0 c (by rw [hsr]; exact (c.S0 : Subgroup G).inv_mem r.2))⟩ := by
    apply Subtype.ext
    change c.s * (x : G) * c.s⁻¹ =
      (c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹)
    rw [hx]
    group
  rw [hxeq]
  have hl_u : l.1 ⟨(c.s * (u : G) * c.s⁻¹), (h12.U_normal_in_H0).1 hsu⟩ = 1 :=
    l.2 ⟨(c.s * (u : G) * c.s⁻¹), (h12.U_normal_in_H0).1 hsu⟩ hsu
  have hl_r : l.1 ⟨(c.s * (r : G) * c.s⁻¹), S0_le_H0 c (by rw [hsr]; exact (c.S0 : Subgroup G).inv_mem r.2)⟩ =
      (l.1 ⟨(r : G), S0_le_H0 c r.2⟩)⁻¹ := by
    have hpair : ⟨(c.s * (r : G) * c.s⁻¹), S0_le_H0 c (by rw [hsr]; exact (c.S0 : Subgroup G).inv_mem r.2)⟩ =
        (⟨(r : G), S0_le_H0 c r.2⟩ : ↥c.H0)⁻¹ := by
      apply Subtype.ext
      change c.s * (r : G) * c.s⁻¹ = (r : G)⁻¹
      exact hsr
    rw [hpair]
    exact map_inv l.1 ⟨(r : G), S0_le_H0 c r.2⟩
  have hxeq' : (⟨(c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 hsu) (S0_le_H0 c (by rw [hsr]; exact (c.S0 : Subgroup G).inv_mem r.2))⟩ : ↥c.H0) =
      ⟨(c.s * (u : G) * c.s⁻¹), (h12.U_normal_in_H0).1 hsu⟩ *
        ⟨(c.s * (r : G) * c.s⁻¹), S0_le_H0 c (by rw [hsr]; exact (c.S0 : Subgroup G).inv_mem r.2)⟩ := rfl
  rw [hxeq', map_mul, hl_u, hl_r]
  simp
  have hxr : x = ⟨(u : G) * (r : G),
      c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ := by
    apply Subtype.ext
    exact hx
  have hl_u' : l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ = 1 :=
    l.2 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ u.2
  have hxr' : (l.1 x : ℂ) = (l.1 ⟨(r : G), S0_le_H0 c r.2⟩ : ℂ) := by
    have hxr0 : l.1 x = l.1 ⟨(u : G) * (r : G),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ :=
      congrArg l.1 hxr
    have hmul : l.1 ⟨(u : G) * (r : G),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ =
        l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ *
          l.1 ⟨(r : G), S0_le_H0 c r.2⟩ :=
      map_mul l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩
        ⟨(r : G), S0_le_H0 c r.2⟩
    calc
      (l.1 x : ℂ) = (l.1 ⟨(u : G) * (r : G),
          c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ : ℂ) := by
        rw [hxr0]
      _ = (l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ *
          l.1 ⟨(r : G), S0_le_H0 c r.2⟩ : ℂ) := by
        exact congrArg (fun z : ℂˣ => (z : ℂ)) hmul
      _ = (l.1 ⟨(r : G), S0_le_H0 c r.2⟩ : ℂ) := by rw [hl_u']; simp
  simpa [hxr']

/-- Each `κi` is a linear (hence irreducible) character of `H0`. -/
theorem kappa_isLinear (c : Hyp11 G) (h12 : Hyp12 c) {κ1 : ClassFunction (↥c.H0)}
    (hκ1 : IsLinearCharacter κ1) (l : LambdaHom c.H0 c.U) :
    IsLinearCharacter (kappa c κ1 l) := by
  unfold kappa
  exact isLinearCharacter_mul c h12 (LambdaChar_isLinear c l) hκ1

/-- `s` fixes no `κi` except `κ1` and `κ2`. -/
theorem kappa_conj_fixed_iff (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    (l : LambdaHom c.H0 c.U) :
    conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 l) = kappa c κ1 l ↔
      l = 1 ∨ l = lambdaTwo c h12 := by
  have hκ1fix := kappaOne_fixed_by_s c h12 hκ1lin hκ1S0 hκ1comm
  have hconj : conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 l) =
      (LambdaChar l.1)⁻¹ * κ1 := by
    unfold kappa
    ext x
    have hκ := congrFun hκ1fix x
    have hlamb := congrFun (LambdaChar_conj_eq_inv c h12 l) x
    have hκ' : κ1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ = κ1 x := by
      simpa [conjChar, conjMonoidHom] using hκ
    have hlamb' : (l.1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ℂ) =
        (l.1 x : ℂ)⁻¹ := by
      simpa [conjChar, conjMonoidHom, LambdaChar] using hlamb
    simp [conjChar, conjMonoidHom, LambdaChar, hκ', hlamb']
  have hiff : (conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 l) =
      kappa c κ1 l) ↔ (LambdaChar l.1)⁻¹ = LambdaChar l.1 := by
    constructor
    · intro h
      funext x
      have hx := congrFun h x
      rw [hconj] at hx
      change (l.1 x : ℂ)⁻¹ * (κ1 x : ℂ) = (l.1 x : ℂ) * (κ1 x : ℂ) at hx
      have hκnz : (κ1 x : ℂ) ≠ 0 := linearChar_ne_zero hκ1lin x
      exact mul_right_cancel₀ hκnz hx
    · intro hl
      ext x
      rw [hconj]
      have hx := congrFun hl x
      have hx' : (l.1 x : ℂ)⁻¹ = (l.1 x : ℂ) := by simpa [LambdaChar] using hx
      simp [LambdaChar, kappa, hx']
  have hc1 : conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) =
      (LambdaChar l.1)⁻¹ := LambdaChar_conj_eq_inv c h12 l
  rw [hiff]
  rw [← hc1]
  exact lambda_fixed_by_s_iff c h12 l

/-- `φ` is a constituent of the generalized character `ψ`: `φ` or `-φ` is
irreducible and occurs in `ψ` with non-zero multiplicity (the paper's notion
of a constituent; for the generalized characters occurring in this paper the
two definitions agree). -/
public def IsConstituentOf {G : Type u} [Group G] [Fintype G]
    (φ ψ : ClassFunction G) : Prop :=
  (IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)) ∧ scalarProduct G φ ψ ≠ 0

/-- `U ∩ S = 1`: the odd core of `H` meets the Sylow 2-subgroup trivially. -/
private lemma U_inter_S_eq_bot' (c : Hyp11 G) {x : G} (hxU : x ∈ c.U)
    (hxS : x ∈ (c.S : Subgroup G)) : x = 1 := by
  classical
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
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
  have hpow : orderOf x ∣ 2 ^ (c.m + 1) := by
    have hpow' : orderOf x ∣ 2 * 2 ^ c.m := by
      rw [← S_nat_card c]
      exact hordS
    rwa [show 2 * 2 ^ c.m = 2 ^ (c.m + 1) by ring] at hpow'
  have hcop' : Nat.Coprime (2 ^ (c.m + 1)) (Nat.card ↥c.U) := by
    exact hcop.pow_left _
  have h1' : orderOf x = 1 := by
    have hdvd : orderOf x ∣ 1 := by
      rw [← hcop'.gcd_eq_one]
      exact Nat.dvd_gcd hpow hordU
    exact Nat.dvd_one.mp hdvd
  exact hx1 (orderOf_eq_one_iff.mp h1')

/-- An element of `S` lies in `H0` iff it lies in `S0`. -/
private lemma S_mem_H0_iff_S0' (c : Hyp11 G) (h12 : Hyp12 c)
    {x : G} (hx : x ∈ (c.S : Subgroup G)) : x ∈ c.H0 ↔ x ∈ (c.S0 : Subgroup G) := by
  constructor
  · intro hxH0
    rcases H0_eq_U_mul_S0 c h12 (x := ⟨x, hxH0⟩) with ⟨u, r, hxEq⟩
    have hxEq' : x = (u : G) * (r : G) := by
      simpa using hxEq
    have hxr : x * (r : G)⁻¹ = (u : G) := by
      calc
        x * (r : G)⁻¹ = ((u : G) * (r : G)) * (r : G)⁻¹ := by rw [hxEq']
        _ = (u : G) := by group
    have hxrS : x * (r : G)⁻¹ ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem hx ((c.S : Subgroup G).inv_mem (c.S0_le_S r.2))
    have hxrU : x * (r : G)⁻¹ ∈ c.U := by
      rw [hxr]
      exact u.2
    have hxr1 : x * (r : G)⁻¹ = 1 := U_inter_S_eq_bot' c hxrU hxrS
    have hxr' : x = (r : G) := by
      calc
        x = (x * (r : G)⁻¹) * (r : G) := by group
        _ = 1 * (r : G) := by rw [hxr1]
        _ = (r : G) := by simp
    rw [hxr']
    exact r.2
  · intro hxS0
    exact S0_le_H0 c hxS0

/-- `s ∉ H0` (the `'` distinguishes it from the private copy of the same
name in `Section2/Lemma22.lean`). -/
public lemma s_not_mem_H0' (c : Hyp11 G) (h12 : Hyp12 c) : c.s ∉ c.H0 := by
  intro h1
  exact c.s_not_mem_S0 ((S_mem_H0_iff_S0' c h12 c.s_mem_S).mp h1)

/-! ## The index facts `|H : H0| = 2` and `t1^H ∩ t2^H = ∅`

The two facts every downstream proof of Sections 2--4 blocks on.  Both follow
directly from the paper's Hypothesis-1.1 notation-block component
`H_eq_US : U ⊔ S = H` (with `U = O(H)`): `H0 = U·S0` has index two in
`H = U·S = H0·⟨s⟩`, and the two reflections `t1, t2` of `S` (with
`S0 = ⟨t1·t2⟩`) are not conjugate in `H` — after reducing to an `S`-conjugacy
via `H = U·S` and `U ∩ S = 1`, the dihedral model `S ≅ D_{2^m}` separates the
two reflection classes by the parity of the rotation index (`m = 1` is the
abelian `D₂ = V₄` case). -/

/-- `U ⊴ H`: conjugation by any element of `H` preserves `U = O(H)`. -/
private lemma U_normal_in_H (c : Hyp11 G) {h u : G} (hh : h ∈ c.H) (hu : u ∈ c.U) :
    h * u * h⁻¹ ∈ c.U := by
  have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hu
  have huH : u ∈ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
  have hchar : (pPrimeCore 2 c.H).Characteristic :=
    pPrimeCore_characteristic (p := 2) (G := c.H)
  have hcomap : (pPrimeCore 2 c.H) ≤ (pPrimeCore 2 c.H).comap
      (MulAut.conj ⟨h, hh⟩).toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) (MulAut.conj ⟨h, hh⟩)
  have huK : (⟨u, huH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
    rcases (Subgroup.mem_map.mp huU) with ⟨x, hx, hxeq⟩
    have hxeq' : (⟨u, huH⟩ : ↥c.H) = x := by
      ext
      simpa using hxeq.symm
    simpa [hxeq'] using hx
  have hconj : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ ∈ pPrimeCore 2 c.H :=
    Subgroup.mem_comap.mp (hcomap huK)
  refine (Subgroup.mem_map.mpr ?_)
  refine ⟨⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩, ?_, rfl⟩
  have hcx : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ =
      (⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩ : ↥c.H) := by
    ext
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hcx]
  exact hconj

/-- Every element of `S` normalizes `U = O(H)` (from `U ⊴ H` and `S ≤ H`). -/
private lemma S_le_normalizer_U (c : Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact U_normal_in_H c (S_le_H c hs) hu
  · intro hsu
    have hs' : s⁻¹ ∈ c.H := c.H.inv_mem (S_le_H c hs)
    have h1 := U_normal_in_H c hs' hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

set_option linter.unusedSectionVars false in
/-- The image of a cyclic subgroup under a monoid hom is cyclic. -/
private lemma zpowers_map {N : Type*} [Group N] (f : G →* N) (x : G) :
    (Subgroup.zpowers x).map f = Subgroup.zpowers (f x) := by
  ext y
  constructor
  · intro hy
    rcases (Subgroup.mem_map.mp hy) with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_zpowers_iff] at hz ⊢
    rcases hz with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk]
    exact (map_zpow f x k).symm
  · intro hy
    rcases (Subgroup.mem_zpowers_iff.mp hy) with ⟨k, hk⟩
    refine (Subgroup.mem_map).2 ?_
    refine ⟨x ^ k, (Subgroup.mem_zpowers_iff).2 ⟨k, rfl⟩, ?_⟩
    rw [map_zpow]
    exact hk

set_option linter.unusedSectionVars false in
/-- Set products are associative. -/
private lemma set_mul_assoc (A B C : Set G) : A * B * C = A * (B * C) := by
  ext x
  constructor
  · rintro ⟨ab, hab, c, hc, rfl⟩
    rcases hab with ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b * c, ?_, ?_⟩
    · exact ⟨b, hb, c, hc, rfl⟩
    · group
  · rintro ⟨a, ha, bc, hbc, rfl⟩
    rcases hbc with ⟨b, hb, c, hc, rfl⟩
    refine ⟨a * b, ?_, c, hc, ?_⟩
    · exact ⟨a, ha, b, hb, rfl⟩
    · group

set_option linter.unusedSectionVars false in
/-- If `K` has index two in `H` and `x ∈ H ∖ K`, then `H = K ⊔ ⟨x⟩`. -/
private lemma eq_sup_zpowers_of_index_two {H K : Subgroup G} (hK : K ≤ H) {x : G}
    (hxH : x ∈ H) (hxK : x ∉ K) (hindex : (K.subgroupOf H).index = 2) :
    H = K ⊔ Subgroup.zpowers x := by
  classical
  let Q := ↥H ⧸ (K.subgroupOf H)
  have hQcard : Nat.card Q = 2 := by
    exact hindex
  let q1 : Q := QuotientGroup.mk (s := K.subgroupOf H) (1 : ↥H)
  let q2 : Q := QuotientGroup.mk (s := K.subgroupOf H) (⟨x, hxH⟩ : ↥H)
  have hq1q2 : q1 ≠ q2 := by
    intro h
    exact hxK (by
      simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
        using (QuotientGroup.eq.mp h))
  have hall : ∀ z : Q, z = q1 ∨ z = q2 := by
    intro z
    by_cases hz : z = q1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' q1).mp hQcard with ⟨y0, _hy0ne, hy0uniq⟩
      exact Or.inr ((hy0uniq z hz).trans (hy0uniq q2 (Ne.symm hq1q2)).symm)
  refine le_antisymm ?_ ?_
  · intro y hy
    by_cases hyq : QuotientGroup.mk (s := K.subgroupOf H) (⟨y, hy⟩ : ↥H) = q1
    · exact SetLike.le_def.mp le_sup_left (by
        simpa [inv_inv] using (K.inv_mem (by
          simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
            using (QuotientGroup.eq.mp hyq))))
    · have hyq2 : QuotientGroup.mk (s := K.subgroupOf H) (⟨y, hy⟩ : ↥H) = q2 :=
        (hall (QuotientGroup.mk (s := K.subgroupOf H) (⟨y, hy⟩ : ↥H))).resolve_left hyq
      have hmem : y⁻¹ * x ∈ K := by
        simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
          using (QuotientGroup.eq.mp hyq2)
      have hxEq : x * (y⁻¹ * x)⁻¹ = y := by group
      rw [← hxEq]
      exact (K ⊔ Subgroup.zpowers x).mul_mem
        (SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers x))
        (SetLike.le_def.mp le_sup_left (K.inv_mem hmem))
  · exact sup_le hK (by
      intro z hz
      rcases (Subgroup.mem_zpowers_iff.mp hz) with ⟨k, hk⟩
      rw [← hk]
      exact H.zpow_mem hxH k)

/-- The parity contradiction: `r 1 ∈ ⟨r (b − a)⟩ ≤ ⟨r 2⟩` forces
`n = orderOf (r 1) ∣ orderOf (r 2) ≤ n/2 < n`. -/
private lemma dihedral_sr_not_conj_of_rotation_sq (n : ℕ) [NeZero n] (hn2 : 2 ∣ n)
    {a b : ZMod n}
    (hgen : (r 1 : DihedralGroup n) ∈ Subgroup.zpowers (r (b - a) : DihedralGroup n))
    (hmem : (r (b - a) : DihedralGroup n) ∈ Subgroup.zpowers (r 2 : DihedralGroup n)) :
    False := by
  have hdvd1 : orderOf (r 1 : DihedralGroup n) ∣ orderOf (r (b - a) : DihedralGroup n) :=
    orderOf_dvd_of_mem_zpowers hgen
  have hdvd2 : orderOf (r (b - a) : DihedralGroup n) ∣ orderOf (r 2 : DihedralGroup n) :=
    orderOf_dvd_of_mem_zpowers hmem
  have hle1 : n ≤ orderOf (r (b - a) : DihedralGroup n) :=
    orderOf_r_one.symm.trans_le (Nat.le_of_dvd (orderOf_pos _) hdvd1)
  have hord2 : orderOf (r 2 : DihedralGroup n) ≤ n / 2 := by
    have hpow : (r 2 : DihedralGroup n) ^ (n / 2) = 1 := by
      rw [r_pow]
      have h2 : 2 * (n / 2) = n := Nat.mul_div_cancel' hn2
      have h3 : (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = 0 := by
        norm_cast
        rw [h2]
        exact ZMod.natCast_self n
      rw [h3]
      rfl
    have h2le : 2 ≤ n := by
      have hn0 : 0 < n := NeZero.pos n
      omega
    have hdiv : 0 < n / 2 := by
      omega
    exact Nat.le_of_dvd hdiv (orderOf_dvd_of_pow_eq_one hpow)
  have hle2 : orderOf (r (b - a) : DihedralGroup n) ≤ orderOf (r 2 : DihedralGroup n) :=
    Nat.le_of_dvd (orderOf_pos _) hdvd2
  have hle : n ≤ n / 2 := le_trans hle1 (le_trans hle2 hord2)
  exact (Nat.not_lt_of_ge hle) (Nat.div_lt_self (NeZero.pos n) (by norm_num))

/-- In the dihedral model, if `r (b − a)` generates the rotation subgroup
`⟨r 1⟩` (i.e. `S0 = ⟨t1·t2⟩` maps to it), then the reflections `sr a` and
`sr b` are not conjugate: conjugation by a rotation sends `sr a` to
`sr (a − 2c)` and by a reflection to `sr (2c − a)`, so `b − a = 2·d` lands in
`⟨r 2⟩`, whose elements have order dividing `n/2 < n`. -/
private lemma dihedral_sr_not_conj (n : ℕ) [NeZero n] (hn2 : 2 ∣ n) {a b : ZMod n}
    (hgen : (r 1 : DihedralGroup n) ∈ Subgroup.zpowers (r (b - a) : DihedralGroup n))
    (hconj : ∃ w : DihedralGroup n, w * (sr a : DihedralGroup n) * w⁻¹ = sr b) :
    False := by
  rcases hconj with ⟨w, hw⟩
  rcases w with ⟨c⟩ | ⟨c⟩
  · -- w = r c: sr b = sr (a - 2c)
    have hmem : (r (b - a) : DihedralGroup n) ∈ Subgroup.zpowers (r 2 : DihedralGroup n) := by
      have hb : b = a - 2 * c := by
        have h' : (sr b : DihedralGroup n) = sr (a - 2 * c) := by
          calc
            (sr b : DihedralGroup n) = (r c : DihedralGroup n) * sr a * (r c)⁻¹ := hw.symm
            _ = sr (a - 2 * c) := by rw [inv_r, r_mul_sr, sr_mul_r]; congr 1; ring
        injection h' with hb
      have hd : b - a = -(2 * c) := by rw [hb]; ring
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨-c.val, ?_⟩
      rw [r_zpow]
      congr 1
      rw [hd]
      rw [Int.cast_neg, Int.cast_natCast]
      rw [ZMod.natCast_zmod_val c]
      ring
    exact dihedral_sr_not_conj_of_rotation_sq n hn2 hgen hmem
  · -- w = sr c: sr b = sr (2c - a)
    have hmem : (r (b - a) : DihedralGroup n) ∈ Subgroup.zpowers (r 2 : DihedralGroup n) := by
      have hb : b = 2 * c - a := by
        have h' : (sr b : DihedralGroup n) = sr (2 * c - a) := by
          calc
            (sr b : DihedralGroup n) = (sr c : DihedralGroup n) * sr a * (sr c)⁻¹ := hw.symm
            _ = sr (2 * c - a) := by rw [inv_sr, sr_mul_sr, r_mul_sr]; congr 1; ring
        injection h' with hb
      have hd : b - a = 2 * (c - a) := by rw [hb]; ring
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨(c - a).val, ?_⟩
      rw [r_zpow]
      congr 1
      rw [hd]
      rw [Int.cast_natCast]
      rw [ZMod.natCast_zmod_val (c - a)]
    exact dihedral_sr_not_conj_of_rotation_sq n hn2 hgen hmem

/-- Every rotation `r a` lies in `⟨r 1⟩`. -/
private lemma mem_r_one_zpowers (n : ℕ) [NeZero n] (a : ZMod n) :
    (r a : DihedralGroup n) ∈ Subgroup.zpowers (r 1 : DihedralGroup n) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(a.val : ℤ), ?_⟩
  rw [r_zpow]
  congr 1
  rw [Int.cast_natCast]
  rw [ZMod.natCast_zmod_val a]
  simp

/-- `DihedralGroup 2` (the Klein four group) is commutative. -/
private lemma dihedral2_comm (w1 w2 : DihedralGroup 2) : w1 * w2 = w2 * w1 := by
  rcases w1 with ⟨a⟩ | ⟨a⟩ <;> rcases w2 with ⟨b⟩ | ⟨b⟩ <;>
    fin_cases a <;> fin_cases b <;> decide

/-- `DihedralGroup n` is commutative when `n = 2`. -/
private lemma dihedral_comm_of_two {n : ℕ} (hn : n = 2) (w1 w2 : DihedralGroup n) :
    w1 * w2 = w2 * w1 := by
  subst hn
  exact dihedral2_comm w1 w2

/-- `t1 ∈ H`. -/
public lemma t1_mem_H (c : Hyp11 G) : c.t1 ∈ c.H := S_le_H c c.t1_mem_S

/-- `t2 ∈ H`. -/
public lemma t2_mem_H (c : Hyp11 G) : c.t2 ∈ c.H := S_le_H c c.t2_mem_S

/-- An `H`-conjugacy of `t1` to `t2` can be witnessed inside `S` (from
`H = U·S`, `U ⊴ H` and `U ∩ S = 1`). -/
private lemma t2_conj_mem_S_of_conj_in_H (c : Hyp11 G) {g : G} (hg : g ∈ c.H)
    (hconj : g * c.t1 * g⁻¹ = c.t2) :
    ∃ s : G, s ∈ (c.S : Subgroup G) ∧ s * c.t1 * s⁻¹ = c.t2 := by
  classical
  have hHset : (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    rw [← c.H_eq_US]
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
      (S_le_normalizer_U c)
  have hg' : g ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    rw [← hHset]
    exact hg
  rcases hg' with ⟨u, hu, s, hs, hEq⟩
  refine ⟨s, hs, ?_⟩
  have hx : s * c.t1 * s⁻¹ ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).mul_mem ((c.S : Subgroup G).mul_mem hs c.t1_mem_S)
      ((c.S : Subgroup G).inv_mem hs)
  have hxH : s * c.t1 * s⁻¹ ∈ c.H := S_le_H c hx
  have hEq2 : c.t2 = u * (s * c.t1 * s⁻¹) * u⁻¹ := by
    calc
      c.t2 = g * c.t1 * g⁻¹ := hconj.symm
      _ = u * (s * c.t1 * s⁻¹) * u⁻¹ := by
        rw [← hEq]
        group
  have hU : c.t2 * (s * c.t1 * s⁻¹)⁻¹ ∈ c.U := by
    have h1 : (s * c.t1 * s⁻¹) * u⁻¹ * (s * c.t1 * s⁻¹)⁻¹ ∈ c.U :=
      U_normal_in_H c hxH (c.U.inv_mem hu)
    have hEq3 : c.t2 * (s * c.t1 * s⁻¹)⁻¹ =
        u * ((s * c.t1 * s⁻¹) * u⁻¹ * (s * c.t1 * s⁻¹)⁻¹) := by
      rw [hEq2]
      group
    rw [hEq3]
    exact c.U.mul_mem hu h1
  have hS : c.t2 * (s * c.t1 * s⁻¹)⁻¹ ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).mul_mem c.t2_mem_S ((c.S : Subgroup G).inv_mem hx)
  have hone : c.t2 * (s * c.t1 * s⁻¹)⁻¹ = 1 := U_inter_S_eq_bot' c hU hS
  calc
    s * c.t1 * s⁻¹ = (c.t2 * (s * c.t1 * s⁻¹)⁻¹)⁻¹ * c.t2 := by group
    _ = 1⁻¹ * c.t2 := by rw [hone]
    _ = c.t2 := by simp

/-- `|H : H0| = 2`: `H0 = U·S0` has index two in `H = C_G(t)` (the paper's
`H0 = US0 (a subgroup of index 2 in H = US = H0⟨s⟩)` of the Hypothesis-1.1
notation block; from the `H_eq_US` component of `Hyp11`: `H = U·S` and
`S = S0·⟨s⟩` give `H = H0·⟨s⟩`, while `s ∉ H0`). -/
public theorem H0_index (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.H0.subgroupOf c.H).index = 2 := by
  classical
  have hSjoin : (c.S : Subgroup G) = (c.S0 : Subgroup G) ⊔ Subgroup.zpowers c.s :=
    eq_sup_zpowers_of_index_two c.S0_le_S c.s_mem_S c.s_not_mem_S0 (S0_index c)
  have hS0mem : Subgroup.zpowers c.s ≤ Subgroup.normalizer ((c.S0 : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact S_conj_mem_S0 c c.s_mem_S hx
    · intro hx
      have h1 := S_conj_mem_S0 c ((c.S : Subgroup G).inv_mem c.s_mem_S) hx
      convert h1 using 1
      group
  have hSset : (↑(c.S : Subgroup G) : Set G) =
      ((c.S0 : Subgroup G) : Set G) * (Subgroup.zpowers c.s : Set G) := by
    rw [hSjoin]
    exact Subgroup.coe_mul_of_right_le_normalizer_left (c.S0 : Subgroup G)
      (Subgroup.zpowers c.s) hS0mem
  have hHset : (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
    rw [← c.H_eq_US]
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
      (S_le_normalizer_U c)
  have hH0set : (↑c.H0 : Set G) = (c.U : Set G) * ((c.S0 : Subgroup G) : Set G) := by
    exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S0 : Subgroup G)
      (S0_le_normalizer_U c h12)
  have hH0mul : (↑c.H : Set G) = (c.H0 : Set G) * (Subgroup.zpowers c.s : Set G) := by
    calc
      (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := hHset
      _ = (c.U : Set G) * (((c.S0 : Subgroup G) : Set G) * (Subgroup.zpowers c.s : Set G)) := by
            rw [hSset]
      _ = ((c.U : Set G) * (c.S0 : Subgroup G)) * (Subgroup.zpowers c.s : Set G) := by
            rw [← set_mul_assoc]
      _ = (c.H0 : Set G) * (Subgroup.zpowers c.s : Set G) := by rw [hH0set]
  rw [Subgroup.index_eq_two_iff_exists_notMem_and']
  refine ⟨⟨c.s, s_mem_H c⟩, ?_, ?_⟩
  · simpa [Subgroup.mem_subgroupOf] using (s_not_mem_H0' c h12)
  · intro b
    have hb : (b : G) ∈ (↑c.H : Set G) := b.2
    have hb' : (b : G) ∈ (c.H0 : Set G) * (Subgroup.zpowers c.s : Set G) := by
      rw [← hH0mul]
      exact hb
    rcases hb' with ⟨h0, hh0, x, hx, hEq⟩
    rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, hk⟩
    rcases Int.even_or_odd k with ⟨n, hn⟩ | ⟨n, hn⟩
    · -- k even: x = 1, so b = h0 ∈ H0
      right
      have hx1 : x = 1 := by
        calc
          x = c.s ^ k := hk.symm
          _ = c.s ^ (2 * n) := by rw [hn, show n + n = 2 * n by ring]
          _ = (c.s * c.s) ^ n := by
            rw [show 2 * n = n + n by ring, zpow_add]
            rw [← (Commute.refl c.s).mul_zpow n]
          _ = 1 := by
            have hs2' : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
            rw [hs2']
            simp
      have hb0 : (b : G) = h0 := by
        calc
          (b : G) = h0 * x := hEq.symm
          _ = h0 * 1 := by rw [hx1]
          _ = h0 := by simp
      rw [Subgroup.mem_subgroupOf]
      rwa [hb0]
    · -- k odd: s·b = s·h0·s⁻¹ ∈ H0
      left
      have hxEq : x = c.s ^ (2 * n + 1) := by
        calc
          x = c.s ^ k := hk.symm
          _ = c.s ^ (2 * n + 1) := by rw [hn]
      have hx1 : c.s * x = 1 := by
        calc
          c.s * x = c.s * c.s ^ (2 * n + 1) := by rw [hxEq]
          _ = c.s ^ (2 * n + 2) := by
            rw [← zpow_one_add]
            congr 1
            ring
          _ = (c.s * c.s) ^ (n + 1) := by
            rw [show 2 * n + 2 = 2 * (n + 1) by ring]
            rw [show 2 * (n + 1) = (n + 1) + (n + 1) by ring, zpow_add]
            rw [← (Commute.refl c.s).mul_zpow (n + 1)]
          _ = 1 := by
            have hs2' : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
            rw [hs2']
            simp
      have hmain : c.s * (h0 * x) = c.s * h0 * c.s⁻¹ := by
        calc
          c.s * (h0 * x) = (c.s * h0 * c.s⁻¹) * (c.s * x) := by group
          _ = (c.s * h0 * c.s⁻¹) * 1 := by rw [hx1]
          _ = c.s * h0 * c.s⁻¹ := by simp
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.coe_mul]
      change c.s * (b : G) ∈ c.H0
      rw [← hEq, hmain]
      exact (h12.H0_normal_in_H).2 c.s (s_mem_H c) h0 hh0

/-- `t1^H ∩ t2^H = ∅`: the `H`-conjugacy classes of the two reflections
`t1, t2` of `S` are disjoint in `H = C_G(t)` (from `H = U·S`, `U ∩ S = 1`,
and the dihedral structure of `S` with `S0 = ⟨t1·t2⟩`: `t1, t2` have opposite
rotation parity in `S ≅ D_{2^m}`). -/
public theorem t1H_disjoint (c : Hyp11 G) (_h12 : Hyp12 c) :
    (ConjClasses.mk (⟨c.t1, t1_mem_H c⟩ : ↥c.H)).carrier ∩
      (ConjClasses.mk (⟨c.t2, t2_mem_H c⟩ : ↥c.H)).carrier = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hx1 : ConjClasses.mk x = ConjClasses.mk (⟨c.t1, t1_mem_H c⟩ : ↥c.H) :=
    (ConjClasses.mem_carrier_iff_mk_eq.mp hx.1)
  have hx2 : ConjClasses.mk x = ConjClasses.mk (⟨c.t2, t2_mem_H c⟩ : ↥c.H) :=
    (ConjClasses.mem_carrier_iff_mk_eq.mp hx.2)
  have hconj1 : IsConj x (⟨c.t1, t1_mem_H c⟩ : ↥c.H) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hx1
  have hconj2 : IsConj x (⟨c.t2, t2_mem_H c⟩ : ↥c.H) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hx2
  rcases (isConj_iff.mp hconj1) with ⟨g1, hg1⟩
  rcases (isConj_iff.mp hconj2) with ⟨g2, hg2⟩
  have hconjH : (g2 * g1⁻¹) * (⟨c.t1, t1_mem_H c⟩ : ↥c.H) * (g2 * g1⁻¹)⁻¹ =
      (⟨c.t2, t2_mem_H c⟩ : ↥c.H) := by
    calc
      (g2 * g1⁻¹) * (⟨c.t1, t1_mem_H c⟩ : ↥c.H) * (g2 * g1⁻¹)⁻¹
          = g2 * (g1⁻¹ * (⟨c.t1, t1_mem_H c⟩ : ↥c.H) * g1) * g2⁻¹ := by group
      _ = g2 * x * g2⁻¹ := by
        have hinner : g1⁻¹ * (⟨c.t1, t1_mem_H c⟩ : ↥c.H) * g1 = x := by
          calc
            g1⁻¹ * (⟨c.t1, t1_mem_H c⟩ : ↥c.H) * g1 = g1⁻¹ * (g1 * x * g1⁻¹) * g1 := by rw [← hg1]
            _ = x := by group
        rw [hinner]
      _ = ⟨c.t2, t2_mem_H c⟩ := hg2
  have hconj : ((g2 : G) * (g1 : G)⁻¹) * c.t1 * (((g2 : G) * (g1 : G)⁻¹)⁻¹) = c.t2 := by
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
      (congrArg (fun z : ↥c.H => (z : G)) hconjH)
  have hg : ((g2 : G) * (g1 : G)⁻¹) ∈ c.H := c.H.mul_mem g2.2 (c.H.inv_mem g1.2)
  rcases (t2_conj_mem_S_of_conj_in_H c hg hconj) with ⟨s, hs, hsconj⟩
  let n := 2 ^ c.m
  have : NeZero n := ⟨pow_ne_zero c.m (by norm_num)⟩
  let e : ↥(c.S : Subgroup G) ≃* DihedralGroup n := Classical.choice c.dihedralEquiv
  let t1S : ↥(c.S : Subgroup G) := ⟨c.t1, c.t1_mem_S⟩
  let t2S : ↥(c.S : Subgroup G) := ⟨c.t2, c.t2_mem_S⟩
  have hconjE : ∃ w : DihedralGroup n, w * e t1S * w⁻¹ = e t2S := by
    let sS : ↥(c.S : Subgroup G) := ⟨s, hs⟩
    refine ⟨e sS, ?_⟩
    have hEqS : sS * t1S * sS⁻¹ = t2S := by
      apply Subtype.ext
      simpa [sS, t1S, t2S] using hsconj
    simpa [map_mul, map_inv] using congrArg e hEqS
  by_cases hm1 : c.m = 1
  · -- m = 1: |S| = 4 and the model `D₂ = V₄` is abelian, while `t1 ≠ t2`
    have ht1ne : c.t1 ≠ c.t2 := by
      intro h
      have hsq : c.t1 * c.t2 = 1 := by simpa [h, pow_two] using c.t1_involution.2
      have hS0 : (c.S0 : Subgroup G) = ⊥ := by
        rw [c.S0_eq_zpowers, hsq]
        exact Subgroup.zpowers_one_eq_bot
      have hcard : Nat.card ↥(c.S0 : Subgroup G) = 1 := by
        rw [hS0]
        exact Subgroup.card_bot
      have hcard2 : Nat.card ↥(c.S0 : Subgroup G) = 2 := by
        rw [S0_nat_card c, hm1]
        norm_num
      omega
    rcases hconjE with ⟨w, hw⟩
    have hn2 : n = 2 := by
      dsimp [n]
      rw [hm1]
      norm_num
    have hEqE : e t1S = e t2S := by
      calc
        e t1S = e t1S * w * w⁻¹ := by group
        _ = w * e t1S * w⁻¹ := by rw [dihedral_comm_of_two hn2 (e t1S) w]
        _ = e t2S := hw
    exact ht1ne (by
      have hEqS : t1S = t2S := e.injective hEqE
      exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hEqS)
  · -- m ≥ 2: reflection parity in the model
    have hm2 : 2 ≤ c.m := Nat.succ_le_of_lt (lt_of_le_of_ne c.one_le_m (Ne.symm hm1))
    have hS0map : (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
        (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) =
        Subgroup.zpowers (r 1 : DihedralGroup n) :=
      eS0_eq_zpowers_r1 c hm2 e
    have hnot_rot1 : e t1S ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
      intro h
      rw [← hS0map] at h
      rcases (Subgroup.mem_map.mp h) with ⟨y, hy, hyeq⟩
      have hι : Subgroup.inclusion c.S0_le_S y = t1S := e.injective hyeq
      have hyG : (y : G) = c.t1 := congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hι
      exact c.t1_not_mem_S0 (by rw [← hyG]; exact y.2)
    have hnot_rot2 : e t2S ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
      intro h
      rw [← hS0map] at h
      rcases (Subgroup.mem_map.mp h) with ⟨y, hy, hyeq⟩
      have hι : Subgroup.inclusion c.S0_le_S y = t2S := e.injective hyeq
      have hyG : (y : G) = c.t2 := congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hι
      exact c.t2_not_mem_S0 (by rw [← hyG]; exact y.2)
    rcases h1 : e t1S with ⟨a⟩ | ⟨a⟩
    · exfalso
      exact hnot_rot1 (by
        rw [h1]
        exact mem_r_one_zpowers n a)
    · rcases h2 : e t2S with ⟨b⟩ | ⟨b⟩
      · exfalso
        exact hnot_rot2 (by
          rw [h2]
          exact mem_r_one_zpowers n b)
      · -- both reflections: parity contradiction
        have hgen : (r 1 : DihedralGroup n) ∈
            Subgroup.zpowers (r (b - a) : DihedralGroup n) := by
          have hst : Subgroup.zpowers (t1S * t2S) =
              (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map (Subgroup.inclusion c.S0_le_S) := by
            ext x
            constructor
            · intro hx
              rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, hk⟩
              refine (Subgroup.mem_map).2 ?_
              refine ⟨⟨(x : G), ?_⟩, by simp, ?_⟩
              · rw [c.S0_eq_zpowers]
                rw [Subgroup.mem_zpowers_iff]
                exact ⟨k, by
                  simpa [t1S, t2S, Subgroup.coe_mul, Subgroup.coe_zpow] using
                    (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hk)⟩
              · rfl
            · intro hx
              rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, hιy⟩
              have hxG : (x : G) = (y : G) := by
                simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hιy).symm
              have hz : (x : G) ∈ Subgroup.zpowers (c.t1 * c.t2 : G) := by
                have hy : (y : G) ∈ Subgroup.zpowers (c.t1 * c.t2 : G) := by
                  rw [← c.S0_eq_zpowers]
                  exact y.2
                exact hxG ▸ hy
              rcases (Subgroup.mem_zpowers_iff.mp hz) with ⟨k, hk⟩
              rw [Subgroup.mem_zpowers_iff]
              refine ⟨k, ?_⟩
              apply Subtype.ext
              simpa [t1S, t2S, Subgroup.coe_mul, Subgroup.coe_zpow] using hk
          have hmain : Subgroup.zpowers (r (b - a) : DihedralGroup n) =
              (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
                (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) := by
            calc
              Subgroup.zpowers (r (b - a) : DihedralGroup n)
                  = Subgroup.zpowers (e (t1S * t2S)) := by
                      congr 1
                      calc
                        r (b - a) = sr a * sr b := by rw [sr_mul_sr]
                        _ = e t1S * e t2S := by rw [h1, h2]
                        _ = e (t1S * t2S) := by exact (map_mul e t1S t2S).symm
              _ = (Subgroup.zpowers (t1S * t2S)).map e := by
                      simp
              _ = ((⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
                    (Subgroup.inclusion c.S0_le_S)).map e := by rw [hst]
              _ = (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
                    (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) := by
                    simp [Subgroup.map_map]
          rw [hmain, hS0map]
          exact Subgroup.mem_zpowers _
        have hconjE' : ∃ w : DihedralGroup n, w * (sr a : DihedralGroup n) * w⁻¹ = sr b := by
          rcases hconjE with ⟨w, hw⟩
          refine ⟨w, ?_⟩
          simpa [h1, h2] using hw
        exact dihedral_sr_not_conj (n := n) (hn2 := by
          refine ⟨2 ^ (c.m - 1), ?_⟩
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel c.one_le_m]) hgen hconjE'

/-! ## `exists_kappaOne_ne_one`: a non-trivial `κ1` when `B ⊄ U'`

The paper's remark after the definition of `κ1`
(`refs/bender-glauberman-character.tex` L327--L330): if
`B = C_U(S) ⊄ U'`, the linear character `κ1` of `H0` whose kernel contains
`S0` and `[S,U]` can be chosen distinct from `λ1 = 1_{H0}`.

We construct `κ1` as a character of the abelian quotient
`U/(U'·[S,U])` (separating a point of `B \ U'`), extended to `H0 = U·S0`
trivially on `S0`.  The separation of `B` from `U'·[S,U]` uses the
coprime-action decomposition on the abelian group `U/U'`: the fixed points
of the 2-group `S` meet the action-commutator subgroup trivially.
-/

/-- The `U`-part of `x ∈ H0 = U·S0`. -/
private noncomputable def uPart (c : Hyp11 G) (h12 : Hyp12 c) (x : ↥c.H0) :
    ↥c.U :=
  Classical.choose (s0Part_spec c h12 x)

/-- The defining property of `uPart`. -/
private lemma uPart_spec (c : Hyp11 G) (h12 : Hyp12 c) (x : ↥c.H0) :
    ∃ r : ↥(c.S0 : Subgroup G), (x : G) = (uPart c h12 x : G) * (r : G) := by
  classical
  exact ⟨s0Part c h12 x, by simpa [uPart] using Classical.choose_spec (s0Part_spec c h12 x)⟩

/-- The `U`-part is well-defined (`U ∩ S0 = 1`). -/
private lemma uPart_unique (c : Hyp11 G) (h12 : Hyp12 c) {x : ↥c.H0}
    {u : ↥c.U} {r : ↥c.S0} (h : (x : G) = (u : G) * (r : G)) :
    uPart c h12 x = u := by
  rcases uPart_spec c h12 x with ⟨r₀, h₀⟩
  have hr : r₀ = r := H0_decomp_unique c h12 h₀ h
  apply Subtype.ext
  have hEq : (uPart c h12 x : G) * (r₀ : G) = (u : G) * (r : G) := by
    simpa using (h₀.symm.trans h)
  have hEq' : (uPart c h12 x : G) * (r : G) = (u : G) * (r : G) := by
    simpa [hr] using hEq
  exact mul_right_cancel hEq'

/-- The `U`-part of an element of `U` is itself. -/
private lemma uPart_eq_of_mem_U (c : Hyp11 G) (h12 : Hyp12 c) {x : ↥c.H0}
    (hxU : (x : G) ∈ c.U) : uPart c h12 x = ⟨(x : G), hxU⟩ := by
  apply uPart_unique c h12 (u := ⟨(x : G), hxU⟩) (r := 1)
  simp

/-- The `U`-part of an element of `S0` is `1`. -/
private lemma uPart_eq_one_of_mem_S0 (c : Hyp11 G) (h12 : Hyp12 c)
    {x : ↥c.H0} (hxS0 : (x : G) ∈ (c.S0 : Subgroup G)) :
    uPart c h12 x = 1 := by
  apply uPart_unique c h12 (u := 1) (r := ⟨(x : G), hxS0⟩)
  simp

/-- Extend a character `l` of `U` (trivial on `K`) to `H0 = U·S0`, trivially
on `S0`.  The extension is a homomorphism because `l` also kills the defect
`[S0,U]` (which is contained in `K`). -/
private noncomputable def kappaOneHom (c : Hyp11 G) (h12 : Hyp12 c)
    (K : Subgroup G) (hS0K : ⁅(c.S0 : Subgroup G), c.U⁆ ≤ K)
    (l : ↥c.U →* ℂˣ) (hl : ∀ x : ↥c.U, (x : G) ∈ K → l x = 1) :
    ↥c.H0 →* ℂˣ where
  toFun := fun x => l (uPart c h12 x)
  map_one' := by
    change l (uPart c h12 (1 : ↥c.H0)) = 1
    have hup : uPart c h12 (1 : ↥c.H0) = 1 := by
      apply uPart_unique c h12 (u := 1) (r := 1)
      simp
    simp [hup]
  map_mul' := by
    intro x y
    rcases uPart_spec c h12 x with ⟨r₁, hx⟩
    rcases uPart_spec c h12 y with ⟨r₂, hy⟩
    have hconj : ((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹) ∈ c.U :=
      (h12.U_normal_in_H0).2 (r₁ : G) (S0_le_H0 c r₁.2) (uPart c h12 y : G)
        (uPart c h12 y).2
    have hxy : (x * y : G) =
        ((uPart c h12 x : G) * ((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹)) *
          ((r₁ : G) * (r₂ : G)) := by
      calc
        (x * y : G) = (x : G) * (y : G) := rfl
        _ = ((uPart c h12 x : G) * (r₁ : G)) *
            ((uPart c h12 y : G) * (r₂ : G)) := by rw [hx, hy]
        _ = ((uPart c h12 x : G) *
            ((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹)) *
            ((r₁ : G) * (r₂ : G)) := by group
    have hmain : uPart c h12 (x * y) =
        uPart c h12 x * ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩ := by
      apply uPart_unique c h12
        (u := uPart c h12 x * ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩)
        (r := ⟨(r₁ : G) * (r₂ : G), (c.S0 : Subgroup G).mul_mem r₁.2 r₂.2⟩)
      exact hxy
    have hlconj : l ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩ =
        l (uPart c h12 y) := by
      have hcS0 : ⁅(r₁ : G), (uPart c h12 y : G)⁆ ∈ ⁅(c.S0 : Subgroup G), c.U⁆ :=
        Subgroup.commutator_mem_commutator (H₁ := (c.S0 : Subgroup G)) (H₂ := c.U)
          r₁.2 (uPart c h12 y).2
      have hleS0 : ⁅(c.S0 : Subgroup G), c.U⁆ ≤ ⁅(c.S : Subgroup G), c.U⁆ :=
        Subgroup.commutator_mono c.S0_le_S le_rfl
      have hmemK : ((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹) * (uPart c h12 y : G)⁻¹ ∈ K := by
        have hEq : ((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹) * (uPart c h12 y : G)⁻¹ =
            ⁅(r₁ : G), (uPart c h12 y : G)⁆ := by
          rw [commutatorElement_def]
        rw [hEq]
        exact hS0K hcS0
      have hkill1 : l ⟨((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹) * (uPart c h12 y : G)⁻¹,
          c.U.mul_mem hconj (c.U.inv_mem (uPart c h12 y).2)⟩ = 1 :=
        hl ⟨((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹) * (uPart c h12 y : G)⁻¹,
          c.U.mul_mem hconj (c.U.inv_mem (uPart c h12 y).2)⟩ hmemK
      have hpr : (⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩ *
            ⟨(uPart c h12 y : G)⁻¹, c.U.inv_mem (uPart c h12 y).2⟩ : ↥c.U) =
          ⟨((r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹) * (uPart c h12 y : G)⁻¹,
            c.U.mul_mem hconj (c.U.inv_mem (uPart c h12 y).2)⟩ := rfl
      have hmul : l ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩ *
            l ⟨(uPart c h12 y : G)⁻¹, c.U.inv_mem (uPart c h12 y).2⟩ = 1 := by
        rw [← map_mul]
        rw [hpr]
        exact hkill1
      have hinv : l ⟨(uPart c h12 y : G)⁻¹, c.U.inv_mem (uPart c h12 y).2⟩ =
          (l (uPart c h12 y))⁻¹ := by
        change l (uPart c h12 y)⁻¹ = (l (uPart c h12 y))⁻¹
        exact map_inv l (uPart c h12 y)
      have hmul' : (l ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩ *
            (l (uPart c h12 y))⁻¹) * l (uPart c h12 y) =
          1 * l (uPart c h12 y) := by
        simpa [hinv] using congrArg (fun z : ℂˣ => z * l (uPart c h12 y)) hmul
      calc
        l ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩
            = (l ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩ *
                (l (uPart c h12 y))⁻¹) * l (uPart c h12 y) := by
                group
        _ = 1 * l (uPart c h12 y) := hmul'
        _ = l (uPart c h12 y) := by simp
    calc
      l (uPart c h12 (x * y))
          = l (uPart c h12 x * ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩) := by
              rw [hmain]
      _ = l (uPart c h12 x) * l ⟨(r₁ : G) * (uPart c h12 y : G) * ((r₁ : G))⁻¹, hconj⟩ := by
              rw [map_mul]
      _ = l (uPart c h12 x) * l (uPart c h12 y) := by rw [hlconj]

/-- Membership in `B1 = C_U(t1)` from membership in `B`. -/
private lemma mem_B1_of_mem_B (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) : b ∈ c.B1 := by
  unfold Hyp11.B at hbB
  exact (inf_le_left : c.B1 ⊓ c.B2 ≤ c.B1) hbB

/-- Membership in `B2 = C_U(t2)` from membership in `B`. -/
private lemma mem_B2_of_mem_B (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) : b ∈ c.B2 := by
  unfold Hyp11.B at hbB
  exact (inf_le_right : c.B1 ⊓ c.B2 ≤ c.B2) hbB

/-- `B ≤ U`. -/
private lemma mem_U_of_mem_B (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) : b ∈ c.U := by
  have hbB1 := mem_B1_of_mem_B c hbB
  unfold Hyp11.B1 centralizerIn at hbB1
  exact (inf_le_left : c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) ≤ c.U) hbB1

/-- Membership in the fixed-point subgroup is pointwise fixedness. -/
private lemma mem_fixedPointSubgroup_iff (A K : Subgroup G) [Subgroup.Normalizes A K]
    {x : ↥K} : x ∈ fixedPointSubgroup (↥A) (↥K) ↔ ∀ a : ↥A, a • x = x := by
  rfl

/-- Every element of `B = C_U(t1) ∩ C_U(t2)` is fixed by the conjugation
action of the whole 2-subgroup `S` on `U` (`S = ⟨t1, t2⟩`, since `t1`, `t2`
are the two reflections of the dihedral group `S`). -/
private lemma b_mem_fixedPointSubgroup (c : Hyp11 G) (_h12 : Hyp12 c)
    [Subgroup.Normalizes (c.S : Subgroup G) c.U] {b : G} (hbB : b ∈ c.B) :
    (⟨b, mem_U_of_mem_B c hbB⟩ : ↥c.U) ∈
      fixedPointSubgroup (↥(c.S : Subgroup G)) (↥c.U) := by
  classical
  have hbU : b ∈ c.U := mem_U_of_mem_B c hbB
  exact (mem_fixedPointSubgroup_iff (c.S : Subgroup G) c.U).2 (by
      have hbt1 : Commute c.t1 b := by
        have hbB1 := mem_B1_of_mem_B c hbB
        have hbcent : b ∈ Subgroup.centralizer ({c.t1} : Set G) := by
          unfold Hyp11.B1 centralizerIn at hbB1
          exact hbB1.2
        have hcomm : c.t1 * b = b * c.t1 :=
          (Subgroup.mem_centralizer_iff).1 hbcent c.t1 (by simp)
        exact hcomm
      have hbt2 : Commute c.t2 b := by
        have hbB2 := mem_B2_of_mem_B c hbB
        have hbcent : b ∈ Subgroup.centralizer ({c.t2} : Set G) := by
          unfold Hyp11.B2 centralizerIn at hbB2
          exact hbB2.2
        have hcomm : c.t2 * b = b * c.t2 :=
          (Subgroup.mem_centralizer_iff).1 hbcent c.t2 (by simp)
        exact hcomm
      have hbt1t2 : Commute (c.t1 * c.t2) b :=
        (Commute.mul_right hbt1.symm hbt2.symm).symm
      intro a
      apply Subtype.ext
      change (a : G) * b * (a : G)⁻¹ = b
      have hcomm_a : Commute (a : G) b := by
        by_cases haS0 : (a : G) ∈ (c.S0 : Subgroup G)
        · rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using haS0)) with
            ⟨k, hk⟩
          have hk' : Commute ((c.t1 * c.t2) ^ k) b := hbt1t2.zpow_left k
          simpa [hk.symm] using hk'
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
          exact hb_a.symm
      have hcomm_eq : (a : G) * b = b * (a : G) := hcomm_a.eq
      calc
        (a : G) * b * (a : G)⁻¹ = (b * (a : G)) * (a : G)⁻¹ := by rw [hcomm_eq]
        _ = b := by group)

/-- If `b ∈ B = C_U(S)` lies outside `U' = ⁅U, U⁆`, then it also lies outside
`U'·[S,U]`: in the abelian quotient `U/U'` the fixed points of the 2-group
`S` meet the action-commutator subgroup trivially (coprime action). -/
private lemma b_not_mem_comm_of_not_mem_Uprime (c : Hyp11 G) (h12 : Hyp12 c) {b : G}
    (hbB : b ∈ c.B) (hbU' : b ∉ ⁅c.U, c.U⁆) :
    b ∉ (⁅c.U, c.U⁆ ⊔ ⁅(c.S : Subgroup G), c.U⁆) := by
  classical
  let U' : Subgroup G := ⁅c.U, c.U⁆
  let C : Subgroup G := ⁅(c.S : Subgroup G), c.U⁆
  let N : Subgroup G := U' ⊔ C
  have hbU : b ∈ c.U := mem_U_of_mem_B c hbB
  have hSnormU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    S_le_normalizer_U c
  have : Subgroup.Normalizes (c.S : Subgroup G) c.U := ⟨hSnormU⟩
  let A : Type u := ↥(c.S : Subgroup G)
  -- `[S,U] ≤ U`
  have hCleU : C ≤ c.U := by
    dsimp [C]
    rw [← Subgroup.commutator_comm c.U (c.S : Subgroup G)]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hSnormU)
  have hNleU : N ≤ c.U := sup_le (Subgroup.commutator_le_self c.U) hCleU
  -- `U` normalizes `U'` and `C`, hence `N`
  have hUleNormU' : c.U ≤ Subgroup.normalizer (U' : Set G) :=
    Subgroup.normalizer_commutator_ge_left c.U c.U
  have hUleNormC : c.U ≤ Subgroup.normalizer (C : Set G) := by
    dsimp [C]
    rw [← Subgroup.commutator_comm c.U (c.S : Subgroup G)]
    exact Subgroup.normalizer_commutator_ge_left c.U (c.S : Subgroup G)
  have hUleNormN : c.U ≤ Subgroup.normalizer (N : Set G) := by
    exact (le_inf hUleNormU' hUleNormC).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup U' C)
  -- invariance of `U'` and `C` under the action of `S` on `U`
  have : IsInvariant A (↥c.U) (⊤ : Subgroup ↥c.U) := ⟨by intro a x; simp⟩
  have hU'subInv : IsInvariant A (↥c.U) (U'.subgroupOf c.U) := by
    have hc : IsInvariant A (↥c.U)
        (⁅(⊤ : Subgroup ↥c.U), (⊤ : Subgroup ↥c.U)⁆) :=
      isInvariant_commutator (G := ↥c.U) (H := ⊤) (K := ⊤)
    have hEq : ⁅(⊤ : Subgroup ↥c.U), (⊤ : Subgroup ↥c.U)⁆ = U'.subgroupOf c.U := by
      apply (Subgroup.map_subtype_inj (H := c.U)).mp
      calc
        (⁅(⊤ : Subgroup ↥c.U), (⊤ : Subgroup ↥c.U)⁆).map c.U.subtype = ⁅c.U, c.U⁆ := by
              simpa [commutator_def] using Subgroup.map_subtype_commutator c.U
        _ = (U'.subgroupOf c.U).map c.U.subtype := by
              exact (Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self c.U)).symm
    simpa [hEq.symm] using hc
  have hCcomm_sub : commutatorAction (A := A) (G := ↥c.U) = C.subgroupOf c.U := by
    apply (Subgroup.map_subtype_inj (H := c.U)).mp
    calc
      (commutatorAction (A := A) (G := ↥c.U)).map c.U.subtype =
          ⁅c.U, (c.S : Subgroup G)⁆ :=
            commutatorAction_subgroup_conj_map_eq_commutator c.U (c.S : Subgroup G) hSnormU
      _ = ⁅(c.S : Subgroup G), c.U⁆ := Subgroup.commutator_comm c.U (c.S : Subgroup G)
      _ = (C.subgroupOf c.U).map c.U.subtype := by
            exact (Subgroup.map_subgroupOf_eq_of_le hCleU).symm
  have hCsubInv : IsInvariant A (↥c.U) (C.subgroupOf c.U) := by
    have hc : IsInvariant A (↥c.U) (commutatorAction (A := A) (G := ↥c.U)) :=
      commutatorAction_isInvariant (G := ↥c.U) (A := A)
    simpa [hCcomm_sub.symm] using hc
  have : IsInvariant A (↥c.U) (U'.subgroupOf c.U) := hU'subInv
  have : IsInvariant A (↥c.U) (C.subgroupOf c.U) := hCsubInv
  -- the quotient `Q = U / U'` is abelian, solvable, and the action is coprime
  let U'sub : Subgroup ↥c.U := U'.subgroupOf c.U
  have : U'sub.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.commutator_le_self c.U)).mpr
      hUleNormU'
  let : MulAction.QuotientAction A U'sub := quotientAction_of_isInvariant U'sub hU'subInv
  let : MulDistribMulAction A (↥c.U ⧸ U'sub) :=
    quotientMulDistribMulAction (H := U'sub) hU'subInv
  have hQcomm : IsMulCommutative (↥c.U ⧸ U'sub) := by
    apply (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := ↥c.U) (N := U'sub)).2
    have hEq : commutator (↥c.U) = U'sub := by
      apply (Subgroup.map_subtype_inj (H := c.U)).mp
      calc
        (commutator (↥c.U)).map c.U.subtype = ⁅c.U, c.U⁆ :=
              Subgroup.map_subtype_commutator c.U
        _ = U'sub.map c.U.subtype := by
              exact (Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self c.U)).symm
    rw [hEq]
  have hsolvQ : IsSolvable (↥c.U ⧸ U'sub) := by
    let : IsMulCommutative (↥c.U ⧸ U'sub) := hQcomm
    let : CommGroup (↥c.U ⧸ U'sub) := IsMulCommutative.instCommGroup
    exact isSolvable_of_comm (fun a b => mul_comm a b)
  have hcop2U : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hcopSU : Nat.Coprime (Nat.card A) (Nat.card ↥c.U) := by
    rcases (IsPGroup.exists_card_eq (p := 2) (G := A) c.S.isPGroup') with ⟨n, hn⟩
    rw [hn]
    exact (Nat.Coprime.pow_left n hcop2U)
  have hcopQ : Nat.Coprime (Nat.card A) (Nat.card (↥c.U ⧸ U'sub)) := by
    have hdiv : Nat.card (↥c.U ⧸ U'sub) ∣ Nat.card ↥c.U :=
      Subgroup.card_quotient_dvd_card U'sub
    exact Nat.Coprime.of_dvd_right hdiv hcopSU
  have hcompl : IsCompl (fixedPointSubgroup A (↥c.U ⧸ U'sub))
      (commutatorAction (A := A) (G := ↥c.U ⧸ U'sub)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := ↥c.U ⧸ U'sub) (A := A) hsolvQ hcopQ hQcomm
  have hinf : fixedPointSubgroup A (↥c.U ⧸ U'sub) ⊓
      commutatorAction (A := A) (G := ↥c.U ⧸ U'sub) = ⊥ :=
    hcompl.disjoint.eq_bot
  -- the image of `b` in `Q` is fixed by `S`
  have hbfix : (⟨b, hbU⟩ : ↥c.U) ∈ fixedPointSubgroup A (↥c.U) :=
    b_mem_fixedPointSubgroup c h12 hbB
  let qb : ↥c.U ⧸ U'sub := QuotientGroup.mk' U'sub ⟨b, hbU⟩
  have hqbfix : qb ∈ fixedPointSubgroup A (↥c.U ⧸ U'sub) := by
    intro a
    have hfix' : a • (⟨b, hbU⟩ : ↥c.U) = (⟨b, hbU⟩ : ↥c.U) := by
      exact (mem_fixedPointSubgroup_iff (c.S : Subgroup G) c.U).mp hbfix a
    have hsmul : a • (QuotientGroup.mk' U'sub ⟨b, hbU⟩ : ↥c.U ⧸ U'sub) =
        QuotientGroup.mk' U'sub (a • ⟨b, hbU⟩ : ↥c.U) := by
      simpa using (MulAction.Quotient.smul_mk (H := U'sub) a ⟨b, hbU⟩)
    calc
      a • qb = QuotientGroup.mk' U'sub (a • ⟨b, hbU⟩ : ↥c.U) := hsmul
      _ = QuotientGroup.mk' U'sub ⟨b, hbU⟩ := by rw [hfix']
  -- action commutators of `U` map into action commutators of `Q`
  have hmap_le : (commutatorAction (A := A) (G := ↥c.U)).map (QuotientGroup.mk' U'sub) ≤
      commutatorAction (A := A) (G := ↥c.U ⧸ U'sub) := by
    rw [commutatorAction_eq_closure (G := ↥c.U)]
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro q hq
    rcases hq with ⟨x, hx, rfl⟩
    rcases hx with ⟨a0, u, hxeq⟩
    refine ⟨a0, QuotientGroup.mk' U'sub u, ⟨by simp, ?_⟩⟩
    have hsmul : a0 • (QuotientGroup.mk' U'sub u) = QuotientGroup.mk' U'sub (a0 • u) := by
      simpa using (MulAction.Quotient.smul_mk (H := U'sub) a0 u)
    calc
      QuotientGroup.mk' U'sub x = QuotientGroup.mk' U'sub (u⁻¹ * (a0 • u)) := by rw [hxeq]
      _ = (QuotientGroup.mk' U'sub u)⁻¹ * QuotientGroup.mk' U'sub (a0 • u) := by
            rw [map_mul, map_inv]
      _ = (QuotientGroup.mk' U'sub u)⁻¹ * (a0 • QuotientGroup.mk' U'sub u) := by rw [hsmul]
  -- `U'` maps to `⊥` and `C` maps into the action commutators
  have hU'sub_map_bot : U'sub.map (QuotientGroup.mk' U'sub) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hC_map_le : (C.subgroupOf c.U).map (QuotientGroup.mk' U'sub) ≤
      commutatorAction (A := A) (G := ↥c.U ⧸ U'sub) := by
    rw [← hCcomm_sub]
    exact hmap_le
  have hN_map_le : (N.subgroupOf c.U).map (QuotientGroup.mk' U'sub) ≤
      commutatorAction (A := A) (G := ↥c.U ⧸ U'sub) := by
    have hsub_sup : U'.subgroupOf c.U ⊔ C.subgroupOf c.U = N.subgroupOf c.U := by
      dsimp [N]
      exact (Subgroup.subgroupOf_sup (Subgroup.commutator_le_self c.U) hCleU).symm
    calc
      (N.subgroupOf c.U).map (QuotientGroup.mk' U'sub)
          = (U'.subgroupOf c.U ⊔ C.subgroupOf c.U).map (QuotientGroup.mk' U'sub) := by
              rw [hsub_sup.symm]
      _ = (U'.subgroupOf c.U).map (QuotientGroup.mk' U'sub) ⊔
          (C.subgroupOf c.U).map (QuotientGroup.mk' U'sub) := by rw [Subgroup.map_sup]
      _ ≤ commutatorAction (A := A) (G := ↥c.U ⧸ U'sub) := by
            exact sup_le (by rw [hU'sub_map_bot]; simp) hC_map_le
  -- assume `b ∈ N`; then its image lies in both fixed points and commutators
  intro hbN
  have hqbcomm : qb ∈ commutatorAction (A := A) (G := ↥c.U ⧸ U'sub) := by
    have hbNU : ⟨b, hbU⟩ ∈ N.subgroupOf c.U := Subgroup.mem_subgroupOf.mpr hbN
    have hqbmap : qb ∈ (N.subgroupOf c.U).map (QuotientGroup.mk' U'sub) :=
      Subgroup.mem_map.mpr ⟨(⟨b, hbU⟩ : ↥c.U), hbNU, rfl⟩
    exact hN_map_le hqbmap
  have hqbot : qb ∈ (⊥ : Subgroup (↥c.U ⧸ U'sub)) := by
    have hxinf : qb ∈ fixedPointSubgroup A (↥c.U ⧸ U'sub) ⊓
        commutatorAction (A := A) (G := ↥c.U ⧸ U'sub) :=
      ⟨hqbfix, hqbcomm⟩
    simpa [hinf] using hxinf
  have hqb1 : qb = 1 := Subgroup.mem_bot.mp hqbot
  have hbU'_mem : b ∈ U' := by
    have hmem : (⟨b, hbU⟩ : ↥c.U) ∈ U'sub := by
      apply (QuotientGroup.eq_one_iff (N := U'sub) (⟨b, hbU⟩ : ↥c.U)).mp
      simpa [qb] using hqb1
    exact Subgroup.mem_subgroupOf.mp hmem
  exact hbU' (by simpa [U'] using hbU'_mem)

/-- If `B ⊄ U'`, then `κ1` can be chosen distinct from `λ1 = 1_{H0}`. -/
theorem exists_kappaOne_ne_one (c : Hyp11 G) (h12 : Hyp12 c)
    (hB : ¬ c.B ≤ ⁅c.U, c.U⁆) :
    ∃ κ1 : ClassFunction (↥c.H0), IsLinearCharacter κ1 ∧ κ1 ≠ 1 ∧
      (∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1) ∧
      (∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1) := by
  classical
  rcases (SetLike.not_le_iff_exists.mp hB) with ⟨b, hbB, hbU'⟩
  let U' : Subgroup G := ⁅c.U, c.U⁆
  let C : Subgroup G := ⁅(c.S : Subgroup G), c.U⁆
  let N : Subgroup G := U' ⊔ C
  have hbU : b ∈ c.U := mem_U_of_mem_B c hbB
  have hbN : b ∉ N := by
    exact b_not_mem_comm_of_not_mem_Uprime c h12 hbB hbU'
  have hSnormU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    S_le_normalizer_U c
  have hCleU : C ≤ c.U := by
    dsimp [C]
    rw [← Subgroup.commutator_comm c.U (c.S : Subgroup G)]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hSnormU)
  have hNleU : N ≤ c.U := sup_le (Subgroup.commutator_le_self c.U) hCleU
  have hUleNormU' : c.U ≤ Subgroup.normalizer (U' : Set G) :=
    Subgroup.normalizer_commutator_ge_left c.U c.U
  have hUleNormC : c.U ≤ Subgroup.normalizer (C : Set G) := by
    dsimp [C]
    rw [← Subgroup.commutator_comm c.U (c.S : Subgroup G)]
    exact Subgroup.normalizer_commutator_ge_left c.U (c.S : Subgroup G)
  have hUleNormN : c.U ≤ Subgroup.normalizer (N : Set G) := by
    exact (le_inf hUleNormU' hUleNormC).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup U' C)
  let : (N.subgroupOf c.U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleU).mpr hUleNormN
  rcases (LambdaHom_separates c.U N (hK := by infer_instance)
      (hcomm := commutator_le_quotient_comm c.U N (show ⁅c.U, c.U⁆ ≤ N from le_sup_left))
      ⟨b, hbU⟩ hbN) with ⟨l, hl⟩
  have hS0K : ⁅(c.S0 : Subgroup G), c.U⁆ ≤ N := by
    exact (Subgroup.commutator_mono c.S0_le_S le_rfl).trans (show C ≤ N from le_sup_right)
  let φ : ↥c.H0 →* ℂˣ := kappaOneHom c h12 N hS0K l.1 l.2
  let κ1 : ClassFunction (↥c.H0) :=
    LambdaChar φ
  refine ⟨κ1, ?_, ?_, ?_, ?_⟩
  · exact isLinearCharacter_of_hom φ
  · intro hk1
    have hbH0 : b ∈ c.H0 := SetLike.le_def.mp le_sup_left hbU
    have hval1 : φ ⟨b, hbH0⟩ ≠ 1 := by
      intro hφ1
      have hup : uPart c h12 ⟨b, hbH0⟩ = ⟨b, hbU⟩ :=
        uPart_eq_of_mem_U c h12 hbU
      have hl1 : (l.1 ⟨b, hbU⟩ : ℂ) ≠ 1 := by
        intro h
        exact hl (Units.ext h)
      have hφ2 : (l.1 ⟨b, hbU⟩ : ℂ) = 1 := by
        have hφ1' : (φ ⟨b, hbH0⟩ : ℂ) = 1 :=
          congrArg (fun z : ℂˣ => (z : ℂ)) hφ1
        change (l.1 (uPart c h12 ⟨b, hbH0⟩) : ℂ) = 1 at hφ1'
        rw [hup] at hφ1'
        exact hφ1'
      exact hl1 hφ2
    apply hval1
    have hφ1 : φ = 1 := by
      apply MonoidHom.ext
      intro x
      apply Units.ext
      have hx := congrFun hk1 x
      change ((φ x : ℂˣ) : ℂ) = 1 at hx
      exact hx
    simpa [hφ1]
  · intro x hxS0
    change (l.1 (uPart c h12 x) : ℂ) = 1
    have hup : uPart c h12 x = 1 := uPart_eq_one_of_mem_S0 c h12 hxS0
    simp [hup]
  · intro x hxcomm
    change (l.1 (uPart c h12 x) : ℂ) = 1
    have hxU : (x : G) ∈ c.U := hCleU hxcomm
    have hup : uPart c h12 x = ⟨(x : G), hxU⟩ :=
      uPart_eq_of_mem_U c h12 hxU
    have hl1 : l.1 ⟨(x : G), hxU⟩ = 1 :=
      l.2 ⟨(x : G), hxU⟩ (show (x : G) ∈ N from (le_sup_right : C ≤ U' ⊔ C) hxcomm)
    simp [hup, hl1]

end Section2

end CFSG.BenderGlauberman
