module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBWeightAux1
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.StandardType.HdRo7C

@[expose] def hdRo7CKCoordAux_signedPermAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3)
    (f : Fin n → ZMod 3) : Fin n → ZMod 3 :=
  fun l => c (σ.symm l) * f (σ.symm l)

private def hdRo7CKCoordAux_supp {n : ℕ} (v : Fin n → ZMod 3) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i ≠ 0)

private def hdRo7CKCoordAux_signOf {n : ℕ} (T : Finset (Fin n)) : Fin n → ZMod 3 :=
  fun l => if l ∈ T then -1 else 1

private lemma hdRo7CKCoordAux_signOf_apply {n : ℕ} (T : Finset (Fin n)) (l : Fin n) :
    hdRo7CKCoordAux_signOf T l = 1 ∨ hdRo7CKCoordAux_signOf T l = -1 := by
  unfold hdRo7CKCoordAux_signOf
  by_cases h : l ∈ T <;> simp [h]

private lemma hdRo7CKCoordAux_supp_single_one {n : ℕ} (k : Fin n) : hdRo7CKCoordAux_supp (Pi.single k (1 : ZMod 3)) = {k} := by
  unfold hdRo7CKCoordAux_supp
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hne
    exact h (Pi.single_eq_of_ne hne 1)
  · intro h
    subst h
    simp [Pi.single_eq_same]

private lemma hdRo7CKCoordAux_eq_single_of_supp_eq_singleton {n : ℕ} {a : Fin n → ZMod 3} {i : Fin n}
    (h : hdRo7CKCoordAux_supp a = {i}) : a = Pi.single i (a i) := by
  ext l
  by_cases hl : l = i
  · subst hl; simp [Pi.single_eq_same]
  · have hnot : l ∉ hdRo7CKCoordAux_supp a := by rw [h]; simp [Finset.mem_singleton, hl]
    have hzero : a l = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    rw [hzero, Pi.single_eq_of_ne hl]

private noncomputable def hdRo7CKCoordAux_chooseIdx {n : ℕ} (β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (x : {x : Fin n → ZMod 3 // (hdRo7CKCoordAux_supp (β.symm x)).card = 1}) : Fin n :=
  Classical.choose (Finset.card_eq_one.mp x.2)

private lemma hdRo7CKCoordAux_chooseIdx_spec {n : ℕ} (β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (x : {x : Fin n → ZMod 3 // (hdRo7CKCoordAux_supp (β.symm x)).card = 1}) :
    hdRo7CKCoordAux_supp (β.symm x.1) = {hdRo7CKCoordAux_chooseIdx β x} :=
  Classical.choose_spec (Finset.card_eq_one.mp x.2)

private noncomputable def hdRo7CKCoordAux_toPair {n : ℕ} (β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (x : {x : Fin n → ZMod 3 // (hdRo7CKCoordAux_supp (β.symm x)).card = 1}) : Fin n × Fin 2 :=
  (hdRo7CKCoordAux_chooseIdx β x, if (β.symm x.1) (hdRo7CKCoordAux_chooseIdx β x) = 1 then 0 else 1)

private lemma hdRo7CKCoordAux_toPair_injective {n : ℕ} (β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    Function.Injective (hdRo7CKCoordAux_toPair β) := by
  intro x y hxy
  have hix : hdRo7CKCoordAux_chooseIdx β x = hdRo7CKCoordAux_chooseIdx β y := congrArg Prod.fst hxy
  have hs : (if (β.symm x.1) (hdRo7CKCoordAux_chooseIdx β x) = 1 then (0 : Fin 2) else 1) =
            (if (β.symm y.1) (hdRo7CKCoordAux_chooseIdx β y) = 1 then 0 else 1) := congrArg Prod.snd hxy
  have hxspec : hdRo7CKCoordAux_supp (β.symm x.1) = {hdRo7CKCoordAux_chooseIdx β x} := hdRo7CKCoordAux_chooseIdx_spec β x
  have hyspec : hdRo7CKCoordAux_supp (β.symm y.1) = {hdRo7CKCoordAux_chooseIdx β y} := hdRo7CKCoordAux_chooseIdx_spec β y
  have hxne : (β.symm x.1) (hdRo7CKCoordAux_chooseIdx β x) ≠ 0 := by
    have hmem : hdRo7CKCoordAux_chooseIdx β x ∈ hdRo7CKCoordAux_supp (β.symm x.1) := by rw [hxspec]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hyne : (β.symm y.1) (hdRo7CKCoordAux_chooseIdx β y) ≠ 0 := by
    have hmem : hdRo7CKCoordAux_chooseIdx β y ∈ hdRo7CKCoordAux_supp (β.symm y.1) := by rw [hyspec]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hval : (β.symm x.1) (hdRo7CKCoordAux_chooseIdx β x) = (β.symm y.1) (hdRo7CKCoordAux_chooseIdx β y) :=
    hdRo7CKCoordAux_ite_one_inj _ _ hxne hyne hs
  apply Subtype.ext
  have h1 : β.symm x.1 = Pi.single (hdRo7CKCoordAux_chooseIdx β x) ((β.symm x.1) (hdRo7CKCoordAux_chooseIdx β x)) :=
    hdRo7CKCoordAux_eq_single_of_supp_eq_singleton hxspec
  have h2 : β.symm y.1 = Pi.single (hdRo7CKCoordAux_chooseIdx β y) ((β.symm y.1) (hdRo7CKCoordAux_chooseIdx β y)) :=
    hdRo7CKCoordAux_eq_single_of_supp_eq_singleton hyspec
  apply β.symm.injective
  rw [h1, h2, hval, hix]

private lemma hdRo7CKCoordAux_W_card_le {n : ℕ} (β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    (Finset.univ.filter (fun x : Fin n → ZMod 3 => (hdRo7CKCoordAux_supp (β.symm x)).card = 1)).card ≤ 2 * n := by
  have hcard : (Finset.univ.filter (fun x : Fin n → ZMod 3 => (hdRo7CKCoordAux_supp (β.symm x)).card = 1)).card
      = Fintype.card {x : Fin n → ZMod 3 // (hdRo7CKCoordAux_supp (β.symm x)).card = 1} := by
    rw [Fintype.card_subtype]
  rw [hcard]
  calc Fintype.card {x : Fin n → ZMod 3 // (hdRo7CKCoordAux_supp (β.symm x)).card = 1}
      ≤ Fintype.card (Fin n × Fin 2) :=
        Fintype.card_le_of_injective (hdRo7CKCoordAux_toPair β) (hdRo7CKCoordAux_toPair_injective β)
    _ = 2 * n := by simp [Fintype.card_prod, Fintype.card_fin, mul_comm]

private lemma hdRo7CKCoordAux_signOf_injective {n : ℕ} : Function.Injective (hdRo7CKCoordAux_signOf : Finset (Fin n) → Fin n → ZMod 3) := by
  intro T T' h
  ext m
  have hm := congrFun h m
  simp only [hdRo7CKCoordAux_signOf] at hm
  by_cases hT : m ∈ T
  · by_cases hT' : m ∈ T'
    · simp [hT, hT']
    · exact absurd (by simpa [hT, hT'] using hm) (by decide)
  · by_cases hT' : m ∈ T'
    · exact absurd (by simpa [hT, hT'] using hm) (by decide)
    · simp [hT, hT']

private lemma hdRo7CKCoordAux_family_false {n : ℕ} (hn : 5 ≤ n)
    (β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (hinv : ∀ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3),
      (∀ i, c i = 1 ∨ c i = -1) → ∀ u : Fin n → ZMod 3,
        (hdRo7CKCoordAux_supp (β.symm (hdRo7CKCoordAux_signedPermAct σ c u))).card = (hdRo7CKCoordAux_supp (β.symm u)).card)
    (v : Fin n → ZMod 3) (hv : (hdRo7CKCoordAux_supp (β.symm v)).card = 1) :
    ¬ (2 ≤ (hdRo7CKCoordAux_supp v).card) := by
  intro h2
  let W : Finset (Fin n → ZMod 3) :=
    Finset.univ.filter (fun x => (hdRo7CKCoordAux_supp (β.symm x)).card = 1)
  have hW : W.card ≤ 2 * n := by
    have := hdRo7CKCoordAux_W_card_le (n := n) β
    simpa only [W] using this
  by_cases ht : (hdRo7CKCoordAux_supp v).card ≤ n - 1
  ·
    have hSne : (hdRo7CKCoordAux_supp v).Nonempty := Finset.card_pos.mp (by omega)
    let i := Classical.choose hSne
    have hi : i ∈ hdRo7CKCoordAux_supp v := Classical.choose_spec hSne
    have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
    let D : Finset (Fin n × Finset (Fin n)) := (Finset.univ \ hdRo7CKCoordAux_supp v) ×ˢ (hdRo7CKCoordAux_supp v).powerset
    let f : Fin n × Finset (Fin n) → (Fin n → ZMod 3) :=
      fun p => hdRo7CKCoordAux_signedPermAct (Equiv.swap i p.1) (hdRo7CKCoordAux_signOf p.2) v
    have hDcard : D.card = (n - (hdRo7CKCoordAux_supp v).card) * 2 ^ (hdRo7CKCoordAux_supp v).card := by
      simp only [D, Finset.card_product, Finset.card_univ_sdiff, Finset.card_powerset,
        Fintype.card_fin]
    have hmaps : Set.MapsTo f (D : Set _) (W : Set _) := by
      intro p hp
      simp only [W, f, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hinv (Equiv.swap i p.1) (hdRo7CKCoordAux_signOf p.2) (hdRo7CKCoordAux_signOf_apply p.2) v]
      exact hv
    have hinj : (D : Set _).InjOn f := by
      rintro ⟨j, T⟩ hp ⟨j', T'⟩ hq heq
      change (j, T) ∈ (Finset.univ \ hdRo7CKCoordAux_supp v) ×ˢ (hdRo7CKCoordAux_supp v).powerset at hp
      change (j', T') ∈ (Finset.univ \ hdRo7CKCoordAux_supp v) ×ˢ (hdRo7CKCoordAux_supp v).powerset at hq
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
      have hjS : j ∉ hdRo7CKCoordAux_supp v := (Finset.mem_sdiff.mp hp1).2
      have hTS : T ⊆ hdRo7CKCoordAux_supp v := Finset.mem_powerset.mp hp2
      have hjS' : j' ∉ hdRo7CKCoordAux_supp v := (Finset.mem_sdiff.mp hq1).2
      have hTS' : T' ⊆ hdRo7CKCoordAux_supp v := Finset.mem_powerset.mp hq2
      have hjj : j = j' := by
        by_contra hne
        have hnei : j ≠ i := fun h => hjS (h ▸ hi)
        have hpj : f (j, T) j ≠ 0 := by
          simp only [f, hdRo7CKCoordAux_signedPermAct]
          rw [hdRo7CKCoordAux_swap_symm_apply_left i j]
          rcases hdRo7CKCoordAux_signOf_apply T i with h1 | h1 <;> rw [h1] <;> simp [hvi]
        have hqj : f (j', T') j = 0 := by
          simp only [f, hdRo7CKCoordAux_signedPermAct]
          rw [hdRo7CKCoordAux_swap_symm_apply_of_ne i j' j hnei hne]
          have hvj : v j = 0 := by
            by_contra h
            exact hjS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          rw [hvj, mul_zero]
        exact hpj (by rw [heq, hqj])
      subst hjj
      have hTT : T = T' := by
        have hsign : ∀ m, m ∈ T ↔ m ∈ T' := by
          intro m
          by_cases hmS : m ∈ hdRo7CKCoordAux_supp v
          · have hm := congrFun heq (Equiv.swap i j m)
            simp only [f, hdRo7CKCoordAux_signedPermAct] at hm
            rw [show (Equiv.swap i j).symm (Equiv.swap i j m) = m from
              Equiv.symm_apply_apply _ m] at hm
            have hvm : v m ≠ 0 := (Finset.mem_filter.mp hmS).2
            have hcancel : hdRo7CKCoordAux_signOf T m = hdRo7CKCoordAux_signOf T' m := mul_right_cancel₀ hvm hm
            rw [hdRo7CKCoordAux_signOf, hdRo7CKCoordAux_signOf] at hcancel
            by_cases hTm : m ∈ T
            · by_cases hTm' : m ∈ T'
              · simp [hTm, hTm']
              · exact absurd (by simpa [hTm, hTm'] using hcancel) (by decide)
            · by_cases hTm' : m ∈ T'
              · exact absurd (by simpa [hTm, hTm'] using hcancel) (by decide)
              · simp [hTm, hTm']
          · have hmT : m ∉ T := fun h => hmS (hTS h)
            have hmT' : m ∉ T' := fun h => hmS (hTS' h)
            simp [hmT, hmT']
        ext m
        exact hsign m
      subst hTT
      rfl
    have hle : D.card ≤ 2 * n := by
      calc D.card ≤ W.card := Finset.card_le_card_of_injOn f hmaps hinj
        _ ≤ 2 * n := hW
    have hkey := hdRo7CKCoordAux_key1 hn h2 ht
    rw [hDcard] at hle
    exact absurd hkey (not_lt.mpr hle)
  ·
    have htn : (hdRo7CKCoordAux_supp v).card = n := by
      have hle := Finset.card_le_univ (hdRo7CKCoordAux_supp v)
      simp only [Fintype.card_fin] at hle
      omega
    have hvm_all : ∀ m, v m ≠ 0 := by
      intro m hm
      have hsub : hdRo7CKCoordAux_supp v ⊆ Finset.univ.erase m := by
        intro x hx
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        rintro rfl
        exact (Finset.mem_filter.mp hx).2 hm
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin] at hcard
      omega
    let D2 : Finset (Finset (Fin n)) := (hdRo7CKCoordAux_supp v).powerset
    let f2 : Finset (Fin n) → (Fin n → ZMod 3) := fun T => hdRo7CKCoordAux_signedPermAct (Equiv.refl (Fin n)) (hdRo7CKCoordAux_signOf T) v
    have hD2card : D2.card = 2 ^ n := by
      simp only [D2, Finset.card_powerset]
      rw [htn]
    have hmaps2 : Set.MapsTo f2 (D2 : Set _) (W : Set _) := by
      intro T hT
      simp only [W, f2, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hinv (Equiv.refl (Fin n)) (hdRo7CKCoordAux_signOf T) (hdRo7CKCoordAux_signOf_apply T) v]
      exact hv
    have hinj2 : (D2 : Set _).InjOn f2 := by
      intro T hT T' hT' heq
      have hsign : hdRo7CKCoordAux_signOf T = hdRo7CKCoordAux_signOf T' := by
        funext m
        have hm := congrFun heq m
        simp only [f2, hdRo7CKCoordAux_signedPermAct] at hm
        rw [show (Equiv.refl (Fin n)).symm m = m from rfl] at hm
        exact mul_right_cancel₀ (hvm_all m) hm
      exact hdRo7CKCoordAux_signOf_injective hsign
    have hle2 : 2 ^ n ≤ 2 * n := by
      rw [← hD2card]
      calc D2.card ≤ W.card := Finset.card_le_card_of_injOn f2 hmaps2 hinj2
        _ ≤ 2 * n := hW
    exact absurd (hdRo7CKCoordAux_key2 hn) (not_lt.mpr hle2)

private lemma hdRo7CKCoordAux_supp_nonempty {n : ℕ} {v : Fin n → ZMod 3} (hv : v ≠ 0) : (hdRo7CKCoordAux_supp v).Nonempty := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext fun i => h i)
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

theorem hdRo7CKCoordAux_weight_two {n : ℕ} (hn : 5 ≤ n)
    (β : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (hinv : ∀ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3), (∀ i, c i = 1 ∨ c i = -1) →
      ∀ u : Fin n → ZMod 3,
        (Finset.univ.filter (fun k => β.symm (hdRo7CKCoordAux_signedPermAct σ c u) k ≠ 0)).card =
          (Finset.univ.filter (fun k => β.symm u k ≠ 0)).card)
    (u : Fin n → ZMod 3) (hu : (Finset.univ.filter (fun k => β.symm u k ≠ 0)).card = 2) :
    (Finset.univ.filter (fun i => u i ≠ 0)).card = 2 := by

  have hk1 (k : Fin n) : (hdRo7CKCoordAux_supp (β (Pi.single k 1))).card = 1 := by
    have hsymm : (hdRo7CKCoordAux_supp (β.symm (β (Pi.single k 1)))).card = 1 := by
      rw [β.symm_apply_apply, hdRo7CKCoordAux_supp_single_one, Finset.card_singleton]
    have hnot := hdRo7CKCoordAux_family_false hn β hinv (β (Pi.single k 1)) hsymm
    have hne0 : β (Pi.single k 1) ≠ 0 := by
      intro h
      have h0 : Pi.single k (1 : ZMod 3) = 0 := β.map_eq_zero_iff.mp h
      have := congrFun h0 k
      simpa [Pi.single_eq_same] using this
    have hpos : 0 < (hdRo7CKCoordAux_supp (β (Pi.single k 1))).card :=
      Finset.card_pos.mpr (hdRo7CKCoordAux_supp_nonempty hne0)
    omega
  let π : Fin n → Fin n := fun k => Classical.choose (Finset.card_eq_one.mp (hk1 k))
  have hπspec (k : Fin n) : hdRo7CKCoordAux_supp (β (Pi.single k 1)) = {π k} :=
    Classical.choose_spec (Finset.card_eq_one.mp (hk1 k))
  have hβk (k : Fin n) :
      β (Pi.single k 1) = Pi.single (π k) ((β (Pi.single k 1)) (π k)) :=
    hdRo7CKCoordAux_eq_single_of_supp_eq_singleton (hπspec k)
  have hβk_ne (k : Fin n) : (β (Pi.single k 1)) (π k) ≠ 0 := by
    have hmem : π k ∈ hdRo7CKCoordAux_supp (β (Pi.single k 1)) := by rw [hπspec k]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hπinj : Function.Injective π := by
    intro k l hkl
    by_contra hne
    have hk := hβk k
    have hl := hβk l
    set ck := (β (Pi.single k 1)) (π k) with hck
    set cl := (β (Pi.single l 1)) (π l) with hcl
    have hck' : ck ≠ 0 := hβk_ne k
    have hcl' : cl ≠ 0 := hβk_ne l
    have hlk : π l = π k := hkl.symm
    have hcomb : cl • (Pi.single k (1 : ZMod 3)) - ck • (Pi.single l (1 : ZMod 3)) = 0 := by
      apply β.injective
      rw [map_sub, map_smul, map_smul, map_zero, hk, hl, hlk]
      ext m
      by_cases hm : m = π k
      · subst hm
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Pi.zero_apply]
        ring
      · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hm, smul_eq_mul, mul_zero,
          sub_zero, Pi.zero_apply]
    have hval := congrFun hcomb k
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hne, smul_eq_mul, mul_one, mul_zero, sub_zero, Pi.zero_apply] at hval
    exact hcl' hval
  let a : Fin n → ZMod 3 := β.symm u
  have ha : a = β.symm u := rfl
  have hu' : (hdRo7CKCoordAux_supp a).card = 2 := by rw [ha]; exact hu
  obtain ⟨k1, k2, hne, hsupp⟩ := Finset.card_eq_two.mp hu'
  have ha1 : a k1 ≠ 0 := by
    have : k1 ∈ hdRo7CKCoordAux_supp a := by rw [hsupp]; simp
    exact (Finset.mem_filter.mp this).2
  have ha2 : a k2 ≠ 0 := by
    have : k2 ∈ hdRo7CKCoordAux_supp a := by rw [hsupp]; simp
    exact (Finset.mem_filter.mp this).2
  have hπne : π k1 ≠ π k2 := fun h => hne (hπinj h)
  have hsum : a = Pi.single k1 (a k1) + Pi.single k2 (a k2) := by
    ext l
    by_cases hl1 : l = k1
    · subst hl1; simp [Pi.single_eq_same, Pi.single_eq_of_ne hne]
    · by_cases hl2 : l = k2
      · subst hl2; simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)]
      · have hz : a l = 0 := by
          by_contra h
          have : l ∈ hdRo7CKCoordAux_supp a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          rw [hsupp] at this
          simp [Finset.mem_insert, Finset.mem_singleton, hl1, hl2] at this
        simp [hz, Pi.single_eq_of_ne hl1, Pi.single_eq_of_ne hl2]
  have hu_eq (l : Fin n) : u l = a k1 * (β (Pi.single k1 1)) l
      + a k2 * (β (Pi.single k2 1)) l := by
    have hua : u = β a := by rw [ha]; exact (β.apply_symm_apply u).symm
    rw [hua]
    conv_lhs => rw [hsum, hdRo7CKCoordAux_single_eq_smul k1 (a k1), hdRo7CKCoordAux_single_eq_smul k2 (a k2), map_add, map_smul,
      map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hu_single (k : Fin n) : β (Pi.single k 1)
      = ((β (Pi.single k 1)) (π k)) • (Pi.single (π k) (1 : ZMod 3)) := by
    have h := hβk k
    rw [hdRo7CKCoordAux_single_eq_smul (π k) ((β (Pi.single k 1)) (π k))] at h
    exact h
  have hsuppu : hdRo7CKCoordAux_supp u = {π k1, π k2} := by
    ext l
    simp only [hdRo7CKCoordAux_supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [hu_eq l, hu_single k1, hu_single k2]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hl1 : l = π k1
    · subst hl1
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hπne]
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        simp only [mul_one, mul_zero, add_zero]
        exact mul_ne_zero ha1 (hβk_ne k1)
    · by_cases hl2 : l = π k2
      · subst hl2
        rw [Pi.single_eq_of_ne (Ne.symm hπne), Pi.single_eq_same]
        constructor
        · intro _
          exact Or.inr rfl
        · intro _
          simp only [mul_one, mul_zero, zero_add]
          exact mul_ne_zero ha2 (hβk_ne k2)
      · rw [Pi.single_eq_of_ne hl1, Pi.single_eq_of_ne hl2]
        simp [hl1, hl2]
  change (hdRo7CKCoordAux_supp u).card = 2
  rw [hsuppu]
  simp [hπne]

end CFSG.StandardType.HdRo7C

end
