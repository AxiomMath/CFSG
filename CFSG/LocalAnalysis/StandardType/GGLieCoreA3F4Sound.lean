module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeDefs
public import Certificates.Data.A3LatticeF4
public import Certificates.Certificate715501
public import CFSG.RankThree.PartOne.KF4.Strings

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open Matrix

private def toArr (γ : Fin Tag.F4.rank → ℤ) : Array Int := Array.ofFn γ

private def codes (c : Fin Tag.F4.rank → ZMod 3) : Array Nat :=
  Array.ofFn fun i => (c i).val

private theorem toArr_getElem!_nat (γ : Fin Tag.F4.rank → ℤ) (j : Nat)
    (hj : j < Tag.F4.rank) : (toArr γ)[j]! = γ ⟨j, hj⟩ := by
  show (Array.ofFn γ)[j]! = γ ⟨j, hj⟩
  rw [getElem!_pos (Array.ofFn γ) j (by simpa only [Array.size_ofFn] using hj),
    Array.getElem_ofFn]

private theorem toArr_getElem! (γ : Fin Tag.F4.rank → ℤ) (j : Fin Tag.F4.rank) :
    (toArr γ)[j.val]! = γ j := by
  rw [toArr_getElem!_nat γ j.val j.isLt]

private theorem toArr_injective : Function.Injective toArr := by
  intro γ δ h
  funext j
  have := congrArg (fun a : Array Int => a[j.val]!) h
  rwa [toArr_getElem! γ j, toArr_getElem! δ j] at this

private theorem codes_getElem!_nat (c : Fin Tag.F4.rank → ZMod 3) (j : Nat)
    (hj : j < Tag.F4.rank) : (codes c)[j]! = (c ⟨j, hj⟩).val := by
  show (Array.ofFn (fun i => (c i).val))[j]! = (c ⟨j, hj⟩).val
  rw [getElem!_pos (Array.ofFn (fun i => (c i).val)) j
      (by simpa only [Array.size_ofFn] using hj), Array.getElem_ofFn]

private theorem foldl_rank (f : ℕ → ℤ) :
    (List.range Certificates.A3LatticeF4.rank).foldl (fun s j => s + f j) 0 =
      f 0 + f 1 + f 2 + f 3 := by
  simp only [Certificates.A3LatticeF4.rank, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil, zero_add]

private theorem sum_univ_f4 (f : Fin Tag.F4.rank → ℤ) :
    (∑ l : Fin Tag.F4.rank, f l) = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

private theorem symm_getElem (i j : Fin Tag.F4.rank) :
    Certificates.A3LatticeF4.symm[Certificates.A3LatticeF4.rank * i.val + j.val]! =
      Tag.F4.symmetrizedCartan i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem symm_getElem_nat (i : Fin Tag.F4.rank) (j : Nat) (hj : j < Tag.F4.rank) :
    Certificates.A3LatticeF4.symm[Certificates.A3LatticeF4.rank * i.val + j]! =
      Tag.F4.symmetrizedCartan i ⟨j, hj⟩ := by
  rw [symm_getElem i ⟨j, hj⟩]

private theorem foldl_inner_nat (i : Nat) (hi : i < Certificates.A3LatticeF4.rank)
    (β : Fin Tag.F4.rank → ℤ) :
    (List.range Certificates.A3LatticeF4.rank).foldl (fun t j =>
        t + Certificates.A3LatticeF4.symm[Certificates.A3LatticeF4.rank * i + j]! *
          (toArr β)[j]!) 0
      = ∑ j : Fin Tag.F4.rank, Tag.F4.symmetrizedCartan ⟨i, hi⟩ j * β j := by
  rw [foldl_rank]
  rw [toArr_getElem!_nat β 0 (by decide), toArr_getElem!_nat β 1 (by decide),
      toArr_getElem!_nat β 2 (by decide), toArr_getElem!_nat β 3 (by decide)]
  rw [symm_getElem_nat ⟨i, hi⟩ 0 (by decide), symm_getElem_nat ⟨i, hi⟩ 1 (by decide),
      symm_getElem_nat ⟨i, hi⟩ 2 (by decide), symm_getElem_nat ⟨i, hi⟩ 3 (by decide)]
  rw [sum_univ_f4]
  rfl

private theorem form_toArr (α β : Fin Tag.F4.rank → ℤ) :
    Certificates.A3LatticeF4.form (toArr α) (toArr β) =
      α ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ β) := by
  rw [Certificates.A3LatticeF4.form, foldl_rank]
  rw [toArr_getElem!_nat α 0 (by decide), toArr_getElem!_nat α 1 (by decide),
      toArr_getElem!_nat α 2 (by decide), toArr_getElem!_nat α 3 (by decide)]
  rw [foldl_inner_nat 0 (by decide) β, foldl_inner_nat 1 (by decide) β,
      foldl_inner_nat 2 (by decide) β, foldl_inner_nat 3 (by decide) β]
  rw [dotProduct]
  simp only [Matrix.mulVec_apply_eq_sum, sum_univ_f4]
  rfl

private theorem pair3_foldl (γ : Fin Tag.F4.rank → ℤ) (c : Fin Tag.F4.rank → ZMod 3) :
    (List.range Certificates.A3LatticeF4.rank).foldl (fun s j =>
        s + (toArr γ)[j]! * Int.ofNat ((codes c)[j]!)) 0
      = ∑ i : Fin Tag.F4.rank, γ i * (c i).val := by
  rw [foldl_rank]
  rw [toArr_getElem!_nat γ 0 (by decide), toArr_getElem!_nat γ 1 (by decide),
      toArr_getElem!_nat γ 2 (by decide), toArr_getElem!_nat γ 3 (by decide)]
  rw [codes_getElem!_nat c 0 (by decide), codes_getElem!_nat c 1 (by decide),
      codes_getElem!_nat c 2 (by decide), codes_getElem!_nat c 3 (by decide)]
  rw [sum_univ_f4]
  rfl

private theorem pair3_eq (γ : Fin Tag.F4.rank → ℤ) (c : Fin Tag.F4.rank → ZMod 3) :
    Certificates.A3LatticeF4.pair3 (toArr γ) (codes c) =
      (∑ i : Fin Tag.F4.rank, γ i * (c i).val) % 3 := by
  rw [Certificates.A3LatticeF4.pair3, pair3_foldl]

private theorem ggLiePair_eq_intCast (γ : Fin Tag.F4.rank → ℤ) (c : Fin Tag.F4.rank → ZMod 3) :
    ggLiePair γ c = ((∑ i : Fin Tag.F4.rank, γ i * (c i).val : ℤ) : ZMod 3) := by
  rw [ggLiePair]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [ZMod.natCast_zmod_val]

private theorem pair3_toArr_codes (γ : Fin Tag.F4.rank → ℤ) (c : Fin Tag.F4.rank → ZMod 3) :
    Certificates.A3LatticeF4.pair3 (toArr γ) (codes c) = 0 ↔ ggLiePair γ c = 0 := by
  rw [pair3_eq, ggLiePair_eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.dvd_iff_emod_eq_zero]
  rfl

private theorem smul_add_eq_zero_of_comboZero (c₁ c₂ : Fin Tag.F4.rank → ZMod 3)
    {s t : Nat} (h : Certificates.A3LatticeF4.comboZero s t (codes c₁) (codes c₂) = true) :
    (s : ZMod 3) • c₁ + (t : ZMod 3) • c₂ = 0 := by
  funext j
  have hj := (List.all_eq_true.mp h) j.val (List.mem_range.mpr j.isLt)
  rw [beq_iff_eq] at hj
  rw [codes_getElem!_nat c₁ j.val j.isLt, codes_getElem!_nat c₂ j.val j.isLt] at hj
  have h3 : (3 : ℕ) ∣ (s * (c₁ j).val + t * (c₂ j).val) := by
    rw [Nat.dvd_iff_mod_eq_zero]; exact hj
  have hz : ((s * (c₁ j).val + t * (c₂ j).val : ℕ) : ZMod 3) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact h3
  show (s : ZMod 3) * c₁ j + (t : ZMod 3) * c₂ j = 0
  rw [← hz]
  push_cast
  rw [ZMod.natCast_zmod_val (c₁ j), ZMod.natCast_zmod_val (c₂ j)]

private theorem comboZero_eq_false (c₁ c₂ : Fin Tag.F4.rank → ZMod 3)
    (hind : ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0)
    (s t : Nat) (hs : s < 3) (ht : t < 3) (hst : ¬(s = 0 ∧ t = 0)) :
    Certificates.A3LatticeF4.comboZero s t (codes c₁) (codes c₂) = false := by
  by_contra h
  have htrue : Certificates.A3LatticeF4.comboZero s t (codes c₁) (codes c₂) = true := by
    cases hb : Certificates.A3LatticeF4.comboZero s t (codes c₁) (codes c₂) <;> simp_all
  have hz := smul_add_eq_zero_of_comboZero c₁ c₂ htrue
  have hst' := hind (s : ZMod 3) (t : ZMod 3) hz
  have hs0 : s = 0 := by
    have : (s : ZMod 3) = 0 := hst'.1
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at this
    omega
  have ht0 : t = 0 := by
    have : (t : ZMod 3) = 0 := hst'.2
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at this
    omega
  exact hst ⟨hs0, ht0⟩

private theorem indep_codes (c₁ c₂ : Fin Tag.F4.rank → ZMod 3)
    (hind : ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0) :
    Certificates.A3LatticeF4.indep (codes c₁) (codes c₂) = true := by
  rw [Certificates.A3LatticeF4.indep, List.all_eq_true]
  intro s hs
  rw [List.all_eq_true]
  intro t ht
  rw [List.mem_range] at hs ht
  by_cases hst : s = 0 ∧ t = 0
  · obtain ⟨rfl, rfl⟩ := hst; simp
  · have hc := comboZero_eq_false c₁ c₂ hind s t hs ht hst
    rw [hc]; simp

private abbrev rs : List (Array Int) := Certificates.A3LatticeF4.rootsOf ()

private def ksOf (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) : List (Array Int) :=
  rs.filter fun g =>
    Certificates.A3LatticeF4.pair3 g (codes c₁) == 0 &&
      Certificates.A3LatticeF4.pair3 g (codes c₂) == 0

private def csOf (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ) :
    List (Array Int) :=
  Certificates.A3LatticeF4.comp (ksOf c₁ c₂) (toArr m)

private def AdjRel (c₁ c₂ : Fin Tag.F4.rank → ZMod 3)
    (α β : Fin Tag.F4.rank → ℤ) : Prop :=
  α ∈ a3Ker Tag.F4 c₁ c₂ ∧ β ∈ a3Ker Tag.F4 c₁ c₂ ∧
    α ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ β) ≠ 0

private theorem rs_sub_all : rs.all (fun r => (List.finRange 48).any (fun m : Fin 48 =>
    decide (toArr (CFSG.RankThree.PartOne.KF4.f4RootVec m) = r))) = true := by
  decide +kernel

private theorem rs_sup_all : (List.finRange 48).all (fun m : Fin 48 =>
    rs.contains (toArr (CFSG.RankThree.PartOne.KF4.f4RootVec m))) = true := by
  decide +kernel

private theorem rs_sub {r : Array Int} (hr : r ∈ rs) :
    ∃ m : Fin 48, toArr (CFSG.RankThree.PartOne.KF4.f4RootVec m) = r := by
  have h := (List.all_eq_true.mp rs_sub_all) r hr
  obtain ⟨m, _, hm⟩ := List.any_eq_true.mp h
  exact ⟨m, of_decide_eq_true hm⟩

private theorem rs_sup (m : Fin 48) : toArr (CFSG.RankThree.PartOne.KF4.f4RootVec m) ∈ rs := by
  have h := (List.all_eq_true.mp rs_sup_all) m (by simp [List.mem_finRange])
  exact List.contains_iff.mp h

private theorem isRoot_iff_mem_rs (γ : Fin Tag.F4.rank → ℤ) :
    IsRoot Tag.F4 γ ↔ toArr γ ∈ rs := by
  constructor
  · intro h
    obtain ⟨m, rfl⟩ := CFSG.RankThree.PartOne.KF4.isRoot_iff_exists_f4RootVec.mp h
    exact rs_sup m
  · intro h
    obtain ⟨m, hm⟩ := rs_sub h
    rw [← toArr_injective hm]
    exact CFSG.RankThree.PartOne.KF4.isRoot_f4RootVec m

private theorem ks_subset_rs {c₁ c₂ : Fin Tag.F4.rank → ZMod 3} {x : Array Int}
    (hx : x ∈ ksOf c₁ c₂) : x ∈ rs :=
  (List.mem_filter.mp hx).1

private theorem a3Ker_iff_mem_ks
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (γ : Fin Tag.F4.rank → ℤ) :
    γ ∈ a3Ker Tag.F4 c₁ c₂ ↔ toArr γ ∈ ksOf c₁ c₂ := by
  rw [a3Ker, ksOf, List.mem_filter]
  constructor
  · rintro ⟨hroot, h1, h2⟩
    exact ⟨(isRoot_iff_mem_rs γ).mp hroot, by
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨(pair3_toArr_codes γ c₁).mpr h1, (pair3_toArr_codes γ c₂).mpr h2⟩⟩
  · rintro ⟨hmem, hpair⟩
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpair
    exact ⟨(isRoot_iff_mem_rs γ).mpr hmem,
      (pair3_toArr_codes γ c₁).mp hpair.1, (pair3_toArr_codes γ c₂).mp hpair.2⟩

private def CompInv (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ)
    (acc : List (Array Int)) : Prop :=
  acc.Nodup ∧ (∀ x ∈ acc, x ∈ ksOf c₁ c₂) ∧
    (∀ δ : Fin Tag.F4.rank → ℤ, toArr δ ∈ acc → Relation.EqvGen (AdjRel c₁ c₂) m δ)

private theorem compInv_foldl {α : Type*} (c₁ c₂ : Fin Tag.F4.rank → ZMod 3)
    (m : Fin Tag.F4.rank → ℤ) (l : List α)
    (f : List (Array Int) → α → List (Array Int)) (b : List (Array Int))
    (hb : CompInv c₁ c₂ m b)
    (hstep : ∀ acc a, a ∈ l → CompInv c₁ c₂ m acc → CompInv c₁ c₂ m (f acc a)) :
    CompInv c₁ c₂ m (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact hb
  | cons a l ih =>
    exact ih (f b a) (hstep b a (by simp) hb)
      (fun acc a' ha' hacc => hstep acc a' (List.mem_cons_of_mem a ha') hacc)

private theorem compInv_inner_step
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ) {acc : List (Array Int)}
    (hacc : CompInv c₁ c₂ m acc) {k : Array Int} (hk : k ∈ ksOf c₁ c₂) :
    CompInv c₁ c₂ m (if acc.contains k then acc
      else if acc.any (fun c => Certificates.A3LatticeF4.form c k != 0) then acc ++ [k]
      else acc) := by
  by_cases h1 : acc.contains k
  · simp only [h1, if_true]; exact hacc
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : acc.any (fun c => Certificates.A3LatticeF4.form c k != 0)
    · simp only [h2, if_true]
      have hkacc : k ∉ acc := fun hk' => h1 (List.contains_iff.mpr hk')
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hacc.1, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        intro hab
        exact hkacc (hab ▸ ha)
      · intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hacc.2.1 x hx
        · simp only [List.mem_singleton] at hx
          rwa [hx]
      · intro δ hδ
        rw [List.mem_append] at hδ
        rcases hδ with hδ | hδ
        · exact hacc.2.2 δ hδ
        · simp only [List.mem_singleton] at hδ
          obtain ⟨c, hcacc, hcf⟩ := List.any_eq_true.mp h2
          rw [bne_iff_ne] at hcf
          obtain ⟨m₁, hm₁⟩ := rs_sub (ks_subset_rs (hacc.2.1 c hcacc))
          obtain ⟨m₂, hm₂⟩ := rs_sub (ks_subset_rs hk)
          have hαker : CFSG.RankThree.PartOne.KF4.f4RootVec m₁ ∈ a3Ker Tag.F4 c₁ c₂ :=
            (a3Ker_iff_mem_ks c₁ c₂ _).mpr (hm₁.symm ▸ hacc.2.1 c hcacc)
          have hβker : CFSG.RankThree.PartOne.KF4.f4RootVec m₂ ∈ a3Ker Tag.F4 c₁ c₂ :=
            (a3Ker_iff_mem_ks c₁ c₂ _).mpr (hm₂.symm ▸ hk)
          have hadj : AdjRel c₁ c₂ (CFSG.RankThree.PartOne.KF4.f4RootVec m₁)
              (CFSG.RankThree.PartOne.KF4.f4RootVec m₂) := by
            refine ⟨hαker, hβker, ?_⟩
            rw [← form_toArr (CFSG.RankThree.PartOne.KF4.f4RootVec m₁)
              (CFSG.RankThree.PartOne.KF4.f4RootVec m₂), hm₁, hm₂]
            exact hcf
          have heq : Relation.EqvGen (AdjRel c₁ c₂) m
              (CFSG.RankThree.PartOne.KF4.f4RootVec m₁) :=
            hacc.2.2 _ (hm₁.symm ▸ hcacc)
          have hβδ : CFSG.RankThree.PartOne.KF4.f4RootVec m₂ = δ := by
            apply toArr_injective
            rw [hm₂, hδ]
          rw [← hβδ]
          exact Relation.EqvGen.trans _ _ _ heq (Relation.EqvGen.rel _ _ hadj)
    · simp only [h2, if_false]; exact hacc

private theorem compInv_ks_foldl
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ) (acc : List (Array Int))
    (hacc : CompInv c₁ c₂ m acc) :
    CompInv c₁ c₂ m (ksOf c₁ c₂ |>.foldl (fun cs k =>
      if cs.contains k then cs
      else if cs.any (fun c => Certificates.A3LatticeF4.form c k != 0) then cs ++ [k]
      else cs) acc) := by
  refine compInv_foldl c₁ c₂ m (ksOf c₁ c₂) _ acc hacc ?_
  intro acc' k hk hacc'
  exact compInv_inner_step c₁ c₂ m hacc' hk

private theorem compInv_comp
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ)
    (hm : toArr m ∈ ksOf c₁ c₂) :
    CompInv c₁ c₂ m (csOf c₁ c₂ m) := by
  rw [csOf, Certificates.A3LatticeF4.comp]
  refine compInv_foldl c₁ c₂ m (List.range (ksOf c₁ c₂).length)
    (fun cs _ => ksOf c₁ c₂ |>.foldl (fun cs k =>
      if cs.contains k then cs
      else if cs.any (fun c => Certificates.A3LatticeF4.form c k != 0) then cs ++ [k]
      else cs) cs) [toArr m] ?_ ?_
  · refine ⟨by simp, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      rwa [hx]
    · intro δ hδ
      simp only [List.mem_singleton] at hδ
      have : δ = m := toArr_injective hδ
      rw [this]
      exact Relation.EqvGen.refl m
  · intro acc a _ hacc
    exact compInv_ks_foldl c₁ c₂ m acc hacc

private theorem mem_foldl_of_mem {α : Type*} (l : List α)
    (f : List (Array Int) → α → List (Array Int)) (b : List (Array Int)) (x : Array Int)
    (hx : x ∈ b) (hstep : ∀ acc a, x ∈ acc → x ∈ f acc a) : x ∈ l.foldl f b := by
  induction l generalizing b with
  | nil => exact hx
  | cons a l ih => exact ih (f b a) (hstep b a hx)

private theorem mem_inner (ks acc : List (Array Int)) (seed : Array Int) (hx : seed ∈ acc) :
    seed ∈ ks.foldl (fun cs k => if cs.contains k then cs
      else if cs.any (fun c => Certificates.A3LatticeF4.form c k != 0) then cs ++ [k]
      else cs) acc := by
  refine mem_foldl_of_mem ks _ acc seed hx ?_
  intro acc' k hx'
  by_cases h1 : acc'.contains k
  · simp only [h1, if_true]; exact hx'
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : acc'.any (fun c => Certificates.A3LatticeF4.form c k != 0)
    · simp only [h2, if_true]; exact List.mem_append_left _ hx'
    · simp only [h2, if_false]; exact hx'

private theorem mem_comp_seed (ks : List (Array Int)) (seed : Array Int) :
    seed ∈ Certificates.A3LatticeF4.comp ks seed := by
  rw [Certificates.A3LatticeF4.comp]
  refine mem_foldl_of_mem (List.range ks.length) _ [seed] seed (by simp) ?_
  intro acc _ hx
  exact mem_inner ks acc seed hx

private theorem adjClosed_elim {ks cs : List (Array Int)}
    (h : Certificates.A3LatticeF4.adjClosed ks cs = true) :
    ∀ c ∈ cs, ∀ k ∈ ks, Certificates.A3LatticeF4.form c k = 0 ∨ k ∈ cs := by
  rw [Certificates.A3LatticeF4.adjClosed, List.all_eq_true] at h
  intro c hc k hk
  have h1 := h c hc
  rw [List.all_eq_true] at h1
  have h2 := h1 k hk
  rw [Bool.or_eq_true, beq_iff_eq, List.contains_iff] at h2
  exact h2

private theorem f4Symm_symm (i j : Fin Tag.F4.rank) :
    Tag.F4.symmetrizedCartan i j = Tag.F4.symmetrizedCartan j i := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem dotProduct_mulVec_comm (α β : Fin Tag.F4.rank → ℤ) :
    α ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ β) = β ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ α) := by
  rw [dotProduct_mulVec_symmetrizedCartan_eq_sum, dotProduct_mulVec_symmetrizedCartan_eq_sum,
      Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [f4Symm_symm j i]
  ring

private theorem mem_a3Comp_of_mem_cs
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ)
    (hm : toArr m ∈ ksOf c₁ c₂) {δ : Fin Tag.F4.rank → ℤ}
    (hδ : toArr δ ∈ csOf c₁ c₂ m) : δ ∈ a3Comp Tag.F4 c₁ c₂ m := by
  have hinv := compInv_comp c₁ c₂ m hm
  refine ⟨?_, hinv.2.2 δ hδ⟩
  exact (a3Ker_iff_mem_ks c₁ c₂ δ).mpr (hinv.2.1 (toArr δ) hδ)

private theorem mem_cs_of_mem_a3Comp
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ)
    (hadj : ∀ c ∈ csOf c₁ c₂ m, ∀ k ∈ ksOf c₁ c₂,
      Certificates.A3LatticeF4.form c k = 0 ∨ k ∈ csOf c₁ c₂ m)
    {δ : Fin Tag.F4.rank → ℤ} (hδ : δ ∈ a3Comp Tag.F4 c₁ c₂ m) :
    toArr δ ∈ csOf c₁ c₂ m := by
  obtain ⟨-, hδeqv⟩ := hδ
  have hseed : toArr m ∈ csOf c₁ c₂ m := mem_comp_seed (ksOf c₁ c₂) (toArr m)
  have hmotive : ∀ a b : Fin Tag.F4.rank → ℤ, Relation.EqvGen (AdjRel c₁ c₂) a b →
      (toArr a ∈ csOf c₁ c₂ m ↔ toArr b ∈ csOf c₁ c₂ m) := by
    intro a b hab
    refine Relation.EqvGen.rec (motive := fun a b _ =>
      toArr a ∈ csOf c₁ c₂ m ↔ toArr b ∈ csOf c₁ c₂ m) ?_ ?_ ?_ ?_ hab
    · intro x y hxy
      obtain ⟨hxker, hyker, hf⟩ := hxy
      have hxks : toArr x ∈ ksOf c₁ c₂ := (a3Ker_iff_mem_ks c₁ c₂ x).mp hxker
      have hyks : toArr y ∈ ksOf c₁ c₂ := (a3Ker_iff_mem_ks c₁ c₂ y).mp hyker
      constructor
      · intro hxcs
        have hf' : Certificates.A3LatticeF4.form (toArr x) (toArr y) ≠ 0 := by
          rwa [form_toArr]
        rcases hadj (toArr x) hxcs (toArr y) hyks with h0 | hycs
        · exact absurd h0 hf'
        · exact hycs
      · intro hycs
        have hf' : Certificates.A3LatticeF4.form (toArr y) (toArr x) ≠ 0 := by
          rw [form_toArr, dotProduct_mulVec_comm]
          exact hf
        rcases hadj (toArr y) hycs (toArr x) hxks with h0 | hxcs
        · exact absurd h0 hf'
        · exact hxcs
    · intro x; exact Iff.rfl
    · intro x y _ ih; exact ih.symm
    · intro x y z _ _ ih1 ih2; exact ih1.trans ih2
  exact (hmotive m δ hδeqv).mp hseed

private theorem a3Comp_eq_cs
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ)
    (hm : toArr m ∈ ksOf c₁ c₂)
    (hadj : ∀ c ∈ csOf c₁ c₂ m, ∀ k ∈ ksOf c₁ c₂,
      Certificates.A3LatticeF4.form c k = 0 ∨ k ∈ csOf c₁ c₂ m) :
    a3Comp Tag.F4 c₁ c₂ m = {δ : Fin Tag.F4.rank → ℤ | toArr δ ∈ csOf c₁ c₂ m} := by
  apply Set.Subset.antisymm
  · intro δ hδ
    show toArr δ ∈ csOf c₁ c₂ m
    exact mem_cs_of_mem_a3Comp c₁ c₂ m hadj hδ
  · intro δ hδ
    exact mem_a3Comp_of_mem_cs c₁ c₂ m hm hδ

private theorem ncard_a3Comp_eq_length
    (c₁ c₂ : Fin Tag.F4.rank → ZMod 3) (m : Fin Tag.F4.rank → ℤ)
    (hm : toArr m ∈ ksOf c₁ c₂)
    (hadj : ∀ c ∈ csOf c₁ c₂ m, ∀ k ∈ ksOf c₁ c₂,
      Certificates.A3LatticeF4.form c k = 0 ∨ k ∈ csOf c₁ c₂ m) :
    (a3Comp Tag.F4 c₁ c₂ m).ncard = (csOf c₁ c₂ m).length := by
  have hinv := compInv_comp c₁ c₂ m hm
  have himg : toArr '' {δ : Fin Tag.F4.rank → ℤ | toArr δ ∈ csOf c₁ c₂ m} =
      (↑(csOf c₁ c₂ m).toFinset : Set (Array Int)) := by
    ext y
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact List.mem_toFinset.mpr hδ
    · intro hy
      have hycs : y ∈ csOf c₁ c₂ m := List.mem_toFinset.mp hy
      obtain ⟨m', hm'⟩ := rs_sub (ks_subset_rs (hinv.2.1 y hycs))
      refine ⟨CFSG.RankThree.PartOne.KF4.f4RootVec m', ?_, hm'⟩
      show toArr (CFSG.RankThree.PartOne.KF4.f4RootVec m') ∈ csOf c₁ c₂ m
      rw [hm']
      exact hycs
  rw [a3Comp_eq_cs c₁ c₂ m hm hadj,
    ← Set.ncard_image_of_injective _ toArr_injective, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hinv.1]

private theorem codes_mem_vecs_all :
    ∀ c : Fin Tag.F4.rank → ZMod 3, codes c ∈ Certificates.A3LatticeF4.vecs := by
  decide +kernel

theorem a3SpecF4_of_check
    (h : Certificates.A3LatticeF4.check () = true) : A3SpecF4 := by
  intro c₁ c₂ hind m hm
  change (a3Comp Tag.F4 c₁ c₂ m).ncard ≠ 12
  have h' : (Certificates.A3LatticeF4.rootsClosed rs &&
      Certificates.A3LatticeF4.mainCheck rs) = true := by
    rw [Certificates.A3LatticeF4.check, Certificates.A3LatticeF4.verifyWith] at h
    exact h
  obtain ⟨-, hmc⟩ := Bool.and_eq_true_iff.mp h'
  have h1 := (List.all_eq_true.mp (by
    simpa only [Certificates.A3LatticeF4.mainCheck] using hmc)) (codes c₁)
      (codes_mem_vecs_all c₁)
  have h2 := (List.all_eq_true.mp h1) (codes c₂) (codes_mem_vecs_all c₂)
  rw [indep_codes c₁ c₂ hind] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  have hcomp : (ksOf c₁ c₂).all (fun m =>
      Certificates.A3LatticeF4.adjClosed (ksOf c₁ c₂)
        (Certificates.A3LatticeF4.comp (ksOf c₁ c₂) m) &&
      (Certificates.A3LatticeF4.comp (ksOf c₁ c₂) m).length != 12) = true := by
    simpa only [ksOf] using h2
  have hmks : toArr m ∈ ksOf c₁ c₂ := (a3Ker_iff_mem_ks c₁ c₂ m).mp hm
  have hmcomp := (List.all_eq_true.mp hcomp) (toArr m) hmks
  obtain ⟨hadj0, hlen0⟩ := Bool.and_eq_true_iff.mp hmcomp
  have hadj : Certificates.A3LatticeF4.adjClosed (ksOf c₁ c₂)
      (Certificates.A3LatticeF4.comp (ksOf c₁ c₂) (toArr m)) = true := hadj0
  have hlen : (Certificates.A3LatticeF4.comp (ksOf c₁ c₂) (toArr m)).length ≠ 12 := by
    have h := hlen0
    rw [bne_iff_ne] at h
    exact h
  intro h12
  rw [ncard_a3Comp_eq_length c₁ c₂ m hmks (adjClosed_elim hadj)] at h12
  exact hlen h12

theorem a3SpecF4_of_certificate :
    A3SpecF4 :=
  a3SpecF4_of_check Certificates.certificate715501

end CFSG.StandardType.LieCore
