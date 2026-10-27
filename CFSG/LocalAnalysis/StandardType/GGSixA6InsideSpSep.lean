module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
import CFSG.LocalAnalysis.StandardType.GGPRankBoundsEigen
import CFSG.LieType.BorelTits.Symplectic

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace CFSG.StandardType

namespace A6InsideSp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L] [Algebra K L]
  {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)

private theorem frame_form (d d' : Fin F.s → L) :
    (CFSG.LieType.BorelTits.spForm n K).β (F.Φ d) (F.Φ d') =
      ∑ i, F.β (d i) (d' i) := by
  rw [show (CFSG.LieType.BorelTits.spForm n K).β (F.Φ d) (F.Φ d') =
      CFSG.RankThree.Classical.spForm n K (F.Φ d) (F.Φ d') from by
    rw [spForm_β, CFSG.RankThree.Classical.spForm_apply]
    rfl]
  exact F.form d d'

private theorem torE_unit_eq_zero (hζo : IsPrimitiveRoot ζ 3) (a : ℕ)
    (ha0 : a ≠ 0) (ha3 : a < 3) : ζ ^ (a + a) + ζ ^ a + 1 = 0 := by
  have h : ζ ^ 2 + ζ + 1 = 0 := by
    have h3 : ζ ^ 3 = 1 := hζo.pow_eq_one
    have h1 : ζ - 1 ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      simpa using hζo.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num) (by norm_num)
    have h0 : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp h0).resolve_left h1
  have h3 : ζ ^ 3 = 1 := hζo.pow_eq_one
  interval_cases a
  · exact absurd rfl ha0
  · simpa using h
  · have h4 : ζ ^ (2 + 2) = ζ := by
      rw [show 2 + 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    rw [h4]
    linear_combination h

private theorem tor_proj (hζo : IsPrimitiveRoot ζ 3) (f : Fin F.s → ZMod 3) (d : Fin F.s → L) :
    spEnd (F.tor f) (spEnd (F.tor f) (F.Φ d)) + spEnd (F.tor f) (F.Φ d) + F.Φ d =
      F.Φ (fun i => if f i = 0 then d i else 0) := by
  rw [F.tor_acts f, F.tor_acts f, ← map_add, ← map_add]
  congr 1
  funext i
  simp only [Pi.add_apply, ChoiceTwo.torE_apply]
  by_cases h : f i = 0
  · rw [if_pos h, h, ZMod.val_zero, pow_zero, one_mul, one_mul,
      ChoiceTwo.add_self_eq_zero_of_charTwo (K := K) (w := d i), zero_add]
  · have ha0 : (f i).val ≠ 0 := fun h0 => h ((ZMod.val_eq_zero (f i)).mp h0)
    have ha3 : (f i).val < 3 := ZMod.val_lt (f i)
    have hfac : ζ ^ ((f i).val + (f i).val) + ζ ^ (f i).val + 1 = 0 :=
      torE_unit_eq_zero hζo _ ha0 ha3
    have e : ζ ^ (f i).val * (ζ ^ (f i).val * d i) + ζ ^ (f i).val * d i + d i =
        (ζ ^ ((f i).val + (f i).val) + ζ ^ (f i).val + 1) * d i := by
      rw [pow_add]
      ring
    rw [if_neg h, e, hfac, zero_mul]

private theorem sum_single_left (j : Fin F.s) (x : L) (d' : Fin F.s → L) :
    (∑ i : Fin F.s, F.β ((Pi.single j x : Fin F.s → L) i) (d' i)) = F.β x (d' j) := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem sum_single_single (j : Fin F.s) (x y : L) :
    (∑ i : Fin F.s, F.β ((Pi.single j x : Fin F.s → L) i)
      ((Pi.single j y : Fin F.s → L) i)) = F.β x y := by
  rw [sum_single_left F j x (Pi.single j y : Fin F.s → L)]
  simp

private theorem endo_add_apply (g : StatedSp n K) (w : Fin n ⊕ Fin n → K) :
    (natRep (StatedSp n K) g * natRep (StatedSp n K) g
      + natRep (StatedSp n K) g + 1) w =
      natRep (StatedSp n K) g (natRep (StatedSp n K) g w)
        + natRep (StatedSp n K) g w + w := by
  change (spEnd g * spEnd g + spEnd g + 1) w = spEnd g (spEnd g w) + spEnd g w + w
  rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]

private theorem tor_proj_natRep (hζo : IsPrimitiveRoot ζ 3) (f : Fin F.s → ZMod 3)
    (d : Fin F.s → L) :
    (natRep (StatedSp n K) (F.tor f) * natRep (StatedSp n K) (F.tor f)
      + natRep (StatedSp n K) (F.tor f) + 1) (F.Φ d) =
      F.Φ (fun i => if f i = 0 then d i else 0) := by
  rw [endo_add_apply]
  exact tor_proj F hζo f d

theorem eq_bot_of_separating [Module.Finite K L] (hK : Nat.card K = 2)
    (hζo : IsPrimitiveRoot ζ 3) (hL : Module.finrank K L = 2) {B U : Subgroup (StatedSp n K)}
    (hs : 2 ≤ F.s) (hsep : ∀ i j : Fin F.s, i ≠ j → ∃ f, F.tor f ∈ B ∧ f i = 0 ∧ f j ≠ 0)
    (hU : IsPGroup 2 U) (hBU : B ≤ Subgroup.normalizer (U : Set (StatedSp n K))) : U = ⊥ := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hU1
  refine PRankBounds.false_of_fixSub_inf_perp 2 (CFSG.LieType.BorelTits.spForm n K)
    (CFSG.LieType.BorelTits.natRep (StatedSp n K))
    (CFSG.LieType.BorelTits.isIsometric_natRep_statedSp n K)
    (CFSG.LieType.BorelTits.natRep_injective _) U hU hU1 ?_
  set W : Submodule K (Fin n ⊕ Fin n → K) :=
    PRankBounds.fixSub (CFSG.LieType.BorelTits.natRep (StatedSp n K)) U with hWdef
  set R : Submodule K (Fin n ⊕ Fin n → K) :=
    W ⊓ (CFSG.LieType.BorelTits.spForm n K).perp W with hRdef
  change R = ⊥
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  have hBinv : ∀ b ∈ B, ∀ w ∈ R, natRep (StatedSp n K) b w ∈ R := by
    intro b hb w hw
    rw [hRdef] at hw ⊢
    refine ⟨?_, ?_⟩
    · rw [hWdef]
      exact PRankBounds.apply_mem_fixSub (hBU hb) hw.1
    · exact IsIsometric.apply_mem_perp_of_forall
        (CFSG.LieType.BorelTits.isIsometric_natRep_statedSp n K)
        (fun u hu => by
          rw [hWdef] at hu ⊢
          exact PRankBounds.apply_mem_fixSub (hBU (inv_mem hb)) hu) hw.2
  have hTmem : ∀ f, F.tor f ∈ B → ∀ w ∈ R,
      (natRep (StatedSp n K) (F.tor f) * natRep (StatedSp n K) (F.tor f)
        + natRep (StatedSp n K) (F.tor f) + 1) w ∈ R := by
    intro f hf w hw
    have h1 : natRep (StatedSp n K) (F.tor f) w ∈ R := hBinv _ hf w hw
    have h2 : natRep (StatedSp n K) (F.tor f) (natRep (StatedSp n K) (F.tor f) w) ∈ R :=
      hBinv _ hf _ h1
    have heq : (natRep (StatedSp n K) (F.tor f) * natRep (StatedSp n K) (F.tor f)
        + natRep (StatedSp n K) (F.tor f) + 1) w =
        natRep (StatedSp n K) (F.tor f) (natRep (StatedSp n K) (F.tor f) w)
          + natRep (StatedSp n K) (F.tor f) w + w := by
      exact endo_add_apply (F.tor f) w
    rw [heq]
    exact add_mem (add_mem h2 h1) hw
  have hdj : ∀ j : Fin F.s, d j = 0 := by
    intro j
    let ff : Fin F.s → (Fin F.s → ZMod 3) := fun i =>
      if h : i = j then 0 else Classical.choose (hsep j i (Ne.symm h))
    have hff_mem : ∀ i (hi : i ≠ j), F.tor (ff i) ∈ B := by
      intro i hi
      simp only [ff, dif_neg hi]
      exact (Classical.choose_spec (hsep j i (Ne.symm hi))).1
    have hff_j : ∀ i (hi : i ≠ j), ff i j = 0 := by
      intro i hi
      simp only [ff, dif_neg hi]
      exact (Classical.choose_spec (hsep j i (Ne.symm hi))).2.1
    have hff_i : ∀ i (hi : i ≠ j), ff i i ≠ 0 := by
      intro i hi
      simp only [ff, dif_neg hi]
      exact (Classical.choose_spec (hsep j i (Ne.symm hi))).2.2
    have hcomp : ∀ s : Finset (Fin F.s), (∀ i ∈ s, i ≠ j) →
        F.Φ (fun l => if ∀ i ∈ s, ff i l = 0 then d l else 0) ∈ R := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        have hfun : (fun l => if ∀ i ∈ (∅ : Finset (Fin F.s)), ff i l = 0 then d l else 0)
            = d := by
          funext l
          simp
        rw [hfun]
        exact hv
      | insert a s ha ih =>
        intro hs'
        have haj : a ≠ j := hs' a (Finset.mem_insert_self a s)
        have hs'' : ∀ i ∈ s, i ≠ j := fun i hi => hs' i (Finset.mem_insert_of_mem hi)
        have hprev := ih hs''
        set ds : Fin F.s → L := fun l => if ∀ i ∈ s, ff i l = 0 then d l else 0 with hds
        have hprev' : F.Φ ds ∈ R := by simpa [hds] using hprev
        have hnew := hTmem (ff a) (hff_mem a haj) (F.Φ ds) hprev'
        have hfun : (fun i => if ff a i = 0 then ds i else 0) =
            (fun l => if ∀ i ∈ insert a s, ff i l = 0 then d l else 0) := by
          funext l
          by_cases hfa : ff a l = 0 <;> simp [hds, hfa, Finset.mem_insert]
        rw [← hfun, ← tor_proj_natRep F hζo (ff a) ds]
        exact hnew
    have hu : F.Φ (Pi.single j (d j)) ∈ R := by
      have h := hcomp (Finset.univ.erase j) (fun i hi => Finset.ne_of_mem_erase hi)
      have hfun : (fun l => if ∀ i ∈ Finset.univ.erase j, ff i l = 0 then d l else 0) =
          (Pi.single j (d j) : Fin F.s → L) := by
        funext l
        by_cases hlj : l = j
        · subst hlj
          rw [if_pos]
          · simp
          · intro i hi
            exact hff_j i (Finset.ne_of_mem_erase hi)
        · rw [if_neg, Pi.single_eq_of_ne hlj]
          · intro hc
            exact hff_i l hlj (hc l (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ l⟩))
      rwa [hfun] at h
    obtain ⟨i, hij⟩ := Fintype.exists_ne_of_one_lt_card
      (α := Fin F.s) (by rw [Fintype.card_fin]; omega) j
    obtain ⟨g, hgB, -, hgj⟩ := hsep i j hij
    have htoru : spEnd (F.tor g) (F.Φ (Pi.single j (d j))) =
        F.Φ (Pi.single j (ζ ^ (g j).val * d j)) := by
      rw [F.tor_acts g]
      congr 1
      funext l
      rw [ChoiceTwo.torE_apply]
      by_cases hlj : l = j
      · subst hlj
        simp
      · simp [Pi.single_eq_of_ne hlj]
    have htorW : spEnd (F.tor g) (F.Φ (Pi.single j (d j))) ∈ W :=
      PRankBounds.apply_mem_fixSub (hBU hgB) hu.1
    have hp0 : (CFSG.LieType.BorelTits.spForm n K).β (F.Φ (Pi.single j (d j)))
        (spEnd (F.tor g) (F.Φ (Pi.single j (d j)))) = 0 := by
      rw [hRdef] at hu
      exact (CFSG.LieType.BorelTits.spForm n K).refl _ _
        ((CFSG.LieType.BorelTits.spForm n K).mem_perp.mp hu.2 _ htorW)
    have hz : F.β (d j) (ζ ^ (g j).val * d j) = 0 := by
      have h0 : (CFSG.LieType.BorelTits.spForm n K).β (F.Φ (Pi.single j (d j)))
          (F.Φ (Pi.single j (ζ ^ (g j).val * d j))) = 0 := by
        rw [← htoru]
        exact hp0
      rw [frame_form F (Pi.single j (d j)) (Pi.single j (ζ ^ (g j).val * d j)),
        sum_single_single F j] at h0
      exact h0
    have hdd : F.β (d j) (d j) = 0 := by
      have h0 : (CFSG.LieType.BorelTits.spForm n K).β (F.Φ (Pi.single j (d j)))
          (F.Φ (Pi.single j (d j))) = 0 := spForm_self n K _
      rw [frame_form F (Pi.single j (d j)) (Pi.single j (d j)), sum_single_single F j] at h0
      exact h0
    by_contra hx
    have hζnz : ζ ≠ 0 := hζo.ne_zero (by norm_num)
    have hζa0 : ζ ^ (g j).val ≠ 0 := pow_ne_zero _ hζnz
    have hζa1 : ζ ^ (g j).val ≠ 1 :=
      hζo.pow_ne_one_of_pos_of_lt (fun h0 => hgj ((ZMod.val_eq_zero (g j)).mp h0))
        (ZMod.val_lt (g j))
    have hζaK : ζ ^ (g j).val * d j ∉ Submodule.span K {d j} := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hc' : (algebraMap K L c) * d j = ζ ^ (g j).val * d j := by
        rwa [Algebra.smul_def] at hc
      have hcdj : (ζ ^ (g j).val - algebraMap K L c) * d j = 0 := by
        rw [sub_mul, hc', sub_self]
      have hζeq : ζ ^ (g j).val = algebraMap K L c :=
        sub_eq_zero.mp ((mul_eq_zero.mp hcdj).resolve_right hx)
      rcases ChoiceTwo.eq_zero_or_eq_one hK c with hc0 | hc1
      · rw [hc0, map_zero] at hζeq
        exact hζa0 hζeq
      · rw [hc1, map_one] at hζeq
        exact hζa1 hζeq
    have hspan : Submodule.span K {d j} ⊔ Submodule.span K {ζ ^ (g j).val * d j} = ⊤ := by
      have hfin : Module.finrank K ↥(Submodule.span K {d j} ⊔
          Submodule.span K {ζ ^ (g j).val * d j}) = 2 := by
        rw [Submodule.finrank_sup_span_singleton hζaK, finrank_span_singleton hx]
      exact Submodule.eq_top_of_finrank_eq (hfin.trans hL.symm)
    have hzero : ∀ z : L, F.β (d j) z = 0 := by
      intro z
      have hzmem : z ∈ Submodule.span K {d j} ⊔
          Submodule.span K {ζ ^ (g j).val * d j} := hspan ▸ Submodule.mem_top
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hzmem
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_add, map_smul, map_smul, hdd, hz, smul_zero, smul_zero, add_zero]
    have hu0 : F.Φ (Pi.single j (d j)) = 0 := by
      refine (CFSG.LieType.BorelTits.spForm n K).nondeg _ fun w => ?_
      obtain ⟨d', rfl⟩ := F.Φ.surjective w
      rw [frame_form F (Pi.single j (d j)) d', sum_single_left F j]
      exact hzero (d' j)
    have hsingle0 : (Pi.single j (d j) : Fin F.s → L) = 0 :=
      F.Φ.injective (by simpa using hu0)
    exact hx (by simpa using congrFun hsingle0 j)
  rw [show d = 0 from funext hdj, LinearEquiv.map_zero]

end A6InsideSp

end CFSG.StandardType

