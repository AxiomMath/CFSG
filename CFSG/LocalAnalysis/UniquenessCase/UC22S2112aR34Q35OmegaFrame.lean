module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35OmegaBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBInv

import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7

open CFSG.OddStandard.SmallF3.Omega CFSG.GroupTheory CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def frameSignGroup (fr : Sec4IFrame Q) : Subgroup (OGroup Q) where
  carrier := {g | ∃ u : Fin 7 → ZMod 2, IsEvenVec u ∧ sec4IT fr u = g}
  mul_mem' := by
    rintro g h ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨u + w, ?_, sec4IT_add fr u w⟩
    rw [IsEvenVec] at hu hw ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, hu, hw, add_zero]
  one_mem' := ⟨0, by simp [IsEvenVec], sec4IT_zero fr⟩
  inv_mem' := by
    rintro g ⟨u, hu, rfl⟩
    exact ⟨u, hu, eq_inv_of_mul_eq_one_right (sec4IT_mul_self fr u)⟩

theorem frameSignGroup_le_omegaGroup (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    frameSignGroup fr ≤ omegaGroup hQ := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := hg
  change sec4IMono fr 1 u ∈ omegaGroup hQ
  exact (sec4IMono_mem_omegaGroup_iff hQ fr 1 u).mpr ⟨Equiv.Perm.sign_one, hu⟩

theorem isPGroup_frameSignGroup (fr : Sec4IFrame Q) : IsPGroup 2 (frameSignGroup fr) := by
  intro g
  obtain ⟨u, _, hgu⟩ := g.2
  have hg2 : (g : OGroup Q) ^ 2 = 1 := by
    rw [pow_two, ← hgu]
    exact sec4IT_mul_self fr u
  exact ⟨1, by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_one] using hg2⟩

private theorem sec4ISgn_eq_neg_one_of_ne_zero {u : ZMod 2} (hu : u ≠ 0) :
    sec4ISgn u = -1 := by
  revert u
  decide

private theorem mem_commSp_sec4IT_iff (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) (v : V) :
    v ∈ commSp (sec4IT fr s) ↔ ∀ i, s i = 0 → fr.b.repr v i = 0 := by
  rw [mem_commSp_iff (sec4IT_mul_self fr s)]
  constructor
  · intro hv i hi
    have h := congrArg (fun w => fr.b.repr w i) hv
    simp only [map_neg] at h
    rw [sec4IT_repr] at h
    rw [hi, sec4ISgn_zero] at h
    have hx : fr.b.repr v i = -fr.b.repr v i := by simpa using h
    have h2 : (2 : ZMod 3) * fr.b.repr v i = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp hx
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  · intro hv
    apply fr.b.ext_elem
    intro i
    rw [sec4IT_repr, map_neg]
    by_cases hi : s i = 0
    · have hx : (fr.b.repr v) i = 0 := hv i hi
      rw [hi, sec4ISgn_zero, Units.val_one, one_mul]
      rw [Finsupp.neg_apply, hx, neg_zero]
    · rw [sec4ISgn_eq_neg_one_of_ne_zero hi]
      simp

theorem commSp_sec4IT (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) :
    commSp (sec4IT fr s) = Submodule.span (ZMod 3) (fr.b '' {i | s i ≠ 0}) := by
  apply le_antisymm
  · intro v hv
    rw [Module.Basis.mem_span_image]
    intro i hi
    by_contra hsi
    have h0 : fr.b.repr v i = 0 :=
      (mem_commSp_sec4IT_iff fr s v).mp hv i (not_not.mp hsi)
    exact (Finsupp.mem_support_iff.mp (by simpa using hi)) h0
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact (mem_commSp_sec4IT_iff fr s (fr.b i)).mpr fun j hj => by
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with hji
      · exact absurd (show s i = 0 from hji.symm ▸ hj) hi
      · rfl

private theorem mem_fixSp_sec4IT_iff (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) (v : V) :
    v ∈ fixSp (sec4IT fr s) ↔ ∀ i, s i ≠ 0 → fr.b.repr v i = 0 := by
  rw [mem_fixSp_iff]
  constructor
  · intro hv i hi
    have h := congrArg (fun w => fr.b.repr w i) hv
    rw [sec4IT_repr, sec4ISgn_eq_neg_one_of_ne_zero hi] at h
    have hx : fr.b.repr v i = -fr.b.repr v i := by simpa using h.symm
    have h2 : (2 : ZMod 3) * fr.b.repr v i = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp hx
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  · intro hv
    apply fr.b.ext_elem
    intro i
    rw [sec4IT_repr]
    by_cases hi : s i = 0
    · rw [hi, sec4ISgn_zero, Units.val_one, one_mul]
    · rw [sec4ISgn_eq_neg_one_of_ne_zero hi, hv i hi]
      simp

theorem fixSp_sec4IT (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) :
    fixSp (sec4IT fr s) = Submodule.span (ZMod 3) (fr.b '' {i | s i = 0}) := by
  apply le_antisymm
  · intro v hv
    rw [Module.Basis.mem_span_image]
    intro i hi
    by_contra hsi
    have h0 : fr.b.repr v i = 0 :=
      (mem_fixSp_sec4IT_iff fr s v).mp hv i hsi
    exact (Finsupp.mem_support_iff.mp (by simpa using hi)) h0
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact (mem_fixSp_sec4IT_iff fr s (fr.b i)).mpr fun j hj => by
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with hji
      · exact absurd (hji.symm ▸ hi) hj
      · rfl

private theorem fin7_ne_add_one (i : Fin 7) : i ≠ i + 1 := by
  revert i
  decide

private theorem fin7_ne_add_two (i : Fin 7) : i ≠ i + 2 := by
  revert i
  decide

private theorem fin7_add_one_ne_add_two (i : Fin 7) : i + 1 ≠ i + 2 := by
  revert i
  decide

private theorem sec4ISgn_add_single_eq_neg {a b l : Fin 7} (hab : a ≠ b) (h : l = a ∨ l = b) :
    ((sec4ISgn ((Pi.single a 1 + Pi.single b 1 :
        Fin 7 → ZMod 2) l) : (ZMod 3)ˣ) : ZMod 3) = -1 := by
  rcases h with rfl | rfl
  · rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
    decide
  · rw [Pi.add_apply, Pi.single_eq_of_ne hab.symm, Pi.single_eq_same, zero_add]
    decide

private theorem sec4ISgn_add_single_eq_one {a b l : Fin 7} (hla : l ≠ a) (hlb : l ≠ b) :
    ((sec4ISgn ((Pi.single a 1 + Pi.single b 1 :
        Fin 7 → ZMod 2) l) : (ZMod 3)ˣ) : ZMod 3) = 1 := by
  rw [Pi.add_apply, Pi.single_eq_of_ne hla, Pi.single_eq_of_ne hlb, add_zero]
  decide

private theorem repr_sub_sec4IT (fr : Sec4IFrame Q) (s : Fin 7 → ZMod 2) (x : V) (l : Fin 7) :
    fr.b.repr (x - (sec4IT fr s : V ≃ₗ[ZMod 3] V) x) l =
      (1 - ((sec4ISgn (s l) : (ZMod 3)ˣ) : ZMod 3)) * fr.b.repr x l := by
  rw [map_sub, Finsupp.sub_apply, sec4IT_repr]
  ring

private theorem zmod3_one_sub_neg_one (a : ZMod 3) :
    (1 - (-1)) * ((1 - (-1)) * a) = a := by
  revert a
  decide

private theorem frameSign_coord_eq (fr : Sec4IFrame Q) (w : V) (i : Fin 7) :
    (w - (sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) : V ≃ₗ[ZMod 3] V) w) -
      (sec4IT fr (Pi.single i 1 + Pi.single (i + 2) 1) : V ≃ₗ[ZMod 3] V)
        (w - (sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) : V ≃ₗ[ZMod 3] V) w) =
      fr.b.repr w i • fr.b i := by
  classical
  have h1 : i ≠ i + 1 := fin7_ne_add_one i
  have h2 : i ≠ i + 2 := fin7_ne_add_two i
  have h3 : i + 1 ≠ i + 2 := fin7_add_one_ne_add_two i
  apply fr.b.ext_elem
  intro l
  rw [repr_sub_sec4IT fr (Pi.single i 1 + Pi.single (i + 2) 1)
      (w - (sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) :
        V ≃ₗ[ZMod 3] V) w) l,
    repr_sub_sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) w l,
    map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  by_cases hli : l = i
  · rw [hli]
    rw [sec4ISgn_add_single_eq_neg (a := i) (b := i + 1) h1 (Or.inl rfl),
      sec4ISgn_add_single_eq_neg (a := i) (b := i + 2) h2 (Or.inl rfl),
      if_pos rfl, mul_one]
    exact zmod3_one_sub_neg_one _
  · by_cases hlj : l = i + 1
    · rw [hlj]
      rw [sec4ISgn_add_single_eq_neg (a := i) (b := i + 1) h1 (Or.inr rfl),
        sec4ISgn_add_single_eq_one (a := i) (b := i + 2) (l := i + 1) h1.symm h3,
        if_neg h1, mul_zero]
      simp
    · by_cases hlk : l = i + 2
      · rw [hlk]
        rw [sec4ISgn_add_single_eq_one (a := i) (b := i + 1) (l := i + 2) h2.symm h3.symm,
          sec4ISgn_add_single_eq_neg (a := i) (b := i + 2) h2 (Or.inr rfl),
          if_neg h2, mul_zero]
        simp
      · rw [sec4ISgn_add_single_eq_one (a := i) (b := i + 1) hli hlj,
          sec4ISgn_add_single_eq_one (a := i) (b := i + 2) hli hlk,
          if_neg (Ne.symm hli), mul_zero]
        simp

private theorem pi_single_indicator (a : Fin 7) :
    (Pi.single a (1 : ZMod 2) : Fin 7 → ZMod 2) = fun i => if i = a then 1 else 0 := by
  funext i
  by_cases hi : i = a
  · rw [hi]
    simp
  · rw [if_neg hi]
    exact Pi.single_eq_of_ne hi 1

private theorem sum_if_eq_one (a : Fin 7) :
    (∑ i, (if i = a then (1 : ZMod 2) else 0)) = 1 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · intro h
    exact absurd (Finset.mem_univ a) h

private theorem isEvenVec_single_add_single (a b : Fin 7) :
    IsEvenVec (Pi.single a (1 : ZMod 2) + Pi.single b (1 : ZMod 2)) := by
  rw [IsEvenVec, pi_single_indicator a, pi_single_indicator b]
  change (∑ i, ((if i = a then (1 : ZMod 2) else 0) + (if i = b then 1 else 0))) = 0
  rw [Finset.sum_add_distrib, sum_if_eq_one a, sum_if_eq_one b]
  decide

private theorem frameSign_coord_smul_mem (fr : Sec4IFrame Q) {W : Submodule (ZMod 3) V}
    (hW : ∀ g ∈ frameSignGroup fr, ∀ w ∈ W, (g : V ≃ₗ[ZMod 3] V) w ∈ W)
    {w : V} (hw : w ∈ W) (i : Fin 7) :
    fr.b.repr w i • fr.b i ∈ W := by
  have hsj : IsEvenVec (Pi.single i 1 + Pi.single (i + 1) 1) :=
    isEvenVec_single_add_single i (i + 1)
  have hrk : IsEvenVec (Pi.single i 1 + Pi.single (i + 2) 1) :=
    isEvenVec_single_add_single i (i + 2)
  have hB1 : sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) ∈ frameSignGroup fr :=
    ⟨_, hsj, rfl⟩
  have hB2 : sec4IT fr (Pi.single i 1 + Pi.single (i + 2) 1) ∈ frameSignGroup fr :=
    ⟨_, hrk, rfl⟩
  have hx : w - (sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) :
      V ≃ₗ[ZMod 3] V) w ∈ W := W.sub_mem hw (hW _ hB1 w hw)
  have hy : (w - (sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) :
      V ≃ₗ[ZMod 3] V) w) - (sec4IT fr (Pi.single i 1 + Pi.single (i + 2) 1) :
      V ≃ₗ[ZMod 3] V) (w - (sec4IT fr (Pi.single i 1 + Pi.single (i + 1) 1) :
      V ≃ₗ[ZMod 3] V) w) ∈ W := W.sub_mem hx (hW _ hB2 _ hx)
  rwa [frameSign_coord_eq fr w i] at hy

theorem eq_span_of_frameSignGroup_invariant (fr : Sec4IFrame Q) {W : Submodule (ZMod 3) V}
    (hW : ∀ g ∈ frameSignGroup fr, ∀ w ∈ W, (g : V ≃ₗ[ZMod 3] V) w ∈ W) :
    W = Submodule.span (ZMod 3) (fr.b '' {i | fr.b i ∈ W}) := by
  classical
  apply le_antisymm
  · intro w hw
    have hsum : w = ∑ i, fr.b.repr w i • fr.b i := (fr.b.sum_repr w).symm
    rw [hsum]
    apply Submodule.sum_mem
    intro i _
    by_cases hc : fr.b.repr w i = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · have hmem := frameSign_coord_smul_mem fr hW hw i
      have hbi : fr.b i ∈ W := by
        have h1 := W.smul_mem (fr.b.repr w i)⁻¹ hmem
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hbi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hi

private theorem zmod2_add_one_ne_zero_iff (x : ZMod 2) : x + 1 ≠ 0 ↔ x = 0 := by
  revert x
  decide

private theorem neg_one_sq : (-1 : ℤˣ) ^ 2 = 1 := by
  decide

private theorem neg_one_cube : (-1 : ℤˣ) ^ 3 = -1 := by
  decide

theorem exists_split_of_frameSignGroup_invariant
    (hE5 : ∀ (X : Type) [Group X], LieModel X .PSp 2 3 1 → SylowPQMaximal 2 5 X)
    (hE6 : ∀ (X : Type) [Group X], LieModel X .PSU 4 3 1 → SylowPQMaximal 2 5 X)
    (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) (W : Submodule (ZMod 3) V) (hW0 : W ≠ ⊥)
    (hW1 : W ≠ ⊤) (hW : ∀ g ∈ frameSignGroup fr, ∀ w ∈ W, (g : V ≃ₗ[ZMod 3] V) w ∈ W) :
    ∃ (s : OGroup Q) (hs : s * s = 1), commSp s = W ∧
      SylowPQMaximal 2 5 (omegaGroup (nondegenerate_restrict_fixSp hQ hs)) ∧
      SylowPQMaximal 2 5 (omegaGroup (nondegenerate_restrict_commSp hQ hs)) := by
  classical
  set s : Fin 7 → ZMod 2 := fun i => if fr.b i ∈ W then 1 else 0
  have htsq : sec4IT fr s * sec4IT fr s = 1 := sec4IT_mul_self fr s
  have hsupp : {i : Fin 7 | s i ≠ 0} = {i : Fin 7 | fr.b i ∈ W} := by
    ext i
    show (if fr.b i ∈ W then (1 : ZMod 2) else 0) ≠ 0 ↔ fr.b i ∈ W
    by_cases hi : fr.b i ∈ W
    · rw [if_pos hi]
      simp [hi]
    · rw [if_neg hi]
      simp [hi]
  have hcomm : commSp (sec4IT fr s) = W := by
    rw [commSp_sec4IT, hsupp, ← eq_span_of_frameSignGroup_invariant fr hW]
  have hdimV : Module.finrank (ZMod 3) V = 7 := by
    rw [Module.finrank_eq_card_basis fr.b]
    simp
  have hdimC : Module.finrank (ZMod 3) (commSp (sec4IT fr s)) = vecWeight s := by
    simpa only [invDim] using sec4IT_invDim fr s
  have hn0 : vecWeight s ≠ 0 := by
    intro h0
    apply hW0
    have hfin : Module.finrank (ZMod 3) (commSp (sec4IT fr s)) = 0 := by rw [hdimC, h0]
    rw [← hcomm]
    exact Submodule.finrank_eq_zero.mp hfin
  have hn7 : vecWeight s ≠ 7 := by
    intro h7
    apply hW1
    rw [← hcomm]
    apply Submodule.eq_top_of_finrank_eq
    rw [hdimC, h7, hdimV]
  have hnle : vecWeight s ≤ 7 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin 7)) (fun i => s i ≠ 0)
    simpa only [vecWeight, Finset.card_univ, Fintype.card_fin] using h
  have hn1 : 1 ≤ vecWeight s := by
    have := Nat.pos_of_ne_zero hn0
    omega
  have hn6 : vecWeight s ≤ 6 := by omega
  have hdimF : Module.finrank (ZMod 3) (fixSp (sec4IT fr s)) = 7 - vecWeight s := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) (sec4IT fr s)
    rw [hdimC, hdimV] at h
    omega
  have hweight : vecWeight (s + sec4IOnes) = 7 - vecWeight s := by
    have hnot : Finset.univ.filter (fun i => ¬ s i ≠ 0) =
        Finset.univ.filter (fun i => (s + sec4IOnes) i ≠ 0) := by
      apply Finset.filter_congr
      intro i _
      simp only [Pi.add_apply, sec4IOnes, not_not]
      exact (zmod2_add_one_ne_zero_iff (s i)).symm
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i => s i ≠ 0)
    rw [hnot] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    simp only [vecWeight]
    omega
  have hfix_eq : commSp (sec4IT fr (s + sec4IOnes)) = fixSp (sec4IT fr s) := by
    have hset : {i : Fin 7 | (s + sec4IOnes) i ≠ 0} = {i : Fin 7 | s i = 0} := by
      ext i
      simp only [Set.mem_setOf_eq, Pi.add_apply, sec4IOnes]
      exact zmod2_add_one_ne_zero_iff (s i)
    rw [commSp_sec4IT, fixSp_sec4IT, hset]
  have hsignC : Even (vecWeight s) →
      quadSign (Q.restrict (commSp (sec4IT fr s))) = (-1) ^ (vecWeight s / 2) := by
    intro he
    have hse : IsEvenVec s := (sec4I_isEvenVec_iff_even_vecWeight s).mpr he
    have h := congrArg Prod.snd (sec4IT_invType hQ fr hse)
    simpa only [invType, invSign] using h
  have hsignF : Odd (vecWeight s) →
      quadSign (Q.restrict (fixSp (sec4IT fr s))) = (-1) ^ ((7 - vecWeight s) / 2) := by
    intro ho
    have hsne : ¬ IsEvenVec s := by
      rw [sec4I_isEvenVec_iff_even_vecWeight]
      rintro ⟨m, hm⟩
      rcases ho with ⟨k, hk⟩
      omega
    have hse : IsEvenVec (s + sec4IOnes) := sec4I_isEvenVec_add_ones hsne
    have h := congrArg Prod.snd (sec4IT_invType hQ fr hse)
    simp only [invType, invSign] at h
    rw [hweight] at h
    have hcongr := congrArg (fun U : Submodule (ZMod 3) V => quadSign (Q.restrict U)) hfix_eq
    rw [← hcongr]
    exact h
  refine ⟨sec4IT fr s, htsq, hcomm, ?_⟩
  interval_cases h : vecWeight s
  · refine ⟨sylowPQMaximal_omegaGroup_six_minus (V := ↥(fixSp (sec4IT fr s)))
      (Q := Q.restrict (fixSp (sec4IT fr s))) hE6
      (nondegenerate_restrict_fixSp hQ htsq) hdimF ?_, ?_⟩
    · have hs := hsignF ⟨0, by norm_num⟩
      rwa [show (7 - 1) / 2 = 3 by norm_num, neg_one_cube] at hs
    · exact sylowPQMaximal_omegaGroup_of_small (V := ↥(commSp (sec4IT fr s)))
        (Q := Q.restrict (commSp (sec4IT fr s)))
        (nondegenerate_restrict_commSp hQ htsq) (Or.inl (by omega))
  · refine ⟨sylowPQMaximal_omegaGroup_five (V := ↥(fixSp (sec4IT fr s)))
      (Q := Q.restrict (fixSp (sec4IT fr s))) hE5
      (nondegenerate_restrict_fixSp hQ htsq) hdimF, ?_⟩
    exact sylowPQMaximal_omegaGroup_of_small (V := ↥(commSp (sec4IT fr s)))
      (Q := Q.restrict (commSp (sec4IT fr s)))
      (nondegenerate_restrict_commSp hQ htsq) (Or.inl (by omega))
  · refine ⟨sylowPQMaximal_omegaGroup_of_small (V := ↥(fixSp (sec4IT fr s)))
      (Q := Q.restrict (fixSp (sec4IT fr s)))
      (nondegenerate_restrict_fixSp hQ htsq) (Or.inr ⟨hdimF, ?_⟩), ?_⟩
    · have hs := hsignF ⟨1, by norm_num⟩
      rwa [show (7 - 3) / 2 = 2 by norm_num, neg_one_sq] at hs
    · exact sylowPQMaximal_omegaGroup_of_small (V := ↥(commSp (sec4IT fr s)))
        (Q := Q.restrict (commSp (sec4IT fr s)))
        (nondegenerate_restrict_commSp hQ htsq) (Or.inl (by omega))
  · refine ⟨sylowPQMaximal_omegaGroup_of_small (V := ↥(fixSp (sec4IT fr s)))
      (Q := Q.restrict (fixSp (sec4IT fr s)))
      (nondegenerate_restrict_fixSp hQ htsq) (Or.inl (by omega)), ?_⟩
    refine sylowPQMaximal_omegaGroup_of_small (V := ↥(commSp (sec4IT fr s)))
      (Q := Q.restrict (commSp (sec4IT fr s)))
      (nondegenerate_restrict_commSp hQ htsq) (Or.inr ⟨hdimC, ?_⟩)
    have hs := hsignC ⟨2, by norm_num⟩
    rwa [show 4 / 2 = 2 by norm_num, neg_one_sq] at hs
  · refine ⟨sylowPQMaximal_omegaGroup_of_small (V := ↥(fixSp (sec4IT fr s)))
      (Q := Q.restrict (fixSp (sec4IT fr s)))
      (nondegenerate_restrict_fixSp hQ htsq) (Or.inl (by omega)), ?_⟩
    exact sylowPQMaximal_omegaGroup_five (V := ↥(commSp (sec4IT fr s)))
      (Q := Q.restrict (commSp (sec4IT fr s))) hE5
      (nondegenerate_restrict_commSp hQ htsq) hdimC
  · refine ⟨sylowPQMaximal_omegaGroup_of_small (V := ↥(fixSp (sec4IT fr s)))
      (Q := Q.restrict (fixSp (sec4IT fr s)))
      (nondegenerate_restrict_fixSp hQ htsq) (Or.inl (by omega)), ?_⟩
    refine sylowPQMaximal_omegaGroup_six_minus (V := ↥(commSp (sec4IT fr s)))
      (Q := Q.restrict (commSp (sec4IT fr s))) hE6
      (nondegenerate_restrict_commSp hQ htsq) hdimC ?_
    have hs := hsignC ⟨3, by norm_num⟩
    rwa [show 6 / 2 = 3 by norm_num, neg_one_cube] at hs

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7
