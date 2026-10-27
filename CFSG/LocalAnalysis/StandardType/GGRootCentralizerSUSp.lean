module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.RankThree.PartOne.KFCL.SpPerm
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.StandardType

namespace RootCentSp

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot OTwoGen
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E)
open scoped MatrixGroups

section Generation

variable {F : Type} [Field F] [CharP F 2]

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras in
theorem top_le_closure_statedSp (m : ℕ) :
    (⊤ : Subgroup (StatedSp m F)) ≤ Subgroup.closure {x | ∃ k : ℕ, x ^ (2 ^ k) = 1} := by
  rw [← (isCTGroupDatum m F).iSup_eq_top]
  refine iSup₂_le fun γ hγ x hx => Subgroup.subset_closure ⟨1, ?_⟩
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hx
  rw [pow_one, pow_two, ← elt_add, CharTwo.add_self_eq_zero, elt_zero]

theorem top_le_closure_sl2 :
    (⊤ : Subgroup SL(2, F)) ≤ Subgroup.closure {x | ∃ k : ℕ, x ^ (2 ^ k) = 1} :=
  top_le_closure_of_surjective (longBlockEquivOne F).symm.toMonoidHom
    (MulEquiv.surjective _) (top_le_closure_statedSp 1)

end Generation

section LongRoot

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

theorem centralizer_siegDiag_le_ggOTwoPrime (p : Fin n) :
    centralizer ({siegDiag F p 1} : Set (StatedSp n F)) ≤
      ggOTwoPrime (centralizer ({siegDiag F p 1} : Set (StatedSp n F))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := p.isLt; omega⟩
  have hC := centralizer_siegDiag_eq_sup (K := F) (p := p)
  calc centralizer ({siegDiag F p 1} : Set (StatedSp (m + 1) F))
      = transvRadical F p ⊔ complSp F p := hC
    _ ≤ _ := by
      refine sup_le (le_ggOTwoPrime_of_isPGroup transvRadical_le_centralizer
        isPGroup_transvRadical) ?_
      have hle : (spEmbed (K := F) p.succAbove Fin.succAbove_right_injective).range ≤
          centralizer ({siegDiag F p 1} : Set (StatedSp (m + 1) F)) := by
        rw [← complSp_eq_range_spEmbed]
        exact complSp_le_centralizer_siegDiag
      rw [complSp_eq_range_spEmbed]
      exact range_le_ggOTwoPrime _ hle (top_le_closure_statedSp m)

end LongRoot

section ShortRoot

variable {K : Type} [Field K] {n : ℕ} {p q : Fin n}

theorem leviHom_mem_suppGroup_offPQ (hpq : p ≠ q) {a b : K} (hb : b ≠ 0)
    (g : centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K)))
    (hA : ∀ x y : Fin n, (x = p ∨ x = q) → (y = p ∨ y = q) →
      mat n K g (Sum.inl x) (Sum.inl y) = (1 : Matrix (Fin n) (Fin n) K) x y)
    (hD : ∀ x y : Fin n, (x = p ∨ x = q) → (y = p ∨ y = q) →
      mat n K g (Sum.inr x) (Sum.inr y) = (1 : Matrix (Fin n) (Fin n) K) x y) :
    leviHom hpq a hb g ∈ suppGroup {t | OffPQ p q t} := by
  intro r t hrt
  rw [mat_leviHom, leviPart_apply]
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  split_ifs with hb'
  · rcases h3 (blk p q r) with h0 | h1 | h2
    · obtain ⟨x, rfl, hx⟩ : ∃ x, r = Sum.inl x ∧ (x = p ∨ x = q) := by
        rcases blk_eq_zero_iff.1 h0 with h' | h' <;> exact ⟨_, h', by simp⟩
      obtain ⟨y, rfl, hy⟩ : ∃ y, t = Sum.inl y ∧ (y = p ∨ y = q) := by
        rcases blk_eq_zero_iff.1 (hb' ▸ h0) with h' | h' <;> exact ⟨_, h', by simp⟩
      rw [hA x y hx hy]
      simp [Matrix.one_apply]
    · obtain ⟨x, rfl, hx⟩ : ∃ x, r = Sum.inr x ∧ (x = p ∨ x = q) := by
        rcases blk_eq_one_iff.1 h1 with h' | h' <;> exact ⟨_, h', by simp⟩
      obtain ⟨y, rfl, hy⟩ : ∃ y, t = Sum.inr y ∧ (y = p ∨ y = q) := by
        rcases blk_eq_one_iff.1 (hb' ▸ h1) with h' | h' <;> exact ⟨_, h', by simp⟩
      rw [hD x y hx hy]
      simp [Matrix.one_apply]
    · exact absurd ⟨blk_eq_two_iff.1 h2, blk_eq_two_iff.1 (hb' ▸ h2)⟩ hrt
  · rw [Matrix.one_apply_ne (by rintro rfl; exact hb' rfl)]

theorem suppGroup_offPQ_le_centralizer (a b : K) :
    suppGroup {t | OffPQ p q t} ≤
      centralizer ({twoCentralElt n p q a b} : Set (StatedSp n K)) := by
  intro g hg
  have hmem : ∀ x, x = p ∨ x = q →
      (Sum.inl x : Fin n ⊕ Fin n) ∈ {t | OffPQ p q t}ᶜ ∧
        (Sum.inr x : Fin n ⊕ Fin n) ∈ {t | OffPQ p q t}ᶜ := by
    rintro x (rfl | rfl)
    · exact ⟨fun h => h.1 (inl_mem_coords _), fun h => h.1 (inr_mem_coords _)⟩
    · exact ⟨fun h => h.2 (inl_mem_coords _), fun h => h.2 (inr_mem_coords _)⟩
  have hz : twoCentralElt n p q a b ∈ suppGroup {t | OffPQ p q t}ᶜ := by
    intro r t hrt
    rw [mat_twoCentralElt_eq_add]
    simp only [Matrix.add_apply, Matrix.single_apply]
    have h1 : ¬(Sum.inl p = r ∧ Sum.inr p = t) := by
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨(hmem p (Or.inl rfl)).1, (hmem p (Or.inl rfl)).2⟩
    have h2 : ¬(Sum.inl p = r ∧ Sum.inr q = t) := by
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨(hmem p (Or.inl rfl)).1, (hmem q (Or.inr rfl)).2⟩
    have h3 : ¬(Sum.inl q = r ∧ Sum.inr p = t) := by
      rintro ⟨rfl, rfl⟩
      exact hrt ⟨(hmem q (Or.inr rfl)).1, (hmem p (Or.inl rfl)).2⟩
    rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h2),
      ite_eq_right_iff.mpr (fun h => absurd h h3), add_zero, add_zero, add_zero]
  rw [mem_centralizer_singleton_iff]
  exact (commute_suppGroup_compl hg hz).eq

theorem centralizer_a2_le_of_ne [CharP K 2] (hpq : p ≠ q) :
    centralizer ({twoCentralElt n p q (0 : K) 1} : Set (StatedSp n K)) ≤
      wRadical K p q ⊔ ((shortBlock K hpq).range ⊔ suppGroup {t | OffPQ p q t}) := by
  set C := centralizer ({twoCentralElt n p q (0 : K) 1} : Set (StatedSp n K))
  intro g hg
  set A := a2Coord hpq (one_ne_zero (α := K)) ⟨g, hg⟩
  have hsC : shortBlock K hpq A ∈ C := shortBlock_mem_centralizer hpq A 1
  set s : C := ⟨shortBlock K hpq A, hsC⟩
  have hsA : a2Coord hpq (one_ne_zero (α := K)) s = A := Subtype.ext (wBlock_shortBlock hpq A)
  set g' : C := s⁻¹ * ⟨g, hg⟩
  have hg'A : a2Coord hpq (one_ne_zero (α := K)) g' = 1 := by
    rw [map_mul, map_inv, hsA, inv_mul_cancel]
  have hW : wBlock p q (mat n K g') = 1 := congrArg Subtype.val hg'A
  have hcomm := (commute_twoCentralElt_iff (0 : K) 1).1 (mem_centralizer_singleton_iff.1 g'.2)
  obtain ⟨-, d1, d2, d3, d4⟩ := a2_blocks hpq one_ne_zero hcomm
  have hW' : ∀ i j : Fin 2,
      wBlock p q (mat n K g') i j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by rw [hW]
  have a11 := hW' 0 0
  have a12 := hW' 0 1
  have a21 := hW' 1 0
  have a22 := hW' 1 1
  simp only [wBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.one_apply_eq] at a11 a12 a21 a22
  simp only [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at a12 a21
  have hA : ∀ x y : Fin n, (x = p ∨ x = q) → (y = p ∨ y = q) →
      mat n K g' (Sum.inl x) (Sum.inl y) = (1 : Matrix (Fin n) (Fin n) K) x y := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp [a11, a12, a21, a22, hpq, Ne.symm hpq]
  have hD : ∀ x y : Fin n, (x = p ∨ x = q) → (y = p ∨ y = q) →
      mat n K g' (Sum.inr x) (Sum.inr y) = (1 : Matrix (Fin n) (Fin n) K) x y := by
    rintro x y (rfl | rfl) (rfl | rfl) <;>
      simp [d1, d2, d3, d4, a11, a12, a21, a22, hpq, Ne.symm hpq]
  have hm := leviHom_mem_suppGroup_offPQ hpq (one_ne_zero (α := K)) g' hA hD
  set m' : C := ⟨leviHom hpq 0 one_ne_zero g', leviHom_mem_centralizer hpq one_ne_zero g'⟩
  have hq : ((g' * m'⁻¹ : C) : StatedSp n K) ∈ wRadical K p q := by
    rw [mem_wRadical_iff_leviHom_eq_one hpq one_ne_zero, map_mul, map_inv, leviHom_leviHom,
      mul_inv_cancel]
  have e1 : ((g' * m'⁻¹ : C) : StatedSp n K) * leviHom hpq 0 one_ne_zero g' =
      (g' : StatedSp n K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    change (g' : StatedSp n K) * (leviHom hpq 0 one_ne_zero g')⁻¹ *
      leviHom hpq 0 one_ne_zero g' = g'
    group
  have e2 : (g' : StatedSp n K) = (shortBlock K hpq A)⁻¹ * g := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  have e : g = shortBlock K hpq A *
      (((g' * m'⁻¹ : C) : StatedSp n K) * leviHom hpq 0 one_ne_zero g') := by
    rw [e1, e2]
    group
  rw [e]
  refine Subgroup.mul_mem _ (mem_sup_right (mem_sup_left ⟨A, rfl⟩)) ?_
  exact Subgroup.mul_mem _ (mem_sup_left hq) (mem_sup_right (mem_sup_right hm))

theorem exists_planes_offPQ {k : ℕ} {p q : Fin (k + 2)} (hpq : p ≠ q) :
    ∃ σ : Fin k → Fin (k + 2), Function.Injective σ ∧
      Set.range (Sum.map σ σ) = {t | OffPQ p q t} := by
  obtain ⟨q', hq'⟩ := Fin.exists_succAbove_eq (Ne.symm hpq)
  have hinj : Function.Injective (p.succAbove ∘ q'.succAbove) :=
    Fin.succAbove_right_injective.comp Fin.succAbove_right_injective
  refine ⟨p.succAbove ∘ q'.succAbove, hinj, ?_⟩
  have hrange : ∀ x : Fin (k + 2), x ∈ Set.range (p.succAbove ∘ q'.succAbove) ↔
      (x ≠ p ∧ x ≠ q) := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨Fin.succAbove_ne _ _, fun h => ?_⟩
      rw [← hq'] at h
      exact Fin.succAbove_ne q' u (Fin.succAbove_right_injective h)
    · rintro ⟨hxp, hxq⟩
      obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hxp
      have hz : z ≠ q' := fun h => hxq (by rw [h, hq'])
      obtain ⟨u, rfl⟩ := Fin.exists_succAbove_eq hz
      exact ⟨u, rfl⟩
  ext t
  simp only [Set.mem_ofPred_eq, OffPQ, mem_coords]
  rcases t with x | x
  · have h := hrange x
    constructor
    · rintro ⟨u, hu⟩
      rcases u with u | u
      · simp only [Sum.map_inl, Sum.inl.injEq] at hu
        subst hu
        have h' := h.1 ⟨u, rfl⟩
        simp only [Function.comp_apply] at h'
        simp [h'.1, h'.2]
      · simp at hu
    · intro hx
      have hx' : x ≠ p ∧ x ≠ q := ⟨fun e => hx.1 (Or.inl (by rw [e])),
        fun e => hx.2 (Or.inl (by rw [e]))⟩
      obtain ⟨u, hu⟩ := h.2 hx'
      exact ⟨Sum.inl u, by rw [Sum.map_inl, ← hu]⟩
  · have h := hrange x
    constructor
    · rintro ⟨u, hu⟩
      rcases u with u | u
      · simp at hu
      · simp only [Sum.map_inr, Sum.inr.injEq] at hu
        subst hu
        have h' := h.1 ⟨u, rfl⟩
        simp only [Function.comp_apply] at h'
        simp [h'.1, h'.2]
    · intro hx
      have hx' : x ≠ p ∧ x ≠ q := ⟨fun e => hx.1 (Or.inr (by rw [e])),
        fun e => hx.2 (Or.inr (by rw [e]))⟩
      obtain ⟨u, hu⟩ := h.2 hx'
      exact ⟨Sum.inr u, by rw [Sum.map_inr, ← hu]⟩

theorem centralizer_twoCentralElt_le_ggOTwoPrime [CharP K 2] (hpq : p ≠ q) :
    centralizer ({twoCentralElt n p q (0 : K) 1} : Set (StatedSp n K)) ≤
      ggOTwoPrime (centralizer ({twoCentralElt n p q (0 : K) 1} : Set (StatedSp n K))) := by
  refine (centralizer_a2_le_of_ne hpq).trans (sup_le ?_ (sup_le ?_ ?_))
  · exact le_ggOTwoPrime_of_isPGroup (wRadical_le_centralizer_twoCentralElt 0 1)
      (isPGroup_wRadical hpq)
  · refine range_le_ggOTwoPrime _ ?_ top_le_closure_sl2
    rintro _ ⟨A, rfl⟩
    exact shortBlock_mem_centralizer hpq A 1
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by
      have h1 := p.isLt
      have h2 := q.isLt
      have h3 : (p : ℕ) ≠ q := fun h => hpq (Fin.ext h)
      omega⟩
    obtain ⟨σ, hσ, hrange⟩ := exists_planes_offPQ hpq
    rw [← hrange, ← range_spEmbed hσ]
    refine range_le_ggOTwoPrime _ ?_ (top_le_closure_statedSp k)
    rw [range_spEmbed hσ, hrange]
    exact suppGroup_offPQ_le_centralizer 0 1

end ShortRoot

section RootElements

variable {F : Type} [Field F] {n : ℕ}

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  TauCeti.GLSymplecticFin
open CFSG.RankThree.PartOne.KFCL.Sp (Hp permSp cj mat_cj_apply)

theorem centralizer_elt_eq (r : RootSubgroupIndex n) {c : F} (hc : c ≠ 0) :
    centralizer ({elt r c} : Set (StatedSp n F)) =
      centralizer ({elt r 1} : Set (StatedSp n F)) := by
  have key : ∀ d : F, d ≠ 0 → ∀ g : StatedSp n F,
      g * elt r d = elt r d * g ↔ mat n F g * E F r = E F r * mat n F g := by
    intro d hd g
    rw [← mat_injective.eq_iff, map_mul, map_mul, mat_elt, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, add_right_inj, Matrix.mul_smul, Matrix.smul_mul]
    exact (smul_right_injective _ hd).eq_iff
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, key c hc, key 1 one_ne_zero]

theorem swap_plane_mem_Hp (k : Fin n) : Equiv.swap (Sum.inl k) (Sum.inr k) ∈ Hp n := by
  intro a
  by_cases h1 : a = Sum.inl k
  · subst h1
    simp [par]
  · by_cases h2 : a = Sum.inr k
    · subst h2
      simp [par]
    · have h3 : par a ≠ Sum.inl k := by
        intro h
        apply h2
        rw [← par_par a, h]
        rfl
      have h4 : par a ≠ Sum.inr k := by
        intro h
        apply h1
        rw [← par_par a, h]
        rfl
      rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem cj_eq_conj [CharP F 2] {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n)
    (x : StatedSp n F) : cj hτ x = (permSp τ hτ)⁻¹ * x * ((permSp τ hτ)⁻¹)⁻¹ := by
  rw [inv_inv]
  rfl

theorem single_apply_swap (x y u v a b : Fin n ⊕ Fin n) (c : F) :
    single u v c (Equiv.swap x y a) (Equiv.swap x y b) =
      single (Equiv.swap x y u) (Equiv.swap x y v) c a b := by
  simp only [Matrix.single_apply, Equiv.swap_apply_eq_iff]

theorem one_apply_swap (x y a b : Fin n ⊕ Fin n) :
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Equiv.swap x y a) (Equiv.swap x y b) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a b := by
  simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]

theorem elt_positiveLong_one (i : Fin n) : elt (.positiveLong i) (1 : F) = siegDiag F i 1 := by
  apply mat_injective
  rw [mat_elt, mat_siegDiag_one, one_smul]
  rfl

theorem elt_positiveSum_one {i j : Fin n} (hij : i < j) :
    elt (.positiveSum i j hij) (1 : F) = twoCentralElt n i j 0 1 := by
  apply mat_injective
  rw [mat_elt, mat_twoCentralElt_eq_add, one_smul, Matrix.single_zero, add_zero, add_assoc]
  rfl

variable [CharP F 2]

theorem elt_negativeLong_one (i : Fin n) :
    elt (.negativeLong i) (1 : F) = cj (swap_plane_mem_Hp i) (siegDiag F i 1) := by
  apply mat_injective
  ext a b
  rw [mat_cj_apply, mat_elt, mat_siegDiag_one, one_smul, Matrix.add_apply, Matrix.add_apply,
    one_apply_swap, single_apply_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rfl

theorem elt_difference_one {i j : Fin n} (hij : i ≠ j) :
    elt (.difference i j hij) (1 : F) =
      cj (swap_plane_mem_Hp j) (twoCentralElt n i j (0 : F) 1) := by
  apply mat_injective
  ext a b
  have hi1 : Equiv.swap (Sum.inl j) (Sum.inr j) (Sum.inl i : Fin n ⊕ Fin n) = Sum.inl i :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hij (Sum.inl_injective h)) Sum.inl_ne_inr
  have hi2 : Equiv.swap (Sum.inl j) (Sum.inr j) (Sum.inr i : Fin n ⊕ Fin n) = Sum.inr i :=
    Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => hij (Sum.inr_injective h))
  rw [mat_cj_apply, mat_elt, mat_twoCentralElt_eq_add, one_smul, Matrix.single_zero, add_zero]
  simp only [Matrix.add_apply, one_apply_swap, single_apply_swap, hi1, hi2,
    Equiv.swap_apply_left, Equiv.swap_apply_right, E, Matrix.sub_apply, CharTwo.sub_eq_add,
    add_assoc]

theorem elt_negativeSum_one {i j : Fin n} (hij : i < j) :
    elt (.negativeSum i j hij) (1 : F) =
      cj (swap_plane_mem_Hp i) (elt (.difference i j hij.ne) (1 : F)) := by
  apply mat_injective
  ext a b
  have hj1 : Equiv.swap (Sum.inl i) (Sum.inr i) (Sum.inl j : Fin n ⊕ Fin n) = Sum.inl j :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hij.ne (Sum.inl_injective h).symm) Sum.inl_ne_inr
  have hj2 : Equiv.swap (Sum.inl i) (Sum.inr i) (Sum.inr j : Fin n ⊕ Fin n) = Sum.inr j :=
    Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => hij.ne (Sum.inr_injective h).symm)
  rw [mat_cj_apply, mat_elt, mat_elt, one_smul, one_smul]
  simp only [Matrix.add_apply, one_apply_swap, E, Matrix.sub_apply, single_apply_swap, hj1, hj2,
    Equiv.swap_apply_left, Equiv.swap_apply_right, CharTwo.sub_eq_add]

theorem centralizer_elt_one_le_ggOTwoPrime (r : RootSubgroupIndex n) :
    centralizer ({elt r (1 : F)} : Set (StatedSp n F)) ≤
      ggOTwoPrime (centralizer ({elt r (1 : F)} : Set (StatedSp n F))) := by
  have hdiff : ∀ (i j : Fin n) (hij : i ≠ j),
      centralizer ({elt (.difference i j hij) (1 : F)} : Set (StatedSp n F)) ≤
        ggOTwoPrime (centralizer ({elt (.difference i j hij) (1 : F)} :
          Set (StatedSp n F))) := by
    intro i j hij
    rw [elt_difference_one hij, cj_eq_conj]
    exact centralizer_conj_le_ggOTwoPrime (centralizer_twoCentralElt_le_ggOTwoPrime hij) _
  cases r with
  | positiveLong i =>
    rw [elt_positiveLong_one]
    exact centralizer_siegDiag_le_ggOTwoPrime i
  | negativeLong i =>
    rw [elt_negativeLong_one, cj_eq_conj]
    exact centralizer_conj_le_ggOTwoPrime (centralizer_siegDiag_le_ggOTwoPrime i) _
  | difference i j hij => exact hdiff i j hij
  | positiveSum i j hij =>
    rw [elt_positiveSum_one]
    exact centralizer_twoCentralElt_le_ggOTwoPrime hij.ne
  | negativeSum i j hij =>
    rw [elt_negativeSum_one, cj_eq_conj]
    exact centralizer_conj_le_ggOTwoPrime (hdiff i j hij.ne) _

theorem centralizer_le_ggOTwoPrime_of_mem_rootGroup {γ : Fin n → ℤ}
    (hγ : γ ∈ (rootDatum n F).roots) {x : StatedSp n F} (hx : x ∈ (rootDatum n F).rootGroup γ)
    (hx1 : x ≠ 1) :
    centralizer ({x} : Set (StatedSp n F)) ≤ ggOTwoPrime (centralizer ({x} : Set (StatedSp n F))) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (elt_zero r)
  rw [centralizer_elt_eq r hc]
  exact centralizer_elt_one_le_ggOTwoPrime r

end RootElements

end RootCentSp

end CFSG.StandardType
