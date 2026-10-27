module

public import CFSG.LocalAnalysis.StandardType.PhanEResSLPath
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {M : ChevModel2 D n H Fld} {m : ℕ}

lemma hmbSL_pathRoot_castSucc_succ {r m : ℕ} (e : Fin m → Fin r) (k : Fin m) :
    pathRoot e k.castSucc k.succ = Pi.single (e k) 1 := by
  unfold pathRoot
  rw [if_pos (by simp [Fin.lt_def])]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j hj
    have hne : ¬ (k.val ≤ j.val ∧ j.val < k.val + 1) := by
      rintro ⟨h1, h2⟩
      exact hj (Fin.ext (by omega))
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [if_neg hne]

lemma hmbSL_pathRoot_succ_castSucc {r m : ℕ} (e : Fin m → Fin r) (k : Fin m) :
    pathRoot e k.succ k.castSucc = -Pi.single (e k) 1 := by
  unfold pathRoot
  rw [if_neg (by simp [Fin.lt_def])]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j hj
    have hne : ¬ (k.val ≤ j.val ∧ j.val < k.val + 1) := by
      rintro ⟨h1, h2⟩
      exact hj (Fin.ext (by omega))
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [if_neg hne]

lemma hmbSL_castSucc_ne_succ {m : ℕ} (k : Fin m) : k.castSucc ≠ k.succ := by
  intro h
  exact absurd (congrArg Fin.val h) (by simp)

lemma hmbSL_pathRoot_self {r m : ℕ} (e : Fin m → Fin r) (p : Fin (m + 1)) :
    pathRoot e p p = 0 := by
  unfold pathRoot
  rw [if_neg (lt_irrefl p), neg_eq_zero]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_neg]
  omega

private def hmbSL_pathRoot_S {m : ℕ} (p q : Fin (m + 1)) : Finset (Fin m) :=
  Finset.univ.filter fun k => p.val ≤ k.val ∧ k.val < q.val

private lemma hmbSL_pathRoot_eq_sum {r m : ℕ} (e : Fin m → Fin r) {p q : Fin (m + 1)}
    (h : p < q) :
    pathRoot e p q = ∑ k ∈ hmbSL_pathRoot_S p q, Pi.single (e k) 1 := by
  unfold pathRoot hmbSL_pathRoot_S
  rw [if_pos h, ← Finset.sum_filter]

private lemma hmbSL_pathRoot_S_union {m : ℕ} {p s q : Fin (m + 1)} (hps : p ≤ s) (hsq : s ≤ q) :
    hmbSL_pathRoot_S p q = hmbSL_pathRoot_S p s ∪ hmbSL_pathRoot_S s q := by
  have h1 : p.val ≤ s.val := hps
  have h2 : s.val ≤ q.val := hsq
  ext k
  simp only [hmbSL_pathRoot_S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  omega

private lemma hmbSL_pathRoot_S_disjoint {m : ℕ} {p s q : Fin (m + 1)} :
    Disjoint (hmbSL_pathRoot_S p s) (hmbSL_pathRoot_S s q) := by
  rw [Finset.disjoint_left]
  intro k h1 h2
  simp only [hmbSL_pathRoot_S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

lemma hmbSL_pathRoot_split {r m : ℕ} (e : Fin m → Fin r) {p s q : Fin (m + 1)}
    (hps : p ≤ s) (hsq : s ≤ q) :
    pathRoot e p q = pathRoot e p s + pathRoot e s q := by
  rcases lt_or_eq_of_le hps with hps' | rfl
  · rcases lt_or_eq_of_le hsq with hsq' | rfl
    · rw [hmbSL_pathRoot_eq_sum e (lt_trans hps' hsq'),
        hmbSL_pathRoot_eq_sum e hps', hmbSL_pathRoot_eq_sum e hsq',
        hmbSL_pathRoot_S_union (le_of_lt hps') (le_of_lt hsq'),
        Finset.sum_union hmbSL_pathRoot_S_disjoint]
    · rw [hmbSL_pathRoot_self, add_zero]
  · rw [hmbSL_pathRoot_self, zero_add]

private lemma hmbSL_pathRoot_coroot {r m : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (e : Fin m → Fin r)
    (hcart : ∀ k l : Fin m, A (e k) (e l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0)
    (k : Fin m) {q : Fin (m + 1)} (hk : k.succ < q) :
    (∑ t, A (e k) t * (pathRoot e k.succ q) t) = -1 := by
  have hk' : k.val + 1 < q.val := by
    rw [Fin.lt_def] at hk
    simpa only [Fin.val_succ] using hk
  let j0 : Fin m := ⟨k.val + 1, by have := q.isLt; omega⟩
  have hj0 : j0.val = k.val + 1 := rfl
  have hpath : pathRoot e k.succ q
      = ∑ j : Fin m, (if k.val + 1 ≤ j.val ∧ j.val < q.val then Pi.single (e j) 1 else 0) := by
    unfold pathRoot
    rw [if_pos hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_succ]
  rw [← coroot_apply, hpath, map_sum]
  have hsum : (∑ x : Fin m, coroot A (e k)
        (if k.val + 1 ≤ x.val ∧ x.val < q.val then Pi.single (e x) 1 else 0))
      = coroot A (e k)
        (if k.val + 1 ≤ j0.val ∧ j0.val < q.val then Pi.single (e j0) 1 else 0) := by
    refine Fintype.sum_eq_single j0 ?_
    intro x hx
    by_cases hc : k.val + 1 ≤ x.val ∧ x.val < q.val
    · rw [if_pos hc, coroot_single, hcart k x]
      rw [if_neg (by intro h; have := congrArg Fin.val h; omega)]
      rw [if_neg]
      rintro (h1 | h1)
      · exact hx (Fin.ext (by rw [hj0]; omega))
      · omega
    · rw [if_neg hc, map_zero]
  rw [hsum]
  rw [if_pos (by rw [hj0]; omega), coroot_single, hcart k j0]
  rw [if_neg (by intro h; have := congrArg Fin.val h; rw [hj0] at this; omega)]
  rw [if_pos (Or.inl hj0)]

private lemma hmbSL_pathRoot_reflect {K : Type} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]
    {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m) {k : Fin m} {q : Fin (m + 1)}
    (hk : k.succ < q) :
    weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple (L.e k))
      (pathRoot L.e k.succ q) = pathRoot L.e k.castSucc q := by
  have hc : (∑ t, D.cartan (L.e k) t * (pathRoot L.e k.succ q) t) = -1 :=
    hmbSL_pathRoot_coroot D.cartan L.e L.cartan k hk
  have hdecomp : pathRoot L.e k.castSucc q = Pi.single (L.e k) 1 + pathRoot L.e k.succ q := by
    rw [hmbSL_pathRoot_split L.e (le_of_lt Fin.castSucc_lt_succ) (le_of_lt hk),
      hmbSL_pathRoot_castSucc_succ]
  rw [weylAction_simple, reflection_apply, hc, neg_smul, one_smul, sub_neg_eq_add, hdecomp]
  exact add_comm _ _

theorem pathRoot_mem_roots (L : SLPath M m) {p q : Fin (m + 1)} (hpq : p ≠ q) :
    pathRoot L.e p q ∈ D.roots := by
  have hCT := isCTRootSystem D.isFiniteType D.divisible
  have key : ∀ d : ℕ, ∀ p q : Fin (m + 1), p < q → q.val - p.val = d →
      pathRoot L.e p q ∈ D.roots := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p q hpq hd
      by_cases hadj : q.val = p.val + 1
      · have hpv : p.val < m := by have := q.isLt; omega
        have hks : (p.castLT hpv).succ = q := Fin.ext (by
          have hv : (p.castLT hpv).succ.val = p.val + 1 := rfl
          rw [hv]; omega)
        have hmem : pathRoot L.e p q = Pi.single (L.e (p.castLT hpv)) 1 := by
          rw [← hks]
          exact hmbSL_pathRoot_castSucc_succ L.e (p.castLT hpv)
        rw [hmem]
        exact hCT.single_mem (L.e (p.castLT hpv))
      · have hp1 : p.val + 1 < q.val := by have := q.isLt; omega
        have hpv : p.val < m := by have := q.isLt; omega
        have hksq : (p.castLT hpv).succ < q := by
          rw [Fin.lt_def]
          show p.val + 1 < q.val
          exact hp1
        have hstep := hmbSL_pathRoot_reflect L (k := p.castLT hpv) hksq
        have hlt : q.val - (p.castLT hpv).succ.val < d := by
          have hv : (p.castLT hpv).succ.val = p.val + 1 := rfl
          rw [hv]
          omega
        have hih := ih (q.val - (p.castLT hpv).succ.val) hlt (p.castLT hpv).succ q hksq rfl
        have hpc : (p.castLT hpv).castSucc = p := Fin.ext rfl
        rw [← hpc, ← hstep]
        exact hCT.smul_mem _ _ hih
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact key _ p q hlt rfl
  · have hmem : pathRoot L.e p q = -pathRoot L.e q p := by
      unfold pathRoot
      rw [if_neg (not_lt.mpr hgt.le), if_pos hgt]
    rw [hmem]
    exact OfCartan.neg_mem_roots (hA := D.isFiniteType) (D := D.divisible) (key _ q p hgt rfl)

private lemma hmbSL_x_zero {M : ChevModel2 D n H Fld} {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : M.x γ 0 = 1 := by
  have h := M.x_add γ hγ 0 0
  rw [zero_add] at h
  exact (mul_left_cancel (a := M.x γ 0) (b := 1) (c := M.x γ 0) (by simpa using h)).symm

private lemma hmbSL_x_neg_one {M : ChevModel2 D n H Fld} {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : M.x γ (-1) = (M.x γ 1)⁻¹ := by
  have h := M.x_add γ hγ (-1) 1
  rw [neg_add_cancel, hmbSL_x_zero hγ] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private lemma hmbSL_pathRoot_nonneg {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    {p q : Fin (m + 1)} (hpq : p < q) : 0 ≤ pathRoot L.e p q := by
  have hsum : pathRoot L.e p q =
      ∑ k : Fin m, if p.val ≤ k.val ∧ k.val < q.val then Pi.single (L.e k) (1 : ℤ) else 0 := by
    unfold pathRoot
    rw [if_pos hpq]
  rw [hsum]
  intro r
  simp only [Finset.sum_apply, Pi.zero_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs with hk
  · by_cases hr : r = L.e k <;> simp [Pi.single, Function.update, hr]
  · exact le_refl 0

private lemma hmbSL_ε_diag2n_adj_gen {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    {i j : Fin (m + 1)} (hi : i.val < m) (hij : i < j) (hj : j.val = i.val + 1)
    (a : Fld) (ha : a ≠ 0) :
    L.ε (SpecialLinearGroup.diag2n hij.ne a ha) = M.hh (L.e ⟨i.val, hi⟩) (Units.mk0 a ha) := by
  let k : Fin m := ⟨i.val, hi⟩
  have hik : i = (k.castSucc : Fin (m + 1)) := Fin.ext rfl
  have hik' : j = (k.succ : Fin (m + 1)) := by
    apply Fin.ext
    show j.val = i.val + 1
    exact hj
  have hroot1 : pathRoot L.e i j = Pi.single (L.e k) 1 := by
    rw [hik, hik']
    exact hmbSL_pathRoot_castSucc_succ L.e k
  have hroot2 : pathRoot L.e j i = -Pi.single (L.e k) 1 := by
    rw [hik, hik']
    exact hmbSL_pathRoot_succ_castSucc L.e k
  have hpq : i ≠ j := hij.ne
  rw [SpecialLinearGroup.diag2n_decompose hpq a ha]
  rw [map_mul, map_mul, map_mul, map_mul, map_mul]
  simp only [← tv_of_ne hpq, ← tv_of_ne hpq.symm]
  rw [L.tv_eq i j hpq a,
    L.tv_eq j i hpq.symm (-a⁻¹),
    L.tv_eq i j hpq (-1),
    L.tv_eq j i hpq.symm (1 : Fld),
    hroot1, hroot2]
  have hpos : Pi.single (L.e k) (1 : ℤ) ∈ D.roots := by
    rw [← hmbSL_pathRoot_castSucc_succ L.e k]
    exact pathRoot_mem_roots L (hmbSL_castSucc_ne_succ k)
  have hneg : -Pi.single (L.e k) (1 : ℤ) ∈ D.roots := by
    rw [← hmbSL_pathRoot_succ_castSucc L.e k]
    exact pathRoot_mem_roots L (hmbSL_castSucc_ne_succ k).symm
  have hx1 := hmbSL_x_neg_one (M := M) hpos
  have hx2 := hmbSL_x_neg_one (M := M) hneg
  have hx2' : M.x (-Pi.single (L.e k) 1) 1 =
      (M.x (-Pi.single (L.e k) 1) (-1))⁻¹ := by rw [hx2, inv_inv]
  rw [hx2', hx1]
  rw [M.hh_def (L.e k) (Units.mk0 a ha), M.nm_def (L.e k)]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  group

private lemma hmbSL_diag2n_swap {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j)
    {a : Fld} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha =
      SpecialLinearGroup.diag2n hij.symm a⁻¹ (inv_ne_zero ha) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe]
  congr 1
  funext r
  by_cases h1 : r = i
  · subst h1
    rw [if_pos rfl, if_neg hij, if_pos rfl, inv_inv]
  · by_cases h2 : r = j
    · subst h2
      rw [if_neg h1, if_pos rfl, if_pos rfl]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

private lemma hmbSL_diag2n_mul_mid {m : ℕ} {i l j : Fin (m + 1)}
    (hil : i ≠ l) (hlj : l ≠ j) (hij : i ≠ j) {a : Fld} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hil a ha * SpecialLinearGroup.diag2n hlj a ha =
      SpecialLinearGroup.diag2n hij a ha := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.diag2n_coe,
    SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  by_cases h1 : r = i
  · subst h1
    simp only [if_neg hil, if_neg hij, mul_one]
  · by_cases h2 : r = l
    · subst h2
      simp only [if_neg h1, if_neg hlj]
      exact inv_mul_cancel₀ ha
    · by_cases h3 : r = j
      · subst h3
        simp only [if_neg h1, if_neg h2, one_mul]
      · simp only [if_neg h1, if_neg h2, if_neg h3, mul_one]

private lemma hmbSL_ε_diag2n_mem_iSup {M : ChevModel2 D n H Fld} {m : ℕ}
    (L : SLPath M m) {i j : Fin (m + 1)} (hij : i < j) {a : Fld} (ha : a ≠ 0) :
    L.ε (SpecialLinearGroup.diag2n hij.ne a ha) ∈ ⨆ k, H k := by
  have Hmain : ∀ d : ℕ, ∀ (i j : Fin (m + 1)) (hij : i < j), j.val - i.val = d →
      L.ε (SpecialLinearGroup.diag2n hij.ne a ha) ∈ ⨆ k, H k := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hij hd
      by_cases hadj : j.val = i.val + 1
      · have hi : i.val < m := by have := j.isLt; omega
        have hmem := hmbSL_ε_diag2n_adj_gen L hi hij hadj a ha
        have hH : M.hh (L.e ⟨i.val, hi⟩) (Units.mk0 a ha) ∈ ⨆ k, H k := by
          refine Subgroup.mem_iSup_of_mem (L.e ⟨i.val, hi⟩) ?_
          rw [← M.hh_range (L.e ⟨i.val, hi⟩)]
          exact MonoidHom.mem_range.mpr ⟨Units.mk0 a ha, rfl⟩
        rw [hmem]
        exact hH
      · have hi : i.val < m := by have := j.isLt; omega
        let i' : Fin (m + 1) := ⟨i.val + 1, by omega⟩
        have hii' : i < i' := by
          rw [Fin.lt_def]; show i.val < i.val + 1; omega
        have hi'j : i' < j := by
          rw [Fin.lt_def]; show i.val + 1 < j.val
          have hijv : i.val < j.val := hij
          omega
        have hmem_mid : L.ε (SpecialLinearGroup.diag2n hi'j.ne a ha) ∈ ⨆ k, H k :=
          ih (j.val - i'.val) (by omega) i' j hi'j rfl
        have hmem_first : L.ε (SpecialLinearGroup.diag2n hii'.ne a ha) ∈ ⨆ k, H k := by
          have hmem := hmbSL_ε_diag2n_adj_gen L hi hii' rfl a ha
          have hH : M.hh (L.e ⟨i.val, hi⟩) (Units.mk0 a ha) ∈ ⨆ k, H k := by
            refine Subgroup.mem_iSup_of_mem (L.e ⟨i.val, hi⟩) ?_
            rw [← M.hh_range (L.e ⟨i.val, hi⟩)]
            exact MonoidHom.mem_range.mpr ⟨Units.mk0 a ha, rfl⟩
          rw [hmem]
          exact hH
        have hmul : L.ε (SpecialLinearGroup.diag2n hii'.ne a ha *
            SpecialLinearGroup.diag2n hi'j.ne a ha) ∈ ⨆ k, H k := by
          rw [map_mul]
          exact Subgroup.mul_mem _ hmem_first hmem_mid
        rw [hmbSL_diag2n_mul_mid hii'.ne hi'j.ne hij.ne ha] at hmul
        exact hmul
  exact Hmain _ i j hij rfl

private lemma hmbSL_ε_diag_mem_iSup {M : ChevModel2 D n H Fld} {m : ℕ}
    (L : SLPath M m) (Dg : Fin (m + 1) → Fld) (hDg : (Matrix.diagonal Dg).det = 1) :
    L.ε (⟨Matrix.diagonal Dg, hDg⟩ : SpecialLinearGroup (Fin (m + 1)) Fld) ∈ ⨆ k, H k := by
  rw [SpecialLinearGroup.diag_eq_diag2n_prod (0 : Fin (m + 1)) Dg hDg]
  rw [Finset.map_noncommProd]
  refine Subgroup.noncommProd_mem (K := ⨆ k, H k) _ ?_
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [dite_eq_left hi]
  have hpos : (0 : Fin (m + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
  have hne : Dg i ≠ 0 := SpecialLinearGroup.diagonal_neZero Dg hDg i
  rw [hmbSL_diag2n_swap hi hne]
  exact hmbSL_ε_diag2n_mem_iSup L hpos (inv_ne_zero hne)

private theorem hmbSL_ε_rootElt_mem_posUnipotent {M : ChevModel2 D n H Fld} {m : ℕ}
    (L : SLPath M m) {i j : Fin (m + 1)} (hij : i < j) (a : Fld) :
    L.ε (LinearCover.rootElt i j a) ∈ posUnipotent D := by
  rw [LinearCover.rootElt_of_ne hij.ne, ← tv_of_ne hij.ne]
  rw [L.tv_eq i j hij.ne a]
  exact rootGroup_le_posUnipotent (pathRoot_mem_roots L hij.ne)
    (ht_pos_of_nonneg (pathRoot_mem_roots L hij.ne) (hmbSL_pathRoot_nonneg L hij))
    ((M.x_mem _ (pathRoot_mem_roots L hij.ne) _).mpr ⟨a, rfl⟩)

private theorem hmbSL_ε_unitriangular_mem_posUnipotent {M : ChevModel2 D n H Fld} {m : ℕ}
    (L : SLPath M m) {U : SpecialLinearGroup (Fin (m + 1)) Fld}
    (hU : U ∈ LinearFlag.unitriangular (m + 1) Fld) : L.ε U ∈ posUnipotent D := by
  have hX : {g | ∃ i j : Fin (m + 1), ∃ a : Fld, i < j ∧ LinearCover.rootElt i j a = g} ⊆
      (posUnipotent D).comap L.ε := by
    rintro g ⟨i, j, a, hij, rfl⟩
    exact (Subgroup.mem_comap).mpr (hmbSL_ε_rootElt_mem_posUnipotent L hij a)
  have hclosure := (Subgroup.closure_le ((posUnipotent D).comap L.ε)).mpr hX
  exact hclosure (LinearCover.unitriangular_le_closure_rootElt hU)

theorem ε_mem_borel (L : SLPath M m) {A : SpecialLinearGroup (Fin (m + 1)) Fld}
    (hA : A ∈ LinearFlag.upperTriangular (m + 1) Fld) : L.ε A ∈ borel D H := by
  classical
  let Dg : Fin (m + 1) → Fld := fun i => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) i i
  have hprod : (∏ i : Fin (m + 1), Dg i) = 1 := by
    rw [← Matrix.det_of_isUpperTriangular (fun i j hij => hA i j hij), A.2]
  have hDg : (Matrix.diagonal Dg).det = 1 := by
    rw [Matrix.det_diagonal, hprod]
  have hDg_ne : ∀ i, Dg i ≠ 0 := SpecialLinearGroup.diagonal_neZero Dg hDg
  let dg : SpecialLinearGroup (Fin (m + 1)) Fld := ⟨Matrix.diagonal Dg, hDg⟩
  let dginv : SpecialLinearGroup (Fin (m + 1)) Fld :=
    ⟨Matrix.diagonal (fun i => (Dg i)⁻¹), by
      rw [Matrix.det_diagonal, Finset.prod_inv_distrib, hprod, inv_one]⟩
  let U : SpecialLinearGroup (Fin (m + 1)) Fld := dginv * A
  have hdg_dginv : dg * dginv = 1 := by
    apply Subtype.ext
    change (dg : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) *
        (dginv : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) = 1
    rw [show (dg : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) = Matrix.diagonal Dg from rfl,
      show (dginv : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
        Matrix.diagonal (fun i => (Dg i)⁻¹) from rfl,
      Matrix.diagonal_mul_diagonal]
    exact Matrix.diagonal_eq_one.mpr (funext (fun i => mul_inv_cancel₀ (hDg_ne i)))
  have hAeq : dg * U = A := by
    rw [show U = dginv * A from rfl, ← mul_assoc, hdg_dginv, one_mul]
  have hU : U ∈ LinearFlag.unitriangular (m + 1) Fld := by
    rw [LinearFlag.mem_unitriangular]
    have hcoe : (U : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
        Matrix.diagonal (fun i => (Dg i)⁻¹) * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) := by
      change (dginv : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) *
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) = _
      rw [show (dginv : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
        Matrix.diagonal (fun i => (Dg i)⁻¹) from rfl]
    constructor
    · intro i j hij
      rw [hcoe, Matrix.diagonal_mul, hA i j hij, mul_zero]
    · intro i
      rw [hcoe, Matrix.diagonal_mul]
      exact inv_mul_cancel₀ (hDg_ne i)
  rw [← hAeq, map_mul]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (hmbSL_ε_diag_mem_iSup L Dg hDg))
    (Subgroup.mem_sup_right (hmbSL_ε_unitriangular_mem_posUnipotent L hU))

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
