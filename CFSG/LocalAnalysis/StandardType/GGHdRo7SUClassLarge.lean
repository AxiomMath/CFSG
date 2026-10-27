module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
import CFSG.LocalAnalysis.StandardType.GGRCClassify
import CFSG.LocalAnalysis.StandardType.GGRCWeylOfPerm
import CFSG.LocalAnalysis.StandardType.GGRCArith
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.ZS.MarkedWeyl
import CFSG.LinearAlgebra.F3ConnectedPairingScalar

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7SUClsAux_isRefl_iff_linRefl {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] (r : W ≃ₗ[ZMod p] W) :
    ZS.IsRefl p r ↔ GGLinRefl r := Iff.rfl

private theorem hdRo7SUClsAux_conj_linRefl {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {r : W ≃ₗ[ZMod p] W}
    (hr : GGLinRefl r) (g : W ≃ₗ[ZMod p] W) : GGLinRefl (g * r * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [show g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ by group, hr.1, mul_one,
      mul_inv_cancel]
  · have hmap : ggLinMove (g * r * g⁻¹) = (ggLinMove r).map g.toLinearMap := by
      rw [ggLinMove, ggLinMove]
      have hcomp : (g * r * g⁻¹).toLinearMap - LinearMap.id =
          g.toLinearMap.comp ((r.toLinearMap - LinearMap.id).comp g⁻¹.toLinearMap) := by
        ext v
        simp [map_sub]
      rw [hcomp, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr g⁻¹.surjective, Submodule.map_top]
    rw [hmap]
    have e := Submodule.equivMapOfInjective g.toLinearMap g.injective (ggLinMove r)
    rw [← LinearEquiv.finrank_eq e, hr.2]

private lemma hdRo7SUClsAux_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private theorem hdRo7SUClsAux_groupEquiv_of_eq {B : Type} {M M' : CoxeterMatrix B} (h : M = M') :
    ∃ φ : M.Group ≃* M'.Group, ∀ i, φ (M.simple i) = M'.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

private lemma hdRo7SUClsAux_symm_swap_isRefl {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W]
    (R : Subgroup (W ≃ₗ[ZMod p] W)) {N : ℕ} (hN : 3 ≤ N) (e : R ≃* Equiv.Perm (Fin N))
    (hrefl : ∀ r : R, GGLinRefl (r : W ≃ₗ[ZMod p] W) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r}) (i j : Fin N) (hij : i ≠ j) :
    GGLinRefl (((e.symm (Equiv.swap i j)) : R) : W ≃ₗ[ZMod p] W) := by
  have hex : ∃ r : R, GGLinRefl (r : W ≃ₗ[ZMod p] W) := by
    by_contra h
    have hemp : {φ : W ≃ₗ[ZMod p] W | φ ∈ R ∧ GGLinRefl φ} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro φ ⟨hφR, hφr⟩
      exact h ⟨⟨φ, hφR⟩, hφr⟩
    have hbot : R = ⊥ := by
      have hg : R = Subgroup.closure {φ : W ≃ₗ[ZMod p] W | φ ∈ R ∧ GGLinRefl φ} := hgen
      rw [hg, hemp, Subgroup.closure_empty]
    let z : Fin N := ⟨0, by omega⟩
    let o : Fin N := ⟨1, by omega⟩
    have hzo : z ≠ o := fun hzo =>
      Nat.zero_ne_one (by simpa [z, o] using congrArg Fin.val hzo)
    have hz1 : e.symm (Equiv.swap z o) = 1 := by
      apply Subtype.ext
      have hmem : ((e.symm (Equiv.swap z o) : R) : W ≃ₗ[ZMod p] W) ∈
          (⊥ : Subgroup (W ≃ₗ[ZMod p] W)) := by
        rw [← hbot]
        exact (e.symm (Equiv.swap z o)).2
      simpa using (Subgroup.mem_bot.mp hmem)
    have hswap1 : Equiv.swap z o = 1 := by
      have h1 := congrArg e hz1
      simpa using h1
    have hz : (Equiv.swap z o) z = o := Equiv.swap_apply_left z o
    rw [hswap1] at hz
    exact hzo (by simpa using hz)
  obtain ⟨r0, hr0⟩ := hex
  obtain ⟨a, b, hab, hr0e⟩ := hrefl r0 hr0
  obtain ⟨σ, hσ⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hij)
  let x : R := e.symm σ
  let r' : R := x * r0 * x⁻¹
  have hr'_refl : GGLinRefl (r' : W ≃ₗ[ZMod p] W) := by
    have hh := hdRo7SUClsAux_conj_linRefl hr0 (x : W ≃ₗ[ZMod p] W)
    simpa [r'] using hh
  have he_r' : e r' = Equiv.swap i j := by
    have h1 : e r' = e x * e r0 * (e x)⁻¹ := by
      change e (x * r0 * x⁻¹) = e x * e r0 * (e x)⁻¹
      rw [map_mul, map_mul, map_inv]
    have h2 : e x = σ := by
      change e (e.symm σ) = σ
      exact MulEquiv.apply_symm_apply e σ
    rw [h1, h2, hr0e, hσ]
  have hfin : e.symm (Equiv.swap i j) = r' := by
    rw [← he_r', MulEquiv.symm_apply_apply]
  rw [hfin]
  exact hr'_refl

private theorem hdRo7SUClsAux_linWeyl_of_perm {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] (R : Subgroup (W ≃ₗ[ZMod p] W))
    {N : ℕ} (hN : 3 ≤ N) (e : R ≃* Equiv.Perm (Fin N))
    (hrefl : ∀ r : R, GGLinRefl (r : W ≃ₗ[ZMod p] W) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r}) : ZS.LinWeyl p R := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ (n + 1) - 1 := by omega
  refine ⟨Fin ((n + 1) - 1), CoxeterMatrix.A ((n + 1) - 1), ?_, ?_⟩
  · refine Or.inl ⟨(n + 1) - 1, Equiv.refl _, hn, Or.inl ?_⟩
    exact (hdRo7SUClsAux_reindex_refl _).symm
  · obtain ⟨φ, hφ⟩ := hdRo7SUClsAux_groupEquiv_of_eq (coxeterMatrix_isFiniteType_A_eq n).symm
    let ee : (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)) :=
      φ.trans (typeAWeylEquiv n).symm
    have hee : ∀ k : Fin n,
        ee ((CoxeterMatrix.A n).simple k) = Equiv.swap k.castSucc k.succ := by
      intro k
      change (typeAWeylEquiv n).symm (φ ((CoxeterMatrix.A n).simple k)) =
        Equiv.swap k.castSucc k.succ
      rw [hφ k, ← typeAWeylEquiv_swap n k, MulEquiv.symm_apply_apply]
    refine ⟨ee.trans e.symm, ?_⟩
    intro k
    have hf : (ee.trans e.symm) ((CoxeterMatrix.A n).simple k) =
        e.symm (Equiv.swap k.castSucc k.succ) := by
      change e.symm (ee ((CoxeterMatrix.A n).simple k)) =
        e.symm (Equiv.swap k.castSucc k.succ)
      rw [hee k]
    change ZS.IsRefl p
      (((ee.trans e.symm) ((CoxeterMatrix.A n).simple k) : ↥R) : W ≃ₗ[ZMod p] W)
    rw [hf]
    exact (hdRo7SUClsAux_isRefl_iff_linRefl _).mpr
      (hdRo7SUClsAux_symm_swap_isRefl R hN e hrefl hgen k.castSucc k.succ
        (ne_of_lt (Fin.castSucc_lt_succ (i := k))))

theorem su_linWeyl_of_card_lt (hKG : GGReflClassLargeInput') {p : ℕ} [Fact p.Prime] (hp : p = 3)
    {d : ℕ} (hd : 9 ≤ d) {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (hfin : Module.finrank (ZMod p) W = d) (R : Subgroup (W ≃ₗ[ZMod p] W)) (hirr : ZS.AbsIrred p R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hsmall : 8 * Nat.card R < p ^ (d * (d - 1) / 2)) : ZS.LinWeyl p R := by
  subst hp
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpm1 : 5 ≤ 3 → ∀ f : Module.Basis (Fin d) (ZMod 3) W,
      (∀ a ∈ R, ∃ (σ : Equiv.Perm (Fin d)) (c : Fin d → ZMod 3),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) →
      ∃ b' : Module.Basis (Fin d) (ZMod 3) W, ∀ a ∈ R,
        ∃ (σ : Equiv.Perm (Fin d)) (c : Fin d → ZMod 3),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i) := by
    intro h5
    exact absurd h5 (by norm_num)
  rcases ggRC_classify hKG hp2 hfin hd R hirr hgen hsmall hpm1 with hweyl | ⟨N, hN, e, he⟩
  · exact hweyl
  · exact hdRo7SUClsAux_linWeyl_of_perm R hN e he hgen

theorem su_classLarge_holds : SUClassLargeLeaf := by
  intro hKG p hpFact hp d hd W instW instMod hfin R hirr hgen hsmall
  have : Fact p.Prime := hpFact
  refine su_linWeyl_of_card_lt hKG hp hd hfin R hirr hgen ?_
  subst hp
  have hfac : d + 1 ≤ 6 * 2 ^ d := by
    have h1 : d + 1 ≤ 2 ^ d := by
      have := Nat.lt_two_pow_self (n := d)
      omega
    nlinarith [Nat.one_le_two_pow (n := d)]
  have hfac2 : 2 * (d + 1).factorial ≤ 2 * 6 * (2 ^ d * d.factorial) := by
    rw [Nat.factorial_succ]
    have h1 : (d + 1) * d.factorial ≤ (6 * 2 ^ d) * d.factorial :=
      Nat.mul_le_mul_right _ hfac
    nlinarith [h1]
  have h3 : 2 * 3 ^ d * (d + 1).factorial ≤ 3 ^ d * (2 * 6 * (2 ^ d * d.factorial)) := by
    calc 2 * 3 ^ d * (d + 1).factorial = 3 ^ d * (2 * (d + 1).factorial) := by ring
      _ ≤ 3 ^ d * (2 * 6 * (2 ^ d * d.factorial)) := Nat.mul_le_mul_left _ hfac2
  have harith := ggRC_arith (p := 3) (n := d) (W := 2 ^ d * d.factorial)
    (by norm_num) (by norm_num) hd (Or.inl le_rfl)
  have hmono : 8 * Nat.card R ≤ 8 * (3 ^ d * ((3 - 1) * 6 * (2 ^ d * d.factorial))) := by
    have h1 : 8 * Nat.card R ≤ 8 * (2 * 3 ^ d * (d + 1).factorial) :=
      Nat.mul_le_mul_left 8 hsmall
    have h2 : 8 * (2 * 3 ^ d * (d + 1).factorial) ≤
        8 * (3 ^ d * ((3 - 1) * 6 * (2 ^ d * d.factorial))) := by
      have := Nat.mul_le_mul_left 8 h3
      simpa using this
    exact le_trans h1 h2
  exact lt_of_le_of_lt hmono harith

private theorem hdRo7SUClsAux_linWeyl_of_cartanModel_E {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {M : CoxeterMatrix (Fin n)}
    (hC : GGIntCartan M C)
    (hM : (∃ e : Fin 6 ≃ Fin n, M = CoxeterMatrix.E₆.reindex e) ∨
      (∃ e : Fin 7 ≃ Fin n, M = CoxeterMatrix.E₇.reindex e) ∨
      (∃ e : Fin 8 ≃ Fin n, M = CoxeterMatrix.E₈.reindex e))
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hW : GGWeylModel3 C A) : ZS.LinWeyl 3 A := by
  obtain ⟨z, α, _hz, _hspan, hP, hA⟩ := hW
  have hα : ∀ i, α i (z i) = 2 := by
    intro i
    rw [hP i i, hC.1 i]
    norm_num
  let s : Fin n → ↥A := fun i =>
    ⟨Module.reflection (hα i), by
      rw [hA]
      exact Subgroup.subset_closure ⟨i, fun v => Module.reflection_apply v (hα i)⟩⟩
  have hs : ∀ i v, ((s i : ↥A) : V ≃ₗ[ZMod 3] V) v = v - α i v • z i := by
    intro i v
    change Module.reflection (hα i) v = v - α i v • z i
    exact Module.reflection_apply v (hα i)
  have himage : (A.subtype '' Set.range s : Set (V ≃ₗ[ZMod 3] V)) =
      {t : V ≃ₗ[ZMod 3] V | ∃ j, ∀ v, t v = v - α j v • z j} := by
    ext t
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, fun v => Module.reflection_apply v (hα i)⟩
    · rintro ⟨j, hj⟩
      refine ⟨s j, ⟨j, rfl⟩, ?_⟩
      exact LinearEquiv.ext fun v => by
        change Module.reflection (hα j) v = t v
        rw [Module.reflection_apply, hj v]
  have hgen : Subgroup.closure (Set.range s) = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [MonoidHom.map_closure, himage, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hA.symm
  have hedge : ∀ i j, M i j = 3 → α i (z j) * α j (z i) = 1 := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      rw [M.diagonal i] at hij
      exact absurd hij (by norm_num)
    rcases hC.2 i j hne with ⟨hm, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
    · rw [hij] at hm
      exact absurd hm (by norm_num)
    · rw [hP i j, hP j i, h1, h2]
      norm_num
    · rw [hij] at hm
      exact absurd hm (by norm_num)
    · rw [hij] at hm
      exact absurd hm (by norm_num)
  have hzero : ∀ i j, i ≠ j → M i j = 2 → α i (z j) = 0 := by
    intro i j hne hij
    rcases hC.2 i j hne with ⟨-, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
    · rw [hP i j, h1]
      norm_num
    · rw [hij] at hm
      exact absurd hm (by norm_num)
    · rw [hij] at hm
      exact absurd hm (by norm_num)
    · rw [hij] at hm
      exact absurd hm (by norm_num)
  exact ZS.linWeyl_of_rootData_E (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hM z α hα hedge
    hzero s hs hgen

private theorem hdRo7SUClsAux_linWeyl_of_E7 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hW : GGWeylModel3 (CartanMatrix.E 7) A) :
    ZS.LinWeyl 3 A :=
  hdRo7SUClsAux_linWeyl_of_cartanModel_E (n := 7) (C := CartanMatrix.E 7)
    (M := CoxeterMatrix.E₇) ggIntCartan_E₇
    (Or.inr (Or.inl ⟨Equiv.refl (Fin 7),
      (hdRo7SUClsAux_reindex_refl CoxeterMatrix.E₇).symm⟩)) hW

private theorem hdRo7SUClsAux_linWeyl_of_E8 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hW : GGWeylModel3 (CartanMatrix.E 8) A) :
    ZS.LinWeyl 3 A :=
  hdRo7SUClsAux_linWeyl_of_cartanModel_E (n := 8) (C := CartanMatrix.E 8)
    (M := CoxeterMatrix.E₈) ggIntCartan_E₈
    (Or.inr (Or.inr ⟨Equiv.refl (Fin 8),
      (hdRo7SUClsAux_reindex_refl CoxeterMatrix.E₈).symm⟩)) hW

theorem su_linWeyl_of_card_lt_small (hKG : GGReflClassOmegaSmall) {d : ℕ} (h5 : 5 ≤ d)
    (h8 : d ≤ 8) {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [Module.Finite (ZMod 3) W] (hfin : Module.finrank (ZMod 3) W = d)
    (R : Subgroup (W ≃ₗ[ZMod 3] W)) (hirr : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hsmall : 8 * Nat.card R < 3 ^ (d * (d - 1) / 2)) : ZS.LinWeyl 3 R := by
  rcases hKG W d hfin h5 h8 R hirr hgen with
      himp | ⟨-, hcard⟩ | ⟨-, horthcard⟩ | ⟨-, ⟨e1, he1⟩⟩ | ⟨-, ⟨e2, he2⟩⟩ |
        ⟨-, hW7⟩ | ⟨-, hW8⟩
  · obtain ⟨b, hmon0⟩ := ggRC_monomial_of_imprimitive hfin R hirr hgen himp
    have hmon : ∀ a ∈ R, ∃ (σ : Equiv.Perm (Fin d)) (c : Fin d → ZMod 3),
        (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i) := by
      intro a ha
      obtain ⟨σ, c, hcne, hbc⟩ := hmon0 a ha
      exact ⟨σ, c, fun i =>
        CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one (c i) (hcne i), hbc⟩
    exact ggRC_linWeyl_of_monomial_pm1 (p := 3) (by norm_num : (3 : ℕ) ≠ 2)
      (by omega : 4 ≤ d) b R hirr hgen hmon
  · exact absurd hcard (not_le.mpr hsmall)
  · exact absurd horthcard (not_le.mpr hsmall)
  · exact hdRo7SUClsAux_linWeyl_of_perm R (by omega : 3 ≤ d + 1) e1 he1 hgen
  · exact hdRo7SUClsAux_linWeyl_of_perm R (by omega : 3 ≤ d + 2) e2 he2 hgen
  · exact hdRo7SUClsAux_linWeyl_of_E7 hW7
  · exact hdRo7SUClsAux_linWeyl_of_E8 hW8

end CFSG.StandardType.HdRo7SU
