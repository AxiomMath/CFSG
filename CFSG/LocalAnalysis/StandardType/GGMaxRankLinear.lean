module

public import CFSG.LinearAlgebra.MovedSpanFixSub
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

namespace CFSG.StandardType

open scoped Matrix

private lemma l6m1_A_diag (i : Fin 8) : CartanMatrix.A 8 i i = 2 := by
  simp [CartanMatrix.A]

private lemma l6m1_A_adj {i j : Fin 8} (hij : i ≠ j) (h : i.val + 1 = j.val) :
    CartanMatrix.A 8 i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hij, if_pos (Or.inl h)]

private lemma l6m1_sum_smul_single {p : ℕ} (x : Fin 8 → ZMod p) :
    (∑ j, x j • Pi.single j (1 : ZMod p)) = x := by
  ext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne (Ne.symm hk), smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem ggMaxRank_chain_gauge {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (r : Fin 8 → (V ≃ₗ[ZMod p] V)) (h h' : Fin 8 → V)
    (α α' : Fin 8 → Module.Dual (ZMod p) V)
    (hr : ∀ i v, r i v = v - α i v • h i) (hr' : ∀ i v, r i v = v - α' i v • h' i)
    (hp : ∀ i j, α i (h j) = ((CartanMatrix.A 8 i j : ℤ) : ZMod p))
    (hp' : ∀ i j, α' i (h' j) = ((CartanMatrix.A 8 i j : ℤ) : ZMod p)) :
    ∃ c : ZMod p, c ≠ 0 ∧ (∀ i, h' i = c • h i) ∧ ∀ i, α' i = c⁻¹ • α i := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hdiag : ∀ i, α i (h i) = 2 := by
    intro i
    simpa [l6m1_A_diag i] using hp i i
  have hdiag' : ∀ i, α' i (h' i) = 2 := by
    intro i
    simpa [l6m1_A_diag i] using hp' i i
  have hh : ∀ i, h i ≠ 0 := by
    intro i hi
    have hc := hdiag i
    rw [hi, map_zero] at hc
    exact h2 hc.symm
  have hh' : ∀ i, h' i ≠ 0 := by
    intro i hi
    have hc := hdiag' i
    rw [hi, map_zero] at hc
    exact h2 hc.symm
  have hrel : ∀ i v, α i v • h i = α' i v • h' i := by
    intro i v
    have hmain : v - α i v • h i = v - α' i v • h' i := by rw [← hr i v, hr' i v]
    have hneg : -(α i v • h i) = -(α' i v • h' i) := by
      have hc := congrArg (fun x => -v + x) hmain
      simpa using hc
    exact neg_injective hneg
  have hcancel : ∀ (w : V) (_ : w ≠ 0) (a b : ZMod p), a • w = b • w → a = b := by
    intro w hw a b hab
    have hsub : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp hsub with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hw
  let c : Fin 8 → ZMod p := fun i => (2 : ZMod p)⁻¹ * α i (h' i)
  have hh'c : ∀ i, h' i = c i • h i := by
    intro i
    have h1 := hrel i (h' i)
    rw [hdiag' i] at h1
    calc h' i = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • h' i) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = (2 : ZMod p)⁻¹ • (α i (h' i) • h i) := by rw [← h1]
      _ = c i • h i := by rw [smul_smul]
  have hcne : ∀ i, c i ≠ 0 := by
    intro i hi
    exact hh' i (by rw [hh'c i, hi, zero_smul])
  have hadj : ∀ k : Fin 7, c (Fin.succ k) = c (Fin.castSucc k) := by
    intro k
    have hval : (Fin.castSucc k).val + 1 = (Fin.succ k).val := by simp
    have hij : (Fin.castSucc k : Fin 8) ≠ Fin.succ k := by
      intro hcontra
      have := congrArg Fin.val hcontra
      simp at this
    have hA : ((CartanMatrix.A 8 (Fin.castSucc k) (Fin.succ k) : ℤ) : ZMod p) = -1 := by
      rw [l6m1_A_adj hij hval]
      exact (Int.cast_neg (1 : ℤ)).trans (by rw [Int.cast_one]; rfl)
    have hL : α (Fin.castSucc k) (h' (Fin.succ k))
        = c (Fin.succ k) * ((CartanMatrix.A 8 (Fin.castSucc k) (Fin.succ k) : ℤ) : ZMod p) := by
      rw [hh'c (Fin.succ k), map_smul, hp (Fin.castSucc k) (Fin.succ k), smul_eq_mul]
    have hstep :
        (c (Fin.succ k)
            * ((CartanMatrix.A 8 (Fin.castSucc k) (Fin.succ k) : ℤ) : ZMod p)) • h (Fin.castSucc k)
          = (((CartanMatrix.A 8 (Fin.castSucc k) (Fin.succ k) : ℤ) : ZMod p)
              * c (Fin.castSucc k)) • h (Fin.castSucc k) := by
      have h1 := hrel (Fin.castSucc k) (h' (Fin.succ k))
      rw [hL, hp' (Fin.castSucc k) (Fin.succ k), hh'c (Fin.castSucc k), smul_smul] at h1
      exact h1
    have hAi : ((CartanMatrix.A 8 (Fin.castSucc k) (Fin.succ k) : ℤ) : ZMod p) ≠ 0 := by
      rw [hA]
      intro hcon
      have h1 : (1 : ZMod p) = 0 := neg_eq_zero.mp hcon
      exact h2 (by rw [show (2 : ZMod p) = 2 * 1 by ring, h1, mul_zero])
    have hscalar := hcancel (h (Fin.castSucc k)) (hh (Fin.castSucc k)) _ _ hstep
    rw [mul_comm (c (Fin.succ k)) _] at hscalar
    exact mul_left_cancel₀ hAi hscalar
  have hcommon : ∀ i : Fin 8, c i = c 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ k ih => rw [hadj k, ih]
  refine ⟨c 0, hcne 0, ?_, ?_⟩
  · intro i
    rw [hh'c i, hcommon i]
  · intro i
    ext v
    have hstep := hrel i v
    rw [hh'c i, hcommon i, smul_smul] at hstep
    have hscalar : α i v = α' i v * c 0 :=
      hcancel (h i) (hh i) _ _ hstep
    rw [LinearMap.smul_apply, smul_eq_mul, hscalar, mul_comm (α' i v) (c 0),
      inv_mul_cancel_left₀ (hcne 0)]

theorem ggMaxRank_movedSpan_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} (r : ι → (V ≃ₗ[ZMod p] V)) (h : ι → V)
    (α : ι → Module.Dual (ZMod p) V) (hr : ∀ i v, r i v = v - α i v • h i)
    (hα : ∀ i, α i (h i) = 2) :
    CFSG.LinearAlgebra.movedSpan (Subgroup.closure (Set.range r)) =
      Submodule.span (ZMod p) (Set.range h) := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  have hhH : ∀ i, h i ∈ H := fun i => Submodule.subset_span (Set.mem_range_self i)
  have key : ∀ t : V ≃ₗ[ZMod p] V, t ∈ Subgroup.closure (Set.range r) →
      ∀ u : V, t u - u ∈ H := by
    intro t ht
    refine Subgroup.closure_induction (p := fun t _ => ∀ u : V, t u - u ∈ H)
      ?_ ?_ ?_ ?_ ht
    · intro x hx u
      obtain ⟨i, rfl⟩ := hx
      have hval : r i u - u = (-(α i u)) • h i := by
        rw [hr i u]
        rw [show u - (α i u) • h i - u = -((α i u) • h i) by abel]
        exact (neg_smul (α i u) (h i)).symm
      rw [hval]
      exact H.smul_mem _ (hhH i)
    · intro u
      simp
    · intro x y hx hy hpx hpy u
      have h1 : x (y u) - y u ∈ H := hpx (y u)
      have h2' : y u - u ∈ H := hpy u
      have heq : (x * y) u - u = (x (y u) - y u) + (y u - u) := by
        change x (y u) - u = _
        abel
      rw [heq]
      exact H.add_mem h1 h2'
    · intro x hx hpx u
      have h1 : x (x⁻¹ u) - x⁻¹ u ∈ H := hpx (x⁻¹ u)
      have heq : x⁻¹ u - u = -(x (x⁻¹ u) - x⁻¹ u) := by
        have hxx : x (x⁻¹ u) = u := LinearEquiv.apply_symm_apply x u
        rw [hxx]
        abel
      rw [heq]
      exact H.neg_mem h1
  apply le_antisymm
  · unfold CFSG.LinearAlgebra.movedSpan
    rw [Submodule.span_le]
    rintro w ⟨t, ht, u, rfl⟩
    exact key t ht u
  · rw [Submodule.span_le]
    rintro w ⟨i, rfl⟩
    have hmem : r i (h i) - h i ∈
        CFSG.LinearAlgebra.movedSpan (Subgroup.closure (Set.range r)) :=
      Submodule.subset_span
        ⟨r i, Subgroup.subset_closure (Set.mem_range_self i), h i, rfl⟩
    have hval : r i (h i) - h i = (-(2 : ZMod p)) • h i := by
      rw [hr i (h i), hα i]
      rw [show h i - (2 : ZMod p) • h i - h i = -((2 : ZMod p) • h i) by abel]
      exact (neg_smul (2 : ZMod p) (h i)).symm
    have hmain : (-((2 : ZMod p)⁻¹)) • (r i (h i) - h i) = h i := by
      rw [hval, smul_smul]
      rw [show (-((2 : ZMod p)⁻¹)) * (-(2 : ZMod p)) = (1 : ZMod p) by field_simp]
      rw [one_smul]
    have hthis := Submodule.smul_mem
      (CFSG.LinearAlgebra.movedSpan (Subgroup.closure (Set.range r))) (-((2 : ZMod p)⁻¹)) hmem
    rw [hmain] at hthis
    exact hthis

theorem ggMaxRank_finrank_of_datum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (hsep : ∀ b : ↥Bs, (∀ i, α i (ι (Additive.ofMul b)) = 0) ↔
      (b : G) ∈ Subgroup.centralizer (X : Set G))
    (hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = p) :
    Module.finrank (ZMod p) V = 9 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hBsfin : Finite ↥Bs := inferInstance
  haveI : Finite (Additive ↥Bs) := Finite.of_equiv ↥Bs (Equiv.refl ↥Bs)
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Fintype V := Fintype.ofFinite V
  let F : V →ₗ[ZMod p] (Fin 8 → ZMod p) := LinearMap.pi fun i => α i
  have hF_apply : ∀ v i, F v i = α i v := by
    intro v i
    simp [F, LinearMap.pi_apply]
  let Cinv : Matrix (Fin 8) (Fin 8) ℤ :=
    !![4, 5, 7, 10, 8, 6, 4, 2;
       5, 8, 10, 15, 12, 9, 6, 3;
       7, 10, 14, 20, 16, 12, 8, 4;
       10, 15, 20, 30, 24, 18, 12, 6;
       8, 12, 16, 24, 20, 15, 10, 5;
       6, 9, 12, 18, 15, 12, 8, 4;
       4, 6, 8, 12, 10, 8, 6, 3;
       2, 3, 4, 6, 5, 4, 3, 2]
  have hZ : CartanMatrix.E 8 * Cinv = 1 := by decide
  let M : Matrix (Fin 8) (Fin 8) (ZMod p) :=
    (CartanMatrix.E 8).map (Int.castRingHom (ZMod p))
  let C : Matrix (Fin 8) (Fin 8) (ZMod p) := Cinv.map (Int.castRingHom (ZMod p))
  have hMC : M * C = 1 := by
    have h := congrArg (fun N : Matrix (Fin 8) (Fin 8) ℤ =>
      N.map (Int.castRingHom (ZMod p))) hZ
    rw [Matrix.map_mul (f := Int.castRingHom (ZMod p))] at h
    rw [Matrix.map_one (f := (Int.castRingHom (ZMod p) : ℤ → ZMod p)) (by simp) (by simp)] at h
    simpa [M, C] using h
  have hpairM : ∀ i j, α i (h j) = M i j := by
    intro i j
    rw [hpair i j]
    simp [M, Matrix.map_apply]
  have hFh : ∀ j, F (h j) = M *ᵥ Pi.single j (1 : ZMod p) := by
    intro j
    ext i
    rw [hF_apply, hpairM i j, Matrix.mulVec_single_one, Matrix.col_apply]
  have hF_pre : ∀ w : Fin 8 → ZMod p,
      F (∑ j, (C *ᵥ w) j • h j) = w := by
    intro w
    calc F (∑ j, (C *ᵥ w) j • h j)
        = ∑ j, (C *ᵥ w) j • F (h j) := by simp
      _ = ∑ j, (C *ᵥ w) j • (M *ᵥ Pi.single j (1 : ZMod p)) := by simp [hFh]
      _ = M *ᵥ (∑ j, (C *ᵥ w) j • Pi.single j (1 : ZMod p)) := by
            conv_rhs => rw [← Matrix.mulVecLin_apply]
            rw [map_sum]
            simp [Matrix.mulVecLin_apply, map_smul]
      _ = M *ᵥ (C *ᵥ w) := by
            congr 1
            exact l6m1_sum_smul_single (C *ᵥ w)
      _ = (M * C) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = w := by rw [hMC, Matrix.one_mulVec]
  have hrange : LinearMap.range F = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro w
    exact ⟨∑ j, (C *ᵥ w) j • h j, hF_pre w⟩
  have hker_card : Nat.card ↥(LinearMap.ker F) = p := by
    let φ : ↥(LinearMap.ker F) → ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := fun v =>
      ⟨(Additive.toMul (ι.symm v.1) : ↥Bs), by
        rw [Subgroup.mem_inf]
        refine ⟨(Additive.toMul (ι.symm v.1) : ↥Bs).2, ?_⟩
        exact (hsep (Additive.toMul (ι.symm v.1) : ↥Bs)).mp (fun i => by
          have hv : F v.1 = 0 := LinearMap.mem_ker.mp v.2
          have hv2 := congrFun hv i
          rw [hF_apply] at hv2
          simpa using hv2)⟩
    let ψ : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) → ↥(LinearMap.ker F) := fun b =>
      ⟨ι (Additive.ofMul (⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩ : ↥Bs)), by
        rw [LinearMap.mem_ker]
        funext i
        rw [hF_apply]
        exact (hsep ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩).mpr (Subgroup.mem_inf.mp b.2).2 i⟩
    have hφψ : Function.LeftInverse ψ φ := by
      intro v
      apply Subtype.ext
      simp [φ, ψ]
    have hψφ : Function.RightInverse ψ φ := by
      intro b
      apply Subtype.ext
      simp [φ, ψ]
    let e : ↥(LinearMap.ker F) ≃ ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
      ⟨φ, ψ, hφψ, hψφ⟩
    rw [Nat.card_congr e, hcard]
  haveI : Module.Finite (ZMod p) V := by
    rw [Module.finite_def]
    exact ⟨Finset.univ, by rw [Finset.coe_univ, Submodule.span_univ]⟩
  haveI : Fintype ↥(LinearMap.ker F) := Fintype.ofFinite _
  have hkerfin : Module.Finite (ZMod p) ↥(LinearMap.ker F) := by
    rw [Module.finite_def]
    exact ⟨Finset.univ, by rw [Finset.coe_univ, Submodule.span_univ]⟩
  have hkerrank : Module.finrank (ZMod p) ↥(LinearMap.ker F) = 1 := by
    haveI := hkerfin
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := ↥(LinearMap.ker F))
    rw [Nat.card_zmod, hker_card] at h
    have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h1 : p ^ 1 = p ^ Module.finrank (ZMod p) ↥(LinearMap.ker F) := by
      rw [pow_one]
      exact h
    exact (Nat.pow_right_injective hp2' h1).symm
  let φa : Additive ↥Bs →+ (Fin 8 → ZMod p) :=
    { toFun := fun b => F (ι b)
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add] }
  have hφasurj : Function.Surjective φa := by
    intro w
    have hw : w ∈ LinearMap.range F := by rw [hrange]; trivial
    obtain ⟨v, hv⟩ := hw
    exact ⟨ι.symm v, by simp [φa, hv]⟩
  have hφaker : Nat.card ↥(φa.ker) = p := by
    let Φ : ↥(φa.ker) → ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := fun b =>
      ⟨(Additive.toMul b.1 : ↥Bs), by
        rw [Subgroup.mem_inf]
        refine ⟨(Additive.toMul b.1 : ↥Bs).2, ?_⟩
        exact (hsep (Additive.toMul b.1 : ↥Bs)).mp (fun i => by
          have hb : φa b.1 = 0 := AddMonoidHom.mem_ker.mp b.2
          have hb2 := congrFun hb i
          change F (ι b.1) i = 0 at hb2
          rw [hF_apply] at hb2
          simpa using hb2)⟩
    let Ψ : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) → ↥(φa.ker) := fun b =>
      ⟨Additive.ofMul (⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩ : ↥Bs), by
        rw [AddMonoidHom.mem_ker]
        funext i
        change F (ι (Additive.ofMul (⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩ : ↥Bs))) i = 0
        rw [hF_apply]
        exact (hsep ⟨b.1, (Subgroup.mem_inf.mp b.2).1⟩).mpr (Subgroup.mem_inf.mp b.2).2 i⟩
    have hΦΨ : Function.LeftInverse Ψ Φ := by
      intro b; apply Subtype.ext; simp [Φ, Ψ]
    have hΨΦ : Function.RightInverse Ψ Φ := by
      intro b; apply Subtype.ext; simp [Φ, Ψ]
    let e : ↥(φa.ker) ≃ ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := ⟨Φ, Ψ, hΦΨ, hΨΦ⟩
    rw [Nat.card_congr e, hcard]
  have hφarange : Nat.card ↥(φa.range) = p ^ 8 := by
    have htop : φa.range = ⊤ := AddMonoidHom.range_eq_top.mpr hφasurj
    rw [htop, Nat.card_congr (AddSubgroup.topEquiv).toEquiv, Nat.card_fun, Nat.card_zmod]
    simp [Nat.card_eq_fintype_card]
  have hBs : Nat.card (Additive ↥Bs) = p ^ 9 := by
    have hLag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (φa.ker)
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φa).toEquiv,
      hφarange, hφaker] at hLag
    rw [hLag]
    ring
  have hcardV : Nat.card V = p ^ 9 := by
    rw [← Nat.card_congr ι.toEquiv]
    exact hBs
  have hfin := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
  rw [Nat.card_zmod, hcardV] at hfin
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hfin).symm

end CFSG.StandardType

end
