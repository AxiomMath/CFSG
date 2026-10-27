module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Chevalley.RootComponentType
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Assembly


private theorem l6m6_cast_simple {ι : Type*} {M N : CoxeterMatrix ι} (h : M = N) (i : ι) :
    (Eq.ndrec (motive := fun (N' : CoxeterMatrix ι) => M.Group ≃* N'.Group)
      (MulEquiv.refl M.Group) h) (M.simple i) = N.simple i := by
  subst h
  rfl

private theorem l6m6_E8_cartan_eq : Tag.cartan .E8 = CartanMatrix.E 8 := by
  change Tag.cartanE 8 = CartanMatrix.E 8
  exact cartanE_eq 8

private theorem l6m6_E8_symm (i j : Fin Tag.E8.rank) :
    CartanMatrix.E₈ i j = CartanMatrix.E₈ j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem l6m6_cartan_diag (i : Fin Tag.E8.rank) : Tag.cartan .E8 i i = 2 := by
  change Tag.cartanE 8 i i = 2
  exact if_pos rfl

private theorem l6m6_corootPair_eq_iform
    (β : Fin Tag.E8.rank → ℤ) (hβ : IsRoot .E8 β)
    (v : Fin Tag.E8.rank → ℤ) : corootPair β v = iform v β := by
  rw [corootPair_eq_iform_of_simplyLaced (τ := .E8) (by decide) hβ, iform_comm]

private def l6m6_label (x : Fin Tag.E8.rank → ℤ) (i : Fin Tag.E8.rank) : ℤ :=
  ∑ j, Tag.cartan .E8 i j * x j

private theorem l6m6_reflect_eq (i : Fin Tag.E8.rank) (x : Fin Tag.E8.rank → ℤ) :
    reflect .E8 i x = x - l6m6_label x i • Pi.single i 1 := by
  simp [reflect, l6m6_label]

private theorem l6m6_label_sub_smul (i j : Fin Tag.E8.rank)
    (x : Fin Tag.E8.rank → ℤ) (c : ℤ) :
    l6m6_label (x - c • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) i =
      l6m6_label x i - c * Tag.cartan .E8 i j := by
  have h1 : ∀ k : Fin Tag.E8.rank,
      Tag.cartan .E8 i k * (x - c • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) k =
      Tag.cartan .E8 i k * x k -
        Tag.cartan .E8 i k * (c * (if k = j then (1 : ℤ) else 0)) := by
    intro k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_sub]
  rw [l6m6_label, Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_sub_distrib]
  have h2 : ∑ k, Tag.cartan .E8 i k * (c * (if k = j then (1 : ℤ) else 0)) =
      c * Tag.cartan .E8 i j := by
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro b _ hb; simp [hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h2, l6m6_label]

private theorem l6m6_label_reflect_self (i : Fin Tag.E8.rank) (x : Fin Tag.E8.rank → ℤ) :
    l6m6_label (reflect .E8 i x) i = - l6m6_label x i := by
  rw [l6m6_reflect_eq, l6m6_label_sub_smul, l6m6_cartan_diag]
  ring

private def l6m6_H (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (x : Fin Tag.E8.rank → ℤ) : V :=
  ∑ k, (x k : ZMod p) • h k

private def l6m6_A (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (x : Fin Tag.E8.rank → ℤ) (v : V) : ZMod p :=
  ∑ k, (x k : ZMod p) * α k v

private theorem l6m6_H_add {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (x y : Fin Tag.E8.rank → ℤ) :
    l6m6_H p h (x + y) = l6m6_H p h x + l6m6_H p h y := by
  simp only [l6m6_H, Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]

private theorem l6m6_H_single {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (i : Fin Tag.E8.rank) :
    l6m6_H p h (Pi.single i 1) = h i := by
  rw [l6m6_H, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem l6m6_H_zsmul {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (c : ℤ) (x : Fin Tag.E8.rank → ℤ) :
    l6m6_H p h (c • x) = (c : ZMod p) • l6m6_H p h x := by
  simp only [l6m6_H, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_smul, Finset.smul_sum]

private theorem l6m6_H_sub {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (x y : Fin Tag.E8.rank → ℤ) :
    l6m6_H p h (x - y) = l6m6_H p h x - l6m6_H p h y := by
  simp only [l6m6_H, Pi.sub_apply, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]

private theorem l6m6_H_sub_smul {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (c : ℤ) (x y : Fin Tag.E8.rank → ℤ) :
    l6m6_H p h (x - c • y) = l6m6_H p h x - (c : ZMod p) • l6m6_H p h y := by
  rw [l6m6_H_sub, l6m6_H_zsmul]

private theorem l6m6_A_single_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (i : Fin Tag.E8.rank) (v : V) :
    l6m6_A p α (Pi.single i 1) v = α i v := by
  rw [l6m6_A, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem l6m6_A_add_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (x y : Fin Tag.E8.rank → ℤ) (v : V) :
    l6m6_A p α (x + y) v = l6m6_A p α x v + l6m6_A p α y v := by
  simp only [l6m6_A, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private theorem l6m6_A_zsmul_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (c : ℤ) (x : Fin Tag.E8.rank → ℤ) (v : V) :
    l6m6_A p α (c • x) v = (c : ZMod p) * l6m6_A p α x v := by
  simp only [l6m6_A, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem l6m6_A_sub_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (x y : Fin Tag.E8.rank → ℤ) (v : V) :
    l6m6_A p α (x - y) v = l6m6_A p α x v - l6m6_A p α y v := by
  rw [sub_eq_add_neg, ← neg_one_smul ℤ y, l6m6_A_add_left, l6m6_A_zsmul_left]
  ring

private theorem l6m6_A_sub_right {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (x : Fin Tag.E8.rank → ℤ) (v w : V) :
    l6m6_A p α x (v - w) = l6m6_A p α x v - l6m6_A p α x w := by
  simp only [l6m6_A, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem l6m6_A_smul_right {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (x : Fin Tag.E8.rank → ℤ)
    (c : ZMod p) (v : V) :
    l6m6_A p α x (c • v) = c * l6m6_A p α x v := by
  simp only [l6m6_A, map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem l6m6_A_h {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (x : Fin Tag.E8.rank → ℤ) (j : Fin Tag.E8.rank) :
    l6m6_A p α x (h j) = ((l6m6_label x j : ℤ) : ZMod p) := by
  rw [l6m6_A]
  have h1 : ∀ k, (x k : ZMod p) * α k (h j) =
      ((CartanMatrix.E₈ j k * x k : ℤ) : ZMod p) := by
    intro k
    rw [hpair k j, ← Int.cast_mul, l6m6_E8_symm k j, mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Int.cast_sum]
  congr 1
  simp only [l6m6_label]
  exact Finset.sum_congr rfl fun k _ => by rw [l6m6_E8_cartan_eq]

private theorem l6m6_A_reflect_left {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V) (i : Fin Tag.E8.rank)
    (x : Fin Tag.E8.rank → ℤ) (v : V) :
    l6m6_A p α (reflect .E8 i x) v =
      l6m6_A p α x v - ((l6m6_label x i : ℤ) : ZMod p) * α i v := by
  rw [l6m6_reflect_eq, l6m6_A_sub_left, l6m6_A_zsmul_left, l6m6_A_single_left]

private theorem l6m6_alpha_H {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (x : Fin Tag.E8.rank → ℤ) (i : Fin Tag.E8.rank) :
    α i (l6m6_H p h x) = ((l6m6_label x i : ℤ) : ZMod p) := by
  rw [l6m6_H]
  simp only [map_sum, map_smul, smul_eq_mul]
  have h1 : ∀ k, (x k : ZMod p) * α i (h k) =
      ((CartanMatrix.E₈ i k * x k : ℤ) : ZMod p) := by
    intro k
    rw [hpair i k, ← Int.cast_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Int.cast_sum]
  congr 1
  simp only [l6m6_label]
  exact Finset.sum_congr rfl fun k _ => by rw [l6m6_E8_cartan_eq]

@[expose] noncomputable def ggE8Equiv : CoxeterMatrix.E₈.Group ≃* WeylGroup .E8 :=
  Eq.ndrec (motive := fun (N : CoxeterMatrix (Fin 8)) => CoxeterMatrix.E₈.Group ≃* N.Group)
    (MulEquiv.refl CoxeterMatrix.E₈.Group) CFSG.StandardType.FrameRoute.coxeterE8_eq

theorem ggE8Equiv_simple (i : Fin 8) :
    ggE8Equiv (CoxeterMatrix.E₈.simple i) = simple .E8 i := by
  unfold ggE8Equiv
  exact l6m6_cast_simple CFSG.StandardType.FrameRoute.coxeterE8_eq i

private theorem l6m6_claim1 {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - α i v • h i) :
    ∀ (w : WeylGroup .E8) (x : Fin Tag.E8.rank → ℤ),
      ρ w (l6m6_H p h x) = l6m6_H p h (w • x) := by
  intro w
  induction w using (coxeterSystem .E8).simple_induction_left with
  | one => intro x; simp
  | mul_simple_left w i ih =>
      intro x
      rw [map_mul, LinearEquiv.mul_apply]
      rw [ih x, hρ i, l6m6_alpha_H (p := p) h α hpair (w • x) i,
        ← l6m6_H_single (p := p) h i, ← l6m6_H_sub_smul (p := p) h]
      rw [mul_smul, simple_smul, l6m6_reflect_eq]

private theorem l6m6_A_simple {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - α i v • h i)
    (i : Fin Tag.E8.rank) (x : Fin Tag.E8.rank → ℤ) (v : V) :
    l6m6_A p α (simple .E8 i • x) (ρ (simple .E8 i) v) = l6m6_A p α x v := by
  rw [hρ i v, simple_smul]
  rw [l6m6_A_sub_right (p := p), l6m6_A_smul_right (p := p), l6m6_A_reflect_left (p := p),
    l6m6_A_h (p := p) h α hpair, l6m6_label_reflect_self, Int.cast_neg]
  ring

private theorem l6m6_claim2 {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - α i v • h i) :
    ∀ (w : WeylGroup .E8) (x : Fin Tag.E8.rank → ℤ) (v : V),
      l6m6_A p α (w • x) (ρ w v) = l6m6_A p α x v := by
  intro w
  induction w using (coxeterSystem .E8).simple_induction_right with
  | one => intro x v; simp
  | mul_simple_right w i ih =>
      intro x v
      rw [map_mul, LinearEquiv.mul_apply, mul_smul]
      rw [ih (simple .E8 i • x) (ρ (simple .E8 i) v)]
      exact l6m6_A_simple (p := p) h α hpair ρ hρ i x v

theorem ggMaxRank_weyl_coroot_smul {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - α i v • h i)
    (w : WeylGroup .E8) (x : Fin Tag.E8.rank → ℤ) :
    ρ w (∑ k, (x k : ZMod p) • h k) = ∑ k, ((w • x) k : ZMod p) • h k := by
  simpa only [l6m6_H] using l6m6_claim1 h α hpair ρ hρ w x

theorem ggMaxRank_weyl_dual_smul {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - α i v • h i)
    (w : WeylGroup .E8) (x : Fin Tag.E8.rank → ℤ) (v : V) :
    ∑ k, ((w • x) k : ZMod p) * α k (ρ w v) = ∑ k, (x k : ZMod p) * α k v := by
  simpa only [l6m6_A] using l6m6_claim2 h α hpair ρ hρ w x v

theorem ggMaxRank_weyl_refl_form
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin Tag.E8.rank → V) (α : Fin Tag.E8.rank → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod p))
    (ρ : WeylGroup .E8 →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ (i : Fin Tag.E8.rank) (v : V), ρ (simple .E8 i) v = v - α i v • h i)
    (β : Fin Tag.E8.rank → ℤ) (hβ : IsRoot .E8 β) (s : WeylGroup .E8)
    (hs : ∀ v : Fin Tag.E8.rank → ℤ, s • v = v - iform (τ := .E8) v β • β) :
    ∀ v : V, ρ s v = v - (∑ k, (β k : ZMod p) * α k v) • ∑ k, (β k : ZMod p) • h k := by
  obtain ⟨w, i, hwi⟩ := isRoot_iff_exists_smul_single.1 hβ
  have hwwβ : w⁻¹ • β = (Pi.single i 1 : Fin Tag.E8.rank → ℤ) := by
    rw [← hwi, ← mul_smul, inv_mul_cancel, one_smul]
  have hroot : s = rootReflection β := by
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.E8.rank → ℤ) fun x => ?_
    rw [hs x, rootReflection_smul hβ x, l6m6_corootPair_eq_iform β hβ x]
  have hsconj : s = w * simple .E8 i * w⁻¹ := by
    rw [hroot, rootReflection_eq_conj hwi]
  intro v
  rw [hsconj]
  have hstep : ρ (w * simple .E8 i * w⁻¹) v = ρ w (ρ (simple .E8 i) (ρ w⁻¹ v)) := by
    simp only [map_mul, LinearEquiv.mul_apply]
  rw [hstep, hρ i]
  rw [map_sub, map_smul]
  have hww : ρ w (ρ w⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    simp
  have hA : α i (ρ w⁻¹ v) = l6m6_A p α β v := by
    have h2 := l6m6_claim2 (p := p) h α hpair ρ hρ w⁻¹ β v
    rw [hwwβ, l6m6_A_single_left (p := p)] at h2
    exact h2
  have hB : ρ w (h i) = l6m6_H p h β := by
    have h1 := l6m6_claim1 (p := p) h α hpair ρ hρ w (Pi.single i 1)
    rw [l6m6_H_single (p := p), hwi] at h1
    exact h1
  rw [hww, hA, hB]
  simp only [l6m6_A, l6m6_H]

end CFSG.StandardType

end
