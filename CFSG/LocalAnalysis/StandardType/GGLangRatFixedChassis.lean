module

public import CFSG.LocalAnalysis.StandardType.GGLangRatLift
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open scoped TensorProduct

section Tensor

theorem langRatWRestrict_pow_coe {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (k : ℕ) (ψ : ↥(Submodule.span ℤ Ψ)) :
    (((wRestrict Ψ w hw ^ k) ψ : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) =
      (w ^ k) • (ψ : Fin τ.rank → ℤ) := by
  induction k generalizing ψ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul, coe_wRestrict]

private theorem langRatFC_sigmaT_pow_tmul {τ : Tag} {L : Type} [Field L]
    (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q k : ℕ) (ψ : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ) :
    ((langRatSigmaT Ψ L w hw q : Module.End ℤ (TSc Ψ L)) ^ k) (ψ ⊗ₜ[ℤ] v) =
      ((wRestrict Ψ w hw ^ k) ψ) ⊗ₜ[ℤ] (((q : ℤ) ^ k) • v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    rw [langRatSigmaT_tmul, pow_succ', Module.End.mul_apply, smul_smul, pow_succ']

private theorem langRatFC_toMul_piT_tmul {τ : Tag} {L : Type} [Field L]
    (Ψ : Set (Fin τ.rank → ℤ)) (ψ : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ) :
    Additive.toMul (langRatPiT Ψ L (ψ ⊗ₜ[ℤ] v)) =
      Hchar (τ := τ) (ψ : Fin τ.rank → ℤ) (Additive.toMul v) :=
  toMul_langRatPiT_tmul Ψ L ψ v

theorem langRatFC_toMul_piT_sigma_pow_tmul {τ : Tag} {L : Type} [Field L]
    (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q k : ℕ) (ψ : ↥(Submodule.span ℤ Ψ)) (v : Additive Lˣ) :
    Additive.toMul (langRatPiT Ψ L
      (((langRatSigmaT Ψ L w hw q : Module.End ℤ (TSc Ψ L)) ^ k) (ψ ⊗ₜ[ℤ] v))) =
      Hchar ((w ^ k) • (ψ : Fin τ.rank → ℤ)) (Additive.toMul v ^ q ^ k) := by
  rw [langRatFC_sigmaT_pow_tmul, langRatFC_toMul_piT_tmul, langRatWRestrict_pow_coe, toMul_zsmul]
  congr 1

private theorem langRatFC_exists_unit_pow_eq {L : Type} [Field L] [IsAlgClosed L] (u : Lˣ)
    {c : ℕ} (hc : 0 < c) :
    ∃ v : Lˣ, v ^ c = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) hc
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hc.ne'] at hz
    exact (Units.ne_zero _) hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

private theorem langRatFC_tsc_divisible {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (Ψ : Set (Fin τ.rank → ℤ)) {c : ℕ} (hc : 0 < c)
    (t : TSc Ψ L) : ∃ z : TSc Ψ L, (c : ℤ) • z = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, smul_zero _⟩
  | tmul γ u =>
    obtain ⟨v, hv⟩ := langRatFC_exists_unit_pow_eq (Additive.toMul u) hc
    refine ⟨γ ⊗ₜ[ℤ] Additive.ofMul v, ?_⟩
    have h : (c : ℤ) • Additive.ofMul v = u := by
      apply Additive.toMul.injective
      rw [toMul_zsmul, zpow_natCast]
      exact hv
    rw [← TensorProduct.tmul_smul, h]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [smul_add, ha, hb]⟩

private def langRatFC_NGGood {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (L : Type) [Field L] (N : ℕ)
    (t : TSc Ψ L) : Prop :=
  ∃ l : List (↥(Submodule.span ℤ Ψ) × Additive Lˣ),
    (∀ p ∈ l, (p.1 : Fin τ.rank → ℤ) ∈ Ψ ∧ Additive.toMul p.2 ^ N = Additive.toMul p.2) ∧
    t = (l.map fun p => p.1 ⊗ₜ[ℤ] p.2).sum

private theorem langRatFC_NGGood.zero {τ : Tag} {L : Type} [Field L] (Ψ : Set (Fin τ.rank → ℤ))
    (N : ℕ) : langRatFC_NGGood Ψ L N 0 :=
  ⟨[], by simp, by simp⟩

private theorem langRatFC_NGGood.add {τ : Tag} {L : Type} [Field L] {Ψ : Set (Fin τ.rank → ℤ)}
    {N : ℕ} {a b : TSc Ψ L} (ha : langRatFC_NGGood Ψ L N a) (hb : langRatFC_NGGood Ψ L N b) :
    langRatFC_NGGood Ψ L N (a + b) := by
  obtain ⟨l₁, h₁, rfl⟩ := ha
  obtain ⟨l₂, h₂, rfl⟩ := hb
  refine ⟨l₁ ++ l₂, ?_, by rw [List.map_append, List.sum_append]⟩
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact h₁ p h
  · exact h₂ p h

private theorem langRatFC_NGGood.tmul {τ : Tag} {L : Type} [Field L] {Ψ : Set (Fin τ.rank → ℤ)}
    {N : ℕ} (ψ : ↥(Submodule.span ℤ Ψ))
    (u : Additive Lˣ) (hu : Additive.toMul u ^ N = Additive.toMul u) :
    langRatFC_NGGood Ψ L N (ψ ⊗ₜ[ℤ] u) := by
  obtain ⟨x, hx⟩ := ψ
  induction hx using Submodule.span_induction generalizing u with
  | mem x hx =>
    exact ⟨[(⟨x, Submodule.subset_span hx⟩, u)], by simpa using ⟨hx, hu⟩, by simp⟩
  | zero =>
    have : (⟨0, Submodule.zero_mem _⟩ : ↥(Submodule.span ℤ Ψ)) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]
    exact langRatFC_NGGood.zero Ψ N
  | add x y hx hy ihx ihy =>
    have : (⟨x + y, Submodule.add_mem _ hx hy⟩ : ↥(Submodule.span ℤ Ψ)) =
        ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, TensorProduct.add_tmul]
    exact (ihx u hu).add (ihy u hu)
  | smul c x hx ih =>
    have : (⟨c • x, Submodule.smul_mem _ c hx⟩ : ↥(Submodule.span ℤ Ψ)) =
        c • (⟨x, hx⟩ : ↥(Submodule.span ℤ Ψ)) := rfl
    rw [this, TensorProduct.smul_tmul]
    refine ih (c • u) ?_
    rw [toMul_zsmul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu]

private theorem langRatFC_sigmaT_pow_apply {τ : Tag} {L : Type} [Field L]
    (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q n : ℕ) (hwn : ∀ γ ∈ Ψ, (w ^ n) • γ = γ) (t : TSc Ψ L) :
    ((langRatSigmaT Ψ L w hw q : Module.End ℤ (TSc Ψ L)) ^ n) t = ((q : ℤ) ^ n) • t := by
  have hW : wRestrict Ψ w hw ^ n = 1 := by
    refine LinearMap.ext_on (Submodule.span_span_coe_preimage (R := ℤ) (s := Ψ)) fun ψ hψ => ?_
    apply Subtype.ext
    rw [langRatWRestrict_pow_coe, Module.End.one_apply]
    exact hwn _ hψ
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul ψ v =>
    rw [langRatFC_sigmaT_pow_tmul, hW, Module.End.one_apply]
    exact TensorProduct.tmul_smul (R := ℤ) (R' := ℤ) (M := ↥(Submodule.span ℤ Ψ))
      (N := Additive Lˣ) ((q : ℤ) ^ n) ψ v
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

theorem langRatSigmaT_pow_apply {τ : Tag} {L : Type} [Field L] (Ψ : Set (Fin τ.rank → ℤ))
    (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q k : ℕ) (z : TSc Ψ L) :
    ((langRatSigmaT Ψ L w hw q : Module.End ℤ (TSc Ψ L)) ^ k) z =
      (q ^ k : ℤ) • (TensorProduct.map ((wRestrict Ψ w hw) ^ k)
        (LinearMap.id : Additive Lˣ →ₗ[ℤ] Additive Lˣ) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul ψ v =>
    rw [langRatFC_sigmaT_pow_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
    exact TensorProduct.tmul_smul (R := ℤ) (R' := ℤ) (M := ↥(Submodule.span ℤ Ψ))
      (N := Additive Lˣ) ((q : ℤ) ^ k) ((wRestrict Ψ w hw ^ k) ψ) v
  | add x y hx hy => rw [map_add, hx, hy, map_add, smul_add]

private theorem langRatFC_sum_pow_list_sum {M : Type*} [AddCommGroup M] (σ : Module.End ℤ M) (n : ℕ)
    {ι : Type*} (l : List ι) (f : ι → M) :
    ∑ k ∈ Finset.range n, (σ ^ k) (l.map f).sum =
      (l.map fun p => ∑ k ∈ Finset.range n, (σ ^ k) (f p)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, map_add, Finset.sum_add_distrib, ih]

theorem langRatNormGeneration {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (Ψ : Set (Fin τ.rank → ℤ)) (w : WeylGroup τ)
    (hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ) (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (hn : 0 < n)
    (hwn : ∀ γ ∈ Ψ, (w ^ n) • γ = γ) (x : TSc Ψ L)
    (hx : langRatSigmaT Ψ L w hw q x = x) :
    ∃ l : List (↥(Submodule.span ℤ Ψ) × Additive Lˣ),
      (∀ p ∈ l, (p.1 : Fin τ.rank → ℤ) ∈ Ψ ∧ Additive.toMul p.2 ^ (q ^ n) = Additive.toMul p.2) ∧
      x = (l.map fun p => ∑ k ∈ Finset.range n,
        ((langRatSigmaT Ψ L w hw q : Module.End ℤ (TSc Ψ L)) ^ k) (p.1 ⊗ₜ[ℤ] p.2)).sum := by
  classical
  set σ : Module.End ℤ (TSc Ψ L) := langRatSigmaT Ψ L w hw q with hσ
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' (by omega)
  have hσn : ∀ t : TSc Ψ L, (σ ^ n) t = ((q : ℤ) ^ n) • t :=
    langRatFC_sigmaT_pow_apply Ψ w hw q n hwn
  obtain ⟨z, hz⟩ := langRatFC_tsc_divisible (L := L) Ψ (c := q ^ n - 1) (by omega) x
  have hc : (((q ^ n - 1 : ℕ) : ℤ)) = (q : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub hqn.le, Nat.cast_pow, Nat.cast_one]
  rw [hc] at hz
  set y : TSc Ψ L := σ z - z with hy
  have hνy : ∑ k ∈ Finset.range n, (σ ^ k) y = x := by
    have h1 : ∀ k : ℕ, (σ ^ k) y = (σ ^ (k + 1)) z - (σ ^ k) z := by
      intro k
      rw [hy, map_sub, pow_succ, Module.End.mul_apply]
    simp_rw [h1]
    rw [Finset.sum_range_sub (fun k => (σ ^ k) z) n, hσn, pow_zero, Module.End.one_apply,
      ← hz, sub_smul, one_smul]
  have hyc : ((q : ℤ) ^ n - 1) • y = 0 := by
    rw [hy, smul_sub, ← map_zsmul, hz, hx, sub_self]
  let g : Additive Lˣ →ₗ[ℤ] Additive Lˣ := (((q : ℤ) ^ n - 1)) • LinearMap.id
  have hex := Module.Flat.lTensor_exact (R := ℤ) (↥(Submodule.span ℤ Ψ))
    (LinearMap.exact_subtype_ker_map g)
  have hgy : g.lTensor (↥(Submodule.span ℤ Ψ)) y = 0 := by
    have : g.lTensor (↥(Submodule.span ℤ Ψ)) = ((q : ℤ) ^ n - 1) • LinearMap.id := by
      rw [LinearMap.lTensor_smul, LinearMap.lTensor_id]
    rw [this, LinearMap.smul_apply, LinearMap.id_apply]
    exact hyc
  obtain ⟨y', hy'⟩ := (hex y).1 hgy
  have hgood : langRatFC_NGGood Ψ L (q ^ n) y := by
    rw [← hy']
    clear hy'
    induction y' using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact langRatFC_NGGood.zero Ψ _
    | tmul ψ κ =>
      rw [LinearMap.lTensor_tmul]
      refine langRatFC_NGGood.tmul ψ (κ : Additive Lˣ) ?_
      have hκ : (((q : ℤ) ^ n - 1)) • (κ : Additive Lˣ) = 0 := κ.2
      have h2 := congrArg Additive.toMul hκ
      rw [toMul_zsmul, toMul_zero] at h2
      calc Additive.toMul (κ : Additive Lˣ) ^ (q ^ n)
          = Additive.toMul (κ : Additive Lˣ) ^ (((q : ℤ) ^ n - 1) + 1) := by
            rw [← zpow_natCast]
            congr 1
            push_cast
            ring
        _ = Additive.toMul (κ : Additive Lˣ) := by rw [zpow_add_one, h2, one_mul]
    | add a b ha hb => rw [map_add]; exact ha.add hb
  obtain ⟨l, hl, hyl⟩ := hgood
  refine ⟨l, hl, ?_⟩
  rw [← hνy, hyl]
  exact langRatFC_sum_pow_list_sum σ n l _

end Tensor

section Core

@[expose] noncomputable def langRatFC_core
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (Ψ₁ : Set (Fin τ.rank → ℤ)) (s : ℕ) : Subgroup (ModGL τ L) :=
  ⨆ (H : Subgroup (ModGL τ L)) (_ : H ≤ rootSpan τ L Ψ₁ ∧
    (∀ g ∈ H, iterHom S.D.step s g = g) ∧ Group.IsPerfect ↥H), H

theorem langRatFC_core_le_rootSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (Ψ₁ : Set (Fin τ.rank → ℤ)) (s : ℕ) : langRatFC_core S Ψ₁ s ≤ rootSpan τ L Ψ₁ :=
  iSup₂_le fun _ hH => hH.1

theorem iterHom_step_eq_of_mem_langRatFC_core
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (Ψ₁ : Set (Fin τ.rank → ℤ)) (s : ℕ) {g : ModGL τ L}
    (hg : g ∈ langRatFC_core S Ψ₁ s) : iterHom S.D.step s g = g := by
  have : langRatFC_core S Ψ₁ s ≤ (iterHom S.D.step s).eqLocus (MonoidHom.id _) :=
    iSup₂_le fun H hH g hg => hH.2.1 g hg
  exact this hg

theorem isPerfect_langRatFC_core
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (Ψ₁ : Set (Fin τ.rank → ℤ)) (s : ℕ) : Group.IsPerfect ↥(langRatFC_core S Ψ₁ s) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) (iSup₂_le fun H hH => ?_)
  calc H = ⁅H, H⁆ := (Subgroup.isPerfect_iff.1 hH.2.2).symm
    _ ≤ ⁅langRatFC_core S Ψ₁ s, langRatFC_core S Ψ₁ s⁆ :=
        Subgroup.commutator_mono
          (le_iSup₂ (f := fun (H : Subgroup (ModGL τ L)) (_ : H ≤ rootSpan τ L Ψ₁ ∧
            (∀ g ∈ H, iterHom S.D.step s g = g) ∧ Group.IsPerfect ↥H) => H) H hH)
          (le_iSup₂ (f := fun (H : Subgroup (ModGL τ L)) (_ : H ≤ rootSpan τ L Ψ₁ ∧
            (∀ g ∈ H, iterHom S.D.step s g = g) ∧ Group.IsPerfect ↥H) => H) H hH)

end Core

section Comb

theorem langRatFC_prod_range_shift_period {M : Type*} [CommGroup M] (h : ℕ → M) (n : ℕ)
    (hper : ∀ j, h (j + n) = h j) (m : ℕ) :
    ∏ k ∈ Finset.range n, h (k + m) = ∏ k ∈ Finset.range n, h k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← ih]
    have h1 : ∏ k ∈ Finset.range (n + 1), h (k + m) =
        (∏ k ∈ Finset.range n, h (k + 1 + m)) * h (0 + m) := Finset.prod_range_succ' _ _
    have h2 : ∏ k ∈ Finset.range (n + 1), h (k + m) =
        (∏ k ∈ Finset.range n, h (k + m)) * h (n + m) := Finset.prod_range_succ _ _
    have h3 : h (n + m) = h (0 + m) := by rw [add_comm n m, zero_add, hper m]
    rw [h3] at h2
    have h4 : ∏ k ∈ Finset.range n, h (k + 1 + m) = ∏ k ∈ Finset.range n, h (k + m) :=
      mul_right_cancel (h1.symm.trans h2)
    rw [← h4]
    exact Finset.prod_congr rfl fun k _ => by rw [show k + (m + 1) = k + 1 + m by omega]

theorem langRatFC_prod_range_mul_regroup {M : Type*} [CommGroup M] (h : ℕ → M) (s r : ℕ) :
    ∏ k ∈ Finset.range (s * r), h k =
      ∏ j ∈ Finset.range s, ∏ t ∈ Finset.range r, h (j + s * t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih]
    simp_rw [Finset.prod_range_succ, Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [add_comm]

end Comb

section Frob

theorem langRatFC_exists_unit_root_fixed {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {q : ℕ} (e : ℕ)
    (hqe : q = 2 ^ e) (u : Lˣ) (m n : ℕ) (hu : u ^ (q ^ n) = u) :
    ∃ v : Lˣ, v ^ (q ^ m) = u ∧ v ^ (q ^ n) = v := by
  have hqm : 0 < q ^ m := pow_pos (by rw [hqe]; positivity) m
  obtain ⟨v, hv⟩ := langRatFC_exists_unit_pow_eq u hqm
  refine ⟨v, hv, ?_⟩
  have h1 : (v ^ (q ^ n)) ^ (q ^ m) = v ^ (q ^ m) := by
    calc (v ^ (q ^ n)) ^ (q ^ m) = (v ^ (q ^ m)) ^ (q ^ n) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = u ^ (q ^ n) := by rw [hv]
      _ = u := hu
      _ = v ^ (q ^ m) := hv.symm
  have hqm2 : q ^ m = 2 ^ (e * m) := by rw [hqe, ← pow_mul]
  have h2 : ((v ^ (q ^ n) : Lˣ) : L) ^ (2 ^ (e * m)) = (v : L) ^ (2 ^ (e * m)) := by
    rw [← hqm2, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h1]
  haveI : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have h3 := iterateFrobenius_inj L 2 (e * m) h2
  exact Units.ext h3

end Frob

section Norm

private theorem langRatFC_step_prod_stride
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (γ : Fin τ.rank → ℤ) (v : Lˣ) (s r a : ℕ) :
    S.D.step (rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (a + s * t)) • γ) (v ^ S.D.q ^ (a + s * t)))) =
      rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (a + 1 + s * t)) • γ) (v ^ S.D.q ^ (a + 1 + s * t))) := by
  induction r with
  | zero => simp [rootDiagUnit_one]
  | succ r ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, rootDiagUnit_mul, rootDiagUnit_mul,
      map_mul, ih]
    congr 1
    have := S.step_Hel hFr hΦ hn ((w ^ (a + s * r)) • γ) (v ^ S.D.q ^ (a + s * r))
    unfold Hel at this
    have e : a + 1 + s * r = (a + s * r) + 1 := by omega
    rw [this, e, pow_succ' w, mul_smul, pow_succ, pow_mul]

theorem langRatFC_iterHom_step_prod_stride
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (γ : Fin τ.rank → ℤ) (v : Lˣ) (s r j : ℕ) :
    iterHom S.D.step j (rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (s * t)) • γ) (v ^ S.D.q ^ (s * t)))) =
      rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (j + s * t)) • γ) (v ^ S.D.q ^ (j + s * t))) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iterHom_succ, ih]
    exact langRatFC_step_prod_stride S hFr hΦ hn γ v s r j

private theorem langRatFC_noncommProd_rootDiagUnit
    {τ : Tag} {L : Type} [Field L] {ι : Type*} [DecidableEq ι]
    (F : ι → ModGL τ L) (c : ι → (Fin τ.rank → Lˣ)) (hF : ∀ k, F k = rootDiagUnit τ (c k))
    (s : Finset ι) : ∀ comm : (s : Set ι).Pairwise (Function.onFun Commute F),
      s.noncommProd F comm = rootDiagUnit τ (∏ k ∈ s, c k) := by
  induction s using Finset.induction_on with
  | empty => intro comm; simp [rootDiagUnit_one]
  | insert a s ha ih =>
    intro comm
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Finset.prod_insert ha, rootDiagUnit_mul,
      hF a, ih]

theorem langRatFC_norm_eq_rootDiagUnit_prod
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom b) i =
      componentRoots (rootCharHom b) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i ≠
        componentRoots (rootCharHom b) i)
    (y : (outerOrbitFamily S hb i hs hmin).S 0) (c : ℕ → (Fin τ.rank → Lˣ))
    (hc : ∀ j, iterHom S.D.step j (y : ModGL τ L) = rootDiagUnit τ (c j)) :
    (outerOrbitFamily S hb i hs hmin).norm y = rootDiagUnit τ (∏ j ∈ Finset.range s, c j) := by
  have h1 : ∀ k : ZMod s,
      ((((outerOrbitFamily S hb i hs hmin).diag y k : (outerOrbitFamily S hb i hs hmin).S k)) :
        ModGL τ L) = rootDiagUnit τ (c k.val) := fun k => by
    rw [CycFamily.coe_diag_apply]
    exact hc _
  show (outerOrbitFamily S hb i hs hmin).mu ((outerOrbitFamily S hb i hs hmin).diag y) = _
  unfold CycFamily.mu
  rw [Subgroup.noncommPiCoprod_apply]
  refine (langRatFC_noncommProd_rootDiagUnit _ (fun k : ZMod s => c k.val) h1 Finset.univ
    _).trans ?_
  congr 1
  refine Finset.prod_bij (fun k _ => k.val) (fun k _ => Finset.mem_range.2 (ZMod.val_lt k))
    (fun a _ b _ h => ZMod.val_injective s h) (fun j hj => ⟨(j : ZMod s), Finset.mem_univ _, ?_⟩)
    (fun _ _ => rfl)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hj)]

end Norm

section Assembly

private theorem langRatFC_orbit_norm_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom b) i =
      componentRoots (rootCharHom b) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i ≠
        componentRoots (rootCharHom b) i)
    {d : ModGL τ L} (hd : d ∈ langRatFC_core S (componentRoots (rootCharHom b) i) s)
    (c : ℕ → (Fin τ.rank → Lˣ)) (hc : ∀ j, iterHom S.D.step j d = rootDiagUnit τ (c j)) :
    rootDiagUnit τ (∏ j ∈ Finset.range s, c j) ∈
      rationalComponent S.ρ S.Γ (rootCharHom b) i := by
  have hle : langRatFC_core S (componentRoots (rootCharHom b) i) s ≤
      (outerOrbitFamily S hb i hs hmin).S 0 := by
    refine (langRatFC_core_le_rootSpan S _ s).trans (le_of_eq ?_)
    show rootSpan τ L (componentRoots (rootCharHom b) i) = rootSpan τ L
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[(0 : ZMod s).val] '' componentRoots (rootCharHom b) i)
    rw [ZMod.val_zero]
    simp
  let θ₀ : ↥(langRatFC_core S (componentRoots (rootCharHom b) i) s) →*
      (outerOrbitFamily S hb i hs hmin).S 0 := Subgroup.inclusion hle
  have hfix : ∀ x, iterHom S.D.step s
      ((θ₀ x : (outerOrbitFamily S hb i hs hmin).S 0) : ModGL τ L) = θ₀ x := fun x =>
    iterHom_step_eq_of_mem_langRatFC_core S (componentRoots (rootCharHom b) i) s x.2
  have h1 := outer_norm_mem_rationalComponent S hb i hs hmin
    (isPerfect_langRatFC_core S _ s) θ₀ hfix ⟨d, hd⟩
  rwa [langRatFC_norm_eq_rootDiagUnit_prod S hb i hs hmin (θ₀ ⟨d, hd⟩) c hc] at h1

end Assembly

section Final

theorem langRatFC_isRoot_of_mem_rationalRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rationalRoots S.ρ (rootCharHom a) i) : IsRoot τ γ := by
  obtain ⟨k, δ, hδ, rfl⟩ := hγ
  induction k with
  | zero => exact hδ.1.1
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (S.frob.isRoot_iff _).2 ih

theorem langRatFC_norm_factor_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom b) i =
      componentRoots (rootCharHom b) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom b) i ≠
        componentRoots (rootCharHom b) i)
    {γ : Fin τ.rank → ℤ} (u : Lˣ) (r : ℕ)
    (hd : rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (s * t)) • γ) (u ^ S.D.q ^ (s * t))) ∈
      langRatFC_core S (componentRoots (rootCharHom b) i) s) :
    rootDiagUnit τ (∏ k ∈ Finset.range (s * r), Hchar ((w ^ k) • γ) (u ^ S.D.q ^ k)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom b) i := by
  have hc : ∀ j, iterHom S.D.step j (rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (s * t)) • γ) (u ^ S.D.q ^ (s * t)))) =
      rootDiagUnit τ (∏ t ∈ Finset.range r,
        Hchar ((w ^ (j + s * t)) • γ) (u ^ S.D.q ^ (j + s * t))) :=
    fun j => langRatFC_iterHom_step_prod_stride S hFr hΦ hn γ u s r j
  have := langRatFC_orbit_norm_mem S hb i hs hmin hd
    (fun j => ∏ t ∈ Finset.range r,
      Hchar ((w ^ (j + s * t)) • γ) (u ^ S.D.q ^ (j + s * t))) hc
  rw [langRatFC_prod_range_mul_regroup (fun k => Hchar ((w ^ k) • γ) (u ^ S.D.q ^ k)) s r]
  exact this

end Final

end CFSG.StandardType.LangRat
