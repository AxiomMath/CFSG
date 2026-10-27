module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOrbit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusCopies
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisOrbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.RootSystem
open scoped Matrix TensorProduct

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem omMinus_two_mu_cases (hK : Nat.card K = 2) {k : Type} [Field k] [CharP k 2]
    {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} {y : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ) :
    (∀ s, μ s = 0 ∨ μ s = 1) ∧ ((∃ h ∈ (o8mDatum hirrQ).H, χ h ≠ 1) → μ 2 = 0) := by
  have hχ1 : χ 1 = 1 := ht.chi_one
  have hlong : ∀ {i : Fin 3}, i.val < 2 → (o8mDatum hirrQ).d'Scalar χ i = 1 :=
    fun {i} hi => o8mDatum_d'Scalar_long (hirrQ := hirrQ) hK hχ1 hi
  by_cases hne : ∃ h ∈ (o8mDatum hirrQ).H, χ h ≠ 1
  · have hd := o8mDatum_dScalar_short_of_ne (hirrQ := hirrQ) hK ht hne
    have hμ2 : μ 2 = 0 := by
      rcases ht.mu_eq 2 with h | h
      · exact h
      · rw [h, hd.2]
    refine ⟨fun s => ?_, fun _ => hμ2⟩
    rcases ht.mu_eq s with h | h
    · exact Or.inl h
    · by_cases hs : s.val < 2
      · exact Or.inr (by rw [h, hlong hs])
      · have hs2 : s = 2 := Fin.ext (by have := s.isLt; omega)
        rw [hs2] at h ⊢
        exact Or.inl (by rw [h, hd.2])
  · have htriv : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1 := by
      intro h hh
      by_contra hc
      exact hne ⟨h, hh, hc⟩
    have hd := o8mDatum_dScalar_short_of_trivial (hirrQ := hirrQ) hK htriv
    refine ⟨fun s => ?_, fun hcon => absurd hcon hne⟩
    rcases ht.mu_eq s with h | h
    · exact Or.inl h
    · by_cases hs : s.val < 2
      · exact Or.inr (by rw [h, hlong hs])
      · have hs2 : s = 2 := Fin.ext (by have := s.isLt; omega)
        rw [hs2] at h ⊢
        exact Or.inr (by rw [h, hd.2])

theorem omMinus_two_seventeen_le_finrank_of_pair (hK : Nat.card K = 2) {k : Type} [Field k]
    [CharP k 2] {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ) (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1)
    {i j : Fin 3} (hij : i ≠ j) (hi : μ i = 1) (hj : μ j = 1) :
    17 ≤ Module.finrank k V := by
  classical
  have hd1 : ∀ s : Fin 3, (o8mDatum hirrQ).dScalar χ s = 1 := by
    intro s
    by_cases hs : s.val < 2
    · exact o8mDatum_dScalar_long (hirrQ := hirrQ) hK ht.chi_one hs
    · have hs2 : s = 2 := Fin.ext (by have := s.isLt; omega)
      rw [hs2]
      exact (o8mDatum_dScalar_short_of_trivial (hirrQ := hirrQ) hK hχ).1
  have hcard : ({i, j} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h2 : ({i, j} : Finset (Fin 3)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
    omega
  obtain ⟨l, -, hlnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hli : l ≠ i := fun h => hlnot (by simp [h])
  have hlj : l ≠ j := fun h => hlnot (by simp [h])
  let : MulAction (coxeterMatrix (isFiniteType_cartanB 3)).Group (Fin 3 → ℤ) :=
    MulAction.compHom (Fin 3 → ℤ) (weylAction (isFiniteType_cartanB 3))
  have hv : ∀ s, μ s ≠ (o8mDatum hirrQ).dScalar χ s →
      o8mSimple s • (o8mWtPair l) = o8mWtPair l := by
    intro s hne
    have hsi : s ≠ i := fun h => hne (by rw [h, hi, hd1 i])
    have hsj : s ≠ j := fun h => hne (by rw [h, hj, hd1 j])
    have hsl : s = l := by
      apply Fin.ext
      have h1 : s.val ≠ i.val := fun h => hsi (Fin.ext h)
      have h2 : s.val ≠ j.val := fun h => hsj (Fin.ext h)
      have h3 : l.val ≠ i.val := fun h => hli (Fin.ext h)
      have h4 : l.val ≠ j.val := fun h => hlj (Fin.ext h)
      have h5 : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have := s.isLt; have := i.isLt; have := j.isLt; have := l.isLt
      omega
    rw [hsl]
    simpa [MulAction.compHom_smul_def, Module.End.smul_def, o8mAct] using o8mWtPair_fixed l
  obtain ⟨u, hu_mem, hu_inj⟩ := exists_seventeen_orbit_o8mWtPair l
  have hu : ∀ a, u a ∈ MulAction.orbit (coxeterMatrix (isFiniteType_cartanB 3)).Group
      (o8mWtPair l) := by
    intro a
    obtain ⟨w, hw⟩ := hu_mem a
    exact MulAction.mem_orbit_iff.mpr ⟨w, by
      simpa [MulAction.compHom_smul_def, Module.End.smul_def, o8mAct] using hw.symm⟩
  exact card_le_finrank_of_mem_orbit (D := o8mDatum hirrQ) hρ ht hv u hu hu_inj

private abbrev omMinusEndField {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) : Type _ :=
  Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule

private theorem omMinus_two_chi_ne_zero {k : Type} [Field k] [CharP k 2] {V : Type}
    [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} {y : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ)
    {h : spinGroup (quadMinus 4 K b c)} (hh : h ∈ (o8mDatum hirrQ).H) : χ h ≠ 0 := by
  intro h0
  have hmul := ht.chi_mul hh (inv_mem hh)
  rw [mul_inv_cancel, ht.chi_one, h0, zero_mul] at hmul
  exact zero_ne_one hmul.symm

private theorem omMinus_two_finrank_range_conj {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (g y : G) :
    Module.finrank F (LinearMap.range (ρ (g * y * g⁻¹) - 1)) =
      Module.finrank F (LinearMap.range (ρ y - 1)) := by
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[F] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

private theorem omMinus_two_k_orbit_bound {k : Type} [Field k] [CharP k 2] {V : Type}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ) {z : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ z χ μ) {v : Fin 3 → ℤ}
    (hv : ∀ s, μ s ≠ (o8mDatum hirrQ).dScalar χ s → o8mAct (o8mSimple s) v = v)
    (x : o8mW) {m : ℕ} (u : Fin m → (Fin 3 → ℤ))
    (hu_mem : ∀ a, ∃ w : o8mW, u a = o8mAct w v) (hinj : Function.Injective u)
    (hmove : ∀ a b, u a ≠ o8mAct x (u b)) :
    m ≤ Module.finrank k (LinearMap.range (ρ ((o8mDatum hirrQ).nW x) - 1)) := by
  let : MulAction (coxeterMatrix (isFiniteType_cartanB 3)).Group (Fin 3 → ℤ) :=
    { smul := fun w v => o8mAct w v
      one_smul := fun v => by
        show weylAction (isFiniteType_cartanB 3) 1 v = v
        rw [map_one, Module.End.one_apply]
      mul_smul := fun w w' v => by
        show weylAction (isFiniteType_cartanB 3) (w * w') v =
          weylAction (isFiniteType_cartanB 3) w (weylAction (isFiniteType_cartanB 3) w' v)
        rw [map_mul, Module.End.mul_apply] }
  have hv' : ∀ s : Fin 3, μ s ≠ (o8mDatum hirrQ).dScalar χ s → o8mSimple s • v = v :=
    fun s h => hv s h
  have hu : ∀ a, u a ∈ MulAction.orbit (coxeterMatrix (isFiniteType_cartanB 3)).Group v := by
    intro a
    obtain ⟨w, hw⟩ := hu_mem a
    exact MulAction.mem_orbit_iff.mpr ⟨w, hw.symm⟩
  have hmove' : ∀ a b, u a ≠ x • u b := fun a b h => hmove a b h
  exact le_finrank_range_sub_one_of_mem_orbit (D := o8mDatum hirrQ) hρ ht hv' x u hu hinj hmove'

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem omMinus_two_exists_equivariant_map (hK : Nat.card K = 2)
    {E k : Type} [Field E] [Field k] [CharP k 2] [Algebra E k]
    {W : Type} [AddCommGroup W] [Module E W] [Nontrivial W]
    (ρ : Representation E (spinGroup (quadMinus 4 K b c)) W)
    (hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k ρ))
    (φ : K →+* k) {z : k ⊗[E] W} {χ : spinGroup (quadMinus 4 K b c) → k}
    (ht : (o8mDatum hirrQ).IsCurtisType (CFSG.Theory.Representation.extendScalars k ρ) z χ
      (fun s => if s.val = 0 then 1 else 0))
    (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    ∃ f : W →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g w,
      f (ρ g w) = mat 4 g *ᵥ f w := by
  classical
  let : Algebra K k := φ.toAlgebra
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := o8mDatum hirrQ
  obtain ⟨β, hβ⟩ := D.iso_of_isCurtisType hsimp
    (SmallO8mCurtis.naturalRep_isSimple (by norm_num : 4 ≤ 4) hirrQ φ) ht
    (isCurtisType_omMinus_two_natural (hirrQ := hirrQ) hK φ hχ)
  obtain ⟨w, hw⟩ : ∃ w : W, w ≠ 0 := exists_ne 0
  let F : W →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → k) :=
    { toFun := fun w => β ((1 : k) ⊗ₜ[E] w)
      map_zero' := by simp
      map_add' := fun w w' => by simp [TensorProduct.tmul_add] }
  have hF : F ≠ 0 := by
    intro h
    have hzero : β ((1 : k) ⊗ₜ[E] w) = 0 := DFunLike.congr_fun h w
    have htzero := β.injective (hzero.trans (map_zero β).symm)
    exact hw ((Module.FaithfullyFlat.one_tmul_eq_zero_iff E W (A := k) w).mp htzero)
  let : DistribMulAction (spinGroup (quadMinus 4 K b c)) W :=
    { smul := fun g w => ρ g w
      one_smul := fun w => by change ρ 1 w = w; rw [map_one]; rfl
      mul_smul := fun g h w => by change ρ (g * h) w = ρ g (ρ h w); rw [map_mul]; rfl
      smul_zero := fun g => map_zero (ρ g)
      smul_add := fun g w w' => map_add (ρ g) w w' }
  have hFeq : ∀ (g : spinGroup (quadMinus 4 K b c)) (w : W),
      F (g • w) = (mat 4 g).map (algebraMap K k) *ᵥ F w := by
    intro g w
    have h := hβ g ((1 : k) ⊗ₜ[E] w)
    rw [CFSG.Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul,
      SmallO8mCurtis.naturalRep_apply] at h
    exact h
  exact CFSG.LieType.SpecialLinear.exists_addHom_of_extend (fun g => mat 4 g) F hF hFeq

private theorem omMinus_two_exists_ringHom {K k : Type} [Field K] [Finite K] [CharP K 2]
    [Field k] [CharP k 2] (hK : Nat.card K = 2) : Nonempty (K →+* k) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
    exact hK
  let e : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨(ZMod.castHom (dvd_refl 2) k).comp e.toRingHom⟩

private theorem omMinus_two_four_le_of_four_le_k {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) G V} [ρ.IsIrreducible] {s : ℕ}
    (hE : Nat.card (omMinusEndField ρ) = 2 ^ s)
    (hs : 1 ≤ s) {g : G} {k : Type} [Field k]
    [Algebra (omMinusEndField ρ) k]
    (h : 4 ≤ Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g - 1))) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := by
  have hrank :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.finrank_range_sub_one_eq_mul
      (s := s) ρ hE k g
  calc (4 : ℕ) = 1 * 4 := (one_mul 4).symm
    _ ≤ s * Module.finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g - 1)) :=
      Nat.mul_le_mul hs h
    _ = Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := hrank.symm

private theorem omMinus_two_four_le_of_two_le_k {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) G V} [ρ.IsIrreducible] {s : ℕ}
    (hE : Nat.card (omMinusEndField ρ) = 2 ^ s)
    (hs : 2 ≤ s) {g : G} {k : Type} [Field k]
    [Algebra (omMinusEndField ρ) k]
    (h : 2 ≤ Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g - 1))) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := by
  have hrank :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.finrank_range_sub_one_eq_mul
      (s := s) ρ hE k g
  calc (4 : ℕ) = 2 * 2 := rfl
    _ ≤ s * Module.finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g - 1)) :=
      Nat.mul_le_mul hs h
    _ = Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := hrank.symm

private theorem omMinus_two_conj_theta :
    ∃ h ∈ (o8mDatum hirrQ).H,
      ((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1)⁻¹ *
        (o8mDatum hirrQ).n 0 *
        ((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1) =
      (o8mDatum hirrQ).nW ((o8mSimple 1 * o8mSimple 2 * o8mSimple 1)⁻¹ * o8mSimple 0 *
        (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)) * h := by
  classical
  let D := o8mDatum hirrQ
  let A := D.n 1 * D.n 2 * D.n 1
  set sθ : (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)⁻¹ * o8mSimple 0 *
      (o8mSimple 1 * o8mSimple 2 * o8mSimple 1) with hsθdef
  obtain ⟨h₂, hh₂, e₂⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.nW_mul D (o8mSimple 0)
      (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)
  obtain ⟨h₃, hh₃, e₃⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.nW_inv_mul D
      (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)
      (o8mSimple 0 * (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))
  refine ⟨h₃ * h₂, mul_mem hh₃ hh₂, ?_⟩
  have hn0 : D.nW (o8mSimple 0) = D.n 0 := by
    simpa using o8mDatum_nW_simple (hirrQ := hirrQ) 0
  have hA : D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1) = A := by
    simpa [A] using o8mDatum_nW_one_two_one (hirrQ := hirrQ)
  have hsθ : (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)⁻¹ *
      (o8mSimple 0 * (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)) = sθ := by
    simp only [sθ]; group
  have hkey : (D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))⁻¹ *
      D.nW (o8mSimple 0 * (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)) = D.nW sθ * h₃ := by
    rw [e₃, hsθ]
  calc A⁻¹ * D.n 0 * A
      = (D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))⁻¹ *
          D.nW (o8mSimple 0) * D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1) := by
        rw [← hA, ← hn0]
    _ = (D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))⁻¹ *
          (D.nW (o8mSimple 0) * D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)) := by
        group
    _ = (D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))⁻¹ *
          (D.nW (o8mSimple 0 * (o8mSimple 1 * o8mSimple 2 * o8mSimple 1)) * h₂) := by
        rw [e₂]
    _ = ((D.nW (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))⁻¹ *
          D.nW (o8mSimple 0 * (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))) * h₂ := by
        group
    _ = (D.nW sθ * h₃) * h₂ := by rw [hkey]
    _ = D.nW sθ * (h₃ * h₂) := by group

private theorem omMinus_two_nW_word_mul_ne {k : Type} [Field k] [CharP k 2] {V' : Type}
    [AddCommGroup V'] [Module k V'] [Module.Finite k V']
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V'} (hρ : IsSimpleRep ρ) {z : V'}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ z χ μ)
    (hv : ∀ t, μ t ≠ (o8mDatum hirrQ).dScalar χ t → o8mAct (o8mSimple t) (o8mWt 2) = o8mWt 2)
    {h : spinGroup (quadMinus 4 K b c)} (hh : h ∈ (o8mDatum hirrQ).H) {ω : List (Fin 3)}
    (hωred : (coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.IsReduced ω)
    (hnotfix : o8mAct ((coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.wordProd ω)
      (o8mWt 2) ≠ o8mWt 2) :
    ρ ((o8mDatum hirrQ).nW ((coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.wordProd ω) *
      h) z ≠ z := by
  intro hfix
  let D := o8mDatum hirrQ
  let : MulAction (coxeterMatrix (isFiniteType_cartanB 3)).Group (Fin 3 → ℤ) :=
    { smul := fun w v => o8mAct w v
      one_smul := fun v => by
        show weylAction (isFiniteType_cartanB 3) 1 v = v
        rw [map_one, Module.End.one_apply]
      mul_smul := fun w w' v => by
        show weylAction (isFiniteType_cartanB 3) (w * w') v =
          weylAction (isFiniteType_cartanB 3) w (weylAction (isFiniteType_cartanB 3) w' v)
        rw [map_mul, Module.End.mul_apply] }
  obtain ⟨t, htmem, htsep⟩ := exists_mem_mu_eq_dScalar_of_smul_ne (D := D) (v := o8mWt 2)
    (fun t htne => hv t htne) hnotfix
  have hcoinv : D.coinvScalar χ μ ω = 0 := by
    unfold CurtisDatum.coinvScalar
    exact List.prod_eq_zero (List.mem_map.mpr ⟨t, htmem, sub_eq_zero.mpr htsep⟩)
  obtain ⟨f, hf, hfy⟩ := D.exists_form hρ ht.1 ht.2.1
  have hform : f (ρ (D.nW ((coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.wordProd ω) *
      h) z) = 0 := by
    rw [CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.form_nW_mul D ρ ht hf hfy hωred hh,
      hcoinv, mul_zero]
  have h1 : (0 : k) = 1 := by rw [← hform, hfix, hfy]
  exact one_ne_zero h1.symm

private theorem omMinus_two_theta_ne {k : Type} [Field k] [CharP k 2] {V : Type}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ) {z : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ z χ μ)
    (hv : ∀ t, μ t ≠ (o8mDatum hirrQ).dScalar χ t → o8mAct (o8mSimple t) (o8mWt 2) = o8mWt 2) :
    ρ (((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1)⁻¹ *
        (o8mDatum hirrQ).n 0 *
        ((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1)) z ≠ z := by
  classical
  let D := o8mDatum hirrQ
  let A := D.n 1 * D.n 2 * D.n 1
  obtain ⟨h, hh, htθeq⟩ := omMinus_two_conj_theta (hirrQ := hirrQ)
  obtain ⟨ω, hωred, hωprod⟩ :=
    (coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.exists_isReduced
      ((o8mSimple 1 * o8mSimple 2 * o8mSimple 1)⁻¹ * o8mSimple 0 *
        (o8mSimple 1 * o8mSimple 2 * o8mSimple 1))
  have hnotfix : o8mAct ((coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.wordProd ω)
      (o8mWt 2) ≠ o8mWt 2 := by
    rw [← hωprod]
    exact weylAction_theta_o8mWt_two_ne
  have hne := omMinus_two_nW_word_mul_ne (hirrQ := hirrQ) hρ ht hv hh hωred hnotfix
  rw [show ((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1)⁻¹ *
      (o8mDatum hirrQ).n 0 *
      ((o8mDatum hirrQ).n 1 * (o8mDatum hirrQ).n 2 * (o8mDatum hirrQ).n 1) =
      D.nW ((coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem.wordProd ω) * h by
    rw [htθeq, hωprod]]
  exact hne

private theorem omMinus_two_hb_of_three {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {g0 g2 g02 : G}
    (h0 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ g0 - 1)))
    (h2 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ g2 - 1)))
    (h02 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ g02 - 1))) :
    ∀ x, (x = g0 ∨ x = g2 ∨ x = g02) →
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact h0
  · exact h2
  · exact h02

private theorem omMinus_two_four_le_of_three {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V}
    {y : spinGroup (quadMinus 4 K b c)} (hy : y * y = 1) (hy1 : y ≠ 1)
    (h0 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ ((o8mDatum hirrQ).n 0) - 1)))
    (h2 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ ((o8mDatum hirrQ).n 2) - 1)))
    (h02 : 4 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (ρ ((o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) - 1))) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  have hb := omMinus_two_hb_of_three (ρ := ρ) (g0 := (o8mDatum hirrQ).n 0)
    (g2 := (o8mDatum hirrQ).n 2) (g02 := (o8mDatum hirrQ).n 0 * (o8mDatum hirrQ).n 2) h0 h2 h02
  obtain ⟨g, hg | hg | hg⟩ := omMinus_exists_conj_weyl (hirrQ := hirrQ) hy hy1
  · rw [← omMinus_two_finrank_range_conj ρ g y, hg]
    exact hb _ (Or.inl rfl)
  · rw [← omMinus_two_finrank_range_conj ρ g y, hg]
    exact hb _ (Or.inr (Or.inl rfl))
  · rw [← omMinus_two_finrank_range_conj ρ g y, hg]
    exact hb _ (Or.inr (Or.inr rfl))

private theorem omMinus_two_chi_triv_d {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V}
    {y : spinGroup (quadMinus 4 K b c)} (hy : y * y = 1) (hy1 : y ≠ 1)
    {k : Type} [Field k] [CharP k 2] {V' : Type} [AddCommGroup V'] [Module k V']
    [Module.Finite k V'] {τ : Representation k (spinGroup (quadMinus 4 K b c)) V'}
    (hτ : IsSimpleRep τ) {z : V'} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType τ z χ μ)
    (hμ1 : μ 1 = 1) (hd1 : ∀ t : Fin 3, (o8mDatum hirrQ).dScalar χ t = 1)
    (hrk : ∀ x : spinGroup (quadMinus 4 K b c), 4 ≤ Module.finrank k
      (LinearMap.range (τ x - 1)) → 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1))) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  let D := o8mDatum hirrQ
  have hn0 : D.nW (o8mSimple 0) = D.n 0 := by
    simpa using o8mDatum_nW_simple (hirrQ := hirrQ) 0
  have hn2 : D.nW (o8mSimple 2) = D.n 2 := by
    simpa using o8mDatum_nW_simple (hirrQ := hirrQ) 2
  have hn02 : D.nW (o8mSimple 0 * o8mSimple 2) = D.n 0 * D.n 2 := by
    simpa using o8mDatum_nW_zero_two (hirrQ := hirrQ)
  have hv_d : ∀ t, μ t ≠ D.dScalar χ t → o8mAct (o8mSimple t) (o8mWt 1) = o8mWt 1 := by
    intro t htne
    exact o8mWt_fixed (i := t) (j := 1) (fun h => htne (by rw [h, hμ1, hd1 1]))
  obtain ⟨u0, hu0_mem, hu0_inj, hu0_move⟩ := exists_four_orbit_o8mWt_one (Or.inl rfl)
  have hk0 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 0) - 1)) := by
    rw [← hn0]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_d (o8mSimple 0) u0
      hu0_mem hu0_inj hu0_move
  obtain ⟨u2, hu2_mem, hu2_inj, hu2_move⟩ :=
    exists_four_orbit_o8mWt_one (Or.inr (Or.inl rfl))
  have hk2 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 2) - 1)) := by
    rw [← hn2]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_d (o8mSimple 2) u2
      hu2_mem hu2_inj hu2_move
  obtain ⟨u02, hu02_mem, hu02_inj, hu02_move⟩ :=
    exists_four_orbit_o8mWt_one (Or.inr (Or.inr rfl))
  have hk02 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 0 * D.n 2) - 1)) := by
    rw [← hn02]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_d (o8mSimple 0 * o8mSimple 2) u02
      hu02_mem hu02_inj hu02_move
  exact Or.inr (omMinus_two_four_le_of_three (hirrQ := hirrQ) hy hy1
    (hrk (D.n 0) hk0) (hrk (D.n 2) hk2) (hrk (D.n 0 * D.n 2) hk02))

private theorem omMinus_two_theta_bound {k : Type} [Field k] [CharP k 2]
    {V' : Type} [AddCommGroup V'] [Module k V'] [Module.Finite k V']
    {τ : Representation k (spinGroup (quadMinus 4 K b c)) V'} (hτ : IsSimpleRep τ)
    {z : V'} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType τ z χ μ) (hμ2 : μ 2 = 1)
    (hv : ∀ t, μ t ≠ (o8mDatum hirrQ).dScalar χ t → o8mAct (o8mSimple t) (o8mWt 2) = o8mWt 2)
    (hK : Nat.card K = 2) :
    4 ≤ Module.finrank k (LinearMap.range (τ ((o8mDatum hirrQ).n 0) - 1)) := by
  classical
  let D := o8mDatum hirrQ
  let A := D.n 1 * D.n 2 * D.n 1
  let tθ := A⁻¹ * D.n 0 * A
  have hcommX := omMinus_commute_theta_X_short (hirrQ := hirrQ)
  have hcommn := omMinus_commute_theta_n_short (hirrQ := hirrQ)
  have hmove := omMinus_two_theta_ne (hirrQ := hirrQ) hτ ht hv
  have hX2 := o8mDatum_card_X_short (hirrQ := hirrQ) hK
  have hkθ : 4 ≤ Module.finrank k (LinearMap.range (τ tθ - 1)) := by
    have hcard := card_X_le_finrank_range_sub_one_of_commute (D := D) ht
      (s := 2) (by rw [hμ2]; exact one_ne_zero) hcommX hcommn hmove
    exact Nat.le_trans (le_of_eq hX2.symm) hcard
  have hconj := omMinus_two_finrank_range_conj τ A⁻¹ (D.n 0)
  have hAinv : A⁻¹ * D.n 0 * (A⁻¹)⁻¹ = tθ := by rw [inv_inv]
  rw [hAinv] at hconj
  exact hconj ▸ hkθ

private theorem omMinus_two_chi_triv_e (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V}
    {y : spinGroup (quadMinus 4 K b c)} (hy : y * y = 1) (hy1 : y ≠ 1)
    {k : Type} [Field k] [CharP k 2] {V' : Type} [AddCommGroup V'] [Module k V']
    [Module.Finite k V'] {τ : Representation k (spinGroup (quadMinus 4 K b c)) V'}
    (hτ : IsSimpleRep τ) {z : V'} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType τ z χ μ)
    (hμ2 : μ 2 = 1) (hd1 : ∀ t : Fin 3, (o8mDatum hirrQ).dScalar χ t = 1)
    (hrk : ∀ x : spinGroup (quadMinus 4 K b c), 4 ≤ Module.finrank k
      (LinearMap.range (τ x - 1)) → 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1))) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  let D := o8mDatum hirrQ
  have hn0 : D.nW (o8mSimple 0) = D.n 0 := by
    simpa using o8mDatum_nW_simple (hirrQ := hirrQ) 0
  have hn2 : D.nW (o8mSimple 2) = D.n 2 := by
    simpa using o8mDatum_nW_simple (hirrQ := hirrQ) 2
  have hn02 : D.nW (o8mSimple 0 * o8mSimple 2) = D.n 0 * D.n 2 := by
    simpa using o8mDatum_nW_zero_two (hirrQ := hirrQ)
  have hv_e : ∀ t, μ t ≠ D.dScalar χ t → o8mAct (o8mSimple t) (o8mWt 2) = o8mWt 2 := by
    intro t htne
    exact o8mWt_fixed (i := t) (j := 2) (fun h => htne (by rw [h, hμ2, hd1 2]))
  obtain ⟨u2, hu2_mem, hu2_inj, hu2_move⟩ := exists_four_orbit_o8mWt_two (Or.inl rfl)
  have hk2 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 2) - 1)) := by
    rw [← hn2]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_e (o8mSimple 2) u2
      hu2_mem hu2_inj hu2_move
  obtain ⟨u02, hu02_mem, hu02_inj, hu02_move⟩ := exists_four_orbit_o8mWt_two (Or.inr rfl)
  have hk02 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 0 * D.n 2) - 1)) := by
    rw [← hn02]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_e (o8mSimple 0 * o8mSimple 2) u02
      hu02_mem hu02_inj hu02_move
  have hk0 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 0) - 1)) :=
    omMinus_two_theta_bound (hirrQ := hirrQ) hτ ht hμ2 hv_e hK
  exact Or.inr (omMinus_two_four_le_of_three (hirrQ := hirrQ) hy hy1
    (hrk (D.n 0) hk0) (hrk (D.n 2) hk2) (hrk (D.n 0 * D.n 2) hk02))

private theorem omMinus_two_chi_ne_le (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V}
    {y : spinGroup (quadMinus 4 K b c)} (hy : y * y = 1) (hy1 : y ≠ 1)
    {k : Type} [Field k] [CharP k 2] {V' : Type} [AddCommGroup V'] [Module k V']
    [Module.Finite k V'] {τ : Representation k (spinGroup (quadMinus 4 K b c)) V'}
    (hτ : IsSimpleRep τ) {z : V'} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType τ z χ μ)
    (hχne : ∃ h ∈ (o8mDatum hirrQ).H, χ h ≠ 1)
    (hrk4 : ∀ x : spinGroup (quadMinus 4 K b c), 4 ≤ Module.finrank k
      (LinearMap.range (τ x - 1)) → 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)))
    (hrk2 : ∀ x : spinGroup (quadMinus 4 K b c), 2 ≤ Module.finrank k
      (LinearMap.range (τ x - 1)) → 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1))) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  let D := o8mDatum hirrQ
  have hn0 : D.nW (o8mSimple 0) = D.n 0 := by
    simpa using o8mDatum_nW_simple (hirrQ := hirrQ) 0
  have hn2 : D.nW (o8mSimple 2) = D.n 2 := by
    simpa using o8mDatum_nW_simple (hirrQ := hirrQ) 2
  have hn02 : D.nW (o8mSimple 0 * o8mSimple 2) = D.n 0 * D.n 2 := by
    simpa using o8mDatum_nW_zero_two (hirrQ := hirrQ)
  have hμ2 : μ 2 = 0 := (omMinus_two_mu_cases (hirrQ := hirrQ) hK ht).2 hχne
  have hd2 := o8mDatum_dScalar_short_of_ne (hirrQ := hirrQ) hK ht hχne
  have hv_a : ∀ t, μ t ≠ D.dScalar χ t → o8mAct (o8mSimple t) (o8mWt 2) = o8mWt 2 := by
    intro t htne
    exact o8mWt_fixed (i := t) (j := 2) (fun h => htne (by rw [h, hμ2, hd2.1]))
  obtain ⟨u2, hu2_mem, hu2_inj, hu2_move⟩ := exists_four_orbit_o8mWt_two (Or.inl rfl)
  have hk2 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 2) - 1)) := by
    rw [← hn2]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_a (o8mSimple 2) u2
      hu2_mem hu2_inj hu2_move
  obtain ⟨u02, hu02_mem, hu02_inj, hu02_move⟩ := exists_four_orbit_o8mWt_two (Or.inr rfl)
  have hk02 : 4 ≤ Module.finrank k (LinearMap.range (τ (D.n 0 * D.n 2) - 1)) := by
    rw [← hn02]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_a (o8mSimple 0 * o8mSimple 2) u02
      hu02_mem hu02_inj hu02_move
  obtain ⟨u0, hu0_mem, hu0_inj, hu0_move⟩ := exists_two_orbit_o8mWt_two
  have hk0 : 2 ≤ Module.finrank k (LinearMap.range (τ (D.n 0) - 1)) := by
    rw [← hn0]
    exact omMinus_two_k_orbit_bound (hirrQ := hirrQ) hτ ht hv_a (o8mSimple 0) u0
      hu0_mem hu0_inj hu0_move
  exact Or.inr (omMinus_two_four_le_of_three (hirrQ := hirrQ) hy hy1
    (hrk2 (D.n 0) hk0) (hrk4 (D.n 2) hk2) (hrk4 (D.n 0 * D.n 2) hk02))

private theorem omMinus_two_dScalar_eq_one_of_trivial (hK : Nat.card K = 2)
    {k : Type} [Field k] [CharP k 2] {χ : spinGroup (quadMinus 4 K b c) → k} (hχ1 : χ 1 = 1)
    (hχtriv : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    ∀ t : Fin 3, (o8mDatum hirrQ).dScalar χ t = 1 := by
  intro t
  by_cases ht2 : t.val < 2
  · exact o8mDatum_dScalar_long (hirrQ := hirrQ) hK hχ1 ht2
  · have ht3 : t = 2 := Fin.ext (by have := t.isLt; omega)
    rw [ht3]
    exact (o8mDatum_dScalar_short_of_trivial (hirrQ := hirrQ) hK hχtriv).1

private theorem omMinus_two_trivial_of_mu_zero {k : Type} [Field k] [CharP k 2] {V' : Type}
    [AddCommGroup V'] [Module k V']
    {τ : Representation k (spinGroup (quadMinus 4 K b c)) V'} (hτ : IsSimpleRep τ)
    {z : V'} {χ : spinGroup (quadMinus 4 K b c) → k}
    (ht : (o8mDatum hirrQ).IsCurtisType τ z χ (0 : Fin 3 → k))
    (hχtriv : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) : ∀ g, τ g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ := (o8mDatum hirrQ).iso_of_isCurtisType hτ
    (omMinus_isSimpleRep_trivial (k := k) (spinGroup (quadMinus 4 K b c))) ht
    (isCurtisType_omMinus_two_trivial (hirrQ := hirrQ) hχtriv)
  intro g
  apply LinearMap.ext
  intro v
  simpa using β.injective (by simpa using hβ g v)

private theorem omMinus_two_mu_zero_absurd {k : Type} [Field k] [CharP k 2] {V' : Type}
    [AddCommGroup V'] [Module k V']
    {τ : Representation k (spinGroup (quadMinus 4 K b c)) V'} (hτ : IsSimpleRep τ)
    {z : V'} {χ : spinGroup (quadMinus 4 K b c) → k}
    (ht : (o8mDatum hirrQ).IsCurtisType τ z χ (0 : Fin 3 → k))
    (hχtriv : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) (hτ1 : ∃ g, τ g ≠ 1) : False := by
  obtain ⟨g, hg⟩ := hτ1
  exact hg (omMinus_two_trivial_of_mu_zero (hirrQ := hirrQ) hτ ht hχtriv g)

private theorem omMinus_two_chi_triv_cases (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V}
    {y : spinGroup (quadMinus 4 K b c)} (hy : y * y = 1) (hy1 : y ≠ 1)
    {k : Type} [Field k] [CharP k 2] {V' : Type} [AddCommGroup V'] [Module k V']
    [Module.Finite k V'] {τ : Representation k (spinGroup (quadMinus 4 K b c)) V'}
    (hτ : IsSimpleRep τ) {z : V'} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType τ z χ μ)
    (hχtriv : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) (hτ1 : ∃ g, τ g ≠ 1)
    (hnat : μ = (fun t : Fin 3 => if t.val = 0 then 1 else 0) →
      ∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v)
    (hrk : ∀ x : spinGroup (quadMinus 4 K b c), 4 ≤ Module.finrank k
      (LinearMap.range (τ x - 1)) → 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1))) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  have hd1 := omMinus_two_dScalar_eq_one_of_trivial (hirrQ := hirrQ) hK ht.chi_one hχtriv
  have hμ01 := (omMinus_two_mu_cases (hirrQ := hirrQ) (k := k) (ρ := τ) (y := z)
    (χ := χ) (μ := μ) hK ht).1
  by_cases hμ1 : μ 1 = 1
  · exact omMinus_two_chi_triv_d (hirrQ := hirrQ) hy hy1 hτ ht hμ1 hd1 hrk
  by_cases hμ2 : μ 2 = 1
  · exact omMinus_two_chi_triv_e (hirrQ := hirrQ) hK hy hy1 hτ ht hμ2 hd1 hrk
  · have hμ1z : μ 1 = 0 := (hμ01 1).resolve_right hμ1
    have hμ2z : μ 2 = 0 := (hμ01 2).resolve_right hμ2
    rcases hμ01 0 with hμ0 | hμ0
    · exfalso
      have hμzero : μ = 0 := by
        funext t
        fin_cases t
        · exact hμ0
        · exact hμ1z
        · exact hμ2z
      rw [hμzero] at ht
      exact omMinus_two_mu_zero_absurd (hirrQ := hirrQ) hτ ht hχtriv hτ1
    · have hμnat : μ = (fun t : Fin 3 => if t.val = 0 then 1 else 0) := by
        funext t
        fin_cases t
        · simpa using hμ0
        · simpa using hμ1z
        · simpa using hμ2z
      exact Or.inl (hnat hμnat)

private theorem omMinus_two_chi_triv_le (hK : Nat.card K = 2) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} [ρ.IsIrreducible]
    (hρ : IsSimpleRep ρ) (hρ1 : ∃ g, ρ g ≠ 1) {y : spinGroup (quadMinus 4 K b c)}
    (hy : y * y = 1) (hy1 : y ≠ 1) {k : Type} [Field k] [CharP k 2]
    [Algebra (omMinusEndField ρ) k] {s : ℕ}
    (hE : Nat.card (omMinusEndField ρ) = 2 ^ s) (hs0 : 0 < s)
    {z : k ⊗[omMinusEndField ρ] ρ.asModule}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) z χ μ)
    (hχtriv : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  have : Finite V := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) V)
  have : Nontrivial ρ.asModule := hρ.1
  let E := omMinusEndField ρ
  have : Module.Finite E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have : Module.Finite k (k ⊗[E] ρ.asModule) := Module.Finite.base_change E k ρ.asModule
  let τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  have hτ : IsSimpleRep τ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  have hτ1 : ∃ g, τ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hρ1
    exact ⟨g, fun h => hg
      ((CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
        ρ k g).mp h)⟩
  have hnat : μ = (fun t : Fin 3 => if t.val = 0 then 1 else 0) →
      ∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v := by
    intro hμnat
    obtain ⟨φ⟩ := omMinus_two_exists_ringHom (K := K) (k := k) hK
    rw [hμnat] at ht
    obtain ⟨f, hf, hfeq⟩ := omMinus_two_exists_equivariant_map (hirrQ := hirrQ) hK
      (ρ := CFSG.endFieldRep ρ) hτ φ ht hχtriv
    refine ⟨f.comp ((ρ.asModuleEquiv.symm : V →ₗ[ZMod 2] ρ.asModule).toAddMonoidHom), ?_, ?_⟩
    · intro hzero
      apply hf
      refine AddMonoidHom.ext fun w => ?_
      obtain ⟨v, rfl⟩ := ρ.asModuleEquiv.symm.surjective w
      exact DFunLike.congr_fun hzero v
    · intro g v
      change f (ρ.asModuleEquiv.symm (ρ g v)) =
        mat 4 g *ᵥ f (ρ.asModuleEquiv.symm v)
      have h := hfeq g (ρ.asModuleEquiv.symm v)
      simpa [CFSG.endFieldRep_apply] using h
  exact omMinus_two_chi_triv_cases (hirrQ := hirrQ) hK hy hy1 hτ ht hχtriv hτ1 hnat
    (fun x hx => omMinus_two_four_le_of_four_le_k hE hs0 hx)

private theorem omMinus_two_card_ne_two_of_mem {G : Type*} {E k : Type} [Field E] [Finite E]
    [Field k] [Algebra E k] {χ : G → k} {h : G}
    (hmem : χ h ∈ (algebraMap E k).fieldRange) (h0 : χ h ≠ 0) (hne : χ h ≠ 1) :
    Nat.card E ≠ 2 := by
  classical
  intro hE2
  let : Fintype E := Fintype.ofFinite E
  have hle : Fintype.card E ≤ 2 := by rw [← Nat.card_eq_fintype_card, hE2]
  have huniv := Finset.univ_of_card_le_two (R := E) hle
  obtain ⟨r, hr⟩ := RingHom.mem_fieldRange.mp hmem
  have hr01 : r = 0 ∨ r = 1 := by
    have hx : r ∈ ({0, 1} : Finset E) := by rw [← huniv]; exact Finset.mem_univ r
    simpa using hx
  rcases hr01 with rfl | rfl
  · rw [map_zero] at hr
    exact h0 hr.symm
  · rw [map_one] at hr
    exact hne hr.symm

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
include hirrQ in
theorem omMinus_two_natural_or_four_le (hK : Nat.card K = 2) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) {y : spinGroup (quadMinus 4 K b c)} (hy : y * y = 1) (hy1 : y ≠ 1) :
    (∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  classical
  let D := o8mDatum hirrQ
  have : ρ.IsIrreducible := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mpr hρ
  have : Finite V := Module.finite_iff_finite.mp (inferInstance : Module.Finite (ZMod 2) V)
  let E := omMinusEndField ρ
  have : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  let k := AlgebraicClosure E
  have : Nontrivial ρ.asModule := hρ.1
  have : Module.Finite E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have : Module.Finite k (k ⊗[E] ρ.asModule) := Module.Finite.base_change E k ρ.asModule
  obtain ⟨s, hs0, hE⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.exists_card_endField_eq_two_pow ρ
  let τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  have hτ : IsSimpleRep τ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  have : Finite (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanB 3)
  obtain ⟨z, χ, μ, ht⟩ := D.exists_isCurtisType
    (SmallO8mCurtis.curtisDatum_splitOver (K := K) (k := k) hirrQ) hτ
  by_cases hχtriv : ∀ h ∈ D.H, χ h = 1
  · exact omMinus_two_chi_triv_le (hirrQ := hirrQ) hK hρ hρ1 hy hy1 hE hs0 ht hχtriv
  · push Not at hχtriv
    have hcardE : Nat.card E ≠ 2 := by
      obtain ⟨h, hh, hhne⟩ := hχtriv
      have h0 := omMinus_two_chi_ne_zero (hirrQ := hirrQ) ht hh
      have hmem : χ h ∈ (algebraMap E k).fieldRange := by
        rw [CFSG.HardMathSupport.GuralnickMalle.isCurtisType_fieldRange_eq_closure ρ D k ht]
        exact Subfield.subset_closure ⟨h, hh, rfl⟩
      exact omMinus_two_card_ne_two_of_mem hmem h0 hhne
    have hs2 : 2 ≤ s := by
      have hne : s ≠ 1 := fun h1 => hcardE (by rw [hE, h1]; norm_num)
      omega
    exact omMinus_two_chi_ne_le (hirrQ := hirrQ) hK hy hy1 hτ ht hχtriv
      (fun x hx => omMinus_two_four_le_of_four_le_k hE hs0 hx)
      (fun x hx => omMinus_two_four_le_of_two_le_k hE hs2 hx)

end CFSG.LocalAnalysis.WeakClosure81
