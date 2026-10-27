module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestBlock

public section

open Polynomial Module

namespace CFSG.StandardType

namespace SpNS

section Cyc

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {g : K[X]}

@[expose] noncomputable def kerRestr (z : Module.End K V) (g : K[X]) :
    Module.End K (LinearMap.ker (aeval z g)) :=
  z.restrict (OrdPNS.mapsTo_ker_aeval (Commute.refl z) g)

theorem aeval_kerRestr (z : Module.End K V) (g : K[X]) : aeval (kerRestr z g) g = 0 :=
  LinearMap.ext fun w => Subtype.ext (by
    rw [kerRestr, OrdPNS.coe_aeval_restrict_apply]
    exact w.2)

@[expose] noncomputable def lAct (z : Module.End K V) (g : K[X]) :
    AdjoinRoot g →ₐ[K] Module.End K (LinearMap.ker (aeval z g)) :=
  Ideal.Quotient.liftₐ (Ideal.span {g}) (aeval (kerRestr z g)) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, aeval_kerRestr, mul_zero])

theorem lAct_mk (z : Module.End K V) (P : K[X]) :
    lAct z g (AdjoinRoot.mk g P) = aeval (kerRestr z g) P := rfl

theorem coe_lAct_mk (z : Module.End K V) (P : K[X]) (w : LinearMap.ker (aeval z g)) :
    ((lAct z g (AdjoinRoot.mk g P) w : LinearMap.ker (aeval z g)) : V) = aeval z P (w : V) := by
  rw [lAct_mk, kerRestr, OrdPNS.coe_aeval_restrict_apply]

@[expose] noncomputable def cycMap (z : Module.End K V) (v : V) (hv : aeval z g v = 0) :
    AdjoinRoot g →ₗ[K] V :=
  (LinearMap.ker (aeval z g)).subtype ∘ₗ
    (LinearMap.applyₗ (⟨v, hv⟩ : LinearMap.ker (aeval z g))) ∘ₗ (lAct z g).toLinearMap

theorem cycMap_apply (z : Module.End K V) (v : V) (hv : aeval z g v = 0) (μ : AdjoinRoot g) :
    cycMap z v hv μ = ((lAct z g μ ⟨v, hv⟩ : LinearMap.ker (aeval z g)) : V) := rfl

theorem cycMap_mk (z : Module.End K V) (v : V) (hv : aeval z g v = 0) (P : K[X]) :
    cycMap z v hv (AdjoinRoot.mk g P) = aeval z P v :=
  coe_lAct_mk z P ⟨v, hv⟩

theorem aeval_cycMap (z : Module.End K V) (v : V) (hv : aeval z g v = 0) (μ : AdjoinRoot g) :
    aeval z g (cycMap z v hv μ) = 0 :=
  (lAct z g μ ⟨v, hv⟩).2

theorem cycMap_one (z : Module.End K V) (v : V) (hv : aeval z g v = 0) :
    cycMap z v hv 1 = v := by
  rw [← map_one (AdjoinRoot.mk g), cycMap_mk, map_one, Module.End.one_apply]

theorem cycMap_mk_mul (z : Module.End K V) (v : V) (hv : aeval z g v = 0) (Q : K[X])
    (μ : AdjoinRoot g) : cycMap z v hv (AdjoinRoot.mk g Q * μ) = aeval z Q (cycMap z v hv μ) := by
  induction μ using AdjoinRoot.induction_on with
  | ih P => rw [← map_mul, cycMap_mk, cycMap_mk, map_mul, Module.End.mul_apply]

theorem cycMap_root_mul (z : Module.End K V) (v : V) (hv : aeval z g v = 0) (μ : AdjoinRoot g) :
    cycMap z v hv (AdjoinRoot.root g * μ) = z (cycMap z v hv μ) := by
  rw [← AdjoinRoot.mk_X, cycMap_mk_mul, aeval_X]

theorem cycMap_root_pow_mul (z : Module.End K V) (v : V) (hv : aeval z g v = 0) (m : ℕ)
    (μ : AdjoinRoot g) : cycMap z v hv (AdjoinRoot.root g ^ m * μ) = (z ^ m) (cycMap z v hv μ) := by
  rw [← AdjoinRoot.mk_X, ← map_pow, cycMap_mk_mul, map_pow, aeval_X]

theorem aeval_mem_of_forall_mem {R : Submodule K V} {z : Module.End K V}
    (hR : ∀ r ∈ R, z r ∈ R) (P : K[X]) {r : V} (hr : r ∈ R) : aeval z P r ∈ R := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, LinearMap.add_apply]
    exact R.add_mem hP hQ
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine R.smul_mem c ?_
    induction n with
    | zero => rwa [pow_zero, Module.End.one_apply]
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hR _ ih

theorem apply_cycMap {z x : Module.End K V} (hxz : Commute x z) {v : V} (hv : aeval z g v = 0)
    {a : ℕ} (hxv : x v = (z ^ a) v) (μ : AdjoinRoot g) :
    x (cycMap z v hv μ) = cycMap z v hv (AdjoinRoot.root g ^ a * μ) := by
  induction μ using AdjoinRoot.induction_on with
  | ih P =>
    have h1 : x (aeval z P v) = aeval z P (x v) := by
      rw [← Module.End.mul_apply, ← (OrdPNS.commute_aeval hxz.symm P).eq, Module.End.mul_apply]
    have h2 : aeval z P ((z ^ a) v) = (z ^ a) (aeval z P v) := by
      rw [← Module.End.mul_apply, ((OrdPNS.commute_aeval (Commute.refl z) P).pow_right a).eq,
        Module.End.mul_apply]
    rw [cycMap_mk, cycMap_root_pow_mul, cycMap_mk, h1, hxv, h2]

variable [Fact (Irreducible g)]

theorem cycMap_injective (z : Module.End K V) {v : V} (hv : aeval z g v = 0) (hv0 : v ≠ 0) :
    Function.Injective (cycMap z v hv) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro μ hμ
  by_contra hne
  obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective μ⁻¹
  apply hv0
  rw [← cycMap_one z v hv, ← inv_mul_cancel₀ hne, ← hQ, cycMap_mk_mul, hμ, map_zero]

theorem cycMap_mem_of_mem (z : Module.End K V) {v : V} (hv : aeval z g v = 0)
    {R : Submodule K V} (hR : ∀ r ∈ R, z r ∈ R) {μ : AdjoinRoot g} (hμ : μ ≠ 0)
    (hμR : cycMap z v hv μ ∈ R) (ν : AdjoinRoot g) : cycMap z v hv ν ∈ R := by
  obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective (ν * μ⁻¹)
  have e : ν = AdjoinRoot.mk g Q * μ := by rw [hQ, inv_mul_cancel_right₀ hμ]
  rw [e, cycMap_mk_mul]
  exact aeval_mem_of_forall_mem hR Q hμR

end Cyc

section Adj

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} {y y' : Module.End K V}

theorem bilin_pow_pow (hyB : ∀ u w, B (y u) (y w) = B u w) (n : ℕ) (u w : V) :
    B ((y ^ n) u) ((y ^ n) w) = B u w := by
  induction n generalizing u w with
  | zero => rfl
  | succ n ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hyB]

theorem bilin_apply_left (hyy : y * y' = 1) (hyB : ∀ u w, B (y u) (y w) = B u w) (u w : V) :
    B (y u) w = B u (y' w) := by
  conv_lhs => rw [show w = y (y' w) by rw [← Module.End.mul_apply, hyy, Module.End.one_apply]]
  exact hyB u (y' w)

theorem bilin_pow_left (hyy : y * y' = 1) (hyB : ∀ u w, B (y u) (y w) = B u w) (n : ℕ)
    (u w : V) : B ((y ^ n) u) w = B u ((y' ^ n) w) := by
  induction n generalizing u w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, bilin_apply_left hyy hyB, ih, pow_succ,
      Module.End.mul_apply]

theorem bilin_aeval_left (hyy : y * y' = 1) (hyB : ∀ u w, B (y u) (y w) = B u w) (P : K[X])
    (u w : V) : B (aeval y P u) w = B u (aeval y' P w) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add,
      LinearMap.add_apply, hP, hQ, map_add]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smul₂,
      LinearMap.map_smul, bilin_pow_left hyy hyB]

theorem bilin_eq_zero_of_ker [FiniteDimensional K V] (hyy : y * y' = 1)
    (hyB : ∀ u w, B (y u) (y w) = B u w) {g h : K[X]}
    (hc : IsCompl (LinearMap.ker (aeval y' g)) (LinearMap.ker (aeval y' h))) {u w : V}
    (hu : aeval y g u = 0) (hw : aeval y' h w = 0) : B u w = 0 := by
  have hmaps : ∀ v ∈ LinearMap.ker (aeval y' h), aeval y' g v ∈ LinearMap.ker (aeval y' h) :=
    OrdPNS.mapsTo_ker_aeval (OrdPNS.commute_aeval (Commute.refl y') g).symm h
  set T := (aeval y' g).restrict hmaps with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : aeval y' g (v : V) = 0 := congrArg Subtype.val hv
    exact Subtype.ext (Submodule.disjoint_def.mp hc.disjoint _ hv' v.2)
  obtain ⟨w₀, hw₀⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  have e : aeval y' g (w₀ : V) = w := congrArg Subtype.val hw₀
  rw [← e, ← bilin_aeval_left hyy hyB, hu, map_zero, LinearMap.zero_apply]

end Adj

section Eigen

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {g : K[X]} [Fact (Irreducible g)] {ℓ : ℕ}

theorem exists_eigenBasis (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K)
    (z : Module.End K V) (T : Set (Module.End K V)) (hTc : ∀ x ∈ T, ∀ x' ∈ T, Commute x x')
    (hTz : ∀ x ∈ T, Commute x z) (hTp : ∀ x ∈ T, x ^ ℓ = 1) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → V) (hb : ∀ i, aeval z g (b i) = 0),
      (∀ i, b i ≠ 0) ∧ (∀ x ∈ T, ∀ i, ∃ a : ℕ, x (b i) = (z ^ a) (b i)) ∧
      ∀ w, aeval z g w = 0 → ∃ μ : ι → AdjoinRoot g, w = ∑ i, cycMap z (b i) (hb i) (μ i) := by
  classical
  have hg : Irreducible g := Fact.out
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set W := LinearMap.ker (aeval z g) with hW
  set φ := lAct z g with hφ
  let _ : Module (AdjoinRoot g) W := Module.compHom W φ.toRingHom
  have hsmul : ∀ (l : AdjoinRoot g) (v : W), l • v = φ l v := fun _ _ => rfl
  have : IsScalarTower K (AdjoinRoot g) W := ⟨fun a l v => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have : Module.Finite K (AdjoinRoot g) := (AdjoinRoot.powerBasis hg.ne_zero).finite
  have : Module.Finite (AdjoinRoot g) W :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot g) W
  have hζ : IsPrimitiveRoot (AdjoinRoot.root g) ℓ := NSFrame.root_isPrimitiveRoot hℓ hℓK hgd
  have hm : ∀ x ∈ T, ∀ v ∈ W, x v ∈ W := fun x hx => OrdPNS.mapsTo_ker_aeval (hTz x hx).symm g
  have hcommφ : ∀ x : Module.End K W, Commute x (kerRestr z g) → ∀ l, Commute x (φ l) := by
    intro x hx l
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective l
    rw [hφ, lAct_mk]
    exact (OrdPNS.commute_aeval hx.symm P).symm
  let toL : ∀ x : Module.End K W, Commute x (kerRestr z g) → Module.End (AdjoinRoot g) W :=
    fun x hx =>
      { toFun := x
        map_add' := x.map_add
        map_smul' := fun l v => by
          rw [hsmul, hsmul, RingHom.id_apply, ← Module.End.mul_apply, (hcommφ x hx l).eq,
            Module.End.mul_apply] }
  have hrc : ∀ x (hx : x ∈ T), Commute (x.restrict (hm x hx)) (kerRestr z g) := fun x hx =>
    OrdPNS.restrict_commute' (hTz x hx) _ _
  have : Finite (Module.End K V) := Module.finite_of_finite K
  let fT : T → Module.End (AdjoinRoot g) W := fun x => toL _ (hrc x.1 x.2)
  have hfc : ∀ i j, Commute (fT i) (fT j) := fun i j =>
    LinearMap.ext fun v => LinearMap.congr_fun
      (OrdPNS.restrict_commute' (hTc i.1 i.2 j.1 j.2) (hm i.1 i.2) (hm j.1 j.2)).eq v
  have hfp : ∀ i, fT i ^ ℓ = 1 := fun i => LinearMap.ext fun v => by
    rw [Module.End.pow_apply, Module.End.one_apply]
    have h1 := LinearMap.congr_fun (OrdPNS.restrict_pow_eq_one (hTp i.1 i.2) (hm i.1 i.2)) v
    rw [Module.End.pow_apply, Module.End.one_apply] at h1
    exact h1
  obtain ⟨b, μ, hb⟩ :=
    CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ fT hfc hfp
  have hμp : ∀ i k, μ i k ^ ℓ = 1 := by
    intro i k
    have h1 := OrdPNS.pow_apply_of_apply_eq_smul (hb i k) ℓ
    rw [hfp i, Module.End.one_apply] at h1
    have h2 : (μ i k ^ ℓ - 1) • b k = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (b.ne_zero k))
  have hφpow : ∀ (a : ℕ) (v : W), ((φ (AdjoinRoot.root g ^ a) v : W) : V) = (z ^ a) (v : V) := by
    intro a v
    rw [← AdjoinRoot.mk_X, ← map_pow, hφ, coe_lAct_mk, map_pow, aeval_X]
  refine ⟨Fin (finrank (AdjoinRoot g) W), inferInstance, fun k => (b k : V), fun k => (b k).2,
    fun k h0 => b.ne_zero k (Subtype.ext h0), fun x hx k => ?_, fun w hw => ?_⟩
  · obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (hμp ⟨x, hx⟩ k)
    refine ⟨a, ?_⟩
    have h1 : fT ⟨x, hx⟩ (b k) = μ ⟨x, hx⟩ k • b k := hb ⟨x, hx⟩ k
    have h2 : x (b k : V) = ((fT ⟨x, hx⟩ (b k) : W) : V) := rfl
    rw [h2, h1, ← ha, hsmul, hφpow]
  · refine ⟨fun k => b.repr ⟨w, hw⟩ k, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h1
    refine h1.symm.trans (Finset.sum_congr rfl fun k _ => ?_)
    rw [hsmul]
    rfl

end Eigen

section Match

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {g : K[X]}
  [Fact (Irreducible g)] {ℓ : ℕ} {B : LinearMap.BilinForm K V}

theorem mod_eq_of_pair (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) (hgd : g ∣ cyclotomic ℓ K)
    {y x : Module.End K V} (hyℓ : y ^ ℓ = 1) (hyB : ∀ u w, B (y u) (y w) = B u w)
    (hxB : ∀ u w, B (x u) (x w) = B u w) (hxy : Commute x y) {u w : V} (hu : aeval y g u = 0)
    {a a' : ℕ} (hxu : x u = (y ^ a) u) (hxw : x w = (y ^ a') w) (huw : B u w ≠ 0) :
    a % ℓ = a' % ℓ := by
  have hζ : IsPrimitiveRoot (AdjoinRoot.root g) ℓ := NSFrame.root_isPrimitiveRoot hℓ hℓK hgd
  obtain ⟨m, hm⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by have := hℓ.pos; omega⟩
  set N := a + (ℓ - 1) * a' with hN
  have hNa : N + a' = a + ℓ * a' := by
    rw [hN, hm, Nat.add_sub_cancel]
    ring
  have hxv : ∀ μ, x (cycMap y u hu μ) = (y ^ a) (cycMap y u hu μ) := fun μ => by
    rw [apply_cycMap hxy hu hxu, cycMap_root_pow_mul]
  have hyN : ∀ μ, B (cycMap y u hu μ) w = B ((y ^ N) (cycMap y u hu μ)) w := by
    intro μ
    have h1 : (y ^ ((ℓ - 1) * a')) ((y ^ a') w) = w := by
      rw [← Module.End.mul_apply, ← pow_add]
      have : (ℓ - 1) * a' + a' = ℓ * a' := by
        rw [hm, Nat.add_sub_cancel]
        ring
      rw [this, pow_mul, hyℓ, one_pow, Module.End.one_apply]
    have h2 : (y ^ ((ℓ - 1) * a')) ((y ^ a) (cycMap y u hu μ)) = (y ^ N) (cycMap y u hu μ) := by
      rw [← Module.End.mul_apply, ← pow_add, hN, add_comm]
    calc B (cycMap y u hu μ) w = B (x (cycMap y u hu μ)) (x w) := (hxB _ w).symm
      _ = B ((y ^ a) (cycMap y u hu μ)) ((y ^ a') w) := by rw [hxv μ, hxw]
      _ = B ((y ^ ((ℓ - 1) * a')) ((y ^ a) (cycMap y u hu μ)))
            ((y ^ ((ℓ - 1) * a')) ((y ^ a') w)) := (bilin_pow_pow hyB _ _ _).symm
      _ = B ((y ^ N) (cycMap y u hu μ)) w := by rw [h1, h2]
  have hdvd : ℓ ∣ N := by
    by_contra hnd
    have hne : AdjoinRoot.root g ^ N - 1 ≠ 0 := fun h0 =>
      hnd (hζ.dvd_of_pow_eq_one N (sub_eq_zero.mp h0))
    apply huw
    set t := (AdjoinRoot.root g ^ N - 1)⁻¹ with ht
    have e : u = cycMap y u hu (AdjoinRoot.root g ^ N * t) - cycMap y u hu t := by
      rw [← map_sub, ← sub_one_mul, ht, mul_inv_cancel₀ hne, cycMap_one]
    rw [e, LinearMap.map_sub₂, cycMap_root_pow_mul, ← hyN, sub_self]
  calc a % ℓ = (a + ℓ * a') % ℓ := (Nat.add_mul_mod_self_left a ℓ a').symm
    _ = (N + a') % ℓ := by rw [hNa]
    _ = a' % ℓ := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add, Nat.mod_mod]

end Match

end SpNS

end CFSG.StandardType
