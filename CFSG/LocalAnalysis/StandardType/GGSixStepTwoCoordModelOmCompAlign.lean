module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompBasic
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompAlign
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompRoots
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmFrame

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Pieces

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem isCompl_polarOrth [FiniteDimensional K V] {W : Submodule K V}
    (hW : ∀ w ∈ W, (∀ v ∈ W, QuadraticMap.polar Q v w = 0) → w = 0) :
    IsCompl W (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W) := by
  refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint fun x y hxy => ?_).mpr ?_
  · rw [QuadraticMap.polarBilin_apply_apply] at hxy ⊢
    rw [QuadraticMap.polar_comm]
    exact hxy
  · rw [Submodule.disjoint_def]
    intro w hw hw'
    exact hW w hw fun v hv => LinearMap.BilinForm.mem_orthogonal_iff.mp hw' v hv

theorem aeval_apply_mem {T : Module.End K V} {U : Submodule K V} (hU : ∀ u ∈ U, T u ∈ U)
    (f : K[X]) {u : V} (hu : u ∈ U) : aeval T f u ∈ U := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem hf hg
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact U.smul_mem c (CoordSU.pow_apply_mem hU n hu)

theorem frame_single_sub_mem [FiniteDimensional K V] (F : SevOm.Frame Q p A r) (j : Fin r)
    (v : V) : F.ι (ofAdd (Pi.single j 1)) v - v ∈ F.U j := by
  classical
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl (isCompl_polarOrth (F.nondeg j)) v
  have hw' : F.ι (ofAdd (Pi.single j 1)) w = w := by
    refine (F.fix _ w).mpr fun k hk u' hu' => ?_
    have hkj : k = j := by
      by_contra hne
      exact hk (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
    subst hkj
    have h1 := LinearMap.BilinForm.mem_orthogonal_iff.mp hw u' hu'
    exact h1
  rw [map_add, hw', add_sub_add_right_eq_sub]
  exact sub_mem (F.mapsTo _ j u hu) hu

theorem frame_map_piece [FiniteDimensional K V] [Fact p.Prime] (F : SevOm.Frame Q p A r)
    {j j' : Fin r} {g : V ≃ₗ[K] V}
    (hg : ∀ v, g (F.ι (ofAdd (Pi.single j 1)) v) = F.ι (ofAdd (Pi.single j' 1)) (g v)) {u : V}
    (hu : u ∈ F.U j) : g u ∈ F.U j' := by
  have hle := le_of_fpf (y := F.ι (ofAdd (Pi.single j 1))) (U := F.U j)
    (W := (F.U j').comap (g : V →ₗ[K] V)) (fun u hu => F.mapsTo _ j u hu)
    (fun u hu h1 => frame_single_fpf F j hu h1) (fun v => by
      show g (_ - v) ∈ F.U j'
      rw [map_sub, hg]
      exact frame_single_sub_mem F j' (g v))
  exact hle hu

theorem frame_apply_eq_pow [NeZero p] (F : SevOm.Frame Q p A r) (β : Fin r → ZMod p) (j : Fin r)
    {u : V} (hu : u ∈ F.U j) :
    F.ι (ofAdd β) u = (F.ι (ofAdd (Pi.single j 1)) ^ (β j).val) u := by
  classical
  have h1 : F.ι (ofAdd β) = F.ι (ofAdd (Pi.single j 1)) ^ (β j).val *
      F.ι (ofAdd (β - (β j).val • Pi.single j (1 : ZMod p))) := by
    rw [← map_pow, ← map_mul, ← ofAdd_nsmul, ← ofAdd_add, add_sub_cancel]
  have h2 : toAdd (ofAdd (β - (β j).val • Pi.single j (1 : ZMod p)) :
      Multiplicative (Fin r → ZMod p)) j = 0 := by
    rw [toAdd_ofAdd, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one,
      ZMod.natCast_zmod_val, sub_self]
  rw [h1, LinearEquiv.mul_apply, F.triv _ j h2 u hu]

end Pieces

section Align

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] in
theorem natCast_ne_zero_of_odd (hp : p.Prime) (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
  exact one_ne_zero

omit [CharP K 2] in
theorem coprime_card [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2) : Nat.Coprime (Nat.card K) p := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

omit [Finite K] [CharP K 2] in
theorem exists_galSigns_mul [Finite K] [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2) {a b : ZMod p}
    (j : ℕ) (h : b = (Nat.card K : ZMod p) ^ j * a ∨ b = -((Nat.card K : ZMod p) ^ j * a)) :
    ∃ u ∈ CoordSpNs.galSigns p (Nat.card K), b = (u : ZMod p) * a := by
  set uq : (ZMod p)ˣ := ZMod.unitOfCoprime (Nat.card K) (coprime_card (K := K) hp hp2) with huq
  have huqm : uq ∈ CoordSpNs.galSigns p (Nat.card K) :=
    Subgroup.subset_closure (Or.inl (by rw [huq, ZMod.coe_unitOfCoprime]))
  have hval : ((uq ^ j : (ZMod p)ˣ) : ZMod p) = (Nat.card K : ZMod p) ^ j := by
    rw [Units.val_pow_eq_pow_val, huq, ZMod.coe_unitOfCoprime]
  rcases h with h | h
  · exact ⟨uq ^ j, Subgroup.pow_mem _ huqm j, by rw [h, hval]⟩
  · refine ⟨-1 * uq ^ j, Subgroup.mul_mem _ (CoordSpNs.neg_one_mem_galSigns _ _)
      (Subgroup.pow_mem _ huqm j), ?_⟩
    have hm1 : ((-1 : (ZMod p)ˣ) : ZMod p) = -1 := by
      rw [Units.val_neg, Units.val_one]
    rw [h, Units.val_mul, hm1, hval, neg_one_mul, neg_mul]

theorem frame_align (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r) (β : Fin r → ZMod p)
    {h : K[X]} (hh : h ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap) (hX : h ≠ X - 1)
    {i i' : Fin r} (hi : F.U i ≤ orbitSpace (F.ι (ofAdd β)).toLinearMap h)
    (hi' : F.U i' ≤ orbitSpace (F.ι (ofAdd β)).toLinearMap h) {w : V ≃ₗ[K] V}
    (hw : ∀ s : Fin r → ZMod p,
      w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd fun k => s (Equiv.swap i i' k))) :
    ∃ u ∈ CoordSpNs.galSigns p (Nat.card K), β i' = (u : ZMod p) * β i := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set x := F.ι (ofAdd β) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  set y := F.ι (ofAdd (Pi.single i (1 : ZMod p))) with hydef
  set y' := F.ι (ofAdd (Pi.single i' (1 : ZMod p))) with hy'def
  have hint : ∀ v, w (y v) = y' (w v) := by
    intro v
    have h1 := hw (Pi.single i' 1)
    have h2 : (fun k => (Pi.single i' (1 : ZMod p) : Fin r → ZMod p) (Equiv.swap i i' k)) =
        (Pi.single i 1 : Fin r → ZMod p) := by
      funext k
      simp only [Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    rw [h2] at h1
    have h3 : (w⁻¹ * y' * w) v = y v := by rw [h1]
    calc w (y v) = w ((w⁻¹ * y' * w) v) := by rw [h3]
      _ = (w * w⁻¹ * y' * w) v := rfl
      _ = y' (w v) := by rw [mul_inv_cancel, one_mul]; rfl
  have hwU : ∀ u ∈ F.U i, w u ∈ F.U i' := fun u hu => frame_map_piece F hint hu
  have hintpow : ∀ (n : ℕ) (v : V), w ((y ^ n) v) = (y' ^ n) (w v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', LinearEquiv.mul_apply, hint, ih, pow_succ', LinearEquiv.mul_apply]
  set P : K[X] := h * reciprocalPolynomial h with hP
  have hPorb : ∀ u ∈ orbitSpace x.toLinearMap h, aeval x.toLinearMap P u = 0 := by
    intro u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    have e1 : aeval x.toLinearMap P u₁ = 0 := by
      rw [hP, mul_comm, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hu₁, map_zero]
    have e2 : aeval x.toLinearMap P u₂ = 0 := by
      rw [hP, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hu₂, map_zero]
    rw [map_add, e1, e2, add_zero]
  have hyU : ∀ u ∈ F.U i, y.toLinearMap u ∈ F.U i := fun u hu => F.mapsTo _ i u hu
  have hR₁ : ∀ u ∈ F.U i, aeval y.toLinearMap (P.comp (X ^ (β i).val)) u = 0 := by
    intro u hu
    have h1 := CoordSU.aeval_apply_comp_pow (T₁ := x.toLinearMap) (θ := LinearMap.id) hyU
      (β i).val (fun v hv => by
        rw [LinearMap.id_apply, LinearMap.id_apply, ← toLinearMap_pow]
        exact frame_apply_eq_pow F β i hv) P hu
    rw [LinearMap.id_apply, LinearMap.id_apply, hPorb u (hi hu)] at h1
    exact h1.symm
  have hR₂ : ∀ u ∈ F.U i, aeval y.toLinearMap (P.comp (X ^ (β i').val)) u = 0 := by
    intro u hu
    have h1 := CoordSU.aeval_apply_comp_pow (T₁ := x.toLinearMap) (θ := w.toLinearMap) hyU
      (β i').val (fun v hv => by
        rw [← toLinearMap_pow]
        show x (w v) = w ((y ^ (β i').val) v)
        rw [hintpow, frame_apply_eq_pow F β i' (hwU v hv)]) P hu
    have h2 : aeval x.toLinearMap P (w.toLinearMap u) = 0 := hPorb (w u) (hi' (hwU u hu))
    rw [h2] at h1
    exact (LinearEquiv.map_eq_zero_iff w).mp h1.symm
  have hR₃ : ∀ u ∈ F.U i, aeval y.toLinearMap (cyclotomic p K) u = 0 := by
    intro u hu
    have hzU : aeval y.toLinearMap (cyclotomic p K) u ∈ F.U i := aeval_apply_mem hyU _ hu
    have hyp : y.toLinearMap ^ p = 1 := by
      rw [← toLinearMap_pow, F.pow_p]
      rfl
    have h1 : aeval y.toLinearMap ((X - 1) * cyclotomic p K) u = 0 := by
      rw [mul_comm, cyclotomic_prime_mul_X_sub_one, map_sub, map_pow, aeval_X, map_one, hyp,
        sub_self, LinearMap.zero_apply]
    rw [map_mul, Module.End.mul_apply, map_sub, aeval_X, map_one, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero] at h1
    exact frame_single_fpf F i hzU h1
  obtain ⟨ν, hν₁, hν₂, hν₃⟩ := CoordSU.exists_root_of_restrict hyU (F.ne_bot i) hR₁ hR₂ hR₃
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpE : (p : AlgebraicClosure K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have : NeZero (p : AlgebraicClosure K) := ⟨hpE⟩
  have hνp : IsPrimitiveRoot ν p := by
    rw [← Polynomial.isRoot_cyclotomic_iff, IsRoot, ← map_cyclotomic p (algebraMap K _),
      eval_map, ← aeval_def]
    exact hν₃
  have hν0 : ν ≠ 0 := hνp.ne_zero hp.ne_zero
  have hroot : ∀ e : ZMod p, aeval (ν ^ e.val) P = 0 →
      aeval (AddChar.zmodChar p hνp.pow_eq_one e) h = 0 ∨
        aeval (AddChar.zmodChar p hνp.pow_eq_one (-e)) h = 0 := by
    intro e he
    rw [hP, map_mul, mul_eq_zero] at he
    rcases he with he | he
    · left
      rwa [AddChar.zmodChar_apply]
    · right
      have hμ0 : ν ^ e.val ≠ 0 := pow_ne_zero _ hν0
      have h1 := aeval_reciprocalPolynomial_of_unit (Units.mk0 (ν ^ e.val) hμ0) h
      rw [Units.val_mk0, he] at h1
      have h2 : aeval (((Units.mk0 (ν ^ e.val) hμ0)⁻¹ : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K) h = 0 := by
        rcases smul_eq_zero.mp h1.symm with h3 | h3
        · exact absurd h3 (inv_ne_zero (hx.coeff_zero_ne hh))
        · exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ hμ0)
      rw [AddChar.map_neg_eq_inv, AddChar.zmodChar_apply]
      simpa using h2
  have h₁ : aeval (ν ^ (β i).val) P = 0 := by rwa [aeval_comp, map_pow, aeval_X] at hν₁
  have h₂ : aeval (ν ^ (β i').val) P = 0 := by rwa [aeval_comp, map_pow, aeval_X] at hν₂
  have hirr := irreducible_of_mem_primaryFactors hh
  have hcd : h ∣ cyclotomic p K := CoordSU.dvd_cyclotomic_of_dvd hp hirr
    (monic_of_mem_primaryFactors hh) (by rw [C_1]; exact hx.dvd_X_pow_sub_one hh)
    (by rwa [C_1])
  rcases hroot _ h₁ with r1 | r1 <;> rcases hroot _ h₂ with r2 | r2
  · obtain ⟨j, hj⟩ := CoordSU.eq_pow_mul_of_roots hp hpK hirr hcd hνp r1 r2
    exact exists_galSigns_mul hp hp2 j (Or.inl hj)
  · obtain ⟨j, hj⟩ := CoordSU.eq_pow_mul_of_roots hp hpK hirr hcd hνp r1 r2
    exact exists_galSigns_mul hp hp2 j (Or.inr (neg_eq_iff_eq_neg.mp hj))
  · obtain ⟨j, hj⟩ := CoordSU.eq_pow_mul_of_roots hp hpK hirr hcd hνp r1 r2
    exact exists_galSigns_mul hp hp2 j (Or.inr (by rw [hj, mul_neg]))
  · obtain ⟨j, hj⟩ := CoordSU.eq_pow_mul_of_roots hp hpK hirr hcd hνp r1 r2
    exact exists_galSigns_mul hp hp2 j (Or.inl (neg_inj.mp (by rw [hj, mul_neg])))

end Align

end CoordOm

end CFSG.StandardType
