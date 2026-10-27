module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompAlign

public section

namespace CFSG.StandardType

namespace CoordSU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Multiplicative

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

theorem le_orbW_of_pieceIn (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {x : ↥(unitarySU 2 f K n)} (hxA : x ∈ A) {a : K[X]} (ha : a ∈ primaryFactors (Xe x))
    {i : Fin F.r} (hi : PieceIn F x a i) : rng (F.y i) ≤ orbW h x a := by
  intro v hv
  have H := primaryData h hA.prime hA.ne_two (hA.pow x hxA)
  obtain ⟨w, hwW, hw', hwU⟩ := exists_orbW_decomp H ha v
  have hwi : w ∈ rng (F.y i) := hwU _ (rng_inv hA (F.y_mem i) hxA) hv
  have hd : v - w = 0 := by
    refine F.nondeg hA i (v - w) ((rng (F.y i)).sub_mem hv hwi) fun m hm => ?_
    exact (Submodule.mem_orthogonalBilin.mp (mem_orth_of_pieceIn hA F hi hw')) m hm
  rw [sub_eq_zero.mp hd]
  exact hwW

theorem aeval_mul_dualPoly_eq_zero {x : ↥(unitarySU 2 f K n)} {a : K[X]} {u : Fin n → K}
    (hu : u ∈ orbW h x a) : aeval (Xe x) (a * dualPoly h.bar a) u = 0 := by
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hu
  have e1 : aeval (Xe x) (a * dualPoly h.bar a) w₁ =
      aeval (Xe x) (dualPoly h.bar a) (aeval (Xe x) a w₁) := by
    rw [mul_comm, map_mul, Module.End.mul_apply]
  have e2 : aeval (Xe x) (a * dualPoly h.bar a) w₂ =
      aeval (Xe x) a (aeval (Xe x) (dualPoly h.bar a) w₂) := by
    rw [map_mul, Module.End.mul_apply]
  rw [map_add, e1, e2, mem_primaryComponent.mp hw₁, mem_primaryComponent.mp hw₂, map_zero,
    map_zero, add_zero]

theorem exists_eq_lin_b_sub (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (i : Fin F.r)
    {u : Fin n → K} (hu : u ∈ rng (F.y i)) : ∃ v, u = lin (F.b i) v - v := by
  obtain ⟨v₀, rfl⟩ := hu
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth (F.nondeg hA i) v₀
  have hz' : lin (F.y i) z = z := by
    have h1 : z ∈ LinearMap.ker (lin (F.y i) - 1) := (rng_orth_eq_ker hA (F.y_mem i)) ▸ hz
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    exact h1
  refine ⟨m, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply, map_add, hz', F.b_on i m hm]
  abel

theorem lin_b_pow_on (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (j : Fin F.r) (k : ℕ)
    {v : Fin n → K} (hv : v ∈ rng (F.y j)) : lin (F.b j ^ k) v = lin (F.y j ^ k) v := by
  induction k with
  | zero => rw [pow_zero, pow_zero]
  | succ k ih =>
    have hv' : lin (F.y j ^ k) v ∈ rng (F.y j) :=
      rng_inv hA (F.y_mem j) (A.pow_mem (F.y_mem j) k) v hv
    rw [pow_succ', lin_mul, Module.End.mul_apply, ih, F.b_on j _ hv', ← Module.End.mul_apply,
      ← lin_mul, ← pow_succ']

theorem zmod_mul_right_cancel (hp : p.Prime) {a b k : ZMod p} (hk : k ≠ 0)
    (hab : a * k = b * k) : a = b := by
  have : Fact p.Prime := ⟨hp⟩
  exact mul_right_cancel₀ hk hab

theorem exists_negQ_mul_of_pieceIn (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    (hFm : FrameMoves F) {β : Fin F.r → ZMod p} {x : ↥(unitarySU 2 f K n)}
    (hxβ : F.ι (ofAdd β) = x) {a : K[X]} (ha : a ∈ primaryFactors (Xe x)) (ha1 : a ≠ X - C 1)
    {i i' : Fin F.r} (hi : PieceIn F x a i) (hi' : PieceIn F x a i') :
    ∃ o ∈ negQ p (2 ^ f), β i' = (o : ZMod p) * β i := by
  classical
  by_cases hii : i = i'
  · exact ⟨1, (negQ p (2 ^ f)).one_mem, by rw [hii, Units.val_one, one_mul]⟩
  have hp := hA.prime
  have hp2 := hA.ne_two
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have hxA : x ∈ A := hxβ ▸ ι_mem F _
  have hxp : x ^ p = 1 := hA.pow x hxA
  have H := primaryData h hp hp2 hxp
  have had := dualPoly_mem_primaryFactors H ha
  have hdd := dualPoly_dualPoly_of_mem H ha
  have had1 : dualPoly h.bar a ≠ X - C 1 := by
    intro e
    apply ha1
    rw [← hdd, e, dualPoly_X_sub_C_one]
  have hminp : minpoly K (Xe x) ∣ X ^ p - C 1 := by
    refine minpoly.dvd K _ ?_
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, coe_toUnitHom, ← SUTB.lin_pow, hxp,
      SUTB.lin_one, sub_self]
  have hdvdX : ∀ c ∈ primaryFactors (Xe x), c ∣ X ^ p - C 1 := fun c hc =>
    (mem_primaryFactors.mp hc).2.2.trans hminp
  have hacd := dvd_cyclotomic_of_dvd hp (irreducible_of_mem_primaryFactors ha)
    (monic_of_mem_primaryFactors ha) (hdvdX a ha) ha1
  have hadcd := dvd_cyclotomic_of_dvd hp (irreducible_of_mem_primaryFactors had)
    (monic_of_mem_primaryFactors had) (hdvdX _ had) had1
  have hpK : (p : K) ≠ 0 := by
    rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  set P := a * dualPoly h.bar a with hP
  have hPW : ∀ j, PieceIn F x a j → ∀ u ∈ rng (F.y j), aeval (lin x) P u = 0 :=
    fun j hj u hu => aeval_mul_dualPoly_eq_zero (le_orbW_of_pieceIn hA F hxA ha hj hu)
  set T := lin (F.y i) with hT
  have hTU : ∀ u ∈ rng (F.y i), T u ∈ rng (F.y i) := rng_inv hA (F.y_mem i) (F.y_mem i)
  have hR1 : ∀ u ∈ rng (F.y i), aeval T (P.comp (X ^ (β i).val)) u = 0 := by
    intro u hu
    have h1 := aeval_apply_comp_pow (T₁ := lin x) (θ := LinearMap.id) hTU (β i).val
      (fun u' hu' => by
        rw [LinearMap.id_apply, LinearMap.id_apply, hT, ← SUTB.lin_pow, ← hxβ,
          F.ι_on _ i u' hu', toAdd_ofAdd]) P hu
    rw [LinearMap.id_apply, LinearMap.id_apply, hPW i hi u hu] at h1
    exact h1.symm
  obtain ⟨w, hw⟩ := hFm (Equiv.swap i i') (fun _ => 1) (fun _ => (negQ p (2 ^ f)).one_mem)
    (by simp)
  have hbb : w⁻¹ * F.b i' * w = F.b i := by
    rw [← F.ι_single i', hw, ← F.ι_single i]
    congr 2
    funext j
    rw [Units.val_one, one_mul]
    by_cases hj : j = i
    · rw [hj, Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_same]
    · by_cases hj' : j = i'
      · rw [hj', Equiv.swap_apply_right, Pi.single_eq_of_ne hii, Pi.single_eq_of_ne (Ne.symm hii)]
      · rw [Equiv.swap_apply_of_ne_of_ne hj hj', Pi.single_eq_of_ne hj', Pi.single_eq_of_ne hj]
  have h1w : F.b i' * w = w * F.b i := by
    rw [← hbb]
    group
  have hbw : ∀ k : ℕ, F.b i' ^ k * w = w * F.b i ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, h1w, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have hwmap : ∀ u ∈ rng (F.y i), lin w u ∈ rng (F.y i') := by
    intro u hu
    obtain ⟨v, rfl⟩ := exists_eq_lin_b_sub hA F i hu
    have h1 := sub_mem_rng F hA i' 1 (lin w v)
    rwa [pow_one, ← Module.End.mul_apply, ← lin_mul, h1w, lin_mul, Module.End.mul_apply,
      ← map_sub] at h1
  have hwinj : ∀ v, lin w v = 0 → v = 0 := by
    intro v hv
    have h1 := congrArg (lin w⁻¹) hv
    rwa [← Module.End.mul_apply, ← lin_mul, inv_mul_cancel, lin_one, map_zero] at h1
  have hR2 : ∀ u ∈ rng (F.y i), aeval T (P.comp (X ^ (β i').val)) u = 0 := by
    intro u hu
    have hT' : ∀ u' ∈ rng (F.y i), lin x (lin w u') = lin w ((T ^ (β i').val) u') := by
      intro u' hu'
      rw [← hxβ, F.ι_on _ i' _ (hwmap u' hu'), toAdd_ofAdd,
        ← lin_b_pow_on hA F i' _ (hwmap u' hu'), ← Module.End.mul_apply, ← lin_mul, hbw,
        lin_mul, Module.End.mul_apply, lin_b_pow_on hA F i _ hu', hT, SUTB.lin_pow]
    have h1 := aeval_apply_comp_pow (T₁ := lin x) (θ := lin w) hTU (β i').val hT' P hu
    rw [hPW i' hi' _ (hwmap u hu)] at h1
    exact hwinj _ h1.symm
  have hR3 : ∀ u ∈ rng (F.y i), aeval T (X ^ p - 1 : K[X]) u = 0 := by
    intro u _
    rw [map_sub, map_pow, aeval_X, map_one, hT, ← SUTB.lin_pow, hA.pow _ (F.y_mem i), SUTB.lin_one,
      sub_self, LinearMap.zero_apply]
  obtain ⟨ν, hν1, hν2, hν3⟩ := exists_root_of_restrict hTU (F.ne_bot i) hR1 hR2 hR3
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpE : (p : AlgebraicClosure K) ≠ 0 := by
    rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpE
  have hνp : ν ^ p = 1 := by
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at hν3
    exact hν3
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hνp
  set ψ := AddChar.zmodChar p hζ.pow_eq_one with hψ
  have hνψ : ν = ψ (k : ZMod p) := by rw [hψ, AddChar.zmodChar_apply', hk]
  have hroot : ∀ m : ℕ, aeval ν (P.comp (X ^ m)) = 0 →
      aeval (ψ ((m : ZMod p) * (k : ZMod p))) a = 0 ∨
        aeval (ψ ((m : ZMod p) * (k : ZMod p))) (dualPoly h.bar a) = 0 := by
    intro m hm
    rw [aeval_comp, map_pow, aeval_X, hνψ, ← zmodChar_natCast_mul, hP, map_mul] at hm
    exact mul_eq_zero.mp hm
  obtain ⟨t, ht⟩ := exists_negQ_of_roots h hp hp2 (irreducible_of_mem_primaryFactors ha) hacd
    (irreducible_of_mem_primaryFactors had) hadcd hdd hζ (hroot _ hν1) (hroot _ hν2)
  have hk0 : (k : ZMod p) ≠ 0 := by
    intro hk0
    have h1 := hroot _ hν1
    rw [hk0, mul_zero, AddChar.map_zero_eq_one] at h1
    rcases h1 with h1 | h1
    · exact aeval_one_ne_zero_of_dvd hp hpK hacd h1
    · exact aeval_one_ne_zero_of_dvd hp hpK hadcd h1
  set u₀ : (ZMod p)ˣ := -ZMod.unitOfCoprime (2 ^ f) (coprime_two_pow hp hp2 f) with hu₀
  have hu₀v : (u₀ : ZMod p) = -((2 ^ f : ℕ) : ZMod p) := by simp [hu₀]
  refine ⟨u₀ ^ t, (negQ p (2 ^ f)).pow_mem (mem_negQ_of_eq hu₀v) t, ?_⟩
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at ht
  rw [Units.val_pow_eq_pow_val, hu₀v]
  exact zmod_mul_right_cancel hp hk0 (by rw [ht, mul_assoc])

end CoordSU

end CFSG.StandardType
