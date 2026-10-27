module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSUCount
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPair
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitRank
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneDimension

public section

namespace CFSG.StandardType

namespace OrdPNsU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.OddIso CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryPlane

section Numbers

variable {f : ℕ} {K : Type} [Field K]

theorem two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ((2 : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

theorem ordNegQ_pos {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 0 < ordNegQ 2 f p := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : -(((2 : ℕ) : ZMod p) ^ f) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (two_ne_zero_zmod hp hp2))
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hne⟩)

theorem ordQ_dvd_ordNegQ (h : UnitaryFieldData 2 f K) (p : ℕ) :
    OrdPNS.ordQ K p ∣ ordNegQ 2 f p := by
  rw [OrdPNS.ordQ_def, h.card, ordNegQ]
  refine orderOf_dvd_of_pow_eq_one ?_
  have h1 := pow_orderOf_eq_one (-(((2 : ℕ) : ZMod p) ^ f))
  have h2 : ((2 ^ (2 * f) : ℕ) : ZMod p) = (-(((2 : ℕ) : ZMod p) ^ f)) ^ 2 := by
    push_cast
    ring
  rw [h2, ← pow_mul, mul_comm, pow_mul, h1, one_pow]

theorem dualPoly_eq_self_of_dvd (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    {g : K[X]} (hg : Irreducible g) (hgm : g.Monic) (hgd : g ∣ X ^ p - C 1)
    (hodd : Odd g.natDegree) (hpd : p ∣ 2 ^ (f * g.natDegree) + 1) : dualPoly h.bar g = g := by
  classical
  have : Fact (Irreducible g) := ⟨hg⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set d := g.natDegree with hd
  have h0 : g.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_dvd hp.pos hgd
  have : CharP (AdjoinRoot g) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
  have : ExpChar (AdjoinRoot g) 2 := ExpChar.prime Nat.prime_two
  set ζ : AdjoinRoot g := AdjoinRoot.root g with hζ
  have hζp : ζ ^ p = 1 := by
    have h1 : AdjoinRoot.mk g (X ^ p - C 1) = 0 := AdjoinRoot.mk_eq_zero.mpr hgd
    simpa [hζ, sub_eq_zero] using h1
  have hζ0 : ζ ≠ 0 := by
    intro h1
    rw [h1, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  set θ : AdjoinRoot g →+* AdjoinRoot g := iterateFrobenius (AdjoinRoot g) 2 (f * d) with hθ
  have hθK : ∀ c : K, θ (algebraMap K (AdjoinRoot g) c) =
      algebraMap K (AdjoinRoot g) (h.bar c) := by
    intro c
    obtain ⟨m, hm⟩ := hodd
    have hcard : Fintype.card K = 2 ^ (2 * f) := by rw [← Nat.card_eq_fintype_card, h.card]
    have hexp : 2 ^ (f * d) = 2 ^ f * (2 ^ (2 * f)) ^ m := by
      rw [← pow_mul, ← pow_add, hm]
      congr 1
      ring
    have hc : c ^ 2 ^ (f * d) = c ^ 2 ^ f := by
      calc c ^ 2 ^ (f * d) = (c ^ 2 ^ f) ^ (2 ^ (2 * f)) ^ m := by rw [hexp, pow_mul]
        _ = c ^ 2 ^ f := by rw [← hcard]; exact FiniteField.pow_card_pow m _
    rw [hθ, iterateFrobenius_def, ← map_pow, hc, UnitaryFieldData.bar_apply]
  have hθζ : θ ζ = ζ⁻¹ := by
    rw [hθ, iterateFrobenius_def]
    obtain ⟨k, hk⟩ := hpd
    have h1 : ζ ^ (2 ^ (f * d) + 1) = 1 := by rw [hk, pow_mul, hζp, one_pow]
    rw [pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have heval : (g.map h.bar).eval₂ (algebraMap K (AdjoinRoot g)) ζ⁻¹ = 0 := by
    have hcomp : (algebraMap K (AdjoinRoot g)).comp h.bar =
        θ.comp (algebraMap K (AdjoinRoot g)) := RingHom.ext fun c => (hθK c).symm
    rw [← hθζ, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, map_zero]
  have hrev : ((g.map h.bar).reverse).eval₂ (algebraMap K (AdjoinRoot g)) ζ = 0 := by
    let : Invertible ζ⁻¹ := invertibleOfNonzero (inv_ne_zero hζ0)
    have h1 := Polynomial.eval₂_reverse_mul_pow (algebraMap K (AdjoinRoot g)) ζ⁻¹ (g.map h.bar)
    rw [heval, invOf_eq_inv, inv_inv] at h1
    exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ (inv_ne_zero hζ0))
  have hroot : AdjoinRoot.mk g (dualPoly h.bar g) = 0 := by
    rw [← AdjoinRoot.aeval_eq, dualPoly, map_mul, aeval_C, aeval_def, hrev, mul_zero]
  have hdvd : g ∣ dualPoly h.bar g := AdjoinRoot.mk_eq_zero.mp hroot
  have hdirr : Irreducible (dualPoly h.bar g) := irreducible_dualPoly h.bar_bar hg h0
  exact (eq_of_monic_of_associated hgm (monic_dualPoly h0) (hg.associated_of_dvd hdirr hdvd)).symm

theorem two_mul_natDegree_le (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : K[X]} (hg : Irreducible g) (hgm : g.Monic) (hgd : g ∣ cyclotomic p K)
    (hpair : dualPoly h.bar g ≠ g) : 2 * g.natDegree ≤ ordNegQ 2 f p := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have hpK : (p : K) ≠ 0 := by
    rw [natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  have hd := OrdPNS.natDegree_eq_ordQ hp hpK hg hgd
  have hdpos : 0 < g.natDegree := Irreducible.natDegree_pos hg
  have hde : g.natDegree ∣ ordNegQ 2 f p := hd ▸ ordQ_dvd_ordNegQ h p
  set t : ZMod p := ((2 : ℕ) : ZMod p) ^ f with ht
  have he : ordNegQ 2 f p = orderOf (-t) := rfl
  have ht2 : t ^ 2 = ((2 ^ (2 * f) : ℕ) : ZMod p) := by
    rw [ht]
    push_cast
    ring
  have hord : (((2 ^ (2 * f) : ℕ) : ZMod p)) ^ g.natDegree = 1 := by
    rw [hd, OrdPNS.ordQ_def, h.card]
    exact pow_orderOf_eq_one _
  have he2 : ordNegQ 2 f p ∣ 2 * g.natDegree := by
    rw [he]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_mul, neg_sq, ht2, hord]
  obtain ⟨m, hm⟩ := hde
  have hm2 : m ∣ 2 := by
    have h1 : g.natDegree * m ∣ g.natDegree * 2 := by rw [← hm, mul_comm g.natDegree 2]; exact he2
    exact Nat.dvd_of_mul_dvd_mul_left hdpos h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with hm1 | hm2'
  · exfalso
    rw [hm1, mul_one] at hm
    have hpow : (-t) ^ g.natDegree = 1 := by
      have h1 := pow_orderOf_eq_one (-t)
      rwa [← he, hm] at h1
    rcases Nat.even_or_odd g.natDegree with hev | hodd
    · obtain ⟨k, hk⟩ := hev
      have h1 : (((2 ^ (2 * f) : ℕ) : ZMod p)) ^ k = 1 := by
        rw [← ht2, ← pow_mul, show 2 * k = k + k by ring, ← hk, ← Even.neg_pow ⟨k, hk⟩ t, hpow]
      have h2 : OrdPNS.ordQ K p ∣ k := by
        rw [OrdPNS.ordQ_def, h.card]
        exact orderOf_dvd_of_pow_eq_one h1
      rw [← hd] at h2
      have := Nat.le_of_dvd (by omega) h2
      omega
    · apply hpair
      have hgX : g ∣ X ^ p - C 1 := by
        rw [C_1]
        exact hgd.trans (cyclotomic.dvd_X_pow_sub_one p K)
      refine dualPoly_eq_self_of_dvd h hp hg hgm hgX hodd ?_
      have hpow' : t ^ g.natDegree = -1 := by
        rw [Odd.neg_pow hodd] at hpow
        rw [← neg_neg (t ^ g.natDegree), hpow]
      have h1 : ((2 ^ (f * g.natDegree) + 1 : ℕ) : ZMod p) = 0 := by
        have h2 : ((2 ^ (f * g.natDegree) : ℕ) : ZMod p) = t ^ g.natDegree := by
          rw [ht, ← pow_mul]
          push_cast
          rfl
        rw [Nat.cast_add, h2, hpow', Nat.cast_one, neg_add_cancel]
      exact (ZMod.natCast_eq_zero_iff _ _).mp h1
  · rw [hm2'] at hm
    omega

end Numbers

section Pieces

variable {f n : ℕ} {K : Type} [Field K]

theorem ordNegQ_dvd_finrank_rng (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : ↥(unitarySU 2 f K n)} (hyp : y ^ p = 1) : ordNegQ 2 f p ∣ finrank K (rng y) := by
  have h1 := ordNegQ_dvd_finrank_sub h hp hp2 (stdHermForm_isSymm h n)
    (stdHermForm_separatingLeft h n) (x := toUnit y) (isometry_lin h y)
    (by rw [coe_toUnit, ← SUTB.lin_pow, hyp, lin_one])
  have h2 : finrank K (rng y) + finrank K (LinearMap.ker (lin y - 1)) = finrank K (Fin n → K) :=
    LinearMap.finrank_range_add_finrank_ker (lin y - 1)
  rw [coe_toUnit] at h1
  rwa [show finrank K (Fin n → K) - finrank K (LinearMap.ker (lin y - 1)) = finrank K (rng y) by
    omega] at h1

theorem finrank_cyc_le {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Y : Module.End K V) {g : K[X]} (hgm : g.Monic) (hg1 : g ≠ 1) {w : V}
    (hw : aeval Y g w = 0) : finrank K (cyc Y w) ≤ g.natDegree := by
  classical
  have hle : cyc Y w ≤ Submodule.span K (Set.range fun j : Fin g.natDegree => (Y ^ (j : ℕ)) w) := by
    intro v hv
    obtain ⟨t, rfl⟩ := (mem_cyc_iff Y w v).mp hv
    have ht : aeval Y t w = aeval Y (t %ₘ g) w := by
      conv_lhs => rw [← modByMonic_add_div t g]
      rw [map_add, LinearMap.add_apply, mul_comm g (t /ₘ g), map_mul, Module.End.mul_apply, hw,
        map_zero, add_zero]
    rw [ht, aeval_eq_sum_range' (natDegree_modByMonic_lt t hgm hg1), LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)
  exact (Submodule.finrank_mono hle).trans ((finrank_range_le_card _).trans (by simp))

theorem unitaryPrimaryData_of_pow (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {y : ↥(unitarySU 2 f K n)} (hyp : y ^ p = 1) :
    UnitaryPrimaryData h.bar (stdHermForm h n) (toUnit y) where
  invol := h.bar_bar
  symm := stdHermForm_isSymm h n
  sep := stdHermForm_separatingLeft h n
  isom := isometry_lin h y
  squarefree := by
    have : CharP K 2 := h.charP
    have hpK : (p : K) ≠ 0 := by
      rw [natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
      exact one_ne_zero
    refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - 1) ?_ ?_
    · have := (separable_X_pow_sub_C (1 : K) hpK one_ne_zero).squarefree
      rwa [map_one] at this
    · rw [coe_toUnit, map_sub, map_pow, aeval_X, map_one, ← SUTB.lin_pow, hyp, lin_one, sub_self]

theorem finrank_le_ordNegQ_of_minimal (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {y : ↥(unitarySU 2 f K n)} (hyp : y ^ p = 1) {U : Submodule K (Fin n → K)}
    (hUle : U ≤ rng y) (hU0 : U ≠ ⊥) (hUnd : NondegOn (stdHermForm h n) U)
    (hUy : ∀ u ∈ U, lin y u ∈ U)
    (hmin : ∀ W : Submodule K (Fin n → K), W ≤ U → W ≠ ⊥ → NondegOn (stdHermForm h n) W →
      (∀ w ∈ W, lin y w ∈ W) → W = U) :
    finrank K U ≤ ordNegQ 2 f p := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hpK : (p : K) ≠ 0 := by
    rw [natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  set B := stdHermForm h n with hB
  set x := toUnit y with hx
  have H : UnitaryPrimaryData h.bar B x := unitaryPrimaryData_of_pow h hp hp2 hyp
  have hX : (x : Module.End K (Fin n → K)) = lin y := coe_toUnit y
  have hlinp : lin y ^ p = 1 := by rw [← SUTB.lin_pow, hyp, lin_one]
  have hfix : ∀ u ∈ U, lin y u = u → u = 0 := fun u hu hyu =>
    eq_zero_of_fixed_range (hp.odd_of_ne_two hp2) hlinp (hUle hu) hyu
  set yU : Module.End K U := (lin y).restrict hUy with hyU
  have hyUp : yU ^ p = 1 := OrdPNS.restrict_pow_eq_one hlinp hUy
  have hyU1 : yU ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    exact hu0 (hfix u hu (congrArg Subtype.val (LinearMap.congr_fun h1 ⟨u, hu⟩)))
  obtain ⟨g₀, hg₀, hg₀d, hg₀k⟩ := OrdPNS.exists_irreducible_ker_ne_bot hp hyUp hyU1
  obtain ⟨g, hg, hgm, hgg₀, hker⟩ := exists_monic_of_irreducible (V := U) hg₀
  have : Fact (Irreducible g) := ⟨hg⟩
  have hgd : g ∣ cyclotomic p K := hgg₀.trans hg₀d
  have hgk : LinearMap.ker (aeval yU g) ≠ ⊥ := by rw [hker yU]; exact hg₀k
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hgk
  set w : Fin n → K := (w₀ : Fin n → K) with hw
  have hwU : w ∈ U := w₀.2
  have hw0 : w ≠ 0 := fun h0 => hw₀0 (Subtype.ext h0)
  have hwg : aeval (x : Module.End K (Fin n → K)) g w = 0 := by
    have h1 := OrdPNS.coe_aeval_restrict_apply hUy g w₀
    rw [LinearMap.mem_ker.mp hw₀, Submodule.coe_zero] at h1
    rw [hX, hw, ← h1]
  have hgx : g ∈ primaryFactors (x : Module.End K (Fin n → K)) :=
    mem_primaryFactors_of_ker hg hgm hw0 hwg
  have hd := OrdPNS.natDegree_eq_ordQ hp hpK hg hgd
  have he := ordNegQ_pos (f := f) hp hp2
  have hde : g.natDegree ≤ ordNegQ 2 f p := Nat.le_of_dvd he (hd ▸ ordQ_dvd_ordNegQ h p)
  have hUx : ∀ u ∈ U, (x : Module.End K (Fin n → K)) u ∈ U := by rw [hX]; exact hUy
  have hxinv : ∀ (u : Fin n → K), ∀ v ∈ cyc (x : Module.End K (Fin n → K)) u,
      (x : Module.End K (Fin n → K)) v ∈ cyc (x : Module.End K (Fin n → K)) u :=
    fun u => cyc_invariant _ u
  by_cases hself : dualPoly h.bar g = g
  ·
    obtain ⟨u, huU, hu⟩ := exists_selfDualVal_ne_zero h H hgx hself hUnd hUx ⟨w, hwU, hw0, hwg⟩
    have hcyc := nondegOn_cyc_of_selfDualVal h H hgx hself u hu
    have hu0 : (u : Fin n → K) ≠ 0 := by
      intro h0
      apply hu
      have h2 : u = 0 := Subtype.ext h0
      rw [h2]
      have := selfDualVal_smul_right (B := B) (0 : AdjoinRoot g)
        (0 : primaryComponent (x : Module.End K (Fin n → K)) g)
        (0 : primaryComponent (x : Module.End K (Fin n → K)) g)
      rwa [zero_smul, zero_mul] at this
    have heq : cyc (x : Module.End K (Fin n → K)) (u : Fin n → K) = U := by
      refine hmin _ (cyc_le hUx huU) ?_ hcyc ?_
      · intro hbot
        apply hu0
        have h1 : (u : Fin n → K) ∈ cyc (x : Module.End K (Fin n → K)) (u : Fin n → K) := by
          simpa using pow_mem_cyc (x : Module.End K (Fin n → K)) (u : Fin n → K) 0
        rw [hbot, Submodule.mem_bot] at h1
        exact h1
      · intro v hv
        rw [← hX]
        exact hxinv _ v hv
    rw [← heq]
    exact (finrank_cyc_le _ hgm hg.ne_one (mem_primaryComponent.mp u.2)).trans hde
  ·
    obtain ⟨w', hw'U, hww'⟩ := exists_pair_vec h H hgx hUnd hUx hwU hw0 hwg
    have hg'x : dualPoly h.bar g ∈ primaryFactors (x : Module.End K (Fin n → K)) :=
      dualPoly_mem_primaryFactors H hgx
    have hg'irr : Irreducible (dualPoly h.bar g) := irreducible_of_mem_primaryFactors hg'x
    have hne : g ≠ dualPoly h.bar g := fun h' => hself h'.symm
    have hgg : dualPoly h.bar (dualPoly h.bar g) = g := dualPoly_dualPoly_of_mem H hgx
    have hne' : dualPoly h.bar g ≠ dualPoly h.bar (dualPoly h.bar g) := by rw [hgg]; exact hself
    have hVg : ∀ (a : K[X]) (v : Fin n → K),
        v ∈ primaryComponent (x : Module.End K (Fin n → K)) a →
          (x : Module.End K (Fin n → K)) v ∈ primaryComponent (x : Module.End K (Fin n → K)) a :=
      fun a v hv => apply_mem_primaryComponent (Commute.refl _) hv
    have hwV : w ∈ primaryComponent (x : Module.End K (Fin n → K)) g :=
      mem_primaryComponent.mpr hwg
    have hiso : ∀ a ∈ cyc (x : Module.End K (Fin n → K)) w,
        ∀ b ∈ cyc (x : Module.End K (Fin n → K)) w, B a b = 0 := fun a ha b hb =>
      isotropic_primaryComponent H hgx hne (cyc_le (hVg g) hwV ha) (cyc_le (hVg g) hwV hb)
    have hiso' : ∀ a ∈ cyc (x : Module.End K (Fin n → K)) (w' : Fin n → K),
        ∀ b ∈ cyc (x : Module.End K (Fin n → K)) (w' : Fin n → K), B a b = 0 := fun a ha b hb =>
      isotropic_primaryComponent H hg'x hne' (cyc_le (hVg _) w'.2 ha) (cyc_le (hVg _) w'.2 hb)
    have hnd := nondegOn_cyc_sup H.symm H.isom hp.one_lt.le (by rw [hX]; exact hlinp) hg hg'irr
      hwg (mem_primaryComponent.mp w'.2) hww' hiso hiso'
    have heq : cyc (x : Module.End K (Fin n → K)) w ⊔
        cyc (x : Module.End K (Fin n → K)) (w' : Fin n → K) = U := by
      refine hmin _ (sup_le (cyc_le hUx hwU) (cyc_le hUx hw'U)) ?_ hnd ?_
      · intro hbot
        apply hw0
        have h1 : w ∈ cyc (x : Module.End K (Fin n → K)) w ⊔
            cyc (x : Module.End K (Fin n → K)) (w' : Fin n → K) :=
          Submodule.mem_sup_left (by simpa using pow_mem_cyc (x : Module.End K (Fin n → K)) w 0)
        rw [hbot, Submodule.mem_bot] at h1
        exact h1
      · intro v hv
        rw [← hX]
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        exact Submodule.add_mem_sup (hxinv w a ha) (hxinv _ b hb)
    rw [← heq]
    have h1 := Submodule.finrank_add_le_finrank_add_finrank
      (cyc (x : Module.End K (Fin n → K)) w) (cyc (x : Module.End K (Fin n → K)) (w' : Fin n → K))
    have h2 := finrank_cyc_le (x : Module.End K (Fin n → K)) hgm hg.ne_one hwg
    have h3 := finrank_cyc_le (x : Module.End K (Fin n → K)) (monic_of_mem_primaryFactors hg'x)
      hg'irr.ne_one (mem_primaryComponent.mp w'.2)
    have h4 : (dualPoly h.bar g).natDegree = g.natDegree :=
      natDegree_dualPoly (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree hgx)
    have h5 := two_mul_natDegree_le h hp hp2 hg hgm hgd hself
    omega

end Pieces

end OrdPNsU

end CFSG.StandardType
