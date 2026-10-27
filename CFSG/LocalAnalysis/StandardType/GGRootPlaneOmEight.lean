module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEight
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDFour

public section

namespace CFSG.StandardType

namespace RootPlaneOm

open Module QuadraticMap Multiplicative NoOffOm SUTB Polynomial
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem exists_eigen_of_pow_eq_one {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] [Nontrivial W] {f : Module.End K W} {p : ℕ} (hp0 : 0 < p)
    (hfp : f ^ p = 1) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∃ (μ : K) (w : W), w ≠ 0 ∧ f w = μ • w ∧ μ ^ p = 1 := by
  have hint : IsIntegral K f := Algebra.IsIntegral.isIntegral f
  have hdvd : minpoly K f ∣ X ^ p - C 1 := minpoly.dvd K f (by simp [hfp])
  have hsplit : Splits (minpoly K f) :=
    (X_pow_sub_one_splits hζ).of_dvd (X_pow_sub_C_ne_zero hp0 1) hdvd
  have hdeg : (minpoly K f).degree ≠ 0 := (minpoly.degree_pos hint).ne'
  obtain ⟨μ, hμ⟩ := hsplit.exists_eval_eq_zero hdeg
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_of_isRoot hμ).exists_hasEigenvector
  refine ⟨μ, w, hw.2, hw.apply_eq_smul, ?_⟩
  have h1 := hw.pow_apply p
  rw [hfp, Module.End.one_apply] at h1
  by_contra hμp
  apply hw.2
  have h2 : (μ ^ p - 1) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hμp)

section Eight

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {p : ℕ} {A : Subgroup (GL (Fin d) K)}

theorem eight_facts (hnd : Q.polarBilin.Nondegenerate) (hd : d ≤ 8)
    (hA : GenMax (polB Q) (matrixDerived Q) p A) (hcard : p ^ 4 ≤ Nat.card A) :
    Nat.card K ^ 2 ≡ 1 [MOD p] ∧ (∃ c ∈ A, ∀ v, glin c v = v → v = 0) ∧
      ((∃ ζ : K, IsPrimitiveRoot ζ p) →
        ∃ T : Submodule K (Fin d → K), finrank K T = 4 ∧ ∀ x ∈ T, Q x = 0) := by
  classical
  have : Fact p.Prime := ⟨hA.prime⟩
  obtain ⟨r, ι₀, U, hinj, hrange, hUnd, hUne, horth, hfix, hinv⟩ := exists_blockFrame hA
  have hcardA : Nat.card A = p ^ r := by
    rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin r → ZMod p) ≃ (Fin r → ZMod p)),
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hr : 4 ≤ r := (Nat.pow_le_pow_iff_right hA.prime.one_lt).mp (hcardA ▸ hcard)
  set i : Fin 4 → Fin r := fun k => ⟨k, by omega⟩ with hi
  have hine : ∀ k l, k ≠ l → i k ≠ i l := fun k l hkl h => hkl (Fin.ext (by
    have := congrArg Fin.val h
    simpa [hi] using this))
  have hB : ∀ v, polB Q v v = 0 := fun v =>
    CFSG.ComponentClassification.UnbalancedCatalog.polar_self_charTwo Q v
  have h2 : ∀ a, 2 ≤ finrank K (U a) := fun a => two_le_finrank hB (hUnd a) (hUne a)
  have hsupnd : ∀ a b, a ≠ b → NondegOn (polB Q) (U a ⊔ U b) := fun a b hab =>
    nondegOn_sup (hUnd a) (hUnd b) fun u hu v hv => ⟨horth b a (Ne.symm hab) u hu v hv,
      horth a b hab v hv u hu⟩
  have hfr2 : ∀ a b, a ≠ b → finrank K ↥(U a ⊔ U b) = finrank K (U a) + finrank K (U b) := by
    intro a b hab
    have hinf : U a ⊓ U b = ⊥ := (Submodule.eq_bot_iff _).mpr fun v hv =>
      hUnd a v hv.1 fun n hn => horth a b hab n hn v hv.2
    have h := Submodule.finrank_sup_add_finrank_inf_eq (U a) (U b)
    rwa [hinf, finrank_bot, add_zero] at h
  set X := U (i 0) ⊔ U (i 1) with hX
  set Y := U (i 2) ⊔ U (i 3) with hY
  have hXY : ∀ x ∈ X, ∀ y ∈ Y, polB Q x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add, LinearMap.add_apply]
    rw [horth _ _ (hine 0 2 (by decide)) a ha a' ha', horth _ _ (hine 0 3 (by decide)) a ha b' hb',
      horth _ _ (hine 1 2 (by decide)) b hb a' ha', horth _ _ (hine 1 3 (by decide)) b hb b' hb']
    simp
  have hinfXY : X ⊓ Y = ⊥ := (Submodule.eq_bot_iff _).mpr fun v hv =>
    hsupnd _ _ (hine 0 1 (by decide)) v hv.1 fun n hn => hXY n hn v hv.2
  have hfrXY := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [hinfXY, finrank_bot, add_zero, hfr2 _ _ (hine 0 1 (by decide)),
    hfr2 _ _ (hine 2 3 (by decide))] at hfrXY
  have hle : finrank K ↥(X ⊔ Y) ≤ d := by
    have := Submodule.finrank_le (X ⊔ Y)
    rwa [Module.finrank_fin_fun] at this
  have h20 := h2 (i 0)
  have h21 := h2 (i 1)
  have h22 := h2 (i 2)
  have h23 := h2 (i 3)
  have hdim0 : finrank K (U (i 0)) = 2 := by omega
  have htop : X ⊔ Y = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
  have hzero : ∀ v, (∀ k, v ∈ (U (i k)).orthogonalBilin (polB Q)) → v = 0 := by
    intro v hv
    have hvXY : v ∈ (X ⊔ Y).orthogonalBilin (polB Q) :=
      mem_orth_sup_iff.mpr ⟨mem_orth_sup_iff.mpr ⟨hv 0, hv 1⟩, mem_orth_sup_iff.mpr ⟨hv 2, hv 3⟩⟩
    rw [htop] at hvXY
    exact hnd.2 v fun w => (Submodule.mem_orthogonalBilin.mp hvXY) w Submodule.mem_top
  have hιA : ∀ s, ι₀ s ∈ A := fun s => hrange ▸ ⟨s, rfl⟩
  have hU0 : ∀ a ∈ A, ∀ u ∈ U (i 0), glin a u ∈ U (i 0) := by
    intro a ha u hu
    obtain ⟨s, rfl⟩ := hrange ▸ ha
    exact hinv (toAdd s) (i 0) u hu
  refine ⟨?_, ⟨ι₀ (ofAdd fun _ => 1), hιA _, fun v hv => hzero v fun k =>
    (hfix (fun _ => 1) v).mp hv (i k) one_ne_zero⟩, ?_⟩
  ·
    let _ : MulAction A (U (i 0)) :=
      { smul := fun a u => ⟨glin (a : GL (Fin d) K) u, hU0 a a.2 u u.2⟩
        one_smul := fun u => Subtype.ext (by
          change glin (1 : GL (Fin d) K) u = u
          rw [glin_one]
          rfl)
        mul_smul := fun a b u => Subtype.ext (by
          change glin ((a * b : A) : GL (Fin d) K) u =
            glin (a : GL (Fin d) K) (glin (b : GL (Fin d) K) u)
          rw [Subgroup.coe_mul, glin_mul]
          rfl) }
    have hpA : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.pow a a.2)⟩
    have hmod := hpA.card_modEq_card_fixedPoints (U (i 0))
    have hkey : ∀ u : U (i 0), u ∈ MulAction.fixedPoints A (U (i 0)) → u = 0 := by
      intro u hu
      have h1 : glin (ι₀ (ofAdd (Pi.single (i 0) 1))) u = u :=
        congrArg Subtype.val (hu ⟨_, hιA (ofAdd (Pi.single (i 0) 1))⟩)
      have h2 := (hfix (Pi.single (i 0) 1) u).mp h1 (i 0)
        (by rw [Pi.single_eq_same]; exact one_ne_zero)
      exact Subtype.ext (hUnd (i 0) u u.2 fun n hn => (Submodule.mem_orthogonalBilin.mp h2) n hn)
    have hfixed1 : Nat.card (MulAction.fixedPoints A (U (i 0))) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((hkey a.1 a.2).trans (hkey b.1 b.2).symm)⟩,
        ⟨⟨0, fun g => Subtype.ext (map_zero (glin ((g : A) : GL (Fin d) K)))⟩⟩⟩
    rw [hfixed1] at hmod
    have : Fintype K := Fintype.ofFinite K
    have : Fintype (U (i 0)) := Fintype.ofFinite _
    rwa [Nat.card_eq_fintype_card (α := U (i 0)), Module.card_eq_pow_finrank (K := K),
      ← Nat.card_eq_fintype_card, hdim0] at hmod
  ·
    rintro ⟨ζ, hζ⟩
    have hx : ∀ k : Fin 4, ∃ x ∈ U (i k), x ≠ 0 ∧ Q x = 0 := by
      intro k
      set b := ι₀ (ofAdd (Pi.single (i k) 1)) with hb
      have hbinv : ∀ u ∈ U (i k), glin b u ∈ U (i k) := fun u hu => hinv _ (i k) u hu
      have : Nontrivial (U (i k)) := Submodule.nontrivial_iff_ne_bot.mpr (hUne (i k))
      have hfp : ((glin b).restrict hbinv) ^ p = 1 := by
        rw [Module.End.pow_restrict]
        refine LinearMap.ext fun u => Subtype.ext ?_
        change (glin b ^ p) u = u
        rw [← glin_pow, hA.pow b (hιA _), glin_one]
        rfl
      obtain ⟨μ, w, hw0, hwμ, hμp⟩ := exists_eigen_of_pow_eq_one hA.prime.pos hfp hζ
      have hbw : glin b w = μ • (w : Fin d → K) := congrArg Subtype.val hwμ
      have hw0' : (w : Fin d → K) ≠ 0 := fun h => hw0 (Subtype.ext h)
      have hμ1 : μ ≠ 1 := by
        rintro rfl
        rw [one_smul] at hbw
        have h1 := (hfix (Pi.single (i k) 1) w).mp hbw (i k)
          (by rw [Pi.single_eq_same]; exact one_ne_zero)
        exact hw0' (hUnd (i k) w w.2 fun n hn => (Submodule.mem_orthogonalBilin.mp h1) n hn)
      refine ⟨w, w.2, hw0', ?_⟩
      have hiso : Q (glin b w) = Q w := by
        have hbI := matrixDerived_le_isometries Q (hA.le (hιA (ofAdd (Pi.single (i k) 1))))
        rw [glin_apply, ← matrixLinearEquiv_apply]
        exact (mem_matrixIsometries_iff Q b).mp hbI w
      rw [hbw, QuadraticMap.map_smul, smul_eq_mul] at hiso
      have h3 : (μ * μ - 1) * Q w = 0 := by rw [sub_mul, one_mul, hiso, sub_self]
      refine (mul_eq_zero.mp h3).resolve_left fun h => hμ1 ?_
      have h4 : (μ - 1) * (μ - 1) = 0 := by
        have h5 : (μ - 1) * (μ - 1) = μ * μ - 1 - 2 * μ + 2 := by ring
        rw [h5, h, CharTwo.two_eq_zero]
        ring
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h4)
    choose x hxU hx0 hxQ using hx
    have hpx : ∀ k l, polar Q (x k) (x l) = 0 := by
      intro k l
      by_cases hkl : k = l
      · subst hkl
        exact CFSG.ComponentClassification.UnbalancedCatalog.polar_self_charTwo Q (x k)
      · exact horth _ _ (hine k l hkl) _ (hxU k) _ (hxU l)
    set T := Submodule.span K (Set.range x) with hT
    have hpT1 : ∀ u ∈ T, ∀ k, polar Q (x k) u = 0 := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv => obtain ⟨l, rfl⟩ := hv; exact fun k => hpx k l
      | zero => exact fun k => QuadraticMap.polar_zero_right Q (x k)
      | add u v _ _ hu hv => exact fun k => by rw [polar_add_right, hu k, hv k, add_zero]
      | smul a u _ hu => exact fun k => by rw [polar_smul_right, hu k, smul_zero]
    have hpT : ∀ u ∈ T, ∀ v ∈ T, polar Q v u = 0 := by
      intro u hu v hv
      induction hv using Submodule.span_induction with
      | mem w hw => obtain ⟨l, rfl⟩ := hw; exact hpT1 u hu l
      | zero => exact QuadraticMap.polar_zero_left Q u
      | add v w _ _ hv hw => rw [polar_add_left, hv, hw, add_zero]
      | smul a v _ hv => rw [polar_smul_left, hv, smul_zero]
    have hQT : ∀ u ∈ T, Q u = 0 := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv => obtain ⟨l, rfl⟩ := hv; exact hxQ l
      | zero => exact QuadraticMap.map_zero _
      | add u v hu' hv' hu hv =>
        rw [QuadraticMap.map_add Q u v, hu, hv, hpT v hv' u hu', add_zero, add_zero]
      | smul a u _ hu => rw [QuadraticMap.map_smul, hu, smul_zero]
    have hli : LinearIndependent K x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg k
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ U (i k), polar Q y (x k) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx0 k (hUnd (i k) (x k) (hxU k) fun n hn => hcon n hn)
      have h1 := congrArg (fun v => polarBilin Q y v) hg
      simp only [map_sum, map_smul, map_zero, polarBilin_apply_apply, smul_eq_mul] at h1
      rw [Finset.sum_eq_single k] at h1
      · exact (mul_eq_zero.mp h1).resolve_right hyx
      · intro l _ hlk
        have h0 : polar Q y (x l) = 0 := horth _ _ (hine k l (Ne.symm hlk)) y hy _ (hxU l)
        rw [h0, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ k) h
    exact ⟨T, by rw [hT, finrank_span_eq_card hli, Fintype.card_fin], hQT⟩

end Eight

section MinusEight

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {p : ℕ}

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateMinusIsometry)

theorem not_le_card_of_minus_eight (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadMinus 4 K (by omega) b c))
      (matrixDerived (coordinateQuadMinus 4 K (by omega) b c)) p A) :
    ¬ p ^ 4 ≤ Nat.card A := by
  intro hcard
  classical
  have : Fact p.Prime := ⟨hA.prime⟩
  have hp2 := hA.ne_two
  set Q := coordinateQuadMinus 4 K (by omega) b c with hQ
  obtain ⟨hnd, hW⟩ := CFSG.SeitzReduction.OmegaPilot.regular_wittIndex_coordinateQuadMinus
    (K := K) (m := 4) (by omega) hirr
  obtain ⟨hq2, ⟨g, hgA, hgfix⟩, hT⟩ := eight_facts (Q := Q) hnd (by norm_num) hA hcard
  set q := Nat.card K with hq
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hsq : ((q : ZMod p)) * (q : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hq2
    rw [Nat.cast_pow, Nat.cast_one, _root_.sq] at h
    exact h
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  ·
    have hdvd : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, ← hq, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h1, Nat.cast_one,
        sub_self]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvd
    obtain ⟨T, hT4, hTQ⟩ := hT ⟨(ζ : K), IsPrimitiveRoot.coe_units_iff.mpr
      (hζ ▸ IsPrimitiveRoot.orderOf ζ)⟩
    have := hW T hTQ
    omega
  ·
    have hiso : ∀ h ∈ A, ∀ v, Q (glin h v) = Q v := fun h hh v => by
      rw [glin_apply, ← matrixLinearEquiv_apply]
      exact (mem_matrixIsometries_iff Q h).mp (matrixDerived_le_isometries Q (hA.le hh)) v
    have hgz : ∀ h ∈ Subgroup.zpowers g, h ∈ A := fun h hh =>
      (Subgroup.zpowers_le.mpr hgA) hh
    let _ : MulAction (Subgroup.zpowers g) {v : Fin (2 * 4) → K // Q v = 0} :=
      { smul := fun h v => ⟨glin (h : GL (Fin (2 * 4)) K) v,
          by rw [hiso _ (hgz _ h.2), v.2]⟩
        one_smul := fun v => Subtype.ext (by
          change glin (1 : GL (Fin (2 * 4)) K) v = v
          rw [glin_one]
          rfl)
        mul_smul := fun h h' v => Subtype.ext (by
          change glin ((h * h' : Subgroup.zpowers g) : GL (Fin (2 * 4)) K) v =
            glin (h : GL (Fin (2 * 4)) K) (glin (h' : GL (Fin (2 * 4)) K) v)
          rw [Subgroup.coe_mul, glin_mul]
          rfl) }
    have hpG : IsPGroup p (Subgroup.zpowers g) := fun h =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (hA.pow _ (hgz _ h.2))⟩
    have hmod := hpG.card_modEq_card_fixedPoints {v : Fin (2 * 4) → K // Q v = 0}
    have hkey : ∀ v ∈ MulAction.fixedPoints (Subgroup.zpowers g)
        {v : Fin (2 * 4) → K // Q v = 0}, v = ⟨0, QuadraticMap.map_zero Q⟩ := by
      intro v hv
      exact Subtype.ext (hgfix v (congrArg Subtype.val (hv ⟨g, Subgroup.mem_zpowers g⟩)))
    have hfixed1 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g)
        {v : Fin (2 * 4) → K // Q v = 0}) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((hkey a.1 a.2).trans (hkey b.1 b.2).symm)⟩,
        ⟨⟨⟨0, QuadraticMap.map_zero Q⟩, fun h => Subtype.ext
          (map_zero (glin ((h : Subgroup.zpowers g) : GL (Fin (2 * 4)) K)))⟩⟩⟩
    rw [hfixed1] at hmod
    have hN := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) 3 hirr).1
    rw [CFSG.Timmesfeld.ClassicalOrders.card_singular_congr
      (coordinateMinusIsometry 4 K (by omega) b c)] at hN
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    have h3 := congrArg (fun z : ℤ => (z : ZMod p)) hN
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_pow,
      Int.cast_sub] at h3
    rw [h2, ← hq, h1] at h3
    have h4 : ((4 : ℕ) : ZMod p) = 0 := by
      push_cast at h3 ⊢
      linear_combination h3
    have h5 : p ∣ 2 ^ 2 := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using h4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hA.prime Nat.prime_two).mp (hA.prime.dvd_of_dvd_pow h5))

end MinusEight

end RootPlaneOm

end CFSG.StandardType
