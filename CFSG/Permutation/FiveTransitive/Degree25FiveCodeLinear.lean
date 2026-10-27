module

public import CFSG.Permutation.FiveTransitive.Degree25FiveCodeAut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace FiveTransitive.Degree25

open FiveTransitive.Degree24

@[expose] abbrev StandardFiveParameters := Fin 3 → ZMod 5

private abbrev standardFiveWeightClass (k : ℕ) :=
  {v : StandardFiveParameters //
    fiveWeight (standardFiveCodeVector v) = k}

private theorem standardFiveWeightClass_card_two :
    Nat.card (standardFiveWeightClass 2) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem standardFiveWeightClass_card_three :
    Nat.card (standardFiveWeightClass 3) = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem standardFiveWeightClass_card_four :
    Nat.card (standardFiveWeightClass 4) = 52 := by
  rw [Nat.card_eq_fintype_card]
  decide

private def standardFiveWeightEquiv
    (g :
      StandardFiveParameters ≃ₗ[ZMod 5]
        StandardFiveParameters)
    (hweight :
      ∀ v : StandardFiveParameters,
        fiveWeight (standardFiveCodeVector (g v)) =
          fiveWeight (standardFiveCodeVector v))
    (k : ℕ) :
    standardFiveWeightClass k ≃
      standardFiveWeightClass k where
  toFun v :=
    ⟨g v.1, (hweight v.1).trans v.2⟩
  invFun v :=
    ⟨g.symm v.1, by
      have h := hweight (g.symm v.1)
      rw [g.apply_symm_apply] at h
      exact h.symm.trans v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact g.symm_apply_apply v.1
  right_inv v := by
    apply Subtype.ext
    exact g.apply_symm_apply v.1

private abbrev standardFiveFixedWeight
    (g :
      StandardFiveParameters ≃ₗ[ZMod 5]
        StandardFiveParameters)
    (hweight :
      ∀ v : StandardFiveParameters,
        fiveWeight (standardFiveCodeVector (g v)) =
          fiveWeight (standardFiveCodeVector v))
    (k : ℕ) :=
  Function.fixedPoints
    (standardFiveWeightEquiv g hweight k).toFun

theorem standardFiveCode_weight_preserving_order_ne_five
    (g :
      StandardFiveParameters ≃ₗ[ZMod 5]
        StandardFiveParameters)
    (hweight :
      ∀ v : StandardFiveParameters,
        fiveWeight (standardFiveCodeVector (g v)) =
          fiveWeight (standardFiveCodeVector v)) :
    orderOf g ≠ 5 := by
  classical
  intro horder
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hgpow : g ^ 5 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one g
  let N :
      StandardFiveParameters →ₗ[ZMod 5]
        StandardFiveParameters :=
    g.toLinearMap - LinearMap.id
  let K : Submodule (ZMod 5) StandardFiveParameters :=
    LinearMap.ker N
  have hKiff (v : StandardFiveParameters) :
      v ∈ K ↔ g v = v := by
    change g v - v = 0 ↔ g v = v
    exact sub_eq_zero
  have hfixedWeightLower :
      4 ≤ Nat.card (standardFiveFixedWeight g hweight 2) ∧
        3 ≤ Nat.card
          (standardFiveFixedWeight g hweight 3) ∧
        2 ≤ Nat.card
          (standardFiveFixedWeight g hweight 4) := by
    have hmodeq (k : ℕ) :
        Nat.card (standardFiveWeightClass k) ≡
          Nat.card
            (standardFiveFixedWeight g hweight k) [MOD 5] := by
      let w :=
        standardFiveWeightEquiv g hweight k
      have hwpow : w ^ 5 = 1 := by
        apply Equiv.ext
        intro v
        apply Subtype.ext
        change (g ^ 5) v.1 = v.1
        rw [hgpow]
        rfl
      let f : Function.End (standardFiveWeightClass k) :=
        w.toFun
      have hfpow : f ^ 5 = 1 := by
        funext v
        change w.toFun^[5] v = v
        have hwapp : (w ^ 5) v = v := by
          rw [hwpow]
          rfl
        simpa only [Function.iterate_succ_apply,
          Function.iterate_zero_apply, Equiv.Perm.coe_pow,
          Equiv.toFun_as_coe, one_apply, f] using hwapp
      simpa only [standardFiveFixedWeight, f, w,
        Nat.card_eq_fintype_card] using
        (Equiv.Perm.card_fixedPoints_modEq
          (f := f) (p := 5) (n := 1)
          (by simpa only [pow_one] using hfpow))
    have htwo := hmodeq 2
    have hthree := hmodeq 3
    have hfour := hmodeq 4
    rw [standardFiveWeightClass_card_two] at htwo
    rw [standardFiveWeightClass_card_three] at hthree
    rw [standardFiveWeightClass_card_four] at hfour
    change
      24 % 5 =
        Nat.card
          (standardFiveFixedWeight g hweight 2) % 5 at htwo
    change
      48 % 5 =
        Nat.card
          (standardFiveFixedWeight g hweight 3) % 5 at hthree
    change
      52 % 5 =
        Nat.card
          (standardFiveFixedWeight g hweight 4) % 5 at hfour
    have htwoLower :
        4 ≤ Nat.card
          (standardFiveFixedWeight g hweight 2) := by
      calc
        4 = 24 % 5 := by norm_num
        _ = Nat.card
            (standardFiveFixedWeight g hweight 2) % 5 :=
          htwo
        _ ≤ Nat.card
            (standardFiveFixedWeight g hweight 2) :=
          Nat.mod_le _ _
    have hthreeLower :
        3 ≤ Nat.card
          (standardFiveFixedWeight g hweight 3) := by
      calc
        3 = 48 % 5 := by norm_num
        _ = Nat.card
            (standardFiveFixedWeight g hweight 3) % 5 :=
          hthree
        _ ≤ Nat.card
            (standardFiveFixedWeight g hweight 3) :=
          Nat.mod_le _ _
    have hfourLower :
        2 ≤ Nat.card
          (standardFiveFixedWeight g hweight 4) := by
      calc
        2 = 52 % 5 := by norm_num
        _ = Nat.card
            (standardFiveFixedWeight g hweight 4) % 5 :=
          hfour
        _ ≤ Nat.card
            (standardFiveFixedWeight g hweight 4) :=
          Nat.mod_le _ _
    exact ⟨htwoLower, hthreeLower, hfourLower⟩
  let fixedToK (k : ℕ) :
      standardFiveFixedWeight g hweight k → K :=
    fun v =>
      ⟨v.1.1, (hKiff v.1.1).mpr (by
        exact congrArg Subtype.val v.2)⟩
  let fixedSumToK :
      standardFiveFixedWeight g hweight 2 ⊕
          (standardFiveFixedWeight g hweight 3 ⊕
            standardFiveFixedWeight g hweight 4) →
        K
    | Sum.inl v => fixedToK 2 v
    | Sum.inr (Sum.inl v) => fixedToK 3 v
    | Sum.inr (Sum.inr v) => fixedToK 4 v
  have hfixedSumInjective :
      Function.Injective fixedSumToK := by
    have hinj (k : ℕ) :
        Function.Injective (fixedToK k) := by
      intro a b hab
      have hval : a.1.1 = b.1.1 :=
        congrArg (fun z : K => z.1) hab
      exact Subtype.ext (Subtype.ext hval)
    have hne {k m : ℕ} (hkm : k ≠ m)
        (a : standardFiveFixedWeight g hweight k)
        (b : standardFiveFixedWeight g hweight m) :
        fixedToK k a ≠ fixedToK m b := by
      intro hab
      have hval : a.1.1 = b.1.1 :=
        congrArg (fun z : K => z.1) hab
      have ha := a.1.2
      have hb := b.1.2
      rw [hval] at ha
      exact hkm (ha.symm.trans hb)
    intro x y hab
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            exact congrArg Sum.inl (hinj 2 hab)
        | inr b =>
            cases b with
            | inl b => exact (hne (by norm_num) a b hab).elim
            | inr b => exact (hne (by norm_num) a b hab).elim
    | inr a =>
        cases a with
        | inl a =>
            cases y with
            | inl b => exact (hne (by norm_num) a b hab).elim
            | inr b =>
                cases b with
                | inl b =>
                    exact congrArg (fun z => Sum.inr (Sum.inl z))
                      (hinj 3 hab)
                | inr b =>
                    exact (hne (by norm_num) a b hab).elim
        | inr a =>
            cases y with
            | inl b => exact (hne (by norm_num) a b hab).elim
            | inr b =>
                cases b with
                | inl b =>
                    exact (hne (by norm_num) a b hab).elim
                | inr b =>
                    exact congrArg (fun z => Sum.inr (Sum.inr z))
                      (hinj 4 hab)
  have hKcardLower : 9 ≤ Nat.card K := by
    have hle :=
      Nat.card_le_card_of_injective
        fixedSumToK hfixedSumInjective
    rw [Nat.card_sum, Nat.card_sum] at hle
    omega
  have hVfinrank :
      Module.finrank (ZMod 5) StandardFiveParameters = 3 := by
    rw [Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hKfinrankLe :
      Module.finrank (ZMod 5) K ≤ 3 := by
    calc
      Module.finrank (ZMod 5) K ≤
          Module.finrank (ZMod 5)
            StandardFiveParameters :=
        Submodule.finrank_le K
      _ = 3 := hVfinrank
  have hKfinrank :
      Module.finrank (ZMod 5) K = 2 := by
    let d := Module.finrank (ZMod 5) K
    have hdcases :
        d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by
      dsimp only [d]
      omega
    rcases hdcases with hd | hd | hd | hd
    · have hKfinrankZero :
          Module.finrank (ZMod 5) K = 0 := by
        simpa only [d] using hd
      have hKpow :=
        Module.natCard_eq_pow_finrank
          (K := ZMod 5) (V := K)
      have hKcard : Nat.card K = 1 := by
        simpa [Nat.card_zmod, hKfinrankZero] using hKpow
      rw [hKcard] at hKcardLower
      norm_num at hKcardLower
    · have hKfinrankOne :
          Module.finrank (ZMod 5) K = 1 := by
        simpa only [d] using hd
      have hKpow :=
        Module.natCard_eq_pow_finrank
          (K := ZMod 5) (V := K)
      have hKcard : Nat.card K = 5 := by
        simpa [Nat.card_zmod, hKfinrankOne] using hKpow
      rw [hKcard] at hKcardLower
      norm_num at hKcardLower
    · exact hd
    · have hKfinrankThree :
          Module.finrank (ZMod 5) K = 3 := by
        simpa only [d] using hd
      have hKtop : K = ⊤ :=
        Submodule.eq_top_of_finrank_eq
          (hKfinrankThree.trans hVfinrank.symm)
      have hNzero : N = 0 :=
        LinearMap.ker_eq_top.mp hKtop
      have hgOne : g = 1 := by
        apply LinearEquiv.ext
        intro v
        have happ :=
          LinearMap.congr_fun hNzero v
        change g v - v = 0 at happ
        simpa using sub_eq_zero.mp happ
      rw [hgOne, orderOf_one] at horder
      norm_num at horder
  have hRangeFinrank :
      Module.finrank (ZMod 5)
          (LinearMap.range N) = 1 := by
    have hrank :=
      LinearMap.finrank_range_add_finrank_ker N
    rw [hKfinrank, hVfinrank] at hrank
    omega
  let eRange :
      ZMod 5 ≃ₗ[ZMod 5] LinearMap.range N :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one
      hRangeFinrank).some
  let l : StandardFiveParameters :=
    (eRange 1).1
  have hl : l ≠ 0 := by
    intro hlZero
    have heZero : eRange (1 : ZMod 5) = 0 := by
      apply Subtype.ext
      exact hlZero
    have : (1 : ZMod 5) = 0 := eRange.injective
      (heZero.trans (map_zero eRange).symm)
    norm_num at this
  let φ :
      StandardFiveParameters →ₗ[ZMod 5] ZMod 5 :=
    eRange.symm.toLinearMap.comp N.rangeRestrict
  have hN_eq (v : StandardFiveParameters) :
      N v = φ v • l := by
    have heApply :
        eRange (φ v) = N.rangeRestrict v :=
      eRange.apply_symm_apply (N.rangeRestrict v)
    have heScalar :
        eRange (φ v) = φ v • eRange (1 : ZMod 5) := by
      calc
        eRange (φ v) =
            eRange (φ v • (1 : ZMod 5)) := by
          rw [smul_eq_mul, mul_one]
        _ = φ v • eRange (1 : ZMod 5) :=
          map_smul eRange (φ v) 1
    exact congrArg Subtype.val
      (heApply.symm.trans heScalar)
  have hφne : φ ≠ 0 := by
    intro hφZero
    have hNzero : N = 0 := by
      apply LinearMap.ext
      intro v
      rw [hN_eq, hφZero]
      simp
    have hgOne : g = 1 := by
      apply LinearEquiv.ext
      intro v
      have happ :=
        LinearMap.congr_fun hNzero v
      change g v - v = 0 at happ
      simpa using sub_eq_zero.mp happ
    rw [hgOne, orderOf_one] at horder
    norm_num at horder
  let c : Fin 3 → ZMod 5 :=
    fun i => φ (Pi.single i 1)
  have hφdot (v : StandardFiveParameters) :
      φ v = standardFiveCodeDot c v := by
    have hv :
        v = ∑ i, (v i) •
          Pi.single i (1 : ZMod 5) := by
      calc
        v = ∑ i, Pi.single i (v i) :=
          (Finset.univ_sum_single v).symm
        _ = ∑ i, (v i) •
            Pi.single i (1 : ZMod 5) := by
          apply Finset.sum_congr rfl
          intro i _
          ext j
          by_cases hij : i = j
          · subst j
            simp
          · simp [hij]
    calc
      φ v = φ (∑ i, (v i) •
          Pi.single i (1 : ZMod 5)) := by rw [← hv]
      _ = ∑ i, (v i) •
          φ (Pi.single i (1 : ZMod 5)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
      _ = standardFiveCodeDot c v := by
        simp only [standardFiveCodeDot, c, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  have hcne : c ≠ 0 := by
    intro hcZero
    apply hφne
    apply LinearMap.ext
    intro v
    rw [hφdot, hcZero]
    simp [standardFiveCodeDot]
  have hg_eq (v : StandardFiveParameters) :
      g v = standardFiveCodeShear l c v := by
    have hNv := hN_eq v
    change g v - v = φ v • l at hNv
    rw [hφdot] at hNv
    rw [standardFiveCodeShear]
    calc
      g v = (g v - v) + v := by abel
      _ = standardFiveCodeDot c v • l + v := by
        rw [hNv]
      _ = v + standardFiveCodeDot c v • l :=
        add_comm _ _
  have hφl : φ l = 0 := by
    let a : ZMod 5 := φ l
    have hgl : g l = (1 + a) • l := by
      calc
        g l = l + φ l • l := by
          have hNl := hN_eq l
          change g l - l = φ l • l at hNl
          calc
            g l = (g l - l) + l := by abel
            _ = φ l • l + l := by rw [hNl]
            _ = l + φ l • l := add_comm _ _
        _ = (1 + a) • l := by
          simp [a, add_smul]
    have hgpowApply :
        (g ^ 5) l = l := by
      rw [hgpow]
      rfl
    have hiterate (n : ℕ) :
        (g ^ n) l = (1 + a) ^ n • l := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, LinearEquiv.mul_apply, hgl,
            map_smul, ih, smul_smul, pow_succ]
          rw [mul_comm]
    rw [hiterate 5] at hgpowApply
    have hscalar : (1 + a) ^ 5 = 1 := by
      by_contra hne
      have hzero :
          (((1 + a) ^ 5 - 1) : ZMod 5) • l = 0 := by
        rw [sub_smul, one_smul, hgpowApply, sub_self]
      rcases smul_eq_zero.mp hzero with hscalarZero | hlZero
      · exact hne (sub_eq_zero.mp hscalarZero)
      · exact hl hlZero
    have hfrobenius :
        (1 + a) ^ 5 = 1 + a := by
      exact ZMod.pow_card (1 + a)
    have ha : a = 0 := by
      rw [hfrobenius] at hscalar
      exact add_left_cancel
        (hscalar.trans (add_zero 1).symm)
    exact ha
  have hcl : standardFiveCodeDot c l = 0 := by
    rw [← hφdot]
    exact hφl
  apply
    standardFiveCode_no_weight_preserving_transvection
      l c hl hcne hcl
  intro v
  rw [← hg_eq]
  exact hweight v

end FiveTransitive.Degree25

end CFSG
