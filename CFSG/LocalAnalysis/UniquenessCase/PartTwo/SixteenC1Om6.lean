module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Model

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem s16c1_fixed_eichler (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (hPP' : P.Orth P') {v : V} (hv : ∀ w : V, polar Q P.e w = 0 → eichler Q P.e w v = v) :
    ∃ c : K, v = c • P.e := by
  have hmain : ∀ w : V, polar Q P.e w = 0 →
      polar Q v P.e • w = (polar Q v w + Q w * polar Q v P.e) • P.e := by
    intro w hw
    have h := hv w hw
    rw [eichler_apply P.Q_e hw v] at h
    exact add_left_cancel (sub_eq_iff_eq_add.mp h)
  have hP'e : polar Q P.e P'.e = 0 := hPP'.ee
  have h1 := hmain P'.e hP'e
  rw [P'.Q_e, zero_mul, add_zero] at h1
  have h2 : polar Q v P'.e = 0 := by
    have h3 := congrArg (fun z => polar Q z P.f) h1
    simp only [polar_smul_left_eq] at h3
    rw [show polar Q P'.e P.f = 0 from by rw [polar_comm, hPP'.fe], mul_zero, P.polar_ef,
      mul_one] at h3
    exact h3.symm
  have ha : polar Q v P.e = 0 := by
    rw [h2, zero_smul] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h P'.e_ne_zero
  have hii : ∀ w : V, polar Q P.e w = 0 → polar Q v w = 0 := by
    intro w hw
    have h1 := hmain w hw
    rw [ha, mul_zero, add_zero] at h1
    have h1' : polar Q v w • P.e = 0 := by simpa using h1.symm
    rcases smul_eq_zero.mp h1' with h | h
    · exact h
    · exact absurd h P.e_ne_zero
  have hperp : P.proj v = 0 := by
    refine P.polarNondegOn_perp hQ (P.proj v) (P.proj_mem_perp v) ?_
    intro z hz
    rw [HypPair.mem_perp] at hz
    have hvz : polar Q v z = 0 := hii z hz.1
    rw [HypPair.proj, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
      hvz, ha, hz.1, hz.2]
    ring
  refine ⟨polar Q v P.f, ?_⟩
  conv_lhs => rw [P.eq_add_proj v]
  rw [ha, zero_smul, hperp, add_zero, add_zero]

end Model

section Helpers

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

private theorem s16c1_elementaryGroup_le_commutator_of_perfect {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (hperf : Group.IsPerfect ↥(elementaryGroup Q)) :
    elementaryGroup Q ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  haveI := hperf
  calc elementaryGroup Q = ⁅elementaryGroup Q, elementaryGroup Q⁆ :=
        (Subgroup.commutator_eq_self).symm
    _ ≤ _ := Subgroup.commutator_mono (elementaryGroup_le_orthogonalGroup Q)
        (elementaryGroup_le_orthogonalGroup Q)

private theorem s16c1_eichler_mem_statedOmega {d : ℕ} (hd : 3 ≤ d) {K : Type} [Field K]
    (b c : K) (hK2 : Nat.card K = 2) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K)}
    (hg : g ∈ elementaryGroup (quadMinus d K b c)) :
    (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g ∈
      StatedOmega (StatedQuadMinus d K b c) := by
  haveI : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK2
  have hQ : (polarBilin (quadMinus d K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite d K hpoly
  have hfr : 6 ≤ Module.finrank K (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
    omega
  have hperf : Group.IsPerfect ↥(elementaryGroup (quadMinus d K b c)) :=
    Group.isPerfect_def.mpr
      (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.commutator_elementaryGroup_eq_top_f2
        hQ hfr)
  have hle : elementaryGroup (quadMinus d K b c) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c)⁆ :=
    s16c1_elementaryGroup_le_commutator_of_perfect hperf
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
    (CFSG.LieType.Universal.Spin.coe_quadMinus d K b c), Subgroup.mem_comap]
  change (toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K)
    ((toLinEquiv (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K).symm g) ∈
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus d K b c)⁆
  rw [MulEquiv.apply_symm_apply]
  exact hle hg

end Helpers

section Natural

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {W : Type} [CommGroup W] [Finite W]

theorem natOmegaMinus_exists_eichler {H : Subgroup (MulAut W)}
    (h : NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), Nat.card K = 2 ∧
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ β : W ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
        ∀ u w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K, ∃ φ ∈ H, ∀ x : W,
          β (φ x) = Multiplicative.ofAdd
            (CFSG.ClassicalGroups.Orthogonal.eichler
              (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) u w
              (Multiplicative.toAdd (β x))) := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := h
  letI := hK
  haveI : Finite K := hKf
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) :=
      (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let β' : W ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    (Subgroup.topEquiv (G := W)).symm.trans (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
  refine ⟨K, hK, hKf, b, c, hK2, hpoly, β', ?_⟩
  intro u w
  have hmem : (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).symm
      (CFSG.ClassicalGroups.Orthogonal.eichler
        (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) u w) ∈
      StatedOmega (StatedQuadMinus 3 K b c) :=
    s16c1_eichler_mem_statedOmega (d := 3) (by norm_num) b c hK2 hpoly
      (eichler_mem_elementaryGroup (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) u w)
  let γ : ↥(StatedOmega (StatedQuadMinus (6 / 2) K b c)) :=
    ⟨(toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).symm
      (CFSG.ClassicalGroups.Orthogonal.eichler
        (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) u w), hmem⟩
  let φ : MulAut W := ((π γ : ↥H) : MulAut W)
  refine ⟨φ, (π γ).2, fun x => ?_⟩
  have hx := hβe γ ⟨x, Subgroup.mem_top x⟩ (Subgroup.mem_top _)
  have hβ' : ∀ y : W, β' y = β ⟨y, Subgroup.mem_top y⟩ := fun y => rfl
  calc
    β' (φ x) = β ⟨φ x, Subgroup.mem_top _⟩ := hβ' _
    _ = β ⟨φ (⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup W)), Subgroup.mem_top _⟩ := rfl
    _ = CFSG.Quasithin.natAct _ γ (β ⟨x, Subgroup.mem_top x⟩) := hx
    _ = CFSG.Quasithin.natAct _ γ (β' x) := by rw [hβ']
    _ = Multiplicative.ofAdd
        (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K
          (γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
          (Multiplicative.toAdd (β' x))) := rfl
    _ = Multiplicative.ofAdd (CFSG.ClassicalGroups.Orthogonal.eichler
          (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) u w
          (Multiplicative.toAdd (β' x))) := by
        rw [show toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K
              (γ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) =
            CFSG.ClassicalGroups.Orthogonal.eichler
              (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) u w from
          MulEquiv.apply_symm_apply
            (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
            (CFSG.ClassicalGroups.Orthogonal.eichler
              (CFSG.LieType.Universal.Spin.quadMinus 3 K b c) u w)]

theorem natOmegaMinus_fixed_eq_one {H : Subgroup (MulAut W)}
    (h : NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1) {w : W} (hw : ∀ φ ∈ H, φ w = w) : w = 1 := by
  obtain ⟨K, hK, hKf, b, c, hK2, hpoly, β, hβ⟩ := natOmegaMinus_exists_eichler h
  letI := hK
  haveI : Finite K := hKf
  let Q : QuadraticForm K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus 3 K b c
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 3 K hpoly
  have hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) := by
    refine ⟨fun i => minusPair K b c (Fin.castLE (by omega : 2 ≤ 3 - 1) i), ?_⟩
    intro i j hij
    exact minusPair_orth (fun h => hij (Fin.castLE_injective _ h))
  obtain ⟨P, hPorth⟩ := hP
  let v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := Multiplicative.toAdd (β w)
  have hfixed : ∀ i : Fin 2, ∃ c : K, v = c • (P i).e := by
    intro i
    fin_cases i
    · refine s16c1_fixed_eichler hQ (hPP' := hPorth 0 1 (by decide)) (v := v) ?_
      intro w' hw'
      obtain ⟨φ, hφH, hφ⟩ := hβ (P 0).e w'
      have h1 : β (φ w) = β w := congrArg β (hw φ hφH)
      have h2 : Multiplicative.ofAdd (eichler Q (P 0).e w' v) = Multiplicative.ofAdd v := by
        rw [← hφ w]
        simpa [v] using h1
      exact Multiplicative.ofAdd.injective h2
    · refine s16c1_fixed_eichler hQ (hPP' := hPorth 1 0 (by decide)) (v := v) ?_
      intro w' hw'
      obtain ⟨φ, hφH, hφ⟩ := hβ (P 1).e w'
      have h1 : β (φ w) = β w := congrArg β (hw φ hφH)
      have h2 : Multiplicative.ofAdd (eichler Q (P 1).e w' v) = Multiplicative.ofAdd v := by
        rw [← hφ w]
        simpa [v] using h1
      exact Multiplicative.ofAdd.injective h2
  obtain ⟨c0, hc0⟩ := hfixed 0
  obtain ⟨c1, hc1⟩ := hfixed 1
  have hc0zero : c0 = 0 := by
    have h1 : polar Q v (P 0).f = c0 := by
      rw [hc0, polar_smul_left_eq, (P 0).polar_ef, mul_one]
    have h2 : polar Q v (P 0).f = 0 := by
      rw [hc1, polar_smul_left_eq, show polar Q (P 1).e (P 0).f = 0 from by
        rw [polar_comm]; exact (hPorth 0 1 (by decide)).fe, mul_zero]
    exact h1.symm.trans h2
  have hβw : β w = 1 := by
    have hv0 : v = 0 := by rw [hc0, hc0zero, zero_smul]
    rw [show β w = Multiplicative.ofAdd v from rfl, hv0]
    simp
  exact β.injective (by rw [hβw, map_one])

theorem natOmegaMinus_commSub_eq_top {H : Subgroup (MulAut W)}
    (h : NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1) : commSub (⊤ : Subgroup W) H = ⊤ := by
  have h_irr := s16c167_mem_irrSet_omegaMinus (Or.inl rfl) h
  show commSub (⊤ : Subgroup W) H = ⊤
  exact h_irr.1

theorem natOmegaMinus_centralizer_eq_one {H : Subgroup (MulAut W)}
    (h : NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1) {x : MulAut W}
    (hx : ∀ φ ∈ H, x * φ = φ * x) : x = 1 := by
  classical
  have h_irr := s16c167_mem_irrSet_omegaMinus (Or.inl rfl) h
  have hirr : IsIrrOn H (⊤ : Subgroup W) (⊤ ⊓ fixV H) := h_irr.2
  have hfixbot : (⊤ : Subgroup W) ⊓ fixV H = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    rw [Subgroup.mem_bot]
    exact natOmegaMinus_fixed_eq_one h (fun φ hφ => (mem_fixV.1 hy.2) φ hφ)
  let A : Subgroup W :=
    { carrier := {y | x y = y}
      one_mem' := map_one x
      mul_mem' := fun {a b} ha hb => by
        change x a = a at ha
        change x b = b at hb
        change x (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        change x a = a at ha
        change x a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hstable : StableUnder H A := by
    intro φ hφ y hy
    change x (φ y) = φ y
    rw [← MulAut.mul_apply, hx φ hφ, MulAut.mul_apply, hy]
  rcases hirr.2.2.2 A hstable (by rw [hfixbot]; exact bot_le) le_top with hAbot | hAtop
  · exfalso
    obtain ⟨K, hK, hKf, b, c, hK2, hpoly, β, hβ⟩ := natOmegaMinus_exists_eichler h
    letI := hK
    haveI : Finite K := hKf
    haveI : Fintype K := Fintype.ofFinite K
    let Q : QuadraticForm K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
      CFSG.LieType.Universal.Spin.quadMinus 3 K b c
    have hQ : (polarBilin Q).Nondegenerate :=
      nondegenerate_polarBilin_quadMinus_of_finite 3 K hpoly
    have hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) := by
      refine ⟨fun i => minusPair K b c (Fin.castLE (by omega : 2 ≤ 3 - 1) i), ?_⟩
      intro i j hij
      exact minusPair_orth (fun hh => hij (Fin.castLE_injective _ hh))
    obtain ⟨P, hPorth⟩ := hP
    have htwo : ∀ t : K, t = 0 ∨ t = 1 := by
      intro t
      have h2 : t ^ 2 = t := by
        have := FiniteField.pow_card t
        rwa [← Nat.card_eq_fintype_card, hK2] at this
      have h3 : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h2, sub_self]
      rcases mul_eq_zero.mp h3 with hh | hh
      · exact Or.inl hh
      · exact Or.inr (sub_eq_zero.mp hh)
    let u : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := (P 0).e
    let w₀ : W := β.symm (Multiplicative.ofAdd u)
    have hβw0 : β w₀ = Multiplicative.ofAdd u := by
      simpa [w₀] using β.apply_symm_apply (Multiplicative.ofAdd u)
    have hw0_ne : w₀ ≠ 1 := by
      intro hh
      have h1 : Multiplicative.ofAdd u = 1 := by
        rw [← hβw0, hh]
        exact map_one β
      exact (P 0).e_ne_zero (by simpa [u] using h1)
    have hxw0 : x w₀ = w₀ := by
      let v₁ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := Multiplicative.toAdd (β (x w₀))
      have hfix : ∀ w' : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
          polar Q u w' = 0 → eichler Q u w' v₁ = v₁ := by
        intro w' hw'
        obtain ⟨φ, hφH, hφ⟩ := hβ u w'
        have hfixφ : φ w₀ = w₀ := by
          apply β.injective
          rw [hφ w₀]
          have hE : eichler Q u w' (Multiplicative.toAdd (β w₀)) = u := by
            rw [hβw0]
            exact eichler_apply_self u w'
          rw [hE]
          exact hβw0.symm
        have hcomm : φ (x w₀) = x w₀ := by
          rw [← MulAut.mul_apply, ← hx φ hφH, MulAut.mul_apply, hfixφ]
        have h2 : Multiplicative.ofAdd (eichler Q u w' v₁) = Multiplicative.ofAdd v₁ := by
          rw [← hφ (x w₀)]
          simpa [v₁] using congrArg β hcomm
        exact Multiplicative.ofAdd.injective h2
      obtain ⟨cc, hcc⟩ :=
        s16c1_fixed_eichler hQ (hPP' := hPorth 0 1 (by decide)) (v := v₁) hfix
      have hv₁_ne : v₁ ≠ 0 := by
        intro h0
        have hxw0_1 : x w₀ = 1 := by
          apply β.injective
          rw [show β (x w₀) = Multiplicative.ofAdd v₁ from rfl, h0]
          simp
        have hw0_1 : w₀ = 1 := by
          have hh := congrArg (fun y => x.symm y) hxw0_1
          simpa using hh
        exact hw0_ne hw0_1
      have hcc1 : cc = 1 := by
        rcases htwo cc with hh | hh
        · exfalso
          apply hv₁_ne
          rw [hcc, hh, zero_smul]
        · exact hh
      rw [hcc1, one_smul] at hcc
      apply β.injective
      rw [show β (x w₀) = Multiplicative.ofAdd v₁ from rfl, hcc]
      exact hβw0.symm
    have hw0A : w₀ ∈ A := by
      change x w₀ = w₀
      exact hxw0
    rw [hfixbot] at hAbot
    rw [hAbot] at hw0A
    exact hw0_ne (Subgroup.mem_bot.1 hw0A)
  · refine MulEquiv.ext fun y => ?_
    have hy : y ∈ A := hAtop ▸ Subgroup.mem_top y
    show x y = y
    exact hy

end Natural

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
