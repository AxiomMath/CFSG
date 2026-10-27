module

public import CFSG.Quasithin.Background.F918V2Defs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Om6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2FixOmega
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONormA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
open QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.SignalizerFunctorTheorem.NonLocal.Orth CFSG.LieType.Universal.Spin

theorem s16c167_endUnits_omegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {U : Subgroup W} (h : NatOmegaMinus H U ⊥ 6 1) :
    Z391.EndUnitsTrivial H U := by
  classical
  have hNat : NatOmegaMinus H U ⊥ 6 1 := h
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := h
  letI := hK
  haveI : Finite K := hKf
  haveI : Fintype K := Fintype.ofFinite K
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hstab : ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := R.U_inv
  let π' : ↥(StatedOmega (StatedQuadMinus (6 / 2) K b c)) →* ↥H := π
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hfixbot : U ⊓ fixV H = ⊥ := s16c167_cfg2_fix_omegaMinus (Or.inl rfl) hNat
  have htwo : ∀ t : K, t = 0 ∨ t = 1 := by
    intro t
    have h2 : t ^ 2 = t := by
      have := FiniteField.pow_card t
      rwa [← Nat.card_eq_fintype_card, hK2] at this
    have h3 : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h2, sub_self]
    rcases mul_eq_zero.mp h3 with hh | hh
    · exact Or.inl hh
    · exact Or.inr (sub_eq_zero.mp hh)
  let Q : QuadraticForm K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) := quadMinus 3 K b c
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 3 K hpoly
  have hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) := by
    refine ⟨fun i => minusPair K b c (Fin.castLE (by omega : 2 ≤ 3 - 1) i), ?_⟩
    intro i j hij
    exact minusPair_orth (fun hh => hij (Fin.castLE_injective _ hh))
  obtain ⟨P, hPorth⟩ := hP
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; simpa using hK2)
  have hex : ∀ u w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K, ∃ φ : ↥H, ∀ x : ↥U,
      β ⟨(φ : MulAut W) (x : W), hstab φ x x.2⟩ =
        Multiplicative.ofAdd (eichler Q u w (Multiplicative.toAdd (β x))) := by
    intro u w
    obtain ⟨A₀, hA₀, hA₀x⟩ :=
      CFSG.LocalAnalysis.RankThreeUC.eichler_mem_statedOmega
        (F := K) (b := b) (c := c) hpoly u w
    let γ : ↥(StatedOmega (StatedQuadMinus (6 / 2) K b c)) := ⟨A₀, hA₀⟩
    refine ⟨π' γ, fun x => ?_⟩
    rw [hβe γ x (hstab (π' γ) x x.2)]
    exact congrArg Multiplicative.ofAdd (hA₀x (Multiplicative.toAdd (β x)))
  intro φ hφ
  have hφ' : ∀ (l : ↥H) (x : ↥U),
      φ ⟨(l : MulAut W) (x : W), hstab l x x.2⟩ =
        ⟨(l : MulAut W) ((φ x : ↥U) : W), hstab l (φ x) (φ x).2⟩ := by
    intro l x
    exact Subtype.ext (hφ l x ⟨(l : MulAut W) (x : W), hstab l x x.2⟩ rfl).symm
  let B : Subgroup ↥U :=
    { carrier := {y | φ y = y}
      one_mem' := map_one φ
      mul_mem' := fun {a b} ha hb => by
        change φ a = a at ha
        change φ b = b at hb
        change φ (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        change φ a = a at ha
        change φ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let A : Subgroup W := B.map U.subtype
  have hAle : A ≤ U := map_subtype_le B
  have hstable : StableUnder H A := by
    intro x hx a ha
    obtain ⟨bb, hbB, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr
      ⟨⟨(x : MulAut W) (bb : W), hstab ⟨x, hx⟩ bb bb.2⟩, ?_, rfl⟩
    have hby : ((φ bb : ↥U) : W) = (bb : W) := congrArg Subtype.val hbB
    have h1 := hφ ⟨x, hx⟩ bb ⟨(x : MulAut W) (bb : W), hstab ⟨x, hx⟩ bb bb.2⟩ rfl
    rw [hby] at h1
    exact Subtype.ext (by simpa using h1.symm)
  have h_irr := s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hNat
  rcases h_irr.2.2.2.2 A hstable (by rw [hfixbot]; exact bot_le) hAle with hAbot | hAtop
  · exfalso
    let u : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := (P 0).e
    obtain ⟨w₀, hβw0⟩ := hβsurj (Multiplicative.ofAdd u)
    have hw0_ne : w₀ ≠ 1 := by
      intro hh
      have h1 : Multiplicative.ofAdd u = 1 := by rw [← hβw0, hh]; exact map_one β
      exact (P 0).e_ne_zero (by simpa [u] using h1)
    have hxw0 : φ w₀ = w₀ := by
      let v₁ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
        Multiplicative.toAdd (β (φ w₀))
      have hfix : ∀ w' : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
          polar Q u w' = 0 → eichler Q u w' v₁ = v₁ := by
        intro w' hw'
        obtain ⟨χ, hχ⟩ := hex u w'
        have hfixχ : (⟨(χ : MulAut W) (w₀ : W), hstab χ w₀ w₀.2⟩ : ↥U) = w₀ := by
          apply hβinj
          have hE : eichler Q u w' (Multiplicative.toAdd (β w₀)) = u := by
            rw [hβw0]
            exact eichler_apply_self u w'
          rw [hχ w₀, hE, hβw0]
        have hfixW : (⟨(χ : MulAut W) ((φ w₀ : ↥U) : W),
            hstab χ (φ w₀) (φ w₀).2⟩ : ↥U) = φ w₀ := by
          apply Subtype.ext
          rw [← congrArg Subtype.val (hφ' χ w₀), hfixχ]
        have h2 : Multiplicative.ofAdd (eichler Q u w' v₁) = Multiplicative.ofAdd v₁ := by
          have h3 := congrArg β hfixW
          rw [hχ (φ w₀)] at h3
          simpa [v₁] using h3
        exact Multiplicative.ofAdd.injective h2
      obtain ⟨cc, hcc⟩ := s16c1_fixed_eichler hQ (hPP' := hPorth 0 1 (by decide)) (v := v₁) hfix
      have hv₁_ne : v₁ ≠ 0 := by
        intro h0
        have hxw0_1 : φ w₀ = 1 := by
          apply hβinj
          rw [show β (φ w₀) = Multiplicative.ofAdd v₁ from rfl, h0]
          simp
        have hw0_1 : w₀ = 1 := by
          have hh := congrArg (fun y => φ.symm y) hxw0_1
          simpa using hh
        exact hw0_ne hw0_1
      have hcc1 : cc = 1 := by
        rcases htwo cc with hh | hh
        · exfalso
          apply hv₁_ne
          rw [hcc, hh, zero_smul]
        · exact hh
      rw [hcc1, one_smul] at hcc
      apply hβinj
      rw [show β (φ w₀) = Multiplicative.ofAdd v₁ from rfl, hcc]
      exact hβw0.symm
    have hw0A : (w₀ : W) ∈ A := Subgroup.mem_map.mpr ⟨w₀, hxw0, rfl⟩
    rw [hAbot, hfixbot] at hw0A
    exact hw0_ne (Subtype.ext (Subgroup.mem_bot.1 hw0A))
  · refine MulEquiv.ext fun y => ?_
    have hy : (y : W) ∈ A := hAtop.symm.le y.2
    obtain ⟨bb, hbB, hby⟩ := Subgroup.mem_map.mp hy
    have hbby : bb = y := Subtype.ext hby
    rw [← hbby]
    exact hbB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
