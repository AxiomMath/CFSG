module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONormA
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.HardMathSupport.U4FF.Outer
public import CFSG.Quasithin.Vol2.Ch10SecD12D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.LieType.Universal.Spin QuadraticMap Matrix
open scoped Pointwise Matrix

theorem k_Omega6Minus_irr :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      NatOmegaMinus H ⊤ ⊥ 6 n → CFSG.LocalAnalysis.RankThreeUC.IsIrrOn H := by
  intro W _ _ H n hN
  intro A hA
  obtain ⟨F, hFfield, hFfinite, b, c, hFcard, hpoly, ε, ψ, hψ⟩ :=
    exists_natCoords_of_natOmegaMinus hN
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFcard])
  let ι : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2
  let V : Type := ι → F
  let Q : QuadraticForm F V := quadMinus 3 F b c
  let ψW : W ≃* Multiplicative V := (Subgroup.topEquiv (G := W)).symm.trans ψ
  have ψW_apply (a : W) : ψW a = ψ ⟨a, Subgroup.mem_top a⟩ := rfl
  let A' : AddSubgroup V :=
    { carrier := {x | Multiplicative.ofAdd x ∈ A.map ψW}
      zero_mem' := by
        change Multiplicative.ofAdd (0 : V) ∈ A.map ψW
        simpa using (A.map ψW).one_mem
      add_mem' := by
        intro x y hx hy
        change Multiplicative.ofAdd (x + y) ∈ A.map ψW
        rw [show Multiplicative.ofAdd (x + y) =
            Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl]
        have hx' : Multiplicative.ofAdd x ∈ A.map ψW := hx
        have hy' : Multiplicative.ofAdd y ∈ A.map ψW := hy
        exact Subgroup.mul_mem (H := A.map ψW) (x := Multiplicative.ofAdd x)
          (y := Multiplicative.ofAdd y) hx' hy'
      neg_mem' := by
        intro x hx
        change Multiplicative.ofAdd (-x) ∈ A.map ψW
        rw [show Multiplicative.ofAdd (-x) = (Multiplicative.ofAdd x)⁻¹ from rfl]
        have hx' : Multiplicative.ofAdd x ∈ A.map ψW := hx
        exact Subgroup.inv_mem (H := A.map ψW) (x := Multiplicative.ofAdd x) hx' }
  let W' : Submodule F V :=
    { carrier := {x | ∀ t : F, t • x ∈ A'}
      zero_mem' := by
        intro t
        simpa using A'.zero_mem
      add_mem' := by
        intro x y hx hy t
        rw [smul_add]
        exact A'.add_mem (hx t) (hy t)
      smul_mem' := by
        intro s x hx t
        simpa only [smul_smul] using hx (t * s) }
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 3 F hpoly
  have hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) := by
    refine ⟨fun i => minusPair F b c (Fin.castLE (by omega : 2 ≤ 3 - 1) i), ?_⟩
    intro i j hij
    exact minusPair_orth (fun h => hij (Fin.castLE_injective _ h))
  have hA'Stated : ∀ B ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∀ y ∈ A', ((B : GL ι F) : Matrix ι ι F) *ᵥ y ∈ A' := by
    intro B hB y hy
    have hy' : Multiplicative.ofAdd y ∈ A.map ψW := hy
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy'
    let h : ↥H := ε.symm ⟨B, hB⟩
    have hε : ε h = ⟨B, hB⟩ := MulEquiv.apply_symm_apply ε ⟨B, hB⟩
    have hha : (h : MulAut W) a ∈ A := hA h.1 h.2 a ha
    have hψa := hψ h ⟨a, Subgroup.mem_top a⟩
    have hay' : Multiplicative.toAdd (ψ ⟨a, Subgroup.mem_top a⟩) = y := by
      have h := congrArg Multiplicative.toAdd hay
      simpa [ψW_apply] using h
    change ∃ a ∈ A, ψW a =
      Multiplicative.ofAdd (((B : GL ι F) : Matrix ι ι F) *ᵥ y)
    refine ⟨(h : MulAut W) a, hha, ?_⟩
    rw [ψW_apply, hψa, hay', hε]
  have hW'Stated : ∀ B ∈ StatedOmega (StatedQuadMinus 3 F b c), ∀ x ∈ W',
      ((B : GL ι F) : Matrix ι ι F) *ᵥ x ∈ W' := by
    intro B hB x hx t
    rw [← Matrix.mulVec_smul]
    exact hA'Stated B hB (t • x) (hx t)
  let SΩ : Subgroup (V ≃ₗ[F] V) :=
    (StatedOmega (StatedQuadMinus 3 F b c)).map (toLinEquiv ι F).toMonoidHom
  have hE : elementaryGroup Q ≤ SΩ := by
    refine elementaryGroup_le_of_eichler_mem ?_
    intro u w _ _
    obtain ⟨B, hB, hBact⟩ :=
      CFSG.LocalAnalysis.RankThreeUC.eichler_mem_statedOmega hpoly u w
    refine Subgroup.mem_map.mpr ⟨B, hB, ?_⟩
    refine LinearEquiv.ext fun x => ?_
    change ((B : GL ι F) : Matrix ι ι F) *ᵥ x = eichler Q u w x
    exact hBact x
  have hA'eich : ∀ u w : V, Q u = 0 → polar Q u w = 0 → ∀ y ∈ A',
      eichler Q u w y ∈ A' := by
    intro u w hu hw y hy
    have hg : eichler Q u w ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q u w
    have hgS : eichler Q u w ∈ SΩ := hE hg
    obtain ⟨B, hB, hBg⟩ := Subgroup.mem_map.mp hgS
    have hBg' : toLinEquiv ι F B = eichler Q u w := hBg
    rw [← hBg']
    change ((B : GL ι F) : Matrix ι ι F) *ᵥ y ∈ A'
    exact hA'Stated B hB y hy
  have hKey : A' ≠ ⊥ → W' ≠ ⊥ := by
    intro hA'ne
    obtain ⟨⟨x, hxA'⟩, hx0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hA'ne
    have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hspan : Submodule.span F {v : V | Q v = 0} = ⊤ :=
      span_singular_eq_top (minusPair F b c (0 : Fin (3 - 1)))
    have hu : ∃ u : V, Q u = 0 ∧ polar Q x u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hzero : ∀ v : V, polar Q x v = 0 := by
        intro v
        have hv : v ∈ Submodule.span F {u : V | Q u = 0} := by
          rw [hspan]
          exact Submodule.mem_top
        have hle : Submodule.span F {u : V | Q u = 0} ≤
            LinearMap.ker ((polarBilin Q) x) := by
          rw [Submodule.span_le]
          intro u hu
          simpa using hcon u hu
        exact hle hv
      obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hx0'
      exact hy (hzero y)
    obtain ⟨u, huQ, hxu⟩ := hu
    have hu0 : u ≠ 0 := by
      intro h0
      exact hxu (by rw [h0, polar_zero_right])
    have hV6 : Module.finrank F V = 6 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp [ι, Fintype.card_sum]
    have horthfin : Module.finrank F
        (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {u})) = 5 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hQ, hV6, finrank_span_singleton hu0]
    have hy : ∃ y ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {u}),
        y ∉ Submodule.span F {u} := by
      by_contra! hsub
      have hle := Submodule.finrank_mono hsub
      rw [horthfin, finrank_span_singleton hu0] at hle
      omega
    obtain ⟨y, hyorth, hyL⟩ := hy
    obtain ⟨w, hwX, hwQ, hwu, hwL⟩ :=
      exists_singular_mem hQ (by omega : 5 ≤ Module.finrank F V) huQ
        (le_rfl : LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {u}) ≤
          LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {u}))
        (fun s hs x hx => by
          rw [mem_orth_span_single_iff, polar_comm]
          have hx' : polar Q x u = 0 := by
            rw [polar_comm]
            exact mem_orth_span_single_iff.mp hx
          exact polar_app_eq_zero_of_mem_pointStabilizer hu0 hs hx')
        hyorth hyL
    let z : V := polar Q x u • w - polar Q x w • u
    have hz0 : z ≠ 0 := by
      intro hz
      have h1 : polar Q x u • w = polar Q x w • u := sub_eq_zero.mp hz
      have hwmem : w ∈ Submodule.span F {u} := by
        rw [Submodule.mem_span_singleton]
        refine ⟨(polar Q x u)⁻¹ * polar Q x w, ?_⟩
        calc ((polar Q x u)⁻¹ * polar Q x w) • u
            = (polar Q x u)⁻¹ • (polar Q x w • u) := (smul_smul _ _ _).symm
          _ = (polar Q x u)⁻¹ • (polar Q x u • w) := by rw [← h1]
          _ = w := inv_smul_smul₀ hxu w
      exact hwL hwmem
    have hzmem : ∀ s : F, s • z ∈ A' := by
      intro s
      have hQw' : Q (s • w) = 0 := by
        rw [map_smul_eq_sq, hwQ, mul_zero]
      have huw' : polar Q u (s • w) = 0 := by
        rw [polar_smul_right_eq, hwu, mul_zero]
      have heich : eichler Q u (s • w) x = x + s • z := by
        rw [eichler_apply huQ huw', hQw']
        simp only [polar_smul_right_eq, zero_mul, add_zero, z]
        module
      have hmem := hA'eich u (s • w) huQ huw' x hxA'
      rw [heich] at hmem
      have := A'.sub_mem hmem hxA'
      simpa using this
    intro hbot
    have hzW : z ∈ W' := fun t => hzmem t
    rw [hbot] at hzW
    exact hz0 (by simpa using hzW)
  rcases submodule_eq_bot_or_top_of_elementaryGroup_invariant hQ hP W'
      (fun g hg x hx => by
        obtain ⟨B, hB, hBg⟩ := Subgroup.mem_map.mp (hE hg)
        have hBg' : toLinEquiv ι F B = g := hBg
        rw [← hBg']
        exact hW'Stated B hB x hx) with hW'bot | hW'top
  · have hA'bot : A' = ⊥ := by
      by_contra hne
      exact hKey hne hW'bot
    refine Or.inl (le_bot_iff.mp fun a ha => ?_)
    have h1 : Multiplicative.toAdd (ψW a) ∈ A' := by
      show Multiplicative.ofAdd (Multiplicative.toAdd (ψW a)) ∈ A.map ψW
      simpa using (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩ : ψW a ∈ A.map ψW)
    rw [hA'bot] at h1
    have h2 : ψW a = 1 := by
      have h3 : Multiplicative.toAdd (ψW a) = 0 := by simpa using h1
      simpa using congrArg Multiplicative.ofAdd h3
    have h3 : ψ ⟨a, Subgroup.mem_top a⟩ = 1 := by
      rw [← ψW_apply a]
      exact h2
    have h4 : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup W)) = 1 :=
      ψ.injective (by rw [h3, map_one])
    simpa using congrArg Subtype.val h4
  · refine Or.inr (eq_top_iff.mpr fun w _ => ?_)
    have hxW : Multiplicative.toAdd (ψW w) ∈ W' := by
      rw [hW'top]
      exact Submodule.mem_top
    have hxA' : Multiplicative.toAdd (ψW w) ∈ A' := by
      have := hxW (1 : F)
      simpa using this
    have hmem : Multiplicative.ofAdd (Multiplicative.toAdd (ψW w)) ∈ A.map ψW := hxA'
    obtain ⟨a, ha, haw⟩ := Subgroup.mem_map.mp hmem
    have haw' : ψW a = ψW w := by
      calc ψW a = Multiplicative.ofAdd (Multiplicative.toAdd (ψW w)) := haw
        _ = ψW w := by simp
    have hae : a = w := ψW.injective haw'
    rwa [hae] at ha

theorem k1_of_irr : K_Omega6Minus_outIndex := by
  have hirr := @k_Omega6Minus_irr
  intro W _ _ H n hn hO hN E hEN hE
  have hS : ∀ s : W, s * s = 1 := by
    obtain ⟨F, _, _, b, c, hF, -, ε, ψ, -⟩ := exists_natCoords_of_natOmegaMinus hN
    haveI := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
    intro s
    have h1 : ψ (⟨s, Subgroup.mem_top s⟩ * ⟨s, Subgroup.mem_top s⟩) = 1 := by
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      funext i
      exact CharTwo.add_self_eq_zero _
    have h2 : (⟨s, Subgroup.mem_top s⟩ * ⟨s, Subgroup.mem_top s⟩ : ↥(⊤ : Subgroup W)) = 1 :=
      ψ.injective (h1.trans (map_one ψ).symm)
    simpa using congrArg Subtype.val h2
  have hU4 : CFSG.LocalAnalysis.RankThreeUC.IsU4Group n H := by
    have hC := CFSG.Blueprint.LieModel.statedClassicalModel
      (isU4_of_isOmegaMinus hO) (by decide)
    obtain ⟨q, hv, hp, he, ⟨e⟩⟩ :=
      KSExact.exists_twistedA_of_statedClassicalModel_PSU (m := 3) hC
    exact ⟨⟨_, hv⟩, ⟨q, hp, he, rfl⟩, ⟨e⟩⟩
  have hirrE : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn (H ⊔ E) := fun U hU =>
    hirr H n hN U fun x hx u hu => hU x (le_sup_left (a := H) hx) u hu
  have hc := CFSG.HardMathSupport.U4FF.card_le_two_mul_inf hS hU4 hE hEN hirrE
  refine CFSG.Quasithin.Vol2.Ch10.SecD.mQuot_le_one_of_card_le ?_ inf_le_left hc
  intro g
  exact ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem k_Omega6Minus_outIndex : K_Omega6Minus_outIndex :=
  k1_of_irr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
