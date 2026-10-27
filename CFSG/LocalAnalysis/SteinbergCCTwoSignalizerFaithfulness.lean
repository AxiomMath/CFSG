module

public import CFSG.Quasithin.SteinbergBMPerfectSubnormalSignalizer
public import CFSG.Quasithin.SteinbergBMPerfectAbelianCommutator
public import CFSG.LocalAnalysis.SteinbergCEPerfectFixedPoints
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis

open scoped commutatorElement

namespace TwoSignalizer

variable {M : Type*} [Group M]

@[expose] def omegaOneCenter (H : Subgroup M) : Subgroup M where
  carrier := {a | a ∈ H ∧ (∀ b ∈ H, a * b = b * a) ∧ a ^ 2 = 1}
  one_mem' := ⟨H.one_mem, fun b _ => by rw [one_mul, mul_one], one_pow 2⟩
  mul_mem' := by
    rintro a c ⟨ha, hac, ha2⟩ ⟨hc, hcc, hc2⟩
    refine ⟨H.mul_mem ha hc, fun b hb => ?_, ?_⟩
    · rw [mul_assoc, hcc b hb, ← mul_assoc, hac b hb, mul_assoc]
    · calc (a * c) ^ 2 = a * (c * a) * c := by rw [sq]; group
        _ = a * (a * c) * c := by rw [← hac c hc]
        _ = a ^ 2 * c ^ 2 := by rw [sq, sq]; group
        _ = 1 := by rw [ha2, hc2, one_mul]
  inv_mem' := by
    rintro a ⟨ha, hac, ha2⟩
    refine ⟨H.inv_mem ha, fun b hb => ?_, by rw [inv_pow, ha2, inv_one]⟩
    calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * b) * a⁻¹ := by rw [hac b hb]
      _ = b * a⁻¹ := by group

theorem conj_mem_omegaOneCenter {H : Subgroup M} {g a : M}
    (hg : g ∈ Subgroup.normalizer (H : Set M)) (ha : a ∈ omegaOneCenter H) :
    g * a * g⁻¹ ∈ omegaOneCenter H := by
  obtain ⟨haH, hac, ha2⟩ := ha
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg a).mp haH, fun b hb => ?_, by
    rw [conj_pow, ha2, mul_one, mul_inv_cancel]⟩
  have hb' : g⁻¹ * b * g ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) b).mp hb
    rwa [inv_inv] at this
  calc g * a * g⁻¹ * b = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by rw [hac _ hb']
    _ = b * (g * a * g⁻¹) := by group

theorem normalizer_le_normalizer_omegaOneCenter (H : Subgroup M) :
    Subgroup.normalizer (H : Set M) ≤ Subgroup.normalizer (omegaOneCenter H : Set M) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨conj_mem_omegaOneCenter hg, fun h => ?_⟩
  have := conj_mem_omegaOneCenter (Subgroup.inv_mem _ hg) h
  simpa [mul_assoc] using this

theorem conj_mem_inSubgroup_pCore (p : ℕ) {X : Subgroup M} {g y : M}
    (hg : g ∈ Subgroup.normalizer (X : Set M)) (hy : y ∈ CFSG.inSubgroup (CFSG.pCore p) X) :
    g * y * g⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore p) X := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  let φ : MulAut X := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hφk : φ k ∈ CFSG.pCore p X := by
    have hfix := (CFSG.pCore_characteristic (p := p) (G := X)).fixed φ
    rw [← hfix] at hk
    exact hk
  exact Subgroup.mem_map.mpr ⟨φ k, hφk, rfl⟩

theorem normalizer_le_normalizer_inSubgroup_pCore (p : ℕ) (X : Subgroup M) :
    Subgroup.normalizer (X : Set M) ≤
      Subgroup.normalizer (CFSG.inSubgroup (CFSG.pCore p) X : Set M) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨conj_mem_inSubgroup_pCore p hg, fun h => ?_⟩
  have := conj_mem_inSubgroup_pCore p (Subgroup.inv_mem _ hg) h
  simpa [mul_assoc] using this

end TwoSignalizer

open TwoSignalizer

theorem perfect_two_signalizer_faithfulness {M : Type*} [Group M] [Finite M] {X S : Subgroup M}
    (hXp : ⁅X, X⁆ = X) (hXs : X.IsSubnormal) (hS : IsPGroup 2 S)
    (hXS : X ≤ Subgroup.normalizer (S : Set M))
    (hOS : CFSG.inSubgroup (CFSG.pCore 2) X ≤ S) :
    let O := CFSG.inSubgroup (CFSG.pCore 2) X
    let A := Subgroup.closure {a : M | a ∈ O ∧ (∀ b ∈ O, a * b = b * a) ∧ a ^ 2 = 1}
    let V := ⁅A, X⁆
    let W := ⁅Subgroup.closure {s : M | s ∈ S ∧ (∀ b ∈ S, s * b = b * s) ∧ s ^ 2 = 1}, X⁆
    W = ⁅V ⊓ Subgroup.centralizer (S : Set M), X⁆ ∧ W ≤ V ∧ (W ≠ ⊥ ↔ V ≠ ⊥) := by
  intro O A V W
  classical
  obtain ⟨hSX, hXSO⟩ :=
    Quasithin.SteinbergBM.perfect_subnormal_p_signalizer_action Nat.prime_two hXp hXs hS hXS
  have hAeq : A = omegaOneCenter O := by
    show Subgroup.closure (omegaOneCenter O : Set M) = _
    exact Subgroup.closure_eq _
  set B := Subgroup.closure {s : M | s ∈ S ∧ (∀ b ∈ S, s * b = b * s) ∧ s ^ 2 = 1} with hBdef
  have hBeq : B = omegaOneCenter S := by
    show Subgroup.closure (omegaOneCenter S : Set M) = _
    exact Subgroup.closure_eq _
  have hNO : Subgroup.normalizer (X : Set M) ≤ Subgroup.normalizer (O : Set M) :=
    normalizer_le_normalizer_inSubgroup_pCore 2 X
  have hXA : X ≤ Subgroup.normalizer (A : Set M) := by
    rw [hAeq]
    exact (Subgroup.le_normalizer.trans hNO).trans (normalizer_le_normalizer_omegaOneCenter O)
  have hSA : S ≤ Subgroup.normalizer (A : Set M) := by
    rw [hAeq]
    exact (hSX.trans hNO).trans (normalizer_le_normalizer_omegaOneCenter O)
  have hXB : X ≤ Subgroup.normalizer (B : Set M) := by
    rw [hBeq]
    exact hXS.trans (normalizer_le_normalizer_omegaOneCenter S)
  have hAcomm' : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rw [hAeq]
    intro a ha b hb
    exact ha.2.1 b hb.1
  have hAcomm : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAcomm' a a.2 b b.2)⟩⟩
  have hBcomm' : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rw [hBeq]
    intro a ha b hb
    exact ha.2.1 b hb.1
  have hBcomm : IsMulCommutative B := ⟨⟨fun a b => Subtype.ext (hBcomm' a a.2 b b.2)⟩⟩
  have hVX : ⁅V, X⁆ = V :=
    Quasithin.SteinbergBM.perfect_abelian_action_commutator hXp hAcomm hXA
  have hWX : ⁅W, X⁆ = W :=
    Quasithin.SteinbergBM.perfect_abelian_action_commutator hXp hBcomm hXB
  have hVA : V ≤ A := Subgroup.le_normalizer_iff_commutator_le_left.mp hXA
  have hWB : W ≤ B := Subgroup.le_normalizer_iff_commutator_le_left.mp hXB
  have hBS : B ≤ S := by
    rw [hBeq]
    exact fun s hs => hs.1
  have hWO : W ≤ O := by
    calc W ≤ ⁅S, X⁆ := Subgroup.commutator_mono hBS le_rfl
      _ = ⁅X, S⁆ := Subgroup.commutator_comm _ _
      _ ≤ O := hXSO
  have hWA : W ≤ A := by
    intro w hw
    have hwB := hWB hw
    rw [hBeq] at hwB
    rw [hAeq]
    exact ⟨hWO hw, fun b hb => hwB.2.1 b (hOS hb), hwB.2.2⟩
  have hWV : W ≤ V := by
    rw [← hWX]
    exact Subgroup.commutator_mono hWA le_rfl
  have hWC : W ≤ Subgroup.centralizer (S : Set M) := by
    intro w hw
    have hwB := hWB hw
    rw [hBeq] at hwB
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hwB.2.1 b hb).symm
  have hCVB : V ⊓ Subgroup.centralizer (S : Set M) ≤ B := by
    rintro v ⟨hvV, hvC⟩
    have hvA := hVA hvV
    rw [hAeq] at hvA
    rw [hBeq]
    refine ⟨hOS hvA.1, fun b hb => ?_, hvA.2.2⟩
    exact ((Subgroup.mem_centralizer_iff.mp hvC) b hb).symm
  have hWeq : W = ⁅V ⊓ Subgroup.centralizer (S : Set M), X⁆ := by
    apply le_antisymm
    · rw [← hWX]
      exact Subgroup.commutator_mono (le_inf hWV hWC) le_rfl
    · exact Subgroup.commutator_mono hCVB le_rfl
  refine ⟨hWeq, hWV, fun hW hV => hW (le_bot_iff.mp (hV ▸ hWV)), fun hV hW => hV ?_⟩
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have haA := hVA ha
    have hbA := hVA hb
    rw [hAeq] at haA hbA
    exact haA.2.1 b hbA.1
  have hVsq : ∀ a ∈ V, a ^ 2 = 1 := by
    intro a ha
    have haA := hVA ha
    rw [hAeq] at haA
    exact haA.2.2
  have hXV : X ≤ Subgroup.normalizer (V : Set M) := Subgroup.normalizer_commutator_ge_right A X
  have hSV : S ≤ Subgroup.normalizer (V : Set M) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (⁅A, X⁆ : Subgroup M).map (MulAut.conj s) = ⁅A, X⁆
    rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSA hs),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSX hs)]
  let _ : CommGroup V :=
    { (inferInstance : Group V) with
      mul_comm := fun a b => Subtype.ext (hVcomm a a.2 b b.2) }
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    apply Additive.toMul.injective
    apply Subtype.ext
    show ((Additive.toMul x : V) : M) ^ 2 = 1
    exact hVsq _ (Additive.toMul x).2
  let cj : ∀ g : M, g ∈ Subgroup.normalizer (V : Set M) → Additive V →+ Additive V :=
    fun g hg =>
      { toFun := fun v => Additive.ofMul ⟨g * (Additive.toMul v : V) * g⁻¹,
          (Subgroup.mem_normalizer_iff.mp hg _).mp (Additive.toMul v).2⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          show g * 1 * g⁻¹ = 1
          group
        map_add' := fun v w => by
          apply Additive.toMul.injective
          apply Subtype.ext
          show g * ((Additive.toMul v : V) * (Additive.toMul w : V) : M) * g⁻¹ =
            g * (Additive.toMul v : V) * g⁻¹ * (g * (Additive.toMul w : V) * g⁻¹)
          group }
  let ρ : Representation (ZMod 2) X (Additive V) :=
    { toFun := fun x => (cj x (hXV x.2)).toZModLinearMap 2
      map_one' := LinearMap.ext fun v => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show (1 : M) * (Additive.toMul v : V) * (1 : M)⁻¹ = (Additive.toMul v : V)
        group
      map_mul' := fun x y => LinearMap.ext fun v => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show ((x : M) * y) * (Additive.toMul v : V) * ((x : M) * y)⁻¹ =
          (x : M) * ((y : M) * (Additive.toMul v : V) * (y : M)⁻¹) * (x : M)⁻¹
        group }
  let σ : Representation (ZMod 2) S (Additive V) :=
    { toFun := fun s => (cj s (hSV s.2)).toZModLinearMap 2
      map_one' := LinearMap.ext fun v => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show (1 : M) * (Additive.toMul v : V) * (1 : M)⁻¹ = (Additive.toMul v : V)
        group
      map_mul' := fun x y => LinearMap.ext fun v => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show ((x : M) * y) * (Additive.toMul v : V) * ((x : M) * y)⁻¹ =
          (x : M) * ((y : M) * (Additive.toMul v : V) * (y : M)⁻¹) * (x : M)⁻¹
        group }
  have hρσ : ∀ x s, Commute (ρ x) (σ s) := by
    intro x s
    refine LinearMap.ext fun v => ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    show (x : M) * ((s : M) * (Additive.toMul v : V) * (s : M)⁻¹) * (x : M)⁻¹ =
      (s : M) * ((x : M) * (Additive.toMul v : V) * (x : M)⁻¹) * (s : M)⁻¹
    set u : M := ((Additive.toMul v : V) : M) with hu
    have huA : u ∈ omegaOneCenter O := hAeq ▸ hVA (Additive.toMul v).2
    set c : M := (x : M)⁻¹ * (s : M)⁻¹ * x * s with hcdef
    have hc : c ∈ O := by
      apply hXSO
      have := Subgroup.commutator_mem_commutator (X.inv_mem x.2) (S.inv_mem s.2)
      simpa [commutatorElement_def] using this
    have hcu : c * u * c⁻¹ = u := by
      rw [← huA.2.1 c hc]
      group
    calc (x : M) * ((s : M) * u * (s : M)⁻¹) * (x : M)⁻¹
        = (s : M) * x * (c * u * c⁻¹) * (x : M)⁻¹ * (s : M)⁻¹ := by rw [hcdef]; group
      _ = (s : M) * ((x : M) * u * (x : M)⁻¹) * (s : M)⁻¹ := by rw [hcu]; group
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hXp
  have hdet := perfect_action_detected_on_p_fixed_points hS ρ σ hρσ
  have hfix : ∀ x, ∀ v ∈ σ.invariants, ρ x v = v := by
    intro x v hv
    rw [Representation.mem_invariants] at hv
    apply Additive.toMul.injective
    apply Subtype.ext
    show (x : M) * (Additive.toMul v : V) * (x : M)⁻¹ = (Additive.toMul v : V)
    have hvC : ((Additive.toMul v : V) : M) ∈ Subgroup.centralizer (S : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := congrArg (fun w : Additive V => ((Additive.toMul w : V) : M)) (hv ⟨b, hb⟩)
      change b * (Additive.toMul v : V) * b⁻¹ = (Additive.toMul v : V) at h1
      calc b * (Additive.toMul v : V) = b * (Additive.toMul v : V) * b⁻¹ * b := by group
        _ = (Additive.toMul v : V) * b := by rw [h1]
    have hcomm : ⁅((Additive.toMul v : V) : M), (x : M)⁆ ∈
        ⁅V ⊓ Subgroup.centralizer (S : Set M), X⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mpr ⟨(Additive.toMul v).2, hvC⟩) x.2
    rw [← hWeq, hW, Subgroup.mem_bot, commutatorElement_def] at hcomm
    set u : M := ((Additive.toMul v : V) : M) with hu
    calc (x : M) * u * (x : M)⁻¹ = (u * x * u⁻¹ * (x : M)⁻¹)⁻¹ * u := by group
      _ = u := by rw [hcomm, inv_one, one_mul]
  have htriv := hdet.mpr hfix
  have hVX1 : ⁅V, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun f : Additive V →ₗ[ZMod 2] Additive V =>
      ((Additive.toMul (f (Additive.ofMul ⟨u, hu⟩)) : V) : M)) (htriv ⟨x, hx⟩)
    change x * u * x⁻¹ = u at h1
    calc x * u = x * u * x⁻¹ * x := by group
      _ = u * x := by rw [h1]
  rw [← hVX, hVX1]

end CFSG.LocalAnalysis
