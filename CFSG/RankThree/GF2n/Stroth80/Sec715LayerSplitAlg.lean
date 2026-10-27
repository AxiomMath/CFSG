module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjCited

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.Open
open scoped Matrix

variable {K X H : Type} [Field K] [AddCommGroup X] [Module K X] [Group H]

section Avg

variable [Fintype K] [DecidableEq K]

theorem card_units_ne_zero : ((Fintype.card (Units K) : ℕ) : K) ≠ 0 := by
  have hq : (Fintype.card K : K) = 0 := FiniteField.cast_card_eq_zero K
  have h1 : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [Fintype.card_units, Nat.cast_sub h1, hq, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

variable (K) in
@[expose] noncomputable def avgUnits (p : X →+ X) (v : X) : X :=
  ((Fintype.card (Units K) : ℕ) : K)⁻¹ • ∑ c : Units K, ((c⁻¹ : Units K) : K) • p ((c : K) • v)

theorem avgUnits_add (p : X →+ X) (v v' : X) :
    avgUnits K p (v + v') = avgUnits K p v + avgUnits K p v' := by
  simp only [avgUnits, smul_add, map_add, Finset.sum_add_distrib]

theorem avgUnits_smul (p : X →+ X) (a : K) (v : X) :
    avgUnits K p (a • v) = a • avgUnits K p v := by
  by_cases ha : a = 0
  · subst ha
    simp [avgUnits]
  · let u : Units K := Units.mk0 a ha
    have hsum : ∑ c : Units K, ((c⁻¹ : Units K) : K) • p ((c : K) • (a • v)) =
        a • ∑ c : Units K, ((c⁻¹ : Units K) : K) • p ((c : K) • v) := by
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulRight u) _ _ fun c => ?_
      simp only [Equiv.coe_mulRight, Units.val_mul, mul_inv_rev, smul_smul, u, Units.val_mk0]
      congr 1
      rw [Units.val_inv_eq_inv_val (Units.mk0 a ha), Units.val_mk0]
      field_simp
    rw [avgUnits, avgUnits, hsum, smul_comm]

theorem avgUnits_mem (p : X →+ X) (W : Submodule K X) (hpW : ∀ v, p v ∈ W) (v : X) :
    avgUnits K p v ∈ W :=
  W.smul_mem _ (W.sum_mem fun c _ => W.smul_mem _ (hpW _))

theorem avgUnits_eq_self (p : X →+ X) (W : Submodule K X) (hp : ∀ w ∈ W, p w = w) {w : X}
    (hw : w ∈ W) : avgUnits K p w = w := by
  have h : ∀ c : Units K, ((c⁻¹ : Units K) : K) • p ((c : K) • w) = w := fun c => by
    rw [hp _ (W.smul_mem _ hw), smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]
  simp only [avgUnits, h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ card_units_ne_zero, one_smul]

theorem exists_linear_proj (W : Submodule K X) (p : X →+ X) (hpW : ∀ v, p v ∈ W)
    (hp : ∀ w ∈ W, p w = w) (T : H → X →ₗ[K] X) (hT : ∀ h v, p (T h v) = T h (p v)) :
    ∃ pK : X →ₗ[K] X, (∀ v, pK v ∈ W) ∧ (∀ w ∈ W, pK w = w) ∧
      ∀ h v, pK (T h v) = T h (pK v) := by
  refine ⟨⟨⟨avgUnits K p, avgUnits_add p⟩, avgUnits_smul p⟩, avgUnits_mem p W hpW,
    fun w hw => avgUnits_eq_self p W hp hw, fun h v => ?_⟩
  show avgUnits K p (T h v) = T h (avgUnits K p v)
  rw [avgUnits, avgUnits, LinearMap.map_smul (T h), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.map_smul (T h), ← hT, LinearMap.map_smul (T h)]

end Avg

section Inv

variable {act : H →* (X ≃ₗ[K] X)}

theorem IsInvSub.inv_mem {U : Submodule K X} (hU : IsInvSub act U) (h : H) {x : X} (hx : x ∈ U) :
    (act h).symm x ∈ U := by
  have := hU h⁻¹ x hx
  rwa [map_inv, LinearEquiv.coe_inv] at this

theorem IsInvSub.map_eq {U : Submodule K X} (hU : IsInvSub act U) (h : H) :
    U.map ((act h : X ≃ₗ[K] X) : X →ₗ[K] X) = U := by
  refine le_antisymm ?_ fun x hx => ⟨(act h).symm x, hU.inv_mem h hx, by simp⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hU h y hy

variable [Fintype K] [DecidableEq K]

theorem exists_invSub_isCompl (W : Submodule K X) (p : X →+ X) (hpW : ∀ v, p v ∈ W)
    (hp : ∀ w ∈ W, p w = w) (hpact : ∀ h v, p (act h v) = act h (p v)) :
    ∃ W' : Submodule K X, IsInvSub act W' ∧ IsCompl W W' := by
  obtain ⟨pK, hpKW, hpK, hpKact⟩ :=
    exists_linear_proj W p hpW hp (fun h => ((act h : X ≃ₗ[K] X) : X →ₗ[K] X)) hpact
  let f : X →ₗ[K] W := pK.codRestrict W hpKW
  have hf : ∀ x : W, f x = x := fun x => Subtype.ext (hpK x x.2)
  refine ⟨LinearMap.ker f, fun h x hx => ?_, LinearMap.isCompl_of_proj hf⟩
  rw [LinearMap.mem_ker] at hx ⊢
  have hx' : pK x = 0 := congrArg Subtype.val hx
  refine Subtype.ext ?_
  show pK (act h x) = 0
  have := hpKact h x
  simp only [LinearEquiv.coe_coe] at this
  rw [this, hx', map_zero]

end Inv

section Restrict

variable (act : H →* (X ≃ₗ[K] X)) {Y : Submodule K X} (hY : IsInvSub act Y)

@[expose] noncomputable def restrictAct : H →* (↥Y ≃ₗ[K] ↥Y) where
  toFun h := (act h).ofSubmodules Y Y (hY.map_eq h)
  map_one' := LinearEquiv.ext fun y => Subtype.ext (by
    show act 1 (y : X) = y
    rw [map_one]
    rfl)
  map_mul' g h := LinearEquiv.ext fun y => Subtype.ext (by
    show act (g * h) (y : X) = act g (act h y)
    rw [map_mul]
    rfl)

theorem coe_restrictAct (h : H) (y : ↥Y) : ((restrictAct act hY h y : ↥Y) : X) = act h y := rfl

theorem map_restrictAct_sub (h : H) :
    (LinearMap.range (((restrictAct act hY h : ↥Y ≃ₗ[K] ↥Y) : ↥Y →ₗ[K] ↥Y) - LinearMap.id)).map
        Y.subtype = Y.map ((act h : X →ₗ[K] X) - LinearMap.id) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.sub_apply, LinearMap.id_apply,
    Submodule.subtype_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, y.2, by simp [coe_restrictAct]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, by simp [coe_restrictAct]⟩

theorem finrank_map_sub_eq (h : H) :
    Module.finrank K (Y.map ((act h : X →ₗ[K] X) - LinearMap.id)) =
      Module.finrank K (LinearMap.range (((restrictAct act hY h : ↥Y ≃ₗ[K] ↥Y) :
        ↥Y →ₗ[K] ↥Y) - LinearMap.id)) := by
  rw [← map_restrictAct_sub act hY h]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ Y.injective_subtype _).symm

theorem restrictAct_irred (hirr : IsIrrSub act Y) :
    ∀ S : Submodule K ↥Y, (∀ h : H, ∀ x ∈ S, restrictAct act hY h x ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS
  have hinv : IsInvSub act (S.map Y.subtype) := by
    rintro h _ ⟨y, hy, rfl⟩
    exact ⟨_, hS h y hy, rfl⟩
  rcases hirr.2.2 _ (Submodule.map_subtype_le Y S) hinv with h0 | h1
  · left
    exact Submodule.map_injective_of_injective Y.injective_subtype
      (h0.trans (Submodule.map_bot _).symm)
  · right
    rw [eq_top_iff]
    intro y _
    have : (y : X) ∈ S.map Y.subtype := by rw [h1]; exact y.2
    obtain ⟨z, hz, hzy⟩ := this
    rwa [← Subtype.ext hzy]

end Restrict

section Split

variable {act : H →* (X ≃ₗ[K] X)} [FiniteDimensional K X]

theorem exists_isIrrSub_le {U : Submodule K X} (hU : IsInvSub act U) (hU0 : U ≠ ⊥) :
    ∃ Y ≤ U, IsIrrSub act Y := by
  classical
  have hP : ∃ k, ∃ Y ≤ U, IsInvSub act Y ∧ Y ≠ ⊥ ∧ Module.finrank K Y = k :=
    ⟨_, U, le_rfl, hU, hU0, rfl⟩
  obtain ⟨Y, hYU, hYinv, hY0, hYk⟩ := Nat.find_spec hP
  refine ⟨Y, hYU, hY0, hYinv, fun Y' hY'Y hY'inv => ?_⟩
  by_cases h0 : Y' = ⊥
  · exact Or.inl h0
  · right
    have hle : Nat.find hP ≤ Module.finrank K Y' :=
      Nat.find_min' hP ⟨Y', hY'Y.trans hYU, hY'inv, h0, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hY'Y (hYk ▸ hle)

theorem exists_invSub_finrank_one_of_trivial {Y : Submodule K X} (hY0 : Y ≠ ⊥)
    (htriv : ∀ h : H, ∀ y ∈ Y, act h y = y) :
    ∃ U : Submodule K X, IsInvSub act U ∧ U ≠ ⊥ ∧ Module.finrank K U = 1 := by
  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  refine ⟨K ∙ y, fun h x hx => ?_, ?_, finrank_span_singleton hy0⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, htriv h y hyY]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)
  · intro h
    exact hy0 ((Submodule.span_singleton_eq_bot).mp h)

variable [Finite K] [CharP K 2]

theorem finrank_eq_eight_of_isIrrSub (hRoot8 : Omega8LongRootRankStatement)
    (hq : 4 ≤ Nat.card K) (φ : H →* GL (Fin 4 ⊕ Fin 4) K)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (hker : ∀ h, φ h = 1 → act h = 1)
    (hmin : ∀ U : Submodule K X, IsInvSub act U → U ≠ ⊥ → 8 ≤ Module.finrank K U)
    (hdim : Module.finrank K X ≤ 16) {Y : Submodule K X} (hY : IsIrrSub act Y) :
    Module.finrank K Y = 8 := by
  have hnt : ∃ h : H, restrictAct act hY.2.1 h ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have htriv : ∀ h : H, ∀ y ∈ Y, act h y = y := fun h y hy => by
      have := congrArg (fun T : ↥Y ≃ₗ[K] ↥Y => ((T ⟨y, hy⟩ : ↥Y) : X)) (hcon h)
      simpa [coe_restrictAct] using this
    obtain ⟨U, hUinv, hU0, hU1⟩ := exists_invSub_finrank_one_of_trivial hY.1 htriv
    have := hmin U hUinv hU0
    omega
  have hker' : ∀ h : H, φ h = 1 → restrictAct act hY.2.1 h = 1 := fun h hh =>
    LinearEquiv.ext fun y => Subtype.ext (by
      rw [coe_restrictAct, hker h hh]
      rfl)
  exact (hRoot8 K hq H φ hφ ↥Y (restrictAct act hY.2.1) hker'
    (restrictAct_irred act hY.2.1 hY) hnt
    ((Submodule.finrank_le Y).trans hdim)).1

theorem exists_split (hRoot8 : Omega8LongRootRankStatement) (hq : 4 ≤ Nat.card K)
    (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hker : ∀ h, φ h = 1 → act h = 1)
    (hmin : ∀ U : Submodule K X, IsInvSub act U → U ≠ ⊥ → 8 ≤ Module.finrank K U)
    (hdim : Module.finrank K X = 16)
    (hcompl : ∀ U : Submodule K X, IsInvSub act U → ∃ p : X →+ X, (∀ v, p v ∈ U) ∧
      (∀ u ∈ U, p u = u) ∧ ∀ h v, p (act h v) = act h (p v)) :
    ∃ Y₁ Y₂ : Submodule K X, IsCompl Y₁ Y₂ ∧ IsIrrSub act Y₁ ∧ IsIrrSub act Y₂ ∧
      Module.finrank K Y₁ = 8 ∧ Module.finrank K Y₂ = 8 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have htop : (⊤ : Submodule K X) ≠ ⊥ := by
    intro h
    have : Module.finrank K (⊤ : Submodule K X) = 0 := by rw [h, finrank_bot]
    rw [finrank_top, hdim] at this
    exact absurd this (by norm_num)
  obtain ⟨Y₁, -, hY₁⟩ := exists_isIrrSub_le (act := act) (fun h x _ => Submodule.mem_top) htop
  have h8₁ := finrank_eq_eight_of_isIrrSub hRoot8 hq φ hφ hker hmin hdim.le hY₁
  obtain ⟨p, hpW, hp, hpact⟩ := hcompl Y₁ hY₁.2.1
  obtain ⟨Y₂, hY₂inv, hcomp⟩ := exists_invSub_isCompl Y₁ p hpW hp hpact
  have h8₂ : Module.finrank K Y₂ = 8 := by
    have := Submodule.finrank_add_eq_of_isCompl hcomp
    omega
  have hY₂0 : Y₂ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h8₂
    exact absurd h8₂ (by norm_num)
  refine ⟨Y₁, Y₂, hcomp, hY₁, ⟨hY₂0, hY₂inv, fun Y' hY' hY'inv => ?_⟩, h8₁, h8₂⟩
  by_cases h0 : Y' = ⊥
  · exact Or.inl h0
  · exact Or.inr (Submodule.eq_of_le_of_finrank_le hY' (h8₂ ▸ hmin Y' hY'inv h0))

theorem rootProp_of_isIrrSub (hRoot8 : Omega8LongRootRankStatement) (hq : 4 ≤ Nat.card K)
    (φ : H →* GL (Fin 4 ⊕ Fin 4) K) (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hker : ∀ h, φ h = 1 → act h = 1)
    (hmin : ∀ U : Submodule K X, IsInvSub act U → U ≠ ⊥ → 8 ≤ Module.finrank K U)
    (hdim : Module.finrank K X ≤ 16) {Y : Submodule K X} (hY : IsIrrSub act Y)
    {u w : Fin 4 ⊕ Fin 4 → K} (huw : IsTSLine8 u w) {r r' : H} (hr : IsLongRoot8 u w (φ r))
    (hr' : IsLongRoot8 u w (φ r')) (hr1 : φ r ≠ 1) :
    Module.finrank K (Y.map ((act r : X →ₗ[K] X) - LinearMap.id)) = 2 ∧
      ∃ c : K, ∀ y ∈ Y, act r' y - y = c • (act r y - y) := by
  have hnt : ∃ h : H, restrictAct act hY.2.1 h ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have htriv : ∀ h : H, ∀ y ∈ Y, act h y = y := fun h y hy => by
      have := congrArg (fun T : ↥Y ≃ₗ[K] ↥Y => ((T ⟨y, hy⟩ : ↥Y) : X)) (hcon h)
      simpa [coe_restrictAct] using this
    obtain ⟨U, hUinv, hU0, hU1⟩ := exists_invSub_finrank_one_of_trivial hY.1 htriv
    have := hmin U hUinv hU0
    omega
  have hker' : ∀ h : H, φ h = 1 → restrictAct act hY.2.1 h = 1 := fun h hh =>
    LinearEquiv.ext fun y => Subtype.ext (by
      rw [coe_restrictAct, hker h hh]
      rfl)
  obtain ⟨-, hrt⟩ := hRoot8 K hq H φ hφ ↥Y (restrictAct act hY.2.1) hker'
    (restrictAct_irred act hY.2.1 hY) hnt ((Submodule.finrank_le Y).trans hdim)
  obtain ⟨h2, c, hc⟩ := hrt u w huw.1 huw.2.1 huw.2.2.1 huw.2.2.2 r r' hr.1 hr.2 hr'.1 hr'.2 hr1
  refine ⟨?_, c, fun y hy => ?_⟩
  · rw [finrank_map_sub_eq act hY.2.1 r]
    exact h2
  · have := congrArg Subtype.val (hc ⟨y, hy⟩)
    simpa [coe_restrictAct] using this

end Split

end CFSG.RankThree.GF2n.Stroth80.S715L
