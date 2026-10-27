module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import CFSG.RankThree.Classical.SiegelRadical

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {n : ℕ}

section PairRadical

@[expose] def IsPairRadical (W L : Submodule K (Fin n → K)) (g : Matrix (Fin n) (Fin n) K) :
    Prop :=
  (∀ w ∈ W, g *ᵥ w = w) ∧ (∀ v ∈ L, g *ᵥ v - v ∈ W) ∧ ∀ v, g *ᵥ v - v ∈ L

theorem isPairRadical_one (W L : Submodule K (Fin n → K)) : IsPairRadical W L 1 :=
  ⟨fun w _ => one_mulVec w, fun v _ => by rw [one_mulVec, sub_self]; exact zero_mem _,
    fun v => by rw [one_mulVec, sub_self]; exact zero_mem _⟩

theorem IsPairRadical.mul {W L : Submodule K (Fin n → K)} {g g' : Matrix (Fin n) (Fin n) K}
    (hg : IsPairRadical W L g) (hg' : IsPairRadical W L g') : IsPairRadical W L (g * g') := by
  obtain ⟨h1, h2, h3⟩ := hg
  obtain ⟨h1', h2', h3'⟩ := hg'
  refine ⟨fun w hw => by rw [← mulVec_mulVec, h1' w hw, h1 w hw], fun v hv => ?_, fun v => ?_⟩
  · have hv' : g' *ᵥ v ∈ L := by
      have := add_mem (h3' v) hv
      rwa [sub_add_cancel] at this
    have := add_mem (h2 _ hv') (h2' v hv)
    rwa [sub_add_sub_cancel, mulVec_mulVec] at this
  · have := add_mem (h3 (g' *ᵥ v)) (h3' v)
    rwa [sub_add_sub_cancel, mulVec_mulVec] at this

theorem IsPairRadical.of_mul_eq_one {W L : Submodule K (Fin n → K)}
    {g g' : Matrix (Fin n) (Fin n) K} (hg : IsPairRadical W L g) (hgg : g * g' = 1)
    (hgg' : g' * g = 1) : IsPairRadical W L g' := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hinv : ∀ v, g *ᵥ (g' *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hgg, one_mulVec]
  refine ⟨fun w hw => ?_, fun v hv => ?_, fun v => ?_⟩
  · conv_lhs => rw [← h1 w hw]
    rw [mulVec_mulVec, hgg', one_mulVec]
  · have hu : g' *ᵥ v ∈ L := by
      have := sub_mem hv (h3 (g' *ᵥ v))
      rwa [hinv, sub_sub_cancel] at this
    have := neg_mem (h2 _ hu)
    rwa [hinv, neg_sub] at this
  · have := neg_mem (h3 (g' *ᵥ v))
    rwa [hinv, neg_sub] at this

theorem IsPairRadical.sub_one_pow_three {W L : Submodule K (Fin n → K)}
    {g : Matrix (Fin n) (Fin n) K} (hg : IsPairRadical W L g) : (g - 1) ^ 3 = 0 := by
  obtain ⟨h1, h2, h3⟩ := hg
  exact sub_one_pow_three_eq_zero fun v => by rw [h1 _ (h2 _ (h3 v)), sub_self]

variable (p f : ℕ)

@[expose] def pairRadical (W L : Submodule K (Fin n → K)) : Subgroup (unitarySU p f K n) where
  carrier := {g | IsPairRadical W L ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  one_mem' := isPairRadical_one W L
  mul_mem' hg hg' := IsPairRadical.mul hg hg'
  inv_mem' {g} hg := IsPairRadical.of_mul_eq_one hg (g : GL (Fin n) K).val_inv
    (g : GL (Fin n) K).inv_val

variable {p f}

theorem mem_pairRadical {W L : Submodule K (Fin n → K)} {g : unitarySU p f K n} :
    g ∈ pairRadical p f W L ↔
      IsPairRadical W L ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  Iff.rfl

theorem pow_four_eq_one_of_mem_pairRadical [CharP K 2] {W L : Submodule K (Fin n → K)}
    {g : unitarySU p f K n} (hg : g ∈ pairRadical p f W L) : g ^ 4 = 1 :=
  Subtype.ext (Units.ext (by
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
    exact pow_four_eq_one_of_sub_one_pow_three (IsPairRadical.sub_one_pow_three hg)))

variable (p f) in
theorem isPGroup_pairRadical [CharP K 2] (W L : Submodule K (Fin n → K)) :
    IsPGroup 2 (pairRadical p f W L) := fun g =>
  ⟨2, Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact pow_four_eq_one_of_mem_pairRadical g.2)⟩

theorem mem_centralizer_of_mem_pairRadical {W L : Submodule K (Fin n → K)}
    {s : unitarySU p f K n}
    (hsW : ∀ v, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ W)
    (hsL : ∀ v ∈ L, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v)
    {g : unitarySU p f K n} (hg : g ∈ pairRadical p f W L) :
    g ∈ Subgroup.centralizer {s} := by
  obtain ⟨h1, -, h3⟩ := hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  set S := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hS
  set G := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hG
  have key : G * S = S * G := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec]
    have e1 : G *ᵥ (S *ᵥ v) = G *ᵥ v + (S *ᵥ v - v) := by
      rw [show S *ᵥ v = v + (S *ᵥ v - v) by abel, mulVec_add, h1 _ (hsW v)]
      abel
    have e2 : S *ᵥ (G *ᵥ v) = G *ᵥ v + (S *ᵥ v - v) := by
      have h4 := hsL _ (h3 v)
      have h5 : S *ᵥ (G *ᵥ v) = S *ᵥ v + S *ᵥ (G *ᵥ v - v) := by
        rw [← mulVec_add]
        congr 1
        abel
      rw [h5, h4]
      abel
    rw [e1, e2]
  exact Subtype.ext (Units.ext key)

end PairRadical

section Params

variable {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}

@[expose] noncomputable def radC (β : Fin ε → Fin r → K) (i j : Fin r) : K :=
  ∑ l, h.bar (β l i) * β l j

theorem bar_radC (β : Fin ε → Fin r → K) (i j : Fin r) :
    h.bar (radC h β j i) = radC h β i j := by
  simp only [radC, map_sum, map_mul, h.bar_bar]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

@[expose] noncomputable def radX₀ (θ : K) (β : Fin ε → Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => if i < j then radC h β i j else if i = j then θ * radC h β i i else 0

theorem radCond_radX₀ [CharP K 2] {θ : K} (hθ : θ + h.bar θ = 1) (β : Fin ε → Fin r → K) :
    RadCond h β (radX₀ h θ β) := by
  intro i j
  change radX₀ h θ β i j + h.bar (radX₀ h θ β j i) + radC h β i j = 0
  simp only [radX₀, Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [ite_eq_left hij, ite_eq_right (not_lt.mpr hij.le), ite_eq_right hij.ne', map_zero,
      add_zero]
    exact CharTwo.add_self_eq_zero _
  · rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl, map_mul, bar_radC, ← add_mul, hθ, one_mul]
    exact CharTwo.add_self_eq_zero _
  · rw [ite_eq_right (not_lt.mpr hij.le), ite_eq_right hij.ne', ite_eq_left hij, bar_radC,
      zero_add]
    exact CharTwo.add_self_eq_zero _

theorem radCond_add_skewHerm {β : Fin ε → Fin r → K} {X : Matrix (Fin r) (Fin r) K}
    (hX : RadCond h β X) {H : Matrix (Fin r) (Fin r) K}
    (hH : H ∈ CFSG.RankThree.Classical.skewHermMatrices h r) : RadCond h β (X + H) := by
  intro i j
  have h1 := hX i j
  have h2 := (CFSG.RankThree.Classical.mem_skewHermMatrices_iff h).mp hH i j
  simp only [Matrix.add_apply, map_add]
  linear_combination h1 + h2

theorem exists_add_bar_eq_one : ∃ θ : K, θ + h.bar θ = 1 := by
  obtain ⟨θ, hθ⟩ := h.traceLin_surjective 1
  exact ⟨θ, by simpa [UnitaryFieldData.trace] using congrArg Subtype.val hθ⟩

theorem card_radParams :
    Nat.card ((Fin ε → Fin r → K) × CFSG.RankThree.Classical.skewHermMatrices h r) =
      2 ^ (f * (r * (r + 2 * ε))) := by
  have := h.finite
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, CFSG.RankThree.Classical.card_skewHermMatrices,
    h.card_eq_sq, Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin ε),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

end Params

section Elements

variable {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}
  (w : Module.Basis (HypIndex r ε) K (Fin n → K))
  (hw : ∀ x y, CFSG.LinearGroups.stdHermForm h n (w x) (w y) = hypGram r ε K x y)

@[expose] noncomputable def radMat (β : Fin ε → Fin r → K) (X : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix' (radLin h w β X)

theorem radMat_mulVec (β : Fin ε → Fin r → K) (X : Matrix (Fin r) (Fin r) K) (v : Fin n → K) :
    radMat h w β X *ᵥ v = radLin h w β X v :=
  LinearMap.toMatrix'_mulVec _ v

theorem isPairRadical_radMat (β : Fin ε → Fin r → K) (X : Matrix (Fin r) (Fin r) K) :
    IsPairRadical (aSpanTop K ⇑w) (aSpanTop K ⇑w ⊔ zSpan K ⇑w) (radMat h w β X) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v => ?_⟩
  · rw [radMat_mulVec, radLin_eq_self_of_mem h w β X hv]
  · rw [radMat_mulVec]
    exact radLin_sub_mem_of_mem_sup h w β X hv
  · rw [radMat_mulVec]
    exact radLin_sub_mem_sup h w β X v

include hw in
theorem unipotentGL_radMat_mem [CharP K 2] {β : Fin ε → Fin r → K}
    {X : Matrix (Fin r) (Fin r) K} (hRC : RadCond h β X) :
    unipotentGL (radMat h w β X) (isPairRadical_radMat h w β X).sub_one_pow_three ∈
      unitarySU 2 f K n := by
  refine (mem_unitarySU_iff_isometry h).mpr ⟨?_, fun x y => ?_⟩
  · rw [coe_unipotentGL]
    exact det_eq_one_of_sub_one_pow_three (isPairRadical_radMat h w β X).sub_one_pow_three
  · rw [coe_unipotentGL, radMat_mulVec, radMat_mulVec]
    exact radLin_isometry h w β X hw hRC x y

@[expose] noncomputable def radElt [CharP K 2] {β : Fin ε → Fin r → K}
    {X : Matrix (Fin r) (Fin r) K} (hRC : RadCond h β X) : unitarySU 2 f K n :=
  ⟨_, unipotentGL_radMat_mem h w hw hRC⟩

theorem coe_radElt [CharP K 2] {β : Fin ε → Fin r → K} {X : Matrix (Fin r) (Fin r) K}
    (hRC : RadCond h β X) :
    (((radElt h w hw hRC : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      radMat h w β X :=
  rfl

theorem radElt_mem_pairRadical [CharP K 2] {β : Fin ε → Fin r → K}
    {X : Matrix (Fin r) (Fin r) K} (hRC : RadCond h β X) :
    radElt h w hw hRC ∈ pairRadical 2 f (aSpanTop K ⇑w) (aSpanTop K ⇑w ⊔ zSpan K ⇑w) := by
  rw [mem_pairRadical, coe_radElt]
  exact isPairRadical_radMat h w β X

include hw in
theorem eq_of_radElt_eq [CharP K 2] {β β' : Fin ε → Fin r → K}
    {X X' : Matrix (Fin r) (Fin r) K} (hRC : RadCond h β X) (hRC' : RadCond h β' X')
    (he : radElt h w hw hRC = radElt h w hw hRC') : β = β' ∧ X = X' := by
  have hm := congrArg (fun g : unitarySU 2 f K n =>
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) he
  simp only [coe_radElt, radMat] at hm
  exact eq_of_radLin_eq h w β X hw (LinearMap.toMatrix'.injective hm)

include hw in
theorem card_pairRadical_ge [CharP K 2] :
    2 ^ (f * (r * (r + 2 * ε))) ≤
      Nat.card (pairRadical 2 f (aSpanTop K ⇑w) (aSpanTop K ⇑w ⊔ zSpan K ⇑w)) := by
  have := h.finite
  have : Finite (unitarySU 2 f K n) := inferInstance
  obtain ⟨θ, hθ⟩ := exists_add_bar_eq_one h
  have hRCp : ∀ p : (Fin ε → Fin r → K) × CFSG.RankThree.Classical.skewHermMatrices h r,
      RadCond h p.1 (radX₀ h θ p.1 + p.2) := fun p =>
    radCond_add_skewHerm h (radCond_radX₀ h hθ p.1) p.2.2
  let Φ : (Fin ε → Fin r → K) × CFSG.RankThree.Classical.skewHermMatrices h r →
      pairRadical 2 f (aSpanTop K ⇑w) (aSpanTop K ⇑w ⊔ zSpan K ⇑w) := fun p =>
    ⟨radElt h w hw (hRCp p), radElt_mem_pairRadical h w hw _⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨β, H⟩ ⟨β', H'⟩ he
    have he' := congrArg Subtype.val he
    obtain ⟨rfl, hX⟩ := eq_of_radElt_eq h w hw (hRCp (β, H)) (hRCp (β', H')) he'
    exact Prod.ext rfl (Subtype.ext (add_left_cancel hX))
  rw [← card_radParams h]
  exact Nat.card_le_card_of_injective Φ hΦ

end Elements

end CFSG.SeitzReduction.UnitaryPilot
