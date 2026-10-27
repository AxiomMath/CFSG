module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringsAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mRankOne

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.Quasithin.SmithCurtis Module

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem longRankOne_of_finrank_le (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [Finite (spinGroup (quadMinus 4 K b c))] (hK : 4 ≤ Nat.card K) {k V : Type*} [Field k]
    [CharP k 2] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hsplit : SplitOver k (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H)
    {σ : Representation k (spinGroup (quadMinus 4 K b c)) V} (hσ : IsSimpleRep σ)
    {y₀ : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y₀ χ μ)
    (i : Fin 3) (hi : i.val < 2)
    (hdim : finrank k (fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us i)) ≤ 2) :
    μ i = 0 ∧
      ((∀ a : Kˣ,
          χ ((minusFrame 4 b c).longTorus (succ_ne_of_lt 4 (k := i) (by omega)) true false a) =
            1) ∨
        ∃ φ : K →+* k, ∀ a : Kˣ,
          χ ((minusFrame 4 b c).longTorus (succ_ne_of_lt 4 (k := i) (by omega)) true false a) =
            φ a) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    finite_group (isFiniteType_cartanB 3)
  have hK' : 4 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hi' : i.val + 1 < 4 - 1 := by omega
  obtain ⟨hyU, hy0, hχ, hμ⟩ := ht
  set D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ with hD
  set S := fixSub σ (D.Us i) with hS
  set hij := succ_ne_of_lt 4 hi' with hhij
  set x : K → spinGroup (quadMinus 4 K b c) :=
    fun d => (minusFrame 4 b c).longRoot hij true false (.ofAdd d) with hx
  set h := (minusFrame 4 b c).longTorus hij true false with hh
  set n₀ := (minusFrame 4 b c).longWeyl hij true false with hn₀
  have hXi : ∀ g, g ∈ D.X i ↔ ∃ d : K, g = x d := by
    intro g
    change g ∈ minusRootGroup 4 hirrQ (Pi.single i 1) ↔ _
    rw [minusRootGroup_single_of_lt 4 hirrQ hi', MonoidHom.mem_range]
    exact ⟨fun ⟨d, hd⟩ => ⟨Multiplicative.toAdd d, hd.symm⟩, fun ⟨d, hd⟩ => ⟨_, hd.symm⟩⟩
  have hn : D.n i = n₀ := minusWeyl_of_lt 4 hirrQ hi'
  have hhH : ∀ a, h a ∈ D.H := fun a => by
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [minusTorus_of_lt 4 hirrQ hi']
    exact ⟨a, rfl⟩
  have hxadd : ∀ d d', x (d + d') = x d * x d' := fun d d' => by
    simp only [hx, ofAdd_add, map_mul]
  have hxh : ∀ (a : Kˣ) (d : K), h a * x d * (h a)⁻¹ = x ((a : K) ^ 2 * d) := by
    intro a d
    have key := (minusFrame 4 b c).toHypFrame.longTorus_conj_longRoot hij true false a hij true
      false d
    have hco : longCoroot i ⟨i.val + 1, hi'⟩ true false i true +
        longCoroot i ⟨i.val + 1, hi'⟩ true false ⟨i.val + 1, hi'⟩ false = 2 := by
      simp [longCoroot, Fin.ext_iff]
    rw [hco, zpow_two, Units.val_mul] at key
    rw [sq]
    exact key
  have hnh : ∀ a : Kˣ, n₀ * h a * n₀⁻¹ = h a⁻¹ := fun a =>
    (minusFrame 4 b c).toHypFrame.longWeyl_mul_longTorus_mul_inv hij true false a
  have hn2 : ∃ a₀ : Kˣ, n₀ * n₀ = h a₀ :=
    ⟨-1, (minusFrame 4 b c).toHypFrame.longWeyl_mul_self hij true false⟩
  have hYconj : ∀ y ∈ D.Y i, ∃ d : K, y = n₀ * x d * n₀⁻¹ := by
    intro y hy
    have hxy := D.n_inv_conjY i hy
    rw [hn] at hxy
    obtain ⟨d, hd⟩ := (hXi _).mp hxy
    exact ⟨d, by rw [← hd]; group⟩
  have hhX : ∀ a : Kˣ, h a ∈ Subgroup.closure (Set.range x ∪
      (fun g => n₀ * g * n₀⁻¹) '' Set.range x) := by
    intro a
    have hmem : h a ∈ D.X i ⊔ D.Y i := by
      change h a ∈ CFSG.LieType.CurtisTits.rankOne (minusRootGroup 4 hirrQ) i
      rw [rankOne_minusRootGroup_of_lt 4 hirrQ hi']
      exact ⟨_, ((minusFrame 4 b c).toHypFrame.longTorus_apply hij true false a).symm⟩
    have hle : D.X i ⊔ D.Y i ≤ Subgroup.closure (Set.range x ∪
        (fun g => n₀ * g * n₀⁻¹) '' Set.range x) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · obtain ⟨d, rfl⟩ := (hXi g).mp hg
        exact Subgroup.subset_closure (Or.inl ⟨d, rfl⟩)
      · obtain ⟨d, rfl⟩ := hYconj g hg
        exact Subgroup.subset_closure (Or.inr ⟨x d, ⟨d, rfl⟩, rfl⟩)
    exact hle hmem
  have hSx : ∀ d, ∀ v ∈ S, σ (x d) v ∈ S := fun d v hv =>
    act_mem_fixSub σ (fun u hu => by
      simpa only [inv_inv] using D.X_normUs i _ (inv_mem ((hXi _).mpr ⟨d, rfl⟩)) u hu) hv
  have hSn : ∀ v ∈ S, σ n₀ v ∈ S := fun v hv =>
    act_mem_fixSub σ (fun u hu => by simpa only [hn] using D.n_normUs' i u hu) hv
  have hstab : ∀ T : Submodule k V, (∀ d, ∀ v ∈ T, σ (x d) v ∈ T) →
      (∀ v ∈ T, σ n₀ v ∈ T) → ∀ m ∈ D.X i ⊔ D.Y i, ∀ v ∈ T, σ m v ∈ T := by
    intro T hTx hTn m hm
    have hTn' : ∀ v ∈ T, σ n₀⁻¹ v ∈ T := fun v hv => mem_of_inv_stable σ T hTn hv
    rw [Subgroup.sup_eq_closure] at hm
    induction hm using Subgroup.closure_induction with
    | mem m hm =>
      rcases hm with hm | hm
      · obtain ⟨d, rfl⟩ := (hXi m).mp hm
        exact hTx d
      · obtain ⟨d, rfl⟩ := hYconj m hm
        intro v hv
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
        exact hTn _ (hTx d _ (hTn' v hv))
    | one =>
      intro v hv
      rw [map_one, Module.End.one_apply]
      exact hv
    | mul m m' _ _ hm hm' =>
      intro v hv
      rw [map_mul, Module.End.mul_apply]
      exact hm _ (hm' v hv)
    | inv m _ hm =>
      intro v hv
      exact mem_of_inv_stable σ T hm hv
  have hyS : y₀ ∈ S := fun u hu => hyU u (D.Us_le i hu)
  obtain ⟨hsum, hchar⟩ := hecke_eq_zero_and_char hK' σ S hdim x hxadd h n₀ hxh hnh hn2 hhX
    hSx hSn (fun T hTS hTx hTn => fixSub_Us_eq_bot_or_eq D hsplit hσ i hTS (hstab T hTx hTn))
    hyS hy0 (fun d => hyU _ (D.X_le i ((hXi _).mpr ⟨d, rfl⟩)))
    (fun a => χ (h a)) (fun a => hχ _ (hhH a))
  refine ⟨?_, hchar⟩
  have : Fintype (D.X i) := Fintype.ofFinite _
  have hT : D.heckeT σ i y₀ = 0 := by
    erw [CurtisDatum.heckeT_apply D σ i y₀]
    have hbij : Function.Bijective (fun d : K => (⟨x d, (hXi _).mpr ⟨d, rfl⟩⟩ : D.X i)) := by
      refine ⟨fun d d' hdd => ?_, fun g => ?_⟩
      · exact Multiplicative.ofAdd.injective
          ((minusFrame 4 b c).toHypFrame.longRoot_injective hij true false
            (congrArg Subtype.val hdd))
      · obtain ⟨d, hd⟩ := (hXi g).mp g.2
        exact ⟨d, Subtype.ext hd.symm⟩
    rw [← hbij.sum_comp, hn]
    exact hsum
  have h1 := hμ i
  rw [hT] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_right hy0


section LongString

open CFSG.QuasithinUnique.Setup.SL2Modules (dElt uElt)
open scoped MatrixGroups

omit [Finite K] [CharP K 2] in
private theorem spinAction_minusVec_of_blockDiag {g : spinGroup (quadMinus 4 K b c)}
    (hg : BlockDiag 4 (mat 4 g)) (l : Fin 3) (r : Bool) :
    spinAction (quadMinus 4 K b c) g (minusVec 4 l r) =
      mat 4 g (minusPos 4 l r) (minusPos 4 l r) • minusVec 4 l r := by
  funext a
  rw [minusVec_eq_single, Pi.smul_apply, ← mat_apply, smul_eq_mul]
  by_cases ha : a = minusPos 4 l r
  · subst ha
    rw [Pi.single_eq_same, mul_one]
  · rw [hg.apply_eq_zero 4 ha (Or.inr (minusPos_ne_inr_inr 4 l r)), Pi.single_eq_of_ne ha,
      mul_zero]

omit [Finite K] [CharP K 2] in
private theorem mat_true_mul_false {g : spinGroup (quadMinus 4 K b c)}
    (hg : BlockDiag 4 (mat 4 g)) (l : Fin 3) :
    mat 4 g (minusPos 4 l true) (minusPos 4 l true) *
      mat 4 g (minusPos 4 l false) (minusPos 4 l false) = 1 := by
  have h := polar_spinAction (quadMinus 4 K b c) g (minusVec 4 l true) (minusVec 4 l false)
  rw [spinAction_minusVec_of_blockDiag hg, spinAction_minusVec_of_blockDiag hg,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, polar_minusVec_minusVec] at h
  simpa using h

omit [Finite K] [CharP K 2] in
private theorem conj_longRoot_of_blockDiag {g : spinGroup (quadMinus 4 K b c)}
    (hg : BlockDiag 4 (mat 4 g)) {l m : Fin 3} (hlm : l ≠ m) (s t : Bool) (x : K) :
    g * (minusFrame 4 b c).longRoot hlm s t (.ofAdd x) * g⁻¹ =
      (minusFrame 4 b c).longRoot hlm s t (.ofAdd (mat 4 g (minusPos 4 l s) (minusPos 4 l s) *
        mat 4 g (minusPos 4 m t) (minusPos 4 m t) * x)) :=
  (minusFrame 4 b c).toHypFrame.conj_longRoot g hlm s t hlm s t
    (by simpa only [minusFrame_vec] using spinAction_minusVec_of_blockDiag hg l s)
    (by simpa only [minusFrame_vec] using spinAction_minusVec_of_blockDiag hg m t) x

private theorem blockDiag_of_mem_H (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {h : spinGroup (quadMinus 4 K b c)}
    (hh : h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H) : BlockDiag 4 (mat 4 h) := by
  change h ∈ ⨆ j, minusTorus 4 hirrQ j at hh
  exact Subgroup.iSup_induction (minusTorus 4 hirrQ) (C := fun g => BlockDiag 4 (mat 4 g)) hh
    (fun j x hx => blockDiag_mat_of_mem_minusTorus 4 hirrQ j hx)
    (by rw [mat_one]; exact blockDiag_one 4)
    (fun x y hx hy => by rw [mat_mul]; exact blockDiag_mul 4 hx hy)

omit [Finite K] [CharP K 2] in
private theorem dElt_mul_upperSL2_mul_inv (z : Kˣ) (t : K) :
    dElt z * upperSL2 t * (dElt z)⁻¹ = upperSL2 ((z : K) ^ 2 * t) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [dElt, upperSL2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

omit [Finite K] [CharP K 2] in
private theorem dElt_mul_lowerSL2_mul_inv (z : Kˣ) (t : K) :
    dElt z * lowerSL2 t * (dElt z)⁻¹ = lowerSL2 (((z⁻¹ : Kˣ) : K) ^ 2 * t) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [dElt, lowerSL2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

theorem exists_longString_weights (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [Finite (spinGroup (quadMinus 4 K b c))] {e : ℕ} (hKe : Nat.card K = 2 ^ e)
    {k V : Type} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V] [Module k V]
    (hsplit : SplitOver k (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H)
    {σ : Representation k (spinGroup (quadMinus 4 K b c)) V} (hσ : IsSimpleRep σ)
    {y₀ : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y₀ χ μ)
    (i : Fin 3) (hi : i.val < 2) :
    ∃ J : Finset ℕ, J ⊆ Finset.range e ∧
      (∀ a : Kˣ,
        χ ((minusFrame 4 b c).longTorus (succ_ne_of_lt 4 (k := i) (by omega)) true false a) =
          algebraMap K k a ^ ∑ j ∈ J, 2 ^ j) ∧
      finrank k (fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us i)) =
        2 ^ J.card ∧
      (J = ∅ → ∀ g ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).X i ⊔
        (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Y i, σ g y₀ = y₀) ∧
      ∀ j ∈ J, ∃ v ∈ fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us i),
        v ≠ 0 ∧ ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
          σ h v = (χ h * (algebraMap K k (mat 4 h (.inl i) (.inl i) /
            mat 4 h (.inl ⟨i.val + 1, by omega⟩) (.inl ⟨i.val + 1, by omega⟩)) ^
              (-(2 ^ j : ℤ)))) • v := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    finite_group (isFiniteType_cartanB 3)
  have hi' : i.val + 1 < 4 - 1 := by omega
  obtain ⟨hyU, hy0, hχ, hμ⟩ := ht
  set D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  set S := fixSub σ (D.Us i)
  set hij := succ_ne_of_lt 4 hi'
  set Λ := (minusFrame 4 b c).longSL2 hij true false
  set σ' : Representation k SL(2, K) V := σ.comp Λ
  have hXi : ∀ g, g ∈ D.X i ↔
      ∃ d : K, g = (minusFrame 4 b c).longRoot hij true false (.ofAdd d) := by
    intro g
    change g ∈ minusRootGroup 4 hirrQ (Pi.single i 1) ↔ _
    rw [minusRootGroup_single_of_lt 4 hirrQ hi', MonoidHom.mem_range]
    exact ⟨fun ⟨d, hd⟩ => ⟨Multiplicative.toAdd d, hd.symm⟩, fun ⟨d, hd⟩ => ⟨_, hd.symm⟩⟩
  have hΛU : ∀ t : K, Λ (upperSL2 t) = (minusFrame 4 b c).longRoot hij true false (.ofAdd t) :=
    fun t => (minusFrame 4 b c).toHypFrame.longSL2_upperSL2 hij true false t
  have hΛL : ∀ t : K,
      Λ (lowerSL2 t) = (minusFrame 4 b c).longRoot hij.symm true false (.ofAdd t) :=
    fun t => (minusFrame 4 b c).toHypFrame.longSL2_lowerSL2 hij true false t
  have hrank : ∀ m, m ∈ D.X i ⊔ D.Y i ↔ ∃ g, Λ g = m := by
    intro m
    change m ∈ CFSG.LieType.CurtisTits.rankOne (minusRootGroup 4 hirrQ) i ↔ _
    rw [rankOne_minusRootGroup_of_lt 4 hirrQ hi', MonoidHom.mem_range]
  have hSst : ∀ g : SL(2, K), ∀ w ∈ S, σ' g w ∈ S := by
    intro g w hw
    refine act_mem_fixSub σ (fun u hu => ?_) hw
    have := conj_mem_of_sup (D.X_normUs i) (fun y hy v hv => curtisDatum_Y_normUs D i hy hv)
      (inv_mem ((hrank (Λ g)).mpr ⟨g, rfl⟩)) hu
    simpa only [inv_inv] using this
  have hfix : ∀ f ∈ S, (∀ t : K, σ' (uElt t) f = f) → ∃ a : k, f = a • y₀ := by
    intro f hf hfu
    refine D.fixU_eq_smul hσ ⟨hyU, hy0, hχ, hμ⟩ ?_
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq i u hu
    rw [map_mul, Module.End.mul_apply, hf v hv]
    obtain ⟨d, rfl⟩ := (hXi x).mp hx
    have h := hfu d
    rwa [show σ' (uElt d) = σ (Λ (upperSL2 d)) from rfl, hΛU] at h
  have hyS : y₀ ∈ S := fun u hu => hyU u (D.Us_le i hu)
  have hvu : ∀ t : K, σ' (uElt t) y₀ = y₀ := fun t => by
    rw [show σ' (uElt t) = σ (Λ (upperSL2 t)) from rfl, hΛU]
    exact hyU _ (D.X_le i ((hXi _).mpr ⟨t, rfl⟩))
  have hhH : ∀ a : Kˣ, Λ (dElt a) ∈ D.H := fun a => by
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [minusTorus_of_lt 4 hirrQ hi']
    exact ⟨a, rfl⟩
  obtain ⟨J, hJlt, hεJ, hdimJ, hJ0, hlow⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.string_data hKe σ' hy0 S hyS hSst hfix
      hvu (fun z => χ (Λ (dElt z))) (fun z => hχ _ (hhH z))
  have horbS : orbitSpan σ' y₀ ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hSst g y₀ hyS)
  have horb : orbitSpan σ' y₀ = S := by
    rcases fixSub_Us_eq_bot_or_eq D hsplit hσ i horbS (fun m hm w hw => by
        obtain ⟨g, rfl⟩ := (hrank m).mp hm
        exact orbitSpan_stable σ' y₀ g hw) with h0 | h1
    · exfalso
      have hmem := mem_orbitSpan_self σ' y₀
      rw [h0, Submodule.mem_bot] at hmem
      exact hy0 hmem
    · exact h1
  refine ⟨J, fun j hj => Finset.mem_range.mpr (hJlt j hj), fun a => hεJ a,
    by rw [← horb]; exact hdimJ, fun hJ g hg => ?_, fun j hj => ?_⟩
  ·
    obtain ⟨g, rfl⟩ := (hrank g).mp hg
    exact hJ0 hJ g
  obtain ⟨v, hvorb, hv0, hvw⟩ := hlow j hj
  refine ⟨v, horb ▸ hvorb, hv0, fun h hh => ?_⟩
  have hbd := blockDiag_of_mem_H hirrQ hh
  set i₁ : Fin 3 := ⟨i.val + 1, by omega⟩
  have h0 := mat_true_mul_false hbd i
  have h1 := mat_true_mul_false hbd i₁
  have ht0 : mat 4 h (minusPos 4 i true) (minusPos 4 i true) ≠ 0 := left_ne_zero_of_mul_eq_one h0
  have ht1 : mat 4 h (minusPos 4 i₁ true) (minusPos 4 i₁ true) ≠ 0 :=
    left_ne_zero_of_mul_eq_one h1
  obtain ⟨z, hz⟩ := exists_units_sq_eq (div_ne_zero ht0 ht1)
  have hconjU : ∀ t : K, h * Λ (upperSL2 t) * h⁻¹ = Λ (dElt z * upperSL2 t * (dElt z)⁻¹) := by
    intro t
    rw [hΛU, conj_longRoot_of_blockDiag hbd hij true false t, dElt_mul_upperSL2_mul_inv, hΛU, hz]
    congr 2
    have hs1 : mat 4 h (minusPos 4 i₁ false) (minusPos 4 i₁ false) =
        (mat 4 h (minusPos 4 i₁ true) (minusPos 4 i₁ true))⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    rw [hs1, div_eq_mul_inv]
  have hconjL : ∀ t : K, h * Λ (lowerSL2 t) * h⁻¹ = Λ (dElt z * lowerSL2 t * (dElt z)⁻¹) := by
    intro t
    rw [hΛL, conj_longRoot_of_blockDiag hbd hij.symm true false t, dElt_mul_lowerSL2_mul_inv,
      hΛL, Units.val_inv_eq_inv_val, inv_pow, hz]
    congr 2
    have hs0 : mat 4 h (minusPos 4 i false) (minusPos 4 i false) =
        (mat 4 h (minusPos 4 i true) (minusPos 4 i true))⁻¹ :=
      eq_inv_of_mul_eq_one_right h0
    rw [hs0, inv_div, div_eq_mul_inv]
  have hconj : ∀ g : SL(2, K), h * Λ g * h⁻¹ = Λ (dElt z * g * (dElt z)⁻¹) := by
    intro g
    let f₁ : SL(2, K) →* spinGroup (quadMinus 4 K b c) := (MulAut.conj h).toMonoidHom.comp Λ
    let f₂ : SL(2, K) →* spinGroup (quadMinus 4 K b c) :=
      Λ.comp (MulAut.conj (dElt z)).toMonoidHom
    have hU' : ∀ t, f₁ (upperSL2 t) = f₂ (upperSL2 t) := hconjU
    have hL' : ∀ t, f₁ (lowerSL2 t) = f₂ (lowerSL2 t) := hconjL
    have key : f₁ g = f₂ g := by
      obtain ⟨a₁, a₂, a₃, a₄, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 g
      simp only [map_mul, hU', hL']
    exact key
  have hdinv : (dElt z)⁻¹ = dElt z⁻¹ := by
    rw [show dElt z = diagSL2 z from rfl, ← map_inv]
    rfl
  have hact : ∀ w ∈ orbitSpan σ' y₀,
      σ h w = (χ h * χ (Λ (dElt z⁻¹))) • σ' (dElt z) w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, rfl⟩ := hw
      have e1 : h * Λ g = Λ (dElt z * g * (dElt z)⁻¹) * h := by
        rw [← hconj g]
        group
      change σ h (σ (Λ g) y₀) = _ • σ (Λ (dElt z)) (σ (Λ g) y₀)
      rw [← Module.End.mul_apply, ← map_mul, e1, hdinv]
      simp only [map_mul, Module.End.mul_apply]
      rw [hχ h hh, map_smul, hχ _ (hhH z⁻¹)]
      simp only [map_smul, smul_smul]
    | zero => rw [map_zero, map_zero, smul_zero]
    | add a a' _ _ ha ha' => rw [map_add, ha, ha', map_add, smul_add]
    | smul r a _ ha => rw [map_smul, ha, map_smul, smul_comm]
  rw [hact v hvorb, hvw z, smul_smul, hεJ z⁻¹]
  congr 1
  have hA : algebraMap K k (z : K) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap K k).injective]
    exact z.ne_zero
  rw [show mat 4 h (.inl i) (.inl i) / mat 4 h (.inl ⟨i.val + 1, by omega⟩)
      (.inl ⟨i.val + 1, by omega⟩) = (z : K) ^ 2 from hz.symm, map_pow, Units.val_inv_eq_inv_val,
    map_inv₀, inv_pow, mul_assoc]
  congr 1
  rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hA, ← zpow_natCast (algebraMap K k (z : K)) 2,
    ← zpow_mul]
  congr 1
  push_cast
  ring

end LongString

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mRankOne
