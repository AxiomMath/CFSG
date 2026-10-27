module

public import CFSG.RankThree.GF2n.Parrott.SpinTFacts
public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian
public import CFSG.RankThree.GF2n.Parrott.SpinStabW0

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinRigid
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)

private theorem zmod2_polar_aux : ∀ e a b c d : ZMod 2,
    e * (a + c) * (b + d) + e * a * b + e * c * d = e * (a * d + c * b) := by
  decide

private theorem polar_eq_sum (v w : V) :
    b v w = ∑ i : Fin 8, ∑ j : Fin 8,
      if j ≤ i then QMAT i j * (v i * w j + w i * v j) else 0 := by
  unfold b q
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact zmod2_polar_aux _ _ _ _ _
  · simp

private theorem polar_add_left (x y z : V) : b (x + y) z = b x z + b y z := by
  rw [polar_eq_sum, polar_eq_sum, polar_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp only [Pi.add_apply]
    ring
  · simp

private theorem polar_comm (x y : V) : b x y = b y x := by
  unfold b
  rw [add_comm y x]
  ring

private theorem polar_add_right (x y z : V) : b x (y + z) = b x y + b x z := by
  rw [polar_comm, polar_add_left, polar_comm y x, polar_comm z x]

private theorem v_add_self (x : V) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

private theorem polar_zero_left (y : V) : b 0 y = 0 := by
  unfold b
  have h0 : q (0 : V) = 0 := by
    unfold q
    simp
  rw [zero_add, h0, add_zero]
  exact CharTwo.add_self_eq_zero _

private theorem polar_zero_right (x : V) : b x 0 = 0 := by
  rw [polar_comm]
  exact polar_zero_left x

private noncomputable def spinBilin : LinearMap.BilinForm (ZMod 2) V :=
  LinearMap.mk₂ (ZMod 2) b polar_add_left
    (fun c x y => by
      rcases zmod2_cases c with rfl | rfl
      · rw [zero_smul, zero_smul, polar_zero_left]
      · rw [one_smul, one_smul])
    polar_add_right
    (fun c x y => by
      rcases zmod2_cases c with rfl | rfl
      · rw [zero_smul, zero_smul, polar_zero_right]
      · rw [one_smul, one_smul])

private theorem polar_radical_check : ∀ m < 256, (∀ i < 8, bq m (2 ^ i) = 0) → m = 0 := by
  decide +kernel

private theorem eq_zero_of_polar_eq_zero {x : V} (h : ∀ y, b x y = 0) : x = 0 := by
  have h1 : bitmask x = 0 := polar_radical_check _ (bitmask_lt x) fun i hi => by
    have h2 := h (vecOfNat (2 ^ i))
    have h3 : 2 ^ i < 256 := by
      calc 2 ^ i < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hi
        _ = 256 := by norm_num
    rwa [b_eq_zero_iff, bitmask_vecOfNat _ h3] at h2
  exact bitmask_injective (h1.trans bitmask_zero.symm)

private theorem spinBilin_nondegenerate : spinBilin.Nondegenerate :=
  ⟨fun x hx => eq_zero_of_polar_eq_zero hx,
    fun y hy => eq_zero_of_polar_eq_zero fun z => by rw [polar_comm]; exact hy z⟩

private theorem gen_add_self {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (x : W) :
    x + x = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  calc x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by rw [one_smul]
    _ = ((1 : ZMod 2) + 1) • x := (add_smul 1 1 x).symm
    _ = 0 := by rw [h, zero_smul]

private theorem ncard_mul_self_le_of_isotropic {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.Nondegenerate) (S₀ : Set W)
    (hadd : ∀ x ∈ S₀, ∀ y ∈ S₀, x + y ∈ S₀) (hiso : ∀ x ∈ S₀, ∀ y ∈ S₀, B x y = 0) :
    S₀.ncard * S₀.ncard ≤ Nat.card W := by
  have : FiniteDimensional (ZMod 2) W := inferInstance
  rcases S₀.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have h0 : (0 : W) ∈ S₀ := by
    have h := hadd x₀ hx₀ x₀ hx₀
    rwa [gen_add_self] at h
  let U : Submodule (ZMod 2) W :=
    { carrier := S₀
      add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := h0
      smul_mem' := fun c x hx => by
        rcases zmod2_cases c with rfl | rfl
        · simpa using h0
        · simpa using hx }
  have hiso' : U ≤ B.orthogonal U := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hiso n hn w hw
  have hfin := LinearMap.BilinForm.finrank_orthogonal hB U
  have hle := (Submodule.finrank_mono hiso').trans hfin.le
  have hcU : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [← Nat.card_coe_set_eq]
  calc Nat.card S₀ * Nat.card S₀ = Nat.card U * Nat.card U := rfl
    _ = 2 ^ (2 * Module.finrank (ZMod 2) U) := by rw [hcU, ← pow_add]; ring_nf
    _ ≤ 2 ^ Module.finrank (ZMod 2) W := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = Nat.card W := hcW.symm

private theorem exists_represents_of_nondegenerate {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.Nondegenerate)
    (T : AddSubgroup W) (ℓ : W → ZMod 2) (hadd : ∀ x ∈ T, ∀ y ∈ T, ℓ (x + y) = ℓ x + ℓ y) :
    ∃ c : W, ∀ u ∈ T, ℓ u = B c u := by
  have : FiniteDimensional (ZMod 2) W := inferInstance
  let _ : @Module (ZMod 2) (ZMod 2) _ (inferInstance : AddCommGroup (ZMod 2)).toAddCommMonoid :=
    Semiring.toModule
  let U : Submodule (ZMod 2) W := AddSubgroup.toZModSubmodule 2 T
  have h0 : ℓ 0 = 0 := by
    have h := hadd 0 (zero_mem _) 0 (zero_mem _)
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  let f : U →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => ℓ x.1
      map_add' := fun x y => hadd x.1 x.2 y.1 y.2
      map_smul' := fun c x => by
        rcases zmod2_cases c with rfl | rfl
        · simp [h0]
        · simp }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨(B.toDual hB).symm g, fun u hu => ?_⟩
  have h1 : B ((B.toDual hB).symm g) u = g u :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) g u
  have h2 : g u = ℓ u := LinearMap.congr_fun hg ⟨u, hu⟩
  exact (h1.trans h2).symm

private theorem fixesS_qTab_zero : ∀ m < 256, fixesS m = true → qTab.getD m 0 = 0 := by
  decide +kernel

private def wMasks : List ℕ :=
  [0, 4, 26, 30, 64, 68, 90, 94, 128, 132, 154, 158, 192, 196, 218, 222]

private theorem fixesS_iff_mem_wMasks : ∀ m < 256, fixesS m = true ↔ m ∈ wMasks := by
  decide +kernel

private theorem lt_of_mem_wMasks : ∀ n ∈ wMasks, n < 256 := by
  decide +kernel

private theorem fixesS_of_perp_check : ∀ m < 256,
    (∀ n ∈ wMasks, bq m n = 0) → fixesS m = true := by
  decide +kernel

private theorem exists_alpha_preimage : ∀ m < 256, fixesS m = true →
    ∃ x < 256, bapply (evalB b3 (toW lAl)) x ^^^ x = m := by
  decide +kernel

private theorem exists_ut_preimage : ∀ m < 256, fixesS m = true →
    ∃ x < 256, bapply (bmul (evalB b3 (toW lU)) (evalB b3 (toW lT))) x ^^^ x = m := by
  decide +kernel

private theorem card_V : Nat.card V = 256 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem ncard_le_sixteen_of_totally_singular (S₀ : Set V) (hadd : ∀ x ∈ S₀, ∀ y ∈ S₀, x + y ∈ S₀)
    (hq : ∀ x ∈ S₀, q x = 0) : S₀.ncard ≤ 16 := by
  have hiso : ∀ x ∈ S₀, ∀ y ∈ S₀, b x y = 0 := by
    intro x hx y hy
    unfold b
    rw [hq _ (hadd x hx y hy), hq x hx, hq y hy]
    simp
  have h := @ncard_mul_self_le_of_isotropic V _ (Pi.Function.module (Fin 8) (ZMod 2) (ZMod 2)) _
    spinBilin spinBilin_nondegenerate S₀ hadd hiso
  rw [card_V] at h
  by_contra hlt
  have hlt' : 17 ≤ S₀.ncard := by omega
  nlinarith

section Certified

@[expose] def spinFixS : AddSubgroup V where
  carrier := {v | ∀ s ∈ sQA45, SpinFixes s v}
  zero_mem' := fun s _ => by
    unfold SpinFixes
    rw [Matrix.mulVec_zero]
  add_mem' := fun {_ _} ha hb s hs => by
    have ha' := ha s hs
    have hb' := hb s hs
    unfold SpinFixes at ha' hb' ⊢
    rw [Matrix.mulVec_add, ha', hb']
  neg_mem' := fun {_} ha s hs => by
    have ha' := ha s hs
    unfold SpinFixes at ha' ⊢
    rw [Matrix.mulVec_neg, ha']

theorem mem_spinFixS_iff (v : V) : v ∈ spinFixS ↔ ∀ s ∈ sQA45, SpinFixes s v := Iff.rfl

theorem card_spinFixS : Nat.card ↥spinFixS = 16 := by
  have h : Nat.card ↥spinFixS = Nat.card {v : V // fixesS (bitmask v) = true} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => fixesS_iff v)
  rw [h, Nat.card_eq_fintype_card]
  decide +kernel

theorem spinFixS_singular : ∀ v ∈ spinFixS, q v = 0 := by
  intro v hv
  rw [q_eq_zero_iff]
  exact fixesS_qTab_zero _ (bitmask_lt v) ((fixesS_iff v).1 hv)

theorem spinFixS_perp : ∀ v : V, (∀ w ∈ spinFixS, b v w = 0) → v ∈ spinFixS := by
  intro v hv
  refine (fixesS_iff v).2 (fixesS_of_perp_check _ (bitmask_lt v) fun n hn => ?_)
  have hn256 := lt_of_mem_wMasks n hn
  have hfn : fixesS n = true := (fixesS_iff_mem_wMasks n hn256).2 hn
  have h := hv (vecOfNat n) ((fixesS_iff _).2 (by rw [bitmask_vecOfNat n hn256]; exact hfn))
  rwa [b_eq_zero_iff, bitmask_vecOfNat n hn256] at h

theorem spinFixS_le_closure_commutators : spinFixS ≤ AddSubgroup.closure
    {x : V | ∃ s ∈ sQA45, ∃ v : V, x = ((rhoA s : GL8) : Mat8) *ᵥ v + v} := by
  intro w hw
  refine AddSubgroup.subset_closure ?_
  obtain ⟨x, hx, hxm⟩ := exists_alpha_preimage _ (bitmask_lt w) ((fixesS_iff w).1 hw)
  refine ⟨a1A * a2A, alA_mem_S, vecOfNat x, ?_⟩
  apply bitmask_injective
  rw [bitmask_add, ← bapply_colsOf, ← spinMat_apply, cols_alA, bitmask_vecOfNat x hx]
  exact hxm.symm

private theorem fixW_add_mem {a : A45} (ha : ∀ w ∈ spinFixS, SpinFixes a w) (v : V) :
    ((rhoA a : GL8) : Mat8) *ᵥ v + v ∈ spinFixS := by
  apply spinFixS_perp
  intro w hw
  have hfix : ((rhoA a : GL8) : Mat8) *ᵥ w = w := ha w hw
  have h1 := spinB_invariant a v w
  rw [hfix] at h1
  rw [polar_add_left, h1]
  exact CharTwo.add_self_eq_zero _

private theorem rhoA_mul_mulVec_of_fix {a a' : A45} (ha : ∀ w ∈ spinFixS, SpinFixes a w)
    (ha' : ∀ w ∈ spinFixS, SpinFixes a' w) (v : V) :
    ((rhoA (a * a') : GL8) : Mat8) *ᵥ v =
      ((rhoA a : GL8) : Mat8) *ᵥ v + (((rhoA a' : GL8) : Mat8) *ᵥ v + v) := by
  have h1 : ((rhoA a' : GL8) : Mat8) *ᵥ v = (((rhoA a' : GL8) : Mat8) *ᵥ v + v) + v := by
    rw [add_assoc, v_add_self, add_zero]
  have h2 : ((rhoA a : GL8) : Mat8) *ᵥ (((rhoA a' : GL8) : Mat8) *ᵥ v + v) =
      ((rhoA a' : GL8) : Mat8) *ᵥ v + v := ha _ (fixW_add_mem ha' v)
  rw [rhoA_mulVec_mul]
  conv_lhs => rw [h1]
  rw [Matrix.mulVec_add, h2, add_comm]

private def fixSubgroupS : Subgroup A45 where
  carrier := {a | ∀ w ∈ spinFixS, SpinFixes a w}
  mul_mem' := fun {a b} ha hb w hw => spinFixes_mul (ha w hw) (hb w hw)
  one_mem' := fun w _ => spinFixes_one w
  inv_mem' := fun {a} ha w hw =>
    mem_spinStab_iff.1 ((spinStab w).inv_mem (mem_spinStab_iff.2 (ha w hw)))

private theorem isElemAbelian_fixSubgroupS : IsElemAbelian 2 fixSubgroupS := by
  have hcomm : ∀ a ∈ fixSubgroupS, ∀ a' ∈ fixSubgroupS, a * a' = a' * a := by
    intro a ha a' ha'
    apply rhoA_injective
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [rhoA_mul_mulVec_of_fix ha ha', rhoA_mul_mulVec_of_fix ha' ha]
    abel
  have hsq : ∀ a ∈ fixSubgroupS, a * a = 1 := by
    intro a ha
    apply rhoA_injective
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [rhoA_mul_mulVec_of_fix ha ha, map_one, Units.val_one, Matrix.one_mulVec]
    rw [← add_assoc, v_add_self, zero_add]
  refine ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hcomm a a.2 b b.2), fun x hx => ?_⟩
  rw [pow_two]
  exact hsq x hx

section CardBound

theorem mem_sQA45_of_fixes_spinFixS : ∀ a : A45, (∀ w ∈ spinFixS, SpinFixes a w) → a ∈ sQA45 := by
  intro a ha
  have hle : sQA45 ≤ fixSubgroupS := fun s hs w hw => (mem_spinFixS_iff w).1 hw s hs
  have hcard : Nat.card ↥fixSubgroupS ≤ Nat.card ↥sQA45 := by
    rw [card_sQA45]
    exact qa45_elemAbelian_card_le_sixteen _ isElemAbelian_fixSubgroupS
  have heq : sQA45 = fixSubgroupS := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact ha

end CardBound

theorem exists_range_rhoA_uA_mul_tA (w : V) (hw : w ∈ spinFixS) :
    ∃ x : V, ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ x + x = w := by
  obtain ⟨x, hx, hxm⟩ := exists_ut_preimage _ (bitmask_lt w) ((fixesS_iff w).1 hw)
  refine ⟨vecOfNat x, ?_⟩
  apply bitmask_injective
  have hcols : colsOf ((rhoA (uA * tA) : GL8) : Mat8) =
      bmul (evalB b3 (toW lU)) (evalB b3 (toW lT)) := by
    rw [← spinMat_apply, map_mul, colsOf_mul, cols_uA, cols_tA]
  rw [bitmask_add, ← bapply_colsOf, hcols, bitmask_vecOfNat x hx]
  exact hxm

theorem exists_vector_represents_spinFixS (ℓ : V → ZMod 2)
    (hadd : ∀ x ∈ spinFixS, ∀ y ∈ spinFixS, ℓ (x + y) = ℓ x + ℓ y) :
    ∃ c : V, ∀ u ∈ spinFixS, ℓ u = b c u :=
  @exists_represents_of_nondegenerate V _ (Pi.Function.module (Fin 8) (ZMod 2) (ZMod 2)) _
    spinBilin spinBilin_nondegenerate spinFixS ℓ hadd

end Certified

end CFSG.RankThree.GF2n.Parrott
