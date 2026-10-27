module

public import CFSG.Quasithin.Background.HSU3
public import CFSG.Quasithin.Background.HBang
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

namespace CFSG.Quasithin

namespace H

namespace SU3

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem card_filter_bar_le (hn : 1 ≤ n) [Fintype K] [DecidableEq K] :
    (Finset.univ.filter (fun x : K => bar n x = x)).card ≤ 2 ^ n := by
  by_contra hlt
  push Not at hlt
  have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  have h0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial K) (Finset.univ.filter (fun x : K =>
      bar n x = x)) (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, bar_apply] at hx
        simp [hx]) (by rw [hdeg]; exact hlt)
  rw [h0, Polynomial.natDegree_zero] at hdeg
  omega

theorem exists_bar_ne (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) : ∃ z : K, bar n z ≠ z := by
  classical
  have : Fintype K := Fintype.ofFinite K
  by_contra h
  push Not at h
  have h1 := card_filter_bar_le (K := K) hn
  rw [Finset.filter_true_of_mem (fun x _ => h x), Finset.card_univ, ← Nat.card_eq_fintype_card,
    hK] at h1
  have : 2 ^ n < (2 ^ n) ^ 2 := by
    rw [sq]
    exact lt_mul_self (Nat.one_lt_two_pow (by omega))
  omega

theorem orderOf_bar (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    orderOf (bar n : K ≃+* K) = 2 := by
  apply orderOf_eq_prime
  · ext x
    rw [sq, RingAut.mul_apply, bar_bar hK, RingAut.one_apply]
  · intro h
    obtain ⟨z, hz⟩ := exists_bar_ne hn hK
    apply hz
    rw [h, RingAut.one_apply]

theorem exists_bar_mul_self_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {r : K}
    (hr : bar n r = r) : ∃ t : K, bar n t * t = r := by
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq (bar n) hr
  rw [orderOf_bar hn hK, Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one,
    RingAut.one_apply] at hd
  exact ⟨d, by rw [mul_comm]; exact hd⟩

theorem bar_herm_self (hK : Nat.card K = (2 ^ n) ^ 2) (v : Fin 3 → K) :
    bar n (herm n v v) = herm n v v :=
  (herm_comm hK v v).symm

theorem exists_smul_herm_eq_one (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {v : Fin 3 → K} (hv : herm n v v ≠ 0) : ∃ t : K, herm n (t • v) (t • v) = 1 := by
  have hr : bar n (herm n v v)⁻¹ = (herm n v v)⁻¹ := by rw [map_inv₀, bar_herm_self hK]
  obtain ⟨t, ht⟩ := exists_bar_mul_self_eq hn hK hr
  refine ⟨t, ?_⟩
  rw [herm_smul_left, herm_smul_right, ← mul_assoc, ht, inv_mul_cancel₀ hv]

@[expose] def fixSub (A : Matrix (Fin 3) (Fin 3) K) : Submodule K (Fin 3 → K) :=
  LinearMap.ker (Matrix.mulVecLin A - LinearMap.id)

omit [Finite K] [CharP K 2] in
theorem mem_fixSub {A : Matrix (Fin 3) (Fin 3) K} {v : Fin 3 → K} :
    v ∈ fixSub A ↔ A *ᵥ v = v := by
  simp [fixSub, sub_eq_zero]

theorem exists_anisotropic (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {W : Submodule K (Fin 3 → K)} (hW : Module.finrank K W = 2) :
    ∃ b ∈ W, herm n b b ≠ 0 := by
  by_contra h
  push Not at h
  let β := Module.finBasisOfFinrankEq K W hW
  set u : Fin 3 → K := ((β 0 : W) : Fin 3 → K) with hu
  set u' : Fin 3 → K := ((β 1 : W) : Fin 3 → K) with hu'
  have huW : u ∈ W := (β 0).2
  have hu'W : u' ∈ W := (β 1).2
  have hli : LinearIndependent K ![u, u'] := by
    have := β.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hu0 : u ≠ 0 := hli.ne_zero 0
  have hk : herm n u u' = 0 := by
    by_contra hk
    obtain ⟨z, hz⟩ := exists_bar_ne hn hK
    have h1 := h (u + ((herm n u u')⁻¹ * z) • u') (W.add_mem huW (W.smul_mem _ hu'W))
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h u huW,
      h u' hu'W, mul_zero, add_zero, zero_add] at h1
    rw [herm_comm hK u u'] at h1
    have e1 : (herm n u u')⁻¹ * z * herm n u u' = z := by field_simp
    have e2 : bar n ((herm n u u')⁻¹ * z) * bar n (herm n u u') = bar n z := by
      rw [← map_mul, e1]
    rw [e1, e2, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
    apply hz
    exact h1
  obtain ⟨c, hc⟩ := eq_smul_of_isotropic hK hu0 (h u huW) (h u' hu'W) hk
  have h3 := (LinearIndependent.pair_iff.mp hli) c (-1) (by rw [hc, neg_one_smul, add_neg_cancel])
  exact one_ne_zero (neg_eq_zero.mp h3.2)

omit [Finite K] in
theorem odd_nsmul_eq {p : ℕ} (hp : Odd p) (y : Fin 3 → K) : p • y = y := by
  obtain ⟨m, rfl⟩ := hp
  rw [add_smul, one_smul, mul_comm, mul_smul, two_smul, CharTwo.add_self_eq_zero, smul_zero,
    zero_add]

theorem eq_zero_of_mem_fixSub_of_perp (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A)
    {p : ℕ} (hp : Odd p) (hAp : A ^ p = 1) (hW : Module.finrank K (fixSub A) = 2)
    {v : Fin 3 → K} (hvW : v ∈ fixSub A) (hv : ∀ u ∈ fixSub A, herm n u v = 0) : v = 0 := by
  by_contra hv0
  have hWtop : fixSub A ≠ ⊤ := by
    intro h
    have := Submodule.finrank_eq_rank K (fixSub A)
    rw [h, finrank_top, Module.finrank_fin_fun] at hW
    omega
  obtain ⟨z, hz⟩ : ∃ z, z ∉ fixSub A := by
    by_contra h
    push Not at h
    exact hWtop (eq_top_iff.mpr fun x _ => h x)
  have hsup : fixSub A ⊔ Submodule.span K {z} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixSub A) (Submodule.span K {z})
    have h2 : fixSub A ⊓ Submodule.span K {z} = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxW, hxz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxz
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply hz
        have := (fixSub A).smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have h3 : Module.finrank K (Submodule.span K {z}) = 1 :=
      finrank_span_singleton (fun h => hz (h ▸ (fixSub A).zero_mem))
    rw [h2, finrank_bot, hW, h3, add_zero] at h1
    rw [h1, Module.finrank_fin_fun]
  obtain ⟨y, hy, t, ht, hAz⟩ := Submodule.mem_sup.mp (show A *ᵥ z ∈ fixSub A ⊔ Submodule.span K {z}
    from hsup ▸ Submodule.mem_top)
  obtain ⟨ν, rfl⟩ := Submodule.mem_span_singleton.mp ht
  have hvperp : ∀ u ∈ fixSub A, herm n v u = 0 := fun u hu => by
    rw [herm_comm hK, hv u hu, map_zero]
  have hvz : herm n v z ≠ 0 := by
    intro h0
    apply hv0
    refine eq_zero_of_herm_eq_zero (n := n) fun x => ?_
    have hx : x ∈ fixSub A ⊔ Submodule.span K {z} := hsup ▸ Submodule.mem_top
    obtain ⟨y', hy', t', ht', rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht'
    rw [herm_add_right, herm_smul_right, hvperp y' hy', h0, mul_zero, add_zero]
  have hν : ν = 1 := by
    have h1 : herm n v (A *ᵥ z) = herm n v z := by
      have := herm_mulVec_mulVec hA v z
      rwa [mem_fixSub.mp hvW] at this
    rw [← hAz, herm_add_right, herm_smul_right, hvperp y hy, zero_add] at h1
    have : (ν - 1) * herm n v z = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hvz)
  rw [hν, one_smul] at hAz
  have hiter : ∀ k : ℕ, (A ^ k) *ᵥ z = z + k • y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
        mem_fixSub.mp hy, ← hAz, succ_nsmul]
      abel
  have h1 := hiter p
  rw [hAp, Matrix.one_mulVec, odd_nsmul_eq hp, left_eq_add] at h1
  apply hz
  rw [mem_fixSub, ← hAz, h1, zero_add]

theorem herm_eq_zero_of_mem_span {W : Submodule K (Fin 3 → K)} {ι : Type*} (b : ι → (Fin 3 → K))
    (hb : Submodule.span K (Set.range b) = W) {w : Fin 3 → K} (hw : ∀ i, herm n (b i) w = 0)
    {x : Fin 3 → K} (hx : x ∈ W) : herm n x w = 0 := by
  rw [← hb] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hw i
  | zero =>
    unfold herm conjV
    simp
  | add y z _ _ hy hz => rw [herm_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [herm_smul_left, hy, mul_zero]

theorem exists_unitary_frame (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitaryM n A) {p : ℕ} (hp : Odd p) (hAp : A ^ p = 1)
    (hW : Module.finrank K (fixSub A) = 2) :
    ∃ (b : Fin 3 → (Fin 3 → K)) (ℓ : K),
      (∀ i j, herm n (b i) (b j) = if i = j then 1 else 0) ∧
      A *ᵥ b 0 = b 0 ∧ A *ᵥ b 1 = b 1 ∧ A *ᵥ b 2 = ℓ • b 2 ∧ ℓ ≠ 1 ∧ ℓ ^ p = 1 ∧
      bar n ℓ * ℓ = 1 := by
  set W := fixSub A with hWdef
  let β := Module.finBasisOfFinrankEq K W hW
  have hspan : Submodule.span K (Set.range fun i => (β i : Fin 3 → K)) = W := by
    have h1 := β.span_eq
    have h2 := congrArg (Submodule.map W.subtype) h1
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
    exact h2
  let f : (Fin 3 → K) →ₗ[K] (Fin 2 → K) :=
    { toFun := fun y => fun i => herm n (β i : Fin 3 → K) y
      map_add' := fun y z => by
        ext i
        simp [herm_add_right]
      map_smul' := fun c y => by
        ext i
        simp [herm_smul_right] }
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hr2 : Module.finrank K (LinearMap.range f) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_fin_fun] at this
  rw [Module.finrank_fin_fun] at hrank
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrank
    omega
  obtain ⟨w, hwker, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hwperp : ∀ x ∈ W, herm n x w = 0 := fun x hx =>
    herm_eq_zero_of_mem_span (fun i => (β i : Fin 3 → K)) hspan
      (fun i => congrFun (LinearMap.mem_ker.mp hwker) i) hx
  have hrad : ∀ v ∈ W, (∀ u ∈ W, herm n u v = 0) → v = 0 := fun v hv h =>
    eq_zero_of_mem_fixSub_of_perp hK hA hp hAp hW hv h
  have hwW : w ∉ W := fun h => hw0 (hrad w h hwperp)
  have hsup : W ⊔ Submodule.span K {w} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {w})
    have h2 : W ⊓ Submodule.span K {w} = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxW, hxz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxz
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply hwW
        have := W.smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [h2, finrank_bot, hW, finrank_span_singleton hw0, add_zero] at h1
    rw [h1, Module.finrank_fin_fun]
  have hdecomp : ∀ x : Fin 3 → K, ∃ y ∈ W, ∃ c : K, x = y + c • w := by
    intro x
    obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.mp (show x ∈ W ⊔ Submodule.span K {w} from
      hsup ▸ Submodule.mem_top)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    exact ⟨y, hy, c, rfl⟩
  obtain ⟨y, hyW, ℓ, hAw⟩ := hdecomp (A *ᵥ w)
  have hy0 : y = 0 := by
    refine hrad y hyW fun u hu => ?_
    have h1 : herm n u (A *ᵥ w) = 0 := by
      have := herm_mulVec_mulVec hA u w
      rw [mem_fixSub.mp hu] at this
      rw [this, hwperp u hu]
    have h2 : y = A *ᵥ w - ℓ • w := by rw [hAw]; abel
    rw [h2, herm_sub_right, h1, herm_smul_right, hwperp u hu, mul_zero, sub_zero]
  rw [hy0, zero_add] at hAw
  have hww : herm n w w ≠ 0 := by
    intro h0
    apply hw0
    refine eq_zero_of_herm_eq_zero (n := n) fun x => ?_
    obtain ⟨y', hy', c, rfl⟩ := hdecomp x
    rw [herm_add_right, herm_smul_right, h0, mul_zero, add_zero, herm_comm hK, hwperp y' hy',
      map_zero]
  have hℓ1 : ℓ ≠ 1 := by
    rintro rfl
    apply hwW
    rw [mem_fixSub, hAw, one_smul]
  have hℓp : ℓ ^ p = 1 := by
    have hiter : ∀ k : ℕ, (A ^ k) *ᵥ w = ℓ ^ k • w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hAw, smul_smul, pow_succ]
    have h1 := hiter p
    rw [hAp, Matrix.one_mulVec] at h1
    have : (ℓ ^ p - 1) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw0)
  have hℓbar : bar n ℓ * ℓ = 1 := by
    have h1 := herm_mulVec_mulVec hA w w
    rw [hAw, herm_smul_left, herm_smul_right, ← mul_assoc] at h1
    have : (bar n ℓ * ℓ - 1) * herm n w w = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hww)
  obtain ⟨b, hbW, hbb⟩ := exists_anisotropic hn hK hW
  obtain ⟨t0, ht0⟩ := exists_smul_herm_eq_one hn hK hbb
  set b0 := t0 • b with hb0
  have hb0W : b0 ∈ W := W.smul_mem t0 hbW
  let φ : W →ₗ[K] K :=
    { toFun := fun x => herm n b0 x
      map_add' := fun x y => herm_add_right _ _ _
      map_smul' := fun c x => herm_smul_right _ _ _ }
  have hφsurj : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • ⟨b0, hb0W⟩, by
      change herm n b0 (c • b0) = c
      rw [herm_smul_right, ht0, mul_one]⟩
  have hφker : Module.finrank K (LinearMap.ker φ) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hφsurj, finrank_top, Module.finrank_self, hW] at this
    omega
  have hkerne : LinearMap.ker φ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hφker
    omega
  obtain ⟨c1, hc1ker, hc1ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerne
  set b1 : Fin 3 → K := (c1 : Fin 3 → K) with hb1
  have hb1W : b1 ∈ W := c1.2
  have hb10 : b1 ≠ 0 := fun h => hc1ne (Subtype.ext h)
  have hb0b1 : herm n b0 b1 = 0 := LinearMap.mem_ker.mp hc1ker
  have hcomb : ∀ x ∈ W, ∃ s t : K, x = s • b0 + t • b1 := by
    intro x hx
    have hxk : (⟨x - herm n b0 x • b0, W.sub_mem hx (W.smul_mem _ hb0W)⟩ : W) ∈
        LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      change herm n b0 (x - herm n b0 x • b0) = 0
      rw [herm_sub_right, herm_smul_right, ht0, mul_one, sub_self]
    have hc1ne' : (⟨c1, hc1ker⟩ : LinearMap.ker φ) ≠ 0 := fun h =>
      hc1ne (congrArg Subtype.val h)
    obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (K := K) (V := ↥(LinearMap.ker φ)) _
      hc1ne').mp hφker ⟨_, hxk⟩
    refine ⟨herm n b0 x, t, ?_⟩
    have := congrArg (fun z : LinearMap.ker φ => ((z : W) : Fin 3 → K)) ht
    simp only [SetLike.val_smul] at this
    rw [hb1, this]
    abel
  have hb1b1 : herm n b1 b1 ≠ 0 := by
    intro h0
    apply hb10
    refine hrad b1 hb1W fun u hu => ?_
    obtain ⟨s, t, rfl⟩ := hcomb u hu
    rw [herm_add_left, herm_smul_left s b0 b1, herm_smul_left t b1 b1, h0, hb0b1, mul_zero,
      mul_zero, add_zero]
  obtain ⟨t1, ht1⟩ := exists_smul_herm_eq_one hn hK hb1b1
  obtain ⟨t2, ht2⟩ := exists_smul_herm_eq_one hn hK hww
  refine ⟨![b0, t1 • b1, t2 • w], ℓ, ?_, mem_fixSub.mp hb0W,
    mem_fixSub.mp (W.smul_mem t1 hb1W), ?_, hℓ1, hℓp, hℓbar⟩
  · have h01 : herm n b0 (t1 • b1) = 0 := by rw [herm_smul_right, hb0b1, mul_zero]
    have h02 : herm n b0 (t2 • w) = 0 := by rw [herm_smul_right, hwperp b0 hb0W, mul_zero]
    have h12 : herm n (t1 • b1) (t2 • w) = 0 := by
      rw [herm_smul_right, hwperp _ (W.smul_mem t1 hb1W), mul_zero]
    have h10 : herm n (t1 • b1) b0 = 0 := by rw [herm_comm hK, h01, map_zero]
    have h20 : herm n (t2 • w) b0 = 0 := by rw [herm_comm hK, h02, map_zero]
    have h21 : herm n (t2 • w) (t1 • b1) = 0 := by rw [herm_comm hK, h12, map_zero]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ht0, ht1, ht2, h01, h02, h12, h10, h20, h21]
  · change A *ᵥ (t2 • w) = ℓ • (t2 • w)
    rw [Matrix.mulVec_smul, hAw, smul_comm]

@[expose] def frameMat (b : Fin 3 → (Fin 3 → K)) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => b j i

omit [Finite K] [CharP K 2] in
theorem frameMat_mulVec_single (b : Fin 3 → (Fin 3 → K)) (j : Fin 3) :
    frameMat b *ᵥ Pi.single j 1 = b j := by
  ext i
  simp [frameMat, Matrix.mulVec_single]

theorem isUnitaryM_frameMat {b : Fin 3 → (Fin 3 → K)}
    (hb : ∀ i j, herm n (b i) (b j) = if i = j then 1 else 0) : IsUnitaryM n (frameMat b) := by
  ext i j
  have h := hb i j
  simp only [herm, conjV, dotProduct] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, conjM, Matrix.map_apply, frameMat,
    Matrix.of_apply, Matrix.one_apply]
  rw [h]

omit [Finite K] [CharP K 2] in
theorem mul_frameMat {A : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → (Fin 3 → K)} {ℓ : K}
    (h0 : A *ᵥ b 0 = b 0) (h1 : A *ᵥ b 1 = b 1) (h2 : A *ᵥ b 2 = ℓ • b 2) :
    A * frameMat b = frameMat b * Matrix.diagonal ![1, 1, ℓ] := by
  ext i j
  have hcol : ∀ j : Fin 3, (A * frameMat b) i j = (A *ᵥ b j) i := fun j => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, frameMat]
  rw [hcol, Matrix.mul_diagonal]
  fin_cases j
  · simp [h0, frameMat]
  · simp [h1, frameMat]
  · simp [h2, frameMat, mul_comm]

@[expose] noncomputable def diagPow (ℓ : K) (a b c : ℕ) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![ℓ ^ a, ℓ ^ b, ℓ ^ c]

omit [Finite K] [CharP K 2] in
theorem diagPow_mul (ℓ : K) (a b c a' b' c' : ℕ) :
    diagPow ℓ a b c * diagPow ℓ a' b' c' = diagPow ℓ (a + a') (b + b') (c + c') := by
  rw [diagPow, diagPow, diagPow, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [pow_add]

omit [Finite K] [CharP K 2] in
theorem diagPow_zero (ℓ : K) : diagPow ℓ 0 0 0 = 1 := by
  rw [diagPow, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

omit [Finite K] [CharP K 2] in
theorem diagPow_mod {ℓ : K} {p : ℕ} (hℓp : ℓ ^ p = 1) (a b c : ℕ) :
    diagPow ℓ (a + p) b c = diagPow ℓ a b c ∧ diagPow ℓ a (b + p) c = diagPow ℓ a b c ∧
      diagPow ℓ a b (c + p) = diagPow ℓ a b c := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [diagPow, diagPow] <;> congr 1 <;> ext i <;>
    fin_cases i <;> simp [pow_add, hℓp]

omit [Finite K] [CharP K 2] in
theorem det_diagPow (ℓ : K) (a b c : ℕ) : (diagPow ℓ a b c).det = ℓ ^ (a + b + c) := by
  rw [diagPow, Matrix.det_diagonal, Fin.prod_univ_three]
  simp [pow_add]

theorem isUnitaryM_diagPow {ℓ : K} (hℓ : bar n ℓ * ℓ = 1) (a b c : ℕ) :
    IsUnitaryM n (diagPow ℓ a b c) := by
  have hk : ∀ k : ℕ, bar n ℓ ^ k * ℓ ^ k = 1 := fun k => by
    rw [← mul_pow, hℓ, one_pow]
  have hmap : conjM n (diagPow ℓ a b c) =
      Matrix.diagonal ![bar n (ℓ ^ a), bar n (ℓ ^ b), bar n (ℓ ^ c)] := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [conjM, diagPow]
    · simp [conjM, diagPow, Matrix.diagonal_apply_ne _ hij]
  rw [IsUnitaryM, hmap, Matrix.diagonal_transpose, diagPow, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [hk]

section Bang

variable {P : Matrix (Fin 3) (Fin 3) K} {ℓ : K} {p : ℕ}

@[expose] noncomputable def conjDiag (n : ℕ) (P : Matrix (Fin 3) (Fin 3) K) (ℓ : K) (a b c : ℕ) :
    Matrix (Fin 3) (Fin 3) K :=
  P * diagPow ℓ a b c * (conjM n P)ᵀ

theorem conjDiag_mul (hP : IsUnitaryM n P) (a b c a' b' c' : ℕ) :
    conjDiag n P ℓ a b c * conjDiag n P ℓ a' b' c' =
      conjDiag n P ℓ (a + a') (b + b') (c + c') := by
  unfold conjDiag
  rw [show P * diagPow ℓ a b c * (conjM n P)ᵀ * (P * diagPow ℓ a' b' c' * (conjM n P)ᵀ) =
      P * diagPow ℓ a b c * ((conjM n P)ᵀ * P) * diagPow ℓ a' b' c' * (conjM n P)ᵀ by
    simp only [Matrix.mul_assoc], hP, Matrix.mul_one, Matrix.mul_assoc P, diagPow_mul]

theorem conjDiag_zero (hP : IsUnitaryM n P) : conjDiag n P ℓ 0 0 0 = 1 := by
  unfold conjDiag
  rw [diagPow_zero, Matrix.mul_one, hP.mul_conj]

theorem det_conjDiag (hP : IsUnitaryM n P) (a b c : ℕ) :
    (conjDiag n P ℓ a b c).det = ℓ ^ (a + b + c) := by
  unfold conjDiag
  rw [Matrix.det_mul, Matrix.det_mul, det_diagPow, mul_comm (P.det), mul_assoc, ← Matrix.det_mul,
    hP.mul_conj, Matrix.det_one, mul_one]

theorem isUnitaryM_conjDiag (hK : Nat.card K = (2 ^ n) ^ 2) (hP : IsUnitaryM n P)
    (hℓ : bar n ℓ * ℓ = 1) (a b c : ℕ) : IsUnitaryM n (conjDiag n P ℓ a b c) :=
  (hP.mul (isUnitaryM_diagPow hℓ a b c)).mul (hP.conj_transpose hK)

end Bang


section BetaMain

variable {P : Matrix (Fin 3) (Fin 3) K} {ℓ : K} {p : ℕ}

theorem conjDiag_pow (hP : IsUnitaryM n P) (a b c k : ℕ) :
    conjDiag n P ℓ a b c ^ k = conjDiag n P ℓ (k * a) (k * b) (k * c) := by
  induction k with
  | zero => simpa using (conjDiag_zero (ℓ := ℓ) hP).symm
  | succ k ih =>
    rw [pow_succ, ih, conjDiag_mul hP]
    congr 1 <;> ring

omit [Finite K] [CharP K 2] in
theorem diagPow_mul_p (hℓp : ℓ ^ p = 1) (a b c : ℕ) :
    diagPow ℓ (p * a) (p * b) (p * c) = 1 := by
  rw [diagPow, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [pow_mul, hℓp]

theorem conjDiag_add_p (hℓp : ℓ ^ p = 1) (a b c k : ℕ) :
    conjDiag n P ℓ a b (c + p * k) = conjDiag n P ℓ a b c := by
  unfold conjDiag
  congr 2
  rw [diagPow, diagPow]
  congr 1
  ext i
  fin_cases i <;> simp [pow_add, pow_mul, hℓp]

omit [Finite K] [CharP K 2] in
theorem swapMat_mul_diagPow_mul_swapMat (a b c : ℕ) :
    swapMat * diagPow ℓ a b c * swapMat = diagPow ℓ b a c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, diagPow, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.vecMul, dotProduct]

theorem conjDiag_injective (hP : IsUnitaryM n P) {a b c a' b' c' : ℕ}
    (h : conjDiag n P ℓ a b c = conjDiag n P ℓ a' b' c') :
    diagPow ℓ a b c = diagPow ℓ a' b' c' := by
  have h1 := congrArg (fun M => (conjM n P)ᵀ * M * P) h
  simp only [conjDiag] at h1
  have hPP : P * (conjM n P)ᵀ = 1 := hP.mul_conj
  rwa [show ∀ D : Matrix (Fin 3) (Fin 3) K, (conjM n P)ᵀ * (P * D * (conjM n P)ᵀ) * P = D from
    fun D => by rw [show (conjM n P)ᵀ * (P * D * (conjM n P)ᵀ) * P =
      ((conjM n P)ᵀ * P) * D * ((conjM n P)ᵀ * P) by simp only [Matrix.mul_assoc], hP,
      Matrix.one_mul, Matrix.mul_one], show ∀ D : Matrix (Fin 3) (Fin 3) K,
    (conjM n P)ᵀ * (P * D * (conjM n P)ᵀ) * P = D from fun D => by
      rw [show (conjM n P)ᵀ * (P * D * (conjM n P)ᵀ) * P =
        ((conjM n P)ᵀ * P) * D * ((conjM n P)ᵀ * P) by simp only [Matrix.mul_assoc], hP,
        Matrix.one_mul, Matrix.mul_one]] at h1

end BetaMain


theorem mem_zpowers_of_isCyclic {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    {C : Subgroup Q} (hC : IsCyclic C) (hexp : ∀ g ∈ C, g ^ p = 1) {x z : Q} (hx : x ∈ C)
    (hx1 : x ≠ 1) (hz : z ∈ C) : z ∈ Subgroup.zpowers x := by
  obtain ⟨g, hg⟩ := hC.exists_generator
  have hcard : Nat.card C = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hgp : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hexp g g.2))
  have hxo : orderOf (⟨x, hx⟩ : C) = p := by
    apply orderOf_eq_prime (Subtype.ext (by simpa using hexp x hx))
    intro h
    exact hx1 (congrArg Subtype.val h)
  have hle : Subgroup.zpowers (⟨x, hx⟩ : C) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hxo, hcard]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hgp with h | h
    · exfalso
      have : (⟨x, hx⟩ : C) ∈ Subgroup.zpowers g := hg _
      rw [orderOf_eq_one_iff.mp h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
      exact hx1 (congrArg Subtype.val this)
    · exact h.symm
  have : (⟨z, hz⟩ : C) ∈ Subgroup.zpowers (⟨x, hx⟩ : C) := hle ▸ Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp this
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem le_rkIdx_fixV_of_odd (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hLX : natImage (StatedSU 3 (2 ^ n) K) ≤ X)
    (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) (hB : HypBang X) {p : ℕ} [hpf : Fact p.Prime]
    (hp2 : p ≠ 2) {x : MulAut (StdMod (Fin 3) K)} (hxX : x ∈ X) (hxo : orderOf x = p) :
    4 * n ≤ rkIdx (fixV (Subgroup.zpowers x)) := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hK' := card_eq_two_pow hK
  have hΓ := hasScalarCommutant' (by omega) hK
  have hp : p.Prime := hpf.out
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  have hsl := isSemilinear_fieldAut hΓ ⟨x, hXN hxX⟩
  set σ := fieldAut hΓ ⟨x, hXN hxX⟩ with hσdef
  by_cases hσ : σ = RingEquiv.refl K
  swap
  ·
    have hσp : σ ^ p = 1 := by
      have h1 := hsl.pow p
      rw [hxp] at h1
      exact h1.unique isSemilinear_one
    have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ
    obtain ⟨⟨k, hk⟩, hcard⟩ := card_fixV_of_semilinear (by omega) hK' hsl hσo hxp
    simp only [Fintype.card_fin] at hcard
    have hj : 2 * n * 3 / p = 3 * k := by
      rw [hk, show p * k * 3 = p * (3 * k) by ring, Nat.mul_div_cancel_left _ hp.pos]
    rw [hj] at hcard
    have hle : 3 * k ≤ 2 * n * Fintype.card (Fin 3) := by
      rw [Fintype.card_fin, hk]
      nlinarith [hp.two_le]
    rw [rkIdx_fixV_of_card hK' x hle hcard, Fintype.card_fin, hk]
    have hp3 : 3 ≤ p := by
      rcases hpodd with ⟨j, hj⟩
      have := hp.two_le
      omega
    have : 2 * (p * k) ≤ p * k * 3 - 3 * k := by
      have h1 : p * k * 3 - 3 * k = 3 * k * (p - 1) := by
        rw [Nat.mul_sub, mul_one]
        ring_nf
      rw [h1]
      have h2 : 2 * p ≤ 3 * (p - 1) := by omega
      nlinarith
    linarith
  rw [hσ] at hsl
  obtain ⟨Ag, rfl⟩ := exists_matAut_of_mem_linSub hsl
  set A : Matrix (Fin 3) (Fin 3) K := (Ag : Matrix (Fin 3) (Fin 3) K) with hAdef
  have hAg : Ag ^ p = 1 := matHom_injective (by rw [map_pow, map_one, matHom_apply]; exact hxp)
  have hAp : A ^ p = 1 := by rw [hAdef, ← Units.val_pow_eq_pow_val, hAg, Units.val_one]
  have hnorm : ∀ l ∈ StatedSU 3 (2 ^ n) K, Ag * l * Ag⁻¹ ∈ StatedSU 3 (2 ^ n) K := by
    intro l hl
    have hN := hXN hxX
    have hl' : natAut (StatedSU 3 (2 ^ n) K) ⟨l, hl⟩ ∈ natImage (StatedSU 3 (2 ^ n) K) :=
      ⟨_, rfl⟩
    obtain ⟨l', hl'eq⟩ := (Subgroup.mem_normalizer_iff.mp hN _).mp hl'
    have h2 : matHom (Ag * l * Ag⁻¹) = matHom (l' : GL (Fin 3) K) := by
      rw [map_mul, map_mul, map_inv, matHom_apply, matHom_apply]
      exact hl'eq.symm
    rw [matHom_injective h2]
    exact l'.2
  have hfix := rkIdx_fixV_eq_of_linear hK' (g := matAut Ag) (fixSub A) (fun v => by
    rw [mem_fixSub, toAddMap_matAut])
  by_contra hlt
  push Not at hlt
  rw [hfix, Fintype.card_fin] at hlt
  have hWne : fixSub A ≠ ⊤ := by
    intro h
    apply hx1
    refine toAddMap_injective fun v => ?_
    rw [toAddMap_matAut, toAddMap_one]
    exact mem_fixSub.mp (h ▸ Submodule.mem_top)
  have hW3 : Module.finrank K (fixSub A) < 3 := by
    have := Submodule.finrank_lt hWne
    rwa [Module.finrank_fin_fun] at this
  have hW : Module.finrank K (fixSub A) = 2 := by
    by_contra hne
    have : 3 - Module.finrank K (fixSub A) ≥ 2 := by omega
    have : 2 * n * (3 - Module.finrank K (fixSub A)) ≥ 2 * n * 2 :=
      Nat.mul_le_mul_left _ this
    omega
  obtain ⟨μ, hμ⟩ := exists_gram_scalar (by omega) hK hnorm
  have hu : IsUnitaryM n A := by
    obtain ⟨b, hbW, hbb⟩ := exists_anisotropic (by omega) hK hW
    have h1 : herm n (A *ᵥ b) (A *ᵥ b) = μ * herm n b b := by
      rw [herm_mulVec_left, Matrix.mulVec_mulVec, hμ, Matrix.smul_mulVec,
        Matrix.one_mulVec, herm_smul_right]
    rw [mem_fixSub.mp hbW] at h1
    have hμ1 : μ = 1 := by
      have : (μ - 1) * herm n b b = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hbb)
    rw [IsUnitaryM, hμ, hμ1, one_smul]
  obtain ⟨b, ℓ, hb, hb0, hb1, hb2, hℓ1, hℓp, hℓbar⟩ :=
    exists_unitary_frame (by omega) hK hu hpodd hAp hW
  set P := frameMat b with hPdef
  have hP : IsUnitaryM n P := isUnitaryM_frameMat hb
  have hAP := mul_frameMat hb0 hb1 hb2
  set Ps : Matrix (Fin 3) (Fin 3) K := (conjM n P)ᵀ with hPs
  have hPPs : P * Ps = 1 := hP.mul_conj
  have hPsP : Ps * P = 1 := hP
  have hAeq : A = conjDiag n P ℓ 0 0 1 := by
    have h1 : diagPow ℓ 0 0 1 = Matrix.diagonal ![1, 1, ℓ] := by
      rw [diagPow]
      congr 1
      ext i
      fin_cases i <;> simp
    rw [conjDiag, h1, ← hAP, Matrix.mul_assoc, ← hPs, hPPs, Matrix.mul_one]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hX : ∀ a b c : ℕ, ∃ g : GL (Fin 3) K,
      (g : Matrix (Fin 3) (Fin 3) K) = conjDiag n P ℓ a b c ∧ matAut g ∈ X := by
    intro a b c
    have hdet : (conjDiag n P ℓ a b ((p - 1) * (a + b))).det = 1 := by
      rw [det_conjDiag hP]
      have : a + b + (p - 1) * (a + b) = p * (a + b) := by
        rw [Nat.sub_mul, one_mul]
        have : a + b ≤ p * (a + b) := Nat.le_mul_of_pos_left _ hp.pos
        omega
      rw [this, pow_mul, hℓp, one_pow]
    have hmem : glOfDetOne _ hdet ∈ StatedSU 3 (2 ^ n) K := by
      refine mem_statedSU ?_ ?_
      · rw [coe_glOfDetOne]
        exact hdet
      · rw [coe_glOfDetOne, ← conjM_eq_map_pow]
        exact isUnitaryM_conjDiag hK hP hℓbar a b _
    refine ⟨glOfDetOne _ hdet * Ag ^ (c + a + b), ?_, ?_⟩
    · rw [Units.val_mul, coe_glOfDetOne, Units.val_pow_eq_pow_val, ← hAdef, hAeq,
        conjDiag_pow hP, conjDiag_mul hP]
      have e1 : a + (c + a + b) * 0 = a := by ring
      have e2 : b + (c + a + b) * 0 = b := by ring
      have e3 : (p - 1) * (a + b) + (c + a + b) * 1 = c + p * (a + b) := by
        rw [Nat.sub_mul, one_mul, mul_one]
        have : a + b ≤ p * (a + b) := Nat.le_mul_of_pos_left _ hp.pos
        omega
      rw [e1, e2, e3, conjDiag_add_p hℓp]
    · rw [← matHom_apply, map_mul, map_pow, matHom_apply, matHom_apply]
      exact X.mul_mem (hLX ⟨⟨_, hmem⟩, rfl⟩) (X.pow_mem hxX _)
  let EGL : Subgroup (GL (Fin 3) K) :=
    { carrier := {g | ∃ a b c : ℕ, (g : Matrix (Fin 3) (Fin 3) K) = conjDiag n P ℓ a b c}
      mul_mem' := by
        rintro g h ⟨a, b, c, hg⟩ ⟨a', b', c', hh⟩
        exact ⟨a + a', b + b', c + c', by rw [Units.val_mul, hg, hh, conjDiag_mul hP]⟩
      one_mem' := ⟨0, 0, 0, by rw [Units.val_one, conjDiag_zero hP]⟩
      inv_mem' := by
        rintro g ⟨a, b, c, hg⟩
        refine ⟨(p - 1) * a, (p - 1) * b, (p - 1) * c, ?_⟩
        rw [Matrix.coe_units_inv, hg]
        apply Matrix.inv_eq_right_inv
        rw [conjDiag_mul hP]
        have e : ∀ x : ℕ, x + (p - 1) * x = p * x := fun x => by
          rw [Nat.sub_mul, one_mul]
          have : x ≤ p * x := Nat.le_mul_of_pos_left _ hp.pos
          omega
        rw [e, e, e, conjDiag, diagPow_mul_p hℓp, Matrix.mul_one, ← hPs, hPPs] }
  have hmemE : ∀ g : GL (Fin 3) K, g ∈ EGL ↔
      ∃ a b c : ℕ, (g : Matrix (Fin 3) (Fin 3) K) = conjDiag n P ℓ a b c := fun g => Iff.rfl
  let E : Subgroup (MulAut (StdMod (Fin 3) K)) := EGL.map matHom
  have hEX : E ≤ X := by
    rintro _ ⟨g, ⟨a, b, c, hg⟩, rfl⟩
    obtain ⟨g', hg'e, hg'X⟩ := hX a b c
    have : g = g' := Units.ext (hg.trans hg'e.symm)
    rw [this]
    exact hg'X
  have hEel : IsElemAbelian p E := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, ⟨g, ⟨a, b, c, hg⟩, rfl⟩⟩ ⟨_, ⟨h, ⟨a', b', c', hh⟩, rfl⟩⟩
      apply Subtype.ext
      change matHom g * matHom h = matHom h * matHom g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hg, hh, conjDiag_mul hP, conjDiag_mul hP, add_comm a,
        add_comm b, add_comm c]
    · rintro _ ⟨g, ⟨a, b, c, hg⟩, rfl⟩
      rw [← map_pow]
      have : g ^ p = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, hg, conjDiag_pow hP, Units.val_one, conjDiag,
          diagPow_mul_p hℓp, Matrix.mul_one, ← hPs, hPPs]
      rw [this, map_one]
  have hswapU : IsUnitaryM n (swapMat : Matrix (Fin 3) (Fin 3) K) := by
    rw [IsUnitaryM, conjM_eq_map_pow]
    exact swapMat_unitary (by positivity)
  have hsdet : (P * swapMat * Ps).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, det_swapMat, mul_one, ← Matrix.det_mul, hPPs,
      Matrix.det_one]
  set sGL := glOfDetOne (P * swapMat * Ps) hsdet with hsGL
  have hsmem : sGL ∈ StatedSU 3 (2 ^ n) K := by
    refine mem_statedSU ?_ ?_
    · rw [hsGL, coe_glOfDetOne]
      exact hsdet
    · rw [hsGL, coe_glOfDetOne, ← conjM_eq_map_pow]
      exact (hP.mul hswapU).mul (hP.conj_transpose hK)
  set s := matAut sGL with hsdef
  have hsX : s ∈ X := hLX ⟨⟨sGL, hsmem⟩, rfl⟩
  have hsm2 : (P * swapMat * Ps) * (P * swapMat * Ps) = 1 := by
    rw [show P * swapMat * Ps * (P * swapMat * Ps) = P * swapMat * (Ps * P) * swapMat * Ps by
      simp only [Matrix.mul_assoc], hPsP, Matrix.mul_one, Matrix.mul_assoc P swapMat swapMat,
      swapMat_mul_self, Matrix.mul_one, hPPs]
  have hsGL2 : sGL * sGL = 1 := Units.ext (by rw [Units.val_mul, hsGL, coe_glOfDetOne, hsm2,
    Units.val_one])
  have hs2 : s ^ 2 = 1 := by
    rw [sq, hsdef, ← matHom_apply, ← map_mul, hsGL2, map_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq, hs2])
  have hsconj : ∀ a b c : ℕ, (P * swapMat * Ps) * conjDiag n P ℓ a b c * (P * swapMat * Ps) =
      conjDiag n P ℓ b a c := by
    intro a b c
    rw [conjDiag, conjDiag, show P * swapMat * Ps * (P * diagPow ℓ a b c * Ps) *
        (P * swapMat * Ps) = P * swapMat * (Ps * P) * diagPow ℓ a b c * (Ps * P) * swapMat * Ps by
      simp only [Matrix.mul_assoc], hPsP, Matrix.mul_one, Matrix.mul_one,
      show P * swapMat * diagPow ℓ a b c * swapMat * Ps =
        P * (swapMat * diagPow ℓ a b c * swapMat) * Ps by
      simp only [Matrix.mul_assoc], swapMat_mul_diagPow_mul_swapMat]
  have hsconjE : ∀ h ∈ E, s * h * s⁻¹ ∈ E := by
    rintro _ ⟨g, ⟨a, b, c, hg⟩, rfl⟩
    refine ⟨sGL * g * sGL, ⟨b, a, c, ?_⟩, ?_⟩
    · rw [Units.val_mul, Units.val_mul, hg, hsGL, coe_glOfDetOne, hsconj]
    · rw [hsinv, map_mul, map_mul, matHom_apply, matHom_apply]
  have hsN : s ∈ Subgroup.normalizer (E : Set (MulAut (StdMod (Fin 3) K))) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨hsconjE h, fun hh => ?_⟩
    have := hsconjE _ hh
    rwa [hsinv, show s * (s * h * s) * s = (s * s) * h * (s * s) by group, ← sq, hs2, one_mul,
      mul_one] at this
  have hsC : s ∉ Subgroup.centralizer (E : Set (MulAut (StdMod (Fin 3) K))) := by
    intro hc
    obtain ⟨g1, hg1, -⟩ := hX 1 0 0
    have h1 := Subgroup.mem_centralizer_iff.mp hc (matAut g1) ⟨g1, ⟨1, 0, 0, hg1⟩, rfl⟩
    have h2 : g1 * sGL = sGL * g1 := matHom_injective (by
      rw [map_mul, map_mul, matHom_apply, matHom_apply]
      exact h1)
    have h3 := congrArg (fun g : GL (Fin 3) K => ((g * sGL : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) h2
    simp only [Units.val_mul] at h3
    rw [hsGL, coe_glOfDetOne, hg1, Matrix.mul_assoc, hsm2, Matrix.mul_one, hsconj] at h3
    have h4 := congrFun (congrFun (conjDiag_injective hP h3) 0) 0
    simp [diagPow] at h4
    exact hℓ1 h4
  have hcyc := isCyclic_inf_centralizer_of_hypBang hB hp2 hEX hEel hsX hs2 hsN hsC
  have hcomm : ∀ (g : GL (Fin 3) K) (a c : ℕ),
      (g : Matrix (Fin 3) (Fin 3) K) = conjDiag n P ℓ a a c →
      matAut g ∈ Subgroup.centralizer ({s} : Set (MulAut (StdMod (Fin 3) K))) := by
    intro g a c hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [hsdef, ← matHom_apply, ← matHom_apply, ← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hsGL, coe_glOfDetOne, hg]
    have := hsconj a a c
    calc P * swapMat * Ps * conjDiag n P ℓ a a c
        = P * swapMat * Ps * conjDiag n P ℓ a a c * ((P * swapMat * Ps) * (P * swapMat * Ps)) := by
          rw [hsm2, Matrix.mul_one]
      _ = (P * swapMat * Ps * conjDiag n P ℓ a a c * (P * swapMat * Ps)) * (P * swapMat * Ps) := by
          simp only [Matrix.mul_assoc]
      _ = conjDiag n P ℓ a a c * (P * swapMat * Ps) := by rw [this]
  have hxmem : matAut Ag ∈ E ⊓ Subgroup.centralizer ({s} : Set (MulAut (StdMod (Fin 3) K))) :=
    ⟨⟨Ag, ⟨0, 0, 1, hAeq⟩, rfl⟩, hcomm Ag 0 1 hAeq⟩
  obtain ⟨gz, hgz, -⟩ := hX 1 1 0
  have hzmem : matAut gz ∈ E ⊓ Subgroup.centralizer ({s} : Set (MulAut (StdMod (Fin 3) K))) :=
    ⟨⟨gz, ⟨1, 1, 0, hgz⟩, rfl⟩, hcomm gz 1 0 hgz⟩
  have hexp : ∀ g ∈ E ⊓ Subgroup.centralizer ({s} : Set (MulAut (StdMod (Fin 3) K))),
      g ^ p = 1 := fun g hg => hEel.2 g hg.1
  have hz := mem_zpowers_of_isCyclic hcyc hexp hxmem hx1 hzmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hb0fix : Multiplicative.ofAdd (b 0) ∈ fixV (Subgroup.zpowers (matAut Ag)) := by
    rw [mem_fixV_zpowers_iff]
    exact congrArg Multiplicative.ofAdd hb0
  have h1 : toAddMap (matAut gz) (b 0) = b 0 := by
    rw [← hk]
    exact congrArg Multiplicative.toAdd (hb0fix _ (Subgroup.zpow_mem_zpowers _ k))
  have hPsb0 : Ps *ᵥ b 0 = Pi.single 0 1 := by
    rw [← frameMat_mulVec_single b 0, ← hPdef, Matrix.mulVec_mulVec, hPsP, Matrix.one_mulVec]
  have h2 : toAddMap (matAut gz) (b 0) = ℓ • b 0 := by
    rw [toAddMap_matAut, hgz, conjDiag, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hPs,
      hPsb0]
    have : diagPow ℓ 1 1 0 *ᵥ Pi.single 0 1 = ℓ • Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp [diagPow, Matrix.mulVec_diagonal]
    rw [this, Matrix.mulVec_smul, hPdef, frameMat_mulVec_single]
  have hb0ne : b 0 ≠ 0 := by
    intro h
    have := hb 0 0
    rw [h] at this
    simp [herm] at this
  have : (ℓ - 1) • b 0 = 0 := by rw [sub_smul, one_smul, ← h2, h1, sub_self]
  exact hℓ1 (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hb0ne))


theorem le_betaH (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hLX : natImage (StatedSU 3 (2 ^ n) K) ≤ X)
    (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) (hB : HypBang X) :
    ((4 * n : ℕ) : ℕ∞) ≤ betaH X := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  rw [le_betaH_iff_isPGroup]
  intro U _ hnp
  obtain ⟨p, hp, hp2, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(X ⊓ centSub U) := by
    by_contra h
    push Not at h
    apply hnp
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro d hd hdd
    by_contra hd2
    exact h d hd hd2 hdd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ centSub U)) p hpdvd
  have hxo : orderOf (y : MulAut (StdMod (Fin 3) K)) = p := by
    rw [Subgroup.orderOf_coe, hy]
  have hUx : U ≤ fixV (Subgroup.zpowers (y : MulAut (StdMod (Fin 3) K))) := fun u hu =>
    mem_fixV_zpowers_iff.mpr (y.2.2 u hu)
  have h1 := le_rkIdx_fixV_of_odd hn hK hLX hXN hB hp2 y.2.1 hxo
  have h2 := rkIdx_anti hUx
  exact_mod_cast h1.trans h2

end SU3

open SU3 in
theorem H2_SU3_beta {V : Type*} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)} {n : ℕ}
    (hn : 2 ≤ n) (hL : BinaryNaturalSU3 L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) (hB : HypBang M) :
    ((4 * n : ℕ) : ℕ∞) ≤ betaH M := by
  obtain ⟨K, _, _, hK, hreal⟩ := hL
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * n) (SU3.card_eq_two_pow hK)
  obtain ⟨e, h1, h2⟩ := exists_transport_natural hreal hLM hMN
  rw [← betaH_map_congrHom e]
  exact le_betaH hn hK h1 h2 ((hypBang_map_congrHom e).mpr hB)

end H

end CFSG.Quasithin
