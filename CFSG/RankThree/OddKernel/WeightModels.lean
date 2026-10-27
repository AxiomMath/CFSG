module

public import CFSG.RankThree.OddKernel.TwoRankTwo
public import CFSG.LocalAnalysis.RankTwoShapes.SingleInvolutionClass

public section

namespace CFSG.RankThree.OddKernel

open Module Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coordinates

variable {p : ℕ} [hp : Fact p.Prime] {W : Type*} [Group W] {n : ℕ}

theorem card_coord_mem [Finite W] (e : W ≃* Multiplicative (Fin n → ZMod p))
    (U : Submodule (ZMod p) (Fin n → ZMod p)) :
    Nat.card {w : W // Multiplicative.toAdd (e w) ∈ U} = p ^ finrank (ZMod p) U := by
  have eqv : {w : W // Multiplicative.toAdd (e w) ∈ U} ≃ U :=
    { toFun := fun w => ⟨Multiplicative.toAdd (e w), w.2⟩
      invFun := fun v => ⟨e.symm (Multiplicative.ofAdd v), by simp⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  rw [Nat.card_congr eqv, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem apply_eq_self_iff_coord (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ : MulAut W)
    (w : W) : σ w = w ↔ Multiplicative.toAdd (e w) ∈ fixSpace (coordLin e σ) := by
  rw [mem_fixSpace, coordLin_apply]
  constructor
  · intro h
    rw [h]
  · intro h
    exact e.injective (Multiplicative.toAdd.injective h)

theorem apply_eq_inv_iff_coord (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ : MulAut W)
    (w : W) : σ w = w⁻¹ ↔ Multiplicative.toAdd (e w) ∈ negSpace (coordLin e σ) := by
  rw [mem_negSpace, coordLin_apply, ← toAdd_inv, ← map_inv]
  constructor
  · intro h
    rw [h]
  · intro h
    exact e.injective (Multiplicative.toAdd.injective h)

theorem four_group_weights [Finite W] (hp2 : p ≠ 2) (hWcomm : ∀ x y : W, x * y = y * x)
    (hWpow : ∀ x : W, x ^ p = 1) {σ τ : MulAut W} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hστ : σ * τ = τ * σ) (hσ1 : σ ≠ 1) {c : ℕ} (hcσ : Nat.card {w : W // σ w = w} = p ^ c)
    (hcτ : Nat.card {w : W // τ w = w} = p ^ c)
    (hcστ : Nat.card {w : W // (σ * τ) w = w} = p ^ c) :
    ∃ d₀ d : ℕ, d₀ + d = c ∧ 1 ≤ d ∧ Nat.card W = p ^ (d₀ + 3 * d) ∧
      Nat.card {w : W // σ w = w ∧ τ w = w} = p ^ d₀ ∧
      ∀ ε₁ ε₂ : ℤˣ, (ε₁ ≠ 1 ∨ ε₂ ≠ 1) →
        Nat.card {w : W // σ w = w ^ (ε₁ : ℤ) ∧ τ w = w ^ (ε₂ : ℤ)} = p ^ d := by
  classical
  have hWp : IsPGroup p W := fun x => ⟨1, by rw [pow_one, hWpow]⟩
  obtain ⟨n, hn⟩ := hWp.exists_card_eq
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hn
  have h2K : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hinv := coordLin_involution e hσ
  have hinvτ := coordLin_involution e hτ
  have hcomm := coordLin_comm e hστ
  obtain ⟨hX, hXσ, hXτ, hXστ⟩ := finrank_four_group h2K (coordLin e σ) (coordLin e τ) hinv
    hinvτ hcomm ⊤ (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
  rw [top_inf_eq, top_inf_eq, top_inf_eq, top_inf_eq, finrank_top,
    Module.finrank_fin_fun] at hX
  rw [top_inf_eq, top_inf_eq, top_inf_eq] at hXσ hXτ hXστ
  rw [← coordLin_mul] at hXστ
  rw [card_fixed_eq_pow e] at hcσ hcτ hcστ
  have ec1 := Nat.pow_right_injective hp.out.two_le hcσ
  have ec2 := Nat.pow_right_injective hp.out.two_le hcτ
  have ec3 := Nat.pow_right_injective hp.out.two_le hcστ
  have hd : 1 ≤ finrank (ZMod p) ↥(fixSpace (coordLin e σ) ⊓ negSpace (coordLin e τ)) := by
    by_contra h0
    apply hσ1
    apply coordLin_injective e
    rw [coordLin_one]
    have htop : fixSpace (coordLin e σ) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      omega
    exact LinearMap.ext fun v => mem_fixSpace.1 (htop ▸ Submodule.mem_top)
  have hset : ∀ (ε₁ ε₂ : ℤˣ) (U : Submodule (ZMod p) (Fin n → ZMod p)),
      (∀ w : W, (σ w = w ^ (ε₁ : ℤ) ∧ τ w = w ^ (ε₂ : ℤ)) ↔
        Multiplicative.toAdd (e w) ∈ U) →
      Nat.card {w : W // σ w = w ^ (ε₁ : ℤ) ∧ τ w = w ^ (ε₂ : ℤ)} =
        p ^ finrank (ZMod p) U := by
    intro ε₁ ε₂ U hU
    rw [← card_coord_mem e U]
    exact Nat.card_congr (Equiv.subtypeEquivRight hU)
  refine ⟨finrank (ZMod p) ↥(fixSpace (coordLin e σ) ⊓ fixSpace (coordLin e τ)),
    finrank (ZMod p) ↥(fixSpace (coordLin e σ) ⊓ negSpace (coordLin e τ)), by omega, hd,
    by rw [hn]; congr 1; omega, ?_, fun ε₁ ε₂ hε => ?_⟩
  · have h := hset 1 1 (fixSpace (coordLin e σ) ⊓ fixSpace (coordLin e τ)) fun w => by
      simp only [Units.val_one, zpow_one, Submodule.mem_inf, apply_eq_self_iff_coord e]
    simpa only [Units.val_one, zpow_one] using h
  rcases Int.units_eq_one_or ε₁ with rfl | rfl <;> rcases Int.units_eq_one_or ε₂ with rfl | rfl
  · exact absurd hε (by simp)
  · rw [hset 1 (-1) (fixSpace (coordLin e σ) ⊓ negSpace (coordLin e τ)) fun w => by
      simp only [Units.val_one, Units.val_neg, zpow_one, zpow_neg, Submodule.mem_inf,
        apply_eq_self_iff_coord e, apply_eq_inv_iff_coord e]]
  · rw [hset (-1) 1 (negSpace (coordLin e σ) ⊓ fixSpace (coordLin e τ)) fun w => by
      simp only [Units.val_one, Units.val_neg, zpow_one, zpow_neg, Submodule.mem_inf,
        apply_eq_self_iff_coord e, apply_eq_inv_iff_coord e]]
    congr 1
    omega
  · rw [hset (-1) (-1) (negSpace (coordLin e σ) ⊓ negSpace (coordLin e τ)) fun w => by
      simp only [Units.val_neg, Units.val_one, zpow_neg, zpow_one, Submodule.mem_inf,
        apply_eq_inv_iff_coord e]]
    congr 1
    omega

theorem mem_four_group {G : Type*} [Group G] {V : Subgroup G} (hV4 : Nat.card V = 4) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hab1 : a * b ≠ 1)
    (hab2 : a * b ≠ a) (hab3 : a * b ≠ b) : ∀ v ∈ V, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  classical
  intro v hv
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hsub : ({v, 1, a, b, a * b} : Set G) ⊆ V := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hv
    · exact V.one_mem
    · exact ha
    · exact hb
    · exact V.mul_mem ha hb
  have hfinV : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  have h5 : ({v, 1, a, b, a * b} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3, h4]),
      Set.ncard_insert_of_notMem (by simp [ha1.symm, hb1.symm, hab1.symm]),
      Set.ncard_insert_of_notMem (by simp [hab, hab2.symm]),
      Set.ncard_pair (Ne.symm hab3)]
  have hV : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hV4
  have := Set.ncard_le_ncard hsub (Set.toFinite (V : Set G))
  omega

end Coordinates

theorem card_fixed_conj {W G : Type*} [Group W] [Group G] (α : G →* MulAut W) (g t : G) :
    Nat.card {w : W // α (g * t * g⁻¹) w = w} = Nat.card {w : W // α t w = w} := by
  refine (Nat.card_congr ?_).symm
  exact
    { toFun := fun w => ⟨α g w, by
        rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
          MulEquiv.symm_apply_apply, w.2]⟩
      invFun := fun w => ⟨(α g).symm w.1, by
        obtain ⟨w, hw⟩ := w
        rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
          MulAut.inv_apply] at hw
        have := congrArg (α g).symm hw
        rwa [MulEquiv.symm_apply_apply] at this⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

theorem isConj_involutions_of_mulEquiv {R S : Type*} [Group R] [Group S] [Finite R]
    (B : Subgroup R) [B.Normal] (hB : Odd (Nat.card B)) (e : R ⧸ B ≃* S)
    (hS : ∀ s s' : S, orderOf s = 2 → orderOf s' = 2 → IsConj s s') :
    ∀ r r' : R, orderOf r = 2 → orderOf r' = 2 → IsConj r r' := by
  intro r r' hr hr'
  refine isConj_of_isConj_quotient B hB (fun x y hx hy => ?_) hr hr'
  have hc := hS (e x) (e y) (by rw [MulEquiv.orderOf_eq, hx]) (by rw [MulEquiv.orderOf_eq, hy])
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]

theorem exists_involution_lift {Y H : Type*} [Group Y] [Finite Y] [Group H] (φ : Y →* H)
    (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) {x : H} (hx : orderOf x = 2) :
    ∃ t : Y, orderOf t = 2 ∧ φ t = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hlift := exists_two_subgroup_map_eq φ hφ hker (zpowers x) hE
  obtain ⟨A, -, hAE, hinj⟩ := hlift
  have hxA : x ∈ A.map φ := hAE ▸ mem_zpowers x
  obtain ⟨t, htA, rfl⟩ := mem_map.1 hxA
  refine ⟨t, ?_, rfl⟩
  have h1 := orderOf_injective _ hinj ⟨t, htA⟩
  have h2 : orderOf (⟨t, htA⟩ : A) = orderOf t := (Subgroup.orderOf_coe (⟨t, htA⟩ : A)).symm
  rw [← h2, ← h1, ← hx]
  rfl

theorem weights_of_four_group {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {W : Type*} [Group W]
    [Finite W] (hWcomm : ∀ x y : W, x * y = y * x) (hWpow : ∀ x : W, x ^ p = 1)
    {R : Subgroup (MulAut W)} {c : ℕ} (hc : c = 1 ∨ c = 2)
    (hcR : ∀ r : R, orderOf r = 2 → Nat.card {w : W // (r : MulAut W) w = w} = p ^ c)
    (V : Subgroup R) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hV4 : Nat.card V = 4) :
    ∃ d₀ d : ℕ, ((d₀, d) = (0, 1) ∨ (d₀, d) = (1, 1) ∨ (d₀, d) = (0, 2)) ∧
      Nat.card W = p ^ (d₀ + 3 * d) ∧
      Nat.card {w : W // ∀ v : V, ((v : R) : MulAut W) w =
        w ^ (((1 : V →* ℤˣ) v : ℤˣ) : ℤ)} = p ^ d₀ ∧
      ∀ χ : V →* ℤˣ, χ ≠ 1 →
        Nat.card {w : W // ∀ v : V, ((v : R) : MulAut W) w = w ^ ((χ v : ℤˣ) : ℤ)} = p ^ d := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  have : Fintype V := Fintype.ofFinite V
  have hsq : ∀ x : V, x * x = 1 := fun x => Subtype.ext (by
    rw [← sq]
    exact hV2 x x.2)
  have hcomm : ∀ x y : V, x * y = y * x := fun x y => Subtype.ext (hVc _ x.2 _ y.2)
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1} : Finset V)) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hV4]; simp)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1, a} : Finset V)) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hV4]
      exact Finset.card_le_two.trans_lt (by norm_num))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb
  obtain ⟨hb1, hba⟩ := hb
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
  have hab1 : a * b ≠ 1 := fun h => hba (by rw [← hainv]; exact eq_inv_of_mul_eq_one_right h)
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha (by simpa using h)
  have henum : ∀ v : V, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := fun v =>
    mem_four_group (V := (⊤ : Subgroup V)) (by rw [card_top, hV4]) (mem_top a) (mem_top b) ha
      hb1 (Ne.symm hba) hab1 hab2 hab3 v (mem_top v)
  set σ : MulAut W := ((a : R) : MulAut W) with hσdef
  set τ : MulAut W := ((b : R) : MulAut W) with hτdef
  have hcoe : ∀ x y : V,
      (((x * y : V) : R) : MulAut W) = ((x : R) : MulAut W) * ((y : R) : MulAut W) :=
    fun _ _ => rfl
  have hσ : σ * σ = 1 := by rw [hσdef, ← hcoe, hsq]; rfl
  have hτ : τ * τ = 1 := by rw [hτdef, ← hcoe, hsq]; rfl
  have hστ : σ * τ = τ * σ := by rw [hσdef, hτdef, ← hcoe, ← hcoe, hcomm]
  have hσ1 : σ ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
  have hord : ∀ x : V, x ≠ 1 → orderOf (x : R) = 2 := fun x hx =>
    orderOf_eq_prime (by rw [sq]; exact congrArg Subtype.val (hsq x))
      (fun h => hx (Subtype.ext h))
  have hcσ := hcR (a : R) (hord a ha)
  have hcτ := hcR (b : R) (hord b hb1)
  have hcστ := hcR ((a * b : V) : R) (hord (a * b) hab1)
  rw [hcoe] at hcστ
  have hw := four_group_weights hp2 hWcomm hWpow hσ hτ hστ hσ1 hcσ hcτ hcστ
  obtain ⟨d₀, d, hsum, hd, hcard, h11, hother⟩ := hw
  have key : ∀ χ : V →* ℤˣ, ∀ w : W,
      (∀ v : V, ((v : R) : MulAut W) w = w ^ ((χ v : ℤˣ) : ℤ)) ↔
        (σ w = w ^ ((χ a : ℤˣ) : ℤ) ∧ τ w = w ^ ((χ b : ℤˣ) : ℤ)) := by
    intro χ w
    constructor
    · intro h
      exact ⟨h a, h b⟩
    · rintro ⟨h1, h2⟩ v
      rcases henum v with rfl | rfl | rfl | rfl
      · simp
      · exact h1
      · exact h2
      · rw [hcoe, MulAut.mul_apply, map_mul, Units.val_mul, zpow_mul, ← h1, ← map_zpow, ← h2]
  have hone : ∀ χ : V →* ℤˣ, χ a = 1 → χ b = 1 → χ = 1 := by
    intro χ ha' hb'
    refine MonoidHom.ext fun v => ?_
    rcases henum v with rfl | rfl | rfl | rfl
    · simp
    · simpa using ha'
    · simpa using hb'
    · simp [ha', hb']
  refine ⟨d₀, d, ?_, hcard, ?_, fun χ hχ => ?_⟩
  · simp only [Prod.mk.injEq]
    rcases hc with rfl | rfl <;> omega
  · rw [← h11]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    rw [key]
    simp
  · rw [← hother (χ a) (χ b) (by
      by_contra h
      push Not at h
      exact hχ (hone χ h.1 h.2))]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w => key χ w)

theorem exists_common_fixed_dim {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {W : Type*} [Group W]
    [Finite W] (hWcomm : ∀ x y : W, x * y = y * x) (hWpow : ∀ x : W, x ^ p = 1)
    {R : Subgroup (MulAut W)}
    (hRconj : ∀ r r' : R, orderOf r = 2 → orderOf r' = 2 → IsConj r r') {r₀ : R}
    (hr₀ : orderOf r₀ = 2) (hfix₀ : Nat.card {w : W // (r₀ : MulAut W) w = w} ≤ p ^ 2)
    (hninv : ¬ ∀ w : W, (r₀ : MulAut W) w = w⁻¹) :
    ∃ c : ℕ, (c = 1 ∨ c = 2) ∧ ∀ r : R, orderOf r = 2 →
      Nat.card {w : W // (r : MulAut W) w = w} = p ^ c := by
  have hWp : IsPGroup p W := fun x => ⟨1, by rw [pow_one, hWpow]⟩
  have hcardW := hWp.exists_card_eq
  obtain ⟨n, hn⟩ := hcardW
  have hcw := nonempty_mulEquiv_of_elementary hWcomm hWpow hn
  obtain ⟨cw⟩ := hcw
  have hc₀ := card_fixed_eq_pow cw (r₀ : MulAut W)
  refine ⟨finrank (ZMod p) (fixSpace (coordLin cw (r₀ : MulAut W))), ?_, fun r hr => ?_⟩
  · have hc2 : finrank (ZMod p) (fixSpace (coordLin cw (r₀ : MulAut W))) ≤ 2 := by
      rw [hc₀] at hfix₀
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hfix₀
    have hc1 : finrank (ZMod p) (fixSpace (coordLin cw (r₀ : MulAut W))) ≠ 0 := by
      intro h0
      apply hninv
      have hsq : (r₀ : MulAut W) * (r₀ : MulAut W) = 1 := by
        change ((r₀ * r₀ : R) : MulAut W) = 1
        rw [← sq, ← hr₀, pow_orderOf_eq_one]
        rfl
      exact (coordLin_eq_neg_iff cw _).1
        (eq_neg_of_fixSpace_eq_bot (two_ne_zero_zmod hp2) _ (coordLin_involution cw hsq) h0)
    omega
  · have hgc := isConj_iff.1 (hRconj r₀ r hr₀ hr)
    obtain ⟨g, rfl⟩ := hgc
    rw [← hc₀]
    exact card_fixed_conj R.subtype g r₀

theorem noncentral_odd_prime_kernel_critical_weight_models {p : ℕ} [hp : Fact p.Prime]
    (hp3 : 3 < p) {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y)
    [P.Normal] (hP : IsPGroup p P) (hP1 : P ≠ ⊥) (hE : layer (Y ⧸ P) = ⊤)
    (hZ : center (Y ⧸ P) = ⊥) (hYP : ⁅(⊤ : Subgroup Y), P⁆ ≠ ⊥) (hloc : localRank p Y ≤ 2) :
    ∃ D : Subgroup P, ∃ _ : D.Characteristic, D ≠ ⊥ ∧ Monoid.exponent D = p ∧
      ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P) ∧
      IsPGroup p (frattiniAction D).ker ∧
      (frattiniConjAction P D).ker ≤ P ∧
      IsSimpleGroup (Y ⧸ P) ∧ (∃ a b : Y ⧸ P, a * b ≠ b * a) ∧ pRank 2 (Y ⧸ P) = 2 ∧
      (frattiniConjAction P D).range ≠ ⊥ ∧ Group.IsPerfect (frattiniConjAction P D).range ∧
      (∀ (n : ℕ) (e : D ⧸ frattini D ≃* Multiplicative (Fin n → ZMod p)),
        ∀ r ∈ (frattiniConjAction P D).range,
          Matrix.GeneralLinearGroup.det (elemAutEquivGL e r) = 1) ∧
      P.map (frattiniConjAction P D).rangeRestrict =
        CFSG.pCore p (frattiniConjAction P D).range ∧
      (∃ _ : (P.map (frattiniConjAction P D).rangeRestrict).Normal,
        ∃ e : ((frattiniConjAction P D).range ⧸ P.map (frattiniConjAction P D).rangeRestrict) ≃*
          (Y ⧸ P), ∀ y : Y,
            e (QuotientGroup.mk ((frattiniConjAction P D).rangeRestrict y)) =
              QuotientGroup.mk y) ∧
      (∀ r r' : (frattiniConjAction P D).range, orderOf r = 2 → orderOf r' = 2 → IsConj r r') ∧
      (∃ c : ℕ, (c = 1 ∨ c = 2) ∧ ∀ r : (frattiniConjAction P D).range, orderOf r = 2 →
        Nat.card {w : D ⧸ frattini D // (r : MulAut (D ⧸ frattini D)) w = w} = p ^ c) ∧
      ∀ V : Subgroup (frattiniConjAction P D).range, (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) →
        (∀ x ∈ V, x ^ 2 = 1) → Nat.card V = 4 →
        ∃ d₀ d : ℕ, ((d₀, d) = (0, 1) ∨ (d₀, d) = (1, 1) ∨ (d₀, d) = (0, 2)) ∧
          Nat.card (D ⧸ frattini D) = p ^ (d₀ + 3 * d) ∧
          Nat.card {w : D ⧸ frattini D // ∀ v : V,
              ((v : (frattiniConjAction P D).range) : MulAut (D ⧸ frattini D)) w =
                w ^ (((1 : V →* ℤˣ) v : ℤˣ) : ℤ)} = p ^ d₀ ∧
          ∀ χ : V →* ℤˣ, χ ≠ 1 → Nat.card {w : D ⧸ frattini D // ∀ v : V,
              ((v : (frattiniConjAction P D).range) : MulAut (D ⧸ frattini D)) w =
                w ^ ((χ v : ℤˣ) : ℤ)} = p ^ d := by
  classical
  have hp2 : p ≠ 2 := by omega
  have h6 := noncentral_odd_prime_kernel_two_rank_exactly_two hp3 P hP hP1 hE hZ hYP hloc
  have hS2 : pRank 2 (Y ⧸ P) = 2 := h6.2.2.1
  have h5 := noncentral_odd_prime_kernel_simple_quotient hp3 P hP hP1 hE hZ hYP hloc
  obtain ⟨D, hDc, hD1, hexp, hDZ, hker, hclass, hR, hRperf, hdet, hfixall, hSs, hSnab, hKP,
    hBO, hψex, hiso, hfaith⟩ := h5
  have hψex' := hψex
  obtain ⟨ψ, hψs, hψker, hψapp⟩ := hψex'
  have hiso' := hiso
  obtain ⟨hBn, e, he⟩ := hiso'
  refine ⟨D, hDc, hD1, hexp, hDZ, hker, hKP, hSs, hSnab, hS2, hR, hRperf, hdet, hBO, hiso, ?_⟩
  have hPodd : Odd (Nat.card P) := by
    have hk := hP.exists_card_eq
    obtain ⟨k, hk⟩ := hk
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  have : Finite (frattiniConjAction P D).range :=
    Finite.of_surjective _ (frattiniConjAction P D).rangeRestrict_surjective
  have hBodd : Odd (Nat.card (P.map (frattiniConjAction P D).rangeRestrict)) :=
    Odd.of_dvd_nat hPodd (Subgroup.card_map_dvd P _)
  have hrank : CFSG.Assembly.twoRank (Y ⧸ P) = 2 := by
    rw [← hS2, pRank_eq_open_pRank_top]
    rfl
  have hSconj : ∀ s s' : Y ⧸ P, orderOf s = 2 → orderOf s' = 2 → IsConj s s' := by
    intro s s' hs hs'
    have hz := CFSG.RankTwoShapes.rank_two_simple_involutions_conjugate hSnab hrank
    obtain ⟨z, -, hz⟩ := hz
    obtain ⟨g, hg⟩ := hz s hs
    obtain ⟨g', hg'⟩ := hz s' hs'
    refine isConj_iff.2 ⟨g' * g⁻¹, ?_⟩
    calc g' * g⁻¹ * s * (g' * g⁻¹)⁻¹ = g' * (g⁻¹ * s * g) * g'⁻¹ := by group
      _ = s' := by rw [hg, ← hg']; group
  have hRconj := isConj_involutions_of_mulEquiv _ hBodd e hSconj
  refine ⟨hRconj, ?_⟩
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hel := frattini_quotient_elementary hDp
  obtain ⟨-, hWcomm, hWpow⟩ := hel
  have hS1 := CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hSnab
  obtain ⟨-, s₀, hs₀⟩ := hS1
  have hlift₀ := exists_involution_lift (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
    (by rw [QuotientGroup.ker_mk']; exact hPodd) hs₀
  obtain ⟨t₀, ht₀, ht₀s⟩ := hlift₀
  have hψr₀ : ψ ((frattiniConjAction P D).rangeRestrict t₀) = s₀ := by
    rw [hψapp]
    exact ht₀s
  have hr₀2 : orderOf ((frattiniConjAction P D).rangeRestrict t₀) = 2 := by
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [← map_pow, ← ht₀, pow_orderOf_eq_one, map_one]
    · rw [h, map_one] at hψr₀
      rw [← hψr₀, orderOf_one] at hs₀
      exact absurd hs₀ (by norm_num)
  have hninv : ¬ ∀ w, (((frattiniConjAction P D).rangeRestrict t₀ :
      (frattiniConjAction P D).range) : MulAut (D ⧸ frattini D)) w = w⁻¹ := by
    intro hinv
    have hcen : (frattiniConjAction P D).rangeRestrict t₀ ∈
        center (frattiniConjAction P D).range := by
      rw [mem_center_iff]
      intro r
      apply Subtype.ext
      ext w
      change ((r : (frattiniConjAction P D).range) : MulAut (D ⧸ frattini D))
          ((((frattiniConjAction P D).rangeRestrict t₀ : (frattiniConjAction P D).range) :
            MulAut (D ⧸ frattini D)) w) =
        (((frattiniConjAction P D).rangeRestrict t₀ : (frattiniConjAction P D).range) :
            MulAut (D ⧸ frattini D)) (((r : (frattiniConjAction P D).range) :
              MulAut (D ⧸ frattini D)) w)
      rw [hinv, hinv, map_inv]
    have hcenS : ψ ((frattiniConjAction P D).rangeRestrict t₀) ∈ center (Y ⧸ P) := by
      rw [mem_center_iff]
      intro s
      obtain ⟨r, rfl⟩ := hψs s
      rw [← map_mul, ← map_mul, mem_center_iff.1 hcen r]
    rw [hZ, mem_bot, hψr₀] at hcenS
    rw [hcenS, orderOf_one] at hs₀
    exact absurd hs₀ (by norm_num)
  have hc := exists_common_fixed_dim hp2 hWcomm hWpow hRconj hr₀2 (hfixall t₀ ht₀).2 hninv
  obtain ⟨c, hc12, hcR⟩ := hc
  exact ⟨⟨c, hc12, hcR⟩, fun V hVc hV2 hV4 =>
    weights_of_four_group hp2 hWcomm hWpow hc12 hcR V hVc hV2 hV4⟩

end CFSG.RankThree.OddKernel
