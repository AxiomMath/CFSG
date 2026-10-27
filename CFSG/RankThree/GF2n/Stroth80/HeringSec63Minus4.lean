module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinusType

public section

namespace CFSG.RankThree.GF2n.Stroth80

namespace HS6

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Lines

variable (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W]

@[expose] def lineGrp (w : W) : Subgroup (Multiplicative W) where
  carrier := {x | ∃ c : K, Multiplicative.toAdd x = c • w}
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [toAdd_mul, hc, hd, add_smul]⟩
  one_mem' := ⟨0, by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc⟩
    exact ⟨-c, by rw [toAdd_inv, hc, neg_smul]⟩

variable {K}

theorem ofAdd_smul_mem_lineGrp (w : W) (c : K) :
    Multiplicative.ofAdd (c • w) ∈ lineGrp K w := ⟨c, by simp⟩

@[expose] def lineHom (w : W) : Multiplicative K →* lineGrp K w :=
  MonoidHom.mk' (fun c => ⟨Multiplicative.ofAdd (Multiplicative.toAdd c • w),
    ofAdd_smul_mem_lineGrp w _⟩) (fun a b => by
      apply Subtype.ext
      show Multiplicative.ofAdd (Multiplicative.toAdd (a * b) • w) =
        Multiplicative.ofAdd (Multiplicative.toAdd a • w) *
          Multiplicative.ofAdd (Multiplicative.toAdd b • w)
      rw [toAdd_mul, add_smul, ofAdd_add])

@[expose] noncomputable def lineEquiv {w : W} (hw : w ≠ 0) :
    Multiplicative K ≃* lineGrp K w :=
  MulEquiv.ofBijective (lineHom w)
    ⟨fun a b h => by
      have h1 : Multiplicative.toAdd a • w = Multiplicative.toAdd b • w := by
        have := congrArg (fun x : lineGrp K w => Multiplicative.toAdd (x : Multiplicative W)) h
        simpa [lineHom] using this
      exact Multiplicative.toAdd.injective (smul_left_injective K hw h1),
     fun x => by
      obtain ⟨c, hc⟩ := x.2
      refine ⟨Multiplicative.ofAdd c, Subtype.ext ?_⟩
      show Multiplicative.ofAdd (c • w) = x
      rw [← hc]
      rfl⟩

theorem card_lineGrp [Finite K] {w : W} (hw : w ≠ 0) : Nat.card (lineGrp K w) = Nat.card K := by
  rw [← Nat.card_congr (lineEquiv hw).toEquiv, Nat.card_congr Multiplicative.toAdd]

theorem lineGrp_eq_iff {w w' : W} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    lineGrp K w = lineGrp K w' ↔ ∃ c : K, c ≠ 0 ∧ w' = c • w := by
  constructor
  · intro h
    have : Multiplicative.ofAdd w' ∈ lineGrp K w := by
      rw [h]
      exact ⟨1, by simp⟩
    obtain ⟨c, hc⟩ := this
    refine ⟨c, ?_, hc⟩
    rintro rfl
    rw [zero_smul] at hc
    exact hw' hc
  · rintro ⟨c, hc, rfl⟩
    apply le_antisymm
    · rintro x ⟨d, hd⟩
      exact ⟨d * c⁻¹, by rw [hd, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]⟩
    · rintro x ⟨d, hd⟩
      exact ⟨d * c, by rw [hd, smul_smul]⟩

end Lines

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

theorem lineGrp_inf_eq_bot {w w' : W} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hne : lineGrp K w ≠ lineGrp K w') : lineGrp K w ⊓ lineGrp K w' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hx0 : Multiplicative.toAdd x ≠ 0 := fun h => hx1 (Multiplicative.toAdd.injective h)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hc, zero_smul])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hd, zero_smul])
  apply hne
  rw [lineGrp_eq_iff hw hw']
  refine ⟨c * d⁻¹, mul_ne_zero hc0 (inv_ne_zero hd0), ?_⟩
  have h1 : d • w' = c • w := hd.symm.trans hc
  calc w' = (d⁻¹ * d) • w' := by rw [inv_mul_cancel₀ hd0, one_smul]
    _ = d⁻¹ • (d • w') := by rw [mul_smul]
    _ = d⁻¹ • (c • w) := by rw [h1]
    _ = (c * d⁻¹) • w := by rw [smul_smul, mul_comm]

theorem map_add_smul_singular {w₀ w₁ : W} (h₀ : Q w₀ = 0) (h₁ : Q w₁ = 0) (a b : K) :
    Q (a • w₀ + b • w₁) = a * b * polar Q w₀ w₁ := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, h₀, h₁, polar_smul_left_eq,
    polar_smul_right_eq]
  ring

theorem polar_ne_zero_of_isMinus (h : IsMinus Q 2) {w₀ w₁ : W} (h₀ : Q w₀ = 0) (h₁ : Q w₁ = 0)
    (hw₀ : w₀ ≠ 0) (hind : ∀ c : K, w₁ ≠ c • w₀) : polar Q w₀ w₁ ≠ 0 := by
  intro hp
  have hli : LinearIndependent K ![w₀, w₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hw₀, rfl⟩
    · exfalso
      apply hind (-(s / t))
      have h1 : t • w₁ = -(s • w₀) := eq_neg_of_add_eq_zero_right hst
      calc w₁ = (t⁻¹ * t) • w₁ := by rw [inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (t • w₁) := by rw [mul_smul]
        _ = t⁻¹ • (-(s • w₀)) := by rw [h1]
        _ = (-(s / t)) • w₀ := by rw [smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv, mul_comm]
  have hU : Module.finrank K (Submodule.span K {w₀, w₁}) = 2 := by
    rw [← Matrix.range_cons_cons_empty w₀ w₁ ![], finrank_span_eq_card hli, Fintype.card_fin]
  obtain ⟨u, hu, hQu⟩ := h.noTS _ hU
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  apply hQu
  rw [map_add_smul_singular h₀ h₁, hp, mul_zero]

theorem lineGrp_sum_of_isMinus (h : IsMinus Q 2) {w₀ w₁ w : W} (h₀ : Q w₀ = 0) (h₁ : Q w₁ = 0)
    (hQ : Q w = 0) (hw₀ : w₀ ≠ 0) (hw₁ : w₁ ≠ 0) (hw : w ≠ 0)
    (hne : lineGrp K w₀ ≠ lineGrp K w₁) (hle : lineGrp K w ≤ lineGrp K w₀ ⊔ lineGrp K w₁) :
    lineGrp K w = lineGrp K w₀ ∨ lineGrp K w = lineGrp K w₁ := by
  have hind : ∀ c : K, w₁ ≠ c • w₀ := by
    intro c hc
    apply hne
    rw [lineGrp_eq_iff hw₀ hw₁]
    refine ⟨c, ?_, hc⟩
    rintro rfl
    rw [zero_smul] at hc
    exact hw₁ hc
  have hp := polar_ne_zero_of_isMinus h h₀ h₁ hw₀ hind
  have hmem : Multiplicative.ofAdd w ∈ lineGrp K w₀ ⊔ lineGrp K w₁ := hle ⟨1, by simp⟩
  obtain ⟨y, ⟨a, ha⟩, z, ⟨b, hb⟩, hyz⟩ := Subgroup.mem_sup.mp hmem
  have hwab : w = a • w₀ + b • w₁ := by
    have := congrArg Multiplicative.toAdd hyz
    rw [toAdd_mul, ha, hb] at this
    simpa using this.symm
  have hab : a * b * polar Q w₀ w₁ = 0 := by rw [← map_add_smul_singular h₀ h₁, ← hwab, hQ]
  rcases mul_eq_zero.mp hab with h1 | h1
  · rcases mul_eq_zero.mp h1 with ha0 | hb0
    · right
      have hb0 : b ≠ 0 := by
        rintro rfl
        apply hw
        rw [hwab, ha0, zero_smul, zero_smul, add_zero]
      rw [(lineGrp_eq_iff hw₁ hw).mpr ⟨b, hb0, by rw [hwab, ha0, zero_smul, zero_add]⟩]
    · left
      have ha0 : a ≠ 0 := by
        rintro rfl
        apply hw
        rw [hwab, hb0, zero_smul, zero_smul, add_zero]
      rw [(lineGrp_eq_iff hw₀ hw).mpr ⟨a, ha0, by rw [hwab, hb0, zero_smul, add_zero]⟩]
  · exact absurd h1 hp

end Minus

section HypVec

variable {K : Type} [Field K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K W}

@[expose] def hypVec (P : HypPair Q) (y : W) : W := P.f + Q y • P.e + y

theorem Q_comb (P : HypPair Q) {y : W} (hy : y ∈ P.perp) (a : K) :
    Q (P.f + a • P.e + y) = a + Q y := by
  obtain ⟨hye, hyf⟩ := HypPair.mem_perp.mp hy
  rw [QuadraticMap.map_add Q (P.f + a • P.e) y, QuadraticMap.map_add Q P.f (a • P.e),
    P.Q_f, map_smul_eq_sq, P.Q_e, polar_add_left, polar_smul_left_eq, hyf, hye,
    polar_smul_right_eq, P.polar_fe]
  ring

theorem Q_hypVec (P : HypPair Q) {y : W} (hy : y ∈ P.perp) : Q (hypVec P y) = 0 := by
  rw [hypVec, Q_comb P hy]
  exact CharTwo.add_self_eq_zero _

theorem polar_e_comb (P : HypPair Q) {y : W} (hy : y ∈ P.perp) (a : K) :
    polar Q P.e (P.f + a • P.e + y) = 1 := by
  obtain ⟨hye, -⟩ := HypPair.mem_perp.mp hy
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, P.polar_ee, P.polar_ef, hye]
  ring

theorem polar_f_comb (P : HypPair Q) {y : W} (hy : y ∈ P.perp) (a : K) :
    polar Q (P.f + a • P.e + y) P.f = a := by
  obtain ⟨-, hyf⟩ := HypPair.mem_perp.mp hy
  rw [polar_add_left, polar_add_left, polar_smul_left_eq, P.polar_ff, P.polar_ef, polar_comm Q y,
    hyf]
  ring

theorem proj_comb (P : HypPair Q) {y : W} (hy : y ∈ P.perp) (a : K) :
    P.proj (P.f + a • P.e + y) = y := by
  obtain ⟨hye, hyf⟩ := HypPair.mem_perp.mp hy
  have h1 : polar Q (P.f + a • P.e + y) P.e = 1 := by
    rw [polar_comm, polar_e_comb P hy]
  rw [HypPair.proj, h1, polar_f_comb P hy, one_smul]
  abel

theorem eq_comb_of_singular (P : HypPair Q) {x : W} (hx : Q x = 0) (hx1 : polar Q P.e x = 1) :
    x = hypVec P (P.proj x) := by
  have hy := P.proj_mem_perp x
  have h1 : polar Q x P.e = 1 := by rw [polar_comm]; exact hx1
  have hxe := P.eq_add_proj x
  rw [h1] at hxe
  have hQx : Q x = polar Q x P.f + Q (P.proj x) := by
    conv_lhs => rw [hxe]
    rw [show polar Q x P.f • P.e + (1 : K) • P.f + P.proj x =
      P.f + polar Q x P.f • P.e + P.proj x by rw [one_smul]; abel]
    exact Q_comb P hy _
  have hxQ : polar Q x P.f = Q (P.proj x) := by
    rw [hx] at hQx
    have : polar Q x P.f + Q (P.proj x) = 0 := hQx.symm
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg, CharTwo.neg_eq]; exact this)
  rw [hypVec, ← hxQ]
  conv_lhs => rw [hxe]
  rw [one_smul]
  abel

end HypVec

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

variable (K Q) in
@[expose] def singLines : Set (Subgroup (Multiplicative W)) :=
  {ℓ | ∃ w, Q w = 0 ∧ w ≠ 0 ∧ ℓ = lineGrp K w}

theorem exists_singular_of_isMinus (h : IsMinus Q 2) : ∃ w : W, Q w = 0 ∧ w ≠ 0 := by
  obtain ⟨x, x', w, hx, hx', hxx, -⟩ := exists_minus_data (le_refl 2) h
  refine ⟨x, hx, fun h0 => ?_⟩
  rw [h0, polar_zero_left] at hxx
  exact zero_ne_one hxx

theorem finrank_perp_of_isMinus (h : IsMinus Q 2) (P : HypPair Q) :
    Module.finrank K P.perp = 2 := by
  have := Submodule.finrank_add_eq_of_isCompl P.isCompl_perp
  rw [P.finrank_span, h.finrank_eq] at this
  omega

theorem card_perp_of_isMinus (h : IsMinus Q 2) (P : HypPair Q) :
    Nat.card P.perp = Nat.card K ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := K), finrank_perp_of_isMinus h P]

theorem mem_line_of_orth (h : IsMinus Q 2) (P : HypPair Q) {x : W} (hx : Q x = 0)
    (hex : polar Q P.e x = 0) : ∃ c : K, x = c • P.e := by
  by_contra hcon
  push Not at hcon
  exact polar_ne_zero_of_isMinus h P.Q_e hx P.e_ne_zero (fun c => hcon c) hex

noncomputable def hypVecEquiv (P : HypPair Q) :
    {x : W // Q x = 0 ∧ polar Q P.e x = 1} ≃ P.perp where
  toFun x := ⟨P.proj x.1, P.proj_mem_perp x.1⟩
  invFun y := ⟨hypVec P y.1, Q_hypVec P y.2, by
    rw [hypVec]
    exact polar_e_comb P y.2 _⟩
  left_inv x := Subtype.ext (eq_comb_of_singular P x.2.1 x.2.2).symm
  right_inv y := Subtype.ext (proj_comb P y.2 _)

theorem ncard_singLines (h : IsMinus Q 2) : (singLines K Q).ncard = Nat.card K ^ 2 + 1 := by
  haveI : Finite W := Module.finite_of_finite K
  obtain ⟨e, he, he0⟩ := exists_singular_of_isMinus h
  obtain ⟨P, rfl⟩ := exists_hypPair h.nondeg he he0
  let T₁ : Set W := {x | Q x = 0 ∧ polar Q P.e x = 1}
  have hT₁ne : ∀ x ∈ T₁, x ≠ 0 := fun x hx h0 => by
    have := hx.2
    rw [h0, polar_zero_right] at this
    exact zero_ne_one this
  have hsing : singLines K Q = insert (lineGrp K P.e) (lineGrp K '' T₁) := by
    ext ℓ
    constructor
    · rintro ⟨w, hw, hw0, rfl⟩
      by_cases hl : lineGrp K w = lineGrp K P.e
      · left
        exact hl
      · right
        have hp : polar Q P.e w ≠ 0 := by
          intro hp0
          obtain ⟨c, hc⟩ := mem_line_of_orth h P hw hp0
          have hc0 : c ≠ 0 := by
            rintro rfl
            rw [zero_smul] at hc
            exact hw0 hc
          exact hl ((lineGrp_eq_iff P.e_ne_zero hw0).mpr ⟨c, hc0, hc⟩).symm
        refine ⟨(polar Q P.e w)⁻¹ • w, ⟨?_, ?_⟩, ?_⟩
        · rw [map_smul_eq_sq, hw, mul_zero]
        · rw [polar_smul_right_eq, inv_mul_cancel₀ hp]
        · have hx0 : (polar Q P.e w)⁻¹ • w ≠ 0 := smul_ne_zero (inv_ne_zero hp) hw0
          exact ((lineGrp_eq_iff hw0 hx0).mpr ⟨(polar Q P.e w)⁻¹, inv_ne_zero hp, rfl⟩).symm
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨P.e, P.Q_e, P.e_ne_zero, rfl⟩
      · exact ⟨x, hx.1, hT₁ne x hx, rfl⟩
  have hnot : lineGrp K P.e ∉ lineGrp K '' T₁ := by
    rintro ⟨x, hx, hxe⟩
    obtain ⟨c, -, hc⟩ := (lineGrp_eq_iff (hT₁ne x hx) P.e_ne_zero).mp hxe
    have := hx.2
    rw [hc, polar_smul_left_eq, polar_self_eq_zero hx.1, mul_zero] at this
    exact zero_ne_one this
  have hinj : Set.InjOn (lineGrp K) T₁ := by
    intro x hx x' hx' hxx'
    obtain ⟨c, hc0, hc⟩ := (lineGrp_eq_iff (hT₁ne x hx) (hT₁ne x' hx')).mp hxx'
    have h1 : polar Q P.e x' = c := by
      rw [hc, polar_smul_right_eq, hx.2, mul_one]
    rw [hx'.2] at h1
    rw [hc, ← h1, one_smul]
  have hcard : T₁.ncard = Nat.card K ^ 2 := by
    rw [← Nat.card_coe_set_eq, ← card_perp_of_isMinus h P]
    exact Nat.card_congr (hypVecEquiv P)
  rw [hsing, Set.ncard_insert_of_notMem hnot (Set.toFinite _), hinj.ncard_image,
    hcard]

end Count

section Span

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {Q : QuadraticForm K W}

theorem hypVec_zero (P : HypPair Q) : hypVec P 0 = P.f := by
  simp [hypVec]

theorem hypVec_add_four (P : HypPair Q) (a b : W) :
    hypVec P a + hypVec P b + hypVec P (a + b) + hypVec P 0 = polar Q a b • P.e := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ : Q (a + b) = Q a + Q b + polar Q a b := QuadraticMap.map_add Q a b
  have hsum : hypVec P a + hypVec P b + hypVec P (a + b) + hypVec P 0 - polar Q a b • P.e =
      (2 : K) • ((2 : K) • P.f + (Q a + Q b) • P.e + a + b) := by
    simp only [hypVec, hQ, map_zero]
    module
  rw [h2, zero_smul, sub_eq_zero] at hsum
  exact hsum

theorem singLines_span (h : IsMinus Q 2) {ℓ₀ : Subgroup (Multiplicative W)}
    (hℓ₀ : ℓ₀ ∈ singLines K Q) :
    (⨆ ℓ ∈ singLines K Q, ⨆ (_ : ℓ ≠ ℓ₀), ℓ) = ⊤ := by
  obtain ⟨w₀, hw₀, hw₀0, rfl⟩ := hℓ₀
  obtain ⟨P, rfl⟩ := exists_hypPair h.nondeg hw₀ hw₀0
  set S : Subgroup (Multiplicative W) :=
    ⨆ ℓ ∈ singLines K Q, ⨆ (_ : ℓ ≠ lineGrp K P.e), ℓ with hS
  have hA : ∀ y ∈ P.perp, ∀ c : K, Multiplicative.ofAdd (c • hypVec P y) ∈ S := by
    intro y hy c
    have hne0 : hypVec P y ≠ 0 := by
      intro h0
      have := polar_e_comb P hy (Q y)
      rw [show P.f + Q y • P.e + y = hypVec P y from rfl, h0, polar_zero_right] at this
      exact zero_ne_one this
    have hl : lineGrp K (hypVec P y) ≠ lineGrp K P.e := by
      intro hl
      obtain ⟨c', -, hc'⟩ := (lineGrp_eq_iff hne0 P.e_ne_zero).mp hl
      have h1 := polar_e_comb P hy (Q y)
      rw [show P.f + Q y • P.e + y = hypVec P y from rfl] at h1
      have h2 : polar Q P.e (hypVec P y) = 0 := by
        calc polar Q P.e (hypVec P y) = polar Q (c' • hypVec P y) (hypVec P y) := by
              rw [← hc']
          _ = 0 := by
            rw [polar_smul_left_eq, polar_self_eq_zero (Q_hypVec P hy), mul_zero]
      rw [h2] at h1
      exact zero_ne_one h1
    have hle : lineGrp K (hypVec P y) ≤ S :=
      le_iSup₂_of_le (lineGrp K (hypVec P y)) ⟨hypVec P y, Q_hypVec P hy, hne0, rfl⟩
        (le_iSup (fun _ : lineGrp K (hypVec P y) ≠ lineGrp K P.e => lineGrp K (hypVec P y)) hl)
    exact hle (ofAdd_smul_mem_lineGrp _ c)
  have hB : ∀ c : K, Multiplicative.ofAdd (c • P.f) ∈ S := by
    intro c
    have := hA 0 (Submodule.zero_mem _) c
    rwa [hypVec_zero] at this
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ P.perp, ∃ b ∈ P.perp, polar Q a b = 1 := by
    have hne : P.perp ≠ ⊥ := by
      intro h0
      have := finrank_perp_of_isMinus h P
      rw [h0, finrank_bot] at this
      omega
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hnd := HypPair.polarNondegOn_perp h.nondeg P
    obtain ⟨b, hb, hab⟩ : ∃ b ∈ P.perp, polar Q a b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha0 (hnd a ha hcon)
    exact ⟨a, ha, (polar Q a b)⁻¹ • b, P.perp.smul_mem _ hb, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hab]⟩
  have hC : ∀ c : K, Multiplicative.ofAdd (c • P.e) ∈ S := by
    intro c
    have hcb : c • b ∈ P.perp := P.perp.smul_mem c hb
    have h4 := hypVec_add_four P a (c • b)
    have hm : Multiplicative.ofAdd (hypVec P a + hypVec P (c • b) + hypVec P (a + c • b) +
        hypVec P 0) ∈ S := by
      rw [ofAdd_add, ofAdd_add, ofAdd_add]
      refine S.mul_mem (S.mul_mem (S.mul_mem ?_ ?_) ?_) ?_
      · simpa using hA a ha 1
      · simpa using hA (c • b) hcb 1
      · simpa using hA (a + c • b) (P.perp.add_mem ha hcb) 1
      · simpa using hA 0 (Submodule.zero_mem _) 1
    rw [h4, polar_smul_right_eq, hab, mul_one] at hm
    exact hm
  have hD : ∀ y ∈ P.perp, Multiplicative.ofAdd y ∈ S := by
    intro y hy
    have h1 : Multiplicative.ofAdd (hypVec P y) ∈ S := by simpa using hA y hy 1
    have h2 : Multiplicative.ofAdd (hypVec P 0) ∈ S := by
      simpa using hA 0 (Submodule.zero_mem _) 1
    have h3 := S.mul_mem (S.mul_mem h1 (S.inv_mem h2)) (S.inv_mem (hC (Q y)))
    have e : Multiplicative.ofAdd y = Multiplicative.ofAdd (hypVec P y) *
        (Multiplicative.ofAdd (hypVec P 0))⁻¹ * (Multiplicative.ofAdd (Q y • P.e))⁻¹ := by
      rw [← ofAdd_neg, ← ofAdd_neg, ← ofAdd_add, ← ofAdd_add]
      congr 1
      simp only [hypVec, map_zero, zero_smul, add_zero]
      abel
    rw [e]
    exact h3
  rw [eq_top_iff]
  intro z _
  have hz := P.eq_add_proj (Multiplicative.toAdd z)
  have hz' : z = Multiplicative.ofAdd (polar Q (Multiplicative.toAdd z) P.f • P.e) *
      Multiplicative.ofAdd (polar Q (Multiplicative.toAdd z) P.e • P.f) *
        Multiplicative.ofAdd (P.proj (Multiplicative.toAdd z)) := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    exact hz
  rw [hz']
  exact S.mul_mem (S.mul_mem (hC _) (hB _)) (hD _ (P.proj_mem_perp _))

end Span

end HS6

end CFSG.RankThree.GF2n.Stroth80
