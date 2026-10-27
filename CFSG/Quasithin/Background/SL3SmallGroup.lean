module

public import CFSG.Quasithin.Background.SL3SmallNat
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.SL3Small

open CFSG.RankThree.PartOne.Quotient36 Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement

section Conj

variable {G : Type} [Group G] {Y R : Subgroup G} [hN : (R.subgroupOf Y).Normal] (hRY : R ≤ Y)

include hRY in
theorem conj_mem_of_normal (y : ↥Y) {r : G} (hr : r ∈ R) : (y : G) * r * (y : G)⁻¹ ∈ R := by
  have h := hN.conj_mem ⟨r, hRY hr⟩ (Subgroup.mem_subgroupOf.mpr hr) y
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

@[expose] def conjAut : ↥Y →* MulAut ↥R where
  toFun y :=
    { toFun := fun r => ⟨(y : G) * r * (y : G)⁻¹, conj_mem_of_normal hRY y r.2⟩
      invFun := fun r => ⟨(y : G)⁻¹ * r * y, by
        simpa using conj_mem_of_normal hRY y⁻¹ r.2⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext r
    simp
  map_mul' a b := by
    ext r
    simp [mul_assoc]

theorem coe_conjAut (y : ↥Y) (r : ↥R) :
    ((conjAut hRY y r : ↥R) : G) = (y : G) * r * (y : G)⁻¹ := rfl

end Conj

section Rep

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} [(R.subgroupOf Y).Normal]
  (hRY : R ≤ Y) [Fact (IsPGroup 2 ↥R)]

@[expose, reducible] noncomputable def conjAction : MulDistribMulAction ↥Y ↥R :=
  MulDistribMulAction.compHom ↥R (conjAut hRY)

@[expose] noncomputable def rhoY : Representation (ZMod 2) ↥Y (Additive (↥R ⧸ frattini ↥R)) :=
  letI := conjAction hRY
  frattiniRep (E := ↥Y) (X := ↥R) 2

theorem rhoY_mk (y : ↥Y) (r : ↥R) :
    rhoY hRY y (Additive.ofMul (r : ↥R ⧸ frattini ↥R)) =
      Additive.ofMul ((conjAut hRY y r : ↥R) : ↥R ⧸ frattini ↥R) := by
  let _ := conjAction hRY
  exact frattiniRep_apply_mk (E := ↥Y) (X := ↥R) 2 y r

theorem rhoY_eq_one_of_mem {y : ↥Y} (hy : (y : G) ∈ R) : rhoY hRY y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := (CFSG.GroupTheory.frattini_elementary_quotient
    (Fact.out : IsPGroup 2 ↥R)).2.1
  apply LinearMap.ext
  intro v
  induction v using Additive.rec with
  | ofMul x =>
    induction x using QuotientGroup.induction_on with
    | H r =>
      rw [rhoY_mk, Module.End.one_apply]
      congr 1
      have e : conjAut hRY y r = ⟨y, hy⟩ * r * (⟨y, hy⟩ : ↥R)⁻¹ := Subtype.ext rfl
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        mul_comm (((⟨y, hy⟩ : ↥R) : ↥R ⧸ frattini ↥R)), mul_assoc, mul_inv_cancel, mul_one]

end Rep

section Sigma

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} [(R.subgroupOf Y).Normal]
  (hRY : R ≤ Y) [Fact (IsPGroup 2 ↥R)] {F : Type} [Field F] [Fintype F] [CharP F 2] {m : ℕ}

@[expose] noncomputable def rhoQ :
    Representation (ZMod 2) (↥Y ⧸ R.subgroupOf Y) (Additive (↥R ⧸ frattini ↥R)) :=
  QuotientGroup.lift (R.subgroupOf Y) (rhoY hRY) (fun _y hy =>
    rhoY_eq_one_of_mem hRY (Subgroup.mem_subgroupOf.mp hy))

theorem rhoQ_mk (y : ↥Y) : rhoQ hRY (QuotientGroup.mk y) = rhoY hRY y := rfl

theorem mul_inv_mem_of_inv_mul_mem {H : Type} [Group H] {N : Subgroup H} [N.Normal] {a b : H}
    (h : a⁻¹ * b ∈ N) : b * a⁻¹ ∈ N := by
  have := ‹N.Normal›.conj_mem _ h b
  simpa [mul_assoc] using this

theorem exists_sigma (hF : Fintype.card F = 2 ^ m) (hm : 2 ≤ m)
    (hcard : Nat.card R ≤ 2 ^ (3 * m + 1)) (κ : SL(3, F) →* ↥Y ⧸ R.subgroupOf Y)
    (hκ : Function.Surjective κ) (hκ1 : ∃ t, κ t ≠ 1)
    (hfaith : ∀ y ∈ Y, (∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ (frattini ↥R).map R.subtype) → y ∈ R) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ σ : ↥R →* Multiplicative (Fin 3 → F),
      Function.Surjective σ ∧
      (∀ r, σ r = 1 → ∀ y : ↥Y, (conjAut hRY y r : ↥R) * r⁻¹ ∈ frattini ↥R) ∧
      (∀ r ∈ frattini ↥R, σ r = 1) ∧
      ∀ (g : SL(3, F)) (y : ↥Y), QuotientGroup.mk y = κ g → ∀ r,
        Multiplicative.toAdd (σ (conjAut hRY y r)) =
          ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (σ r) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := Additive (↥R ⧸ frattini ↥R)
  set ρ : Representation (ZMod 2) SL(3, F) V := (rhoQ hRY).comp κ with hρ
  have hρY : ∀ (g : SL(3, F)) (y : ↥Y), QuotientGroup.mk y = κ g → ρ g = rhoY hRY y :=
    fun g y hy => by rw [hρ, MonoidHom.comp_apply, ← hy, rhoQ_mk]
  have hdim : Module.finrank (ZMod 2) V ≤ 3 * m + 1 := by
    have hfin : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have h1 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have h2 : Nat.card V ≤ Nat.card ↥R := by
      show Nat.card (↥R ⧸ frattini ↥R) ≤ Nat.card ↥R
      exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
    rw [h1] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (h2.trans hcard)
  have hnt : ∃ g v, ρ g v ≠ v := by
    by_contra hne
    push Not at hne
    obtain ⟨t, ht⟩ := hκ1
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (κ t)
    have h1 : rhoY hRY y = 1 := by
      rw [← hρY t y hy]
      exact LinearMap.ext (hne t)
    have hyR : (y : G) ∈ R := by
      refine hfaith y y.2 fun r hr => ?_
      have h2 := congrArg (fun T => T (Additive.ofMul ((⟨r, hr⟩ : ↥R) : ↥R ⧸ frattini ↥R))) h1
      simp only [rhoY_mk, Module.End.one_apply] at h2
      have h3 := QuotientGroup.eq.mp (Additive.ofMul.injective h2)
      have h4 : (conjAut hRY y ⟨r, hr⟩ : ↥R) * (⟨r, hr⟩ : ↥R)⁻¹ ∈ frattini ↥R :=
        mul_inv_mem_of_inv_mul_mem (N := frattini ↥R) (by simpa using inv_mem h3)
      refine ⟨_, h4, ?_⟩
      simp [coe_conjAut]
    apply ht
    rw [← hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hyR
  obtain ⟨ψ, hψ, π, hπs, hπk, hπe⟩ := exists_natural_proj hF hm ρ hdim hnt
  let σ : ↥R →* Multiplicative (Fin 3 → F) :=
    { toFun := fun r => Multiplicative.ofAdd (π (Additive.ofMul (r : ↥R ⧸ frattini ↥R)))
      map_one' := by simp
      map_mul' := fun a b => by simp [QuotientGroup.mk_mul, ofMul_mul, map_add] }
  have hσ : ∀ r, Multiplicative.toAdd (σ r) = π (Additive.ofMul (r : ↥R ⧸ frattini ↥R)) :=
    fun r => rfl
  refine ⟨ψ, hψ, σ, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨v, hv⟩ := hπs (Multiplicative.toAdd x)
    induction v using Additive.rec with
    | ofMul q =>
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨r, by rw [← ofAdd_toAdd x, ← hv]; rfl⟩
  · intro r hr y
    obtain ⟨g, hg⟩ := hκ (QuotientGroup.mk y)
    have h0 : π (Additive.ofMul (r : ↥R ⧸ frattini ↥R)) = 0 := by
      rw [← hσ, hr, toAdd_one]
    have h1 := hπk _ h0 g
    rw [hρY g y hg.symm, rhoY_mk] at h1
    have h2 := QuotientGroup.eq.mp (Additive.ofMul.injective h1)
    exact mul_inv_mem_of_inv_mul_mem (N := frattini ↥R) (by simpa using inv_mem h2)
  · intro r hr
    have : ((r : ↥R ⧸ frattini ↥R)) = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    show Multiplicative.ofAdd (π (Additive.ofMul (r : ↥R ⧸ frattini ↥R))) = 1
    rw [this, ofMul_one, map_zero, ofAdd_zero]
  · intro g y hy r
    rw [hσ, hσ, ← rhoY_mk, ← hρY g y hy, hπe]

end Sigma

section Comm

variable {H : Type} [Group H]

theorem commutatorElement_mul_left' {a b c : H} (hz : ∀ x, ⁅b, c⁆ * x = x * ⁅b, c⁆) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  calc ⁅a * b, c⁆ = a * ⁅b, c⁆ * (c * a⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅b, c⁆ * a * (c * a⁻¹ * c⁻¹) := by rw [hz a]
    _ = ⁅b, c⁆ * ⁅a, c⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, c⁆ * ⁅b, c⁆ := hz _

theorem commutatorElement_mul_right' {a b c : H} (hz : ∀ x, ⁅c, b⁆ * x = x * ⁅c, b⁆) :
    ⁅c, a * b⁆ = ⁅c, a⁆ * ⁅c, b⁆ := by
  calc ⁅c, a * b⁆ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅c, a⁆ * (⁅c, b⁆ * a * a⁻¹) := by rw [← hz a]
    _ = ⁅c, a⁆ * ⁅c, b⁆ := by group

theorem commutatorElement_mul_central_left {a φ c : H} (hφ : ∀ x, φ * x = x * φ) :
    ⁅a * φ, c⁆ = ⁅a, c⁆ := by
  have h1 : φ * c * φ⁻¹ = c := by rw [hφ c, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅a * φ, c⁆ = a * (φ * c * φ⁻¹) * a⁻¹ * c⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, c⁆ := by rw [h1, commutatorElement_def]

theorem commutatorElement_mul_central_right {a φ c : H} (hφ : ∀ x, φ * x = x * φ) :
    ⁅c, a * φ⁆ = ⁅c, a⁆ := by
  have h1 : ⁅c, a * φ⁆ = ⁅a * φ, c⁆⁻¹ := (commutatorElement_inv _ _).symm
  rw [h1, commutatorElement_mul_central_left hφ, commutatorElement_inv]

end Comm

section Frattini

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} [(R.subgroupOf Y).Normal]
  (hRY : R ≤ Y) [Fact (IsPGroup 2 ↥R)] {F : Type} [Field F] [Fintype F] {m : ℕ}

theorem frattini_eq_bot (hF : Fintype.card F = 2 ^ m) (hm : 2 ≤ m)
    (hcard : Nat.card R ≤ 2 ^ (3 * m + 1)) (σ : ↥R →* Multiplicative (Fin 3 → F))
    (hσs : Function.Surjective σ) (hΦσ : ∀ r ∈ frattini ↥R, σ r = 1)
    (hinv : ∀ g : SL(3, F), ∃ y : ↥Y, ∀ r, Multiplicative.toAdd (σ (conjAut hRY y r)) =
      ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (σ r)) :
    frattini ↥R = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 ↥R := Fact.out
  obtain ⟨hchar, hqcomm, hqsq, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hR2
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one hF hm
  by_contra hne
  set Φ := frattini ↥R with hΦ
  let σ' : ↥R ⧸ Φ →* Multiplicative (Fin 3 → F) := QuotientGroup.lift Φ σ hΦσ
  have hσ's : Function.Surjective σ' := by
    intro x
    obtain ⟨r, hr⟩ := hσs x
    exact ⟨r, hr⟩
  have hcM : Nat.card (Multiplicative (Fin 3 → F)) = 2 ^ (3 * m) := by
    show Nat.card (Fin 3 → F) = _
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := F), hF, ← pow_mul, mul_comm]
  have hc1' := Nat.card_le_card_of_surjective _ hσ's
  rw [hcM] at hc1'
  have hc2 := Subgroup.card_eq_card_quotient_mul_card_subgroup Φ
  have hc3 : 1 < Nat.card Φ := (Subgroup.one_lt_card_iff_ne_bot Φ).mpr hne
  have hpos : 0 < 2 ^ (3 * m) := by positivity
  have hcΦ : Nat.card Φ = 2 := by
    have h4 : 2 ^ (3 * m + 1) = 2 * 2 ^ (3 * m) := by ring
    rw [hc2, h4] at hcard
    nlinarith
  have hcQ : Nat.card (↥R ⧸ Φ) ≤ 2 ^ (3 * m) := by
    have h4 : 2 ^ (3 * m + 1) = 2 * 2 ^ (3 * m) := by ring
    rw [hc2, h4, hcΦ] at hcard
    nlinarith
  have hσ'b := hσ's.bijective_of_nat_card_le (hcQ.trans hcM.symm.le)
  have hker : ∀ r, σ r = 1 → r ∈ Φ := fun r hr => by
    have h1 : σ' (r : ↥R ⧸ Φ) = σ' 1 := by rw [map_one]; exact hr
    exact (QuotientGroup.eq_one_iff r).mp (hσ'b.1 h1)
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ Φ, z ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.mpr fun z hz => (Subgroup.mem_bot).mpr (h z hz))
  have hΦ2 : ∀ φ ∈ Φ, φ = 1 ∨ φ = z₀ := by
    intro φ hφ
    obtain ⟨a, b, hab, hall⟩ := Nat.card_eq_two_iff.mp hcΦ
    have hmem : ∀ x : ↥Φ, x = a ∨ x = b := fun x => by
      have : x ∈ ({a, b} : Set ↥Φ) := by rw [hall]; trivial
      simpa using this
    by_cases h1 : φ = 1
    · exact Or.inl h1
    · right
      have e1 := hmem ⟨φ, hφ⟩
      have e2 := hmem ⟨z₀, hz₀⟩
      have e3 := hmem ⟨1, Φ.one_mem⟩
      have key : ∀ u v w : ↥Φ, (u = a ∨ u = b) → (v = a ∨ v = b) → (w = a ∨ w = b) →
          u ≠ w → v ≠ w → u = v := by
        intro u v w hu hv hw huw hvw
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
          first | rfl | exact absurd rfl huw | exact absurd rfl hvw
      have := key _ _ _ e1 e2 e3 (fun h => h1 (congrArg Subtype.val h))
        (fun h => hz₀1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  have hcentY : ∀ (y : ↥Y), ∀ φ ∈ Φ, conjAut hRY y φ = φ := by
    intro y φ hφ
    have hmem : conjAut hRY y φ ∈ Φ :=
      Subgroup.characteristic_iff_le_comap.mp hchar (conjAut hRY y) hφ
    rcases hΦ2 φ hφ with h0 | h0
    · rw [h0, map_one]
    · rw [h0] at hmem ⊢
      rcases hΦ2 _ hmem with h | h
      · exact absurd ((conjAut hRY y).injective (h.trans (map_one _).symm)) hz₀1
      · exact h
  have hcentR : ∀ φ ∈ Φ, ∀ a : ↥R, φ * a = a * φ := by
    intro φ hφ a
    have h1 := hcentY ⟨a, hRY a.2⟩ φ hφ
    have h2 : ((conjAut hRY ⟨a, hRY a.2⟩ φ : ↥R) : G) = a * φ * (a : G)⁻¹ := rfl
    have h3 : (a : G) * φ * (a : G)⁻¹ = φ := by rw [← h2, h1]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (φ : G) * a = (a : G) * φ * (a : G)⁻¹ * a := by rw [h3]
      _ = a * φ := by group
  have hcommΦ : ∀ a b : ↥R, ⁅a, b⁆ ∈ Φ := by
    intro a b
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      mul_comm (a : ↥R ⧸ Φ) (b : ↥R ⧸ Φ)]
    group
  have hsqΦ : ∀ a : ↥R, a ^ 2 ∈ Φ := by
    intro a
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hqsq _
  have hz2 : ∀ φ ∈ Φ, φ ^ 2 = 1 := by
    intro φ hφ
    rcases hΦ2 φ hφ with h | h
    · rw [h, one_pow]
    · rw [h]
      rcases hΦ2 _ (hsqΦ z₀) with h' | h'
      · exact h'
      · exact absurd (by rw [pow_two] at h'; exact mul_eq_left.mp h') hz₀1
  set ℓ : (Fin 3 → F) → ↥R := fun x => Function.surjInv hσs (Multiplicative.ofAdd x) with hℓdef
  have hℓ : ∀ x, σ (ℓ x) = Multiplicative.ofAdd x := fun x => Function.surjInv_eq hσs _
  have hdec : ∀ a b : ↥R, σ a = σ b → ∃ φ ∈ Φ, b = a * φ := by
    intro a b hab
    refine ⟨a⁻¹ * b, hker _ (by rw [map_mul, map_inv, hab, inv_mul_cancel]), by group⟩
  have hℓadd : ∀ x x', ∃ φ ∈ Φ, ℓ (x + x') = ℓ x * ℓ x' * φ := fun x x' =>
    hdec _ _ (by rw [map_mul, hℓ, hℓ, hℓ, ofAdd_add])
  have hℓinv : ∀ g : SL(3, F), ∃ y : ↥Y, ∀ x, ∃ φ ∈ Φ,
      ℓ (((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = conjAut hRY y (ℓ x) * φ := by
    intro g
    obtain ⟨y, hy⟩ := hinv g
    refine ⟨y, fun x => hdec _ _ ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hy, hℓ, hℓ]
    rfl
  set B : (Fin 3 → F) → (Fin 3 → F) → ↥R := fun x y => ⁅ℓ x, ℓ y⁆ with hBdef
  have hBc : ∀ x y, ∀ u : ↥R, B x y * u = u * B x y := fun x y u => hcentR _ (hcommΦ _ _) u
  have hB1 : ∀ x x' y, B (x + x') y = B x y * B x' y := by
    intro x x' y
    obtain ⟨φ, hφ, he⟩ := hℓadd x x'
    simp only [hBdef]
    rw [he, commutatorElement_mul_central_left (hcentR φ hφ),
      commutatorElement_mul_left' (hcentR _ (hcommΦ _ _))]
  have hB2 : ∀ x y y', B x (y + y') = B x y * B x y' := by
    intro x y y'
    obtain ⟨φ, hφ, he⟩ := hℓadd y y'
    simp only [hBdef]
    rw [he, commutatorElement_mul_central_right (hcentR φ hφ),
      commutatorElement_mul_right' (hcentR _ (hcommΦ _ _))]
  have hBinv : ∀ (g : SL(3, F)) x y, B (((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
      (((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) = B x y := by
    intro g x y
    obtain ⟨y₀, hy₀⟩ := hℓinv g
    obtain ⟨φ, hφ, he⟩ := hy₀ x
    obtain ⟨φ', hφ', he'⟩ := hy₀ y
    simp only [hBdef]
    rw [he, he', commutatorElement_mul_central_left (hcentR φ hφ),
      commutatorElement_mul_central_right (hcentR φ' hφ'), ← map_commutatorElement,
      hcentY y₀ _ (hcommΦ _ _)]
  have hB := eq_one_of_biadd_inv B hB1 hB2 hBinv hc0 hc1
  have hdecℓ : ∀ a : ↥R, ∃ φ ∈ Φ, a = ℓ (Multiplicative.toAdd (σ a)) * φ := fun a =>
    hdec _ _ (by rw [hℓ, ofAdd_toAdd])
  have hab : ∀ a b : ↥R, a * b = b * a := by
    intro a b
    obtain ⟨φ, hφ, ha⟩ := hdecℓ a
    obtain ⟨φ', hφ', hb⟩ := hdecℓ b
    have h1 : ⁅a, b⁆ = 1 := by
      rw [ha, hb, commutatorElement_mul_central_left (hcentR φ hφ),
        commutatorElement_mul_central_right (hcentR φ' hφ')]
      exact hB _ _
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  set sq : (Fin 3 → F) → ↥R := fun x => ℓ x ^ 2 with hsqdef
  have hpow3 : ∀ a b φ : ↥R, φ ∈ Φ → (a * b * φ) ^ 2 = a ^ 2 * b ^ 2 := by
    intro a b φ hφ
    rw [(Commute.mul_pow (hab (a * b) φ) 2), (Commute.mul_pow (hab a b) 2), hz2 φ hφ, mul_one]
  have hs1 : ∀ x x', sq (x + x') = sq x * sq x' := by
    intro x x'
    obtain ⟨φ, hφ, he⟩ := hℓadd x x'
    simp only [hsqdef]
    rw [he, hpow3 _ _ _ hφ]
  have hsinv : ∀ (g : SL(3, F)) x,
      sq (((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = sq x := by
    intro g x
    obtain ⟨y₀, hy₀⟩ := hℓinv g
    obtain ⟨φ, hφ, he⟩ := hy₀ x
    simp only [hsqdef]
    rw [he, (Commute.mul_pow (hab _ φ) 2), hz2 φ hφ, mul_one, ← map_pow,
      hcentY y₀ _ (hsqΦ _)]
  have hs := eq_one_of_add_inv sq hs1 hsinv
  have hexp : ∀ a : ↥R, a ^ 2 = 1 := by
    intro a
    obtain ⟨φ, hφ, ha⟩ := hdecℓ a
    rw [ha, (Commute.mul_pow (hab _ φ) 2), hz2 φ hφ, mul_one]
    exact hs _
  have : IsElementaryAbelian 2 ↥R :=
    { is_comm := ⟨hab⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  exact hne (frattini_eq_bot_of_isElementaryAbelian (p := 2))

end Frattini

section Main

variable {F : Type} [Field F]

theorem transvection_not_mem_center :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) ∉
      Subgroup.center SL(3, F) := by
  intro h
  have h1 := Subgroup.mem_center_iff.mp h
    (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F))
  have h2 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h1
  simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.single_apply, Matrix.one_apply] at h2

theorem exists_kappa {Q : Type} [Group Q]
    (hiso : Nonempty (Q ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∨
      Nonempty (Q ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    ∃ κ : SL(3, F) →* Q, Function.Surjective κ ∧ (∃ t, κ t ≠ 1) ∧
      ∀ g, κ g = 1 → g ∈ Subgroup.center SL(3, F) := by
  have ht := transvection_not_mem_center (F := F)
  rcases hiso with h | h
  · obtain ⟨e₀⟩ := h
    let e := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).trans e₀.symm
    refine ⟨e.toMonoidHom, e.surjective,
      ⟨SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F), fun h => ht ?_⟩,
      fun g hg => ?_⟩
    · have h' : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) = 1 :=
        e.injective (by rw [map_one]; exact h)
      rw [h']
      exact Subgroup.one_mem _
    · have hg' : g = 1 := e.injective (by rw [map_one]; exact hg)
      rw [hg']
      exact Subgroup.one_mem _
  · obtain ⟨e₀⟩ := h
    let e := (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).trans
      e₀.symm
    let κ : SL(3, F) →* Q :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(3, F)))
    have hκ : ∀ g, κ g = 1 → g ∈ Subgroup.center SL(3, F) := fun g hg => by
      have h1 : (QuotientGroup.mk' (Subgroup.center SL(3, F)) g) = 1 :=
        e.injective (by rw [map_one]; exact hg)
      exact (QuotientGroup.eq_one_iff g).mp h1
    refine ⟨κ, e.surjective.comp (QuotientGroup.mk'_surjective _),
      ⟨SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F),
        fun h => ht (hκ _ h)⟩, hκ⟩

end Main

end CFSG.Quasithin.SL3Small
