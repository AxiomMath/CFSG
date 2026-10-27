module

public import CFSG.Quasithin.H13.KGLieNat
public import CFSG.Quasithin.H13.KGLieSec

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup
open scoped Matrix

section Twist

variable {ι : Type} {F : Type} [Field F]

@[expose] noncomputable def mscal (k : Fˣ) :
    Multiplicative (Matrix ι ι F) ≃* Multiplicative (Matrix ι ι F) :=
  (DistribMulAction.toAddEquiv (Matrix ι ι F) k).toMultiplicative

theorem toAdd_mscal (k : Fˣ) (X : Multiplicative (Matrix ι ι F)) :
    Multiplicative.toAdd (mscal k X) = (k : F) • Multiplicative.toAdd X := rfl

theorem frobPow_smul (a : ℕ) (k : F) (X : Matrix ι ι F) :
    frobPow a (k • X) = k ^ 2 ^ a • frobPow a X := by
  ext i j
  simp [frobPow, mul_pow]

theorem mscal_mem_hermSub_iff [Fintype ι] [CharP F 2] (a : ℕ) {k : Fˣ} (hk : (k : F) ^ 2 ^ a = k)
    (X : Multiplicative (Matrix ι ι F)) :
    X ∈ hermSub a ι F ↔ mscal k X ∈ hermSub a ι F := by
  show (frobPow a (Multiplicative.toAdd X))ᵀ = Multiplicative.toAdd X ↔
    (frobPow a (Multiplicative.toAdd (mscal k X)))ᵀ = Multiplicative.toAdd (mscal k X)
  rw [toAdd_mscal, frobPow_smul, hk, Matrix.transpose_smul]
  exact (smul_right_injective _ k.ne_zero).eq_iff.symm

theorem mscal_twistAct [Fintype ι] [DecidableEq ι] (a : ℕ)
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι F)) (k : Fˣ) (γ : ↥Γ)
    (X : Multiplicative (Matrix ι ι F)) :
    mscal k (twistAct a Γ γ X) = twistAct a Γ γ (mscal k X) := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mscal, twistAct, toAdd_ofAdd]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem eq_of_mscal {X : Multiplicative (Matrix ι ι F)} (hX : X ≠ 1) {k k' : Fˣ}
    (h : mscal k X * (mscal k' X)⁻¹ = 1) : k = k' := by
  have h1 : mscal k X = mscal k' X := mul_inv_eq_one.1 h
  have h2 : (k : F) • Multiplicative.toAdd X = (k' : F) • Multiplicative.toAdd X := by
    rw [← toAdd_mscal, ← toAdd_mscal, h1]
  have hne : Multiplicative.toAdd X ≠ 0 := fun h0 => hX (Multiplicative.toAdd.injective h0)
  exact Units.ext (smul_left_injective F hne h2)

end Twist

section Count

variable {F : Type} [Field F] [Finite F]

theorem card_fixUnits_ge {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) :
    2 ^ a - 1 ≤ Nat.card {k : Fˣ // (k : F) ^ 2 ^ a = k} := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hog : orderOf g = 2 ^ a * 2 ^ a - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF, two_mul, pow_add]
  have hx1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hfac : 2 ^ a * 2 ^ a - 1 = (2 ^ a - 1) * (2 ^ a + 1) := by
    zify [hx1, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by positivity) :
      2 ^ a * 2 ^ a ≠ 0)]
    ring
  set h := g ^ (2 ^ a + 1) with hh
  have hoh : orderOf h = 2 ^ a - 1 := by
    rw [hh, orderOf_pow_of_dvd (by positivity) (by rw [hog, hfac]; exact dvd_mul_left _ _), hog,
      hfac, Nat.mul_div_cancel _ (by positivity)]
  have hfix : ∀ i : ℕ, (((h ^ i : Fˣ) : F)) ^ 2 ^ a = ((h ^ i : Fˣ) : F) := by
    intro i
    have h1 : (h ^ i) ^ (2 ^ a - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hoh, pow_orderOf_eq_one, one_pow]
    have h2 : (h ^ i) ^ 2 ^ a = h ^ i := by
      calc (h ^ i) ^ 2 ^ a = (h ^ i) ^ (2 ^ a - 1 + 1) := by rw [Nat.sub_add_cancel hx1]
        _ = h ^ i := by rw [pow_succ, h1, one_mul]
    rw [← Units.val_pow_eq_pow_val, h2]
  set f : Fin (2 ^ a - 1) → {k : Fˣ // (k : F) ^ 2 ^ a = k} := fun i => ⟨h ^ (i : ℕ), hfix i⟩
  have hfi : Function.Injective f := by
    intro i j hij
    have h1 : h ^ (i : ℕ) = h ^ (j : ℕ) := congrArg Subtype.val hij
    have := pow_injOn_Iio_orderOf (x := h) (by rw [hoh]; exact i.2) (by rw [hoh]; exact j.2) h1
    exact Fin.ext this
  have := Nat.card_le_card_of_injective f hfi
  rwa [Nat.card_fin] at this

end Count

section Rows

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_twist (hV2 : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)} {v : MulAut V}
    (hB4 : B4Hyp G L) (hc : A5.Cond1321 G L v) {ι : Type} [Fintype ι] [DecidableEq ι]
    {i₀ i₁ : ι} (hi : i₀ ≠ i₁) {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} (ha : 3 ≤ a)
    (hF : Nat.card F = 2 ^ (2 * a)) {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (h : (FFModel.twistTensor a Γ).Realizes L ⊤ ⊥) : False := by
  classical
  obtain ⟨π, hπ⟩ := h
  set J := {k : Fˣ // (k : F) ^ 2 ^ a = k} with hJ
  have hJ7 : 7 ≤ Nat.card J := by
    have h1 : 2 ^ a - 1 ≤ Nat.card J := card_fixUnits_ge hF
    have h2 := eight_le_two_pow ha
    omega
  obtain ⟨m, hmL, hinj, hcard⟩ := scalars_of_realizes hπ (fun k : J => mscal k.1)
    (fun k x => mscal_mem_hermSub_iff a k.2 x)
    (fun k x => by
      show x = 1 ↔ mscal k.1 x = 1
      exact (map_eq_one_iff _ (mscal k.1).injective).symm)
    (fun k γ x => mscal_twistAct a Γ k.1 γ x)
    (fun x _ hxk k k' hkk => Subtype.ext (eq_of_mscal (ι := ι) hxk hkk))
  refine false_of_cond_scalars hV2 hB4 hc (ι := J) hJ7 m hmL hinj ?_
  rw [hcard]
  show 16 < Nat.card (↥(hermSub a ι F) ⧸
    (⊥ : Subgroup (Multiplicative (Matrix ι ι F))).subgroupOf (hermSub a ι F))
  rw [Subgroup.bot_subgroupOf, Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  have hK8 : 8 ≤ Nat.card {x : F // x ^ 2 ^ a = x} := by
    have hinj' : Function.Injective (fun c : Option J => match c with
        | none => (⟨0, by simp⟩ : {x : F // x ^ 2 ^ a = x})
        | some k => ⟨(k.1 : F), k.2⟩) := by
      rintro (_ | k) (_ | k') hkk
      · rfl
      · exfalso
        exact k'.1.ne_zero (congrArg Subtype.val hkk).symm
      · exfalso
        exact k.1.ne_zero (congrArg Subtype.val hkk)
      · congr 1
        exact Subtype.ext (Units.ext (congrArg Subtype.val hkk))
    have := Nat.card_le_card_of_injective _ hinj'
    rw [Nat.card_congr (Equiv.optionEquivSumPUnit J), Nat.card_sum] at this
    have hp : Nat.card PUnit.{1} = 1 := Nat.card_unique
    omega
  set f : {x : F // x ^ 2 ^ a = x} × {x : F // x ^ 2 ^ a = x} → ↥(hermSub a ι F) := fun p =>
    ⟨Multiplicative.ofAdd (Matrix.diagonal fun i => if i = i₀ then p.1.1 else
      if i = i₁ then p.2.1 else 0), by
      show (frobPow a _)ᵀ = _
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases h0 : i = i₀
        · simp [frobPow, Matrix.diagonal, h0, p.1.2]
        · by_cases h1 : i = i₁
          · simp [frobPow, Matrix.diagonal, h1, Ne.symm hi, p.2.2]
          · simp [frobPow, Matrix.diagonal, h0, h1]
      · simp [frobPow, Matrix.diagonal, hij, Ne.symm hij]⟩ with hf
  have hfi : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
    have hm := congrArg (fun z : ↥(hermSub a ι F) =>
      Multiplicative.toAdd (z : Multiplicative (Matrix ι ι F))) hxy
    have h0 := congrFun (congrFun hm i₀) i₀
    have h1 := congrFun (congrFun hm i₁) i₁
    simp [hf, Matrix.diagonal, Ne.symm hi] at h0 h1
    exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)
  have hle := Nat.card_le_card_of_injective f hfi
  rw [Nat.card_prod] at hle
  calc 16 < 8 * 8 := by norm_num
    _ ≤ Nat.card {x : F // x ^ 2 ^ a = x} * Nat.card {x : F // x ^ 2 ^ a = x} :=
      Nat.mul_le_mul hK8 hK8
    _ ≤ _ := hle

theorem factLieOrthRow1321_holds : A5.FactLieOrthRow1321 := by
  intro V _ _ hV2 G L v hB4 hc m hm h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  exact false_of_twist hV2 hB4 hc (i₀ := (0 : Fin 2)) (i₁ := 1) (by decide) hm hF hr

theorem factLieNineRow1321_holds : A5.FactLieNineRow1321 := by
  intro V _ _ hV2 G L v hB4 hc m hm h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  exact false_of_twist hV2 hB4 hc (i₀ := (0 : Fin 3)) (i₁ := 1) (by decide) hm hF hr

theorem factLieTwistRow1321_holds : A5.FactLieTwistRow1321 := by
  intro V _ _ hV2 G L v hB4 hc a ha h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  exact false_of_twist hV2 hB4 hc (i₀ := (Sum.inl 0 : Fin 2 ⊕ Fin 2)) (i₁ := Sum.inl 1)
    (by decide) ha hF hr

end Rows

end CFSG.Quasithin.H13.KGLie
