module

public import CFSG.GF2Type.Smith1979.W4AsE11Surv
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open Subgroup
open scoped commutatorElement

theorem aut_eq_one_of_small {X : Type*} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {α : MulAut X} (hα : α ^ r = 1) {d : ℕ} (hX : Nat.card X = 2 ^ d)
    (hsmall : ∀ i, 0 < i → i ≤ d → ¬ r ∣ 2 ^ i - 1) : α = 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hP : IsPGroup r (Subgroup.zpowers α) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  have hmod := hP.card_modEq_card_fixedPoints (α := X)
  let C : Subgroup X := MonoidHom.eqLocus (α : X →* X) (MonoidHom.id X)
  have hfix : MulAction.fixedPoints (Subgroup.zpowers α) X = (C : Set X) := by
    ext x
    constructor
    · intro hx
      exact hx ⟨α, Subgroup.mem_zpowers α⟩
    · intro hx g
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
      have hxα : α x = x := hx
      have : ∀ k : ℤ, (α ^ k) x = x := by
        intro k
        induction k using Int.induction_on with
        | zero => simp
        | succ k ih => rw [zpow_add_one, MulAut.mul_apply, hxα, ih]
        | pred k ih =>
          rw [zpow_sub_one, MulAut.mul_apply]
          have : (α⁻¹) x = x := by
            rw [MulAut.inv_apply]
            exact (MulEquiv.symm_apply_eq α).mpr hxα.symm
          rw [this, ih]
      show (g : MulAut X) x = x
      rw [← hi]
      exact this i
  have hCcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) X) = Nat.card C := by
    rw [hfix]
    rfl
  rw [hCcard, hX] at hmod
  have hdvd : Nat.card C ∣ 2 ^ d := hX ▸ Subgroup.card_subgroup_dvd_card C
  obtain ⟨f, hf, hCf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hCf] at hmod
  obtain ⟨k, rfl⟩ : ∃ k, d = f + k := ⟨d - f, by omega⟩
  have hdiv : r ∣ 2 ^ (f + k) - 2 ^ f :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right f k))).mp hmod.symm
  have e : 2 ^ (f + k) - 2 ^ f = 2 ^ f * (2 ^ k - 1) := by rw [pow_add, Nat.mul_sub_one]
  rw [e] at hdiv
  have hcop : Nat.Coprime r (2 ^ f) :=
    Nat.Coprime.pow_right f ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hk1 : r ∣ 2 ^ k - 1 := hcop.dvd_of_dvd_mul_left hdiv
  have hk0 : k = 0 := by
    by_contra hk
    exact hsmall k (Nat.pos_of_ne_zero hk) (Nat.le_add_left k f) hk1
  subst hk0
  have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hCf, hX, Nat.add_zero])
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ C := hCtop ▸ Subgroup.mem_top x
  exact hx

theorem aut_pow_three_of_pow_nine {X : Type*} [CommGroup X] [Finite X] (h2 : ∀ x : X, x * x = 1)
    {d : ℕ} (hX : Nat.card X = 2 ^ d) (hd : d ≤ 5) {α : MulAut X} (hα : α ^ 9 = 1) :
    α ^ 3 = 1 := by
  have h2' : ∀ v : Additive X, (2 : ℕ) • v = 0 := fun v => by
    have := h2 (Additive.toMul v)
    apply Additive.toMul.injective
    simpa [two_nsmul, sq] using this
  letI : Module (ZMod 2) (Additive X) := AddCommGroup.zmodModule h2'
  haveI : Finite (Additive X) := inferInstanceAs (Finite X)
  haveI : Module.Finite (ZMod 2) (Additive X) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 2) (Additive X) ≤ 5 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
    rw [Nat.card_zmod, show Nat.card (Additive X) = Nat.card X from rfl, hX] at h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  let g : MulAut X →* Module.End (ZMod 2) (Additive X) :=
    { toFun := fun a =>
        AddMonoidHom.toZModLinearMap 2
          (MulEquiv.toAdditive a : Additive X ≃+ Additive X).toAddMonoidHom
      map_one' := LinearMap.ext fun v => rfl
      map_mul' := fun a b => LinearMap.ext fun v => rfl }
  have hg : ∀ (a : MulAut X) (x : X), g a (Additive.ofMul x) = Additive.ofMul (a x) :=
    fun a x => rfl
  have h9 : g α ^ 9 = 1 := by rw [← map_pow, hα, map_one]
  have h3 := CFSG.GF2Type.Smith1979.W4As.pow_three_eq_one_of_pow_nine_eq_one
    (V := Additive X) hfr h9
  rw [← map_pow] at h3
  refine MulEquiv.ext fun x => ?_
  have := congrArg (fun f : Module.End (ZMod 2) (Additive X) => f (Additive.ofMul x)) h3
  simp only [hg] at this
  exact Additive.ofMul.injective this

theorem normal_prod_eq_top {S : Type*} [Group S] [IsSimpleGroup S] (𝒩 : Subgroup (S × S))
    [𝒩.Normal] {a b : S} (ha : a ≠ 1) (hb : b ≠ 1) (hmemA : (a, (1 : S)) ∈ 𝒩)
    (hmemB : ((1 : S), b) ∈ 𝒩) : 𝒩 = ⊤ := by
  have h1 : 𝒩.comap (MonoidHom.inl S S) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (𝒩.comap (MonoidHom.inl S S)) with h | h
    · exfalso
      have : a ∈ 𝒩.comap (MonoidHom.inl S S) := hmemA
      rw [h] at this
      exact ha (Subgroup.mem_bot.mp this)
    · exact h
  have h2 : 𝒩.comap (MonoidHom.inr S S) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (𝒩.comap (MonoidHom.inr S S)) with h | h
    · exfalso
      have : b ∈ 𝒩.comap (MonoidHom.inr S S) := hmemB
      rw [h] at this
      exact hb (Subgroup.mem_bot.mp this)
    · exact h
  refine eq_top_iff.mpr fun x _ => ?_
  have hx1 : (x.1, (1 : S)) ∈ 𝒩 := by
    have : x.1 ∈ 𝒩.comap (MonoidHom.inl S S) := by rw [h1]; exact Subgroup.mem_top _
    exact this
  have hx2 : ((1 : S), x.2) ∈ 𝒩 := by
    have : x.2 ∈ 𝒩.comap (MonoidHom.inr S S) := by rw [h2]; exact Subgroup.mem_top _
    exact this
  have := 𝒩.mul_mem hx1 hx2
  simpa using this

theorem aut_trivial_of_small {Γ S X : Type*} [Group Γ] [Group S] [IsSimpleGroup S] [Finite S]
    [CommGroup X] [Finite X] (h2 : ∀ x : X, x * x = 1) (φ : Γ →* S × S)
    (hφ : Function.Surjective φ) (σ : Γ →* MulAut X) (hker : ∀ g, φ g = 1 → σ g = 1)
    {d : ℕ} (hX : Nat.card X = 2 ^ d)
    (hsmall : (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card S ∧
        ∀ i, 0 < i → i ≤ d → ¬ r ∣ 2 ^ i - 1) ∨ ((∃ s : S, orderOf s = 9) ∧ d ≤ 5)) :
    ∀ g, σ g = 1 := by
  have key : ∀ ι : S →* S × S, Function.Injective ι →
      ∃ a : S, a ≠ 1 ∧ ∃ g : Γ, φ g = ι a ∧ σ g = 1 := by
    intro ι hι
    rcases hsmall with ⟨r, hr, hr2, hrS, hsm⟩ | ⟨⟨s, hs9⟩, hd5⟩
    · haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' r hrS
      have hs1 : s ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hs
        exact hr.one_lt.ne hs
      obtain ⟨g, hg⟩ := hφ (ι s)
      refine ⟨s, hs1, g, hg, ?_⟩
      have hgr : σ g ^ r = 1 := by
        rw [← map_pow]
        apply hker
        rw [map_pow, hg, ← map_pow, ← hs, pow_orderOf_eq_one, map_one]
      exact aut_eq_one_of_small hr hr2 hgr hX hsm
    · obtain ⟨g, hg⟩ := hφ (ι s)
      have hg9 : σ g ^ 9 = 1 := by
        rw [← map_pow]
        apply hker
        rw [map_pow, hg, ← map_pow, ← hs9, pow_orderOf_eq_one, map_one]
      have hg3 := aut_pow_three_of_pow_nine h2 hX hd5 hg9
      refine ⟨s ^ 3, ?_, g ^ 3, by rw [map_pow, hg, map_pow], by rw [map_pow, hg3]⟩
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hs9] at this
      omega
  obtain ⟨a, ha, ga, hga, hσa⟩ := key (MonoidHom.inl S S) (fun x y h => (Prod.mk.inj h).1)
  obtain ⟨b, hb, gb, hgb, hσb⟩ := key (MonoidHom.inr S S) (fun x y h => (Prod.mk.inj h).2)
  haveI : ((Subgroup.map φ (σ.ker))).Normal := Subgroup.Normal.map inferInstance φ hφ
  have htop : Subgroup.map φ σ.ker = ⊤ := by
    refine normal_prod_eq_top _ ha hb ?_ ?_
    · exact ⟨ga, hσa, hga⟩
    · exact ⟨gb, hσb, hgb⟩
  intro g
  have hmem : φ g ∈ Subgroup.map φ σ.ker := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkg⟩ := hmem
  have hgk : φ (g * k⁻¹) = 1 := by rw [map_mul, map_inv, hkg, mul_inv_cancel]
  have := hker _ hgk
  rw [map_mul, map_inv] at this
  have hk' : σ k = 1 := hk
  rw [hk', inv_one, mul_one] at this
  exact this

section Quot

variable {Γ : Type*} [Group Γ]

abbrev Xq (N T : Subgroup Γ) [T.Normal] : Type _ := ↥N ⧸ T.subgroupOf N

variable {N T : Subgroup Γ} [N.Normal] [T.Normal]

theorem map_conjNormal_eq (g : Γ) :
    (T.subgroupOf N).map (MulAut.conjNormal g : MulAut ↥N).toMonoidHom = T.subgroupOf N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show ((MulAut.conjNormal g y : ↥N) : Γ) ∈ T
    rw [MulAut.conjNormal_apply]
    exact ‹T.Normal›.conj_mem _ hy g
  · intro hx
    refine ⟨(MulAut.conjNormal g).symm x, ?_, by simp⟩
    show (((MulAut.conjNormal g).symm x : ↥N) : Γ) ∈ T
    rw [MulAut.conjNormal_symm_apply]
    have := ‹T.Normal›.conj_mem _ hx g⁻¹
    simpa using this

theorem congr_conj_mk (g : Γ) (x : ↥N) :
    QuotientGroup.congr (T.subgroupOf N) (T.subgroupOf N) (MulAut.conjNormal g)
      (map_conjNormal_eq g) (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal g x) :=
  QuotientGroup.congr_mk _ _ _ _ _

noncomputable def actXq : Γ →* MulAut (Xq N T) where
  toFun g := QuotientGroup.congr (T.subgroupOf N) (T.subgroupOf N) (MulAut.conjNormal g)
    (map_conjNormal_eq g)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rw [congr_conj_mk]; simp
  map_mul' g h := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, congr_conj_mk, congr_conj_mk, congr_conj_mk]
      simp

theorem actXq_mk (g : Γ) (x : ↥N) :
    actXq (N := N) (T := T) g (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal g x) :=
  congr_conj_mk g x

end Quot

section Final

variable {Γ S : Type*} [Group Γ] [Group S] [IsSimpleGroup S] [Finite S]

theorem comm_mem_of_small (N T : Subgroup Γ) [N.Normal] [T.Normal]
    (hNN : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ T) (hN2 : ∀ x ∈ N, x ^ 2 ∈ T) [Finite ↥N]
    (φ : Γ →* S × S) (hφ : Function.Surjective φ) (hker : ∀ g, φ g = 1 → g ∈ N)
    {d : ℕ} (hX : Nat.card (Xq N T) = 2 ^ d)
    (hsmall : (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card S ∧
        ∀ i, 0 < i → i ≤ d → ¬ r ∣ 2 ^ i - 1) ∨ ((∃ s : S, orderOf s = 9) ∧ d ≤ 5)) :
    ∀ g : Γ, ∀ x ∈ N, ⁅g, x⁆ ∈ T := by
  classical
  have hcomm : ∀ a b : Xq N T, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        show (((a * b)⁻¹ * (b * a) : ↥N) : Γ) ∈ T
        have := hNN (b⁻¹ : ↥N) (b⁻¹ : ↥N).2 (a⁻¹ : ↥N) (a⁻¹ : ↥N).2
        simpa [commutatorElement_def, mul_assoc] using this
  letI : CommGroup (Xq N T) :=
    { (inferInstance : Group (Xq N T)) with mul_comm := hcomm }
  haveI : Finite (Xq N T) := inferInstance
  have h2 : ∀ x : Xq N T, x * x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      show ((x * x : ↥N) : Γ) ∈ T
      simpa [sq] using hN2 x x.2
  have hσ := aut_trivial_of_small (X := Xq N T) h2 φ hφ (actXq (N := N) (T := T))
    (fun g hg => by
      have hgN : g ∈ N := hker g hg
      ext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [actXq_mk, MulAut.one_apply, QuotientGroup.eq]
        show ((((MulAut.conjNormal g x)⁻¹ * x : ↥N)) : Γ) ∈ T
        have := hNN g hgN (x⁻¹ : ↥N) (x⁻¹ : ↥N).2
        simpa [commutatorElement_def, MulAut.conjNormal_apply, mul_assoc] using this)
    hX hsmall
  intro g x hx
  have h1 := congrArg (fun a : MulAut (Xq N T) => a (QuotientGroup.mk ⟨x, hx⟩)) (hσ g)
  simp only [actXq_mk, MulAut.one_apply, QuotientGroup.eq] at h1
  have h3 : ((((MulAut.conjNormal g ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩ : ↥N)) : Γ) ∈ T := h1
  have h3' : x⁻¹ * (g * x * g⁻¹) ∈ T := by
    have := T.inv_mem h3
    simpa [MulAut.conjNormal_apply, mul_assoc] using this
  have h4 := ‹T.Normal›.conj_mem _ h3' x
  have e : x * (x⁻¹ * (g * x * g⁻¹)) * x⁻¹ = ⁅g, x⁆ := by
    simp only [commutatorElement_def]; group
  rwa [e] at h4

end Final

section Stated

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank

theorem exists_orderOf_nine_statedSL (K : Type) [Field K] [Finite K] (hK : Nat.card K = 8) :
    ∃ s : StatedSL 2 K, orderOf s = 9 := by
  obtain ⟨A, hA⟩ := CFSG.GF2Type.Smith1979.W4As.exists_orderOf_eq_nine_sl2
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 3) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 3 (by decide)]
    rfl
  let e : K ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq hcard
  let f : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3) →*
      Matrix.SpecialLinearGroup (Fin 2) K := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hfinj : Function.Injective f := by
    intro a b h
    ext i j
    have h1 := congrArg
      (fun x : Matrix.SpecialLinearGroup (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K) i j) h
    have h2 : e.symm (a i j) = e.symm (b i j) := by
      simpa [f, Matrix.SpecialLinearGroup.map_apply_coe] using h1
    exact e.symm.injective h2
  refine ⟨specialLinearGroupEquivStatedSL 2 K (f A), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_injective f hfinj, hA]

theorem hsmall_statedSL (K : Type) [Field K] [Finite K] {e : ℕ} (hKe : Nat.card K = 2 ^ e)
    (he : 2 ≤ e) {d : ℕ} (hd : d + 2 ≤ 2 * e) :
    (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card (StatedSL 2 K) ∧
        ∀ i, 0 < i → i ≤ d → ¬ r ∣ 2 ^ i - 1) ∨
      ((∃ s : StatedSL 2 K, orderOf s = 9) ∧ d ≤ 5) := by
  by_cases h3 : e = 3
  · subst h3
    exact Or.inr ⟨exists_orderOf_nine_statedSL K (by rw [hKe]; norm_num), by omega⟩
  · left
    obtain ⟨p, hp, hpd, hpj⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor
      (k := 2 * e) (by omega) (by omega)
    refine ⟨p, hp, ?_, ?_, fun i hi hid => hpj i hi (by omega)⟩
    · rintro rfl
      have h2 : 2 ∣ 2 ^ (2 * e) - 1 := hpd
      have h4 : 2 ∣ 2 ^ (2 * e) := dvd_pow_self 2 (by omega)
      have h5 : 1 ≤ 2 ^ (2 * e) := Nat.one_le_two_pow
      omega
    · rw [card_statedSL_two, hKe]
      refine Dvd.dvd.mul_left ?_ _
      have : (2 ^ e) ^ 2 = 2 ^ (2 * e) := by rw [← pow_mul, mul_comm]
      rw [this]
      exact hpd

end Stated

end CFSG.RankThree.GF2n.Stroth80.HS9
