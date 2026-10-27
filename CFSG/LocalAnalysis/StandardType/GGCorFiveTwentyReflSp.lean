module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut fieldSp fieldAut_proj
  coe_fieldSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace ReflSp

variable {K : Type} [Field K] {m : ℕ}

@[expose] def fullSwap : Equiv.Perm (Fin m ⊕ Fin m) :=
  Equiv.sumComm (Fin m) (Fin m)

theorem largeEvenSpForm_fullSwap [CharP K 2] (x y : Fin m ⊕ Fin m) :
    LargeEvenSpForm K m (fullSwap x) (fullSwap y) = LargeEvenSpForm K m x y := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  rw [largeEvenSpForm_apply, largeEvenSpForm_apply]
  rcases x with a | a <;> rcases y with b | b <;> simp [fullSwap, hneg]

@[expose] noncomputable def fullSwapSp [CharP K 2] : LargeEvenSpGroup K m :=
  ⟨TauCeti.permutationGL fullSwap, permutationGL_mem_sp _ largeEvenSpForm_fullSwap⟩

theorem fullSwapSp_coe [CharP K 2] :
    ((fullSwapSp : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) =
      TauCeti.permutationGL fullSwap :=
  rfl

theorem pairedUnits_comp_fullSwap (u : Fin m → Kˣ) :
    pairedUnits u ∘ fullSwap = pairedUnits u⁻¹ := by
  funext x
  rcases x with a | a <;> simp [pairedUnits, fullSwap]

theorem permutationGL_fullSwap_conj (d : Fin m ⊕ Fin m → Kˣ) :
    TauCeti.permutationGL (k := K) fullSwap * TauCeti.diagGL d *
        (TauCeti.permutationGL (k := K) fullSwap)⁻¹ = TauCeti.diagGL (d ∘ fullSwap) := by
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (TauCeti.permutationGL (k := K) fullSwap)
    fullSwap⁻¹ (TauCeti.permutationGL_coe _), mul_inv_cancel_right]
  congr 2

theorem fullSwap_conj_spTorus [CharP K 2] {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (f : Fin m → Multiplicative (ZMod p)) :
    LargeEvenProjMk _ (fullSwapSp (K := K) (m := m)) * spTorus hζ f *
        (LargeEvenProjMk _ (fullSwapSp (K := K) (m := m)))⁻¹ = (spTorus hζ f)⁻¹ := by
  rw [← map_inv (spTorus (m := m) hζ) f, spTorus, MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, fullSwapSp_coe, spTorusSp_coe,
    spTorusSp_coe, spTorusGL_apply, spTorusGL_apply, permutationGL_fullSwap_conj,
    pairedUnits_comp_fullSwap]
  congr 2
  funext j
  simp

theorem exists_ringEquiv_eq_pow {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ}
    (hζo : orderOf ζ = p) : ∃ c < p, σ (ζ : K) = (ζ : K) ^ c := by
  have hprim : IsPrimitiveRoot (ζ : K) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζo]
    exact IsPrimitiveRoot.orderOf ζ
  have h1 : (σ (ζ : K)) ^ p = 1 := by rw [← map_pow, hprim.pow_eq_one, map_one]
  obtain ⟨c, hc, hc'⟩ := hprim.eq_pow_of_pow_eq_one h1
  exact ⟨c, hc, hc'.symm⟩

theorem ringEquiv_units_pow (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hc : σ (ζ : K) = (ζ : K) ^ c)
    (k : ℕ) : σ ((ζ ^ k : Kˣ) : K) = ((ζ ^ k : Kˣ) : K) ^ c := by
  rw [Units.val_pow_eq_pow_val, map_pow, hc, ← pow_mul, ← pow_mul, mul_comm]

theorem ringEquiv_units_inv_pow (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hc : σ (ζ : K) = (ζ : K) ^ c)
    (k : ℕ) : σ (((ζ ^ k)⁻¹ : Kˣ) : K) = (((ζ ^ k)⁻¹ : Kˣ) : K) ^ c := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, ringEquiv_units_pow σ hc, inv_pow]

theorem fieldSp_spTorusSp {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hζ : ζ ^ p = 1)
    (hc : σ (ζ : K) = (ζ : K) ^ c) (f : Fin m → Multiplicative (ZMod p)) :
    fieldSp m K σ (spTorusSp hζ f) = spTorusSp hζ f ^ c := by
  apply Subtype.ext
  apply Units.ext
  change ((spTorusGL hζ f : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ =
    (((spTorusSp hζ f ^ c : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, spTorusSp_coe, spTorusGL_apply,
    TauCeti.diagGL_coe, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_pow]
  congr 1
  funext x
  rcases x with i | i
  · simp only [Pi.pow_apply, pairedUnits, Sum.elim_inl, zmodPowHom_apply]
    exact ringEquiv_units_pow σ hc _
  · simp only [Pi.pow_apply, pairedUnits, Sum.elim_inr, zmodPowHom_apply]
    exact ringEquiv_units_inv_pow σ hc _

theorem fieldAut_spTorus {p : ℕ} [NeZero p] (σ : K ≃+* K) {ζ : Kˣ} {c : ℕ} (hζ : ζ ^ p = 1)
    (hc : σ (ζ : K) = (ζ : K) ^ c) (f : Fin m → Multiplicative (ZMod p)) :
    (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) (spTorus hζ f) =
      spTorus hζ f ^ c := by
  rw [spTorus, MonoidHom.comp_apply, ← map_pow]
  exact (fieldAut_proj (r := m) (K := K) σ (spTorusSp hζ f)).trans
    (congrArg (proj m K) (fieldSp_spTorusSp σ hζ hc f))

theorem exists_ne_zero_col {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K) (x : ι) :
    ∃ y, (g : Matrix ι ι K) y x ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := congrFun (congrFun g.inv_mul x) x
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp [h] at h1

theorem zmodPowHom_injective {p : ℕ} [NeZero p] {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (hζo : orderOf ζ = p) : Function.Injective (zmodPowHom hζ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  exact (zmodPowHom_eq_one_iff hζ hζo).mp ha

theorem pairedUnits_eq_of_mul_eq {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) {g : GL (Fin m ⊕ Fin m) K}
    {f f' : Fin m → Multiplicative (ZMod p)} (h : g * spTorusGL hζ f = spTorusGL hζ f' * g)
    {x y : Fin m ⊕ Fin m} (hxy : (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x ≠ 0) :
    pairedUnits (fun i => zmodPowHom hζ (f i)) x =
      pairedUnits (fun i => zmodPowHom hζ (f' i)) y := by
  have e := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) y x) h
  simp only [Units.val_mul, spTorusGL_apply, TauCeti.diagGL_coe, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at e
  apply Units.ext
  rw [mul_comm] at e
  exact mul_right_cancel₀ hxy e

theorem exists_monomial_data {p : ℕ} [NeZero p] {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (g : GL (Fin m ⊕ Fin m) K) :
    ∃ (j : Fin m → Fin m) (ε : Fin m → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f' : Fin m → Multiplicative (ZMod p), g * spTorusGL hζ f = spTorusGL hζ f' * g →
        ∀ i, Multiplicative.toAdd (f' (j i)) = ε i * Multiplicative.toAdd (f i) := by
  have key : ∀ i : Fin m, ∃ j : Fin m, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
      ∀ f f' : Fin m → Multiplicative (ZMod p), g * spTorusGL hζ f = spTorusGL hζ f' * g →
        Multiplicative.toAdd (f' j) = ε * Multiplicative.toAdd (f i) := by
    intro i
    obtain ⟨y, hy⟩ := exists_ne_zero_col g (Sum.inl i)
    rcases y with j | j
    · refine ⟨j, 1, Or.inl rfl, fun f f' h => ?_⟩
      have e := pairedUnits_eq_of_mul_eq hζ h hy
      simp only [pairedUnits, Sum.elim_inl] at e
      rw [one_mul, zmodPowHom_injective hζ hζo e]
    · refine ⟨j, -1, Or.inr rfl, fun f f' h => ?_⟩
      have e := pairedUnits_eq_of_mul_eq hζ h hy
      simp only [pairedUnits, Sum.elim_inl, Sum.elim_inr] at e
      rw [← map_inv] at e
      rw [zmodPowHom_injective hζ hζo e, toAdd_inv, neg_one_mul, neg_neg]
  choose j ε hε hj using key
  exact ⟨j, ε, hε, fun f f' h i => hj i f f' h⟩

theorem eq_of_fixed_pair {p : ℕ} (hp : p.Prime) {j : Fin m → Fin m} {ε : Fin m → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) {c : ZMod p} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hc2 : c ≠ -1)
    {a b : Fin m} {f : Fin m → ZMod p} (hf0 : f ≠ 0)
    (hsupp : ∀ i, i ≠ a → i ≠ b → f i = 0) (hf : ∀ i, f (j i) = ε i * c * f i) : j a = b := by
  have := Fact.mk hp
  have key : ∀ i, f i ≠ 0 → f (j i) ≠ 0 ∧ j i ≠ i ∧ (j i = a ∨ j i = b) := by
    intro i hi
    have hε0 : ε i ≠ 0 := by
      rcases hε i with h | h <;> rw [h]
      · exact one_ne_zero
      · exact neg_ne_zero.mpr one_ne_zero
    have hji : f (j i) ≠ 0 := by
      rw [hf]
      exact mul_ne_zero (mul_ne_zero hε0 hc0) hi
    refine ⟨hji, fun hii => ?_, ?_⟩
    · have h2 : (ε i * c - 1) * f i = 0 := by
        have h3 := hf i
        rw [hii] at h3
        linear_combination -h3
      have h3 : ε i * c = 1 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hi
      rcases hε i with h | h <;> rw [h] at h3
      · exact hc1 (by linear_combination h3)
      · exact hc2 (by linear_combination -h3)
    · by_contra hne
      push Not at hne
      exact hji (hsupp _ hne.1 hne.2)
  by_cases ha : f a = 0
  · exfalso
    have hb : f b ≠ 0 := by
      intro hb
      apply hf0
      funext i
      by_cases hia : i = a
      · rw [hia]
        exact ha
      by_cases hib : i = b
      · rw [hib]
        exact hb
      exact hsupp i hia hib
    obtain ⟨h1, h2, h3⟩ := key b hb
    have hjb : j b = a := h3.resolve_right h2
    exact h1 (by rw [hjb]; exact ha)
  · obtain ⟨-, h2, h3⟩ := key a ha
    exact h3.resolve_left h2

section Finite

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_orderOf_eq {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p := by
  have := Fact.mk hp
  exact exists_orderOf_eq_of_dvd hpq

theorem exists_eq_conj_fieldAut (hm3 : 3 ≤ m) (β' : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) :
    ∃ (s : LargeEvenProj (LargeEvenSpGroup K m))
      (φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))),
      (∃ σ : K ≃+* K, φ = fieldAut m K σ) ∧ ∀ y, β' y = s * φ y * s⁻¹ := by
  obtain ⟨_, ⟨s, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩ := AutPSp.exists_mul_compl (K := K) hm3 β'
  exact ⟨s, fieldAut m K σ, ⟨σ, rfl⟩, fun y => rfl⟩

theorem exists_conj_spTorus [NeZero m] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {E : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hE : IsElemAbelian p E)
    (hcard : p ^ m ≤ Nat.card E) :
    ∃ x : LargeEvenProj (LargeEvenSpGroup K m), (∀ f, x * spTorus hζ f * x⁻¹ ∈ E) ∧
      ∀ e ∈ E, ∃ f, x * spTorus hζ f * x⁻¹ = e := by
  have := Fact.mk hp
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Subgroup (LargeEvenSpGroup K m),
      E₁ = E.comap (LargeEvenProjMk _) := ⟨_, rfl⟩
  have hmemE₁ : ∀ g, g ∈ E₁ ↔ LargeEvenProjMk _ g ∈ E := fun g => by
    rw [hE₁]
    rfl
  obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Subgroup (GL (Fin m ⊕ Fin m) K),
      E₂ = E₁.map (LargeEvenSpGroup K m).subtype := ⟨_, rfl⟩
  have hE₁ab : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hπi ?_)⟩⟩, fun a ha => hπi ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE ((hmemE₁ _).mp a.2) ((hmemE₁ _).mp b.2)
    · rw [map_pow, map_one]
      exact hE.2 _ ((hmemE₁ _).mp ha)
  have hcard₁ : Nat.card E₁ = Nat.card E := by
    have h1 : E₁.map (LargeEvenProjMk _) = E := by
      rw [hE₁]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) E
    rw [Nat.card_congr (E₁.equivMapOfInjective _ hπi).toEquiv, h1]
  have hcard₂ : Nat.card E₂ = Nat.card E := by
    rw [hE₂]
    exact (Nat.card_congr (E₁.equivMapOfInjective _
      (LargeEvenSpGroup K m).subtype_injective).toEquiv).symm.trans hcard₁
  obtain ⟨P, hP, hPE⟩ := exists_conj_eq_range_spTorusGL (m := m) (E := E₂) hp2
    (natCast_ne_zero_of_charTwo hp hp2) hζo hζ (by rw [hE₂]; exact Subgroup.map_subtype_le E₁)
    (by rw [hE₂]; exact TableB.isElemAbelian_map hE₁ab _) (by rw [hcard₂]; exact hcard)
  obtain ⟨P', hP'⟩ : ∃ P' : LargeEvenSpGroup K m, (P' : GL (Fin m ⊕ Fin m) K) = P :=
    ⟨⟨P, hP⟩, rfl⟩
  have hconj : ∀ f, LargeEvenProjMk _ P' * spTorus hζ f * (LargeEvenProjMk _ P')⁻¹ =
      LargeEvenProjMk _ (P' * spTorusSp hζ f * P'⁻¹) := fun f => by
    rw [map_mul, map_mul, map_inv]
    rfl
  refine ⟨LargeEvenProjMk _ P', fun f => ?_, fun e he => ?_⟩
  · have h1 : spTorusGL hζ f ∈ E₂.map (MulAut.conj P⁻¹).toMonoidHom := by
      rw [hPE]
      exact ⟨f, rfl⟩
    obtain ⟨g, hg₂, hg⟩ := h1
    rw [hE₂] at hg₂
    obtain ⟨g₁, hg₁, rfl⟩ := hg₂
    have h2 : P' * spTorusSp hζ f * P'⁻¹ = g₁ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe, hP', ← hg]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype, inv_inv]
      group
    rw [hconj, h2]
    exact (hmemE₁ g₁).mp hg₁
  · obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective _ e
    have hg₁ : g₁ ∈ E₁ := (hmemE₁ g₁).mpr he
    have h1 : (MulAut.conj P⁻¹).toMonoidHom (g₁ : GL (Fin m ⊕ Fin m) K) ∈
        E₂.map (MulAut.conj P⁻¹).toMonoidHom := by
      refine ⟨g₁, ?_, rfl⟩
      rw [hE₂]
      exact ⟨g₁, hg₁, rfl⟩
    rw [hPE] at h1
    obtain ⟨f, hf⟩ := h1
    refine ⟨f, ?_⟩
    rw [hconj]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe, hf, hP']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

end Finite

theorem spTorus_hinv [CharP K 2] {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) (i j : Fin m) :
    ∃ w : LargeEvenProj (LargeEvenSpGroup K m), w * torusBasis (spTorus hζ) i * w⁻¹ =
      (torusBasis (spTorus hζ) i)⁻¹ ∧
      (j ≠ i → w * torusBasis (spTorus hζ) j * w⁻¹ = torusBasis (spTorus hζ) j) := by
  refine ⟨LargeEvenProjMk _ (spSwapSp i), ?_, fun hji => ?_⟩
  · rw [torusBasis, spSwap_conj_spTorus, ← map_inv, ← Pi.mulSingle_inv]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx
      simp
    · simp [Function.update_of_ne hx, Pi.mulSingle_eq_of_ne hx]
  · rw [torusBasis, spSwap_conj_spTorus]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [Function.update_self, Pi.mulSingle_eq_of_ne (Ne.symm hji)]
      exact (inv_one : (1 : Multiplicative (ZMod p))⁻¹ = 1)
    · simp [Function.update_of_ne hx]

theorem exists_conj_of_pseudoRefl [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hm3 : 3 ≤ m)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (x : LargeEvenProj (LargeEvenSpGroup K m))
    {E : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} [Finite E]
    (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hτE : ∀ f, x * spTorus hζ f * x⁻¹ ∈ E)
    (hEτ : ∀ e ∈ E, ∃ f, x * spTorus hζ f * x⁻¹ = e)
    {β' : MulAut (LargeEvenProj (LargeEvenSpGroup K m))} (hβE : ∀ e ∈ E, β' e ∈ E)
    (hfix : Nat.card {e : E // β' e = e} * p = Nat.card E) :
    ∃ w, ∀ e ∈ E, w * e * w⁻¹ = β' e := by
  have : NeZero m := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hπi : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  obtain ⟨s, φ, ⟨σ, hφ⟩, hβ⟩ := exists_eq_conj_fieldAut hm3 β'
  obtain ⟨c, hcp, hc⟩ := exists_ringEquiv_eq_pow σ hζo
  have hφt : ∀ f, φ (spTorus hζ f) = spTorus hζ f ^ c := fun f => by
    rw [hφ]
    exact fieldAut_spTorus σ hζ hc f
  have hform : ∀ f, β' (x * spTorus hζ f * x⁻¹) =
      (s * φ x * x⁻¹) * (x * spTorus hζ f * x⁻¹) ^ c * (s * φ x * x⁻¹)⁻¹ := by
    intro f
    rw [hβ, map_mul, map_mul, map_inv, hφt, conj_pow]
    group
  have hpowp : ∀ f, (x * spTorus hζ f * x⁻¹) ^ p = 1 := fun f => by
    rw [conj_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, mul_one, mul_inv_cancel]
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · interval_cases c
    ·
      exfalso
      rw [pow_zero] at hc
      have h1 : (ζ : K) = 1 := σ.injective (by rw [hc, map_one])
      have h2 : ζ = 1 := Units.ext (by rw [h1, Units.val_one])
      rw [h2, orderOf_one] at hζo
      exact hp.one_lt.ne hζo
    ·
      refine ⟨s * φ x * x⁻¹, fun e he => ?_⟩
      obtain ⟨f, rfl⟩ := hEτ e he
      rw [hform, pow_one]
  by_cases hcp1 : c = p - 1
  ·
    subst hcp1
    refine ⟨(s * φ x * x⁻¹) * (x * LargeEvenProjMk _ fullSwapSp * x⁻¹), fun e he => ?_⟩
    obtain ⟨f, rfl⟩ := hEτ e he
    have hinv : (x * spTorus hζ f * x⁻¹) ^ (p - 1) = (x * spTorus hζ f * x⁻¹)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hpowp]
    rw [hform, hinv]
    have hs₀ := fullSwap_conj_spTorus (K := K) (m := m) hζ f
    calc (s * φ x * x⁻¹) * (x * LargeEvenProjMk _ fullSwapSp * x⁻¹) * (x * spTorus hζ f * x⁻¹) *
          ((s * φ x * x⁻¹) * (x * LargeEvenProjMk _ fullSwapSp * x⁻¹))⁻¹ =
          (s * φ x * x⁻¹) * (x * (LargeEvenProjMk _ fullSwapSp * spTorus hζ f *
            (LargeEvenProjMk _ fullSwapSp)⁻¹) * x⁻¹) * (s * φ x * x⁻¹)⁻¹ := by group
      _ = (s * φ x * x⁻¹) * (x * spTorus hζ f * x⁻¹)⁻¹ * (s * φ x * x⁻¹)⁻¹ := by
          rw [hs₀]
          group
  exfalso
  have hcz0 : (c : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hcz1 : (c : ZMod p) ≠ 1 := by
    intro h
    have h' : ((c - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (by omega), h, Nat.cast_one, sub_self]
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    have := Nat.le_of_dvd (by omega) h'
    omega
  have hcz2 : (c : ZMod p) ≠ -1 := by
    intro h
    have h' : ((c + 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_add, h, Nat.cast_one, neg_add_cancel]
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    have := Nat.le_of_dvd (by omega) h'
    omega
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin m ⊕ Fin m) K).subgroupOf (LargeEvenSpGroup K m))
    (x⁻¹ * (s * φ x * x⁻¹) * x)
  obtain ⟨j, ε, hε, hj⟩ := exists_monomial_data hζo hζ (g₀ : GL (Fin m ⊕ Fin m) K)
  have hpair : ∀ a b : Fin m, a ≠ b → j a = b := by
    intro a b hab
    obtain ⟨f, hf1, hfs, hffix⟩ := ReflInner.exists_fixed_of_pseudoRefl hp.one_lt hEc hβE hfix
      ((MulAut.conj x).toMonoidHom.comp (spTorus hζ)) hτE hab
    change β' (x * spTorus hζ f * x⁻¹) = x * spTorus hζ f * x⁻¹ at hffix
    rw [hform, conj_pow] at hffix
    have h1 : (x⁻¹ * (s * φ x * x⁻¹) * x) * spTorus hζ (f ^ c) *
        (x⁻¹ * (s * φ x * x⁻¹) * x)⁻¹ = spTorus hζ f := by
      rw [map_pow]
      calc (x⁻¹ * (s * φ x * x⁻¹) * x) * spTorus hζ f ^ c * (x⁻¹ * (s * φ x * x⁻¹) * x)⁻¹ =
            x⁻¹ * ((s * φ x * x⁻¹) * (x * spTorus hζ f ^ c * x⁻¹) * (s * φ x * x⁻¹)⁻¹) * x := by
            group
        _ = x⁻¹ * (x * spTorus hζ f * x⁻¹) * x := by rw [hffix]
        _ = spTorus hζ f := by group
    have h2 : g₀ * spTorusSp hζ (f ^ c) * g₀⁻¹ = spTorusSp hζ f := by
      apply hπi
      rw [map_mul, map_mul, map_inv]
      exact (congrArg (fun y => y * spTorus hζ (f ^ c) * y⁻¹) hg₀).trans h1
    have h3 : (g₀ : GL (Fin m ⊕ Fin m) K) * spTorusGL hζ (f ^ c) =
        spTorusGL hζ f * (g₀ : GL (Fin m ⊕ Fin m) K) := by
      have h4 := congrArg (fun y : LargeEvenSpGroup K m => (y : GL (Fin m ⊕ Fin m) K)) h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe] at h4
      rw [← h4]
      group
    have h5 := hj _ _ h3
    refine eq_of_fixed_pair hp hε hcz0 hcz1 hcz2 (f := fun i => Multiplicative.toAdd (f i))
      ?_ ?_ ?_
    · intro h0
      apply hf1
      funext i
      have h6 : Multiplicative.toAdd (f i) = 0 := congrFun h0 i
      rw [Pi.one_apply, ← ofAdd_toAdd (f i), h6, ofAdd_zero]
    · intro i hia hib
      simp only [hfs i hia hib, toAdd_one]
    · intro i
      rw [h5 i, Pi.pow_apply, toAdd_pow, nsmul_eq_mul, mul_assoc]
  have h01 := hpair ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
  have h02 := hpair ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp)
  rw [h01] at h02
  simp at h02

theorem ggTorusReflCore_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGTorusReflCore p m (LargeEvenProj (LargeEvenSpGroup K m)) := by
  intro E hE hr h3 β' hβE _ hfix
  have : NeZero m := ⟨by omega⟩
  have hEm : Nat.card E ≤ p ^ m := card_le_of_isElemAbelian_spProj hp hp2 hpq hE
  have hm3 : 3 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hEm)
  have : Finite E := Nat.finite_of_card_ne_zero (by
    have := Nat.one_le_pow 3 p hp.pos
    omega)
  obtain ⟨ζ, hζo⟩ := exists_orderOf_eq (K := K) hp hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨x, hτE, hEτ⟩ := exists_conj_spTorus hp hp2 hζo hζ hE hr
  exact ⟨m, (MulAut.conj x).toMonoidHom.comp (spTorus hζ), fun e he => hEτ e he,
    ReflInner.hinv_conj_comp _ (spTorus_hinv hζ) x,
    exists_conj_of_pseudoRefl hp hm3 hζo hζ x
      (fun e he e' he' => TableB.IsElemAbelian.comm hE he he') hτE hEτ hβE hfix⟩

end ReflSp

theorem ggTorusReflBridge_symplectic {K : Type} [Field K] {m : ℕ} [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 2 ≤ m) :
    GGTorusReflBridge p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggTorusReflBridge_of_core hp hp2 center_spProj_eq_bot sp_I_subset_inn
    (ReflSp.ggTorusReflCore_symplectic hp hp2 hpq (by omega))

theorem recipeSymplectic_reflBridge {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 2 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    ggTorusLift_symplectic hp hp2 hpq (by omega), ggTorusReflBridge_symplectic hp hp2 hpq hl⟩

@[expose] def GGReflSpLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1

theorem largeEvenLabelAll_reflBridge_symplectic {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_reflBridge hp hp2 hpn hlab.2.1 hQ

end CFSG.StandardType

end
