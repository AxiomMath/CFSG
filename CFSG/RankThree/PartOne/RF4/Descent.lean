module

public import CFSG.RankThree.PartOne.RF4.LangData
public import CFSG.RankThree.PartOne.KE.LangDescent
public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.LieType.Ree.LargeReeCenterTrivial

public section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups


theorem det_transpose_cartan_F4 : Tag.F4.cartan.transpose.det = 1 := by
  rw [Matrix.det_transpose, det_cartan_F4]

theorem mem_range_baseChange_of_frobenius_fixed {K : Type} [Field K] [Finite K]
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Frq : L →+* L) (hFrq : ∀ c, Frq c = c ^ Nat.card K) (y : adjointGroup Tag.F4 L)
    (hy : Units.map (entrywiseHom Frq) (y : ModGL Tag.F4 L) = (y : ModGL Tag.F4 L)) :
    (y : ModGL Tag.F4 L) ∈ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  obtain ⟨S, hS⟩ := exists_finset_descent y.2
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
  obtain ⟨y', hy', hyy⟩ := hS E hSE
  obtain ⟨σE, -, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := Tag.F4) Frq hFrq E hKE
  have hΓ : y' ∈ entrywiseFixedGroup Tag.F4 σE := hfix y' hy' (by rw [hyy]; exact hy)
  rw [CFSG.RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one det_transpose_cartan_F4
    σE] at hΓ
  rw [← hJ]
  exact ⟨y', hΓ, hyy⟩

section Gamma

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

@[expose] def reeGammaToAdjoint (a : ℕ) :
    ReeTag.F4.reeGamma K a →* adjointGroup ReeTag.F4.tag K where
  toFun g := ⟨g, (ReeTag.mem_reeGamma.1 g.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem reeGammaToAdjoint_injective (a : ℕ) :
    Function.Injective (reeGammaToAdjoint (K := K) a) := fun g₁ g₂ h => by
  have h' := congrArg (fun y : adjointGroup ReeTag.F4.tag K => (y : ModGL ReeTag.F4.tag K)) h
  exact Subtype.ext h'

theorem finiteReeAut_reeGammaToAdjoint (a : ℕ) (g : ReeTag.F4.reeGamma K a) :
    ReeTag.F4.finiteReeAut K a (reeGammaToAdjoint a g) = reeGammaToAdjoint a g :=
  (ReeTag.mem_reeGamma.1 g.2).2

theorem finiteReeAut_eq_pow (n : ℕ) :
    ReeTag.F4.finiteReeAut K n = ReeTag.F4.finiteExceptionalAut K ^ (2 * n + 1) := by
  change ReeTag.F4.finiteExceptionalAut K * ReeTag.F4.finiteFrobeniusAut K ^ n = _
  rw [← finiteExceptionalAut_mul_self ReeTag.F4, ← sq, ← pow_mul, ← pow_succ']

theorem exists_inner_conj_eq_of_finiteReeAut {a b p : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hp : 1 ≤ p) (hbp : (2 * b + 1) * p = 2 * a + 1) (F₀ : MulAut (ReeTag.F4.reeGamma K a))
    (hF₀ : ∀ g, reeGammaToAdjoint a (F₀ g) =
      ReeTag.F4.finiteReeAut K b (reeGammaToAdjoint a g))
    (x : ReeTag.F4.reeGamma K a) (hβ : (MulAut.conj x * F₀) ^ p = 1) :
    ∃ g : ReeTag.F4.reeGamma K a,
      MulAut.conj g * (MulAut.conj x * F₀) * (MulAut.conj g)⁻¹ = F₀ := by
  classical
  set j := reeGammaToAdjoint (K := K) a with hj
  let L := AlgebraicClosure K
  obtain ⟨S₀, hLang, hS₀ι, hSι, Frq, hFrqc, hS₀pp⟩ := reeF4_lang_data L hK hbp
  set ι := adjointBaseChangeHom Tag.F4 (algebraMap K L) with hιdef
  set e := ι.comp j with hedef
  have he : Function.Injective e :=
    (adjointBaseChangeHom_injective Tag.F4 (algebraMap K L)).comp (reeGammaToAdjoint_injective a)
  have hF₀n : ∀ (n : ℕ) (g : ReeTag.F4.reeGamma K a),
      j ((F₀ ^ n) g) = (ReeTag.F4.finiteReeAut K b ^ n) (j g) := by
    intro n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, hF₀, ih, pow_succ' (ReeTag.F4.finiteReeAut K b),
        MulAut.mul_apply]
  have hF₀p : F₀ ^ p = 1 := by
    refine MulEquiv.ext fun g => reeGammaToAdjoint_injective a ?_
    rw [hF₀n, finiteReeAut_eq_pow, ← pow_mul, hbp, ← finiteReeAut_eq_pow,
      finiteReeAut_reeGammaToAdjoint, MulAut.one_apply]
  have heF₀ : ∀ g, e (F₀ g) = S₀ (e g) := by
    intro g
    change ι (j (F₀ g)) = S₀ (ι (j g))
    rw [hF₀, finiteReeAut_eq_pow]
    exact (hS₀ι (j g)).symm
  have hmem : ∀ h : adjointGroup Tag.F4 L, (S₀ ^ p) h = h → h ∈ e.range := by
    intro h hh
    have hFr : Units.map (entrywiseHom Frq) (h : ModGL Tag.F4 L) = h := by
      rw [← hS₀pp h, hh, hh]
    obtain ⟨u, hu, huy⟩ := mem_range_baseChange_of_frobenius_fixed L Frq hFrqc h hFr
    have hyι : h = ι ⟨u, hu⟩ := Subtype.ext huy.symm
    rw [hyι] at hh
    have hy' := (hSι ⟨u, hu⟩).symm.trans hh
    have hF : ReeTag.F4.finiteReeAut K a ⟨u, hu⟩ = ⟨u, hu⟩ := by
      have h1 := adjointBaseChangeHom_injective Tag.F4 (algebraMap K L) hy'
      rw [finiteReeAut_eq_pow]
      exact h1
    exact ⟨⟨u, ReeTag.mem_reeGamma.2 ⟨hu, hF⟩⟩, hyι.symm⟩
  exact CFSG.RankThree.PartOne.KE.exists_inner_conj_eq_of_lang
    (ReeTag.large_Ree_fixed_group_center_trivial a K hK) F₀ hp hF₀p S₀ hLang e he heF₀ hmem x hβ

end Gamma

open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality) 
in
theorem largeRee_fieldAut_coset_conj (a : ℕ) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (β : K ≃+* K) (hβ : orderOf β = p) (α : MulAut (ReeTag.F4.reeGamma K a)) (hα : α ^ p = 1)
    (hx : ∃ x : ReeTag.F4.reeGamma K a,
      α = MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a β) :
    ∃ g : ReeTag.F4.reeGamma K a,
      α = MulAut.conj g * ReeTag.F4.reeGammaFieldAut K a β * (MulAut.conj g)⁻¹ := by
  classical
  obtain ⟨x, rfl⟩ := hx
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ₁, hσ₁, hσ₁ord, hσ₁top, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_two (by omega) hK
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₁, hσ₁top⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  set βh := ReeTag.F4.reeGammaFieldAut K a β with hβh
  have hpf : p ∣ 2 * a + 1 := by
    rw [← hβ, ← hcardAut]
    exact orderOf_dvd_natCard β
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨d, hd⟩ := hpf
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ := hpodd
  have hdodd : Odd d := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  have hbp : (2 * b + 1) * p = 2 * a + 1 := by rw [← hb, hd, mul_comm]
  have hab : a = b + d * m := by
    have e1 : p * d = 2 * (d * m) + d := by rw [hm]; ring
    omega
  have hσ₁pow : ∀ (n : ℕ) (c : K), (σ₁ ^ n) c = c ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hσ₁, ih, ← pow_mul, ← pow_succ']
  set e₀ := d * (m + 1) with he₀
  set τ₀ := σ₁ ^ e₀ with hτ₀def
  have hτ₀ord : orderOf τ₀ = p := by
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [h, mul_zero] at hd
        omega
      · exact h
    have hcop : Nat.Coprime p (m + 1) := Nat.coprime_of_lt_prime (by omega) (by omega) hp
    have hg : Nat.gcd (p * d) (d * (m + 1)) = d := by
      rw [mul_comm p d, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
    rw [hτ₀def, orderOf_pow' _ (by positivity), hσ₁ord, hd, hg, Nat.mul_div_cancel _ hd0]
  have hzz : Subgroup.zpowers τ₀ = Subgroup.zpowers β :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hτ₀ord, hβ])
  obtain ⟨r, hr⟩ : ∃ r : ℕ, β ^ r = τ₀ := by
    have h : τ₀ ∈ Subgroup.zpowers β := hzz ▸ Subgroup.mem_zpowers τ₀
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, τ₀ ^ r' = β := by
    have h : β ∈ Subgroup.zpowers τ₀ := hzz ▸ Subgroup.mem_zpowers β
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  set τh := ReeTag.F4.reeGammaFieldAut K a τ₀ with hτh
  set x' := ((List.range r).map fun i => (βh ^ i) x).prod with hx'
  have hβ₂ : (MulAut.conj x * βh) ^ r = MulAut.conj x' * τh := by
    rw [CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, hτh, ← hr]
    congr 1
    exact (map_pow (ReeTag.F4.reeGammaFieldAutHom K a) β r).symm
  have hβ₂p : (MulAut.conj x' * τh) ^ p = 1 := by
    rw [← hβ₂, ← pow_mul, mul_comm, pow_mul, hα, one_pow]
  have hexp : ExpChar K 2 := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact ExpChar.prime Nat.prime_two
  have hFr : ∀ g : adjointGroup ReeTag.F4.tag K,
      ((ReeTag.F4.finiteFrobeniusAut K g : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) =
        Units.map (entrywiseHom (iterateFrobenius K 2 1)) (g : ModGL ReeTag.F4.tag K) := by
    intro g
    rw [ReeTag.coe_finiteFrobeniusAut]
    congr 2
  have hτ₀ring : τ₀.toRingHom = iterateFrobenius K 2 e₀ := RingHom.ext fun c => by
    rw [iterateFrobenius_def]
    exact hσ₁pow e₀ c
  have hF₀ : ∀ g, reeGammaToAdjoint a (τh g) =
      ReeTag.F4.finiteReeAut K b (reeGammaToAdjoint a g) := by
    intro g
    have hfixg := finiteReeAut_reeGammaToAdjoint a g
    rw [finiteReeAut_eq_pow] at hfixg
    refine Subtype.ext ?_
    change Units.map (entrywiseHom τ₀.toRingHom) (g : ModGL ReeTag.F4.tag K) = _
    have e2 : e₀ = d * m + d := by rw [he₀]; ring
    have e3 : 2 * b + 1 + (2 * a + 1) = 2 * e₀ := by omega
    rw [finiteReeAut_eq_pow, ← hfixg, ← MulAut.mul_apply, ← pow_add, e3, pow_mul, sq,
      finiteExceptionalAut_mul_self ReeTag.F4, hτ₀ring]
    exact (coe_pow_apply_of_entrywise_frobenius 2 (ReeTag.F4.finiteFrobeniusAut K) hFr e₀
      (reeGammaToAdjoint a g)).symm
  obtain ⟨u, hu⟩ := exists_inner_conj_eq_of_finiteReeAut hK (by omega) hbp τh hF₀ x' hβ₂p
  have hrr : (MulAut.conj x * βh) ^ (r * r') = MulAut.conj x * βh := by
    have hσrr : β ^ (r * r') = β ^ 1 := by rw [pow_mul, hr, hr', pow_one]
    rw [pow_eq_pow_iff_modEq, hβ] at hσrr
    have hdvd : orderOf (MulAut.conj x * βh) ∣ p := orderOf_dvd_of_pow_eq_one hα
    have h2 := Nat.ModEq.of_dvd hdvd hσrr
    rw [← pow_eq_pow_iff_modEq, pow_one] at h2
    exact h2
  have hfin : MulAut.conj u * (MulAut.conj x * βh) * (MulAut.conj u)⁻¹ = βh := by
    rw [← hrr, pow_mul, hβ₂, ← conj_pow, hu, hτh]
    have h1 : ReeTag.F4.reeGammaFieldAut K a τ₀ ^ r' =
        ReeTag.F4.reeGammaFieldAut K a (τ₀ ^ r') :=
      (map_pow (ReeTag.F4.reeGammaFieldAutHom K a) τ₀ r').symm
    rw [h1, hr']
  refine ⟨u⁻¹, ?_⟩
  rw [map_inv, inv_inv]
  calc MulAut.conj x * βh = (MulAut.conj u)⁻¹ *
        (MulAut.conj u * (MulAut.conj x * βh) * (MulAut.conj u)⁻¹) * MulAut.conj u := by group
    _ = _ := by rw [hfin]

end CFSG.RankThree.PartOne.RF4
