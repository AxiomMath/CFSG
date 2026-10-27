module

public import CFSG.RankThree.PartOne.KE8F.E8TorCount

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Arith

@[expose] def gE (q : ℕ) (γ : Fin Tag.E8.rank → ℤ) (j : Fin 4) : ℤ := gA γ j + (q : ℤ) * gB γ j

theorem not_dvd_gE_minor {p : ℕ} (hp2 : 2 < p) {q : ℕ} (hpq : (p : ℤ) ∣ (q : ℤ) * q + 1)
    {α β : Fin Tag.E8.rank → ℤ} {j k : Fin 4}
    (hN : gminorNorm (gA α j, gB α j) (gA α k, gB α k) (gA β j, gB β j) (gA β k, gB β k) = 1 ∨
      gminorNorm (gA α j, gB α j) (gA α k, gB α k) (gA β j, gB β j) (gA β k, gB β k) = 2) :
    ¬ (p : ℤ) ∣ gE q α j * gE q β k - gE q α k * gE q β j := by
  intro h
  unfold gE at h
  unfold gminorNorm at hN
  simp only at hN
  set a1 := gA α j
  set b1 := gB α j
  set a2 := gA α k
  set b2 := gB α k
  set c1 := gA β j
  set d1 := gB β j
  set c2 := gA β k
  set d2 := gB β k
  set X : ℤ := a1 * c2 - b1 * d2 - (a2 * c1 - b2 * d1) with hX
  set Y : ℤ := a1 * d2 + b1 * c2 - (a2 * d1 + b2 * c1) with hY
  have hid : X ^ 2 + Y ^ 2 =
      ((a1 + (q : ℤ) * b1) * (c2 + (q : ℤ) * d2) - (a2 + (q : ℤ) * b2) * (c1 + (q : ℤ) * d1)) *
          (X - (q : ℤ) * Y) +
        ((q : ℤ) * q + 1) * (Y * Y - (b1 * d2 - b2 * d1) * (X - (q : ℤ) * Y)) := by
    simp only [hX, hY]
    ring
  have hdvd : (p : ℤ) ∣ X ^ 2 + Y ^ 2 := by
    rw [hid]
    exact dvd_add (Dvd.dvd.mul_right h _) (Dvd.dvd.mul_right hpq _)
  have hp2' : (2 : ℤ) < p := by exact_mod_cast hp2
  rcases hN with hN | hN
  · rw [hN] at hdvd
    have := Int.le_of_dvd (by norm_num) hdvd
    omega
  · rw [hN] at hdvd
    have := Int.le_of_dvd (by norm_num) hdvd
    omega

theorem not_dvd_gE {p : ℕ} (hp4 : 4 < p) {q : ℕ} (hpq : (p : ℤ) ∣ (q : ℤ) * q + 1)
    {γ : Fin Tag.E8.rank → ℤ} {j : Fin 4} (h1 : 1 ≤ gA γ j ^ 2 + gB γ j ^ 2)
    (h4 : gA γ j ^ 2 + gB γ j ^ 2 ≤ 4) : ¬ (p : ℤ) ∣ gE q γ j := by
  intro h
  unfold gE at h
  have hid : gA γ j ^ 2 + gB γ j ^ 2 =
      (gA γ j + (q : ℤ) * gB γ j) * (gA γ j - (q : ℤ) * gB γ j) +
        ((q : ℤ) * q + 1) * (gB γ j * gB γ j) := by ring
  have hdvd : (p : ℤ) ∣ gA γ j ^ 2 + gB γ j ^ 2 := by
    rw [hid]
    exact dvd_add (Dvd.dvd.mul_right h _) (Dvd.dvd.mul_right hpq _)
  have := Int.le_of_dvd (by omega) hdvd
  have hp4' : (4 : ℤ) < p := by exact_mod_cast hp4
  omega

end Arith

section Group

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

@[expose] def pairGauss (q : ℕ) (j k : Fin 4) (u w : Lˣ) : Fin Tag.E8.rank → Lˣ :=
  torusOfGauss q (fun i => if i = j then u else if i = k then w else 1)

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem cg_pairGauss_j (q : ℕ) {j k : Fin 4} (u w : Lˣ) : cg (pairGauss q j k u w) j = u := by
  rw [pairGauss, cg_torusOfGauss]
  simp

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem cg_pairGauss_k (q : ℕ) {j k : Fin 4} (hjk : j ≠ k) (u w : Lˣ) :
    cg (pairGauss q j k u w) k = w := by
  rw [pairGauss, cg_torusOfGauss]
  simp [hjk.symm]

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem cg_pairGauss_other (q : ℕ) {j k i : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (u w : Lˣ) :
    cg (pairGauss q j k u w) i = 1 := by
  rw [pairGauss, cg_torusOfGauss]
  simp [hij, hik]

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem pairGauss_mem {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ}
    (hpq : p ∣ q * q + 1) {j k : Fin 4} (hjk : j ≠ k) {u w : Lˣ} (hu : u ^ p = 1) (hw : w ^ p = 1) :
    pairGauss q j k u w ∈ T0tors Fr p := by
  have hcn : ∀ c : Lˣ, c ^ p = 1 → c ^ (q * q + 1) = 1 := fun c hc => by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hc, one_pow]
  have hmem : pairGauss q j k u w ∈ fixedCharTuples e8P4V Fr := by
    refine torusOfGauss_mem hFr (fun i => ?_)
    by_cases hij : i = j
    · simp [hij, hcn u hu]
    · by_cases hik : i = k
      · simp [hik, hjk.symm, hcn w hw]
      · simp [hij, hik]
  refine (mem_T0tors_iff hFr).2 ⟨hmem, fun i => ?_⟩
  by_cases hij : i = j
  · rw [hij, cg_pairGauss_j]; exact hu
  · by_cases hik : i = k
    · rw [hik, cg_pairGauss_k q hjk]; exact hw
    · rw [cg_pairGauss_other q hij hik]; simp

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem rootChar_pairGauss {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ}
    (hpq : p ∣ q * q + 1) {j k : Fin 4} (hjk : j ≠ k) {u w : Lˣ} (hu : u ^ p = 1) (hw : w ^ p = 1)
    (γ : Fin Tag.E8.rank → ℤ) :
    rootChar (pairGauss q j k u w) γ = u ^ gE q γ j * w ^ gE q γ k := by
  have hb : pairGauss q j k u w ∈ fixedCharTuples e8P4V Fr :=
    ((mem_T0tors_iff hFr).1 (pairGauss_mem hFr hpq hjk hu hw)).1
  rw [rootChar_T0 hFr hb γ]
  rw [Finset.prod_eq_mul j k hjk]
  · rw [cg_pairGauss_j, cg_pairGauss_k q hjk]
    rfl
  · intro i _ hi
    rw [cg_pairGauss_other q hi.1 hi.2]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h
  · intro h
    exact absurd (Finset.mem_univ k) h

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem pairGauss_mul {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ}
    (hpq : p ∣ q * q + 1) {j k : Fin 4} (hjk : j ≠ k) {u w u' w' : Lˣ} (hu : u ^ p = 1)
    (hw : w ^ p = 1) (hu' : u' ^ p = 1) (hw' : w' ^ p = 1) :
    pairGauss q j k u w * pairGauss q j k u' w' = pairGauss q j k (u * u') (w * w') := by
  have h1 := ((mem_T0tors_iff hFr).1 (pairGauss_mem hFr hpq hjk hu hw)).1
  have h2 := ((mem_T0tors_iff hFr).1 (pairGauss_mem hFr hpq hjk hu' hw')).1
  have h3 := ((mem_T0tors_iff hFr).1 (pairGauss_mem hFr hpq hjk
    (u := u * u') (w := w * w') (by rw [mul_pow, hu, hu', one_mul])
    (by rw [mul_pow, hw, hw', one_mul]))).1
  refine cg_injective hFr ((fixedCharTuples e8P4V Fr).mul_mem h1 h2) h3 (fun i => ?_)
  have hc : ∀ (b b' : Fin Tag.E8.rank → Lˣ), cg (b * b') i = cg b i * cg b' i := fun b b' => by
    simp only [cg, bs]
    exact CTTorus.rootChar_mul b b' (e8P4col (ev i))
  rw [hc]
  by_cases hij : i = j
  · subst hij
    simp only [cg_pairGauss_j]
  · by_cases hik : i = k
    · subst hik
      simp only [cg_pairGauss_k q hjk]
    · simp only [cg_pairGauss_other q hij hik, mul_one]

end Group

section Counting

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem comm_aux {G : Type*} [CommGroup G] (u w u' w' : G) (a₁ b₁ a₂ b₂ : ℤ)
    (e1 : u ^ a₁ * w ^ b₁ = u' ^ a₁ * w' ^ b₁) (e2 : u ^ a₂ * w ^ b₂ = u' ^ a₂ * w' ^ b₂) :
    u ^ (a₁ * b₂ - b₁ * a₂) = u' ^ (a₁ * b₂ - b₁ * a₂) ∧
      w ^ (a₁ * b₂ - b₁ * a₂) = w' ^ (a₁ * b₂ - b₁ * a₂) := by
  have e1' : a₁ • Additive.ofMul u + b₁ • Additive.ofMul w =
      a₁ • Additive.ofMul u' + b₁ • Additive.ofMul w' := by
    have := congrArg Additive.ofMul e1
    simpa [ofMul_mul, ofMul_zpow] using this
  have e2' : a₂ • Additive.ofMul u + b₂ • Additive.ofMul w =
      a₂ • Additive.ofMul u' + b₂ • Additive.ofMul w' := by
    have := congrArg Additive.ofMul e2
    simpa [ofMul_mul, ofMul_zpow] using this
  constructor
  · have : (a₁ * b₂ - b₁ * a₂) • Additive.ofMul u = (a₁ * b₂ - b₁ * a₂) • Additive.ofMul u' := by
      calc (a₁ * b₂ - b₁ * a₂) • Additive.ofMul u
          = b₂ • (a₁ • Additive.ofMul u + b₁ • Additive.ofMul w) -
              b₁ • (a₂ • Additive.ofMul u + b₂ • Additive.ofMul w) := by module
        _ = b₂ • (a₁ • Additive.ofMul u' + b₁ • Additive.ofMul w') -
              b₁ • (a₂ • Additive.ofMul u' + b₂ • Additive.ofMul w') := by rw [e1', e2']
        _ = (a₁ * b₂ - b₁ * a₂) • Additive.ofMul u' := by module
    simpa [ofMul_zpow] using congrArg Additive.toMul this
  · have : (a₁ * b₂ - b₁ * a₂) • Additive.ofMul w = (a₁ * b₂ - b₁ * a₂) • Additive.ofMul w' := by
      calc (a₁ * b₂ - b₁ * a₂) • Additive.ofMul w
          = a₁ • (a₂ • Additive.ofMul u + b₂ • Additive.ofMul w) -
              a₂ • (a₁ • Additive.ofMul u + b₁ • Additive.ofMul w) := by module
        _ = a₁ • (a₂ • Additive.ofMul u' + b₂ • Additive.ofMul w') -
              a₂ • (a₁ • Additive.ofMul u' + b₁ • Additive.ofMul w') := by rw [e1', e2']
        _ = (a₁ * b₂ - b₁ * a₂) • Additive.ofMul w' := by module
    simpa [ofMul_zpow] using congrArg Additive.toMul this

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem unit_eq_of_zpow_eq {p : ℕ} (hp : p.Prime) {u u' : Lˣ} (hu : u ^ p = 1) (hu' : u' ^ p = 1)
    {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) (h : u ^ m = u' ^ m) : u = u' := by
  have hg : (u * u'⁻¹) ^ p = 1 := by rw [mul_pow, inv_pow, hu, hu', inv_one, one_mul]
  have hg' : (u * u'⁻¹) ^ m = 1 := by
    rw [mul_zpow, _root_.inv_zpow', h, ← _root_.zpow_add, add_neg_cancel, zpow_zero]
  have h1 : orderOf (u * u'⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hg
  have h2 : (orderOf (u * u'⁻¹) : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 hg'
  rcases (Nat.dvd_prime hp).1 h1 with h3 | h3
  · have := orderOf_eq_one_iff.1 h3
    exact mul_inv_eq_one.1 this
  · rw [h3] at h2
    exact absurd h2 hm

omit [Fact ℓ.Prime] in
theorem exists_unit_orderOf {p : ℕ} (hp : p.Prime) (hpℓ : ¬ ℓ ∣ p) : ∃ ζ : Lˣ, orderOf ζ = p := by
  have hp' : (p : L) ≠ 0 := fun h => hpℓ ((CharP.cast_eq_zero_iff L ℓ p).1 h)
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hp'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  have hu : IsUnit ζ := hζ.isUnit hp.ne_zero
  refine ⟨hu.unit, ?_⟩
  have : IsPrimitiveRoot hu.unit p := IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)
  exact this.eq_orderOf.symm

omit [Fact ℓ.Prime] in
theorem card_le_sq_of_minor {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ q * q + 1) (hpℓ : ¬ ℓ ∣ p) {j k : Fin 4} (hjk : j ≠ k)
    {α β : Fin Tag.E8.rank → ℤ}
    (hm : ¬ (p : ℤ) ∣ gE q α j * gE q β k - gE q α k * gE q β j)
    {Y : Subgroup (Fin Tag.E8.rank → Lˣ)} (hY : Y ≤ T0tors Fr p)
    (hα : ∀ y ∈ Y, rootChar y α = 1) (hβ : ∀ y ∈ Y, rootChar y β = 1) :
    Nat.card Y ≤ p ^ 2 := by
  classical
  have hMcard : Nat.card {u : Lˣ // u ^ p = 1} = p := card_rootsOfUnity_pos hpℓ hp.ne_zero
  have hT : Nat.card (T0tors Fr p) = p ^ 4 := card_T0tors hFr hp hpq hpℓ
  have hfin : Finite (T0tors Fr p) := Nat.finite_of_card_ne_zero (by rw [hT]; exact pow_ne_zero 4 hp.ne_zero)
  let f : Y × ({u : Lˣ // u ^ p = 1} × {u : Lˣ // u ^ p = 1}) → T0tors Fr p := fun x =>
    ⟨x.1.1 * pairGauss q j k x.2.1.1 x.2.2.1,
      mul_mem (hY x.1.2) (pairGauss_mem hFr hpq hjk x.2.1.2 x.2.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨y, u, w⟩ ⟨y', u', w'⟩ h
    have h' : y.1 * pairGauss q j k u.1 w.1 = y'.1 * pairGauss q j k u'.1 w'.1 :=
      congrArg Subtype.val h
    have hch : ∀ γ, (∀ z ∈ Y, rootChar z γ = 1) →
        u.1 ^ gE q γ j * w.1 ^ gE q γ k = u'.1 ^ gE q γ j * w'.1 ^ gE q γ k := fun γ hγ => by
      have := congrArg (fun z => rootChar z γ) h'
      simp only [CTTorus.rootChar_mul, hγ y y.2, hγ y' y'.2, one_mul] at this
      rwa [rootChar_pairGauss hFr hpq hjk u.2 w.2, rootChar_pairGauss hFr hpq hjk u'.2 w'.2]
        at this
    obtain ⟨h1, h2⟩ := comm_aux u.1 w.1 u'.1 w'.1 _ _ _ _ (hch α hα) (hch β hβ)
    have hm' : ¬ (p : ℤ) ∣ gE q α j * gE q β k - gE q α k * gE q β j := hm
    have hu : u = u' := Subtype.ext (unit_eq_of_zpow_eq hp u.2 u'.2 hm' h1)
    have hw : w = w' := Subtype.ext (unit_eq_of_zpow_eq hp w.2 w'.2 hm' h2)
    subst hu
    subst hw
    have : y.1 = y'.1 := mul_right_cancel h'
    have hy : y = y' := Subtype.ext this
    rw [hy]
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod, hMcard, hT] at hc
  have hpp : 0 < p * p := Nat.mul_pos hp.pos hp.pos
  calc Nat.card Y = Nat.card Y * (p * p) / (p * p) := by
        rw [Nat.mul_div_cancel _ hpp]
    _ ≤ p ^ 4 / (p * p) := Nat.div_le_div_right hc
    _ = p ^ 2 := by
        rw [show p ^ 4 = p ^ 2 * (p * p) by ring, Nat.mul_div_cancel _ hpp]

omit [Fact ℓ.Prime] in
theorem eq_cls_of_trivial {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpq : p ∣ q * q + 1)
    (hpℓ : ¬ ℓ ∣ p) {Y : Subgroup (Fin Tag.E8.rank → Lˣ)} (hY : Y ≤ T0tors Fr p)
    (hcard : p ^ 3 ≤ Nat.card Y) {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α)
    (hβ : IsRoot .E8 β) (hαY : ∀ y ∈ Y, rootChar y α = 1) (hβY : ∀ y ∈ Y, rootChar y β = 1) :
    β = α ∨ β = -α ∨ β = e8P4V *ᵥ α ∨ β = -(e8P4V *ᵥ α) := by
  by_contra hne
  obtain ⟨j, k, hjk, hN⟩ := e8P4_minor hα hβ hne
  have hpq' : (p : ℤ) ∣ (q : ℤ) * q + 1 := by exact_mod_cast hpq
  have hm := not_dvd_gE_minor hp2 hpq' hN
  have hle := card_le_sq_of_minor hFr hp hpq hpℓ hjk hm hY hαY hβY
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

omit [Fact ℓ.Prime] in
theorem exists_nontrivial_char {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {p : ℕ} (hp : p.Prime) (hp4 : 4 < p) (hpq : p ∣ q * q + 1)
    (hpℓ : ¬ ℓ ∣ p) {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    ∃ b ∈ T0tors Fr p, rootChar b α ≠ 1 := by
  obtain ⟨j, h1, h4⟩ := e8P4_coord_nonzero hα
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf (L := L) hp hpℓ
  obtain ⟨k, hjk⟩ : ∃ k : Fin 4, j ≠ k := ⟨j + 1, by fin_cases j <;> decide⟩
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hpq' : (p : ℤ) ∣ (q : ℤ) * q + 1 := by exact_mod_cast hpq
  refine ⟨pairGauss q j k ζ 1, pairGauss_mem hFr hpq hjk hζp (one_pow _), ?_⟩
  rw [rootChar_pairGauss hFr hpq hjk hζp (one_pow _), _root_.one_zpow, mul_one]
  intro h
  have := orderOf_dvd_iff_zpow_eq_one.2 h
  rw [hζ] at this
  exact not_dvd_gE hp4 hpq' h1 h4 this

omit [Fact ℓ.Prime] in
theorem exists_ne_one_trivial {Fr : L →+* L} {p : ℕ}
    (hp : p.Prime) (hpℓ : ¬ ℓ ∣ p) {P : Subgroup (Fin Tag.E8.rank → Lˣ)} (hP : P ≤ T0tors Fr p)
    (hcard : p ^ 2 ≤ Nat.card P) (γ : Fin Tag.E8.rank → ℤ) :
    ∃ x ∈ P, x ≠ 1 ∧ rootChar x γ = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hMcard : Nat.card {u : Lˣ // u ^ p = 1} = p := card_rootsOfUnity_pos hpℓ hp.ne_zero
  have hpow : ∀ x : P, rootChar x.1 γ ^ p = 1 := fun x =>
    CTTorus.rootChar_pow_eq_one (hP x.2).2 γ
  let θ : P → {u : Lˣ // u ^ p = 1} := fun x => ⟨rootChar x.1 γ, hpow x⟩
  have hθ : Function.Injective θ := by
    intro x y hxy
    have h1 : rootChar x.1 γ = rootChar y.1 γ := congrArg Subtype.val hxy
    have h2 : rootChar (x.1 * y.1⁻¹) γ = 1 := by
      rw [CTTorus.rootChar_mul, CFSG.LieType.Chevalley.rootChar_inv_apply, h1, mul_inv_cancel]
    have h3 : x.1 * y.1⁻¹ = 1 := by
      by_contra hne
      exact hcon _ (mul_mem x.2 (inv_mem y.2)) hne h2
    exact Subtype.ext (mul_inv_eq_one.1 h3)
  have hfin : Finite {u : Lˣ // u ^ p = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hMcard]; exact hp.ne_zero)
  have hc := Nat.card_le_card_of_injective θ hθ
  rw [hMcard] at hc
  have h2 : p < p ^ 2 := by nlinarith [hp.one_lt]
  omega

end Counting

end CFSG.RankThree.PartOne.KE8F
