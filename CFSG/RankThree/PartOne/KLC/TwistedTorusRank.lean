module

public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.RankThree.PartOne.KE.CTTorus
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public noncomputable section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section Abstract

variable {τ : Tag} {C : Type} [Group C]
  [Finite C] {L : Type} [Field L]

theorem le_pRank_of_twistedTorus (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (Φ : ModGL τ L →* ModGL τ L) (n g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n) {p : ℕ} (hp : p.Prime)
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P → P ≤ ι.range)
    {A : Type*} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hpow : ∀ a : A, a ^ p = 1) {k : ℕ} (hA : Nat.card A = p ^ k) (φ : A →* ModGL τ L)
    (hφ : Function.Injective φ) (hφT : φ.range ≤ twistedTorusOf n Φ) : k ≤ CFSG.pRank p C := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Ψ : A →* ModGL τ L := (MulAut.conj g0).toMonoidHom.comp φ with hΨ
  have hΨinj : Function.Injective Ψ := (MulAut.conj g0).injective.comp hφ
  have hΨapp : ∀ a, Ψ a = g0 * φ a * g0⁻¹ := fun a => rfl
  have hT0C := twistedTorusOf_le_adjointGroup n Φ
  have hXC : Ψ.range ≤ adjointGroup τ L := by
    rintro _ ⟨a, rfl⟩
    rw [hΨapp]
    exact mul_mem (mul_mem hg0C (hT0C (hφT ⟨a, rfl⟩))) (inv_mem hg0C)
  have hXF : ∀ x ∈ Ψ.range, Φ x = x := by
    rintro _ ⟨a, rfl⟩
    have hfix := (mem_twistedTorusOf.1 (hφT ⟨a, rfl⟩)).2
    rw [hΨapp, map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ (φ a) * (g0 * n)⁻¹ = g0 * (n * Φ (φ a) * n⁻¹) * g0⁻¹ := by group
      _ = g0 * φ a * g0⁻¹ := by rw [hfix]
  have hXfin : Finite Ψ.range := Finite.of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  have hXcard : Nat.card Ψ.range = p ^ k := by
    rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv).symm
  have hXp : IsPGroup p Ψ.range := IsPGroup.of_card hXcard
  have hXι : Ψ.range ≤ ι.range := hrat Ψ.range hXC hXF Ψ.range le_rfl hXp
  let Ψ' : A →* ι.range := Ψ.codRestrict ι.range fun a => hXι ⟨a, rfl⟩
  have hΨ'inj : Function.Injective Ψ' := fun a b h => hΨinj (congrArg Subtype.val h)
  let Θ : A →* C := (MonoidHom.ofInjective hι).symm.toMonoidHom.comp Ψ'
  have hΘinj : Function.Injective Θ := (MonoidHom.ofInjective hι).symm.injective.comp hΨ'inj
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hA Θ hΘinj (H := ⊤) le_top

end Abstract

section Eigen

variable {τ : Tag} {L : Type} [Field L]

@[expose] def eigTuple (ξ₁ ξ₂ : Lˣ) (U : Fin 2 → Fin τ.rank → ℤ) : Fin τ.rank → Lˣ :=
  fun i => ξ₁ ^ U 0 i * ξ₂ ^ U 1 i

theorem eigTuple_mul (ξ₁ ξ₂ η₁ η₂ : Lˣ) (U : Fin 2 → Fin τ.rank → ℤ) :
    eigTuple (ξ₁ * η₁) (ξ₂ * η₂) U = eigTuple ξ₁ ξ₂ U * eigTuple η₁ η₂ U := by
  funext i
  simp only [eigTuple, Pi.mul_apply, mul_zpow]
  exact mul_mul_mul_comm _ _ _ _

theorem prod_zpow_eq_zpow_sum' {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem rootChar_eigTuple (ξ₁ ξ₂ : Lˣ) (U : Fin 2 → Fin τ.rank → ℤ) (v : Fin τ.rank → ℤ) :
    rootChar (eigTuple ξ₁ ξ₂ U) v =
      ξ₁ ^ (∑ i, U 0 i * v i) * ξ₂ ^ (∑ i, U 1 i * v i) := by
  simp only [rootChar, eigTuple, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum', prod_zpow_eq_zpow_sum']

omit [Field L] in
theorem zpow_eq_zpow_of_modEq' {G : Type*} [Group G] {ξ : G} {m : ℕ} (hξ : ξ ^ m = 1) {x y : ℤ}
    (h : x ≡ y [ZMOD m]) : ξ ^ x = ξ ^ y := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.1 h)
  have : y = x + m * k := by omega
  rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, mul_one]

omit [Field L] in
theorem zpow_minor_eq_one' {G : Type*} [CommGroup G] {x y : G} {p q p' q' : ℤ}
    (hA : x ^ p * y ^ q = 1) (hB : x ^ p' * y ^ q' = 1) : x ^ (p * q' - p' * q) = 1 := by
  have h1 : x ^ (p * q') * y ^ (q * q') = 1 := by
    have := congrArg (· ^ q') hA
    simp only [mul_zpow, ← zpow_mul, one_zpow] at this
    exact this
  have h2 : x ^ (p' * q) * y ^ (q * q') = 1 := by
    have := congrArg (· ^ q) hB
    simp only [mul_zpow, ← zpow_mul, one_zpow] at this
    rw [mul_comm q' q] at this
    exact this
  have h3 : x ^ (p * q') = x ^ (p' * q) := mul_right_cancel (h1.trans h2.symm)
  rw [zpow_sub, h3, mul_inv_cancel]

omit [Field L] in
theorem zpow_eq_one_of_coprime' {G : Type*} [Group G] {x : G} {m : ℕ} {δ : ℤ} (hx : x ^ m = 1)
    (hδ : x ^ δ = 1) (hc : IsCoprime δ (m : ℤ)) : x = 1 := by
  obtain ⟨u, v, huv⟩ := hc
  have : x = x ^ (u * δ + v * (m : ℤ)) := by rw [huv, zpow_one]
  rw [this, zpow_add, mul_comm u δ, zpow_mul, hδ, one_zpow, one_mul, mul_comm v, zpow_mul,
    zpow_natCast, hx, one_zpow]

theorem mem_twistedFixedTuples_of_simple {w : WeylGroup τ} {Fr : L →+* L}
    {a : Fin τ.rank → Lˣ}
    (h : ∀ k : Fin τ.rank, rootChar a (w • (Pi.single k 1 : Fin τ.rank → ℤ)) =
      Units.map Fr.toMonoidHom (a k)) : a ∈ twistedFixedTuples w Fr := by
  rw [mem_twistedFixedTuples_iff]
  intro v
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_rhs => rw [hv, rootChar_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, h i, CTTorus.rootChar_single, map_zpow]

variable [IsAlgClosed L]

theorem exists_hom_twistedTorus_of_eigen {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0) (w : WeylGroup τ)
    (Wm : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hW : ∀ k l : Fin τ.rank, (w • (Pi.single k 1 : Fin τ.rank → ℤ)) l = Wm l k)
    (U : Fin 2 → Fin τ.rank → ℤ) (i j : Fin τ.rank)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin τ.rank), (∑ l, U s l * Wm l k) ≡ (q : ℤ) * U s k [ZMOD p]) :
    ∃ φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL τ L, Function.Injective φ ∧
      φ.range ≤ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  let ψ : (rootsOfUnity p L) × (rootsOfUnity p L) →* (Fin τ.rank → Lˣ) :=
    { toFun := fun z => eigTuple (z.1 : Lˣ) (z.2 : Lˣ) U
      map_one' := by
        funext l
        simp [eigTuple]
      map_mul' := fun z z' => by
        simpa using eigTuple_mul (z.1 : Lˣ) (z.2 : Lˣ) (z'.1 : Lˣ) (z'.2 : Lˣ) U }
  let φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL τ L :=
    (rootDiagUnitHom τ L).comp ψ
  have hφ : ∀ z, φ z = rootDiagUnit τ (eigTuple (z.1 : Lˣ) (z.2 : Lˣ) U) := fun z => rfl
  have hroot : ∀ z : (rootsOfUnity p L) × (rootsOfUnity p L),
      (z.1 : Lˣ) ^ p = 1 ∧ (z.2 : Lˣ) ^ p = 1 :=
    fun z => ⟨(mem_rootsOfUnity p _).1 z.1.2, (mem_rootsOfUnity p _).1 z.2.2⟩
  refine ⟨φ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro z hz
    rw [hφ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have hA : (z.1 : Lˣ) ^ U 0 i * (z.2 : Lˣ) ^ U 1 i = 1 := congrFun hb i
    have hB : (z.1 : Lˣ) ^ U 0 j * (z.2 : Lˣ) ^ U 1 j = 1 := congrFun hb j
    obtain ⟨hm1, hm2'⟩ := hroot z
    have h1 := zpow_minor_eq_one' hA hB
    have h2 := zpow_minor_eq_one' (x := (z.2 : Lˣ)) (y := (z.1 : Lˣ)) (by rwa [mul_comm] at hA)
      (by rwa [mul_comm] at hB)
    have h2' : (z.2 : Lˣ) ^ (U 0 i * U 1 j - U 0 j * U 1 i) = 1 := by
      have : U 1 i * U 0 j - U 1 j * U 0 i = -(U 0 i * U 1 j - U 0 j * U 1 i) := by ring
      rw [this, zpow_neg, inv_eq_one] at h2
      exact h2
    have e1 := zpow_eq_one_of_coprime' hm1 h1 hdet
    have e2 := zpow_eq_one_of_coprime' hm2' h2' hdet
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · rintro _ ⟨z, rfl⟩
    rw [hφ]
    refine mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup _, mem_twistedFixedTuples_iff_conj.1 ?_⟩
    refine mem_twistedFixedTuples_of_simple fun k => ?_
    obtain ⟨hm1, hm2'⟩ := hroot z
    rw [rootChar_eigTuple, eigTuple]
    have hFru : ∀ c : Lˣ, Units.map Fr.toMonoidHom c = c ^ q := fun c =>
      Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr _)
    rw [hFru, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
    congr 1
    · refine zpow_eq_zpow_of_modEq' hm1 ?_
      have h0 := hfix 0 k
      simp only [hW] at *
      rw [mul_comm]
      exact h0
    · refine zpow_eq_zpow_of_modEq' hm2' ?_
      have h1 := hfix 1 k
      simp only [hW] at *
      rw [mul_comm]
      exact h1

theorem card_rootsOfUnity_eq {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0) :
    Nat.card (rootsOfUnity p L) = p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hpL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  exact hζ.card_rootsOfUnity

end Eigen

section Untwisted

variable {τ : Tag}

theorem two_le_pRank_untwisted {K : Type} [Field K] [Finite K] (d : ℕ)
    (hrat : ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card K) → ∀ (X : Subgroup (ModGL τ L)) [Finite X],
        X ≤ adjointGroup τ L → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).relIndex X ∣ d ∧
          ∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p' P →
            P ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpK : ¬ p ∣ Nat.card K) (w : WeylGroup τ)
    (Wm : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hW : ∀ k l : Fin τ.rank, (w • (Pi.single k 1 : Fin τ.rank → ℤ)) l = Wm l k)
    (U : Fin 2 → Fin τ.rank → ℤ) (i j : Fin τ.rank)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin τ.rank),
      (∑ l, U s l * Wm l k) ≡ (Nat.card K : ℤ) * U s k [ZMOD p]) :
    2 ≤ CFSG.pRank p (adjointGroup τ K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hpℓ : p ≠ ringChar K := by
    rintro h
    apply hpK
    rw [hq, h]
    exact dvd_pow_self _ f.ne_zero
  have hpL : (p : L) ≠ 0 := by
    intro h0
    have h1 : ringChar K ∣ p := (CharP.cast_eq_zero_iff L (ringChar K) p).1 h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h1).symm
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  let ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrat' : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hP
    rw [hrange]
    exact (hrat L Fr hFr X hXC hXF).2 p hp hp3 P hPX hP
  obtain ⟨φ, hφinj, hφT⟩ := exists_hom_twistedTorus_of_eigen hFr hp hpL w Wm hW U i j hdet hfix
  have hcard : Nat.card ((rootsOfUnity p L) × (rootsOfUnity p L)) = p ^ 2 := by
    rw [Nat.card_prod, card_rootsOfUnity_eq hp hpL, sq]
  have hpow : ∀ a : (rootsOfUnity p L) × (rootsOfUnity p L), a ^ p = 1 := fun a =>
    Prod.ext (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 a.1.2))
      (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 a.2.2))
  exact le_pRank_of_twistedTorus ι hι (Units.map (entrywiseHom Fr))
    (canonicalRep (coxeterSystem τ) L w) g0 hg0C hg0 hp hrat' (fun a b => mul_comm a b) hpow
    hcard φ hφinj hφT

end Untwisted


section Certificates


theorem modEq_of_cert {p : ℕ} {a b c Φ : ℤ} (hΦ : (p : ℤ) ∣ Φ) (h : b - a = Φ * c) :
    a ≡ b [ZMOD p] :=
  (Int.modEq_iff_dvd).2 (h ▸ Dvd.dvd.mul_right hΦ c)

theorem isCoprime_of_cert {p : ℕ} (hp : p.Prime) {μ Φ A B N : ℤ} (hΦ : (p : ℤ) ∣ Φ)
    (h : A * μ + B * Φ = N) (hN : ¬ (p : ℤ) ∣ N) : IsCoprime μ (p : ℤ) := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hnd : ¬ (p : ℤ) ∣ μ := fun hμ => hN (h ▸ dvd_add (Dvd.dvd.mul_left hμ A)
    (Dvd.dvd.mul_left hΦ B))
  exact ((Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd).symm

theorem not_dvd_smooth {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {N : ℤ} {a b : ℕ}
    (hN : N.natAbs = 2 ^ a * 3 ^ b) : ¬ (p : ℤ) ∣ N := by
  intro h
  have h1 : p ∣ N.natAbs := Int.natCast_dvd.1 h
  rw [hN] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h3
  · have := hp.dvd_of_dvd_pow h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have := hp.dvd_of_dvd_pow h3
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem smul_single_eq_lget' (τ : Tag) (l : List (Fin τ.rank)) (L : List (List ℤ))
    (h : CFSG.RankThree.Lattice.wordMat τ l = CFSG.RankThree.Lattice.toMat τ.rank L)
    (k i : Fin τ.rank) :
    ((coxeterSystem τ).wordProd l • (Pi.single k 1 : Fin τ.rank → ℤ)) i =
      CFSG.RankThree.Lattice.lget L i k := by
  rw [wordProd_smul_eq_wordMat_mulVec, h, Matrix.mulVec_single_one]
  rfl

end Certificates

section Rationality


theorem two_le_pRank_F4 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpK : ¬ p ∣ Nat.card K) (w : WeylGroup Tag.F4)
    (Wm : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
    (hW : ∀ k l : Fin Tag.F4.rank, (w • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) l = Wm l k)
    (U : Fin 2 → Fin Tag.F4.rank → ℤ) (i j : Fin Tag.F4.rank)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin Tag.F4.rank),
      (∑ l, U s l * Wm l k) ≡ (Nat.card K : ℤ) * U s k [ZMOD p]) :
    2 ≤ CFSG.pRank p (adjointGroup Tag.F4 K) := by
  refine two_le_pRank_untwisted 1 ?_ hp hp3 hpK w Wm hW U i j hdet hfix
  intro L _ _ _ Fr hFr X _ hXC hXF
  have hXle : X ≤ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
    intro x hx
    rw [← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices Tag.F4
      (Or.inr rfl) K L Fr hFr).1]
    exact ⟨hXC hx, hXF x hx⟩
  exact ⟨Nat.dvd_one.2 (Subgroup.relIndex_eq_one.2 hXle), fun _ _ _ P hPX _ => hPX.trans hXle⟩

theorem two_le_pRank_E {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpK : ¬ p ∣ Nat.card K) (w : WeylGroup τ) (Wm : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hW : ∀ k l : Fin τ.rank, (w • (Pi.single k 1 : Fin τ.rank → ℤ)) l = Wm l k)
    (U : Fin 2 → Fin τ.rank → ℤ) (i j : Fin τ.rank)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (p : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin τ.rank),
      (∑ l, U s l * Wm l k) ≡ (Nat.card K : ℤ) * U s k [ZMOD p]) :
    2 ≤ CFSG.pRank p (adjointGroup τ K) := by
  refine two_le_pRank_untwisted d ?_ hp hp3 hpK w Wm hW U i j hdet hfix
  intro L _ _ _ Fr hFr X _ hXC hXF
  have : Algebra.IsAlgebraic K L := inferInstance
  exact finite_fixed_subgroup_rational d hτ Fr hFr X hXC hXF

end Rationality

end CFSG.RankThree.PartOne.KLC
