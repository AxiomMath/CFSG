module

public import CFSG.RankThree.PartOne.KLR.FrameTorus
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {L : Type} [Field L]

@[expose] def expTuple (ξ₁ ξ₂ : Lˣ) (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) :
    Fin ReeTag.F4.tag.rank → Lˣ := fun i => ξ₁ ^ U 0 i * ξ₂ ^ U 1 i

theorem expTuple_mul (ξ₁ ξ₂ η₁ η₂ : Lˣ) (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) :
    expTuple (ξ₁ * η₁) (ξ₂ * η₂) U = expTuple ξ₁ ξ₂ U * expTuple η₁ η₂ U := by
  funext i
  simp only [expTuple, Pi.mul_apply, mul_zpow]
  exact mul_mul_mul_comm _ _ _ _

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem rootChar_expTuple (ξ₁ ξ₂ : Lˣ) (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ)
    (v : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple ξ₁ ξ₂ U) v =
      ξ₁ ^ (∑ i, U 0 i * v i) * ξ₂ ^ (∑ i, U 1 i * v i) := by
  simp only [rootChar, expTuple, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum, prod_zpow_eq_zpow_sum]

omit [Field L] in
theorem zpow_eq_zpow_of_modEq {G : Type*} [Group G] {ξ : G} {m : ℕ} (hξ : ξ ^ m = 1) {x y : ℤ}
    (h : x ≡ y [ZMOD m]) : ξ ^ x = ξ ^ y := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.1 h)
  have : y = x + m * k := by omega
  rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, mul_one]

theorem rootChar_smul_eq_of_forall_single {τ : Tag} {a b : Fin τ.rank → Lˣ} {w : WeylGroup τ}
    (h : ∀ k, rootChar a (w • (Pi.single k 1 : Fin τ.rank → ℤ)) =
      rootChar b (Pi.single k 1 : Fin τ.rank → ℤ)) (v : Fin τ.rank → ℤ) :
    rootChar a (w • v) = rootChar b v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_rhs => rw [hv, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, h i]

omit [Field L] in
theorem zpow_minor_eq_one {G : Type*} [CommGroup G] {x y : G} {p q p' q' : ℤ}
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
theorem zpow_eq_one_of_coprime {G : Type*} [Group G] {x : G} {m : ℕ} {δ : ℤ} (hx : x ^ m = 1)
    (hδ : x ^ δ = 1) (hc : IsCoprime δ (m : ℤ)) : x = 1 := by
  obtain ⟨u, v, huv⟩ := hc
  have : x = x ^ (u * δ + v * (m : ℤ)) := by rw [huv, zpow_one]
  rw [this, zpow_add, mul_comm u δ, zpow_mul, hδ, one_zpow, one_mul, mul_comm v, zpow_mul,
    zpow_natCast, hx, one_zpow]

variable [CharP L 2] [IsAlgClosed L] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem exists_twisted_subgroup_aux (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) (m : ℕ)
    (hm : Odd m) (Wm : Matrix (Fin ReeTag.F4.tag.rank) (Fin ReeTag.F4.tag.rank) ℤ)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (i j : Fin ReeTag.F4.tag.rank)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (m : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin ReeTag.F4.tag.rank),
      (∑ l, U s l * Wm l k) ≡
        U s (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) [ZMOD m]) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag L), E ≤ torusGroup ReeTag.F4.tag L ∧
      E ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      Nat.card E = m ^ 2 := by
  classical
  have hm2 : ¬ 2 ∣ m := by
    rintro ⟨c, hc⟩
    exact (Nat.not_even_iff_odd.2 hm) ⟨c, by omega⟩
  have hm0 : (m : L) ≠ 0 := fun h => hm2 ((CharP.cast_eq_zero_iff L 2 m).1 h)
  have : NeZero m := ⟨fun h => hm2 (by simp [h])⟩
  have : NeZero (m : L) := ⟨hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L m
  have hcard : Nat.card (rootsOfUnity m L) = m := hζ.card_rootsOfUnity
  let φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* (Fin ReeTag.F4.tag.rank → Lˣ) :=
    { toFun := fun z => expTuple (z.1 : Lˣ) (z.2 : Lˣ) U
      map_one' := by
        funext l
        simp [expTuple]
      map_mul' := fun z z' => by
        simpa using expTuple_mul (z.1 : Lˣ) (z.2 : Lˣ) (z'.1 : Lˣ) (z'.2 : Lˣ) U }
  let Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L :=
    (rootDiagUnitHom ReeTag.F4.tag L).comp φ
  have hΦ : ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U) :=
    fun z => rfl
  have hroot : ∀ z : (rootsOfUnity m L) × (rootsOfUnity m L),
      (z.1 : Lˣ) ^ m = 1 ∧ (z.2 : Lˣ) ^ m = 1 :=
    fun z => ⟨(mem_rootsOfUnity m _).1 z.1.2, (mem_rootsOfUnity m _).1 z.2.2⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have hA : (z.1 : Lˣ) ^ U 0 i * (z.2 : Lˣ) ^ U 1 i = 1 := congrFun hb i
    have hB : (z.1 : Lˣ) ^ U 0 j * (z.2 : Lˣ) ^ U 1 j = 1 := congrFun hb j
    obtain ⟨hm1, hm2'⟩ := hroot z
    have h1 := zpow_minor_eq_one hA hB
    have h2 := zpow_minor_eq_one (x := (z.2 : Lˣ)) (y := (z.1 : Lˣ)) (by rwa [mul_comm] at hA)
      (by rwa [mul_comm] at hB)
    have h2' : (z.2 : Lˣ) ^ (U 0 i * U 1 j - U 0 j * U 1 i) = 1 := by
      have : U 1 i * U 0 j - U 1 j * U 0 i = -(U 0 i * U 1 j - U 0 j * U 1 i) := by ring
      rw [this, zpow_neg, inv_eq_one] at h2
      exact h2
    have e1 := zpow_eq_one_of_coprime hm1 h1 hdet
    have e2 := zpow_eq_one_of_coprime hm2' h2' hdet
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  refine ⟨Φ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [hΦ]
    exact rootDiagUnit_mem_torusGroup _
  · rintro _ ⟨z, rfl⟩
    rw [hΦ, rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF w]
    apply rootChar_smul_eq_of_forall_single
    intro k
    obtain ⟨hm1, hm2'⟩ := hroot z
    rw [rootChar_expTuple, CTTorus.rootChar_single, reeTuple, expTuple]
    have hpow : ∀ (n : ℕ) (x : Lˣ), x ^ n = x ^ (n : ℤ) := fun n x => (zpow_natCast x n).symm
    rw [hpow, mul_zpow, ← zpow_mul, ← zpow_mul]
    congr 1
    · refine zpow_eq_zpow_of_modEq hm1 ?_
      have h0 := hfix 0 k
      simp only [hW] at *
      exact h0
    · refine zpow_eq_zpow_of_modEq hm2' ?_
      have h1 := hfix 1 k
      simp only [hW] at *
      exact h1
  · have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← h, Nat.card_prod, hcard, sq]

omit [CharP L 2] [IsAlgClosed L] in
theorem relExp_long (a : ℕ) (j : Fin ReeTag.F4.tag.rank) (hj : j ∈ ReeTag.F4.longSet) :
    ReeTag.F4.relationExponent a j = 2 ^ a := by
  simp [ReeTag.relationExponent, hj, ReeTag.prime]

omit [CharP L 2] [IsAlgClosed L] in
theorem relExp_short (a : ℕ) (j : Fin ReeTag.F4.tag.rank) (hj : j ∉ ReeTag.F4.longSet) :
    ReeTag.F4.relationExponent a j = 2 ^ (a + 1) := by
  simp [ReeTag.relationExponent, hj, ReeTag.prime]

omit [CharP L 2] [IsAlgClosed L] in
theorem relExp_vec (a : ℕ) (j : Fin ReeTag.F4.tag.rank) :
    ((ReeTag.F4.relationExponent a j : ℕ) : ℤ) =
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) j := by
  fin_cases j
  · rw [relExp_long a _ (by decide)]; push_cast; rfl
  · rw [relExp_long a _ (by decide)]; push_cast; rfl
  · rw [relExp_short a _ (by decide)]; push_cast; rfl
  · rw [relExp_short a _ (by decide)]; push_cast; rfl

omit [CharP L 2] [IsAlgClosed L] in
theorem perm_vec (k : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.perm k = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := by
  refine Fin.ext ?_
  fin_cases k <;> rfl

theorem exists_twisted_subgroup (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) (m : ℕ)
    (hm : Odd m) (Wm : Matrix (Fin 4) (Fin 4) ℤ) (U : Fin 2 → Fin 4 → ℤ) (i j : Fin 4)
    (hW : ∀ k l : Fin 4, (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (m : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin 4),
      (∑ l, U s l * Wm l k) ≡
        U s ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
          (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ)
            ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) [ZMOD m]) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag L), E ≤ torusGroup ReeTag.F4.tag L ∧
      E ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      Nat.card E = m ^ 2 := by
  refine exists_twisted_subgroup_aux hF w m hm Wm U i j hW hdet (fun s k => ?_)
  have h := hfix s k
  have e : (ReeTag.F4.perm k : Fin 4) = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := perm_vec k
  have h1 := congrArg (fun j : Fin 4 => U s j *
    (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) j) e
  have h2 : U s ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) *
      (![2 ^ a, 2 ^ a, 2 ^ (a + 1), 2 ^ (a + 1)] : Fin 4 → ℤ) ((![3, 2, 1, 0] : Fin 4 → Fin 4) k)
        = U s (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) := by
    rw [relExp_vec a (ReeTag.F4.perm k)]
    exact h1.symm
  rw [← h2]
  exact h

end CFSG.RankThree.PartOne.KLR
