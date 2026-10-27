module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExc.Three

local instance tableBExcThreeNeZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def wordE8G0 : List (Fin Tag.E8.rank) := [0, 2]

@[expose] def wordE8G1 : List (Fin Tag.E8.rank) := [5, 4]

@[expose] def wordE8G2 : List (Fin Tag.E8.rank) :=
  [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3]

@[expose] def wordE8G3 : List (Fin Tag.E8.rank) :=
  [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3,
    2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]

@[expose] def wordE8C : List (Fin Tag.E8.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]

@[expose] def wordE8G : Fin 4 → List (Fin Tag.E8.rank) :=
  ![wordE8G0, wordE8G1, wordE8G2, wordE8G3]

@[expose] def gE8 (i : Fin 4) : WeylGroup .E8 := (coxeterSystem .E8).wordProd (wordE8G i)

@[expose] def cE8 : WeylGroup .E8 := (coxeterSystem .E8).wordProd wordE8C

@[expose] def piE8 : Equiv.Perm (Fin 4) := ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

theorem piE8_pow_three : piE8 ^ 3 = 1 := by decide

theorem gE8_pow_three (i : Fin 4) : gE8 i ^ 3 = 1 := by
  refine ext_single fun j => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, gE8, wordProd_smul,
    wordProd_smul, wordProd_smul]
  revert i j
  decide +kernel

theorem gE8_comm (i j : Fin 4) : gE8 i * gE8 j = gE8 j * gE8 i := by
  refine ext_single fun k => ?_
  rw [mul_smul, mul_smul, gE8, gE8, wordProd_smul, wordProd_smul, wordProd_smul, wordProd_smul]
  revert i j k
  decide +kernel

theorem cE8_pow_three : cE8 ^ 3 = 1 := by
  refine ext_single fun j => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, cE8, wordProd_smul,
    wordProd_smul, wordProd_smul]
  revert j
  decide +kernel

theorem cE8_conj (i : Fin 4) : cE8 * gE8 i * cE8⁻¹ = gE8 (piE8 i) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine ext_single fun j => ?_
  rw [mul_smul, mul_smul, gE8, gE8, cE8, wordProd_smul, wordProd_smul, wordProd_smul,
    wordProd_smul]
  revert i j
  decide +kernel

theorem isModel_E8 : IsModel piE8 gE8 cE8 :=
  ⟨gE8_pow_three, gE8_comm, cE8_pow_three, cE8_conj⟩

@[expose] noncomputable def modelHomE8 : Model piE8 piE8_pow_three →* WeylGroup .E8 :=
  modelHom isModel_E8

@[expose] def testE8 : Fin 4 → Fin Tag.E8.rank → ℤ :=
  ![Pi.single 0 1, Pi.single 4 1, Pi.single 1 1, Pi.single 7 1]

theorem testE8_fix : ∀ i j : Fin 4, i ≠ j → gE8 j • testE8 i = testE8 i := by
  intro i j
  rw [gE8, wordProd_smul]
  revert i j
  decide +kernel

theorem testE8_move (i : Fin 4) :
    gE8 i • testE8 i ≠ testE8 i ∧ gE8 i ^ 2 • testE8 i ≠ testE8 i := by
  rw [pow_two, mul_smul, gE8, wordProd_smul, wordProd_smul]
  revert i
  decide +kernel

theorem modelHomE8_injective : Function.Injective modelHomE8 := by
  refine modelHom_injective isModel_E8 (modelN_injective isModel_E8 testE8 testE8_fix testE8_move)
    ⟨0, fun h => ?_, fun h => ?_⟩
  · have h1 := testE8_fix 0 1 (by decide)
    rw [show (1 : Fin 4) = piE8 0 from rfl, h] at h1
    exact (testE8_move 0).1 h1
  · have h1 := testE8_fix 0 2 (by decide)
    rw [show (2 : Fin 4) = (piE8 ^ 2) 0 by decide, h] at h1
    exact (testE8_move 0).1 h1

theorem card_range_modelHomE8 : Nat.card modelHomE8.range = 243 :=
  card_range_modelHom isModel_E8 modelHomE8_injective

theorem card_fixAll_le_of_leftInverse {F : Type*} [Field F] [Fintype F] {ι : Type*} {r k : ℕ}
    (f : ι → (Fin r → F) →ₗ[F] (Fin r → F)) (R : Fin k → ι × Fin r) (C : Fin k → Fin r)
    (hC : Function.Injective C) (N : Fin k → Fin k → F)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (f (R c).1 (Pi.single (C b) 1) (R c).2 -
      if (R c).2 = C b then 1 else 0) = if a = b then 1 else 0) :
    Nat.card {x : Fin r → F // ∀ t, f t x = x} ≤ Fintype.card F ^ (r - k) := by
  classical
  set T : Set (Fin r) := (Set.range C)ᶜ with hT
  let g : {x : Fin r → F // ∀ t, f t x = x} → (T → F) := fun x i => x.1 i
  have hinj : Function.Injective g := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    apply Subtype.ext
    set u := x - y with hu
    have hfu : ∀ t, f t u = u := fun t => by rw [hu, map_sub, hx, hy]
    have hsupp : ∀ i, i ∉ Set.range C → u i = 0 := by
      intro i hi
      have h1 := congrFun hxy ⟨i, hi⟩
      simp only [g] at h1
      rw [hu, Pi.sub_apply, h1, sub_self]
    have hdecomp : u = ∑ b, u (C b) • (Pi.single (C b) 1 : Fin r → F) := by
      funext i
      rw [Finset.sum_apply]
      by_cases hi : i ∈ Set.range C
      · obtain ⟨b, rfl⟩ := hi
        rw [Finset.sum_eq_single b (fun b' _ hb' => by
            rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hb' (hC h).symm), smul_zero])
          (fun h => absurd (Finset.mem_univ b) h), Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one]
      · rw [hsupp i hi]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hi ⟨b, h.symm⟩), smul_zero]
    have hrow : ∀ c : Fin k, ∑ b, (f (R c).1 (Pi.single (C b) 1) (R c).2 -
        if (R c).2 = C b then 1 else 0) * u (C b) = 0 := by
      intro c
      have hfu' : f (R c).1 u (R c).2 =
          ∑ b, u (C b) * f (R c).1 (Pi.single (C b) 1) (R c).2 := by
        conv_lhs => rw [hdecomp]
        rw [map_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul]
      have hu' : u (R c).2 = ∑ b, u (C b) * (if (R c).2 = C b then 1 else 0) := by
        conv_lhs => rw [hdecomp]
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      have h1 : f (R c).1 u (R c).2 - u (R c).2 = 0 := by rw [hfu, sub_self]
      rw [hfu', hu', ← Finset.sum_sub_distrib] at h1
      exact (Finset.sum_congr rfl fun b _ => by ring).trans h1
    have hzero : ∀ b, u (C b) = 0 := by
      intro b
      have h1 : ∑ a, (if b = a then (1 : F) else 0) * u (C a) = u (C b) := by simp
      rw [← h1]
      calc ∑ a, (if b = a then (1 : F) else 0) * u (C a)
          = ∑ a, (∑ c, N b c * (f (R c).1 (Pi.single (C a) 1) (R c).2 -
              if (R c).2 = C a then 1 else 0)) * u (C a) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [hN b a]
        _ = ∑ c, N b c * ∑ a, (f (R c).1 (Pi.single (C a) 1) (R c).2 -
              if (R c).2 = C a then 1 else 0) * u (C a) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
            ring
        _ = 0 := by simp only [hrow, mul_zero, Finset.sum_const_zero]
    have hu0 : u = 0 := by
      rw [hdecomp]
      exact Finset.sum_eq_zero fun b _ => by rw [hzero b, zero_smul]
    rw [hu, sub_eq_zero] at hu0
    exact hu0
  have hcardT : Nat.card T = r - k := by
    rw [hT, Nat.card_coe_set_eq, Set.ncard_compl, ← Nat.card_coe_set_eq,
      Nat.card_range_of_injective hC, Nat.card_fin, Nat.card_fin]
  calc Nat.card {x : Fin r → F // ∀ t, f t x = x} ≤ Nat.card (T → F) :=
        Nat.card_le_card_of_injective g hinj
    _ = Fintype.card F ^ (r - k) := by
        rw [Nat.card_fun, hcardT, Nat.card_eq_fintype_card]

theorem card_fix_two_torusWord_le {τ : Tag} {p : ℕ} [Fact p.Prime] (ω₁ ω₂ : List (Fin τ.rank))
    {k : ℕ} (R : Fin k → Fin 2 × Fin τ.rank) (C : Fin k → Fin τ.rank) (hC : Function.Injective C)
    (N : Fin k → Fin k → ZMod p)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (torusWord τ p (![ω₁, ω₂] (R c).1) (Pi.single (C b) 1)
      (R c).2 - if (R c).2 = C b then 1 else 0) = if a = b then 1 else 0) :
    Nat.card {x : Fin τ.rank → ZMod p // torusWord τ p ω₁ x = x ∧ torusWord τ p ω₂ x = x} ≤
      p ^ (τ.rank - k) := by
  have h := card_fixAll_le_of_leftInverse (fun t => torusWordLin τ p (![ω₁, ω₂] t)) R C hC N
    (by simpa only [torusWordLin_apply] using hN)
  simp only [torusWordLin_apply, ZMod.card] at h
  refine le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)) h
  constructor
  · rintro ⟨h1, h2⟩ t
    fin_cases t
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 0, h 1⟩

local instance tableBExcThreeFactE8 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem cartan_symm_E8 : ∀ i j : Fin Tag.E8.rank, Tag.E8.cartan i j = Tag.E8.cartan j i := by
  have h : ∀ i j : Fin 8, decide (Tag.cartanE 8 i j = Tag.cartanE 8 j i) = true := by decide
  exact fun i j => of_decide_eq_true (h i j)

@[expose] def nfWordE8 (a b c d : ℕ) : List (Fin Tag.E8.rank) :=
  (List.replicate a wordE8G0).flatten ++ (List.replicate b wordE8G1).flatten ++
    (List.replicate c wordE8G2).flatten ++ (List.replicate d wordE8G3).flatten

theorem modelNE8_apply (v : Multiplicative (Fin 4 → ZMod 3)) :
    modelN isModel_E8 v = (coxeterSystem .E8).wordProd
      (nfWordE8 (v.toAdd 0).val (v.toAdd 1).val (v.toAdd 2).val (v.toAdd 3).val) := by
  have hv : v = .ofAdd (Pi.single 0 (v.toAdd 0)) * .ofAdd (Pi.single 1 (v.toAdd 1)) *
      .ofAdd (Pi.single 2 (v.toAdd 2)) * .ofAdd (Pi.single 3 (v.toAdd 3)) := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_mul, map_mul, map_mul, modelN_single, modelN_single, modelN_single, modelN_single,
    nfWordE8, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordProd_append, wordProd_replicate, wordProd_replicate, wordProd_replicate,
    wordProd_replicate]
  rfl

theorem modelHomE8_inl (v : Multiplicative (Fin 4 → ZMod 3)) :
    modelHomE8 (SemidirectProduct.inl v) = (coxeterSystem .E8).wordProd
      (nfWordE8 (v.toAdd 0).val (v.toAdd 1).val (v.toAdd 2).val (v.toAdd 3).val) := by
  rw [modelHomE8, modelHom_inl, modelNE8_apply]

theorem modelHomE8_c (v : Multiplicative (Fin 4 → ZMod 3)) :
    modelHomE8 ⟨v, .ofAdd 1⟩ = (coxeterSystem .E8).wordProd
      (nfWordE8 (v.toAdd 0).val (v.toAdd 1).val (v.toAdd 2).val (v.toAdd 3).val ++ wordE8C) := by
  rw [modelHomE8, modelHom_apply, modelNE8_apply, CoxeterSystem.wordProd_append]
  rfl

theorem card_fix_nfWordE8_0101 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 0 1 0 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 4, 5, 7] ![3, 4, 6, 7] (by decide)
    ![![0, 2, 2, 1], ![2, 2, 1, 2], ![0, 0, 0, 1], ![1, 0, 0, 0]] (by decide +kernel)

theorem card_fix_nfWordE8_0201 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 0 2 0 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 4, 5, 7] ![3, 4, 6, 7] (by decide)
    ![![0, 1, 1, 1], ![1, 0, 1, 2], ![0, 0, 0, 1], ![1, 0, 0, 0]] (by decide +kernel)

theorem card_fix_nfWordE8_1100 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 1 0 0) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 1, 0], ![2, 2, 1, 1]] (by decide +kernel)

theorem card_fix_nfWordE8_1101 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 1 0 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 1, 0], ![2, 2, 1, 1]] (by decide +kernel)

theorem card_fix_nfWordE8_2201 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 2 2 0 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 0, 0, 0], ![1, 1, 0, 0], ![2, 2, 1, 2], ![1, 1, 2, 2]] (by decide +kernel)

theorem card_fix_nfWordE8_1200 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 2 0 0) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 1, 2], ![2, 2, 2, 2]] (by decide +kernel)

theorem card_fix_nfWordE8_1201 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 2 0 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 1, 1, 2], ![2, 2, 2, 2]] (by decide +kernel)

theorem card_fix_nfWordE8_2101 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 2 1 0 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 2, 4, 5] ![0, 3, 4, 6] (by decide)
    ![![1, 0, 0, 0], ![1, 1, 0, 0], ![2, 2, 1, 0], ![1, 1, 1, 1]] (by decide +kernel)

theorem card_fix_nfWordE8_1110 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 1 1 0) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![0, 0, 1, 2], ![0, 1, 0, 2], ![2, 0, 2, 0], ![1, 2, 1, 0]] (by decide +kernel)

theorem card_fix_nfWordE8_1111 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 1 1 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![0, 0, 1, 2], ![0, 1, 0, 2], ![2, 0, 2, 0], ![1, 2, 1, 0]] (by decide +kernel)

theorem card_fix_nfWordE8_2221 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 2 2 2 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![1, 2, 0, 1], ![2, 0, 2, 1], ![1, 0, 1, 0], ![2, 1, 2, 0]] (by decide +kernel)

theorem card_fix_nfWordE8_1210 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 2 1 0) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![1, 2, 2, 2], ![1, 0, 1, 2], ![2, 0, 2, 0], ![1, 2, 1, 0]] (by decide +kernel)

theorem card_fix_nfWordE8_1211 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 1 2 1 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![1, 2, 2, 2], ![1, 0, 1, 2], ![2, 0, 2, 0], ![1, 2, 1, 0]] (by decide +kernel)

theorem card_fix_nfWordE8_2211 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 (nfWordE8 2 2 1 1) x = x} ≤
      3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![1, 1, 0, 1], ![2, 0, 2, 2], ![1, 0, 1, 0], ![2, 2, 2, 0]] (by decide +kernel)

theorem card_fix_wordE8G0 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 wordE8G0 x = x} ≤
      3 ^ (8 - 2) :=
  card_fix_torusWord_le (τ := .E8) wordE8G0 ![0, 2] ![0, 3] (by decide)
    ![![1, 2], ![2, 2]] (by decide +kernel)

theorem card_fix_wordE8G1 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 wordE8G1 x = x} ≤
      3 ^ (8 - 2) :=
  card_fix_torusWord_le (τ := .E8) wordE8G1 ![4, 5] ![3, 4] (by decide)
    ![![2, 2], ![2, 1]] (by decide +kernel)

theorem card_fix_wordE8G2 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 wordE8G2 x = x} ≤
      3 ^ (8 - 2) :=
  card_fix_torusWord_le (τ := .E8) wordE8G2 ![0, 1] ![1, 3] (by decide)
    ![![1, 2], ![0, 2]] (by decide +kernel)

theorem card_fix_wordE8G3 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 // torusWord .E8 3 wordE8G3 x = x} ≤
      3 ^ (8 - 2) :=
  card_fix_torusWord_le (τ := .E8) wordE8G3 ![0, 7] ![6, 7] (by decide)
    ![![0, 1], ![1, 0]] (by decide +kernel)

theorem card_fix_uc_0 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
      torusWord .E8 3 (nfWordE8 0 0 0 0 ++ wordE8C) x = x} ≤ 3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 3] ![0, 1, 2, 6] (by decide)
    ![![2, 0, 0, 2], ![0, 2, 0, 2], ![0, 2, 2, 2], ![0, 0, 0, 1]] (by decide +kernel)

theorem card_fix_uc_1 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
      torusWord .E8 3 (nfWordE8 0 0 0 1 ++ wordE8C) x = x} ≤ 3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 3] ![0, 1, 2, 6] (by decide)
    ![![2, 0, 0, 2], ![0, 2, 0, 2], ![0, 2, 2, 2], ![0, 0, 0, 1]] (by decide +kernel)

theorem card_fix_uc_2 :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
      torusWord .E8 3 (nfWordE8 0 0 0 2 ++ wordE8C) x = x} ≤ 3 ^ (8 - 4) :=
  card_fix_torusWord_le (τ := .E8) _ ![0, 1, 2, 3] ![0, 1, 2, 6] (by decide)
    ![![2, 0, 0, 0], ![0, 2, 0, 2], ![0, 2, 2, 1], ![0, 0, 0, 1]] (by decide +kernel)

theorem card_fix_d_u :
    Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
      torusWord .E8 3 (nfWordE8 1 1 1 0) x = x ∧ torusWord .E8 3 wordE8G3 x = x} ≤ 3 ^ (8 - 5) :=
  card_fix_two_torusWord_le (τ := .E8) _ _ ![(0, 0), (0, 1), (0, 2), (0, 4), (1, 0)]
    ![0, 1, 3, 6, 7] (by decide)
    ![![0, 0, 1, 2, 0], ![0, 1, 0, 2, 0], ![2, 0, 2, 0, 0], ![1, 2, 1, 0, 0], ![0, 0, 0, 0, 1]]
    (by decide +kernel)

theorem eq_ofAdd_vec4 (v : Multiplicative (Fin 4 → ZMod 3)) :
    v = .ofAdd ![v.toAdd 0, v.toAdd 1, v.toAdd 2, v.toAdd 3] := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl

theorem conj_vec4_E8 : ∀ a b c d : ZMod 3,
    (Multiplicative.ofAdd ![a, b, c, d] : Multiplicative (Fin 4 → ZMod 3)) *
        shiftAut piE8 (.ofAdd ![a, b, c, d]) * (shiftAut piE8 ^ 2) (.ofAdd ![a, b, c, d]) = 1 →
      (Multiplicative.ofAdd ![0, -b, a, 0] : Multiplicative (Fin 4 → ZMod 3)) *
          .ofAdd ![a, b, c, d] * (shiftAut piE8 (.ofAdd ![0, -b, a, 0]))⁻¹ =
        .ofAdd ![0, 0, 0, d] := by
  decide +kernel

theorem fix_caseI_E8 (v : Multiplicative (Fin 4 → ZMod 3))
    (hv : v * shiftAut piE8 v * (shiftAut piE8 ^ 2) v = 1) :
    ∃ w, fixCard (torusPerm .E8 3) modelHomE8 ⟨w * v * (shiftAut piE8 w)⁻¹, .ofAdd 1⟩ ≤ 3 ^ 4 := by
  refine ⟨.ofAdd ![0, -(v.toAdd 1), v.toAdd 0, 0], ?_⟩
  rw [eq_ofAdd_vec4 v] at hv
  have hw := conj_vec4_E8 _ _ _ _ hv
  rw [← eq_ofAdd_vec4 v] at hw
  rw [hw, fixCard_torusPerm_eq cartan_symm_E8 _ _ _ (modelHomE8_c _)]
  show Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
    torusWord .E8 3 (nfWordE8 0 0 0 (v.toAdd 3).val ++ wordE8C) x = x} ≤ 3 ^ 4
  have hd : (v.toAdd 3).val = 0 ∨ (v.toAdd 3).val = 1 ∨ (v.toAdd 3).val = 2 := by
    have := ZMod.val_lt (v.toAdd 3)
    omega
  rcases hd with hd | hd | hd <;> rw [hd]
  · exact card_fix_uc_0
  · exact card_fix_uc_1
  · exact card_fix_uc_2

theorem card_fixShift_E8 :
    Nat.card {w : Multiplicative (Fin 4 → ZMod 3) // shiftAut piE8 w = w} ≤ 9 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem exists_rep_E8 : ∀ a b c d : ZMod 3,
    2 ≤ (supp (.ofAdd ![a, b, c, d] : Multiplicative (Fin 4 → ZMod 3))).card →
      ∃ k : Fin 3, ∃ e : Fin 2,
        (shiftAut piE8 ^ (k : ℕ)) ((.ofAdd ![a, b, c, d] : Multiplicative (Fin 4 → ZMod 3)) ^
          ((e : ℕ) + 1)) ∈ ({
          .ofAdd ![0, 1, 0, 1], .ofAdd ![0, 2, 0, 1], .ofAdd ![1, 1, 0, 0],
          .ofAdd ![1, 1, 0, 1], .ofAdd ![2, 2, 0, 1], .ofAdd ![1, 2, 0, 0],
          .ofAdd ![1, 2, 0, 1], .ofAdd ![2, 1, 0, 1], .ofAdd ![1, 1, 1, 0],
          .ofAdd ![1, 1, 1, 1], .ofAdd ![2, 2, 2, 1], .ofAdd ![1, 2, 1, 0],
          .ofAdd ![1, 2, 1, 1], .ofAdd ![2, 2, 1, 1]} : Finset (Multiplicative (Fin 4 → ZMod 3))) := by
  decide +kernel

theorem fix_supp_E8 (v : Multiplicative (Fin 4 → ZMod 3)) (hv : 2 ≤ (supp v).card) :
    fixCard (torusPerm .E8 3) modelHomE8 (SemidirectProduct.inl v) ≤ 3 ^ 4 := by
  rw [eq_ofAdd_vec4 v] at hv ⊢
  obtain ⟨k, e, he⟩ := exists_rep_E8 _ _ _ _ hv
  refine fixCard_inl_le_of_rot _ _ k ((e : ℕ) + 1) (by omega) ?_
  generalize (shiftAut piE8 ^ (k : ℕ)) _ = r at he ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 0 1 0 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_0101
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 0 2 0 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_0201
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 1 0 0)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1100
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 1 0 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1101
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 2 2 0 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_2201
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 2 0 0)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1200
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 2 0 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1201
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 2 1 0 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_2101
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 1 1 0)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1110
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 1 1 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1111
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 2 2 2 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_2221
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 2 1 0)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1210
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 1 2 1 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_1211
  · rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (nfWordE8 2 2 1 1)
      (by rw [modelHomE8_inl]; rfl)]
    exact card_fix_nfWordE8_2211

theorem fix_single_E8 (i : Fin 4) :
    fixCard (torusPerm .E8 3) modelHomE8 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ≤
      3 ^ 6 := by
  rw [fixCard_torusPerm_eq cartan_symm_E8 _ _ (wordE8G i)
    (by rw [modelHomE8, modelHom_inl, modelN_single, ZMod.val_one, pow_one]; rfl)]
  fin_cases i
  · exact card_fix_wordE8G0
  · exact card_fix_wordE8G1
  · exact card_fix_wordE8G2
  · exact card_fix_wordE8G3

theorem fix_N_E8 : Nat.card {x : Fin Tag.E8.rank → ZMod 3 //
    ∀ v, torusPerm .E8 3 (modelHomE8 (SemidirectProduct.inl v)) x = x} ≤ 3 ^ 3 := by
  have h1 : ∀ x : Fin Tag.E8.rank → ZMod 3,
      torusPerm .E8 3 (modelHomE8 (SemidirectProduct.inl (.ofAdd ![1, 1, 1, 0]))) x = x ↔
        torusWord .E8 3 (nfWordE8 1 1 1 0) x = x := fun x => by
    rw [torusPerm_apply, modelHomE8_inl, ← torusWord_eq_torusAct cartan_symm_E8]
    rfl
  have h2 : ∀ x : Fin Tag.E8.rank → ZMod 3,
      torusPerm .E8 3 (modelHomE8 (SemidirectProduct.inl (.ofAdd ![0, 0, 0, 1]))) x = x ↔
        torusWord .E8 3 wordE8G3 x = x := fun x => by
    rw [torusPerm_apply, modelHomE8_inl, ← torusWord_eq_torusAct cartan_symm_E8]
    rfl
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1, (h1 x.1).mp (x.2 _), (h2 x.1).mp (x.2 _)⟩ : {x : Fin Tag.E8.rank → ZMod 3 //
      torusWord .E8 3 (nfWordE8 1 1 1 0) x = x ∧ torusWord .E8 3 wordE8G3 x = x}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) ?_
  exact card_fix_d_u

theorem noOffender_E8 (A : Subgroup (WeylGroup .E8)) (hAS : A ≤ modelHomE8.range)
    (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : Fin Tag.E8.rank → ZMod 3 // ∀ a ∈ A, torusAct .E8 3 a x = x} <
      3 ^ Tag.E8.rank :=
  card_mul_card_fix_lt_of_model (torusPerm .E8 3) modelHomE8 modelHomE8_injective
    (fun _ h3 hc h1 => card_mul_fixAllCard_lt (T := 3 ^ Tag.E8.rank) (torusPerm .E8 3) modelHomE8
      fix_caseI_E8 card_fixShift_E8 fix_supp_E8 fix_single_E8 fix_N_E8
      (by decide) (by decide) (by decide) (by decide) h3 hc h1) hAS hA hA1

open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

theorem geomSum_twentyfour_mod {q : ℕ} (h : q % 3 = 1) : geomSum 24 1 q % 9 = 6 := by
  have hr : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
  rw [geomSum]
  simp only [one_mul]
  rw [TableBF4.geomSum_mod]
  rcases hr with h | h | h <;> rw [h] <;> decide

section T

variable {K : Type} [Field K]

theorem not_three_dvd_index_E8 [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (weylX .E8 K modelHomE8.range).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq3 := mod_eq_one_of_dvd_sub_one (by norm_num) hq h3
  have hq1 : (Nat.card K : ZMod 3) = 1 := cast_eq_one_of_dvd_sub_one hq h3
  have hG3 := geomSum_three_mod hq3
  have hG9 := geomSum_nine_mod hq3
  have hG34 := geomSum_three_four_mod hq3
  have hG24 := geomSum_twentyfour_mod hq3
  have hm3 := cast_div_eq (p := 3) (c := 1) (by norm_num) (by norm_num) hG3
  have hm34 := cast_div_eq (p := 3) (c := 1) (by norm_num) (by norm_num) hG34
  have hm24 := cast_div_eq (p := 3) (c := 2) (by norm_num) (by norm_num) hG24
  have hm9 := cast_div_nine_eq hG9
  have hGm3 : geomSum 3 1 (Nat.card K) = 3 * (geomSum 3 1 (Nat.card K) / 3) := by omega
  have hGm34 : geomSum 3 4 (Nat.card K) = 3 * (geomSum 3 4 (Nat.card K) / 3) := by omega
  have hGm24 : geomSum 24 1 (Nat.card K) = 3 * (geomSum 24 1 (Nat.card K) / 3) := by omega
  have hGm9 : geomSum 9 1 (Nat.card K) = 9 * (geomSum 9 1 (Nat.card K) / 9) := by omega
  set M := Nat.card K ^ 120 * (geomSum 2 1 (Nat.card K) * (geomSum 3 1 (Nat.card K) / 3) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      ((geomSum 9 1 (Nat.card K) / 9) * (geomSum 3 4 (Nat.card K) / 3)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K)) *
      ((geomSum 24 1 (Nat.card K) / 3) * geomSum 2 10 (Nat.card K) *
        geomSum 5 6 (Nat.card K))) with hM
  have hC : Nat.card (adjointGroup .E8 K) =
      Nat.card modelHomE8.range * Nat.card (torusGroup .E8 K) * M := by
    rw [card_adjointGroup_E8_eq, prodE8, card_range_modelHomE8, hM]
    nth_rewrite 1 [hGm3]
    nth_rewrite 1 [hGm9]
    nth_rewrite 1 [hGm34]
    nth_rewrite 1 [hGm24]
    ring
  rw [index_weylX_eq hC]
  apply not_dvd_of_cast_ne_zero
  rw [hM]
  push_cast
  simp only [hq1, hm3, hm34, hm9, hm24, geomSum_cast hq1, one_pow, Nat.cast_one, Nat.cast_ofNat]
  decide

theorem ggExcToralRankInput_E8_three [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E8 K 3 :=
  ggExcToralRankInput_of_noOffender Nat.prime_three h3
    (isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E8 (by norm_num))
    (card_torusPow_E8 Nat.prime_three h3) cartan_symm_E8 (not_three_dvd_index_E8 h3)
    noOffender_E8

end T

end TableBExc.Three

theorem ggE8ThreeToralRankInput_holds :
    GGE8ThreeToralRankInput :=
  fun _ _ _ _ h3 => TableBExc.Three.ggExcToralRankInput_E8_three h3

end CFSG.StandardType
