module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.RankThree.Lattice.SteinbergBIRoots
public import Certificates.Certificate14975
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice RootSpace
open CFSG.RankThree.E6 (charVal charVal_single charVal_dualMatrix dualMatrix weylMatrix
  eq_of_charVal_single weylMatrix_injective weylMatrix_pow weylMatrix_one weylMatrix_mul
  weylMatrix_apply)
open CFSG.RankThree.PartOne.KE (rootKernel dualWeylStabilizer mem_dualWeylStabilizer
  charVal_smul_eq_sum)
open scoped Matrix

set_option linter.unusedSectionVars false

theorem e8Five_sylow_count : E8FiveSylowCount :=
  Certificates.certificate14975

section GroupTheory


theorem exists_conj_pair {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] (a b : G)
    (hab : a * b = b * a) (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hind : ∀ i j : ℕ, a ^ i * b ^ j = 1 → p ∣ i ∧ p ∣ j)
    (hcard : (Nat.card G).factorization p = 2) {g : G} (hg : orderOf g = p) :
    ∃ (x : G) (i j : Fin p), x * g * x⁻¹ = a ^ (i : ℕ) * b ^ (j : ℕ) ∧ (i ≠ 0 ∨ j ≠ 0) := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hcomm : ∀ i j : ℕ, a ^ i * b ^ j = b ^ j * a ^ i := fun i j =>
    (Commute.pow_pow hab i j).eq
  have hinv : ∀ (c : G) (hc : c ^ p = 1) (i : ℕ), (c ^ i)⁻¹ = c ^ ((p - 1) * i) := by
    intro c hc i
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add]
    have : i + (p - 1) * i = p * i := by
      have : p = (p - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    rw [this, pow_mul, hc, one_pow]
  let P : Subgroup G :=
    { carrier := {w | ∃ i j : ℕ, w = a ^ i * b ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        rw [pow_add, pow_add]
        calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
          _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [← hcomm k j]
          _ = a ^ i * a ^ k * (b ^ j * b ^ l) := by group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨(p - 1) * i, (p - 1) * j, ?_⟩
        rw [mul_inv_rev, hinv a ha, hinv b hb]
        exact (hcomm _ _).symm }
  have hmemP : ∀ i j : ℕ, a ^ i * b ^ j ∈ P := fun i j => ⟨i, j, rfl⟩
  have hP25 : Nat.card P = p ^ 2 := by
    let φ : Fin p × Fin p → P := fun ij => ⟨a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ), hmemP _ _⟩
    have hφinj : Function.Injective φ := by
      rintro ⟨i, j⟩ ⟨k, l⟩ h
      have h' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) := congrArg Subtype.val h
      have hi := i.2
      have hj := j.2
      have hk := k.2
      have hl := l.2
      have key : a ^ ((i : ℕ) + (p - k)) * b ^ ((j : ℕ) + (p - l)) = 1 := by
        have e1 : a ^ ((i : ℕ) + (p - k)) * b ^ ((j : ℕ) + (p - l)) =
            (a ^ (i : ℕ) * b ^ (j : ℕ)) * (a ^ (p - k) * b ^ (p - l)) := by
          rw [pow_add, pow_add]
          calc a ^ (i : ℕ) * a ^ (p - k) * (b ^ (j : ℕ) * b ^ (p - l))
              = a ^ (i : ℕ) * (a ^ (p - k) * b ^ (j : ℕ)) * b ^ (p - l) := by group
            _ = a ^ (i : ℕ) * (b ^ (j : ℕ) * a ^ (p - k)) * b ^ (p - l) := by
                rw [hcomm (p - k) j]
            _ = a ^ (i : ℕ) * b ^ (j : ℕ) * (a ^ (p - k) * b ^ (p - l)) := by group
        rw [e1, h']
        calc a ^ (k : ℕ) * b ^ (l : ℕ) * (a ^ (p - k) * b ^ (p - l))
            = a ^ (k : ℕ) * (b ^ (l : ℕ) * a ^ (p - k)) * b ^ (p - l) := by group
          _ = a ^ (k : ℕ) * (a ^ (p - k) * b ^ (l : ℕ)) * b ^ (p - l) := by
              rw [← hcomm (p - k) l]
          _ = (a ^ (k : ℕ) * a ^ (p - k)) * (b ^ (l : ℕ) * b ^ (p - l)) := by group
          _ = 1 := by
              rw [← pow_add, ← pow_add, show (k : ℕ) + (p - k) = p by omega,
                show (l : ℕ) + (p - l) = p by omega, ha, hb, one_mul]
      obtain ⟨hdi, hdj⟩ := hind _ _ key
      obtain ⟨t, ht⟩ := hdi
      obtain ⟨s, hs⟩ := hdj
      have hik : (i : ℕ) = k := by
        rcases t with _ | _ | t
        · omega
        · omega
        · exfalso
          have h2 : p * 2 ≤ p * (t + 1 + 1) := Nat.mul_le_mul_left p (by omega)
          omega
      have hjl : (j : ℕ) = l := by
        rcases s with _ | _ | s
        · omega
        · omega
        · exfalso
          have h2 : p * 2 ≤ p * (s + 1 + 1) := Nat.mul_le_mul_left p (by omega)
          omega
      exact Prod.ext (Fin.ext hik) (Fin.ext hjl)
    have hφsurj : Function.Surjective φ := by
      rintro ⟨_, i, j, rfl⟩
      refine ⟨(⟨i % p, Nat.mod_lt _ hp0⟩, ⟨j % p, Nat.mod_lt _ hp0⟩), Subtype.ext ?_⟩
      show a ^ (i % p) * b ^ (j % p) = a ^ i * b ^ j
      rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]
    rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩), Nat.card_prod]
    simp [sq]
  have hSyl : Nat.card P = p ^ (Nat.card G).factorization p := by rw [hcard, hP25]
  let S0 : Sylow p G := Sylow.ofCard P hSyl
  have hZ : IsPGroup p (Subgroup.zpowers g) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hg, pow_one]
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G Q S0
  have hgQ : g ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g)
  have h1 : (MulAut.conj x) g ∈ ((x • Q : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hgQ
  rw [hx] at h1
  obtain ⟨i, j, hij⟩ := h1
  have hij' : x * g * x⁻¹ = a ^ (i % p) * b ^ (j % p) := by
    rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]
    simpa [MulAut.conj_apply] using hij
  refine ⟨x, ⟨i % p, Nat.mod_lt _ hp0⟩, ⟨j % p, Nat.mod_lt _ hp0⟩, hij', ?_⟩
  by_contra hcon
  push Not at hcon
  have hi0 : i % p = 0 := congrArg Fin.val hcon.1
  have hj0 : j % p = 0 := congrArg Fin.val hcon.2
  rw [hi0, hj0] at hij'
  simp only [pow_zero, mul_one] at hij'
  have : g = 1 := by
    have := congrArg (fun y => x⁻¹ * y * x) hij'
    simpa [mul_assoc] using this
  rw [this, orderOf_one] at hg
  exact hp.out.one_lt.ne hg

end GroupTheory


section Transport

theorem e8Five_image_rootKernel {K : Type*} [CommRing K] {z z' : Fin Tag.E8.rank → K}
    {a : WeylGroup Tag.E8} (h : ∀ x, charVal z' (a • x) = charVal z x) :
    (a • ·) '' rootKernel z = rootKernel z' := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul hα.1 a, by rw [h]; exact hα.2⟩
  · intro hβ
    refine ⟨a⁻¹ • β, ⟨IsRoot.smul hβ.1 a⁻¹, ?_⟩, smul_inv_smul a β⟩
    rw [← h, smul_inv_smul]
    exact hβ.2

theorem e8Five_mem_dualStab_conj {K : Type*} [CommRing K] {z z' : Fin Tag.E8.rank → K}
    {a : WeylGroup Tag.E8} (h : ∀ x, charVal z' (a • x) = charVal z x) (g : WeylGroup Tag.E8) :
    g ∈ dualWeylStabilizer z ↔ a * g * a⁻¹ ∈ dualWeylStabilizer z' := by
  simp only [mem_dualWeylStabilizer]
  constructor
  · intro hg x
    rw [mul_smul, mul_smul, h, hg, ← h, smul_inv_smul]
  · intro hg x
    have := hg (a • x)
    rw [mul_smul, mul_smul, inv_smul_smul, h, h] at this
    exact this

theorem e8Count5_eq_ncard (z : Fin Tag.E8.rank → ZMod 5) :
    e8Count5 z = (rootKernel z).ncard :=
  (ncard_isRoot_and (τ := Tag.E8) (fun v => charVal z v = 0)).symm

theorem e8Count5_transport {z z' : Fin Tag.E8.rank → ZMod 5} {a : WeylGroup Tag.E8}
    (h : ∀ x, charVal z' (a • x) = charVal z x) : e8Count5 z' = e8Count5 z := by
  rw [e8Count5_eq_ncard, e8Count5_eq_ncard, ← e8Five_image_rootKernel h]
  exact Set.ncard_image_of_injective _ (MulAction.injective a)

@[expose] def trCol (x : WeylGroup Tag.E8) (z : Fin Tag.E8.rank → ZMod 5) :
    Fin Tag.E8.rank → ZMod 5 :=
  fun i => charVal z (x⁻¹ • (Pi.single i 1 : Fin Tag.E8.rank → ℤ))

theorem charVal_trCol (x : WeylGroup Tag.E8) (z : Fin Tag.E8.rank → ZMod 5)
    (y : Fin Tag.E8.rank → ℤ) : charVal (trCol x z) y = charVal z (x⁻¹ • y) := by
  rw [charVal_smul_eq_sum z x⁻¹ y]
  rfl

theorem charVal_trCol_smul (x : WeylGroup Tag.E8) (z : Fin Tag.E8.rank → ZMod 5)
    (y : Fin Tag.E8.rank → ℤ) : charVal (trCol x z) (x • y) = charVal z y := by
  rw [charVal_trCol, inv_smul_smul]

theorem trCol_trCol_inv (x : WeylGroup Tag.E8) (z : Fin Tag.E8.rank → ZMod 5) :
    trCol x (trCol x⁻¹ z) = z := by
  refine eq_of_charVal_single fun j => ?_
  rw [charVal_trCol, charVal_trCol, inv_inv, smul_inv_smul]

theorem trCol_inv_trCol (x : WeylGroup Tag.E8) (z : Fin Tag.E8.rank → ZMod 5) :
    trCol x⁻¹ (trCol x z) = z := by
  have := trCol_trCol_inv x⁻¹ z
  rwa [inv_inv] at this

theorem trCol_injective (x : WeylGroup Tag.E8) : Function.Injective (trCol x) := fun z z' h => by
  have h1 := congrArg (trCol x⁻¹) h
  rwa [trCol_inv_trCol, trCol_inv_trCol] at h1

theorem trCol_zero (x : WeylGroup Tag.E8) : trCol x 0 = 0 := by
  funext i
  simp [trCol, charVal]

theorem trCol_eq_zero {x : WeylGroup Tag.E8} {z : Fin Tag.E8.rank → ZMod 5}
    (h : trCol x z = 0) : z = 0 := trCol_injective x (h.trans (trCol_zero x).symm)

@[expose] def fixSet (g : WeylGroup Tag.E8) : Set (Fin Tag.E8.rank → ZMod 5) :=
  {z | g ∈ dualWeylStabilizer z}

@[expose] def m40 (g : WeylGroup Tag.E8) : Set (Fin Tag.E8.rank → ZMod 5) :=
  {z | g ∈ dualWeylStabilizer z ∧ z ≠ 0 ∧ e8Count5 z = 40}

theorem mem_fixSet_trCol (x g : WeylGroup Tag.E8) (z : Fin Tag.E8.rank → ZMod 5) :
    g ∈ dualWeylStabilizer z ↔ x * g * x⁻¹ ∈ dualWeylStabilizer (trCol x z) :=
  e8Five_mem_dualStab_conj (charVal_trCol_smul x z) g

theorem trCol_image_fixSet (x g : WeylGroup Tag.E8) :
    trCol x '' fixSet g = fixSet (x * g * x⁻¹) := by
  ext z'
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_fixSet_trCol x g z).1 hz
  · intro hz'
    refine ⟨trCol x⁻¹ z', ?_, trCol_trCol_inv x z'⟩
    have := (mem_fixSet_trCol x g (trCol x⁻¹ z')).2
    rw [trCol_trCol_inv] at this
    exact this hz'

theorem trCol_image_m40 (x g : WeylGroup Tag.E8) :
    trCol x '' m40 g = m40 (x * g * x⁻¹) := by
  ext z'
  constructor
  · rintro ⟨z, ⟨hz, hz0, hz40⟩, rfl⟩
    refine ⟨(mem_fixSet_trCol x g z).1 hz, fun h => hz0 (trCol_eq_zero h), ?_⟩
    rw [e8Count5_transport (charVal_trCol_smul x z), hz40]
  · rintro ⟨hz', hz0, hz40⟩
    refine ⟨trCol x⁻¹ z', ⟨?_, ?_, ?_⟩, trCol_trCol_inv x z'⟩
    · have := (mem_fixSet_trCol x g (trCol x⁻¹ z')).2
      rw [trCol_trCol_inv] at this
      exact this hz'
    · intro h
      apply hz0
      have := congrArg (trCol x) h
      rw [trCol_trCol_inv, trCol_zero] at this
      exact this
    · rw [e8Count5_transport (charVal_trCol_smul x⁻¹ z')]
      exact hz40

theorem ncard_fixSet_conj (x g : WeylGroup Tag.E8) :
    (fixSet (x * g * x⁻¹)).ncard = (fixSet g).ncard := by
  rw [← trCol_image_fixSet]
  exact Set.ncard_image_of_injective _ (trCol_injective x)

theorem ncard_m40_conj (x g : WeylGroup Tag.E8) :
    (m40 (x * g * x⁻¹)).ncard = (m40 g).ncard := by
  rw [← trCol_image_m40]
  exact Set.ncard_image_of_injective _ (trCol_injective x)

end Transport


section Elements

@[expose] def e8FiveG1 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd [0, 2, 3, 1]

@[expose] def e8FiveG2 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd
  [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4]

@[expose] def e8FiveG1List : List (List ℤ) :=
  [[0, -1, 0, 0, 1, 0, 0, 0],
   [0, -1, 0, 1, 0, 0, 0, 0],
   [1, -1, 0, 0, 1, 0, 0, 0],
   [0, -1, 1, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8FiveG2List : List (List ℤ) :=
  [[1, 0, 0, 0, -2, 2, 0, 0],
   [0, 1, 0, 0, -3, 3, 0, 0],
   [0, 0, 1, 0, -4, 4, 0, 0],
   [0, 0, 0, 1, -6, 6, 0, 0],
   [0, 0, 0, 0, -4, 5, 0, 0],
   [0, 0, 0, 0, -3, 3, 1, 0],
   [0, 0, 0, 0, -2, 2, 0, 1],
   [0, 0, 0, 0, -1, 1, 0, 0]]

theorem weylMatrix_wordProd_of5 {ω : List (Fin Tag.E8.rank)}
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ}
    (h : ∀ j : Fin Tag.E8.rank, ω.foldr (reflect Tag.E8) (Pi.single j 1) = fun i => M i j) :
    weylMatrix ((coxeterSystem Tag.E8).wordProd ω) = M := by
  ext i j
  rw [weylMatrix_apply, wordProd_smul]
  exact congrFun (h j) i

theorem weylMatrix_e8FiveG1 : weylMatrix e8FiveG1 = toMat Tag.E8.rank e8FiveG1List :=
  weylMatrix_wordProd_of5 (by decide +kernel)

theorem weylMatrix_e8FiveG2 : weylMatrix e8FiveG2 = toMat Tag.E8.rank e8FiveG2List :=
  weylMatrix_wordProd_of5 (by decide +kernel)

theorem e8FiveG1_pow : e8FiveG1 ^ 5 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e8FiveG1, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8FiveG2_pow : e8FiveG2 ^ 5 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e8FiveG2, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Five_comm : e8FiveG1 * e8FiveG2 = e8FiveG2 * e8FiveG1 := by
  apply weylMatrix_injective
  rw [weylMatrix_mul, weylMatrix_mul, weylMatrix_e8FiveG1, weylMatrix_e8FiveG2, ← toMat_lmul,
    ← toMat_lmul]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem weylMatrix_e8Five_pow_mul (i j : ℕ) :
    weylMatrix (e8FiveG1 ^ i * e8FiveG2 ^ j) =
      toMat Tag.E8.rank (lmul Tag.E8.rank (lpow Tag.E8.rank e8FiveG1List i)
        (lpow Tag.E8.rank e8FiveG2List j)) := by
  rw [weylMatrix_mul, weylMatrix_pow, weylMatrix_pow, weylMatrix_e8FiveG1, weylMatrix_e8FiveG2,
    toMat_lmul, toMat_lpow, toMat_lpow]

theorem e8Five_ind_fin : ∀ i j : Fin 5,
    toMat Tag.E8.rank (lmul Tag.E8.rank (lpow Tag.E8.rank e8FiveG1List i)
      (lpow Tag.E8.rank e8FiveG2List j)) = 1 → i = 0 ∧ j = 0 := by
  decide +kernel

theorem e8Five_ind (i j : ℕ) (h : e8FiveG1 ^ i * e8FiveG2 ^ j = 1) : 5 ∣ i ∧ 5 ∣ j := by
  have hi : e8FiveG1 ^ i = e8FiveG1 ^ (i % 5) := pow_eq_pow_mod i e8FiveG1_pow
  have hj : e8FiveG2 ^ j = e8FiveG2 ^ (j % 5) := pow_eq_pow_mod j e8FiveG2_pow
  rw [hi, hj] at h
  have h1 := congrArg weylMatrix h
  rw [weylMatrix_e8Five_pow_mul, weylMatrix_one] at h1
  have := e8Five_ind_fin ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ h1
  exact ⟨Nat.dvd_of_mod_eq_zero (congrArg Fin.val this.1), Nat.dvd_of_mod_eq_zero (congrArg Fin.val this.2)⟩

theorem factorization_five : (696729600 : ℕ).factorization 5 = 2 := by
  have h : (696729600 : ℕ) = 5 ^ 2 * 27869184 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem exists_conj_into_P {g : WeylGroup Tag.E8} (hg : orderOf g = 5) :
    ∃ (x : WeylGroup Tag.E8) (i j : Fin 5),
      x * g * x⁻¹ = e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) ∧ (i ≠ 0 ∨ j ≠ 0) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fintype (WeylGroup Tag.E8) := Fintype.ofFinite _
  have hW : Nat.card (WeylGroup Tag.E8) = 696729600 :=
    (CFSG.RankThree.Chevalley.E8_weyl_length_polynomial).2
  exact exists_conj_pair e8FiveG1 e8FiveG2 e8Five_comm e8FiveG1_pow e8FiveG2_pow e8Five_ind
    (by rw [hW]; exact factorization_five) hg

@[expose] def e8FiveH (m : ℕ) : WeylGroup Tag.E8 := e8FiveG1 * e8FiveG2 ^ m

@[expose] def e8FiveHList (m : ℕ) : List (List ℤ) :=
  lmul Tag.E8.rank e8FiveG1List (lpow Tag.E8.rank e8FiveG2List m)

theorem weylMatrix_e8FiveH (m : ℕ) : weylMatrix (e8FiveH m) = toMat Tag.E8.rank (e8FiveHList m) := by
  rw [e8FiveH, weylMatrix_mul, weylMatrix_pow, weylMatrix_e8FiveG1, weylMatrix_e8FiveG2,
    e8FiveHList, toMat_lmul, toMat_lpow]

@[expose] def e8FiveHt (L : List (List ℤ)) : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  ((toMat Tag.E8.rank L).map (Int.cast : ℤ → ZMod 5))ᵀ

theorem echelon_aux5 {M T R : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 5)} {r : ZMod 5}
    (hTR : T * (M - r • 1) = R) {z : Fin Tag.E8.rank → ZMod 5} (h : M *ᵥ z = r • z) :
    R *ᵥ z = 0 := by
  have h0 : (M - r • 1) *ᵥ z = 0 := by
    rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  rw [← hTR, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem fix_mulVec {g : WeylGroup Tag.E8} {L : List (List ℤ)}
    (hL : weylMatrix g = toMat Tag.E8.rank L) {z : Fin Tag.E8.rank → ZMod 5}
    (hz : g ∈ dualWeylStabilizer z) : e8FiveHt L *ᵥ z = (1 : ZMod 5) • z := by
  have h1 : (dualMatrix (ZMod 5) g).mulVec z = z := by
    refine eq_of_charVal_single fun j => ?_
    rw [charVal_dualMatrix, mem_dualWeylStabilizer.1 hz, charVal_single]
  have e : dualMatrix (ZMod 5) g = e8FiveHt L := by
    unfold dualMatrix e8FiveHt
    rw [hL]
    rfl
  rw [e] at h1
  rw [one_smul]
  exact h1

@[expose] def e8FiveFixH1 (c : Fin 2 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![-(3 * c 1), -(3 * c 1), -(3 * c 1), -(3 * c 1), c 0, -(4 * c 1), -(4 * c 1), c 1]

@[expose] def e8FiveFixH2 (c : Fin 2 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![-(c 1), -(c 1), -(c 1), -(c 1), c 0, -(4 * c 1), -(4 * c 1), c 1]

@[expose] def e8FiveFixH3 (c : Fin 2 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![-(4 * c 1), -(4 * c 1), -(4 * c 1), -(4 * c 1), c 0, -(4 * c 1), -(4 * c 1), c 1]

@[expose] def e8FiveFixH4 (c : Fin 2 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![-(2 * c 1), -(2 * c 1), -(2 * c 1), -(2 * c 1), c 0, -(4 * c 1), -(4 * c 1), c 1]


@[expose] def e8FiveTh0 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 3, 0, 2, 0, 0, 0; 0, 2, 0, 0, 2, 0, 0, 0; 2, 0, 3, 0, 2, 0, 0, 0; 2, 0, 4, 0, 2, 0, 0, 0; 2, 3, 4, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def e8FiveRh0 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveTh0_mul : e8FiveTh0 * (e8FiveHt (e8FiveHList 0) - (1 : ZMod 5) • 1) = e8FiveRh0 := by
  decide +kernel

theorem read_h0 {z : Fin 8 → ZMod 5} (h0 : e8FiveRh0 *ᵥ z = 0) :
    z = e8FiveFix1 ![z 4, z 5, z 6, z 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  simp [e8FiveRh0, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3
  funext j
  fin_cases j
  · simp [e8FiveFix1]; linear_combination e0
  · simp [e8FiveFix1]; linear_combination e1
  · simp [e8FiveFix1]; linear_combination e2
  · simp [e8FiveFix1]; linear_combination e3
  · simp [e8FiveFix1]
  · simp [e8FiveFix1]
  · simp [e8FiveFix1]
  · simp [e8FiveFix1]

@[expose] def e8FiveTg2 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![0, 0, 0, 0, 0, 3, 4, 3; 0, 0, 0, 0, 4, 4, 0, 0; 0, 0, 0, 0, 4, 4, 4, 0; 0, 0, 0, 0, 4, 4, 4, 4; 1, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def e8FiveRg2 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 4, 2, 3, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveTg2_mul : e8FiveTg2 * (e8FiveHt (e8FiveG2List) - (1 : ZMod 5) • 1) = e8FiveRg2 := by
  decide +kernel

theorem read_g2 {z : Fin 8 → ZMod 5} (h0 : e8FiveRg2 *ᵥ z = 0) :
    z = e8FiveFix2 ![z 1, z 2, z 3, z 4] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  simp [e8FiveRg2, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3
  funext j
  fin_cases j
  · simp [e8FiveFix2]; linear_combination e0
  · simp [e8FiveFix2]
  · simp [e8FiveFix2]
  · simp [e8FiveFix2]
  · simp [e8FiveFix2]
  · simp [e8FiveFix2]; linear_combination e1
  · simp [e8FiveFix2]; linear_combination e2
  · simp [e8FiveFix2]; linear_combination e3

@[expose] def e8FiveTh1 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![0, 2, 2, 0, 2, 0, 1, 0; 4, 4, 4, 0, 2, 0, 1, 0; 1, 2, 2, 0, 2, 0, 1, 0; 1, 2, 3, 0, 2, 0, 1, 0; 2, 1, 2, 0, 0, 4, 3, 0; 2, 1, 2, 0, 0, 4, 2, 0; 2, 3, 4, 1, 0, 0, 0, 0; 3, 4, 3, 0, 0, 1, 3, 1]

@[expose] def e8FiveRh1 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 0, 0, 0, 0, 0, 3; 0, 1, 0, 0, 0, 0, 0, 3; 0, 0, 1, 0, 0, 0, 0, 3; 0, 0, 0, 1, 0, 0, 0, 3; 0, 0, 0, 0, 0, 1, 0, 4; 0, 0, 0, 0, 0, 0, 1, 4; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveTh1_mul : e8FiveTh1 * (e8FiveHt (e8FiveHList 1) - (1 : ZMod 5) • 1) = e8FiveRh1 := by
  decide +kernel

theorem read_h1 {z : Fin 8 → ZMod 5} (h0 : e8FiveRh1 *ᵥ z = 0) :
    z = e8FiveFixH1 ![z 4, z 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  have e4 := congrFun h0 4
  have e5 := congrFun h0 5
  simp [e8FiveRh1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3 e4 e5
  funext j
  fin_cases j
  · simp [e8FiveFixH1]; linear_combination e0
  · simp [e8FiveFixH1]; linear_combination e1
  · simp [e8FiveFixH1]; linear_combination e2
  · simp [e8FiveFixH1]; linear_combination e3
  · simp [e8FiveFixH1]
  · simp [e8FiveFixH1]; linear_combination e4
  · simp [e8FiveFixH1]; linear_combination e5
  · simp [e8FiveFixH1]

@[expose] def e8FiveTh2 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 3, 0, 2, 1, 1, 0; 0, 2, 0, 0, 2, 1, 1, 0; 2, 0, 3, 0, 2, 1, 1, 0; 2, 0, 4, 0, 2, 1, 1, 0; 4, 2, 4, 0, 0, 4, 2, 0; 1, 3, 1, 0, 0, 3, 0, 0; 2, 3, 4, 1, 0, 0, 0, 0; 1, 3, 1, 0, 0, 1, 3, 1]

@[expose] def e8FiveRh2 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0, 0, 1; 0, 0, 0, 1, 0, 0, 0, 1; 0, 0, 0, 0, 0, 1, 0, 4; 0, 0, 0, 0, 0, 0, 1, 4; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveTh2_mul : e8FiveTh2 * (e8FiveHt (e8FiveHList 2) - (1 : ZMod 5) • 1) = e8FiveRh2 := by
  decide +kernel

theorem read_h2 {z : Fin 8 → ZMod 5} (h0 : e8FiveRh2 *ᵥ z = 0) :
    z = e8FiveFixH2 ![z 4, z 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  have e4 := congrFun h0 4
  have e5 := congrFun h0 5
  simp [e8FiveRh2, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3 e4 e5
  funext j
  fin_cases j
  · simp [e8FiveFixH2]; linear_combination e0
  · simp [e8FiveFixH2]; linear_combination e1
  · simp [e8FiveFixH2]; linear_combination e2
  · simp [e8FiveFixH2]; linear_combination e3
  · simp [e8FiveFixH2]
  · simp [e8FiveFixH2]; linear_combination e4
  · simp [e8FiveFixH2]; linear_combination e5
  · simp [e8FiveFixH2]

@[expose] def e8FiveTh3 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![2, 3, 4, 0, 2, 0, 3, 0; 1, 0, 1, 0, 2, 0, 3, 0; 3, 3, 4, 0, 2, 0, 3, 0; 3, 3, 0, 0, 2, 0, 3, 0; 0, 0, 0, 0, 0, 4, 0, 0; 2, 1, 2, 0, 0, 1, 1, 0; 2, 3, 4, 1, 0, 0, 0, 0; 4, 2, 4, 0, 0, 1, 3, 1]

@[expose] def e8FiveRh3 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 0, 0, 0, 0, 0, 4; 0, 1, 0, 0, 0, 0, 0, 4; 0, 0, 1, 0, 0, 0, 0, 4; 0, 0, 0, 1, 0, 0, 0, 4; 0, 0, 0, 0, 0, 1, 0, 4; 0, 0, 0, 0, 0, 0, 1, 4; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveTh3_mul : e8FiveTh3 * (e8FiveHt (e8FiveHList 3) - (1 : ZMod 5) • 1) = e8FiveRh3 := by
  decide +kernel

theorem read_h3 {z : Fin 8 → ZMod 5} (h0 : e8FiveRh3 *ᵥ z = 0) :
    z = e8FiveFixH3 ![z 4, z 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  have e4 := congrFun h0 4
  have e5 := congrFun h0 5
  simp [e8FiveRh3, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3 e4 e5
  funext j
  fin_cases j
  · simp [e8FiveFixH3]; linear_combination e0
  · simp [e8FiveFixH3]; linear_combination e1
  · simp [e8FiveFixH3]; linear_combination e2
  · simp [e8FiveFixH3]; linear_combination e3
  · simp [e8FiveFixH3]
  · simp [e8FiveFixH3]; linear_combination e4
  · simp [e8FiveFixH3]; linear_combination e5
  · simp [e8FiveFixH3]

@[expose] def e8FiveTh4 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 3, 0, 2, 2, 2, 0; 0, 2, 0, 0, 2, 2, 2, 0; 2, 0, 3, 0, 2, 2, 2, 0; 2, 0, 4, 0, 2, 2, 2, 0; 0, 0, 0, 0, 0, 4, 4, 0; 0, 0, 0, 0, 0, 0, 4, 0; 2, 3, 4, 1, 0, 0, 0, 0; 2, 1, 2, 0, 0, 1, 3, 1]

@[expose] def e8FiveRh4 : Matrix (Fin 8) (Fin 8) (ZMod 5) :=
  !![1, 0, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0, 0, 2; 0, 0, 0, 1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1, 0, 4; 0, 0, 0, 0, 0, 0, 1, 4; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

theorem e8FiveTh4_mul : e8FiveTh4 * (e8FiveHt (e8FiveHList 4) - (1 : ZMod 5) • 1) = e8FiveRh4 := by
  decide +kernel

theorem read_h4 {z : Fin 8 → ZMod 5} (h0 : e8FiveRh4 *ᵥ z = 0) :
    z = e8FiveFixH4 ![z 4, z 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  have e4 := congrFun h0 4
  have e5 := congrFun h0 5
  simp [e8FiveRh4, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3 e4 e5
  funext j
  fin_cases j
  · simp [e8FiveFixH4]; linear_combination e0
  · simp [e8FiveFixH4]; linear_combination e1
  · simp [e8FiveFixH4]; linear_combination e2
  · simp [e8FiveFixH4]; linear_combination e3
  · simp [e8FiveFixH4]
  · simp [e8FiveFixH4]; linear_combination e4
  · simp [e8FiveFixH4]; linear_combination e5
  · simp [e8FiveFixH4]


end Elements

section Bounds

theorem e8FiveFix1_zero : e8FiveFix1 0 = 0 := by
  decide

theorem e8FiveFix2_zero : e8FiveFix2 0 = 0 := by
  decide

theorem fixSet_h0_param {z : Fin Tag.E8.rank → ZMod 5} (hz : z ∈ fixSet (e8FiveH 0)) :
    z = e8FiveFix1 ![z 4, z 5, z 6, z 7] :=
  read_h0 (echelon_aux5 e8FiveTh0_mul (fix_mulVec (weylMatrix_e8FiveH 0) hz))

theorem fixSet_g2_param {z : Fin Tag.E8.rank → ZMod 5} (hz : z ∈ fixSet e8FiveG2) :
    z = e8FiveFix2 ![z 1, z 2, z 3, z 4] :=
  read_g2 (echelon_aux5 e8FiveTg2_mul (fix_mulVec weylMatrix_e8FiveG2 hz))

theorem fixSet_h1_param {z : Fin Tag.E8.rank → ZMod 5} (hz : z ∈ fixSet (e8FiveH 1)) :
    z = e8FiveFixH1 ![z 4, z 7] :=
  read_h1 (echelon_aux5 e8FiveTh1_mul (fix_mulVec (weylMatrix_e8FiveH 1) hz))

theorem fixSet_h2_param {z : Fin Tag.E8.rank → ZMod 5} (hz : z ∈ fixSet (e8FiveH 2)) :
    z = e8FiveFixH2 ![z 4, z 7] :=
  read_h2 (echelon_aux5 e8FiveTh2_mul (fix_mulVec (weylMatrix_e8FiveH 2) hz))

theorem fixSet_h3_param {z : Fin Tag.E8.rank → ZMod 5} (hz : z ∈ fixSet (e8FiveH 3)) :
    z = e8FiveFixH3 ![z 4, z 7] :=
  read_h3 (echelon_aux5 e8FiveTh3_mul (fix_mulVec (weylMatrix_e8FiveH 3) hz))

theorem fixSet_h4_param {z : Fin Tag.E8.rank → ZMod 5} (hz : z ∈ fixSet (e8FiveH 4)) :
    z = e8FiveFixH4 ![z 4, z 7] :=
  read_h4 (echelon_aux5 e8FiveTh4_mul (fix_mulVec (weylMatrix_e8FiveH 4) hz))

theorem ncard_fixSet_le_of_param {g : WeylGroup Tag.E8}
    {P : (Fin 2 → ZMod 5) → Fin Tag.E8.rank → ZMod 5}
    (h : ∀ z ∈ fixSet g, z = P ![z 4, z 7]) : (fixSet g).ncard ≤ 25 := by
  have hsub : fixSet g ⊆ Set.range P := fun z hz => ⟨_, (h z hz).symm⟩
  calc (fixSet g).ncard ≤ (Set.range P).ncard := Set.ncard_le_ncard hsub (Set.finite_range P)
    _ = (P '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Fin 2 → ZMod 5)).ncard := Set.ncard_image_le Set.finite_univ
    _ = 25 := by
      rw [Set.ncard_univ]
      simp [Nat.card_eq_fintype_card]

theorem ncard_m40_h0_le : (m40 (e8FiveH 0)).ncard ≤ 24 := by
  have hsub : m40 (e8FiveH 0) ⊆ ↑((e8FiveT40 e8FiveFix1).image e8FiveFix1) := by
    rintro z ⟨hz, hz0, hz40⟩
    have hp := fixSet_h0_param hz
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨![z 4, z 5, z 6, z 7], ?_, hp.symm⟩)
    simp only [e8FiveT40, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h0 => hz0 ?_, by rw [← hp]; exact hz40⟩
    rw [hp, h0]
    exact e8FiveFix1_zero
  calc (m40 (e8FiveH 0)).ncard ≤ (↑((e8FiveT40 e8FiveFix1).image e8FiveFix1) : Set _).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((e8FiveT40 e8FiveFix1).image e8FiveFix1).card := Set.ncard_coe_finset _
    _ ≤ (e8FiveT40 e8FiveFix1).card := Finset.card_image_le
    _ ≤ 24 := e8Five_sylow_count.1

theorem ncard_m40_g2_le : (m40 e8FiveG2).ncard ≤ 24 := by
  have hsub : m40 e8FiveG2 ⊆ ↑((e8FiveT40 e8FiveFix2).image e8FiveFix2) := by
    rintro z ⟨hz, hz0, hz40⟩
    have hp := fixSet_g2_param hz
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨![z 1, z 2, z 3, z 4], ?_, hp.symm⟩)
    simp only [e8FiveT40, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h0 => hz0 ?_, by rw [← hp]; exact hz40⟩
    rw [hp, h0]
    exact e8FiveFix2_zero
  calc (m40 e8FiveG2).ncard ≤ (↑((e8FiveT40 e8FiveFix2).image e8FiveFix2) : Set _).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((e8FiveT40 e8FiveFix2).image e8FiveFix2).card := Set.ncard_coe_finset _
    _ ≤ (e8FiveT40 e8FiveFix2).card := Finset.card_image_le
    _ ≤ 24 := e8Five_sylow_count.2

theorem bound_h (m : ℕ) (hm : m < 5) :
    (fixSet (e8FiveH m)).ncard ≤ 25 ∨ (m40 (e8FiveH m)).ncard ≤ 24 := by
  interval_cases m
  · exact Or.inr ncard_m40_h0_le
  · exact Or.inl (ncard_fixSet_le_of_param fun z hz => fixSet_h1_param hz)
  · exact Or.inl (ncard_fixSet_le_of_param fun z hz => fixSet_h2_param hz)
  · exact Or.inl (ncard_fixSet_le_of_param fun z hz => fixSet_h3_param hz)
  · exact Or.inl (ncard_fixSet_le_of_param fun z hz => fixSet_h4_param hz)

theorem exists_pow_eq_of_not_dvd {G : Type*} [Group G] {h : G} (hh : h ^ 5 = 1) {k : ℕ}
    (hk : ¬ 5 ∣ k) : ∃ n : ℕ, (h ^ k) ^ n = h := by
  have hfermat : k ^ 4 % 5 = 1 := by
    have h1 : ∀ r : Fin 5, r.val ≠ 0 → r.val ^ 4 % 5 = 1 := by decide
    have h2 : k % 5 ≠ 0 := fun h0 => hk (Nat.dvd_of_mod_eq_zero h0)
    have := h1 ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩ h2
    rw [Nat.pow_mod]
    exact this
  refine ⟨k ^ 3, ?_⟩
  rw [← pow_mul, show k * k ^ 3 = k ^ 4 by ring, pow_eq_pow_mod _ hh, hfermat, pow_one]

theorem fixSet_subset_of_pow {w h : WeylGroup Tag.E8} (hh : h ^ 5 = 1) {k : ℕ} (hk : ¬ 5 ∣ k)
    (hw : w = h ^ k) : fixSet w ⊆ fixSet h := fun z hz => by
  obtain ⟨n, hn⟩ := exists_pow_eq_of_not_dvd hh hk
  rw [← hw] at hn
  have := Subgroup.pow_mem (dualWeylStabilizer z) hz n
  rwa [hn] at this

theorem m40_subset_of_pow {w h : WeylGroup Tag.E8} (hh : h ^ 5 = 1) {k : ℕ} (hk : ¬ 5 ∣ k)
    (hw : w = h ^ k) : m40 w ⊆ m40 h := fun _ ⟨hz, hz0, hz40⟩ =>
  ⟨fixSet_subset_of_pow hh hk hw hz, hz0, hz40⟩

theorem e8FiveH_pow_five (m : ℕ) : e8FiveH m ^ 5 = 1 := by
  have hc : Commute e8FiveG1 (e8FiveG2 ^ m) := (Commute.pow_right (e8Five_comm) m)
  rw [e8FiveH, hc.mul_pow, e8FiveG1_pow, ← pow_mul, mul_comm, pow_mul, e8FiveG2_pow, one_pow,
    mul_one]

theorem bound_w (i j : Fin 5) (hij : i ≠ 0 ∨ j ≠ 0) :
    (fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ))).ncard ≤ 25 ∨
      (m40 (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ))).ncard ≤ 24 := by
  by_cases hi : (i : ℕ) = 0
  · have hj : (j : ℕ) ≠ 0 := by
      rcases hij with h | h
      · exact absurd (Fin.ext hi) h
      · exact fun h0 => h (Fin.ext h0)
    right
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = e8FiveG2 ^ (j : ℕ) := by
      rw [hi, pow_zero, one_mul]
    have hjd : ¬ 5 ∣ (j : ℕ) := fun h => hj (Nat.eq_zero_of_dvd_of_lt h j.2)
    exact (Set.ncard_le_ncard (m40_subset_of_pow e8FiveG2_pow hjd hw) (Set.toFinite _)).trans
      ncard_m40_g2_le
  · have hid : ¬ 5 ∣ (i : ℕ) := fun h => hi (Nat.eq_zero_of_dvd_of_lt h i.2)
    have hex : ∀ i j : Fin 5, (i : ℕ) ≠ 0 → ∃ m : Fin 5, ((m : ℕ) * i) % 5 = j := by decide
    obtain ⟨m, hm⟩ := hex i j hi
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = (e8FiveH m) ^ (i : ℕ) := by
      have hc : Commute e8FiveG1 (e8FiveG2 ^ (m : ℕ)) := Commute.pow_right e8Five_comm _
      rw [e8FiveH, hc.mul_pow, ← pow_mul, pow_eq_pow_mod ((m : ℕ) * (i : ℕ)) e8FiveG2_pow, hm]
    rcases bound_h m m.2 with h | h
    · left
      exact (Set.ncard_le_ncard (fixSet_subset_of_pow (e8FiveH_pow_five m) hid hw)
        (Set.toFinite _)).trans h
    · right
      exact (Set.ncard_le_ncard (m40_subset_of_pow (e8FiveH_pow_five m) hid hw)
        (Set.toFinite _)).trans h

theorem fixset_bound {g : WeylGroup Tag.E8} (hg : orderOf g = 5) :
    (fixSet g).ncard ≤ 25 ∨ (m40 g).ncard ≤ 24 := by
  obtain ⟨x, i, j, hxg, hij⟩ := exists_conj_into_P hg
  rw [← ncard_fixSet_conj x g, ← ncard_m40_conj x g, hxg]
  exact bound_w i j hij

end Bounds

end CFSG.RankThree.PartOne.KE8F
