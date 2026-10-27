module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGField1
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGField1c
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldNorm
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldHom
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

private theorem mul_pow_of_comm_scalar {G : Type*} [Group G] {x y c : G}
    (hc : ∀ g : G, c * g = g * c) (h : x * y = c * (y * x)) (m : ℕ) :
    x * y ^ m = c ^ m * (y ^ m * x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc x * y ^ (m + 1) = x * (y ^ m * y) := by rw [pow_succ]
      _ = (x * y ^ m) * y := by group
      _ = (c ^ m * (y ^ m * x)) * y := by rw [ih]
      _ = c ^ m * (y ^ m * (x * y)) := by group
      _ = c ^ m * (y ^ m * (c * (y * x))) := by rw [h]
      _ = c ^ m * ((y ^ m * c) * (y * x)) := by group
      _ = c ^ m * ((c * y ^ m) * (y * x)) := by rw [← hc (y ^ m)]
      _ = (c ^ m * c) * (y ^ m * (y * x)) := by group
      _ = (c ^ m * c) * ((y ^ m * y) * x) := by group
      _ = c ^ (m + 1) * (y ^ (m + 1) * x) := by rw [← pow_succ, ← pow_succ]

private theorem mul_scalar_mul {G : Type*} [Group G] (s g h : G)
    (hs : ∀ z : G, s * z = z * s) : g * (s * h) = s * (g * h) := by
  calc g * (s * h) = (g * s) * h := by group
    _ = (s * g) * h := by rw [← hs g]
    _ = s * (g * h) := by group

private theorem inv_pow_eq_pow_three {G : Type*} [Group G] {v : G} (hv : v ^ 3 = 1) {m : ℕ}
    (hm : m < 3) : (v ^ m)⁻¹ = v ^ ((3 - m) % 3) := by
  interval_cases m
  · simp
  · rw [show (3 - 1) % 3 = 2 by norm_num, inv_eq_iff_mul_eq_one]
    simp only [pow_one]
    rw [← pow_succ', hv]
  · rw [show (3 - 2) % 3 = 1 by norm_num, inv_eq_iff_mul_eq_one]
    simp only [pow_one]
    rw [← pow_succ, hv]

private theorem conj_key {G : Type*} [Group G] (X₀ M st sζ : G) (j : ℕ)
    (hst : ∀ g : G, st * g = g * st)
    (hX0 : X₀ * M = sζ * (M * X₀)) :
    (st * X₀ * M ^ j) * M = sζ * (M * (st * X₀ * M ^ j)) := by
  have hconj_cancel : (st * (X₀ * M ^ j)) * M * (st * (X₀ * M ^ j))⁻¹ =
      X₀ * M * X₀⁻¹ := by
    rw [show (st * (X₀ * M ^ j))⁻¹ = (X₀ * M ^ j)⁻¹ * st⁻¹ by group]
    rw [show st * (X₀ * M ^ j) * M * ((X₀ * M ^ j)⁻¹ * st⁻¹) =
        st * ((X₀ * M ^ j) * M * (X₀ * M ^ j)⁻¹) * st⁻¹ by group]
    rw [hst ((X₀ * M ^ j) * M * (X₀ * M ^ j)⁻¹)]
    rw [show (X₀ * M ^ j) * M * (X₀ * M ^ j)⁻¹ = X₀ * M * X₀⁻¹ by group]
    group
  have hconj0 : X₀ * M * X₀⁻¹ = sζ * M := by
    rw [hX0]; group
  have hconjX : (st * X₀ * M ^ j) * M * (st * X₀ * M ^ j)⁻¹ = sζ * M := by
    rw [show st * X₀ * M ^ j = st * (X₀ * M ^ j) by group]
    rw [hconj_cancel, hconj0]
  calc (st * X₀ * M ^ j) * M
      = ((st * X₀ * M ^ j) * M * (st * X₀ * M ^ j)⁻¹) * (st * X₀ * M ^ j) := by group
    _ = (sζ * M) * (st * X₀ * M ^ j) := by rw [hconjX]
    _ = sζ * (M * (st * X₀ * M ^ j)) := by group

private theorem direct_key {G : Type*} [Group G] (X N M stZ c : G) (k : ℕ)
    (hstZ : ∀ g : G, stZ * g = g * stZ)
    (hc : ∀ g : G, c * g = g * c)
    (hXN : X * N = N * X)
    (hXM : X * M = c * (M * X)) :
    X * (stZ * N * M ^ k) = c ^ k * ((stZ * N * M ^ k) * X) := by
  have hcpow : ∀ g : G, c ^ k * g = g * c ^ k :=
    fun g => ((show Commute c g from hc g).pow_left k).eq
  have hpow : X * M ^ k = c ^ k * (M ^ k * X) := mul_pow_of_comm_scalar hc hXM k
  have h1 : X * (stZ * (N * M ^ k)) = stZ * (X * (N * M ^ k)) :=
    mul_scalar_mul stZ X (N * M ^ k) hstZ
  have h2 : X * (N * M ^ k) = N * (X * M ^ k) := by
    calc X * (N * M ^ k) = (X * N) * M ^ k := by group
      _ = (N * X) * M ^ k := by rw [hXN]
      _ = N * (X * M ^ k) := by group
  have h3 : N * (c ^ k * (M ^ k * X)) = c ^ k * (N * (M ^ k * X)) :=
    mul_scalar_mul (c ^ k) N (M ^ k * X) hcpow
  calc X * (stZ * N * M ^ k)
      = X * (stZ * (N * M ^ k)) := by group
    _ = stZ * (X * (N * M ^ k)) := h1
    _ = stZ * (N * (X * M ^ k)) := by rw [h2]
    _ = stZ * (N * (c ^ k * (M ^ k * X))) := by rw [hpow]
    _ = stZ * (c ^ k * (N * (M ^ k * X))) := by rw [h3]
    _ = c ^ k * (stZ * (N * (M ^ k * X))) :=
          mul_scalar_mul (c ^ k) stZ (N * (M ^ k * X)) hcpow
    _ = c ^ k * ((stZ * N * M ^ k) * X) := by group

private theorem exists_primitiveRoot_three [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hpq : 3 ∣ 2 ^ n + 1) : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    conv_lhs => rw [show (1 : ℕ) = 1 ^ 2 by norm_num]
    rw [Nat.sq_sub_sq]
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK, hsq]
    exact dvd_mul_of_dvd_left hpq _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨x, IsPrimitiveRoot.iff_orderOf.mpr hx⟩

private theorem exists_good [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))}
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)))
    {M : GL (Fin 6) K}
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {l : Kˣ}
    (hMu : M ∈ primeFormUnitary hKd (idGram K 6))
    (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l) (a : Ab)
    (hcomm : ∀ (N : GL (Fin 6) K)
      (hN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      TableB.projConj (unitarySU 2 n K 6) ⟨N, hN⟩ =
          (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) → N * M = M * N)
    (ha3 : (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) ^ 3 = 1) :
    ∃ (g : GL (Fin 6) K)
      (hgN : g ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) (j : ℕ),
      j < 3 ∧ g ^ 3 = 1 ∧ g * M = M * g ∧
        TableB.projConj (unitarySU 2 n K 6) ⟨g, hgN⟩ =
          (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) *
            (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ j := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have h := congrArg Prod.fst he
    simp only at h
    omega
  obtain ⟨N, hN, hNu, hNeq⟩ := exists_unitary_lift hKd hAbI a.2
  have hN3scal : N ^ 3 ∈ LargeEvenScalars (Fin 6) K := by
    have hproj : TableB.projConj (unitarySU 2 n K 6)
        ((⟨N, hN⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) ^ 3) = 1 := by
      rw [map_pow, hNeq, ha3]
    have h := mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq hp3 hpq hproj
    simpa using h
  obtain ⟨c, hc⟩ := hN3scal
  have hNM : N * M = GeneralLinearGroup.scalar (Fin 6) (1 : Kˣ) * (M * N) := by
    rw [map_one, one_mul]
    exact hcomm N hN hNeq
  obtain ⟨j, t, hj, htu, hgt⟩ :=
    exists_normalized hKd hpq hMu hNu hM3 hl hc.symm (by norm_num : (1 : Kˣ) ^ 3 = 1) hNM
  have hz : GeneralLinearGroup.scalar (Fin 6) t⁻¹ ∈ LargeEvenScalars (Fin 6) K := ⟨t⁻¹, rfl⟩
  have hgN : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * N * M ^ j) ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    (Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).mul_mem
      ((Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).mul_mem
        (TableB.scalar_mem_normalizer _ hz) hN)
      ((Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).pow_mem hMN j)
  refine ⟨GeneralLinearGroup.scalar (Fin 6) t⁻¹ * N * M ^ j, hgN, j, hj, hgt, ?_, ?_⟩
  · have h1 : Commute (GeneralLinearGroup.scalar (Fin 6) t⁻¹) M :=
      TypeA.PGLTor.commute_scalar t⁻¹ M
    have h2 : Commute N M := hcomm N hN hNeq
    exact ((h1.mul_left h2).mul_left ((Commute.refl M).pow_left j)).eq
  · have hsplit : ((⟨GeneralLinearGroup.scalar (Fin 6) t⁻¹ * N * M ^ j, hgN⟩ :
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) =
        (⟨GeneralLinearGroup.scalar (Fin 6) t⁻¹,
            TableB.scalar_mem_normalizer _ hz⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) *
          ⟨N, hN⟩ * ⟨M, hMN⟩ ^ j := by
      apply Subtype.ext
      rfl
    rw [hsplit, map_mul, map_mul, map_pow, TableB.projConj_of_scalar _ hz, hNeq, one_mul]

private theorem chi_nontrivial [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))}
    (hAb : CFSG.Open.IsElemAbelian 3 Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)))
    (hcard : Nat.card Ab = 27) {M : GL (Fin 6) K}
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {l : Kˣ}
    (hMu : M ∈ primeFormUnitary hKd (idGram K 6))
    (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l)
    (hMA : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ ∈ Ab)
    {χ : Ab →* Kˣ} (hχ3 : ∀ a, χ a ^ 3 = 1)
    (hχcomm : ∀ (a : Ab) (N : GL (Fin 6) K)
        (hN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
        TableB.projConj (unitarySU 2 n K 6) ⟨N, hN⟩ =
            (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) →
          N * M = GeneralLinearGroup.scalar (Fin 6) (χ a) * (M * N)) :
    ∃ a : Ab, χ a ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hex : ∀ a : Ab, ∃ (g : GL (Fin 6) K)
      (hgN : g ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) (j : ℕ),
      j < 3 ∧ g ^ 3 = 1 ∧ g * M = M * g ∧
        TableB.projConj (unitarySU 2 n K 6) ⟨g, hgN⟩ =
          (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) *
            (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ j := by
    intro a
    exact exists_good hKd hK hpq hAbI hMN hMu hM3 hl a
      (fun N hN hNeq => by
        have h := hχcomm a N hN hNeq
        rwa [hcon a, map_one, one_mul] at h)
      (hAb.2 (a : MulAut _) a.2)
  choose g hgN j hjg hg3 hgM hgρ using hex
  by_cases hcase : ∃ a : Ab, g a ∉ LargeEvenScalars (Fin 6) K
  · obtain ⟨a₁, ha₁⟩ := hcase
    obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_three (K := K) hK hpq
    have hg₁Ab : TableB.projConj (unitarySU 2 n K 6) ⟨g a₁, hgN a₁⟩ ∈ Ab := by
      rw [hgρ a₁]
      exact Ab.mul_mem a₁.2 (Ab.pow_mem hMA (j a₁))
    obtain ⟨χ₁, hχ₁3, hχ₁comm⟩ :=
      exists_commChar hKd hK hpq hAb hAbI (hgN a₁) hg₁Ab
    have hcomm_all : ∀ a : Ab, g a * g a₁ = g a₁ * g a := by
      intro a
      have hgaAb : TableB.projConj (unitarySU 2 n K 6) ⟨g a, hgN a⟩ ∈ Ab := by
        rw [hgρ a]
        exact Ab.mul_mem a.2 (Ab.pow_mem hMA (j a))
      have hωcomm := hχ₁comm
        ⟨TableB.projConj (unitarySU 2 n K 6) ⟨g a, hgN a⟩, hgaAb⟩ (g a) (hgN a) rfl
      by_cases hω1 : χ₁ ⟨TableB.projConj (unitarySU 2 n K 6) ⟨g a, hgN a⟩, hgaAb⟩ = 1
      · rw [hω1, map_one, one_mul] at hωcomm
        exact hωcomm
      · exact (false_of_cyclic_partner hl hM3 (hg3 a₁) (hgM a₁)
          (IsPrimitiveRoot.iff_orderOf.mpr
            (orderOf_eq_prime (hχ₁3 _) hω1)) hωcomm).elim
    have hrepr : ∀ a : Ab, ∃ (c : Kˣ) (k : ℕ),
        g a = GeneralLinearGroup.scalar (Fin 6) c * (g a₁) ^ k := by
      intro a
      exact exists_eq_scalar_mul_pow_of_commute hl hM3 hζ₀ (hg3 a₁) (hg3 a) (hgM a₁)
        (hgM a) (hcomm_all a).symm ha₁
    have hρrepr : ∀ a : Ab, ∃ k : ℕ,
        TableB.projConj (unitarySU 2 n K 6) ⟨g a, hgN a⟩ =
          (TableB.projConj (unitarySU 2 n K 6) ⟨g a₁, hgN a₁⟩) ^ k := by
      intro a
      obtain ⟨c, k, hck⟩ := hrepr a
      refine ⟨k, ?_⟩
      have hsub : (⟨g a, hgN a⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
          (⟨GeneralLinearGroup.scalar (Fin 6) c,
              TableB.scalar_mem_normalizer _ ⟨c, rfl⟩⟩ :
            Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) *
            ⟨g a₁, hgN a₁⟩ ^ k := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hck
      rw [hsub, map_mul, map_pow, TableB.projConj_of_scalar _ ⟨c, rfl⟩, one_mul]
    have hspan : ∀ a : Ab, ∃ k j : ℕ, k < 3 ∧ j < 3 ∧
        (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) =
          (TableB.projConj (unitarySU 2 n K 6) ⟨g a₁, hgN a₁⟩) ^ k *
            (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ j := by
      intro a
      have hu3 : (TableB.projConj (unitarySU 2 n K 6) ⟨g a₁, hgN a₁⟩) ^ 3 = 1 :=
        hAb.2 _ hg₁Ab
      have hv3 : (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ 3 = 1 :=
        hAb.2 _ hMA
      obtain ⟨k, hk⟩ := hρrepr a
      refine ⟨k % 3, (3 - j a % 3) % 3, Nat.mod_lt _ (by norm_num),
        Nat.mod_lt _ (by norm_num), ?_⟩
      have hkey : (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) =
          (TableB.projConj (unitarySU 2 n K 6) ⟨g a₁, hgN a₁⟩) ^ k *
            ((TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ (j a))⁻¹ := by
        rw [← hk, hgρ a]
        group
      rw [hkey, pow_eq_pow_mod k hu3, pow_eq_pow_mod (j a) hv3,
        inv_pow_eq_pow_three hv3 (Nat.mod_lt _ (by norm_num))]
    have hle9 : Nat.card Ab ≤ 9 :=
      card_le_nine Ab (TableB.projConj (unitarySU 2 n K 6) ⟨g a₁, hgN a₁⟩)
        (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)
        (fun a ha => by
          obtain ⟨k, j, hk, hj, heq⟩ := hspan ⟨a, ha⟩
          exact ⟨k, j, hk, hj, heq⟩)
    omega
  · push Not at hcase
    have hspan : ∀ a : Ab, ∃ k j : ℕ, k < 3 ∧ j < 3 ∧
        (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) =
          (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ k * 1 ^ j := by
      intro a
      have hscal : TableB.projConj (unitarySU 2 n K 6) ⟨g a, hgN a⟩ = 1 := by
        have hz := hcase a
        have he : (⟨g a, hgN a⟩ :
            Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
            ⟨g a, TableB.scalar_mem_normalizer _ hz⟩ := Subtype.ext rfl
        rw [he, TableB.projConj_of_scalar _ hz]
      have hv3 : (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ 3 = 1 :=
        hAb.2 _ hMA
      have haeq : (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) =
          (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ ((3 - j a % 3) % 3) := by
        have h1 : (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) *
            (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ (j a) = 1 := by
          rw [← hgρ a, hscal]
        have h2 : (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) =
            ((TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ (j a))⁻¹ := by
          calc (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) =
              (a : MulAut (LargeEvenProj (unitarySU 2 n K 6))) *
                (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ (j a) *
                ((TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ (j a))⁻¹ := by group
            _ = 1 * ((TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ (j a))⁻¹ := by
                  rw [h1]
            _ = ((TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ (j a))⁻¹ := by
                  rw [one_mul]
        rw [h2, pow_eq_pow_mod (j a) hv3,
          inv_pow_eq_pow_three hv3 (Nat.mod_lt _ (by norm_num))]
      refine ⟨(3 - j a % 3) % 3, 0, Nat.mod_lt _ (by norm_num), by norm_num, ?_⟩
      rw [haeq, pow_zero, mul_one]
    have hle9 : Nat.card Ab ≤ 9 :=
      card_le_nine Ab (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) 1
        (fun a ha => by
          obtain ⟨k, j, hk, hj, heq⟩ := hspan ⟨a, ha⟩
          exact ⟨k, j, hk, hj, heq⟩)
    omega

theorem exists_fieldStruct [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))}
    (hAb : CFSG.Open.IsElemAbelian 3 Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)))
    (hcard : Nat.card Ab = 27) {M : GL (Fin 6) K}
    (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {l : Kˣ}
    (hMu : M ∈ primeFormUnitary hKd (idGram K 6))
    (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l) (hl : ∀ c : Kˣ, c ^ 3 ≠ l)
    (hMA : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ ∈ Ab) :
    ∃ (X Z : GL (Fin 6) K)
      (hXN : X ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
      (hZN : Z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) (ζ : Kˣ),
      X ∈ primeFormUnitary hKd (idGram K 6) ∧ Z ∈ primeFormUnitary hKd (idGram K 6) ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨X, hXN⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ ∈ Ab ∧
      X ^ 3 = 1 ∧ Z ^ 3 = 1 ∧ IsPrimitiveRoot ζ 3 ∧
      X * M = GeneralLinearGroup.scalar (Fin 6) ζ * (M * X) ∧ X * Z = Z * X ∧ M * Z = Z * M ∧
      Z ∉ LargeEvenScalars (Fin 6) K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have h := congrArg Prod.fst he
    simp only at h
    omega
  obtain ⟨χ, hχ3, hχcomm⟩ := exists_commChar hKd hK hpq hAb hAbI hMN hMA
  obtain ⟨a₁, hζne⟩ := chi_nontrivial hKd hK hpq hAb hAbI hcard hMN hMu hM3 hl hMA hχ3 hχcomm
  have hζ3 : (χ a₁) ^ 3 = 1 := hχ3 a₁
  have hζprim : IsPrimitiveRoot (χ a₁) 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζ3 hζne)
  obtain ⟨X₀, hX₀N, hX₀u, hX₀eq⟩ := exists_unitary_lift hKd hAbI a₁.2
  have hX₀comm : X₀ * M = GeneralLinearGroup.scalar (Fin 6) (χ a₁) * (M * X₀) :=
    hχcomm a₁ X₀ hX₀N hX₀eq
  have hX₀3scal : X₀ ^ 3 ∈ LargeEvenScalars (Fin 6) K := by
    have hproj : TableB.projConj (unitarySU 2 n K 6)
        ((⟨X₀, hX₀N⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) ^ 3) =
        1 := by
      rw [map_pow, hX₀eq, hAb.2 (a₁ : MulAut _) a₁.2]
    have h := mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq hp3 hpq hproj
    simpa using h
  obtain ⟨cX, hcX⟩ := hX₀3scal
  obtain ⟨jX, tX, hjX, htXu, hX3⟩ :=
    exists_normalized hKd hpq hMu hX₀u hM3 hl hcX.symm hζ3 hX₀comm
  let X : GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) tX⁻¹ * X₀ * M ^ jX
  have hzX : GeneralLinearGroup.scalar (Fin 6) tX⁻¹ ∈ LargeEvenScalars (Fin 6) K :=
    ⟨tX⁻¹, rfl⟩
  have hXN : X ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
    dsimp only [X]
    exact (Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).mul_mem
      ((Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).mul_mem
        (TableB.scalar_mem_normalizer _ hzX) hX₀N)
      ((Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).pow_mem hMN jX)
  have hXu : X ∈ primeFormUnitary hKd (idGram K 6) := by
    have hstXu : GeneralLinearGroup.scalar (Fin 6) tX⁻¹ ∈ primeFormUnitary hKd (idGram K 6) :=
      by simpa only [map_inv] using (primeFormUnitary hKd (idGram K 6)).inv_mem htXu
    dsimp only [X]
    exact (primeFormUnitary hKd (idGram K 6)).mul_mem
      ((primeFormUnitary hKd (idGram K 6)).mul_mem hstXu hX₀u)
      ((primeFormUnitary hKd (idGram K 6)).pow_mem hMu jX)
  have hXcomm : X * M = GeneralLinearGroup.scalar (Fin 6) (χ a₁) * (M * X) := by
    dsimp only [X]
    exact conj_key X₀ M (GeneralLinearGroup.scalar (Fin 6) tX⁻¹)
      (GeneralLinearGroup.scalar (Fin 6) (χ a₁)) jX
      (fun g => (TypeA.PGLTor.commute_scalar tX⁻¹ g).eq) hX₀comm
  have hXρ : TableB.projConj (unitarySU 2 n K 6) ⟨X, hXN⟩ =
      (a₁ : MulAut (LargeEvenProj (unitarySU 2 n K 6))) *
        (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ jX := by
    dsimp only [X]
    have hsplit : ((⟨GeneralLinearGroup.scalar (Fin 6) tX⁻¹ * X₀ * M ^ jX, hXN⟩ :
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) =
        (⟨GeneralLinearGroup.scalar (Fin 6) tX⁻¹,
            TableB.scalar_mem_normalizer _ hzX⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) *
          ⟨X₀, hX₀N⟩ * ⟨M, hMN⟩ ^ jX := by
      apply Subtype.ext
      rfl
    rw [hsplit, map_mul, map_mul, map_pow, TableB.projConj_of_scalar _ hzX, hX₀eq, one_mul]
  have hXAb : TableB.projConj (unitarySU 2 n K 6) ⟨X, hXN⟩ ∈ Ab := by
    rw [hXρ]
    exact Ab.mul_mem a₁.2 (Ab.pow_mem hMA jX)
  obtain ⟨χX, hχX3, hχXcomm⟩ := exists_commChar hKd hK hpq hAb hAbI hXN hXAb
  obtain ⟨aZ, haZne, hχMZ, hχXZ⟩ := exists_ne_one_ker_two hcard χ χX hχ3 hχX3
  obtain ⟨N, hNN', hNu, hNeq⟩ := exists_unitary_lift hKd hAbI aZ.2
  have hNM : N * M = M * N := by
    have h := hχcomm aZ N hNN' hNeq
    rwa [hχMZ, map_one, one_mul] at h
  have hNX : N * X = X * N := by
    have h := hχXcomm aZ N hNN' hNeq
    rwa [hχXZ, map_one, one_mul] at h
  have hN3scal : N ^ 3 ∈ LargeEvenScalars (Fin 6) K := by
    have hproj : TableB.projConj (unitarySU 2 n K 6)
        ((⟨N, hNN'⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) ^ 3) = 1 := by
      rw [map_pow, hNeq, hAb.2 (aZ : MulAut _) aZ.2]
    have h := mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq hp3 hpq hproj
    simpa using h
  obtain ⟨cN, hcN⟩ := hN3scal
  obtain ⟨jZ, tZ, hjZ, htZu, hZ3⟩ :=
    exists_normalized hKd hpq hMu hNu hM3 hl hcN.symm (by norm_num : (1 : Kˣ) ^ 3 = 1)
      (by rw [hNM, map_one, one_mul])
  let Z : GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) tZ⁻¹ * N * M ^ jZ
  have hzZ : GeneralLinearGroup.scalar (Fin 6) tZ⁻¹ ∈ LargeEvenScalars (Fin 6) K :=
    ⟨tZ⁻¹, rfl⟩
  have hZN : Z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := by
    dsimp only [Z]
    exact (Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).mul_mem
      ((Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).mul_mem
        (TableB.scalar_mem_normalizer _ hzZ) hNN')
      ((Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))).pow_mem hMN jZ)
  have hZu : Z ∈ primeFormUnitary hKd (idGram K 6) := by
    have hstZu : GeneralLinearGroup.scalar (Fin 6) tZ⁻¹ ∈ primeFormUnitary hKd (idGram K 6) :=
      by simpa only [map_inv] using (primeFormUnitary hKd (idGram K 6)).inv_mem htZu
    dsimp only [Z]
    exact (primeFormUnitary hKd (idGram K 6)).mul_mem
      ((primeFormUnitary hKd (idGram K 6)).mul_mem hstZu hNu)
      ((primeFormUnitary hKd (idGram K 6)).pow_mem hMu jZ)
  have hZρ : TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ =
      (aZ : MulAut (LargeEvenProj (unitarySU 2 n K 6))) *
        (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ jZ := by
    dsimp only [Z]
    have hsplit : ((⟨GeneralLinearGroup.scalar (Fin 6) tZ⁻¹ * N * M ^ jZ, hZN⟩ :
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) =
        (⟨GeneralLinearGroup.scalar (Fin 6) tZ⁻¹,
            TableB.scalar_mem_normalizer _ hzZ⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) *
          ⟨N, hNN'⟩ * ⟨M, hMN⟩ ^ jZ := by
      apply Subtype.ext
      rfl
    rw [hsplit, map_mul, map_mul, map_pow, TableB.projConj_of_scalar _ hzZ, hNeq, one_mul]
  have hZAb : TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ ∈ Ab := by
    rw [hZρ]
    exact Ab.mul_mem aZ.2 (Ab.pow_mem hMA jZ)
  have hZM : Z * M = M * Z := by
    dsimp only [Z]
    have h1 : Commute (GeneralLinearGroup.scalar (Fin 6) tZ⁻¹) M :=
      TypeA.PGLTor.commute_scalar tZ⁻¹ M
    have h2 : Commute N M := hNM
    exact ((h1.mul_left h2).mul_left ((Commute.refl M).pow_left jZ)).eq
  have hXZscaled : X * Z =
      GeneralLinearGroup.scalar (Fin 6) ((χ a₁) ^ jZ) * (Z * X) := by
    dsimp only [X, Z]
    simpa only [map_pow] using direct_key X N M (GeneralLinearGroup.scalar (Fin 6) tZ⁻¹)
      (GeneralLinearGroup.scalar (Fin 6) (χ a₁)) jZ
      (fun g => (TypeA.PGLTor.commute_scalar tZ⁻¹ g).eq)
      (fun g => (TypeA.PGLTor.commute_scalar (χ a₁) g).eq) hNX.symm hXcomm
  have hjZ0 : jZ = 0 := by
    by_contra hj
    have hj1 : jZ = 1 ∨ jZ = 2 := by omega
    have hprim : IsPrimitiveRoot ((χ a₁) ^ jZ) 3 := by
      rcases hj1 with rfl | rfl
      · simpa using hζprim
      · simpa using hζprim.pow_of_coprime 2 (by decide : Nat.Coprime 2 3)
    exact (false_of_cyclic_partner hl hM3 hZ3 hZM hprim hXZscaled).elim
  have hXZ : X * Z = Z * X := by
    rw [hjZ0] at hXZscaled
    simpa only [pow_zero, map_one, one_mul] using hXZscaled
  have hZρ' : TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ =
      (aZ : MulAut (LargeEvenProj (unitarySU 2 n K 6))) := by
    rw [hZρ, hjZ0, pow_zero, mul_one]
  have hZns : Z ∉ LargeEvenScalars (Fin 6) K := by
    intro hZsc
    have h1 : TableB.projConj (unitarySU 2 n K 6) ⟨Z, hZN⟩ = 1 := by
      have he : (⟨Z, hZN⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) =
          ⟨Z, TableB.scalar_mem_normalizer _ hZsc⟩ := Subtype.ext rfl
      rw [he, TableB.projConj_of_scalar _ hZsc]
    rw [hZρ'] at h1
    exact haZne (Subtype.ext h1)
  exact ⟨X, Z, hXN, hZN, χ a₁, hXu, hZu, hXAb, hZAb, hX3, hZ3, hζprim, hXcomm, hXZ,
    hZM.symm, hZns⟩

end CFSG.StandardType.UnitSixThreeKG

end
