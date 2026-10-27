module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

theorem ggKGTj_WSL_sq_one {K : Type} [Field K] [CharP K 2] :
    (WSL : SL2 K) * WSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

theorem ggKGTj_WSL_inv_eq {K : Type} [Field K] [CharP K 2] :
    (WSL : SL2 K)⁻¹ = WSL :=
  inv_eq_of_mul_eq_one_right ggKGTj_WSL_sq_one

theorem ggKGTj_exists_omega {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    ∃ ω : K, σ ω ≠ ω := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsCyclic Kˣ := inferInstance
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, ∀ x : Kˣ, x ∈ Subgroup.zpowers g := IsCyclic.exists_generator
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' (Subgroup.zpowers g)).2 hg
  have horder : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_zpowers_eq_top htop, Nat.card_units, hK]
  refine ⟨(g : K), fun hω => ?_⟩
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    rw [hK, hn0] at this; norm_num at this
  have hgpow : g ^ (2 ^ n) = g := by
    apply Units.ext
    change ((g : K) ^ (2 ^ n)) = (g : K)
    rw [← hσ (g : K)]
    exact hω
  have hdvd : orderOf g ∣ 2 ^ n - 1 := by
    apply orderOf_dvd_iff_pow_eq_one.2
    have h1 : g ^ (2 ^ n - 1) * g = 1 * g := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), hgpow]
    exact mul_right_cancel h1
  rw [horder] at hdvd
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hpos : 0 < 2 ^ n - 1 := by omega
  have hle := Nat.le_of_dvd hpos hdvd
  have hx : 2 ^ n < (2 ^ n) ^ 2 := by
    rw [pow_two]
    simpa using Nat.mul_lt_mul_of_pos_left h1 (Nat.two_pow_pos n)
  omega

noncomputable def ggKGTj_FrEquiv {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    AlgebraicClosure K ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective Fr ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (n := 2 ^ n) (by positivity)
    exact ⟨x, by rw [hFr, hx]⟩⟩

noncomputable def ggKGTj_F {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    Subfield (AlgebraicClosure K) :=
  fixSubfield (ggKGTj_FrEquiv Fr hFr)

theorem ggKGTj_pow_card' {K : Type} [Field K] [Finite K] (ω : K) :
    ω ^ Nat.card K = ω := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card ω

theorem ggKGTj_omega_add_mem_fix {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (ω : K) :
    algebraMap K (AlgebraicClosure K) ω +
      algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n) ∈ ggKGTj_F Fr hFr := by
  have hpow : (algebraMap K (AlgebraicClosure K) ω) ^ (2 ^ n * 2 ^ n) =
      algebraMap K (AlgebraicClosure K) ω := by
    rw [← map_pow, show ω ^ (2 ^ n * 2 ^ n) = ω from by
      rw [show 2 ^ n * 2 ^ n = Nat.card K by rw [hK]; ring]
      exact ggKGTj_pow_card' ω]
  rw [ggKGTj_F, mem_fixSubfield]
  change Fr (algebraMap K (AlgebraicClosure K) ω + algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n)) =
    algebraMap K (AlgebraicClosure K) ω + algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n)
  rw [map_add, map_pow, hFr, ← pow_mul, hpow, add_comm]

theorem ggKGTj_exists_s {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (ω : K) :
    ∃ s : AlgebraicClosure K, Fr s = s ∧
      s * s = (algebraMap K (AlgebraicClosure K) ω +
        algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n))⁻¹ := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hmem := ggKGTj_omega_add_mem_fix hK Fr hFr ω
  have ht : Fr (algebraMap K (AlgebraicClosure K) ω +
      algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n)) =
      algebraMap K (AlgebraicClosure K) ω + algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n) := by
    have h := (mem_fixSubfield (ggKGTj_FrEquiv Fr hFr)).1 hmem
    change Fr (algebraMap K (AlgebraicClosure K) ω +
      algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n)) = _ at h
    exact h
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) ω + algebraMap K (AlgebraicClosure K) ω ^ (2 ^ n))⁻¹
    (n := 2) (by norm_num)
  refine ⟨s, ?_, ?_⟩
  · have h1 : (Fr s) ^ 2 = s ^ 2 := by
      rw [← map_pow, hs, map_inv₀, ht]
    exact CharTwo.sq_injective h1
  · simpa [sq] using hs

theorem ggKGTj_mem_F {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (x : AlgebraicClosure K) :
    x ∈ ggKGTj_F Fr hFr ↔ x ^ (2 ^ n) = x := by
  rw [ggKGTj_F, mem_fixSubfield]
  change Fr x = x ↔ x ^ (2 ^ n) = x
  rw [hFr]

theorem ggKGTj_card_F {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    Nat.card ↥(ggKGTj_F Fr hFr) = 2 ^ n := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have h2 : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    rw [hK, hn0] at h2
    norm_num at h2
  have hn1 : 1 < 2 ^ n := Nat.one_lt_two_pow hn.ne'
  let P : Polynomial (AlgebraicClosure K) := Polynomial.X ^ (2 ^ n) - Polynomial.X
  have hPnd : P.natDegree = 2 ^ n := by
    have hlt : (Polynomial.X : Polynomial (AlgebraicClosure K)).natDegree <
        ((Polynomial.X : Polynomial (AlgebraicClosure K)) ^ (2 ^ n)).natDegree := by
      rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
      exact hn1
    change ((Polynomial.X : Polynomial (AlgebraicClosure K)) ^ (2 ^ n) -
      (Polynomial.X : Polynomial (AlgebraicClosure K))).natDegree = 2 ^ n
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hPne : P ≠ 0 := by
    intro h
    rw [h] at hPnd
    simp at hPnd
    exact (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)) hPnd.symm
  have heval : ∀ x : AlgebraicClosure K, Polynomial.eval x P = x ^ (2 ^ n) - x := by
    intro x; simp [P]
  have hroot : ∀ x : AlgebraicClosure K, x ∈ ggKGTj_F Fr hFr ↔ P.IsRoot x := by
    intro x
    rw [ggKGTj_mem_F Fr hFr x, Polynomial.IsRoot.def, heval x, sub_eq_zero]
  have hset : ∀ x : AlgebraicClosure K,
      x ∈ ggKGTj_F Fr hFr ↔ x ∈ P.roots.toFinset :=
    fun x => (hroot x).trans (Multiset.mem_toFinset.trans (Polynomial.mem_roots hPne)).symm
  have hcardGF : Nat.card ↥(ggKGTj_F Fr hFr) = P.roots.toFinset.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hupper : Nat.card ↥(ggKGTj_F Fr hFr) ≤ 2 ^ n := by
    rw [hcardGF]
    refine (Multiset.toFinset_card_le P.roots).trans ?_
    rw [← hPnd]
    exact Polynomial.card_roots' P
  have hcard2 : Nat.card K = 2 ^ (2 * n) := by
    calc Nat.card K = (2 ^ n) ^ 2 := hK
      _ = 2 ^ (n * 2) := by rw [← pow_mul]
      _ = 2 ^ (2 * n) := by rw [show n * 2 = 2 * n by ring]
  obtain ⟨_, _, _, _, _, hAll⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) (p := 2) (n := 2 * n) Nat.prime_two (by omega) hcard2
  have hσ2 : σ ^ 2 = 1 := by
    rw [pow_two]
    ext c
    show σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, show 2 ^ n * 2 ^ n = Nat.card K by rw [hK]; ring,
      ggKGTj_pow_card' c]
  have hσne : σ ≠ 1 := by
    intro h
    obtain ⟨ω, hω⟩ := ggKGTj_exists_omega hK hσ
    exact hω (by rw [h]; rfl)
  have horder2 : orderOf σ = 2 := orderOf_eq_prime hσ2 hσne
  have hA : Nat.card ↥(Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, horder2]
  obtain ⟨S, hS, hScard⟩ := (hAll (Subgroup.zpowers σ)).2
  have hSsub : (S : Set K) ⊆ fixSubfield σ := by
    intro a ha
    rw [hS] at ha
    exact ha σ (Subgroup.mem_zpowers σ)
  have hSsub' : ∀ a : ↥S, σ a.1 = a.1 := fun a => (mem_fixSubfield σ).1 (hSsub a.2)
  have hScard' : Nat.card ↥S = 2 ^ n := by
    rw [hScard, hA, Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]
  have hinj : Function.Injective (fun a : ↥S =>
      (⟨algebraMap K (AlgebraicClosure K) a.1, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def, heval]
        rw [sub_eq_zero, ← map_pow, ← hσ a.1, hSsub' a]⟩ : ↥(P.roots.toFinset))) := by
    intro a b hab
    apply Subtype.ext
    exact (algebraMap K (AlgebraicClosure K)).injective (congrArg Subtype.val hab)
  have hle : Nat.card ↥S ≤ Nat.card ↥(P.roots.toFinset) :=
    Nat.card_le_card_of_injective _ hinj
  have hlow : 2 ^ n ≤ Nat.card ↥(ggKGTj_F Fr hFr) := by
    rw [← hScard', hcardGF]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hle
  exact le_antisymm hupper hlow

noncomputable def ggKGTj_Pmat {K : Type} [Field K] {n : ℕ}
    (s ω : AlgebraicClosure K) : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K) :=
  s • !![1, ω; 1, ω ^ (2 ^ n)]

theorem ggKGTj_Pmat_det {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (s ω : AlgebraicClosure K)
    (ht : ω + ω ^ (2 ^ n) ≠ 0) (hss : s * s = (ω + ω ^ (2 ^ n))⁻¹) :
    Matrix.det (ggKGTj_Pmat (n := n) s ω) = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h2 : (2 : AlgebraicClosure K) = 0 := CharP.cast_eq_zero (AlgebraicClosure K) 2
  have hdet : Matrix.det (!![1, ω; 1, ω ^ (2 ^ n)] : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) =
      ω ^ (2 ^ n) + ω := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    rw [mul_one, one_mul, sub_eq_add_neg, CharTwo.neg_eq]
  rw [ggKGTj_Pmat, Matrix.det_smul, Fintype.card_fin, hdet, pow_two]
  rw [hss, show ω ^ (2 ^ n) + ω = ω + ω ^ (2 ^ n) from add_comm _ _, inv_mul_cancel₀ ht]

theorem ggKGTj_Pmat_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    {s ω : AlgebraicClosure K} (hs : Fr s = s) (hω : Fr ω = ω ^ (2 ^ n))
      (hω2 : Fr (ω ^ (2 ^ n)) = ω) :
    Matrix.map (ggKGTj_Pmat (n := n) s ω) Fr =
      (WSL : SL2 (AlgebraicClosure K)).1 * ggKGTj_Pmat (n := n) s ω := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ggKGTj_Pmat, WSL, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, hs, hω, hω2, CharTwo.neg_eq]

theorem ggKGTj_mem_range_mapF {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (Y : SL2 (AlgebraicClosure K))
    (hY : Matrix.SpecialLinearGroup.map Fr Y = Y) :
    Y ∈ (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr))).range := by
  have hYv : (Matrix.SpecialLinearGroup.map Fr Y :
      Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) = Y.1 := congrArg Subtype.val hY
  have hmem : ∀ i j, Y.1 i j ∈ ggKGTj_F Fr hFr := by
    intro i j
    rw [ggKGTj_F, mem_fixSubfield]
    change Fr (Y.1 i j) = Y.1 i j
    have h := congrFun (congrFun hYv i) j
    simpa [Matrix.map_apply] using h
  let Y' : Matrix (Fin 2) (Fin 2) ↥(ggKGTj_F Fr hFr) := fun i j => ⟨Y.1 i j, hmem i j⟩
  have hmap : Matrix.map Y' (Subfield.subtype (ggKGTj_F Fr hFr)) =
      (Y : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) := by
    ext i j; rfl
  have hY'det : Y'.det = 1 := by
    apply (Subfield.subtype (ggKGTj_F Fr hFr)).injective
    rw [RingHom.map_det]
    change (Matrix.map Y' (Subfield.subtype (ggKGTj_F Fr hFr))).det = _
    rw [hmap, map_one]
    exact Y.property
  exact ⟨⟨Y', hY'det⟩, Subtype.ext hmap⟩

theorem ggKGTj_range_mapF_eq_closure {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr))).range =
      Subgroup.closure (Set.range (fun c : ↥(ggKGTj_F Fr hFr) =>
        Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (uSL c)) ∪
      Set.range (fun c : ↥(ggKGTj_F Fr hFr) =>
        Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (vSL c))) := by
  have htop : Subgroup.closure
      (Set.range (uSL : ↥(ggKGTj_F Fr hFr) → SL2 ↥(ggKGTj_F Fr hFr)) ∪
       Set.range (vSL : ↥(ggKGTj_F Fr hFr) → SL2 ↥(ggKGTj_F Fr hFr))) = ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := ↥(ggKGTj_F Fr hFr))
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨uSL c, Or.inl ⟨c, rfl⟩, rfl⟩
    · exact ⟨vSL c, Or.inr ⟨c, rfl⟩, rfl⟩

noncomputable def ggKGTj_P {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (s ω : AlgebraicClosure K)
    (ht : ω + ω ^ (2 ^ n) ≠ 0) (hss : s * s = (ω + ω ^ (2 ^ n))⁻¹) :
    SL2 (AlgebraicClosure K) :=
  ⟨ggKGTj_Pmat (n := n) s ω, ggKGTj_Pmat_det hK s ω ht hss⟩

theorem ggKGTj_P_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    {s ω : AlgebraicClosure K} (hs : Fr s = s) (hω : Fr ω = ω ^ (2 ^ n))
      (hω2 : Fr (ω ^ (2 ^ n)) = ω)
    (ht : ω + ω ^ (2 ^ n) ≠ 0) (hss : s * s = (ω + ω ^ (2 ^ n))⁻¹) :
    Matrix.SpecialLinearGroup.map Fr (ggKGTj_P hK s ω ht hss) =
      WSL * ggKGTj_P hK s ω ht hss := by
  apply Subtype.ext
  exact ggKGTj_Pmat_pow hK Fr hs hω hω2

theorem ggKGTj_uSL_mul_self {K : Type} [Field K] [CharP K 2] (c : K) :
    (uSL c : SL2 K) * uSL c = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem ggKGTj_vSL_mul_self {K : Type} [Field K] [CharP K 2] (c : K) :
    (vSL c : SL2 K) * vSL c = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem ggKGTj_subtype_fix {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (c : ↥(ggKGTj_F Fr hFr)) :
    Fr ((Subfield.subtype (ggKGTj_F Fr hFr)) c) =
      (Subfield.subtype (ggKGTj_F Fr hFr)) c := by
  have h := (mem_fixSubfield (ggKGTj_FrEquiv Fr hFr)).1 c.property
  change Fr ((Subfield.subtype (ggKGTj_F Fr hFr)) c) = _ at h
  exact h

theorem ggKGTj_conj_mem {K : Type} [Field K] [CharP (AlgebraicClosure K) 2]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (P : SL2 (AlgebraicClosure K))
    (hPq : Matrix.SpecialLinearGroup.map Fr P = WSL * P) {g : SL2 (AlgebraicClosure K)}
    (hg2 : g * g = 1) (hgf : Matrix.SpecialLinearGroup.map Fr g = g) :
    (P * g * P⁻¹) * (P * g * P⁻¹) = 1 ∧
      WSL * Matrix.SpecialLinearGroup.map Fr (P * g * P⁻¹) * WSL = P * g * P⁻¹ := by
  constructor
  · rw [show (P * g * P⁻¹) * (P * g * P⁻¹) = P * (g * g) * P⁻¹ from by group, hg2]
    group
  · rw [map_mul, map_mul, map_inv, hPq, hgf]
    rw [show (WSL * P)⁻¹ = P⁻¹ * WSL by rw [mul_inv_rev, ggKGTj_WSL_inv_eq]]
    rw [show WSL * (WSL * P * g * (P⁻¹ * WSL)) * WSL =
        (WSL * WSL) * P * g * P⁻¹ * (WSL * WSL) from by group]
    rw [ggKGTj_WSL_sq_one, one_mul, mul_one]

theorem ggKGTj_D_gen {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (M : SL2 (AlgebraicClosure K))
    (hM : WSL * Matrix.SpecialLinearGroup.map Fr M * WSL = M) :
    M ∈ Subgroup.closure {X : SL2 (AlgebraicClosure K) | X * X = 1 ∧
      WSL * Matrix.SpecialLinearGroup.map Fr X * WSL = X} := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ω₀, hω₀⟩ := ggKGTj_exists_omega hK hσ
  obtain ⟨s, hs, hss⟩ := ggKGTj_exists_s hK Fr hFr ω₀
  have hωne : Fr (algebraMap K (AlgebraicClosure K) ω₀) ≠ algebraMap K (AlgebraicClosure K) ω₀ := by
    intro h
    apply hω₀
    have h1 : algebraMap K (AlgebraicClosure K) (σ ω₀) =
        Fr (algebraMap K (AlgebraicClosure K) ω₀) := by
      rw [hσ, map_pow, hFr]
    exact (algebraMap K (AlgebraicClosure K)).injective (by rw [h1, h])
  have ht : algebraMap K (AlgebraicClosure K) ω₀ +
      (algebraMap K (AlgebraicClosure K) ω₀) ^ (2 ^ n) ≠ 0 := by
    intro h
    apply hωne
    have h2 : (2 : AlgebraicClosure K) = 0 := CharP.cast_eq_zero (AlgebraicClosure K) 2
    have h' : (algebraMap K (AlgebraicClosure K) ω₀) ^ (2 ^ n) =
        algebraMap K (AlgebraicClosure K) ω₀ := by
      linear_combination h - (algebraMap K (AlgebraicClosure K) ω₀) * h2
    rw [hFr, h']
  have hω2 : Fr ((algebraMap K (AlgebraicClosure K) ω₀) ^ (2 ^ n)) =
      algebraMap K (AlgebraicClosure K) ω₀ := by
    rw [hFr, ← pow_mul, show 2 ^ n * 2 ^ n = Nat.card K by rw [hK]; ring, ← map_pow,
      ggKGTj_pow_card' ω₀]
  let P : SL2 (AlgebraicClosure K) := ggKGTj_P hK s (algebraMap K (AlgebraicClosure K) ω₀) ht hss
  have hPq : Matrix.SpecialLinearGroup.map Fr P = WSL * P :=
    ggKGTj_P_pow hK Fr hs (hFr _) hω2 ht hss
  have hMq : Matrix.SpecialLinearGroup.map Fr M = WSL * M * WSL := by
    have h := congrArg (fun X : SL2 (AlgebraicClosure K) => WSL * X * WSL) hM
    rw [show WSL * (WSL * Matrix.SpecialLinearGroup.map Fr M * WSL) * WSL =
        Matrix.SpecialLinearGroup.map Fr M from ?_] at h
    · exact h
    · rw [show WSL * (WSL * Matrix.SpecialLinearGroup.map Fr M * WSL) * WSL =
          (WSL * WSL) * Matrix.SpecialLinearGroup.map Fr M * (WSL * WSL) from by group,
        ggKGTj_WSL_sq_one, one_mul, mul_one]
  let Y : SL2 (AlgebraicClosure K) := P⁻¹ * M * P
  have hYfix : Matrix.SpecialLinearGroup.map Fr Y = Y := by
    rw [show Y = P⁻¹ * M * P from rfl, map_mul, map_mul, map_inv, hPq, hMq]
    rw [show (WSL * P)⁻¹ = P⁻¹ * WSL by rw [mul_inv_rev, ggKGTj_WSL_inv_eq]]
    rw [show P⁻¹ * WSL * (WSL * M * WSL) * (WSL * P) =
        P⁻¹ * (WSL * WSL) * M * (WSL * WSL) * P from by group,
      ggKGTj_WSL_sq_one]
    group
  have hYmem : Y ∈ (Matrix.SpecialLinearGroup.map
      (Subfield.subtype (ggKGTj_F Fr hFr))).range := ggKGTj_mem_range_mapF Fr hFr Y hYfix
  let GensF : Set (SL2 (AlgebraicClosure K)) :=
    Set.range (fun c : ↥(ggKGTj_F Fr hFr) =>
      Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (uSL c)) ∪
    Set.range (fun c : ↥(ggKGTj_F Fr hFr) =>
      Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (vSL c))
  have hYcl : Y ∈ Subgroup.closure GensF := by
    rw [← ggKGTj_range_mapF_eq_closure Fr hFr]; exact hYmem
  have hPY : (MulAut.conj P) Y ∈ Subgroup.closure ((MulAut.conj P) '' GensF) := by
    have h : (MulAut.conj P).toMonoidHom Y ∈
        (Subgroup.closure GensF).map (MulAut.conj P).toMonoidHom :=
      Subgroup.mem_map.2 ⟨Y, hYcl, rfl⟩
    rwa [MonoidHom.map_closure] at h
  have hM_eq : M = (MulAut.conj P) Y := by
    show M = P * Y * P⁻¹
    simp only [Y]; group
  rw [hM_eq]
  refine Subgroup.closure_mono ?_ hPY
  rintro X ⟨g, hg, rfl⟩
  rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hg2 : (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (uSL c)) *
        (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (uSL c)) = 1 := by
      rw [CFSG.LieType.Chevalley.map_uSL, ggKGTj_uSL_mul_self]
    have hgf : Matrix.SpecialLinearGroup.map Fr
        (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (uSL c)) =
        Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (uSL c) := by
      rw [CFSG.LieType.Chevalley.map_uSL, CFSG.LieType.Chevalley.map_uSL,
        ggKGTj_subtype_fix Fr hFr c]
    exact ggKGTj_conj_mem Fr P hPq hg2 hgf
  · have hg2 : (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (vSL c)) *
        (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (vSL c)) = 1 := by
      rw [CFSG.LieType.Chevalley.map_vSL, ggKGTj_vSL_mul_self]
    have hgf : Matrix.SpecialLinearGroup.map Fr
        (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (vSL c)) =
        Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) (vSL c) := by
      rw [CFSG.LieType.Chevalley.map_vSL, CFSG.LieType.Chevalley.map_vSL,
        ggKGTj_subtype_fix Fr hFr c]
    exact ggKGTj_conj_mem Fr P hPq hg2 hgf


end CFSG.StandardType
