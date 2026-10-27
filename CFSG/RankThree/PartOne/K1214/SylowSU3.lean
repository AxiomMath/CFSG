module

public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.RankThree.PartOne.K1214

theorem su3_card_factor {n e m p : ℕ} (hn : n + 2 = p ^ e * m) :
    (n + 1) ^ 3 * ((n + 1) ^ 2 - 1) * ((n + 1) ^ 3 + 1) =
      p ^ (2 * e) * ((n + 1) ^ 3 * n * (n * (n + 1) + 1) * m ^ 2) := by
  have h1 : (n + 1) ^ 2 - 1 = n * (n + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : (n + 1) ^ 3 + 1 = (n + 2) * (n * (n + 1) + 1) := by ring
  have h3 : (n + 2) ^ 2 = p ^ (2 * e) * m ^ 2 := by
    rw [hn, mul_pow, ← pow_mul, mul_comm e 2]
  rw [h1, h2]
  calc (n + 1) ^ 3 * (n * (n + 2)) * ((n + 2) * (n * (n + 1) + 1))
      = (n + 1) ^ 3 * n * (n * (n + 1) + 1) * (n + 2) ^ 2 := by ring
    _ = p ^ (2 * e) * ((n + 1) ^ 3 * n * (n * (n + 1) + 1) * m ^ 2) := by rw [h3]; ring

theorem su3_index_coprime {p e m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (he1 : 1 ≤ e) (hm : ¬ p ∣ m) (hn : n + 2 = p ^ e * m) :
    ¬ p ∣ (n + 1) ^ 3 * n * (n * (n + 1) + 1) * m ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hz : ((n : ZMod p) + 2) = 0 := by
    have : ((n + 2 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (by
        rw [hn]
        exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m)
    simpa using this
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      ·
        have h1 : p ∣ n + 1 := hp.dvd_of_dvd_pow h
        have h2 : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
        push_cast at h2
        have : (1 : ZMod p) = 0 := by linear_combination hz - h2
        exact one_ne_zero this
      ·
        have h2 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
        have h3 : ((2 : ℕ) : ZMod p) = 0 := by
          push_cast
          linear_combination hz - h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          ((ZMod.natCast_eq_zero_iff _ _).1 h3))
    ·
      have h2 : ((n * (n + 1) + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      push_cast at h2
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination h2 - ((n : ZMod p) - 1) * hz
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        ((ZMod.natCast_eq_zero_iff _ _).1 h3))
  · exact hm (hp.dvd_of_dvd_pow h)

section Torus

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K]

@[expose] def vec3 : Kˣ × Kˣ →* (Fin 3 → Kˣ) where
  toFun x := ![x.1, x.2, (x.1 * x.2)⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i <;> simp [mul_assoc, mul_comm, mul_left_comm]

theorem vec3_injective : Function.Injective (vec3 (K := K)) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [vec3, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

theorem diagU_mem_statedSU {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (d : Fin 3 → Kˣ)
    (hdet : ∏ i, d i = 1) (hd : ∀ i, d i ^ (2 ^ f + 1) = 1) :
    (diagU d : GL (Fin 3) K) ∈ StatedSU 3 (2 ^ f) K := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 3) (by norm_num)).1
  have hmem : (diagU d : GL (Fin 3) K) ∈ {A : GL (Fin 3) K |
      (A : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ f))ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1} := by
    refine ⟨?_, ?_⟩
    · rw [det_diagU, ← Units.coe_prod, hdet, Units.val_one]
    · have hmap : ((diagU d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ f) =
          Matrix.diagonal fun i => (d i : K) ^ 2 ^ f := by
        rw [diagU_val]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Matrix.diagonal_apply_ne _ hij, zero_pow (pow_ne_zero f two_ne_zero)]
      rw [hmap, diagU_val, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← pow_succ]
      have := congrArg (fun u : Kˣ => (u : K)) (hd i)
      simpa using this
  rw [← SetLike.mem_coe, h]
  exact hmem

@[expose] def piFinTwoMul (M : Type*) [Mul M] : (Fin 2 → M) ≃* M × M where
  toEquiv := piFinTwoEquiv fun _ => M
  map_mul' _ _ := rfl

theorem sylowShape_statedSU3 [Finite K] {f p e m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (he1 : 1 ≤ e) (hK : Nat.card K = (2 ^ f) ^ 2) (hQ : 2 ^ f + 1 = p ^ e * m) (hm : ¬ p ∣ m) :
    SylowShape p 2 e ↥(StatedSU 3 (2 ^ f) K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hpe : (p ^ e) ∣ 2 ^ f + 1 := ⟨m, hQ⟩
  have hdvdK : p ^ e ∣ Nat.card K - 1 := by
    rw [hK]
    have : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      obtain ⟨n, hn⟩ : ∃ n, 2 ^ f = n + 1 := ⟨2 ^ f - 1, by omega⟩
      rw [hn]
      have : (n + 1) ^ 2 = n * (n + 1 + 1) + 1 := by ring
      simp only [Nat.add_sub_cancel]
      exact Nat.sub_eq_of_eq_add this
    rw [this]
    exact Dvd.dvd.mul_left hpe _
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard := CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := K) hdvdK
  set μ : Subgroup Kˣ := rootsOfUnity (p ^ e) K with hμ
  set ι : (Kˣ × Kˣ) →* GL (Fin 3) K := diagUHom.comp vec3 with hι
  have hιinj : Function.Injective ι := fun x y h =>
    vec3_injective (diagU_injective (by simpa [hι, diagUHom] using h))
  set T3 : Subgroup (GL (Fin 3) K) := (μ.prod μ).map ι with hT3
  have hpow : ∀ u : Kˣ, u ^ (p ^ e) = 1 → u ^ (2 ^ f + 1) = 1 := fun u hu => by
    rw [hQ, pow_mul, hu, one_pow]
  have hle : T3 ≤ StatedSU 3 (2 ^ f) K := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : x.1 ^ (p ^ e) = 1 := (mem_rootsOfUnity _ _).1 hx.1
    have hx2 : x.2 ^ (p ^ e) = 1 := (mem_rootsOfUnity _ _).1 hx.2
    have hdet : ∏ i, vec3 x i = 1 := by
      rw [Fin.prod_univ_three]
      simp [vec3]
    have hd : ∀ i, vec3 x i ^ (2 ^ f + 1) = 1 := by
      intro i
      fin_cases i
      · simpa [vec3] using hpow _ hx1
      · simpa [vec3] using hpow _ hx2
      · simp [vec3, inv_pow, mul_pow, hpow _ hx1, hpow _ hx2]
    exact diagU_mem_statedSU hK (vec3 x) hdet hd
  set H : Subgroup (GL (Fin 3) K) := StatedSU 3 (2 ^ f) K with hH
  set T' : Subgroup ↥H := T3.subgroupOf H with hT'
  have hμprod : Nat.card (μ.prod μ : Subgroup (Kˣ × Kˣ)) = p ^ e * p ^ e := by
    rw [Nat.card_congr (Subgroup.prodEquiv μ μ).toEquiv, Nat.card_prod, hcard]
  have hT3card : Nat.card T3 = p ^ (2 * e) := by
    rw [hT3, Subgroup.card_map_of_injective hιinj, hμprod, two_mul, pow_add]
  have hT'card : Nat.card T' = p ^ (2 * e) := by
    rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hT3card]
  have hT'p : IsPGroup p ↥T' := IsPGroup.of_card hT'card
  have hQpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  obtain ⟨n, hn⟩ : ∃ n, 2 ^ f = n + 1 := ⟨2 ^ f - 1, by omega⟩
  have hn' : n + 2 = p ^ e * m := by
    have := hQ
    rw [hn] at this
    omega
  have hHcard : Nat.card ↥H = p ^ (2 * e) * ((n + 1) ^ 3 * n * (n * (n + 1) + 1) * m ^ 2) := by
    rw [hH, CFSG.SectionRank.OddCover.card_statedSU_three hK, hn]
    exact su3_card_factor hn'
  have hidx : ¬ p ∣ T'.index := by
    have h1 := Subgroup.card_mul_index T'
    rw [hT'card, hHcard] at h1
    have h2 : T'.index = (n + 1) ^ 3 * n * (n * (n + 1) + 1) * m ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h1
    rw [h2]
    exact su3_index_coprime hp hp2 hp3 he1 hm hn'
  have hcyc : IsCyclic ↥μ := inferInstance
  let φ2 : Multiplicative (ZMod (p ^ e)) ≃* ↥μ :=
    (((ZMod.ringEquivCongr hcard.symm).toAddEquiv).toMultiplicative).trans (zmodCyclicMulEquiv hcyc)
  let φ : ↥T' ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans
      ((Subgroup.equivMapOfInjective (μ.prod μ) ι hιinj).symm.trans
        ((Subgroup.prodEquiv μ μ).trans
          ((MulEquiv.prodCongr φ2.symm φ2.symm).trans (piFinTwoMul _).symm)))
  exact SylowShape.of_witness hp hT'p hidx φ

open CFSG.Assembly.LowTwoRank in
theorem sylowShape_of_psu3Model {X : Type} [Group X] [Finite X] {f p e m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (he1 : 1 ≤ e) (hQ : 2 ^ f + 1 = p ^ e * m) (hm : ¬ p ∣ m)
    (hX : StatedClassicalModel X .PSU 3 2 f) : SylowShape p 2 e X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
  have hker := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 3)
    (by norm_num)).2.2
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ f) K)) := by
    rw [hker]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h.trans (Nat.gcd_dvd_left _ _)))
  exact SylowShape.of_mulEquiv φ (SylowShape.quotient hp _ hN
    (sylowShape_statedSU3 hp hp2 hp3 he1 hK hQ hm))

end Torus

end CFSG.RankThree.PartOne.K1214
