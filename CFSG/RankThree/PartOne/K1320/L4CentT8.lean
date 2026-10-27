module

public import CFSG.RankThree.PartOne.K1320.L4Torus

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_algebraMap_of_pow_eq_one {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K - 1)
    {a : (Qext K)ˣ} (ha : a ^ r = 1) :
    ∃ a₀ : Kˣ, Units.map (algebraMap K (Qext K)).toMonoidHom a₀ = a := by
  have : NeZero r := ⟨hr.ne_zero⟩
  let φ : Kˣ →* (Qext K)ˣ := Units.map (algebraMap K (Qext K)).toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective (algebraMap K (Qext K)).injective
  let f : rootsOfUnity r K → rootsOfUnity r (Qext K) := fun ζ =>
    ⟨φ ζ, by
      rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity r _).1 ζ.2, map_one]⟩
  have hf : Function.Injective f := fun ζ ζ' h =>
    Subtype.ext (hφ (congrArg Subtype.val h))
  have hcard : Nat.card (rootsOfUnity r (Qext K)) ≤ Nat.card (rootsOfUnity r K) := by
    rw [natCard_rootsOfUnity_eq hr hrq]
    exact card_rootsOfUnity (Qext K) r
  obtain ⟨ζ, hζ⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨a, (mem_rootsOfUnity r a).2 ha⟩
  exact ⟨ζ, congrArg Subtype.val hζ⟩

theorem eq_of_mem_centralizer_T8 {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hr : r.Prime) (_hr2 : r ≠ 2) (hrq : r ∣ Nat.card K - 1)
    {g : ↥(M8 K)} (hgr : g ∈ (blk8M (K := K)).range)
    (hg : g ∈ Subgroup.centralizer (T8 p K : Set ↥(M8 K))) (hgp : g ^ r = 1) :
    g ∈ Rr K r := by
  obtain ⟨X, rfl⟩ := hgr
  obtain ⟨m, hmp, hm1, -⟩ := exists_root_not_mem hp hp2 hpq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hmp
    exact zero_ne_one hmp
  let z : (Qext K)ˣ := Units.mk0 m hm0
  have hzp : z ^ p = 1 := Units.ext (by simpa [z] using hmp)
  let zr : rootsOfUnity p (Qext K) := ⟨z, (mem_rootsOfUnity p z).2 hzp⟩
  have hmemT : (⟨d8Emb ((zr, 1) : D8Mod p (Qext K)), d8Emb_mem_M8 hp hp2 hpq _⟩ : ↥(M8 K)) ∈
      T8 p K := Subgroup.mem_subgroupOf.2 ⟨(zr, 1), rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.1 hg _ hmemT
  have hc : ∀ v : QV K (Fin 2),
      d8Emb ((zr, 1) : D8Mod p (Qext K)) ((X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec v) =
        (X : Matrix (Fin 2) (Fin 2) (Qext K)).mulVec (d8Emb ((zr, 1) : D8Mod p (Qext K)) v) := by
    intro v
    have h1 := congrArg (fun y : ↥(M8 K) => (y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) hcomm
    simpa [blk8M_apply] using h1
  have hm1' : m - 1 ≠ 0 := sub_ne_zero.2 hm1
  have e01 : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 1 = 0 := by
    have h0 := congrFun (hc (Pi.single 1 1)) 0
    simp [d8Emb_apply_zero, d8Emb_apply_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      zr, z] at h0
    have h2 : (m - 1) * (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 1 = 0 := by
      linear_combination h0
    exact (mul_eq_zero.1 h2).resolve_left hm1'
  have e10 : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 0 = 0 := by
    have h0 := congrFun (hc (Pi.single 0 1)) 1
    simp [d8Emb_apply_zero, d8Emb_apply_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      zr, z] at h0
    have h2 : (m - 1) * (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 0 = 0 := by
      linear_combination -h0
    exact (mul_eq_zero.1 h2).resolve_left hm1'
  have hdet : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0 * (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 1
      = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe X
    rw [Matrix.det_fin_two, e01, e10] at h
    simpa using h
  have hA : (X : Matrix (Fin 2) (Fin 2) (Qext K)) =
      Matrix.diagonal ![(X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0,
        (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e01, e10]
  have hXr : X ^ r = 1 := blk8M_injective (by rw [map_pow, map_one]; exact hgp)
  have h00 : ((X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0) ^ r = 1 := by
    have h1 : ((X ^ r : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) :
        Matrix (Fin 2) (Fin 2) (Qext K)) = 1 := by
      rw [hXr]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, hA, Matrix.diagonal_pow] at h1
    simpa using congrFun (congrFun h1 0) 0
  have hu : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  let a : (Qext K)ˣ := Units.mk0 _ hu
  have ha : a ^ r = 1 := Units.ext (by simpa [a] using h00)
  obtain ⟨a₀, ha₀⟩ := exists_algebraMap_of_pow_eq_one hr hrq ha
  have hφ : Function.Injective (Units.map (algebraMap K (Qext K)).toMonoidHom) :=
    Units.map_injective (algebraMap K (Qext K)).injective
  have ha₀r : a₀ ^ r = 1 := by
    apply hφ
    rw [map_pow, ha₀, ha, map_one]
  have hmap : algebraMap K (Qext K) (a₀ : K) = (X : Matrix (Fin 2) (Fin 2) (Qext K)) 0 0 := by
    simpa [a] using congrArg Units.val ha₀
  have hinv : algebraMap K (Qext K) (a₀ : K) * algebraMap K (Qext K) ((a₀⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h11 : (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 1 =
      algebraMap K (Qext K) ((a₀⁻¹ : Kˣ) : K) := by
    linear_combination (algebraMap K (Qext K) ((a₀⁻¹ : Kˣ) : K) *
      (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 1) * hmap +
      algebraMap K (Qext K) ((a₀⁻¹ : Kˣ) : K) * hdet -
      (X : Matrix (Fin 2) (Fin 2) (Qext K)) 1 1 * hinv
  have hXd : X = diagSL2 a₀ := by
    apply Subtype.ext
    show (X : Matrix (Fin 2) (Fin 2) (Qext K)) = (diagSLmat a₀ : Matrix (Fin 2) (Fin 2) (Qext K))
    rw [coe_diagSLmat]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using hmap.symm
    · simpa using e01
    · simpa using e10
    · simpa using h11
  rw [hXd]
  exact ⟨a₀, (mem_rootsOfUnity r a₀).2 ha₀r, rfl⟩

end CFSG.RankThree.PartOne.K1320
