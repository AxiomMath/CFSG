module

public import CFSG.RankThree.PartOne.Q1327T.Item7Cover
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank

section Block

variable {K : Type} [Field K]

theorem block_of_commute_diagU {d : Fin 3 → Kˣ} (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2)
    {g : GL (Fin 3) K} (hg : g * diagU d = diagU d * g) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  have hm : (g : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal (fun i => (d i : K)) =
      Matrix.diagonal (fun i => (d i : K)) * (g : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hg
    simpa [diagU_val] using this
  have key : ∀ i j, (g : Matrix (Fin 3) (Fin 3) K) i j * (d j : K) =
      (d i : K) * (g : Matrix (Fin 3) (Fin 3) K) i j := fun i j => by
    have := congrFun (congrFun hm i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hne : (d 0 : K) - d 2 ≠ 0 := sub_ne_zero.2 fun h => h02 (Units.ext h)
  have h01' : (d 0 : K) = (d 1 : K) := congrArg Units.val h01
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (g : Matrix (Fin 3) (Fin 3) K) 0 2 * ((d 0 : K) - d 2) = 0 := by
      linear_combination -key 0 2
    exact (mul_eq_zero.1 h).resolve_right hne
  · have h : (g : Matrix (Fin 3) (Fin 3) K) 1 2 * ((d 0 : K) - d 2) = 0 := by
      have := key 1 2
      rw [← h01'] at this
      linear_combination -this
    exact (mul_eq_zero.1 h).resolve_right hne
  · have h : (g : Matrix (Fin 3) (Fin 3) K) 2 0 * ((d 0 : K) - d 2) = 0 := by
      linear_combination key 2 0
    exact (mul_eq_zero.1 h).resolve_right hne
  · have h : (g : Matrix (Fin 3) (Fin 3) K) 2 1 * ((d 0 : K) - d 2) = 0 := by
      have := key 2 1
      rw [← h01'] at this
      linear_combination this
    exact (mul_eq_zero.1 h).resolve_right hne

theorem entry22_ne_zero {g : GL (Fin 3) K} (h02 : (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (h12 : (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) : (g : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
  intro h
  have hdet : IsUnit ((g : Matrix (Fin 3) (Fin 3) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have h0 : (g : Matrix (Fin 3) (Fin 3) K).det = 0 := by
    rw [Matrix.det_fin_three]
    simp [h02, h12, h20, h21, h]
  rw [h0] at hdet
  exact not_isUnit_zero hdet

theorem entry22_mul {g h : GL (Fin 3) K} (hg20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (hg21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) (hh02 : (h : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (hh12 : (h : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    ((g * h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
      (g : Matrix (Fin 3) (Fin 3) K) 2 2 * (h : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, hg20, hg21, hh02, hh12]

end Block

section Unitary

variable {K : Type} [Field K] {f : ℕ}

theorem mem_statedSU_two_of_blockGL3 (hK : Nat.card K = (2 ^ f) ^ 2) {A : GL (Fin 2) K}
    (hA : blockGL3 A ∈ StatedSU 3 (2 ^ f) K) : A ∈ StatedSU 2 (2 ^ f) K := by
  have hset3 := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
    (by norm_num : 1 ≤ 3)).1
  have hset2 := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
    (by norm_num : 1 ≤ 2)).1
  have h3 : blockGL3 A ∈ ({B : GL (Fin 3) K | (B : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      ((B : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ f))ᵀ * (B : Matrix (Fin 3) (Fin 3) K) = 1} :
      Set (GL (Fin 3) K)) := by
    rw [← hset3]
    exact hA
  obtain ⟨hdet, hu⟩ := h3
  rw [coe_blockGL3, det_leviMat] at hdet
  rw [coe_blockGL3] at hu
  have hq0 : (0 : K) ^ 2 ^ f = 0 := zero_pow (by positivity)
  have h2 : A ∈ ({B : GL (Fin 2) K | (B : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
      ((B : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f))ᵀ * (B : Matrix (Fin 2) (Fin 2) K) = 1} :
      Set (GL (Fin 2) K)) := by
    refine ⟨hdet, ?_⟩
    ext i j
    have := congrFun (congrFun hu (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, leviMat, hq0,
        Matrix.one_apply] using this
  rw [← hset2] at h2
  exact h2

theorem exists_blockGL3_of_entries (hK : Nat.card K = (2 ^ f) ^ 2) {g : GL (Fin 3) K}
    (hg : g ∈ StatedSU 3 (2 ^ f) K) (h02 : (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (h12 : (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) (h22 : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    ∃ A ∈ StatedSU 2 (2 ^ f) K, blockGL3 A = g := by
  set B : Matrix (Fin 2) (Fin 2) K :=
    !![(g : Matrix (Fin 3) (Fin 3) K) 0 0, (g : Matrix (Fin 3) (Fin 3) K) 0 1;
      (g : Matrix (Fin 3) (Fin 3) K) 1 0, (g : Matrix (Fin 3) (Fin 3) K) 1 1] with hB
  have hgB : (g : Matrix (Fin 3) (Fin 3) K) = leviMat B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviMat, hB, h02, h12, h20, h21, h22]
  have hdet : IsUnit B.det := by
    have h1 : (g : Matrix (Fin 3) (Fin 3) K).det = B.det := by rw [hgB, det_leviMat]
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    rwa [h1] at hu
  let A : GL (Fin 2) K := Matrix.GeneralLinearGroup.mk'' B hdet
  have hAB : (A : Matrix (Fin 2) (Fin 2) K) = B := rfl
  have hbl : blockGL3 A = g := Units.ext (by rw [coe_blockGL3, hAB, hgB])
  exact ⟨A, mem_statedSU_two_of_blockGL3 hK (hbl ▸ hg), hbl⟩

end Unitary

section Main

variable {Q : Type} [Group Q] {K : Type} [Field K] [Finite K] {p f : ℕ}

omit [Finite K] in
theorem blockGL3_injective : Function.Injective (blockGL3 : GL (Fin 2) K →* GL (Fin 3) K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  exact blockGL3_eq_one_of_scalar (by rw [hA]; exact Subgroup.one_mem _)

omit [Finite K] in
theorem blockGL3_commute_diagU {d : Fin 3 → Kˣ} (h01 : d 0 = d 1) (A : GL (Fin 2) K) :
    blockGL3 A * diagU d = diagU d * blockGL3 A := by
  apply Units.ext
  have h01' : (d 0 : K) = (d 1 : K) := congrArg Units.val h01
  rw [Units.val_mul, Units.val_mul, coe_blockGL3, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.mul_apply, Matrix.diagonal_apply, h01'] <;> ring

theorem u3_component_card (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (π : StatedSU 3 (2 ^ f) K →* Q) (hπ : Function.Surjective π)
    (hscal : ∀ g, π g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    {ct : StatedSU 3 (2 ^ f) K} (hc : ct ^ p = 1) {d : Fin 3 → Kˣ}
    (hd : (ct : GL (Fin 3) K) = diagU d) (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2) {Kb : Subgroup Q}
    (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q))
    (hKbN : (Kb.subgroupOf (Subgroup.centralizer ({π ct} : Set Q))).Normal)
    (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥) :
    Nat.card Kb = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  classical
  have hkerN : π.ker = (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ f) K) := by
    ext x
    rw [MonoidHom.mem_ker, hscal, Subgroup.mem_subgroupOf]
  have hker : π.ker ≤ Subgroup.center (StatedSU 3 (2 ^ f) K) := by
    intro x hx
    rw [hkerN] at hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    exact (Subgroup.mem_center_iff.1 (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩) (y : GL (Fin 3) K))
  have hpk : ¬ p ∣ Nat.card π.ker := by
    rw [hkerN, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
      (by norm_num : 1 ≤ 3)).2.2]
    intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left 3 _))
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two
      (by rw [hK, ← pow_mul])
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let L : Subgroup (StatedSU 3 (2 ^ f) K) := leviSU3 (2 ^ f)
  have hLmem : ∀ g : StatedSU 3 (2 ^ f) K, g ∈ L ↔
      ∃ A ∈ StatedSU 2 (2 ^ f) K, blockGL3 A = (g : GL (Fin 3) K) := by
    intro g
    change (g : GL (Fin 3) K) ∈ (StatedSU 2 (2 ^ f) K).map blockGL3 ↔ _
    exact Subgroup.mem_map
  have hLC : L ≤ Subgroup.centralizer ({ct} : Set (StatedSU 3 (2 ^ f) K)) := by
    intro g hg
    obtain ⟨A, -, hA⟩ := (hLmem g).1 hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hd, ← hA]
    exact blockGL3_commute_diagU h01 A
  have hle := map_blockGL3_statedSU_le (K := K) hq1
  let eL : L ≃* StatedSU 2 (2 ^ f) K :=
    (Subgroup.subgroupOfEquivOfLe hle).trans
      ((StatedSU 2 (2 ^ f) K).equivMapOfInjective blockGL3 blockGL3_injective).symm
  obtain ⟨eS⟩ := nonempty_sl2_mulEquiv_statedSU_two (r := 2) (f := f) hK
  have hcardF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K 2 f) = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  have hcharF : CharP (CFSG.LieType.Steinberg.fixedSubfield K 2 f) 2 := inferInstance
  have hsimple : IsSimpleGroup L := by
    have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup
      (K := CFSG.LieType.Steinberg.fixedSubfield K 2 f)
      (by rw [hcardF]; exact hq4)
    exact (eS.trans eL.symm).symm.isSimpleGroup
  have hLinj : ∀ g ∈ L, π g = 1 → g = 1 := by
    intro g hg hπg
    obtain ⟨A, -, hA⟩ := (hLmem g).1 hg
    have hA1 : A = 1 := blockGL3_eq_one_of_scalar (by rw [hA]; exact (hscal g).1 hπg)
    apply Subtype.ext
    rw [← hA, hA1, map_one]
    rfl
  have hblock : ∀ g : Subgroup.centralizer ({ct} : Set (StatedSU 3 (2 ^ f) K)),
      (((g : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (((g : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (((g : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (((g : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    intro g
    have h1 : (g : StatedSU 3 (2 ^ f) K) * ct = ct * g :=
      Subgroup.mem_centralizer_singleton_iff.1 g.2
    have h2 := congrArg (fun x : StatedSU 3 (2 ^ f) K => (x : GL (Fin 3) K)) h1
    simp only [Subgroup.coe_mul, hd] at h2
    exact block_of_commute_diagU h01 h02 h2
  let χ : Subgroup.centralizer ({ct} : Set (StatedSU 3 (2 ^ f) K)) →* Kˣ :=
    { toFun := fun g => Units.mk0
        ((((g : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2)
        (entry22_ne_zero (hblock g).1 (hblock g).2.1 (hblock g).2.2.1 (hblock g).2.2.2)
      map_one' := by
        apply Units.ext
        simp
      map_mul' := fun g h => by
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0]
        exact entry22_mul (hblock g).2.2.1 (hblock g).2.2.2 (hblock h).1 (hblock h).2.1 }
  have hχ : ∀ g : Subgroup.centralizer ({ct} : Set (StatedSU 3 (2 ^ f) K)), χ g = 1 →
      (g : StatedSU 3 (2 ^ f) K) ∈ L := by
    intro g hg
    have h22 : (((g : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
        1 := by
      have := congrArg Units.val hg
      simpa [χ] using this
    obtain ⟨A, hA, hAg⟩ := exists_blockGL3_of_entries hK (g : StatedSU 3 (2 ^ f) K).2
      (hblock g).1 (hblock g).2.1 (hblock g).2.2.1 (hblock g).2.2.2 h22
    exact (hLmem _).2 ⟨A, hA, hAg⟩
  have hcard := card_eq_of_component hp π hπ hker hpk hc (C := Subgroup.centralizer {ct}) rfl
    (CQ := Subgroup.centralizer {π ct}) rfl hKbc hKbN hKbp hKb1 L hLC hsimple hLinj χ hχ
  rw [hcard, Nat.card_congr eL.toEquiv]
  exact card_statedSU_two hK

end Main

end CFSG.RankThree.PartOne.Q1327T
