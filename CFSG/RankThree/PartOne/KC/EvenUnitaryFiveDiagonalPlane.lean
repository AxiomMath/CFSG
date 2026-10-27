module

public import CFSG.RankThree.PartOne.KC.UnitaryCoordCentralizer
public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveEigen

public section

namespace CFSG.RankThree.PartOne.KCEvenUnitaryFive

open Matrix CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryLift CFSG.RankThree.PartOne.KCUnitaryCoord

section Count

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem diag_entry_ne_zero {G : Subgroup (primeFormUnitary h (idGram K 5))}
    (hdiag : ∀ x ∈ G, ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag)
    {x : primeFormUnitary h (idGram K 5)} (hx : x ∈ G) (i : Fin 5) :
    ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i ≠ 0 := by
  have h1 : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      (((x⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        1 := by simp
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.one_apply_eq] at h2
  · exact left_ne_zero_of_mul_eq_one h2
  · intro m _ hm
    rw [hdiag x hx (Ne.symm hm), zero_mul]
  · simp

theorem mul_apply_diag {M N : Matrix (Fin 5) (Fin 5) K} (hM : M.IsDiag) (i : Fin 5) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro m _ hm
    rw [hM (Ne.symm hm), zero_mul]
  · simp

@[expose] noncomputable def ratioHom (G : Subgroup (primeFormUnitary h (idGram K 5)))
    (hdiag : ∀ x ∈ G, ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag) (i j : Fin 5) :
    G →* Kˣ where
  toFun x := Units.mk0 (((x : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) i i *
      (((x : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) j j)⁻¹)
    (mul_ne_zero (diag_entry_ne_zero h hdiag x.2 i)
      (inv_ne_zero (diag_entry_ne_zero h hdiag x.2 j)))
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0]
    rw [mul_apply_diag (hdiag x x.2), mul_apply_diag (hdiag x x.2), mul_inv]
    ring

theorem coe_ratioHom (G : Subgroup (primeFormUnitary h (idGram K 5)))
    (hdiag : ∀ x ∈ G, ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag) (i j : Fin 5)
    (x : G) : (ratioHom h G hdiag i j x : K) =
      ((x : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) i i *
        (((x : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) j j)⁻¹ := rfl

theorem exists_lift_equal_entries (A : Subgroup (MulAut (primeFormP h (idGram K 5))))
    (hAD : A ≤ primeFormD h (idGram K 5)) (hAel : IsElementaryAbelian 5 A)
    (hAcard : Nat.card A = 5 ^ 2) (hq : 3 < 2 ^ f)
    (hdiag : ∀ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A →
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag) (i j : Fin 5) :
    ∃ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A ∧
      primeFormConjHom h (idGram K 5) x ≠ 1 ∧
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i =
        ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) j j := by
  have hn : 3 ≤ 5 := by norm_num
  have hfin := h.finite
  by_contra hcon
  push Not at hcon
  set G := A.comap (primeFormConjHom h (idGram K 5)) with hG
  have hdiagG : ∀ x ∈ G, ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag :=
    fun x hx => hdiag x hx
  let δ := ratioHom h G hdiagG i j
  let π : G →* A := ((primeFormConjHom h (idGram K 5)).comp G.subtype).codRestrict A
    (fun x => x.2)
  have hπsurj : Function.Surjective π := by
    intro a
    obtain ⟨x, hx⟩ := hAD a.2
    exact ⟨⟨x, by rw [hG, Subgroup.mem_comap, hx]; exact a.2⟩, Subtype.ext hx⟩
  have hscal : ∀ x : primeFormUnitary h (idGram K 5),
      primeFormConjHom h (idGram K 5) x = 1 →
        ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) i i =
          ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) j j := by
    intro x hx
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn hq x).mp hx
    rw [hc]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hkerle : π.ker ≤ δ.ker := by
    intro x hx
    have hx1 : primeFormConjHom h (idGram K 5) (x : primeFormUnitary h (idGram K 5)) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [coe_ratioHom, hscal _ hx1, mul_inv_cancel₀ (diag_entry_ne_zero h hdiagG x.2 j)]
    rfl
  have hkerge : δ.ker ≤ π.ker := by
    intro x hx
    have hx1 : δ x = 1 := hx
    have h1 : ((x : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) i i =
        ((x : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) j j := by
      have := congrArg Units.val hx1
      rw [Units.val_one, coe_ratioHom] at this
      exact (mul_inv_eq_one₀ (diag_entry_ne_zero h hdiagG x.2 j)).mp this
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    by_contra hne
    exact hcon x x.2 hne h1
  have hkereq : δ.ker = π.ker := le_antisymm hkerge hkerle
  have h1 : δ.ker.index = Nat.card δ.range := Subgroup.index_ker δ
  have h2 : π.ker.index = Nat.card π.range := Subgroup.index_ker π
  have hπrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπsurj
  have h3 : Nat.card A = Nat.card δ.range := by
    rw [← h1, hkereq, h2, hπrange, Subgroup.card_top]
  have hle : δ.range ≤ rootsOfUnity 5 K := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity]
    have hxp : ((x : primeFormUnitary h (idGram K 5)) ^ 5) ∈
        (primeFormConjHom h (idGram K 5)).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      have := hAel
      exact elemPow_eq_one_of_isElementaryAbelian _ x.2
    rw [← map_pow]
    apply Units.ext
    rw [coe_ratioHom, Units.val_one]
    have := hscal _ (MonoidHom.mem_ker.mp hxp)
    rw [Subgroup.coe_pow] at this
    simp only [Subgroup.coe_pow] at this ⊢
    rw [this, mul_inv_cancel₀]
    have := diag_entry_ne_zero h hdiagG (x := ((x : primeFormUnitary h (idGram K 5)) ^ 5))
      (pow_mem x.2 5) j
    simpa using this
  have h4 := Subgroup.card_le_of_le hle
  have h5 := card_rootsOfUnity K 5
  rw [hAcard] at h3
  omega

end Count

section Diagonal

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem autThetaT_eq_bot_of_diagonal (h5 : 5 ∣ 2 ^ f + 1)
    (B : Subgroup (MulAut (primeFormP h (idGram K 5))))
    (hB : (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range ≤ B)
    (A : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hAD : A ≤ primeFormD h (idGram K 5))
    (hAel : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 2)
    (hdiag : ∀ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ A →
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag) :
    autThetaT 5 B A = ⊥ := by
  have hn : 3 ≤ 5 := by norm_num
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) h5
    omega
  have hq3 : 3 < 2 ^ f := by omega
  have hfin := h.finite
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  refine eq_one_of_commute_coordSU h hq4 (fun i j hij Aij hAij => ?_)
  obtain ⟨x, hxA, hx1, hxij⟩ := exists_lift_equal_entries h A hAD hAel hAcard hq3 hdiag i j
  have hsx : s ∈ inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ Subgroup.centralizer ({primeFormConjHom h (idGram K 5) x} :
        Set (MulAut (primeFormP h (idGram K 5))))) := by
    have h1 := Subgroup.mem_iInf.mp hs (primeFormConjHom h (idGram K 5) x)
    have h2 := Subgroup.mem_iInf.mp h1 hxA
    exact Subgroup.mem_iInf.mp h2 hx1
  have hx5 : x ^ 5 ∈ idScalarKernel h 5 := by
    refine (primeFormConjHom_eq_one_iff hn hq3 _).mp ?_
    rw [map_pow]
    have := hAel
    exact elemPow_eq_one_of_isElementaryAbelian _ hxA
  have hH : UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 x) :=
    ⟨h.bar_bar, idForm_isSymm h 5, idForm_separatingLeft h 5, toLinU_mem x,
      squarefree_minpoly_toLinU_of_pow_scalar (five_ne_zero h) hx5⟩
  have hxdiag : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      diagonal (fun k => ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) k k) :=
    (hdiag x hxA).diagonal_diag.symm
  have hle : coordSU h hij ≤ Subgroup.centralizer ({x} : Set (primeFormUnitary h (idGram K 5))) :=
    coordSU_le_centralizer_diagonal h hij _ hxij hxdiag
  have hcomm : coordSU h hij ≤ ⁅Subgroup.centralizer ({x} : Set (primeFormUnitary h (idGram K 5))),
      Subgroup.centralizer ({x} : Set (primeFormUnitary h (idGram K 5)))⁆ := by
    calc coordSU h hij = ⁅coordSU h hij, coordSU h hij⁆ :=
          (commutator_eq_of_isPerfect (isPerfect_coordSU h hq4 hij)).symm
      _ ≤ _ := Subgroup.commutator_mono hle hle
  exact (commute_core_commutator_centralizer hn hq4 hH B hB Nat.prime_five hsx
    (hcomm hAij)).eq.symm

end Diagonal

end CFSG.RankThree.PartOne.KCEvenUnitaryFive
